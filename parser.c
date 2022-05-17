
/*
* 컴파일러 과제 - parser 구현
* 2020112757 컴퓨터학부 김유진
*/

#define _CRT_SECURE_NO_WARNINGS
#define MAXTOKENLEN 40 /* MAXTOKENLEN is the maximum size of a token */
#define MAXRESERVED 6 /* MAXRESERVED = the number of reserved words */
#define BUFLEN 256
#define FALSE 0
#define TRUE 1

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <string.h>

int lineno = 0;
FILE* source;
FILE* listing;
FILE* fp;
FILE* code;

/* allocate and set tracing flags */
int EchoSource = TRUE;
int TraceScan = FALSE;
int TraceParse = TRUE;
int Error = FALSE;

static char lineBuf[BUFLEN]; /* holds the current line */
static int linepos = 0; /* current position in LineBuf */
static int bufsize = 0; /* current size of buffer string */
static int EOF_flag = FALSE; /* corrects ungetNextChar behavior on EOF */

// 토큰을 담을 배열
char tokenString[MAXTOKENLEN + 1];

// StateType 정의
typedef enum
{
    START, INASSIGN, INCOMMENT, INNUM, INID, DONE
}
StateType;


// 토큰 타입
typedef enum
/* book-keeping tokens */
{
	ENDFILE, ERROR,
	/* reserved words */
	IF, ELSE, INT, RETURN, VOID, WHILE,
	/* multicharacter tokens */
	ID, NUM,
	/* special symbols */
	PLUS, MINUS, TIMES, OVER, LT, LTE, GT, GTE, EQ, NEQ, ASSIGN, COMMA, SEMI, LPAREN, RPAREN, LBRAC, RBRAC, LCBRAC, RCBRAC,
	/* nonterminal */
	VAR, FUN
} TokenType;

// 예약어 테이블
/* lookup table of reserved words */
static struct
{
    char* str;
    TokenType tok;
} reservedWords[MAXRESERVED]
= { {"if",IF},{"else",ELSE},
   {"int",INT},{"return",RETURN},
    {"void",VOID},{"while",WHILE} };


static int getNextChar(void);
static void ungetNextChar(void);
static TokenType reservedLookup(char* s);
TokenType getToken(void);
void printToken(TokenType token, const char* tokenString);

// ------------ parser ----------------


typedef enum { DecK, StmtK, ExpK } NodeKind;
typedef enum { VarK, FunK, ArrayK} DecKind;
typedef enum { IfK, ElseK, ReturnK, AssignK, WhileK, CompoundK, CallK } StmtKind;
typedef enum { OpK, ConstK, IdK } ExpKind;

/* ExpType is used for type checking */
typedef enum { Void, Int, Boolean } ExpType;

#define MAXCHILDREN 3

typedef struct treeNode
{
	struct treeNode* child[MAXCHILDREN];
	struct treeNode* sibling;
	int lineno;
	NodeKind nodekind;
	union { StmtKind stmt; ExpKind exp; DecKind dec; } kind;
	union {
		TokenType op;
		int val;
		char* name;
	} attr;

	int value; // array index!
	int isArray;
	int isParameter;
	int isGlobal;
	int param_size;
	int local_size;
	int scope;

	ExpType type; /* for type checking of exps */
} TreeNode;

TreeNode* newDecNode(DecKind kind);
TreeNode* newStmtNode(StmtKind kind);
TreeNode* newExpNode(ExpKind kind);
char* copyString(char* s);
static void printSpaces(void);
void printTree(TreeNode* tree);


// Parser 글로벌 변수들
static TokenType token; /* holds current token */


/* 내가 만든 Parse 함수들 */
TreeNode* declaration_list(void);
TreeNode* declaration(void);
TreeNode* var_declaration(void);
//TreeNode* fun_declaration(void);

static TreeNode* statement(void);

TreeNode* param_list(void);
TreeNode* param(void);

TreeNode* args(void);
TreeNode* args_list(void);
TreeNode* statement_list(void);
TreeNode* statement(void);
TreeNode* expression_stmt(void);
TreeNode* compound_stmt(void);
TreeNode* selection_stmt(void);
TreeNode* iteration_stmt(void);
TreeNode* return_stmt(void);


TreeNode* exp(void);
TreeNode* simple_exp(TreeNode* pass);
TreeNode* additive_exp(TreeNode* pass);
TreeNode* term(TreeNode* pass);
TreeNode* factor(TreeNode* pass);

TreeNode* var_or_call(void);
TreeNode* args(void);

TreeNode* parse(void);

static void printSpaces(void);

static int global_size = 0;

main(int argc, char* argv[])
{
	TreeNode* syntaxTree;
    char pgm[120]; /* source code file name */

    // filename[.exe] input[.c] ouput[.txt] 
    if (argc != 3)
    {
        fprintf(stderr, "usage: %s <input_filename> <output_filename>\n", argv[0]);
        exit(1);
    }

	// c파일 열기
    strcpy(pgm, argv[1]);
    if (strchr(pgm, '.') == NULL)
        strcat(pgm, ".c"); // 대문자?
    source = fopen(pgm, "r");

    if (source == NULL)
    {
        fprintf(stderr, "File %s not found\n", pgm);
        exit(1);
    }

    // 결과 출력: .txt 파일에 결과 출력.
    fp = fopen(argv[2], "w");
	if (fp == NULL)
	{
		fprintf(stderr, "File %s not found\n", argv[2]);
		exit(1);
	}
    // listing = stdout; /* send listing to screen */
    listing = fp;
    fprintf(listing, "\nC- COMPILATION: %s\n", pgm);

    // while (getToken() != ENDFILE); // 파일이 끝날 때 까지 토큰 얻어오기

	syntaxTree = parse();
	if (TraceParse) {
		fprintf(listing, "\nSyntax tree:\n");
		printTree(syntaxTree);
	}

    fclose(source);
	fclose(fp);
    return 0;
}

static int getNextChar(void)
{
    if (!(linepos < bufsize))
    {
        lineno++;
        if (fgets(lineBuf, BUFLEN - 1, source))
        {
            if (EchoSource) fprintf(listing, "%4d: %s", lineno, lineBuf);
            bufsize = strlen(lineBuf);
            linepos = 0;
            return lineBuf[linepos++];
        }
        else
        {
            EOF_flag = TRUE;
            return EOF;
        }
    }
    else return lineBuf[linepos++];
}

/* ungetNextChar backtracks one character
   in lineBuf */
static void ungetNextChar(void)
{
    if (!EOF_flag) linepos--;
}

// 여기서 이진탐색해서 성능을 향상 시킴
/* lookup an identifier to see if it is a reserved word */
/* uses linear search */
static TokenType reservedLookup(char* s)
{
    int i;
    for (i = 0; i < MAXRESERVED; i++)
        if (!strcmp(s, reservedWords[i].str))
            return reservedWords[i].tok;
    return ID;
}

/****************************************/
/* the primary function of the scanner  */
/****************************************/
/* function getToken returns the
 * next token in source file
 */
TokenType getToken(void)
{
	/* index for storing into tokenString */
	int tokenStringIndex = 0;

	/* holds current token to be returned */
	TokenType currentToken;

	/* current state - always begins at START : 처음 시작 start로 */
	StateType state = START;

	/* flag to indicate save to tokenString */
	int save;

	while (state != DONE)
	{
		int c = getNextChar();
		save = TRUE;

		switch (state)
		{
		case START:
			if (isdigit(c)) // 숫자
				state = INNUM;
			else if (isalpha(c)) // 문자
				state = INID;
			// INASSIGN state 진입 조건 : <, >, =, !
			else if ((c == '<') || (c == '>') || (c == '=') || (c == '!')) 
				state = INASSIGN;
			else if ((c == ' ') || (c == '\t') || (c == '\n')) // 공백 처리
				save = FALSE;
			else if (c == '/') // 주석 처리 부분
			{
				// [OTHER]
				// 다음 문자가 '*'일 경우 INCOMMENT state로 진입함.
				c = getNextChar(); 
				if (c == '*') { 
					save = FALSE;
					state = INCOMMENT;
				}
				// 다음 문자가 '*'가 아닐 경우, 커서를 당기고 '/'를 최종 토큰으로 인식함.
				else {
					ungetNextChar();
					state = DONE;
					currentToken = OVER;
				}
			}
			else
			{
				state = DONE;
				switch (c)
				{
				case EOF:
					save = FALSE;
					currentToken = ENDFILE;
					break;
				case '+':
					currentToken = PLUS;
					break;
				case '-':
					currentToken = MINUS;
					break;
				case '*':
					currentToken = TIMES;
					break;
				case ',':	// , 추가
					currentToken = COMMA;
					break;
				case '(':
					currentToken = LPAREN;
					break;
				case ')':
					currentToken = RPAREN;
					break;
				case '[':	// [ 추가
					currentToken = LBRAC;
					break;
				case ']':	// ] 추가
					currentToken = RBRAC;
					break;
				case '{':	// { 추가
					currentToken = LCBRAC;
					break;
				case '}':	// } 추가
					currentToken = RCBRAC;
					break;
				case ';':
					currentToken = SEMI;
					break;
				default:
					currentToken = ERROR;
					break;
				}
			}
			break;
		case INCOMMENT:
			save = FALSE;
			// comment가 끝나기 전에 파일이 끝이나면 error를 출력함.
			if (c == EOF)
			{
				state = DONE;
				currentToken = ENDFILE;
				fprintf(listing, "ERROR: stop before ending\n");
			}
			else if (c == '*')
			{
				// '*' 다음 문자가 '/'일 경우, comment가 끝나고 START state로 돌아감.
				c = getNextChar();
				if (c == '/') {
					state = START;
					break;
				}
			}
			break;
		case INASSIGN:
			state = DONE;
			char t = tokenString[0]; // 앞서 저장한 문자
			// 두 번째로 오는 문자가 '='이 아닐 경우
			if (c != '=') { // [other]
				/* backup in the input */
				ungetNextChar();
				save = FALSE;
				switch (t)
				{
				case '<':	// <
					currentToken = LT;
					break;
				case '>':	// >
					currentToken = GT;
					break;
				case '=':	// =
					currentToken = ASSIGN;
					break;
				case '!':	// !
					currentToken = ERROR;
					break;
				}
			}
			else // c == '='
			{
				switch (t)
				{
				case '<':	// <=
					currentToken = LTE;
					break;
				case '>':	// >=
					currentToken = GTE;
					break;
				case '=':	// ==
					currentToken = EQ;
					break;
				case '!':	// !=
					currentToken = NEQ;
					break;
				}
			}
			break;
		case INNUM:
			if (!isdigit(c))
			{ /* backup in the input */
				ungetNextChar();
				save = FALSE;
				state = DONE;
				currentToken = NUM;
			}
			break;
		case INID:
			if (!isalpha(c))
			{ /* backup in the input */
				ungetNextChar();
				save = FALSE;
				state = DONE;
				currentToken = ID;
			}
			break;
		case DONE:
		default: /* should never happen */
			fprintf(listing, "Scanner Bug: state= %d\n", state);
			state = DONE;
			currentToken = ERROR;
			break;
		}
		if ((save) && (tokenStringIndex <= MAXTOKENLEN))
			tokenString[tokenStringIndex++] = (char)c;
		if (state == DONE)
		{
			tokenString[tokenStringIndex] = '\0';
			if (currentToken == ID)
				currentToken = reservedLookup(tokenString);
		}
	}
	if (TraceScan) {
		fprintf(listing, "\t%d: ", lineno); // 라인 넘버
		printToken(currentToken, tokenString);  // UTIL.C에 있음
	}
	return currentToken;
} /* end getToken */

void printToken(TokenType token, const char* tokenString)
{
	switch (token)
	{
	case IF:
	case ELSE:
	case INT:
	case RETURN:
	case VOID:
	case WHILE:
		fprintf(listing,
			"reserved word: %s\n", tokenString);
		break;
	case ASSIGN: fprintf(listing, "=\n"); break;
	case EQ: fprintf(listing, "==\n"); break;
	case NEQ: fprintf(listing, "!=\n"); break;
	case LT: fprintf(listing, "<\n"); break;
	case LTE: fprintf(listing, "<=\n"); break;
	case GT: fprintf(listing, ">\n"); break;
	case GTE: fprintf(listing, ">=\n"); break;
	case LPAREN: fprintf(listing, "(\n"); break;
	case RPAREN: fprintf(listing, ")\n"); break;
	case LBRAC: fprintf(listing, "[\n"); break;
	case RBRAC: fprintf(listing, "]\n"); break;
	case LCBRAC: fprintf(listing, "{\n"); break;
	case RCBRAC: fprintf(listing, "}\n"); break;
	case SEMI: fprintf(listing, ";\n"); break;
	case PLUS: fprintf(listing, "+\n"); break;
	case MINUS: fprintf(listing, "-\n"); break;
	case TIMES: fprintf(listing, "*\n"); break;
	case OVER: fprintf(listing, "/\n"); break;
	case COMMA: fprintf(listing, ",\n"); break;
	case ENDFILE: fprintf(listing, "EOF\n"); break;
	case NUM:
		fprintf(listing,
			"NUM, val= %s\n", tokenString);
		break;
	case ID:
		fprintf(listing,
			"ID, name= %s\n", tokenString);
		break;
	case ERROR:
		fprintf(listing,
			"ERROR: %s\n", tokenString);
		break;
	default: /* should never happen */
		fprintf(listing, "Unknown token: %d\n", token);
	}
}

//----------------------------------------------------------------------parser!!

static void syntaxError(char* message)
{
	fprintf(listing, "\n>>> ");
	fprintf(listing, "Syntax error at line %d: %s", lineno, message);
	Error = TRUE;
}

static void match(TokenType expected)
{
	if (token == expected) token = getToken();
	else {
		syntaxError("unexpected token -> ");
		printToken(token, tokenString);
		fprintf(listing, "      ");
	}
}

static ExpType type_specifier()
{
	ExpType t_type = VOID;

	switch (token)
	{
	case INT:  t_type = Int; token = getToken(); break;
	case VOID: t_type = Void; token = getToken(); break;
	default: 
	{
		syntaxError("unexpected type ->");
		printToken(token, tokenString);
		fprintf(listing, "\n");
		break;
	}
	}

	return t_type;
}

TreeNode* declaration_list(void)
{
	TreeNode* t = declaration();
	TreeNode * p = t;
	while ((token != ENDFILE))
	{
		TreeNode* q;
		q = declaration();
		if (q != NULL) {
			if (t == NULL) t = p = q;
			else /* now p cannot be NULL either */
			{
				p->sibling = q;
				p = q;
			}
		}
	}
	return t;
}

TreeNode* declaration(void)
{
	TreeNode* t = NULL;
	ExpType   decType;
	char* identifier;
	//if (token == INT) match(INT);
	//else if (token == VOID) match(VOID);

	decType = type_specifier();
	identifier = copyString(tokenString);
	match(ID);

	switch (token) 
	{
	// ; : 변수 
	case SEMI: t = newDecNode(VarK);
		if (t != NULL) 
		{
			t->type = decType;
			t->attr.name = identifier;
			global_size++;
		}
		match(SEMI);
		break;	

	// [ : 배열
	case LBRAC: t = newDecNode(ArrayK); 
		if (t != NULL)
		{
			t->type = decType;
			t->attr.name = identifier;
		}
		match(LBRAC);
		if (t != NULL && token == NUM) {
			//t = newExpNode(ConstK);
			t->value = atoi(tokenString);
			match(NUM);
		}
		else {
			syntaxError("unexpected token -> ");
			printToken(token, tokenString);
			token = getToken();
		}
		match(RBRAC);
		match(SEMI);
		break;

	// '(' : 함수
	case LPAREN: t = newDecNode(FunK); 
		if (t != NULL)
		{
			t->type = decType;
			t->attr.name = identifier;
		}
		match(LPAREN);
		if (t != NULL) t->child[0] = param_list();
		match(RPAREN);
		if (t != NULL) t->child[1] = compound_stmt();
		break;

	default: syntaxError("unexpected token -> ");
		printToken(token, tokenString);
		token = getToken();
		break;
	} /* end case */
	return t;
}

TreeNode* var_declaration(void) 
{
	TreeNode* t = NULL;
	ExpType   decType;
	char* identifier;

	decType = type_specifier();
	identifier = copyString(tokenString);
	match(ID);

	switch (token)
	{
		// ; : 변수 
	case SEMI: t = newDecNode(VarK);
		if (t != NULL)
		{
			t->type = decType;
			t->attr.name = identifier;
		}
		match(SEMI);
		break;

		// [ : 배열
	case LBRAC: t = newDecNode(ArrayK);
		if (t != NULL)
		{
			t->type = decType;
			t->attr.name = identifier;
			t->local_size = 1;
		}
		match(LBRAC);
		if (t != NULL && token == NUM) {
			//t = newExpNode(ConstK);
			t->value = atoi(tokenString);
			t->local_size = t->value;
			t->isArray = TRUE;
			match(NUM);
		}
		else {
			syntaxError("unexpected token -> ");
			printToken(token, tokenString);
			token = getToken();
		}
		match(RBRAC);
		match(SEMI);
		break;

	default: syntaxError("unexpected token -> ");
		printToken(token, tokenString);
		token = getToken();
		break;
	} /* end case */

	return t;
}


TreeNode* param_list(void) 
{
	TreeNode* t;
	TreeNode* p;
	TreeNode* q;
	int param_count = 0;
	if (token == VOID)
	{
		match(VOID);
		return NULL;  /* No parameter ,VOID */
	}

	t = param();
	if (t != NULL) {
		p = t;
		param_count++;
		while ((t != NULL) && (token == COMMA))
		{
			match(COMMA);
			q = param();
			if (q != NULL)
			{
				param_count++;
				p->sibling = q;
				p = q;
			}
		}
		t->param_size = param_count;
	}
	return t;
}

TreeNode* param(void) 
{
	TreeNode* t;
	ExpType parmType;
	char* identifier;

	parmType = type_specifier();
	identifier = copyString(tokenString);
	match(ID);

	// 배열 파라미터
	if (token == LBRAC)
	{
		match(LBRAC);
		match(RBRAC);

		t = newDecNode(ArrayK);
		t->isArray = TRUE;
	}
	// 변수 파라미터
	else 
		t = newDecNode(VarK);

	if (t != NULL)
	{
		t->type = parmType;
		t->attr.name = identifier;
		t->value = 0;
		t->isParameter = TRUE;
	}
	return t;
}

TreeNode* local_declations(void)
{
	TreeNode* t = NULL;
	TreeNode* p;
	TreeNode* q;
	TreeNode* temp;
	int local_var = 0;

	if ((token == VOID) || (token == INT))
		t = var_declaration();

	if (t != NULL)
	{
		p = t;
		while ((token == VOID) || (token == INT))
		{
			q = var_declaration();
			if (q != NULL)
			{
				p->sibling = q;
				p = q;
			}
		}

		temp = t;
		while (temp != NULL) {
			local_var = local_var + temp->local_size;
			temp = temp->sibling;
		}
		t->local_size = local_var;
	}
	return t;
}

TreeNode* compound_stmt(void)
{
	TreeNode* t = newStmtNode(CompoundK);
	match(LCBRAC);

	if ((t != NULL) && (token != RCBRAC)) // compound_stmt의 follow '}'
	{
		if ((token == INT) || (token == VOID))
			t->child[0] = local_declations();
		if (token != RCBRAC)
			t->child[1] = statement_list();
	}

	match(RCBRAC);
	return t;
}

TreeNode* statement_list(void)
{
	//TreeNode* t = NULL;
	//TreeNode* p = t;
	//while (token != RCBRAC)	// follow(statement_list)
	//{
	//	TreeNode* q;
	//	q = statement();
	//	if (q != NULL) {
	//		if(p != NULL)
	//		{
	//			p->sibling = q;
	//			p = q;
	//		}
	//	}
	//}
	//return t;

	TreeNode* t = NULL;
	TreeNode* p;
	TreeNode* q;

	/*first statement */
	if (token != RCBRAC)	// Follow(statement_list)={ '}' }
	{
		t = statement();
		p = t;

		/*subsequest statement */
		while (token != RCBRAC)
		{
			q = statement();
			if ((p != NULL) && (q != NULL))
			{
				p->sibling = q;
				p = q;
			}
		}
	}

	return t;
}

TreeNode* statement(void)
{
	TreeNode* t = NULL;
	switch (token) {
	case ID:
	case NUM:
	case LPAREN:
	case SEMI: t = expression_stmt(); break;

	case LCBRAC: t = compound_stmt(); break; // {
	case IF: t = selection_stmt(); break;
	case WHILE: t = iteration_stmt(); break;
	case RETURN: t = return_stmt(); break;

	default: syntaxError("unexpected token -> ");
		printToken(token, tokenString);
		token = getToken();
		break;
	} /* end case */
	return t;
}


TreeNode* expression_stmt(void)
{
	TreeNode* t = NULL;
	if ((token != SEMI) && (token != RCBRAC)) 
	{
		t = exp();
	}
	match(SEMI);
	return t;
}


TreeNode* selection_stmt(void)
{
	TreeNode* t = newStmtNode(IfK);
	match(IF);
	match(LPAREN);	// (
	if (t != NULL) t->child[0] = exp();
	match(RPAREN);	// )
	if (t != NULL) t->child[1] = statement();
	if (token == ELSE) 
	{
		match(ELSE);
		if (t != NULL) t->child[2] = statement();
	}
	return t;
}

TreeNode* iteration_stmt(void)
{
	TreeNode* t = newStmtNode(WhileK);
	match(WHILE);
	match(LPAREN);	// (
	if (t != NULL) t->child[0] = exp();
	match(RPAREN);	// )
	if (t != NULL) t->child[1] = statement();
	return t;
}

// 수정?
TreeNode* return_stmt(void)
{
	//TreeNode* t = newStmtNode(ReturnK);
	//match(RETURN);
	//if ((t != NULL) && (token != SEMI)) 
	//	t->child[0] = exp();
	//match(SEMI);
	//return t;
	TreeNode* tree;
	TreeNode* expr = NULL;

	match(RETURN);

	tree = newStmtNode(ReturnK);
	if (token != SEMI) 		//follow(return_statement)
		expr = exp();

	if (tree != NULL)
		tree->child[0] = expr;

	match(SEMI);

	return tree;
}

// 고쳐야함!!
TreeNode* exp(void)
{
	TreeNode* t = NULL;
	TreeNode* left = NULL;
	TreeNode* right = NULL;

	int gotLvalue = FALSE;

	if (token == ID) 
	{
		left = var_or_call();
		gotLvalue = TRUE;
	}

	if ((gotLvalue == TRUE) && (token == ASSIGN)) 
	{
		printf("left->kind.dec = %d\n", left->kind.dec);
		if ((left != NULL) && 
			((left->nodekind == ExpK) || (left->nodekind == DecK)) &&
			((left->kind.exp == IdK)||(left->kind.dec == ArrayK)))
        {
            match(ASSIGN);
            right = exp();

            t = newExpNode(AssignK);
            if (t != NULL)
            {
                t->child[0] = left;
                t->child[1] = right;
            }
        }
        else
        { 
            syntaxError("Left can't assign to something.\n"); // 수정
            token = getToken();
        }
	}
	else
		t = simple_exp(left);

	return t;
}

TreeNode* simple_exp(TreeNode* pass)
{
	TreeNode* t;
	TreeNode* left = NULL;
	TreeNode* right = NULL;
	TokenType relop;

	left = additive_exp(pass);


	if ((token == GTE) || (token == GT) || 
		(token == LTE) || (token == LT) || 
		(token == EQ) || (token == NEQ))
	{ 
		relop = token;
		match(token);
		right = additive_exp(NULL);

		t = newExpNode(OpK);
		if (t != NULL)
		{
			t->child[0] = left;
			t->child[1] = right;
			t->attr.op = relop;
		}
	}
	else
		t = left;

	return t;
}

TreeNode* additive_exp(TreeNode* pass)
{
	TreeNode* t;
	TreeNode* p;

	t = term(pass);

	while ((token == PLUS) || (token == MINUS))
	{
		p = newExpNode(OpK);

		if (p != NULL)
		{
			p->attr.op = token;
			p->child[0] = t;
			t = p;
			match(token);
			p->child[1] = term(NULL);
		}
	}

	return t;
}

TreeNode* term(TreeNode* pass)
{
	TreeNode* t;
	TreeNode* p;

	t = factor(pass);

	while ((token == TIMES) || (token == OVER))
	{
		p = newExpNode(OpK);

		if (p != NULL)
		{
			p->attr.op = token;
			p->child[0] = t;
			t = p;
			match(token);
			p->child[1] = factor(NULL);
		}
	}

	return t;
}

TreeNode* factor(TreeNode* pass)
{
	TreeNode* t = NULL;

	if (pass != NULL) return pass;

	if (token == ID)
	{
		t = var_or_call();
	}
	else if (token == LPAREN)
	{
		match(LPAREN);
		t = exp();
		match(RPAREN);
	}
	else if (token == NUM)
	{
		t = newExpNode(ConstK);
		if (t != NULL)
		{
			t->attr.val = atoi(tokenString);
			t->type = Int;
		}
		match(NUM);
	}
	else
	{
		syntaxError("unexpected token ");
		printToken(token, tokenString);
		fprintf(listing, "\n");
		token = getToken();
	}
	return t;
}

TreeNode* var_or_call(void) 
{
	TreeNode* t = NULL;
	TreeNode* exptemp = NULL;
	TreeNode* arguments = NULL;
	char* identifier = NULL;

	// 먼저 ID 처리 (변수인지 배열인지 모름)
	if (token == ID) {
		identifier = copyString(tokenString);
		match(ID);
	}

	// 함수인 경우
	if (token == LPAREN)
	{
		t = newStmtNode(CallK);

		match(LPAREN);
		//arguments = args();
		if (t != NULL) {
			t->child[0] = args();
			t->attr.name = identifier;
			if (t->child[0] != NULL)
				t->param_size = t->child[0]->param_size;
			else
				t->param_size = 0;
		}
		match(RPAREN);
		

	}
	else 
	{
		// 배열인 경우
		if (token == LBRAC)
		{
			t = newDecNode(ArrayK);
			t->isArray = TRUE;
			t->type = Int;
			match(LBRAC);		// [
			exptemp = exp();
			match(RBRAC);		// ]
		}
		// expression
		else
			t = newExpNode(IdK);

		if (t != NULL)
		{
			t->child[0] = exptemp;
			t->attr.name = identifier;
		}
	}
	return t;
}

//TreeNode* call(void)
//{
//	TreeNode* t = newStmtNode(CallK);
//	TreeNode* arguments = NULL;
//
//	if ((t!=NULL) && token == ID) 
//		t->attr.name = copyString(tokenString);
//	match(ID);
//
//	match(LPAREN);
//	arguments = args();
//	if (t != NULL) {
//		t->child[0] = arguments;
//
//		if (arguments != NULL)
//			t->param_size = arguments->param_size;
//		else
//			t->param_size = 0;
//		match(RPAREN);
//	}
//
//	return t;
//}

TreeNode* args(void)
{
	TreeNode* t = NULL;
	if (token != RPAREN)	// follow(args)
		t = args_list();

	return t;
}

TreeNode* args_list(void)
{

	TreeNode* t = exp();
	TreeNode* p = t;
	TreeNode* q;
	int arg_count = 1;

	while (token == COMMA)
	{
		match(COMMA);
		q = exp();
		arg_count++;
		if ((p != NULL) && (t != NULL))
		{
			p->sibling = q;
			p = q;
		}
	}
	t->param_size = arg_count;

	return t;
}



/****************************************/
/* the primary function of the parser   */
/****************************************/
/* Function parse returns the newly
 * constructed syntax tree
 */
TreeNode* parse(void)
{
	TreeNode* t;
	token = getToken();
	t = declaration_list();
	if (token != ENDFILE)
		syntaxError("Code ends before file\n");
	return t;
}


/* Function newDecNode creates a new declaration
 * node for syntax tree construction
 */

TreeNode* newDecNode(DecKind kind)
{
	TreeNode* t = (TreeNode*)malloc(sizeof(TreeNode));
	int i;
	if (t == NULL)
		fprintf(listing, "Out of memory error at line %d\n", lineno);
	else {
		for (i = 0; i < MAXCHILDREN; i++) t->child[i] = NULL;
		t->sibling = NULL;
		t->nodekind = DecK;
		t->kind.stmt = kind;
		t->lineno = lineno;
		t->type = Void;
	}
	return t;
}

/* Function newStmtNode creates a new statement
 * node for syntax tree construction
 */

TreeNode* newStmtNode(StmtKind kind)
{
	TreeNode* t = (TreeNode*)malloc(sizeof(TreeNode));
	int i;
	if (t == NULL)
		fprintf(listing, "Out of memory error at line %d\n", lineno);
	else {
		for (i = 0; i < MAXCHILDREN; i++) t->child[i] = NULL;
		t->sibling = NULL;
		t->nodekind = StmtK;
		t->kind.stmt = kind;
		t->lineno = lineno;
	}
	return t;
}

/* Function newExpNode creates a new expression
 * node for syntax tree construction
 */
TreeNode* newExpNode(ExpKind kind)
{
	TreeNode* t = (TreeNode*)malloc(sizeof(TreeNode));
	int i;
	if (t == NULL)
		fprintf(listing, "Out of memory error at line %d\n", lineno);
	else {
		for (i = 0; i < MAXCHILDREN; i++) t->child[i] = NULL;
		t->sibling = NULL;
		t->nodekind = ExpK;
		t->kind.exp = kind;
		t->lineno = lineno;
		t->type = VOID;
	}
	return t;
}

/* Function copyString allocates and makes a new
 * copy of an existing string
 */
char* copyString(char* s)
{
	int n;
	char* t;
	if (s == NULL) return NULL;
	n = strlen(s) + 1;
	t = malloc(n);
	if (t == NULL)
		fprintf(listing, "Out of memory error at line %d\n", lineno);
	else strcpy(t, s);
	return t;
}

/* Variable indentno is used by printTree to
 * store current number of spaces to indent
 */
static indentno = 0;

/* macros to increase/decrease indentation */
#define INDENT indentno+=2
#define UNINDENT indentno-=2

/* printSpaces indents by printing spaces */
static void printSpaces(void)
{
	int i;
	for (i = 0; i < indentno; i++)
		fprintf(listing, " ");
}

void printTree(TreeNode* tree)
{
	int i;

	INDENT;

	while (tree != NULL)  /* try not to visit null tree children */
	{
		printSpaces();

		/* Examine node type, and base output on that. */
		if (tree->nodekind == DecK)
		{
			switch (tree->kind.dec)
			{
			case VarK:
				fprintf(listing, "[Variable declaration \"%s\" of type \"%s\"]\n"
					, tree->attr.name, tree->type == Int ? "Integer" : "Void");
				break;
			case ArrayK:
				fprintf(listing, "[Array declaration \"%s\" of size %d"
					" and type \"%s\"]\n",
					tree->attr.name, tree->value, tree->type == Int ? "Integer" : "Void");
				break;
			case FunK:
				fprintf(listing, "[Function declaration \"%s()\""
					" of return type \"%s\"]\n",
					tree->attr.name, tree->type == Int ? "Integer" : "Void");
				break;
			default:
				fprintf(listing, "<<<unknown declaration type>>>\n");
				break;
			}
		}
		else if (tree->nodekind == ExpK)
		{
			switch (tree->kind.exp)
			{
			case OpK:
				fprintf(listing, "[Operator \"");
				printToken(tree->attr.op, "");
				// printf("tree-> attr.op = %s\n", (tree->attr.op == OVER) ? "OVER" : "NOT OVER");
				break;
			case IdK:
				fprintf(listing, "[Identifier \"%s", tree->attr.name);
				if (tree->value != 0) /* array indexing */
					fprintf(listing, "[%d]", tree->value);
				fprintf(listing, "\"]\n");
				break;
			case ConstK:
				fprintf(listing, "[Literal constant \"%d\"]\n", tree->attr.val);
				break;
			case AssignK:
				fprintf(listing, "[Assignment]\n");
				break;
			default:
				fprintf(listing, "<<<unknown expression type>>>\n");
				break;
			}
		}
		else if (tree->nodekind == StmtK)
		{
			switch (tree->kind.stmt)
			{
			case CompoundK:
				fprintf(listing, "[Compound statement]\n");
				break;
			case IfK:
				fprintf(listing, "[IF statement]\n");
				break;
			case WhileK:
				fprintf(listing, "[WHILE statement]\n");
				break;
			case ReturnK:
				fprintf(listing, "[RETURN statement]\n");
				break;
			case CallK:
				fprintf(listing, "[Call to function \"%s() %d\"]\n",
					tree->attr.name, (tree->child[0]) != NULL ? (tree->child[0])->param_size : 0);
				break;
			default:
				fprintf(listing, "<<<unknown statement type>>>\n");
				break;
			}
		}
		else
			fprintf(listing, "<<<unknown node kind>>>\n");

		for (i = 0; i < MAXCHILDREN; ++i)
			printTree(tree->child[i]);

		tree = tree->sibling;
	}

	UNINDENT;
}

/* procedure printTree prints a syntax tree to the
 * listing file using indentation to indicate subtrees
 */
//void printTree(TreeNode* tree)
//{
//	int i;
//	INDENT;
//	while (tree != NULL) {
//		printSpaces();
//		if (tree->nodekind == StmtK)
//		{
//			switch (tree->kind.stmt) {
//			case IfK:
//				fprintf(listing, "If\n");
//				break;
//			case ElseK:
//				fprintf(listing, "Else\n");
//				break;
//			case ReturnK:
//				fprintf(listing, "Return : %s\n", tree->attr.name);
//				break;
//			case WhileK:
//				fprintf(listing, "While\n");
//				break;
//			case CompoundK:
//				fprintf(listing, "Compound \n");
//				break;
//			default:
//				fprintf(listing, "Unknown ExpNode kind\n");
//				break;
//			}
//		}
//		else if (tree->nodekind == ExpK)
//		{
//			switch (tree->kind.exp) {
//			//case OpK:
//			//	fprintf(listing, "Op: ");
//			//	printToken(tree->attr.op, "\0");
//			//	break;
//			case RelopK:
//				fprintf(listing, "RelOp: ");
//				printToken(tree->attr.op, "\0");
//				break;
//			case ConstK:
//				fprintf(listing, "Const: %d\n", tree->attr.val);
//				break;
//			case IdK:
//				fprintf(listing, "Id: %s\n", tree->attr.name);
//				break;
//			default:
//				fprintf(listing, "Unknown ExpNode kind\n");
//				break;
//			}
//		}
//		else fprintf(listing, "Unknown node kind\n");
//		for (i = 0; i < MAXCHILDREN; i++)
//			printTree(tree->child[i]);
//		tree = tree->sibling;
//	}
//	UNINDENT;
//}
