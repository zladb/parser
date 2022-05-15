
/*
* 컴파일러 과제 - scanner 구현
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
typedef enum { VarK, FunK} DecKind;
typedef enum { IfK, ElseK, ReturnK, WhileK } StmtKind;
typedef enum { RelopK, AddopK, MulopK, ConstK, IdK } ExpKind;

/* ExpType is used for type checking */
typedef enum { VOID, INT, Boolean } ExpType;

#define MAXCHILDREN 3

typedef struct treeNode
{
	struct treeNode* child[MAXCHILDREN];
	struct treeNode* sibling;
	int lineno;
	NodeKind nodekind;
	union { StmtKind stmt; ExpKind exp; } kind;
	union {
		TokenType op;
		int val;
		char* name;
	} attr;
	ExpType type; /* for type checking of exps */
} TreeNode;

TreeNode* newDecNode(ExpKind kind);
TreeNode* newStmtNode(StmtKind kind);
TreeNode* newExpNode(ExpKind kind);
char* copyString(char* s);
static void printSpaces(void);
void printTree(TreeNode* tree);


// Parser 글로벌 변수들
static TokenType token; /* holds current token */

/* function prototypes for recursive calls */
static TreeNode* stmt_sequence(void);
static TreeNode* statement(void);
static TreeNode* if_stmt(void);
static TreeNode* repeat_stmt(void);
static TreeNode* assign_stmt(void);
static TreeNode* read_stmt(void);
static TreeNode* write_stmt(void);
static TreeNode* exp(void);
static TreeNode* simple_exp(void);
static TreeNode* term(void);
static TreeNode* factor(void);

/* 내가 만든 Parse 함수들 */
TreeNode* declaration_list(void);
TreeNode* declaration(void);

TreeNode* statement(void);
TreeNode* expression_stmt(void);
TreeNode* compound_stmt(void);
TreeNode* selection_stmt(void);
TreeNode* iteration_stmt(void);
TreeNode* return_stmt(void);


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
	switch (token) {
	case VAR: t = var_declaration(); break; // 변수 정의가 나오면
	case FUN: t = fun_declaration(); break; // 함수 정의가 나오면
	default: syntaxError("unexpected token -> ");
		printToken(token, tokenString);
		token = getToken();
		break;
	} /* end case */
	return t;
}

TreeNode* type_sepcifier(void)
{
	TreeNode* t = NULL;
	switch (token) {
	case INT: match(INT); break;
	case VOID: match(VOID); break;
	default: syntaxError("unexpected token -> ");
		printToken(token, tokenString);
		token = getToken();
		break;
	}
	return t;
}


TreeNode* statement(void)
{
	TreeNode* t = NULL;
	switch (token) {
	case ID:
	case NUM:
	case LBRAC:
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

}

TreeNode* compound_stmt(void)
{

}

TreeNode* selection_stmt(void)
{
	TreeNode* t = newStmtNode(IfK);
	match(IF);
	match(LBRAC);	// (
	if (t != NULL) t->child[0] = exp();
	match(RBRAC);	// )
	if (t != NULL) t->child[1] = statement();
	if (token == ELSE) {
		match(ELSE);
		if (t != NULL) t->child[2] = statement();
	}
	return t;
}

TreeNode* iteration_stmt(void)
{

}

TreeNode* return_stmt(void)
{

}


TreeNode* stmt_sequence(void)
{
	TreeNode* t = statement();
	TreeNode* p = t;
	while ((token != ENDFILE) && (token != END) &&
		(token != ELSE) && (token != UNTIL))
	{
		TreeNode* q;
		match(SEMI);
		q = statement();
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

TreeNode* statement(void)
{
	TreeNode* t = NULL;
	switch (token) {
	case IF: t = if_stmt(); break;
	case REPEAT: t = repeat_stmt(); break;
	case ID: t = assign_stmt(); break;
	case READ: t = read_stmt(); break;
	case WRITE: t = write_stmt(); break;
	default: syntaxError("unexpected token -> ");
		printToken(token, tokenString);
		token = getToken();
		break;
	} /* end case */
	return t;
}

TreeNode* if_stmt(void)
{
	TreeNode* t = newStmtNode(IfK);
	match(IF);
	if (t != NULL) t->child[0] = exp();
	match(THEN);
	if (t != NULL) t->child[1] = stmt_sequence();
	if (token == ELSE) {
		match(ELSE);
		if (t != NULL) t->child[2] = stmt_sequence();
	}
	match(END);
	return t;
}

TreeNode* repeat_stmt(void)
{
	TreeNode* t = newStmtNode(RepeatK);
	match(REPEAT);
	if (t != NULL) t->child[0] = stmt_sequence();
	match(UNTIL);
	if (t != NULL) t->child[1] = exp();
	return t;
}

TreeNode* assign_stmt(void)
{
	TreeNode* t = newStmtNode(AssignK);
	if ((t != NULL) && (token == ID))
		t->attr.name = copyString(tokenString);
	match(ID);
	match(ASSIGN);
	if (t != NULL) t->child[0] = exp();
	return t;
}

TreeNode* read_stmt(void)
{
	TreeNode* t = newStmtNode(ReadK);
	match(READ);
	if ((t != NULL) && (token == ID))
		t->attr.name = copyString(tokenString);
	match(ID);
	return t;
}

TreeNode* write_stmt(void)
{
	TreeNode* t = newStmtNode(WriteK);
	match(WRITE);
	if (t != NULL) t->child[0] = exp();
	return t;
}

TreeNode* exp(void)
{
	TreeNode* t = simple_exp();
	if ((token == LT) || (token == EQ)) {
		TreeNode* p = newExpNode(OpK);
		if (p != NULL) {
			p->child[0] = t;
			p->attr.op = token;
			t = p;
		}
		match(token);
		if (t != NULL)
			t->child[1] = simple_exp();
	}
	return t;
}

TreeNode* simple_exp(void)
{
	TreeNode* t = term();
	while ((token == PLUS) || (token == MINUS))
	{
		TreeNode* p = newExpNode(OpK);
		if (p != NULL) {
			p->child[0] = t;
			p->attr.op = token;
			t = p;
			match(token);
			t->child[1] = term();
		}
	}
	return t;
}

TreeNode* term(void)
{
	TreeNode* t = factor();
	while ((token == TIMES) || (token == OVER))
	{
		TreeNode* p = newExpNode(OpK);
		if (p != NULL) {
			p->child[0] = t;
			p->attr.op = token;
			t = p;
			match(token);
			p->child[1] = factor();
		}
	}
	return t;
}

TreeNode* factor(void)
{
	TreeNode* t = NULL;
	switch (token) {
	case NUM:
		t = newExpNode(ConstK);
		if ((t != NULL) && (token == NUM))
			t->attr.val = atoi(tokenString);
		match(NUM);
		break;
	case ID:
		t = newExpNode(IdK);
		if ((t != NULL) && (token == ID))
			t->attr.name = copyString(tokenString);
		match(ID);
		break;
	case LPAREN:
		match(LPAREN);
		t = exp();
		match(RPAREN);
		break;
	default:
		syntaxError("unexpected token -> ");
		printToken(token, tokenString);
		token = getToken();
		break;
	}
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
	t = stmt_sequence();
	if (token != ENDFILE)
		syntaxError("Code ends before file\n");
	return t;
}


/* Function newStmtNode creates a new statement
 * node for syntax tree construction
 */

TreeNode* newDecNode(DeclarationKind kind)
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

/* procedure printTree prints a syntax tree to the
 * listing file using indentation to indicate subtrees
 */
void printTree(TreeNode* tree)
{
	int i;
	INDENT;
	while (tree != NULL) {
		printSpaces();
		if (tree->nodekind == StmtK)
		{
			switch (tree->kind.stmt) {
			case IfK:
				fprintf(listing, "If\n");
				break;
			case RepeatK:
				fprintf(listing, "Repeat\n");
				break;
			case AssignK:
				fprintf(listing, "Assign to: %s\n", tree->attr.name);
				break;
			case ReadK:
				fprintf(listing, "Read: %s\n", tree->attr.name);
				break;
			case WriteK:
				fprintf(listing, "Write\n");
				break;
			default:
				fprintf(listing, "Unknown ExpNode kind\n");
				break;
			}
		}
		else if (tree->nodekind == ExpK)
		{
			switch (tree->kind.exp) {
			case OpK:
				fprintf(listing, "Op: ");
				printToken(tree->attr.op, "\0");
				break;
			case ConstK:
				fprintf(listing, "Const: %d\n", tree->attr.val);
				break;
			case IdK:
				fprintf(listing, "Id: %s\n", tree->attr.name);
				break;
			default:
				fprintf(listing, "Unknown ExpNode kind\n");
				break;
			}
		}
		else fprintf(listing, "Unknown node kind\n");
		for (i = 0; i < MAXCHILDREN; i++)
			printTree(tree->child[i]);
		tree = tree->sibling;
	}
	UNINDENT;
}
