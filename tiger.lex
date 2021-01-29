%{
	/* Lab2 Attention: You are only allowed to add code in this file and start at Line 26.*/
#include <string.h>
#include <ctype.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "y.tab.h"
#include "errormsg.h"

	int charPos = 1;

	int yywrap(void)
	{
		charPos = 1;
		return 1;
	}

	void adjust(void)
	{
		EM_tokPos = charPos;
		charPos += yyleng;
	}

	/*
	* Please don't modify the lines above.
	* You can add C declarations of your own below.
	*/

	/* @function: getstr
	 * @input: a string literal
	 * @output: the string value for the input which has all the escape sequences
	 * translated into their meaning.
	 */
	char *getstr(const char *str)
	{
		return NULL;
	}

	int commentLen = 0;
	char resultString[2048];
	int resultLen = 0;

%}
/* You can add lex definitions here. */
%Start COMMENT STR
%%
	/*
	* Below is an example, which you can wipe out
	* and write reguler expressions and actions of your own.
	*/

<INITIAL>" "|"\t" {adjust();}
<INITIAL>"\n" {adjust(); EM_newline(); continue;}

<INITIAL>"/*" {adjust(); commentLen++; BEGIN COMMENT;}
<COMMENT>"/*" {adjust(); commentLen++;}
<COMMENT>"*/" {adjust(); commentLen--; if (commentLen == 0) {BEGIN INITIAL;}}
<COMMENT>. {adjust();}
<COMMENT>"\n" {adjust(); EM_newline();}

<INITIAL>[0-9]+ {adjust(); yylval.ival=atoi(yytext);return INT;}
<INITIAL>"," {adjust(); return COMMA;}
<INITIAL>":" {adjust(); return COLON;}
<INITIAL>";" {adjust(); return SEMICOLON;}
<INITIAL>"(" {adjust(); return LPAREN;}
<INITIAL>")" {adjust(); return RPAREN;}
<INITIAL>"[" {adjust(); return LBRACK;}
<INITIAL>"]" {adjust(); return RBRACK;}
<INITIAL>"{" {adjust(); return LBRACE;}
<INITIAL>"}" {adjust(); return RBRACE;}
<INITIAL>"." {adjust(); return DOT;}
<INITIAL>"+" {adjust(); return PLUS;}
<INITIAL>"-" {adjust(); return MINUS;}
<INITIAL>"*" {adjust(); return TIMES;}
<INITIAL>"/" {adjust(); return DIVIDE;}
<INITIAL>"=" {adjust(); return EQ;}
<INITIAL>"<>" {adjust(); return NEQ;}
<INITIAL>"<" {adjust(); return LT;}
<INITIAL>"<=" {adjust(); return LE;}
<INITIAL>">" {adjust(); return GT;}
<INITIAL>">=" {adjust(); return GE;}
<INITIAL>"&" {adjust(); return AND;}
<INITIAL>"|" {adjust(); return OR;}
<INITIAL>":=" {adjust(); return ASSIGN;}
<INITIAL>"array" {adjust(); return ARRAY;}
<INITIAL>"if" {adjust(); return IF;}
<INITIAL>"then" {adjust(); return THEN;}
<INITIAL>"else" {adjust(); return ELSE;}
<INITIAL>"while" {adjust(); return WHILE;}
<INITIAL>"for" {adjust(); return FOR;}
<INITIAL>"to" {adjust(); return TO;}
<INITIAL>"do" {adjust(); return DO;}
<INITIAL>"let" {adjust(); return LET;}
<INITIAL>"in" {adjust(); return IN;}
<INITIAL>"end" {adjust(); return END;}
<INITIAL>"of" {adjust(); return OF;}
<INITIAL>"break" {adjust(); return BREAK;}
<INITIAL>"nil" {adjust(); return NIL;}
<INITIAL>"function" {adjust(); return FUNCTION;}
<INITIAL>"var" {adjust(); return VAR;}
<INITIAL>"type" {adjust(); yylval.sval=String(yytext); return TYPE;}
<INITIAL>[a-zA-Z][a-zA-Z0-9_]* {adjust(); yylval.sval=String(yytext); return ID;}

<INITIAL>\" {adjust(); resultLen = 0; BEGIN STR;}
	/* handle ^\ */
<STR>\\n {charPos += yyleng; resultString[resultLen] = '\n'; resultLen++;}
<STR>\\t {charPos += yyleng; resultString[resultLen] = '\t'; resultLen++;}
<STR>\\\\ {charPos += yyleng; resultString[resultLen] = '\\'; resultLen++;}
<STR>\\\" {charPos += yyleng; resultString[resultLen] = '"'; resultLen++;}
<STR>\\[0-9]{3} {charPos += yyleng; resultString[resultLen] = atoi(yytext + 1); resultLen++;}
<STR>\\\^[A-Z] {charPos += yyleng; resultString[resultLen] = yytext[2] - 'A' + 1; resultLen++;}
<STR>\\[\t\n\f ]+\\ {charPos += yyleng;}

<STR>\" {charPos += yyleng; resultString[resultLen] = '\0'; yylval.sval = String(resultString); BEGIN INITIAL; return STRING;}

<STR>. {charPos += yyleng; strcpy(resultString + resultLen, yytext); resultLen += yyleng;}
<STR>"\n" {charPos += yyleng; strcpy(resultString + resultLen, yytext); resultLen += yyleng;}

<INITIAL>. {adjust(); EM_error(charPos, yytext);}
