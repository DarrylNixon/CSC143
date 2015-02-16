/*
 *  The scanner definition for COOL.
 */

/*
 *  Stuff enclosed in %{ %} in the first section is copied verbatim to the
 *  output, so headers and global definitions are placed here to be visible
 * to the code in the file.  Don't remove anything that was here initially
 */
%{
#include <cool-parse.h>
#include <stringtab.h>
#include <utilities.h>

/* The compiler assumes these identifiers. */
#define yylval cool_yylval
#define yylex  cool_yylex

/* Max size of string constants */
#define MAX_STR_CONST 1025
#define YY_NO_UNPUT   /* keep g++ happy */

extern FILE *fin; /* we read from this file */

/* define YY_INPUT so we read from the FILE fin:
 * This change makes it possible to use this scanner in
 * the Cool compiler.
 */
#undef YY_INPUT
#define YY_INPUT(buf,result,max_size) \
	if ( (result = fread( (char*)buf, sizeof(char), max_size, fin)) < 0) \
		YY_FATAL_ERROR( "read() in flex scanner failed");

char string_buf[MAX_STR_CONST]; /* to assemble string constants */
char *string_buf_ptr;

extern int curr_lineno;
extern int verbose_flag;

extern YYSTYPE cool_yylval;

/*
 *  Add Your own definitions here
 */
 
int comment_nest_level = 0;

%}

/*
 * Define names for regular expressions here.
 */

DARROW          =>
LE              <=
ASSIGN          <-
CLASS           [Cc][Ll][Aa][Ss][Ss]
ELSE            [Ee][Ll][Ss][Ee]
FALSE           f[Aa][Ll][Ss][Ee]
FI              [Ff][Ii]
IF              [Ii][Ff]
IN              [Ii][Nn]
INHERITS        [Ii][Nn][Hh][Ee][Rr][Ii][Tt][Ss]
ISVOID          [Ii][Ss][Vv][Oo][Ii][Dd]
LET             [Ll][Ee][Tt]
LOOP            [Ll][Oo][Oo][Pp]
POOL            [Pp][Oo][Oo][Ll]
THEN            [Tt][Hh][Ee][Nn]
WHILE           [Ww][Hh][Ii][Ll][Ee]
CASE            [Cc][Aa][Ss][Ee]
ESAC            [Ee][Ss][Aa][Cc]
NEW             [Nn][Ee][Ww]
OF              [Oo][Ff]
NOT             [Nn][Oo][Tt]
TRUE            t[Rr][Uu][Ee]
OBJECTID        [a-z][a-zA-Z0-9_]*
TYPEID          [A-Z][a-zA-Z0-9_]*
DIGIT           [0-9]+
OPERATOR       	[\+\/\-\*\=\<\.\~\,\;\:\(\)\@\{\}]

%x              COMMENT
%x              STRING
%x              BADSTRING

%%

 /*
  *  Nested comments
  */
"(*" {
  comment_nest_level = 1;
  BEGIN(COMMENT);
}
<COMMENT>{
  "(*" {
    comment_nest_level++;
    BEGIN(COMMENT);
  }
  \n { curr_lineno++; }
  . {}
  "*)" {
    comment_nest_level--;
    if (comment_nest_level == 0) {
      BEGIN(INITIAL);
    }
  }
  <<EOF>> {
    BEGIN(INITIAL);
    cool_yylval.error_msg = "EOF";
    return (ERROR);
  }
}
"*)" {
  cool_yylval.error_msg = "*)";
  return (ERROR);
}

--[^\n]*    {}

 /*
  *  The multiple-character operators.
  */
{DARROW}		{ return (DARROW); }
{LE}        { return (LE); }
{ASSIGN}    { return (ASSIGN); }
"/"         { return '/'; }
"+"         { return '+'; }
"-"         { return '-'; }
"*"         { return '*'; }
"("         { return '('; }
")"         { return ')'; }
"="         { return '='; }
"<"         { return '<'; }
"."         { return '.'; }
"~"         { return '~'; }
","         { return ','; }
";"         { return ';'; }
":"         { return ':'; }
"@"         { return '@'; }
"{"         { return '{'; }
"}"         { return '}'; }
{DIGIT}     { yylval.symbol = inttable.add_string(yytext,yyleng); return (INT_CONST); }
{OPERATOR}	{ return (yytext[0]); }

 /*
  * Keywords are case-insensitive except for the values true and false,
  * which must begin with a lower-case letter.
  */
{CLASS}     { return (CLASS); }
{ELSE}      { return (ELSE); }
{FALSE}     { yylval.boolean = 0; return (BOOL_CONST); }
{FI}        { return (FI); }
{IF}        { return (IF); }
{IN}        { return (IN); }
{INHERITS}  { return (INHERITS); }
{ISVOID}    { return (ISVOID); }
{LET}       { return (LET); }
{LOOP}      { return (LOOP); }
{POOL}      { return (POOL); }
{THEN}      { return (THEN); }
{WHILE}     { return (WHILE); }
{CASE}      { return (CASE); }
{ESAC}      { return (ESAC); }
{NEW}       { return (NEW); }
{OF}        { return (OF); }
{NOT}       { return (NOT); }
{TRUE}      { yylval.boolean = 1; return (BOOL_CONST); }
{OBJECTID}  { yylval.symbol = idtable.add_string(yytext,yyleng); return (OBJECTID); }
{TYPEID}    { yylval.symbol = idtable.add_string(yytext,yyleng); return (TYPEID); }

 /*
  *  String constants (C syntax)
  *  Escape sequence \c is accepted for all characters c. Except for 
  *  \n \t \b \f, the result is c.
  *
  */
\" {
  string_buf_ptr = string_buf;
  BEGIN(STRING);
}
<BADSTRING>.*[\""\n] {
  BEGIN(INITIAL);
}
<STRING>{
  "\"" {
    cool_yylval.symbol = stringtable.add_string(string_buf);
    *string_buf_ptr = 0;
    string_buf[0] = '\0';
    BEGIN(INITIAL);
    return (STR_CONST);
  }
  (\0|\\\0) {
    cool_yylval.error_msg = "null char in string";
    BEGIN(BADSTRING);
    return (ERROR);
  }
  \\\n {
    if (string_buf_ptr - string_buf >= MAX_STR_CONST) {
      cool_yylval.error_msg = "bad string length";
      return (ERROR);
    }
    curr_lineno++;
    *string_buf_ptr++ = ('\n');
  }
  \n {
    curr_lineno++;
    BEGIN(INITIAL);
    *string_buf_ptr = 0;
    string_buf[0] = '\0';
    cool_yylval.error_msg = "unterminated string constant";
    return (ERROR);
  }
  <<EOF>> {
    BEGIN(INITIAL);
    cool_yylval.error_msg = "EOF in string constant";
    return (ERROR);
  }
  \\n {
    if (string_buf_ptr - string_buf >= MAX_STR_CONST) {
      cool_yylval.error_msg = "bad string length";
      return (ERROR);
    }
    curr_lineno++;
    *string_buf_ptr++ = ('\n');
  }
  \\t {
    if (string_buf_ptr - string_buf >= MAX_STR_CONST) {
      cool_yylval.error_msg = "bad string length";
      return (ERROR);
    }
    curr_lineno++;
    *string_buf_ptr++ = ('\t');
  }
  \\b {
    if (string_buf_ptr - string_buf >= MAX_STR_CONST) {
      cool_yylval.error_msg = "bad string length";
      return (ERROR);
    }
    curr_lineno++;
    *string_buf_ptr++ = ('\b');
  }
  \\f {
    if (string_buf_ptr - string_buf >= MAX_STR_CONST) {
      cool_yylval.error_msg = "bad string length";
      return (ERROR);
    }
    curr_lineno++;
    *string_buf_ptr++ = ('\f');
  }
  \\. {
    if (string_buf_ptr - string_buf >= MAX_STR_CONST) {
      cool_yylval.error_msg = "bad string length";
      return (ERROR);
    }
    curr_lineno++;
    *string_buf_ptr++ = (strdup(yytext)[1]);
  }
  . {
    if (string_buf_ptr - string_buf >= MAX_STR_CONST) {
      cool_yylval.error_msg = "bad string length";
      return (ERROR);
    }
    curr_lineno++;
    *string_buf_ptr++ = (strdup(yytext)[0]);
  }
}


\n+            { curr_lineno += yyleng; }
[ \t\r\f\v]   ;
.             { cool_yylval.error_msg = yytext; return (ERROR); }

%%
