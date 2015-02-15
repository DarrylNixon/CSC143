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
WHITESPACE      [ \n\f\r\t\v]
OBJECTID        [a-z][a-zA-Z0-9_]*
TYEPID          [A-Z][a-zA-Z0-9_]*

%%

 /*
  *  Nested comments
  */


 /*
  *  The multiple-character operators.
  */
{DARROW}		{ return (DARROW); }
{LE}        { return (LE); }
{ASSIGN}    { return (ASSIGN); }

 /*
  * Keywords are case-insensitive except for the values true and false,
  * which must begin with a lower-case letter.
  */
{CLASS}     { return (CLASS); }
{ELSE}      { return (CLASS); }
{FALSE}     { yylval.boolean = 0; return (BOOL_CONST); }
{FI}        { return (CLASS); }
{IF}        { return (CLASS); }
{IN}        { return (CLASS); }
{INHERITS}  { return (CLASS); }
{ISVOID}    { return (CLASS); }
{LET}       { return (CLASS); }
{LOOP}      { return (CLASS); }
{POOL}      { return (CLASS); }
{THEN}      { return (CLASS); }
{WHILE}     { return (CLASS); }
{CASE}      { return (CLASS); }
{ESAC}      { return (CLASS); }
{NEW}       { return (CLASS); }
{OF}        { return (CLASS); }
{NOT}       { return (CLASS); }
{TRUE}      { yylval.boolean = 1; return (BOOL_CONST); }
{OBJECTID}  { yylval.symbol = idtable.add_string(yytext,yyleng); return (OBJECTID); }
{TYPEID}  { yylval.symbol = idtable.add_string(yytext,yyleng); return (TYPEID); }

 /*
  *  String constants (C syntax)
  *  Escape sequence \c is accepted for all characters c. Except for 
  *  \n \t \b \f, the result is c.
  *
  */


%%
