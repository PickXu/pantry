package ccomp.parser;

import beaver.Symbol;
import beaver.Scanner;

import static ccomp.parser.CParser.Terminals.*;
import ccomp.parser_hw.CCompiler;
import java.util.*;

%%

%class CScanner
%public
%extends Scanner
%function nextToken
%type Symbol
%yylexthrow Scanner.Exception
%eofval{
  return token(EOF, "end-of-file");
%eofval}
%unicode
%line
%column
%{
  private Symbol token(short id)
  {
  	String got = yytext();
  	
  	if (typeDefList != null && typeDefCBraces.isEmpty() && typeDefSQBraces.isEmpty()){
  	  typeDefList.add(got);
  	}
    return new Symbol(id, yyline + 1, yycolumn + 1, yylength(), got);
  }

  private Symbol token(short id, Object value)
  {
    return new Symbol(id, yyline + 1, yycolumn + 1, yylength(), value);
  }
  
  private Collection<String> typenames = new CCompiler(null).getDefinedTypeNames(); //not backed! free to add stuff.
  private ArrayList<String> typeDefList = null;
  private short check_type(){
    String id = yytext();
    //For now, just check for built-in types. A working type-def system will come later.
    if (typenames.contains(id)){
      return TYPE_NAME;
    } else {
      return IDENTIFIER;
    }
  }
  /** Start listening for typedef tokens **/
  private void beginTypeDef(){
  	typeDefList = new ArrayList<String>();
  }
  private Stack<Object> typeDefCBraces = new Stack();
  private Stack<Object> typeDefSQBraces = new Stack();
  private void pushTypeDefCBrace(){
  	if (typeDefList != null){
  		typeDefCBraces.push(null);
  	}
  }
  private void pushTypeDefSQBrace(){
    if (typeDefList != null){
      typeDefSQBraces.push(null);
    }
  }
  private void popTypeDefCBrace(){
  	if (typeDefList != null){
  		typeDefCBraces.pop();
  	}
  }
  private void popTypeDefSQBrace(){
    if (typeDefList != null){
      typeDefSQBraces.pop();
    }
  }
  private void endTypeDef(){
  	if (typeDefList != null){
      if (!typeDefCBraces.isEmpty()){
        return; //Ignore semicolon nested inside cbraces (i.e. typedef structs)
      }
      if (!typeDefSQBraces.isEmpty()){
        throw new RuntimeException("Assertion error - semicolon inside square braces in typedef");
      }
  	  String newType = typeDefList.get(typeDefList.size()-1);
  	  typenames.add(newType);
  	  //System.out.println("New type: "+newType);
      typeDefList = null;
  	}
  }
  
%}

/* Adapted from http://www.lysator.liu.se/c/ANSI-C-grammar-y.html

In 1985, Jeff Lee published his Yacc grammar (which is accompanied by a matching Lex specification) for the April 30, 1985 draft version of the ANSI C standard.  Tom Stockfisch reposted it to net.sources in 1987; that original, as mentioned in the answer to question 17.25 of the comp.lang.c FAQ, can be ftp'ed from ftp.uu.net, file usenet/net.sources/ansi.c.grammar.Z.
Jutta Degener, 1995 

Unfortunately, I am not starting from a grammar for C99, so I may need to add some features.

*/

D =                      [0-9]
L =                      [a-zA-Z_]
H =                      [a-fA-F0-9]
E =                      [Ee][+-]?{D}+
FS =                     (f|F|l|L)
IS =                     (u|U|l|L)*
WhiteSpace =       [ \t\u000A\u000B\u000C\u000D\u0085\u2028\u2029\n\f]

/* Comment handling is modeled after JAVA, TODO: See if this is the same as C99 */ 

TraditionalComment = "/*" [^*] ~"*/" | "/*" "*"+ "/"
LineTerminator = \r|\n|\r\n
InputCharacter = [^\r\n]
EndOfLineComment = "//" {InputCharacter}* {LineTerminator}?

Comment = {TraditionalComment} | {EndOfLineComment}

%%

<YYINITIAL> {

  {Comment}           { /* ignore */ }
  {WhiteSpace}+     { /* ignore */ }


  "auto"      { return token(AUTO); }
  "break"      { return token(BREAK); }
  "case"      { return token(CASE); }
  "char"      { return token(CHAR); }
  "const"      { return token(CONST); }
  "continue"    { return token(CONTINUE); }
  "default"    { return token(DEFAULT); }
  "do"      { return token(DO); }
  "double"    { return token(DOUBLE); }
  "else"      { return token(ELSE); }
  "enum"      { return token(ENUM); }
  "extern"    { return token(EXTERN); }
  "float"      { return token(FLOAT); }
  "for"      { return token(FOR); }
  "goto"      { return token(GOTO); }
  "if"      { return token(IF); }
  "inline"        { return token(INLINE); }
  "_Noreturn"      { return token(NORETURN); }
  "int"      { return token(INT); }
  "long"      { return token(LONG); }
  "register"    { return token(REGISTER); }
  "return"    { return token(RETURN); }
  "short"      { return token(SHORT); }
  "signed"    { return token(SIGNED); }
  "sizeof"    { return token(SIZEOF); }
  "static"    { return token(STATIC); }
  "struct"    { return token(STRUCT); }
  "switch"    { return token(SWITCH); }
  "typedef"    { beginTypeDef(); return token(TYPEDEF); }
  "union"      { return token(UNION); }
  "unsigned"    { return token(UNSIGNED); }
  "void"      { return token(VOID); }
  "volatile"    { return token(VOLATILE); }
  "while"      { return token(WHILE); }
  
  {L}({L}|{D})*    { return token(check_type()); }
  
  0[xX]{H}+{IS}?    { return token(HEX_CONSTANT); }
  0{D}+{IS}?    { return token(OCTAL_CONSTANT); }
  {D}+{IS}?    { return token(DECIMAL_CONSTANT); }
  
  //???
  L?'(\\.|[^\\'])+'  { return token(CONSTANT); }
  
  //Floating point constants. 
  {D}+{E}{FS}?    { return token(FP_CONSTANT); }
  {D}*"."{D}+({E})?{FS}?  { return token(FP_CONSTANT); }
  {D}+"."{D}*({E})?{FS}?  { return token(FP_CONSTANT); }
  
  L?\"(\\.|[^\\\"])*\"  { return token(STRING_LITERAL); }
  
  "..."      { return token(ELLIPSIS); }
  ">>="      { return token(RIGHT_ASSIGN); }
  "<<="      { return token(LEFT_ASSIGN); }
  "+="      { return token(ADD_ASSIGN); }
  "-="      { return token(SUB_ASSIGN); }
  "*="      { return token(MUL_ASSIGN); }
  "/="      { return token(DIV_ASSIGN); }
  "%="      { return token(MOD_ASSIGN); }
  "&="      { return token(AND_ASSIGN); }
  "^="      { return token(XOR_ASSIGN); }
  "|="      { return token(OR_ASSIGN); }
  ">>"      { return token(RIGHT_OP); }
  "<<"      { return token(LEFT_OP); }
  "++"      { return token(INC_OP); }
  "--"      { return token(DEC_OP); }
  "->"      { return token(PTR_OP); }
  "&&"      { return token(AND_OP); }
  "||"      { return token(OR_OP); }
  "<="      { return token(LE_OP); }
  ">="      { return token(GE_OP); }
  "=="      { return token(EQ_OP); }
  "!="      { return token(NE_OP); }
  ";"      { endTypeDef(); return token(SEMICOLON); }
  ("{"|"<%")    { pushTypeDefCBrace(); return token(LEFT_CBRACE); }
  ("}"|"%>")    { try { return token(RIGHT_CBRACE); } finally { popTypeDefCBrace(); } }
  ","      { return token(COMMA); }
  ":"      { return token(COLON); }
  "="      { return token(ASSIGN); }
  "("      { return token(LEFT_PAREN); }
  ")"      { return token(RIGHT_PAREN); }
  ("["|"<:")    { pushTypeDefSQBrace(); return token(LEFT_SQBRACE); }
  ("]"|":>")    { try { return token(RIGHT_SQBRACE); } finally { popTypeDefSQBrace(); } }
  "."      { return token(PERIOD); }
  "&"      { return token(AMPERSAND); }
  "!"      { return token(NOT_OP); }
  "~"      { return token(NEG_OP); }
  "-"      { return token(MINUS_OP); }
  "+"      { return token(ADD_OP); }
  "*"      { return token(ASTERISK); }
  "/"      { return token(DIV_OP); }
  "%"      { return token(MOD_OP); }
  "<"      { return token(LEFT_ANGBRACE); }
  ">"      { return token(RIGHT_ANGBRACE); }
  "^"      { return token(CARET); }
  "|"      { return token(PIPE); }
  "?"      { return token(QUESTION); }
}

.|\n            { throw new Scanner.Exception("unexpected character '" + yytext() + "'"); }
