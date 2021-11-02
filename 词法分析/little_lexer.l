/*little_lexer.l*/
%{
    #include "stdio.h"
    #include "stdlib.h"
    #include "malloc.h"
    int line = 0;
    int words = 0;
    int chars = 0;
    FILE *fin;  //读取文件
%}
DIGIT [0-9]
INTEGER [1-9][0-9]*|0
DECIMAL {INTEGER}.{DIGIT}+
LETTER [a-zA-Z]
ID  [a-z]({LETTER}|_|{DIGIT})*
SYMBOL ("|"|"&"|"~"|"^"|"&&"|"||"|"!"|"%"|\+|\-|"*"|"/"|"<="|">="|"<"|">"|"=="|":="|"!="|"("|")"|"{"|"}"|"["|"]"|\;)
KEYWORD (fprintf|while|aafor|if|else|continue|break|return)
CAPTION ("#")(.)*
NAME   ^#\ ([0-9a-zA-Z]+\.sealpp)
FUNCTION ("func "){ID}
STDOUT    stdout|stderr
TYPEID (Int|Float|Bool|Void)
%%

\n {++line; ++chars;}        //遇到换行符，行数+1
{TYPEID} {printf("#%d: TYPEID %s \n",line,yytext);  chars+= yyleng;}    //匹配数据类型
{KEYWORD} {printf("#%d: KEYWORD %s \n",line,yytext);   chars+= yyleng;}  //匹配保留字
{STDOUT} {chars+=yyleng;}
{FUNCTION} {printf("#%d: %s \n",line,yytext);    chars+= yyleng;}   //匹配函数
{SYMBOL} {printf("#%d: %s \n",line,yytext);     chars+= yyleng;}        //匹配运算符(包括赋值)
{NAME} {printf("#name %s \n",yytext);     chars+= yyleng;}        //匹配名称
{CAPTION} {chars+=yyleng;}
{ID} {printf("#%d: OBJECTED %s \n",line,yytext);    chars+= yyleng;}    //匹配变量
{INTEGER} {printf("#%d: CONST %s\n",line,yytext);    chars+= yyleng;}     //整形常量(加法无法提取)
{DECIMAL} {printf("#%d: CONST %s\n",line,yytext);    chars+= yyleng;}     //浮点常量
("%f"|"%s"|"%lld")  {printf("#%d: %s \n",line,yytext);   chars+= yyleng;}
. {++chars;}

%%
int main(){
    yylex();
    fin = yyin;
    fseek(fin,0,SEEK_SET);
    char* str = (char*)malloc(sizeof(char) * chars+1);
    fread(str,chars+1,1,fin);
    int IsLastchar = 0;
    for(int i=0; i<chars; i++){
        if(str[i]!=' ' && str[i]!= '\t' && str[i]!= '\n'){
            IsLastchar = 1;
        }
        else if(IsLastchar == true){
            ++words;
            IsLastchar = 0;
        }
    }
    free(str);
    fclose(fin);
    printf("lines:%d,words:%d,chars:%d",line,words,chars);
    return 0;
}