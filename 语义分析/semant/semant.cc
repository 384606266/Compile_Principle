#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"

extern int semant_debug;
extern char *curr_filename;

static ostream& error_stream = cerr;
static int semant_errors = 0;
static Decl curr_decl = 0;
static bool is_in_loop = 0; 
static bool is_returned = 0;

typedef SymbolTable<Symbol, Symbol> ObjectEnvironment; // name, type
ObjectEnvironment objectEnv;        //变量表
typedef SymbolTable<Symbol, Decl> functionTable; 
functionTable funcTab;        //函数表

///////////////////////////////////////////////
// helper func
///////////////////////////////////////////////


static ostream& semant_error() {
    semant_errors++;
    return error_stream;
}

static ostream& semant_error(tree_node *t) {
    error_stream << t->get_line_number() << ": ";
    return semant_error();
}

static ostream& internal_error(int lineno) {
    error_stream << "FATAL:" << lineno << ": ";
    return error_stream;
}

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////

static Symbol 
    Int,
    Float,
    String,
    Bool,
    Void,
    Main,
    print
    ;

bool isValidCallName(Symbol type) {
    return type != (Symbol)print;
}

bool isValidTypeName(Symbol type) {
    return type != Void;
}

//
// Initializing the predefined symbols.
//

static void initialize_constants(void) {
    // 4 basic types and Void type
    Bool        = idtable.add_string("Bool");
    Int         = idtable.add_string("Int");
    String      = idtable.add_string("String");
    Float       = idtable.add_string("Float");
    Void        = idtable.add_string("Void");  
    // Main function
    Main        = idtable.add_string("main");

    // classical function to print things, so defined here for call.
    print       = idtable.add_string("printf");
}

/*
    TODO :
    you should fill the following function defines, so that semant() can realize a semantic 
    analysis in a recursive way. 
    Of course, you can add any other functions to help.
*/
//是否同类型
static bool sameType(Symbol name1, Symbol name2) {
    return strcmp(name1->get_string(), name2->get_string()) == 0;
}
//引入函数
static void install_calls(Decls decls) {
    objectEnv.enterscope();
    funcTab.enterscope();
    funcTab.addid(print,new Decl());        //将默认函数print加入函数表

    for(int i = decls->first(); decls->more(i); i = decls->next(i)){
        if(decls->nth(i)->isCallDecl()){
            curr_decl = decls->nth(i);
            if (funcTab.probe(curr_decl->getName())) 
                semant_error(curr_decl)<<"function "<<curr_decl->getName()<<" has been defined."<< endl;
            else 
                funcTab.addid(curr_decl->getName(), new Decl(curr_decl));
        }
    }
}
//引入全局变量
static void install_globalVars(Decls decls) {
    bool is_defined;
    for(int i = decls->first(); decls->more(i); i = decls->next(i)){
        curr_decl = decls->nth(i);
        if (!curr_decl->isCallDecl()){
            if (funcTab.probe(curr_decl->getName())) 
                semant_error(curr_decl)<<"Variable "<<curr_decl->getName()<<" has been defined."<<endl;
            else if (!isValidTypeName(curr_decl->getType()))
                semant_error(curr_decl)<<"var "<<curr_decl->getName()<<
                " cannot be of type Void. Void can just be used as return type."<< endl;
            else 
                objectEnv.addid(curr_decl->getName(), new Symbol(curr_decl->getType()));
        }
    }
}
//检查函数声明
static void check_calls(Decls decls) {
    for(int i = decls->first(); decls->more(i); i = decls->next(i)){
        curr_decl = decls->nth(i);
        if (curr_decl->isCallDecl())    curr_decl->check();
    }
}
//检查main函数
static void check_main() {
    if (funcTab.lookup(Main) == NULL){
        semant_error()<<"main function is not defined."<< endl;
        return;
    }
    //curr_decl = static_cast<CallDecl>(funcTab.lookup(Main));
    if (((*funcTab.lookup(Main))->getVariables())->more(0)) 
        semant_error(*(funcTab.lookup(Main)))<<"main function should not have any parameters."<< endl;
    if (isValidTypeName((*funcTab.lookup(Main))->getType())) 
        semant_error(*(funcTab.lookup(Main)))<<"main function should have return type Void."<< endl;
}
//检查变量
void VariableDecl_class::check() {
    if (objectEnv.probe(variable->getName()))
        semant_error(variable)<<"Variable "<<variable->getName()<<" has been defined."<< endl;
    else if (!isValidTypeName(variable->getType())) 
        semant_error(variable)<<"invalid type Void."<< endl;
    else 
        objectEnv.addid(variable->getName(), new Symbol(variable->getType()));
}
//检查函数参数
void CallDecl_class::check() {
    objectEnv.enterscope();
    is_returned = false;
    for (int i = paras->first(); paras->more(i); i = paras->next(i)){
        Variable curr_var = paras->nth(i);
        if (!isValidTypeName(curr_var->getType()))
            semant_error(curr_var)<<"function "<<this->getName()<<"'th parameter type is invalid."<< endl;
        else if (objectEnv.probe(curr_var->getName()))
            semant_error(curr_var)<<"parameter name confilct."<< endl;
        else 
            objectEnv.addid(curr_var->getName(), new Symbol(curr_var->getType()));
        if (i >= 6)semant_error(this)<<"function "<<this->getName()<<" has over 6 parameters."<< endl;
    }
    (this->getBody())->check(this->getType());
    if (!is_returned) semant_error(this)<<"function "<<this->getName()<<" has no return"<< endl;    //no return 
    objectEnv.exitscope();
}
//检查语句块
void StmtBlock_class::check(Symbol type) {
    objectEnv.enterscope();
    for (int i = vars->first(); vars->more(i); i = vars->next(i))  
        vars->nth(i)->check();

    for (int i = stmts->first(); stmts->more(i); i = stmts->next(i)){       
        stmts->nth(i)->check(type);        
    }
    objectEnv.exitscope();
}
//If
void IfStmt_class::check(Symbol type) {
    if (!sameType(condition->checkType(), Bool))
        semant_error(this)<<"condition must be Bool"<< endl;
    //then
    objectEnv.enterscope();
    thenexpr->check(type);
    objectEnv.exitscope();
    //else
    objectEnv.enterscope();
    elseexpr->check(type);
    objectEnv.exitscope();
}
//While
void WhileStmt_class::check(Symbol type) {
    if (!sameType(condition->checkType(), Bool))
        semant_error(this)<<"condition must be Bool"<< endl;

    is_in_loop = true;
    objectEnv.enterscope();
    body->check(type);
    objectEnv.exitscope();
    is_in_loop = false;
}
//For
void ForStmt_class::check(Symbol type) {
    if (!initexpr->is_empty_Expr())
        initexpr->checkType();

    if (!condition->is_empty_Expr()){
        if (!sameType(condition->checkType(), Bool))
            semant_error(this)<<"condition must be Bool"<< endl;
    }
    if (!loopact->is_empty_Expr())
        loopact->checkType();

    is_in_loop = true;
    objectEnv.enterscope();
    body->check(type);
    objectEnv.exitscope();
    is_in_loop = false;
}
//Return
void ReturnStmt_class::check(Symbol type) {
    is_returned = true;

    if(value->is_empty_Expr()){
        if(!sameType(type, Void)) 
            semant_error(this) << "Returns Void , but need " << type->get_string() <<endl;
    }
    else{
        if (!sameType(value->checkType(), type)) 
            semant_error(this)<<"Returns "<<value->checkType()<<" , but need " << type->get_string() <<endl;
    }
}
//Continue
void ContinueStmt_class::check(Symbol type) {
    if(!is_in_loop)
        semant_error(this) << "continue must be in a loop"<<endl;
}
//Break
void BreakStmt_class::check(Symbol type) {
    if(!is_in_loop)
        semant_error(this) << "break must be in a loop"<<endl;
}

//检查函数调用
Symbol Call_class::checkType(){
    if (!isValidCallName(name)) {       //内置print函数
        if (!actuals->more(0))
            semant_error(this)<<"function printf must have at least one parameter."<< endl;

        else{
            for (int i = actuals->first(); actuals->more(i); i = actuals->next(i)) 
                actuals->nth(i)->checkType();
            
            if (!sameType((actuals->nth(0))->getType(), String)) 
                semant_error(this)<<"function printf must have string as first parameter."<< endl;
        }
        setType(Void);
        return type;
    }
    if (funcTab.probe(name) == NULL){
        semant_error(this)<<"Function "<<name<<" has not been defined yet."<< endl;
        setType(Void);
        return type;
    }

    Decl curr_decl = *(funcTab.probe(name));
    Variables curr_parameters = curr_decl->getVariables();

    if (actuals->len() != curr_parameters->len()) 
        semant_error(this)<<"Function "<<name<<" call parameters wrong."<< endl;  
    
    for (int i = 0; actuals->more(i) && curr_parameters->more(i); i++){
        if (!sameType(actuals->nth(i)->checkType(),curr_parameters->nth(i)->getType())){
            semant_error(this)<<"Function "<<name<<", type "<< actuals->nth(i)->checkType() <<" of parameter "<<
            curr_parameters->nth(i)->getName() << " does not conform to declared type "<<curr_parameters->nth(i)->getType()<<"."<< endl;
            break;
        }
        if (actuals->more(i+1) ^ curr_parameters->more(i+1)) {
            semant_error(this)<<"Function "<<name<<" call parameters wrong."<< endl;
            break;
        }
    }
    setType(curr_decl->getType());
    return type;
}
//  参数检查
Symbol Actual_class::checkType(){
    setType(expr->checkType());
    return type;
}
//  "="
Symbol Assign_class::checkType(){
    Symbol righttype = value->checkType();

    if (objectEnv.lookup(lvalue))
        setType(*(objectEnv.lookup(lvalue)));
    else{
        semant_error(this)<<"Variable "<<lvalue->get_string()<<" not defined."<< endl;
        setType(Void);
        return type;
    }

    if (!sameType(righttype, type))
        semant_error(this)<<"can`t assign "<<righttype<<" to "<<type<<"."<< endl;
    return type;
}
//  "+"
Symbol Add_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    
    if((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))){
        // ERROR: Non-Int/Float Operand of '+'
        semant_error(this) << "Cannot add a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }

    if(sameType(type1, Int) && sameType(type2, Int)) {
        setType(Int);
    } else {
        setType(Float);
    }
    return type;
}
//  "-"
Symbol Minus_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    
    if((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))){
        // ERROR: Non-Int/Float Operand of '-'
        semant_error(this) << "Cannot minus a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }

    if(sameType(type1, Int) && sameType(type2, Int)) {
        setType(Int);
    } else {
        setType(Float);
    }
    return type;
}
//  "*"
Symbol Multi_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    
    if((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))){
        // ERROR: Non-Int/Float Operand of '*'
        semant_error(this) << "Cannot multi a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }

    if(sameType(type1, Int) && sameType(type2, Int)) {
        setType(Int);
    } else {
        setType(Float);
    }
    return type;
}
//除法，整数除法的返回值有疑问
Symbol Divide_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    
    if((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))){
        // ERROR: Non-Int/Float Operand of '/'
        semant_error(this) << "Cannot divide a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }

    if(sameType(type1, Int) && sameType(type2, Int)) {
        setType(Int);     //整数和整数相除的结果是否应设为浮点数？
    } else {
        setType(Float);
    }
    return type;
}
//  "%"
Symbol Mod_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    
    if(sameType(type1, Int) && sameType(type2, Int)) {
        setType(Int);
        return type;
    } else{
        semant_error(this) << "Cannot mod a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }
}
//  "-"取负
Symbol Neg_class::checkType(){
    Symbol type1 = e1->checkType();

    if(sameType(type1, Int)){
        setType(Int);
        return type;
    }
    if(sameType(type1, Float)){
        setType(Float);
        return type;
    }
    
    semant_error(this) << "Neg must be int or Float, not a " << type1->get_string() << endl;
    setType(Void);
    return type;
}
//  "<"
Symbol Lt_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    
    if((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))){
        // ERROR: Non-Int/Float Operand of '<'
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }

    setType(Bool);
    return type;
}
//  "<="
Symbol Le_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    
    if((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))){
        // ERROR: Non-Int/Float Operand of '<='
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }

    setType(Bool);
    return type;
}
//  "==" 允许bool
Symbol Equ_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    
    if((!sameType(type1, Int) && !sameType(type1, Float) && !sameType(type1, Bool)) || (!sameType(type2, Int) && !sameType(type2, Float) && !sameType(type2, Bool))){
        // ERROR: Non-Int/Float Operand of '=='
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }
    
    if((sameType(type1, Int) && sameType(type2, Bool)) || (sameType(type1, Bool) && sameType(type2, Int))) {
        // ERROR: cannot compare Int==Bool
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        setType(Void);
        return type;        
    }

    if((sameType(type1, Float) && sameType(type2, Bool)) || (sameType(type1, Bool) && sameType(type2, Float))) {
        // ERROR: cannot compare Float==Bool
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        setType(Void);
        return type;        
    }

    setType(Bool);
    return type;
}
//  "!=" 允许bool
Symbol Neq_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    
    if((!sameType(type1, Int) && !sameType(type1, Float) && !sameType(type1, Bool)) || (!sameType(type2, Int) && !sameType(type2, Float) && !sameType(type2, Bool))){
        // ERROR: Non-Int/Float Operand of '!='
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }
    
    if((sameType(type1, Int) && sameType(type2, Bool)) || (sameType(type1, Bool) && sameType(type2, Int))) {
        // ERROR: cannot compare Int!=Bool
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        setType(Void);
        return type;        
    }

    if((sameType(type1, Float) && sameType(type2, Bool)) || (sameType(type1, Bool) && sameType(type2, Float))) {
        // ERROR: cannot compare Float!=Bool
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        setType(Void);
        return type;        
    }

    setType(Bool);
    return type;
}
//  ">="
Symbol Ge_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    
    if((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))){
        // ERROR: Non-Int/Float Operand of '>='
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }

    setType(Bool);
    return type;
}
//  ">"
Symbol Gt_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    
    if((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))){
        // ERROR: Non-Int/Float Operand of '>'
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }

    setType(Bool);
    return type;
}
//  "&&" bool
Symbol And_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if(sameType(type1, Bool) && sameType(type2, Bool)){
        setType(Bool);
        return type;
    }
    else{
        // ERROR: Non-Bool Operand of '&&'
        semant_error(this) << "Cannot use &&  between a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }
}
//  "||" bool
Symbol Or_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if(sameType(type1, Bool) && sameType(type2, Bool)){
        setType(Bool);
        return type;
    }
    else{
        // ERROR: Non-Bool Operand of '||'
        semant_error(this) << "Cannot use ||  between a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }
}
//  "^" bool类型的异或      Int类型的按位异或    
Symbol Xor_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if(sameType(type1, Bool) && sameType(type2, Bool)){
        setType(Bool);
        return type;
    }
    if(sameType(type1, Int) && sameType(type2, Int)){
        setType(Int);
        return type;
    }
    else{
        // ERROR: Non-Bool_Int Operand of '^'
        semant_error(this) << "Cannot use ^ between a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }
}
//  "!" bool类型
Symbol Not_class::checkType(){
    Symbol type1 = e1->checkType();

    if(sameType(type1, Bool)){
        setType(Bool);
        return type;
    }
    else{
        // ERROR: Non-Bool Operand of '!'
        semant_error(this) << "Cannot use !(bool)  with a " << type1->get_string() << endl;
        setType(Void);
        return type;
    }    
}
//按位与，Int类型的 &
Symbol Bitand_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if(sameType(type1, Int) && sameType(type2, Int)){
        setType(Int);
        return type;
    }
    else{
        // ERROR: Non-Int Operand of '&'
        semant_error(this) << "Cannot use & between a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }
}
//按位或，Int类型的 |
Symbol Bitor_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if(sameType(type1, Int) && sameType(type2, Int)){
        setType(Int);
        return type;
    }
    else{
        // ERROR: Non-Int Operand of '|'
        semant_error(this) << "Cannot use | between a " << type1->get_string() << " and a " << type2->get_string() << endl;
        setType(Void);
        return type;
    }
}
//按位取反，Int类型的 ~
Symbol Bitnot_class::checkType(){
    Symbol type1 = e1->checkType();

    if(sameType(type1, Int)){
        setType(Int);
        return type;
    }
    else{
        // ERROR: Non-Int Operand of '~'
        semant_error(this) << "Cannot use ~ with a " << type1->get_string() << endl;
        setType(Void);
        return type;
    }
}

Symbol Const_int_class::checkType(){
    setType(Int);
    return type;
}

Symbol Const_string_class::checkType(){
    setType(String);
    return type;
}

Symbol Const_float_class::checkType(){
    setType(Float);
    return type;
}

Symbol Const_bool_class::checkType(){
    setType(Bool);
    return type;
}

Symbol Object_class::checkType(){
    if(!objectEnv.lookup(var)) {
        // ERROR: undefined object
        semant_error(this) << "object " << var->get_string() << " has not been defined." << endl;
        return Void;
    }
    Symbol object_type = *objectEnv.lookup(var);
    setType(object_type);
    return object_type;
}

Symbol No_expr_class::checkType(){
    setType(Void);
    return getType();
}

void Program_class::semant() {
    initialize_constants();         //预定义常量
    install_calls(decls);           //
    check_main();
    install_globalVars(decls);
    check_calls(decls);
    
    if (semant_errors > 0) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
    objectEnv.exitscope();
    funcTab.exitscope();
}



