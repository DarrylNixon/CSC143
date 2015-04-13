

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"


extern int semant_debug;
extern char *curr_filename;

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
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}

ClassTable::ClassTable(Classes classesIn) : semant_errors(0) , error_stream(cerr) {
    install_basic_classes();
    classes = append_Classes(classes, classesIn);
    SymbolTable<Symbol,Entry> symTab;
    symTab.enterscope();
    symTab.addid(Object, Object);
    symTab.addid(Int, Int);
    symTab.addid(Str, Str);
    symTab.addid(IO, IO);
    symTab.addid(SELF_TYPE, SELF_TYPE);

    for (int i = classesIn->first(); classesIn->more(i); i = classesIn->next(i)) {
        Class_ c = classesIn->nth(i);

        if (symTab.lookup(c->getName()) != NULL) {
            semant_error(c) << "Name taken" << std::endl;
            return;
        }

        symTab.addid(c->getName(), c->getName());

        if (checkClass(c)) {
            semant_error(c) << "Cyclic dependency detected" << std::endl;
            return;
        }
    }

    if (getClass(Main) == NULL) {
        semant_error() << "Class main is not defined." << std::endl; //CHECK
        return;
    }
}

Class_ ClassTable::getClass(Symbol name)
{ 
    if (name == SELF_TYPE || name == self) {
        name = symbols.lookup(self);
    }

    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        Class_ c = classes->nth(i);
        if (name == c->getName()) 
            return c;
    }

    return NULL;
}

bool ClassTable::checkClass(Class_ c)
{
    int n = classes->len();
    int i = 0;
    Class_ parent = getClass(c->getParentName());
     
    if (parent == NULL)
    {
        semant_error(c) << "undefined parent" << std::endl; 
        return true;
    }

    while (parent->getName() != Object)
    {
        if (parent->getName() == Str 
                || parent->getName() == Bool 
                || parent->getName() == Int
                || parent->getName() == SELF_TYPE)
            semant_error(c) << "not allowed to derive from basic classes" << std::endl;

        i++;
        
        if (i > n) {
            return true;
        }
        
        parent = getClass(parent->getParentName());
        
        if (parent == NULL)
        {
            semant_error(c) << "undefined parent" << std::endl;   
            return true;
        }
    }

    return false;
}

Symbol ClassTable::getReturnType(Symbol c, Symbol m)
{
   
}

method_class* ClassTable::getMethod(Class_ c, Symbol m)
{
    for (int i = c->getFeatures()->first(); c->getFeatures()->more(i); i = c->getFeatures()->next(i))
    {
        method_class *method = dynamic_cast<method_class*>(c->getFeatures()->nth(i));
        
        if (method == NULL) {
            continue;
        }

        if (method->getName() == m)
        {
            return method;

        }
    }
    Class_ p = getClass(c->getParentName());
    return (p == NULL) ? NULL : getMethod(p, m);
}

bool ClassTable::isSubClass(Class_ class1, Class_ class2)
{
    if (class1->getName() == class2->getName()) return true;
    Class_ parent = getClass(class1->getParentName());
    if (parent) {
        return isSubClass(parent, class2);
    } else {
    return false;
    }
}

Symbol ClassTable::lowestUpperBound(Class_ class1, Class_ class2)
{
    if (class1->getName() == class2->getName()) return class1->getName();
    
    SymbolTable<Symbol, Entry> parents;
    parents.enterscope();
    parents.addid(class1->getName(), class1->getName());

    Class_ p1 = getClass(class1->getParentName());

    // add all of class1's parents to a symbol table
    for (Class_ i = getClass(class1->getParentName()); i != NULL; i = getClass(i->getParentName())) {
        parents.addid(i->getName(), i->getName());
    }
    // check class2's parents against symbol table, return if found
    for (Class_ j = class2; j != NULL; j = getClass(j->getParentName())) {
        if (parents.lookup(j->getName()) != NULL) {
            return j->getName();
        }
    }
    // shouldn't ever be reached but warnings suck
    return Object;
}

void ClassTable::publishVariables(Class_ class_)
{
    Features features = class_->getFeatures();
    for (int i = features->first(); features->more(i); i = features->next(i))
    {
        attr_class *attr = dynamic_cast<attr_class*>(features->nth(i));
        if (attr == NULL) continue;
        attr->publish(this);
    }
    if (Class_ p = getClass(class_->getParentName())) publishVariables(p);
}

void ClassTable::publishVariables(method_class* m)
{
    
}

void method_class::publish(ClassTable *classtable)
{
    SymbolTable<Symbol, Entry> params;
    params.enterscope();

    for (int i = formals->first(); formals->more(i); i = formals->next(i))
    {
        Formal_class *formal = formals->nth(i);

        if (params.lookup(formal->getName()) != NULL)
        {
            classtable->semant_error(classtable->getCurrentClass()) << 
                "Duplicated parameter name " << formal->getName() 
                << " in method " << name << std::endl;
            return; 
        }

        params.addid(formal->getName(), formal->getName());

        formal->publish(classtable);
    }

    params.exitscope();
}

void attr_class::publish(ClassTable *classtable)
{
    if (classtable->symbols.lookup(name) != NULL)
    {    
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Attribute " << name << " already defined" 
            << std::endl;
        return;    
    }

    classtable->symbols.addid(name, type_decl);
}

void formal_class::publish(ClassTable *classtable)
{
    if (name == self)
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Using keyword as parameter name: " << name 
            << std::endl;
        return;          
    }
    classtable->symbols.addid(name, type_decl);
}

void ClassTable::install_basic_classes() {

    // The tree package uses these globals to annotate the classes built below.
   // curr_lineno  = 0;
    Symbol filename = stringtable.add_string("<basic class>");

    // The following demonstrates how to create dummy parse trees to
    // refer to basic Cool classes.  There's no need for method
    // bodies -- these are already built into the runtime system.

    // IMPORTANT: The results of the following expressions are
    // stored in local variables.  You will want to do something
    // with those variables at the end of this method to make this
    // code meaningful.

    //
    // The Object class has no parent class. Its methods are
    //        abort() : Object    aborts the program
    //        type_name() : Str   returns a string representation of class name
    //        copy() : SELF_TYPE  returns a copy of the object
    //
    // There is no need for method bodies in the basic classes---these
    // are already built in to the runtime system.

    Class_ Object_class =
	class_(Object,
	       No_class,
	       append_Features(
			       append_Features(
					       single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
					       single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
			       single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
	       filename);

    //
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class =
	class_(IO,
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       single_Features(method(out_string, single_Formals(formal(arg, Str)),
										      SELF_TYPE, no_expr())),
							       single_Features(method(out_int, single_Formals(formal(arg, Int)),
										      SELF_TYPE, no_expr()))),
					       single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
			       single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
	       filename);

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer.
    //
    Class_ Int_class =
	class_(Int,
	       Object,
	       single_Features(attr(val, prim_slot, no_expr())),
	       filename);

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
	class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //
    Class_ Str_class =
	class_(Str,
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       append_Features(
									       single_Features(attr(val, Int, no_expr())),
									       single_Features(attr(str_field, prim_slot, no_expr()))),
							       single_Features(method(length, nil_Formals(), Int, no_expr()))),
					       single_Features(method(concat,
								      single_Formals(formal(arg, Str)),
								      Str,
								      no_expr()))),
			       single_Features(method(substr,
						      append_Formals(single_Formals(formal(arg, Int)),
								     single_Formals(formal(arg2, Int))),
						      Str,
						      no_expr()))),
	       filename);

    classes = append_Classes(nil_Classes(), single_Classes(Object_class));
    classes = append_Classes(classes, single_Classes(IO_class));
    classes = append_Classes(classes, single_Classes(Int_class));
    classes = append_Classes(classes, single_Classes(Bool_class));
    classes = append_Classes(classes, single_Classes(Str_class));
}

////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

ostream& ClassTable::semant_error(Class_ c)
{
    return semant_error(c->get_filename(),c);
}

ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
{
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error()
{
    semant_errors++;
    return error_stream;
}



/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
        by setting the `type' field in each Expression node.
        (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
 */
void program_class::semant()
{
    initialize_constants();

    /* ClassTable constructor may do some semantic analysis */
    ClassTable *classtable = new ClassTable(classes);

    /* some semantic analysis code may go here */

    if (classtable->errors()) {
	   cerr << "Compilation halted due to static semantic errors." << endl;
	   exit(1);
    }

    classtable->symbols.enterscope();

    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        Class_ class_ = classes->nth(i);
        Symbol name = class_->getName();
        classtable->symbols.addid(name,name);
        class_->semant(classtable);
    }

    classtable->symbols.exitscope();

    if (classtable->errors()) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    } 
}

void class__class::semant(ClassTable *classtable) {
    if (parent == SELF_TYPE) {
        classtable->semant_error(classtable->getCurrentClass()) << "Parent invalid" << std::endl;
        return;
    }
    if (classtable->getClass(parent) == NULL)
    {
        classtable->semant_error(classtable->getCurrentClass()) << "Parent invalid" << std::endl;
        return;
    }
    classtable->symbols.enterscope();
    classtable->setCurrentClass(this);
    classtable->symbols.addid(self, classtable->getCurrentClass()->getName());
    classtable->publishVariables(this);
    for (int i = features->first(); features->more(i); i = features->next(i)) {
        features->nth(i)->semant(classtable);
    }
    classtable->symbols.exitscope();
}

void method_class::semant(ClassTable *classtable) {
    classtable->symbols.enterscope();
    publish(classtable);

    Symbol type = expr->semant(classtable);
    method_class *parent_method = classtable->getMethod(classtable->getClass(classtable->getCurrentClass()->getParentName()), name);

    if (return_type == SELF_TYPE && type != SELF_TYPE) {
        classtable->semant_error(classtable->getCurrentClass()) << "Bad return type" << std::endl;
        goto exit;
    }

    if (type == SELF_TYPE) {
        type = classtable->symbols.lookup(self);
    }

    if (classtable->getClass(return_type) == NULL) {
        classtable->semant_error(classtable->getCurrentClass()) << "No return type" << std::endl;
        goto exit;
    }

    if (!classtable->isSubClass(classtable->getClass(type), classtable->getClass(return_type))) {
        classtable->semant_error(classtable->getCurrentClass()) << "Bad return type" << std::endl;
        goto exit;
    }

    if (parent_method && parent_method->getFormals()->len() != formals->len()) {
        classtable->semant_error(classtable->getCurrentClass()) << "Wrong # parameters" << std::endl;
        goto exit;
    }

    for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
        if (formals->nth(i)->getType() == SELF_TYPE) {
            classtable->semant_error(classtable->getCurrentClass()) << "Bad SELF_TYPE" << std::endl;
            goto exit;
        }
        if (parent_method && parent_method->getFormals()->nth(i)->getType() != formals->nth(i)->getType()) {
            classtable->semant_error(classtable->getCurrentClass()) << "Bad parameter type" << std::endl;
            goto exit;
        }
    }

    exit:
        classtable->symbols.exitscope();
}

void attr_class::semant(ClassTable *classtable)
{
    if (name == self)
    { 
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Using keyword as attribute name: " << name 
            << std::endl;
        return; 
    }

    Symbol type = init->semant(classtable);
    
    if (type == No_type)
    {
        return;
    }

    if (!classtable->isSubClass(classtable->getClass(type), classtable->getClass(type_decl)))
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Wrong type in attribute initialization: " << name 
            << " expected " << type_decl << " was " << type << std::endl;
        return; 
    }
}

Symbol assign_class::semant(ClassTable *classtable)
{
    Symbol type = classtable->symbols.lookup(name);
                              
    if (type == NULL) 
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Identifier not declared: " << name << std::endl;
        set_type(Object);
        return Object;
    } 

    Symbol type2 = expr->semant(classtable);

    if (type != type2)
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Wrong type in assign statement" << std::endl;
        set_type(Object);
        return Object; 
    }

    set_type(type);
    return type;
}

Symbol static_dispatch_class::semant(ClassTable *classtable)
{    
    Symbol c_type = expr->semant(classtable);

    Class_ c;

    if (c_type == No_type || c_type == SELF_TYPE) 
        c = classtable->getCurrentClass();
    else
        c = classtable->getClass(c_type);

    if (c == NULL)
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Tried to dispatch method on non-class" << std::endl;
        set_type(Object);
        return Object;
    }

    Class_ p = classtable->getClass(c->getParentName());

    if (!classtable->isSubClass(c, p))
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Tried static dispatch to non-parent class" << std::endl;
        set_type(Object);
        return Object;
    }
    
    method_class *m = classtable->getMethod(p, name);
    
    if (m == NULL)
    { 
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Class " << c_type << " doesnt have method " << name << std::endl;
        set_type(Object);
        return Object;
    }

    if (actual->len() != m->getFormals()->len())
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            name << " expects " << m->getFormals()->len() << " parameters " << 
            actual->len() << " given" << std::endl;
        set_type(Object);
        return Object;
    }

    Formals formals = m->getFormals();
    int j = formals->first();

    for (int i = actual->first(); 
            actual->more(i); i = actual->next(i), j = formals->next(j))
    {
        Symbol type = actual->nth(i)->semant(classtable);
        
        if (!classtable->isSubClass(classtable->getClass(type), 
                    classtable->getClass(formals->nth(j)->getType())))
        {
            classtable->semant_error(classtable->getCurrentClass()) << 
                name << " parameter " << i << " expected " << formals->nth(j)->getType()
                <<  " given " << type << std::endl; 
            set_type(Object);
            return Object; 
        }
    }

    Symbol return_type = m->getReturnType();

    if (return_type == SELF_TYPE)
    {
        return_type = c_type;
    }

    set_type(return_type);
    return return_type; 
}

Symbol dispatch_class::semant(ClassTable *classtable)
{
    Symbol c_type = expr->semant(classtable);

    Class_ c;

    if (c_type == No_type || c_type == SELF_TYPE) 
        c = classtable->getCurrentClass();
    else
        c = classtable->getClass(c_type);

    if (c == NULL)
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Tried to dispatch method on non-class" << std::endl;
        set_type(Object);
        return Object;
    }
    
    method_class *m = classtable->getMethod(c, name);
    
    if (m == NULL)
    { 
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Class " << c_type << " doesnt have method " << name << std::endl;
        set_type(Object);
        return Object;
    }

    if (actual->len() != m->getFormals()->len())
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            name << " expects " << m->getFormals()->len() << " parameters " << 
            actual->len() << " given" << std::endl;
        set_type(Object);
        return Object;
    }

    Formals formals = m->getFormals();
    int j = formals->first();

    for (int i = actual->first(); 
            actual->more(i); i = actual->next(i), j = formals->next(j))
    {
        Symbol type = actual->nth(i)->semant(classtable);
       
        if (!classtable->isSubClass(classtable->getClass(type), 
                    classtable->getClass(formals->nth(j)->getType())))
        {
            classtable->semant_error(classtable->getCurrentClass()) << 
                name << " parameter " << i << " expected " << formals->nth(j)->getType()
                <<  " given " << type << std::endl; 
            set_type(Object);
            return Object; 
        }
    }

    Symbol return_type = m->getReturnType();

    if (return_type == SELF_TYPE)
    {
        return_type = c_type;
    }

    set_type(return_type);
    return return_type; 
}

Symbol cond_class::semant(ClassTable *classtable)
{
    Symbol type1 = pred->semant(classtable);

    if (type1 != Bool)
    { 
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Loop predicate must be boolean, " << type << " given." << std::endl; 
        set_type(Object);
        return Object; 
    }

    Symbol type2 = then_exp->semant(classtable);
    Symbol type3 = else_exp->semant(classtable);

    Symbol type4 = classtable->lowestUpperBound(classtable->getClass(type2), classtable->getClass(type3));

    set_type(type4);
    return type4;
}

Symbol loop_class::semant(ClassTable *classtable)
{
    Symbol type = pred->semant(classtable);

    body->semant(classtable);

    if (type != Bool)
    {
       classtable->semant_error(classtable->getCurrentClass()) << 
            "Loop predicate must be boolean, " << type << " given." << std::endl; 
       set_type(Object);
       return Object; 
    }

    set_type(Object);
    return Object;
}

Symbol typcase_class::semant(ClassTable *classtable)
{
    Symbol type1 = expr->semant(classtable);
    Symbol type2;

    SymbolTable<Symbol, Entry> distinct_set;
    distinct_set.enterscope();

    Symbol lub = NULL;

    for (int i = cases->first(); cases->more(i); i = cases->next(i))
    {
        Symbol type_decl = cases->nth(i)->getType();

        type2 = cases->nth(i)->semant(classtable);
        
        if (distinct_set.lookup(type_decl) != NULL)
        {
            classtable->semant_error(classtable->getCurrentClass()) << 
                "Branches in Case statement must be of different types" << std::endl; 
            set_type(Object);
            return Object;
        }

        distinct_set.addid(type_decl, type_decl);
        
        if (lub == NULL)
            lub = type2;

        lub = classtable->lowestUpperBound(classtable->getClass(lub), classtable->getClass(type2));
    }

    set_type(lub);
    return lub;
}
 
Symbol branch_class::semant(ClassTable *classtable)
{
    classtable->symbols.enterscope();
    classtable->symbols.addid(name, type_decl);

    Symbol type = expr->semant(classtable);

    classtable->symbols.exitscope();

    return type;
}

Symbol block_class::semant(ClassTable *classtable)
{
    Symbol type;
    for (int i = body->first(); body->more(i); i = body->next(i))
    {
        type = body->nth(i)->semant(classtable);
    }

    set_type(type);
    return type;
}

Symbol let_class::semant(ClassTable *classtable)
{
    if (identifier == self)
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Can not use self as let variable" << std::endl;
        set_type(Object);
        return Object;    
    }

    Symbol type = init->semant(classtable);
    
    if (type != No_type && type != type_decl)
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Wrong type in let initialization" << std::endl;
        set_type(Object);
        return Object; 
    } 
    
    classtable->symbols.enterscope();
    classtable->symbols.addid(identifier, type_decl);

    Symbol type2 = body->semant(classtable);

    classtable->symbols.exitscope();

    set_type(type2);
    return type2;
}

Symbol plus_class::typeCheck(ClassTable *classtable)
{
    /*Symbol type1 = e1->semant(classtable);
    Symbol type2 = e2->semant(classtable);
    
    if (type1 != Int || type2 != Int)
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Addition used with non Integer variable" << std::endl;
        set_type(Object);
        return Object;
    }*/

    set_type(Int);
    return Int;
}

Symbol sub_class::semant(ClassTable *classtable)
{ 
    /*Symbol type1 = e1->semant(classtable);
    Symbol type2 = e2->semant(classtable);
    
    if (type1 != Int || type2 != Int)
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Substract used with non Integer variable" << std::endl;
        set_type(Object);
        return Object;
    }*/

    set_type(Int);
    return Int;
}

Symbol mul_class::semant(ClassTable *classtable)
{ 
    /*Symbol type1 = e1->semant(classtable);
    Symbol type2 = e2->semant(classtable);
    
    if (type1 != Int || type2 != Int)
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Multiply used with non Integer variable" << std::endl;
        set_type(Object);
        return Object;
    }*/

    set_type(Int);
    return Int;
}

Symbol divide_class::semant(ClassTable *classtable)
{
    /*Symbol type1 = e1->semant(classtable);
    Symbol type2 = e2->semant(classtable);
    
    if (type1 != Int || type2 != Int)
    {                 
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Divide used with non Integer variable" << std::endl;
        set_type(Object);
        return Object;
    }*/

    set_type(Int);
    return Int;
}

Symbol neg_class::semant(ClassTable *classtable)
{
    /*Symbol type = e1->semant(classtable);

    if (type != Int) 
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Neg used with non Integer variable" << std::endl;
        set_type(Object);
        return Object;
    }*/

    set_type(Int);
    return Int;
}

Symbol lt_class::semant(ClassTable *classtable)
{
    /*Symbol type1 = e1->semant(classtable);
    Symbol type2 = e2->semant(classtable);

    if (type1 != Int || type2 != Int)
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Less-than comparison only valid with Integers" << std::endl;
        set_type(Object);
        return Object; 
    }*/

    set_type(Bool);
    return Bool;
}

Symbol eq_class::semant(ClassTable *classtable)
{
    /*Symbol type1 = e1->semant(classtable);
    Symbol type2 = e2->semant(classtable);

    if ((type1 == Int && type2 != Int) || 
            (type1 == Bool && type2 != Bool) ||
            (type1 == Str && type2 != Str))
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "compare only supports standard types" << std::endl;
        set_type(Object);
        return Object;
    }*/

    set_type(Bool);
    return Bool;
}

Symbol leq_class::semant(ClassTable *classtable)
{
    /*Symbol type1 = e1->semant(classtable);
    Symbol type2 = e2->semant(classtable);

    if (type1 != Int || type2 != Int)
    {
        classtable->semant_error(classtable->getCurrentClass()) << 
            "Less-than-equal comparison only valid with Integers" << std::endl;
        set_type(Object);
        return Object; 
    }*/

    set_type(Bool);
    return Bool; 
}

Symbol comp_class::semant(ClassTable *classtable)
{
    /*Symbol type = e1->semant(classtable);
    if (type != Bool)
    {
        classtable->semant_error(classtable->getCurrentClass()) 
            << "Not requires Boolean" << std::endl; 
        set_type(Object);
        return Object;
    }*/

    set_type(Bool);
    return Bool;
}

Symbol int_const_class::semant(ClassTable *classtable)
{
    set_type(Int);
    return Int;
}

Symbol bool_const_class::semant(ClassTable *classtable)
{
    set_type(Bool);
    return Bool;
}

Symbol string_const_class::semant(ClassTable *classtable)
{
    set_type(Str);
    return Str;
}

Symbol new__class::semant(ClassTable *classtable)
{        
    set_type(type_name);
    return type_name;
}

Symbol isvoid_class::semant(ClassTable *classtable)
{
    e1->semant(classtable);
    set_type(Bool);
    return Bool;
}

Symbol no_expr_class::semant(ClassTable *classtable)
{
    set_type(No_type);
    return No_type;
}

Symbol object_class::semant(ClassTable *classtable)
{
    /*if (name == self) // handle SELF_TYPE
    {
        set_type(SELF_TYPE);
        return SELF_TYPE;
    }
    
    Symbol type = classtable->symbols.lookup(name);
                              
    if (type == NULL) 
    {
        classtable->semant_error(classtable->getCurrentClass()) 
            << "identifier not declared: " << name << std::endl;
        set_type(Object);
        return Object;
    }*/

    set_type(type);
    return type;
}
