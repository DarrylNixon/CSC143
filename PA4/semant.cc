

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"


extern int semant_debug;
extern char *curr_filename;

typedef SymbolTable<Symbol,Entry> SymTable;

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
static void initialize_constants(void) {
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

void errorOut(ClassTable *classtable, Class_ class_, char* err) {
    classtable->semant_error(class_) << err << endl;
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
        
        if (c->getParentName() == Bool || c->getParentName() == Str || c->getParentName() == SELF_TYPE) {
            errorOut(this, c, "Can't inherit Bool || SELF_TYPE || Str.");
        }

        if (symTab.lookup(c->getName()) != NULL) {
            errorOut(this, c, "Duplicate name.");
            return;
        }

        symTab.addid(c->getName(), c->getName());
    }
    if (getClass(Main) == NULL) {
        semant_error() << "Class main is not defined." << endl;
        return;
    }
}

Class_ ClassTable:: getCurrentClass() {
    return currentClass;
}

void ClassTable::setCurrentClass(Class_ class1) {
      currentClass = class1;
  }

Class_ ClassTable::getClass(Symbol name) { 
    if (name == SELF_TYPE || name == self) {
        name = symbols.lookup(self);
    }
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        if (name == classes->nth(i)->getName()) return classes->nth(i);
    }
    return NULL;
}

method_class* ClassTable::getMethod(Class_ c, Symbol m) {
    for (int i = c->getFeatures()->first(); c->getFeatures()->more(i); i = c->getFeatures()->next(i)) {
        // borrowed dynamic cast... cool!
        method_class *method = dynamic_cast<method_class*>(c->getFeatures()->nth(i));
        if (method == NULL) {
            continue;
        }
        if (method->getName() == m) {
            return method;
        }
    }
    Class_ p = getClass(c->getParentName());
    return (p == NULL) ? NULL : getMethod(p, m);
}

void ClassTable::processTypes(Class_ class_) {
    Features features = class_->getFeatures();
    for (int i = features->first(); features->more(i); i = features->next(i)) {
        attr_class *attr = dynamic_cast<attr_class*>(features->nth(i));
        if (attr == NULL) continue;
        attr->processTypes(this);
    }
    if (Class_ p = getClass(class_->getParentName())) processTypes(p);
}

void method_class::processTypes(ClassTable *classtable) {
    SymTable symbolTable;
    symbolTable.enterscope();
    for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
        Formal_class *formal = formals->nth(i);
        Symbol temp = formal->getName();
        if (symbolTable.lookup(temp) != NULL) {
            errorOut(classtable, classtable->getCurrentClass(), "Duplicate param in method.");
            return; 
        }
        symbolTable.addid(temp, temp);
        formal->processTypes(classtable);
    }
    symbolTable.exitscope();
}

void attr_class::processTypes(ClassTable *classtable) {
    if (classtable->symbols.lookup(name) != NULL) {
        errorOut(classtable, classtable->getCurrentClass(), "Attribute already defined.");
        return;    
    }

    classtable->symbols.addid(name, type_decl);
}

void formal_class::processTypes(ClassTable *classtable) {
    if (name == self) {
            errorOut(classtable, classtable->getCurrentClass(), "Param name is not allowed.");
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

ostream& ClassTable::semant_error(Class_ c) {
    return semant_error(c->get_filename(),c);
}

ostream& ClassTable::semant_error(Symbol filename, tree_node *t) {
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error() {
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
void program_class::semant() {
    initialize_constants();

    ClassTable *classtable = new ClassTable(classes);
    if (classtable->errors()) {
	   cerr << "Compilation halted due to static semantic errors." << endl;
	   exit(1);
    }

    classtable->symbols.enterscope();

    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        Class_ class_ = classes->nth(i);
        Symbol name = class_->getName();
        classtable->symbols.addid(name,name);
        class_->typeCheck(classtable);
    }

    classtable->symbols.exitscope();

    if (classtable->errors()) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    } 
}

void class__class::typeCheck(ClassTable *classtable) {
    if (parent == SELF_TYPE) {
        errorOut(classtable, classtable->getCurrentClass(), "Parent not valid.");
        return;
    }
    if (classtable->getClass(parent) == NULL) {
        errorOut(classtable, classtable->getCurrentClass(), "Parent not valid.");
        return;
    }
    classtable->symbols.enterscope();
    classtable->setCurrentClass(this);
    classtable->symbols.addid(self, classtable->getCurrentClass()->getName());
    classtable->processTypes(this);
    for (int i = features->first(); features->more(i); i = features->next(i)) {
        features->nth(i)->typeCheck(classtable);
    }
    classtable->symbols.exitscope();
}

Symbol object_class::typeCheck(ClassTable *classtable) {
    if (name == self) {
        set_type(SELF_TYPE);
        return SELF_TYPE;
    }

    Symbol type = classtable->symbols.lookup(name);
    if (type == NULL) {
        errorOut(classtable, classtable->getCurrentClass(), "Type error.");
        return Object;
    }

    set_type(type);
    return type;
}

bool ClassTable::isSubClass(Class_ class1, Class_ class2) {
    if (class1->getName() == class2->getName()) return true;
    Class_ parent = getClass(class1->getParentName());
    if (parent) {
        return isSubClass(parent, class2);
    } else {
    return false;
    }
}

void method_class::typeCheck(ClassTable *classtable) {
    classtable->symbols.enterscope();
    processTypes(classtable);

    Symbol type = expr->typeCheck(classtable);
    method_class *parent_method = classtable->getMethod(classtable->getClass(classtable->getCurrentClass()->getParentName()), name);

    if (return_type == SELF_TYPE && type != SELF_TYPE) {
        errorOut(classtable, classtable->getCurrentClass(), "Bad return type.");
        classtable->symbols.exitscope();
        return;
    }

    if (type == SELF_TYPE) {
        type = classtable->symbols.lookup(self);
    }

    if (classtable->getClass(return_type) == NULL) {
        errorOut(classtable, classtable->getCurrentClass(), "No return type.");
        classtable->symbols.exitscope();
        return;
    }

    if (!classtable->isSubClass(classtable->getClass(type), classtable->getClass(return_type))) {
        errorOut(classtable, classtable->getCurrentClass(), "Bad return type.");
        classtable->symbols.exitscope();
        return;
    }

    if (parent_method && parent_method->getFormals()->len() != formals->len()) {
        errorOut(classtable, classtable->getCurrentClass(), "Bad parameter count.");
        classtable->symbols.exitscope();
        return;
    }

    for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
        if (formals->nth(i)->getType() == SELF_TYPE) {
            errorOut(classtable, classtable->getCurrentClass(), "Bad SELF_TYPE.");
            classtable->symbols.exitscope();
            return;
        }
        if (parent_method && parent_method->getFormals()->nth(i)->getType() != formals->nth(i)->getType()) {
            errorOut(classtable, classtable->getCurrentClass(), "Bad parameter type.");
            classtable->symbols.exitscope();
            return;
        }
    }
}

void attr_class::typeCheck(ClassTable *classtable) {
    if (name == self) { 
        errorOut(classtable, classtable->getCurrentClass(), "Attribute name is a keyword.");
        return; 
    }

    Symbol type = init->typeCheck(classtable);
    
    if (type == No_type) {
        return;
    }

    if (!classtable->isSubClass(classtable->getClass(type), classtable->getClass(type_decl))) {
        errorOut(classtable, classtable->getCurrentClass(), "Bad attribute type.");
        return; 
    }
}

Symbol assign_class::typeCheck(ClassTable *classtable) {
    Symbol type = classtable->symbols.lookup(name);
                              
    if (type == NULL) {
        errorOut(classtable, classtable->getCurrentClass(), "Identifier not declared.");
        set_type(Object);
        return Object;
    } 

    Symbol type2 = expr->typeCheck(classtable);

    if (type != type2) {
        errorOut(classtable, classtable->getCurrentClass(), "Bad type in assign.");
        set_type(Object);
        return Object; 
    }

    set_type(type);
    return type;
}

Symbol static_dispatch_class::typeCheck(ClassTable *classtable) {    
    Symbol c_type = expr->typeCheck(classtable);
    Class_ class_;

    if (c_type == No_type || c_type == SELF_TYPE) 
        class_ = classtable->getCurrentClass();
    else
        class_ = classtable->getClass(c_type);

    if (class_ == NULL) {
        errorOut(classtable, classtable->getCurrentClass(), "Dispatch on non-class.");
        set_type(Object);
        return Object;
    }

    Class_ p = classtable->getClass(class_->getParentName());

    if (!classtable->isSubClass(class_, p)) {
        errorOut(classtable, classtable->getCurrentClass(), "Static dispatch on non-parent.");
        set_type(Object);
        return Object;
    }
    
    method_class *m = classtable->getMethod(p, name);
    
    if (m == NULL) { 
        errorOut(classtable, classtable->getCurrentClass(), "Method doesn't exist.");
        set_type(Object);
        return Object;
    }

    if (actual->len() != m->getFormals()->len()) {
        errorOut(classtable, classtable->getCurrentClass(), "Bad formal length.");
        set_type(Object);
        return Object;
    }

    Formals formals = m->getFormals();
    int j = formals->first();

    for (int i = actual->first(); actual->more(i); i = actual->next(i), j = formals->next(j)) {
        Symbol type = actual->nth(i)->typeCheck(classtable);
        
        if (!classtable->isSubClass(classtable->getClass(type), classtable->getClass(formals->nth(j)->getType()))) {
            errorOut(classtable, classtable->getCurrentClass(), "Unexpected mismatch in dispatch.");
            set_type(Object);
            return Object; 
        }
    }

    Symbol return_type = m->getReturnType();

    if (return_type == SELF_TYPE) {
        return_type = c_type;
    }

    set_type(return_type);
    return return_type; 
}

Symbol dispatch_class::typeCheck(ClassTable *classtable) {
    Class_ c;
    Symbol c_type = expr->typeCheck(classtable);
    if (c_type == No_type || c_type == SELF_TYPE) 
        c = classtable->getCurrentClass();
    else
        c = classtable->getClass(c_type);

    if (c == NULL) {
        errorOut(classtable, classtable->getCurrentClass(), "Dispatch on non-class.");
        set_type(Object);
        return Object;
    }
    method_class *m = classtable->getMethod(c, name);
    
    if (m == NULL) { 
        errorOut(classtable, classtable->getCurrentClass(), "Method doesn't exist.");
        set_type(Object);
        return Object;
    }

    if (actual->len() != m->getFormals()->len()) {
        errorOut(classtable, classtable->getCurrentClass(), "Bad formal length.");
        set_type(Object);
        return Object;
    }

    Formals formals = m->getFormals();
    int j = formals->first();

    for (int i = actual->first(); actual->more(i); i = actual->next(i), j = formals->next(j)) {
        Symbol type = actual->nth(i)->typeCheck(classtable);
       
        if (!classtable->isSubClass(classtable->getClass(type), classtable->getClass(formals->nth(j)->getType()))) {
            errorOut(classtable, classtable->getCurrentClass(), "Unexpected mismatch on dispatch.");
            set_type(Object);
            return Object; 
        }
    }

    Symbol return_type = m->getReturnType();

    if (return_type == SELF_TYPE) {
        return_type = c_type;
    }

    set_type(return_type);
    return return_type; 
}

Symbol ClassTable::lowestUpperBound(Class_ class1, Class_ class2) {
    if (class1->getName() == class2->getName()) return class1->getName();
    
    SymTable parents;
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

Symbol cond_class::typeCheck(ClassTable *classtable) {
    Symbol type1 = pred->typeCheck(classtable);

    if (type1 != Bool) { 
        errorOut(classtable, classtable->getCurrentClass(), "Cond needs bool.");
        set_type(Object);
        return Object; 
    }

    Symbol type2 = then_exp->typeCheck(classtable);
    Symbol type3 = else_exp->typeCheck(classtable);

    Symbol type4 = classtable->lowestUpperBound(classtable->getClass(type2), classtable->getClass(type3));

    set_type(type4);
    return type4;
}

Symbol loop_class::typeCheck(ClassTable *classtable) {
    Symbol type = pred->typeCheck(classtable);

    body->typeCheck(classtable);

    if (type != Bool) {
        errorOut(classtable, classtable->getCurrentClass(), "Loop needs bool.");
        set_type(Object);
        return Object; 
    }

    set_type(Object);
    return Object;
}

Symbol typcase_class::typeCheck(ClassTable *classtable) {
    Symbol type1 = expr->typeCheck(classtable);
    Symbol type2;

    SymTable distinct_set;
    distinct_set.enterscope();

    Symbol lub = NULL;

    for (int i = cases->first(); cases->more(i); i = cases->next(i)) {
        Symbol type_decl = cases->nth(i)->getType();
        type2 = cases->nth(i)->typeCheck(classtable);
        
        if (distinct_set.lookup(type_decl) != NULL) {
            errorOut(classtable, classtable->getCurrentClass(), "Duplicate in case.");
            set_type(Object);
            return Object;
        }

        distinct_set.addid(type_decl, type_decl);
        
        if (lub == NULL) {
            lub = type2;
        }

        lub = classtable->lowestUpperBound(classtable->getClass(lub), classtable->getClass(type2));
    }

    set_type(lub);
    return lub;
}
 
Symbol branch_class::typeCheck(ClassTable *classtable) {
    classtable->symbols.enterscope();
    classtable->symbols.addid(name, type_decl);

    Symbol type = expr->typeCheck(classtable);

    classtable->symbols.exitscope();

    return type;
}

Symbol block_class::typeCheck(ClassTable *classtable) {
    Symbol type;
    for (int i = body->first(); body->more(i); i = body->next(i)) {
        type = body->nth(i)->typeCheck(classtable);
    }

    set_type(type);
    return type;
}

Symbol let_class::typeCheck(ClassTable *classtable) {
    if (identifier == self) {
        errorOut(classtable, classtable->getCurrentClass(), "Self in let.");
        set_type(Object);
        return Object;    
    }

    Symbol type = init->typeCheck(classtable);
    
    if (type != No_type && type != type_decl) {
        errorOut(classtable, classtable->getCurrentClass(), "Bad type in let.");
        set_type(Object);
        return Object; 
    } 
    
    classtable->symbols.enterscope();
    classtable->symbols.addid(identifier, type_decl);

    Symbol type2 = body->typeCheck(classtable);

    classtable->symbols.exitscope();

    set_type(type2);
    return type2;
}

Symbol intCheck(ClassTable *classtable, Symbol operand1, Symbol operand2) {
    if (operand1 != Int || operand2 != Int) {
        errorOut(classtable, classtable->getCurrentClass(), "Expression requires integers.");
        return Object;
    }
    return Int;
}

Symbol boolCheck(ClassTable *classtable, Symbol operand1, Symbol operand2) {
    if (operand1 != Int || operand2 != Int) {
        errorOut(classtable, classtable->getCurrentClass(), "Expression requires booleans.");
        return Object;
    }
    return Bool;
}

Symbol stringCheck(ClassTable *classtable, Symbol operand1, Symbol operand2) {
    if (operand1 != Str || operand2 != Str) {
        errorOut(classtable, classtable->getCurrentClass(), "Expression requires strings.");
        return Object;
    }
    return Str;
}

Symbol plus_class::typeCheck(ClassTable *classtable) {
    Symbol ret = intCheck(classtable, e1->typeCheck(classtable), e2->typeCheck(classtable));
    set_type(ret);
    return ret;
}

Symbol sub_class::typeCheck(ClassTable *classtable) { 
    Symbol ret = intCheck(classtable, e1->typeCheck(classtable), e2->typeCheck(classtable));
    set_type(ret);
    return ret;
}

Symbol mul_class::typeCheck(ClassTable *classtable) { 
    Symbol ret = intCheck(classtable, e1->typeCheck(classtable), e2->typeCheck(classtable));
    set_type(ret);
    return ret;
}

Symbol divide_class::typeCheck(ClassTable *classtable) {
    Symbol ret = intCheck(classtable, e1->typeCheck(classtable), e2->typeCheck(classtable));
    set_type(ret);
    return ret;
}

Symbol neg_class::typeCheck(ClassTable *classtable) {
    Symbol ret = intCheck(classtable, e1->typeCheck(classtable), e1->typeCheck(classtable));
    set_type(ret);
    return ret;
}

Symbol lt_class::typeCheck(ClassTable *classtable) {
    Symbol ret = boolCheck(classtable, e1->typeCheck(classtable), e2->typeCheck(classtable));
    set_type(ret);
    return ret;
}

Symbol eq_class::typeCheck(ClassTable *classtable) {
    Symbol operand1 = e1->typeCheck(classtable);
    Symbol operand2 = e2->typeCheck(classtable);

    if ((operand1 == Int && operand2 != Int) || (operand1 == Bool && operand2 != Bool) || (operand1 == Str && operand2 != Str)) {
        errorOut(classtable, classtable->getCurrentClass(), "Equality type check error.");
        return Object;
    }
    set_type(Bool);
    return Bool;
}

Symbol leq_class::typeCheck(ClassTable *classtable) {
    Symbol ret = boolCheck(classtable, e1->typeCheck(classtable), e2->typeCheck(classtable));
    set_type(ret);
    return ret;
}

Symbol comp_class::typeCheck(ClassTable *classtable) {
    if (e1->typeCheck(classtable) != Bool) {
        errorOut(classtable, classtable->getCurrentClass(), "Comp needs bool.");
        set_type(Object);
        return Object;
    }

    set_type(Bool);
    return Bool;
}

Symbol int_const_class::typeCheck(ClassTable *classtable) {
    set_type(Int);
    return Int;
}

Symbol bool_const_class::typeCheck(ClassTable *classtable) {
    set_type(Bool);
    return Bool;
}

Symbol string_const_class::typeCheck(ClassTable *classtable) {
    set_type(Str);
    return Str;
}

Symbol new__class::typeCheck(ClassTable *classtable) {
    set_type(type_name);
    return type_name;
}

Symbol isvoid_class::typeCheck(ClassTable *classtable) {
    e1->typeCheck(classtable);
    set_type(Bool);
    return Bool;
}

Symbol no_expr_class::typeCheck(ClassTable *classtable) {
    set_type(No_type);
    return No_type;
}
