#include <iostream>
#include <iomanip>
#include <stdio.h>
#include "symtab.hh"
#include "ast.hh"
#include "quads.hh"
using namespace std;

/* This little #define is only here to suppress compiler warnings for methods
   not using the quad_list given to it as a parameter. */
#define USE_Q { quad_list *foo = &q; foo = foo; }


/* Constructors for quadruples. The order of assigning the member fields might
   looks strange, but it's arranged in the same order as they are declared
   in quads.hh to avoid compiler rearrangements. */
quadruple::quadruple(quad_op_type op, long a1, long a2, long a3) :
    op_code(op),
    sym1(a1),
    sym2(a2),
    sym3(a3),
    int1(a1),
    int2(a2),
    int3(a3)
{
}




/* The quad_list_element constructor. Not very exciting really. This class
   is never used outside the quad_list class. */
quad_list_element::quad_list_element(quadruple *q, quad_list_element *n) :
    data(q),
    next(n)
{
}



/* The quad_list_iterator constructor. It initializes the iterator to point
   to the first element of the quad list passed to it as an argument. */
quad_list_iterator::quad_list_iterator(quad_list *q_list) :
    current(q_list->head)
{
}

/* Return the current quad on the quad list we're iterating over, or NULL if
   we've reached the end of the list. */
quadruple *quad_list_iterator::get_current()
{
    if (current == NULL) {
        return NULL;
    }

    return current->data;
}

/* Return the next quadruple on the quad list we're iterating over, or NULL if
   there are no more. */
quadruple *quad_list_iterator::get_next()
{
    if (current->next == NULL) {
        return NULL;
    }

    current = current->next;
    return current->data;
}



/* The quad_list class. */
quad_list::quad_list(int ll) :
    head(NULL),
    tail(NULL),
    last_label(ll)
{
    quad_nr = 1;
}


/* Operator for adding on a new quadruple to the list. */
quad_list &quad_list::operator+=(quadruple *q)
{
    if (head == NULL) {
        head = new quad_list_element(q, NULL);
        tail = head;
    } else {
        tail->next = new quad_list_element(q, NULL);
        tail = tail->next;
    }

    return *this;
}



/**************************************************************
 *** THE AST NODE METHODS FOR GENERATING QUADS FOLLOW HERE. ***
 **************************************************************/

/* Methods for the abstract AST classes. Calling these methods is an error,
   which causes the compiler to abort. */
sym_index ast_expr_list::generate_quads(quad_list &q)
{
    USE_Q;

    fatal("Trying to call generate_quads for ast_expr_list. Try 'generate_parameter_list' instead.");
    return NULL_SYM;
}

sym_index ast_elsif_list::generate_quads(quad_list &q)
{
    USE_Q;

    fatal("Trying to call generate_quads for ast_elsif_list. Try 'generate_quads_and_jump' instead.");
    return NULL_SYM;
}



/* Here come the concrete classes. First the leaf nodes. Note that the
   return value of all these quads is an index to the temporary variable in
   which will be stored the the result the node will generate,
   in one form or another. For nodes that don't return a useful result,
   NULL_SYM is returned. */

sym_index ast_elsif::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    //not useful result
    body->generate_quads(q);
    return NULL_SYM;
}


sym_index ast_id::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    // not a useful result
    return sym_p;
}


sym_index ast_integer::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    sym_index temp = sym_tab->gen_temp_var(integer_type);
    q += new quadruple(q_iload, value, NULL_SYM, temp);
    return temp;

}


sym_index ast_real::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    sym_index temp = sym_tab->gen_temp_var(real_type);
    q += new quadruple(q_rload, sym_tab->ieee(value), NULL_SYM, temp);
    return temp;
    
}


/* Expressions of various kinds. */


/* These three following methods are extremely similar, and we could have
   written a static do_unary function above to handle them. To be able to
   do so, we'd have to pass on more arguments than we are to the two
   do_binary* functions above. Why? */

sym_index ast_not::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    //format (operation, sym_index, -, sym_index) i.e. operand1 and temp var
    sym_index addr = expr->generate_quads(q); // operand1 generate quad for expr
    sym_index temp = sym_tab->gen_temp_var(integer_type); // temporary value
    q += new quadruple(q_inot, addr, NULL_SYM, temp);
    return temp;
}


sym_index ast_uminus::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
     sym_index addr = expr->generate_quads(q);
     sym_index temp;
	   if (expr->type == integer_type) {
      temp = sym_tab->gen_temp_var(integer_type);
      q += new quadruple(q_iuminus, addr, NULL_SYM, temp);
     } else {
      temp = sym_tab->gen_temp_var(real_type);
      q += new quadruple(q_ruminus, addr, NULL_SYM, temp);
     }
     return temp;
}


sym_index ast_cast::generate_quads(quad_list &q)
{
   
    /* Your code here */
    sym_index expr_value = expr->generate_quads(q);
    sym_index new_index;
    if (type == real_type){
        new_index = sym_tab->gen_temp_var(integer_type);
        q += new quadruple(q_itor, expr_value, NULL_SYM, new_index);
    }
    else {
      fatal("Illegal type ");
    }
    return new_index;
}


sym_index binop1(quad_list & q, quad_op_type iop, quad_op_type rop, ast_binaryoperation * node){
  sym_index left = node->left->generate_quads(q);
  sym_index right = node->right->generate_quads(q);
  sym_index temp;

  if (sym_tab->get_symbol_type(left) == integer_type)
  {
    temp = sym_tab->gen_temp_var(integer_type);
    q += new quadruple(iop, left, right, temp);
  }
  else
  {
 // For real (rop)
    temp = sym_tab->gen_temp_var(real_type);
    q += new quadruple(rop, left, right, temp);
  }
  return temp;
}
sym_index ast_add::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    return binop1(q, q_iplus, q_rplus, this);
}

sym_index ast_sub::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    return binop1(q, q_iminus, q_rminus, this);
}

sym_index ast_mult::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    return binop1(q, q_imult, q_rmult, this);
}

sym_index ast_divide::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    return binop1(q, q_rdivide, q_rdivide, this);
}

sym_index ast_idiv::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
  return binop1(q, q_idivide, q_idivide, this);
}

sym_index ast_mod::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    return binop1(q, q_imod, q_imod, this);
}

sym_index ast_or::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    return binop1(q, q_ior, q_ior, this);
}

sym_index ast_and::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    return binop1(q, q_iand, q_iand, this);
}
// for bin relations = <, >,
sym_index binop2(quad_list & q, quad_op_type iop, quad_op_type rop, ast_binaryrelation * node){
  sym_index left = node->left->generate_quads(q);
  sym_index right = node->right->generate_quads(q);
  sym_index temp;

  if (sym_tab->get_symbol_type(left) == integer_type)
  {
    temp = sym_tab->gen_temp_var(integer_type);
    q += new quadruple(iop, left, right, temp);
  }
  else
  {
 // For real (rop)
    temp = sym_tab->gen_temp_var(real_type);
    q += new quadruple(rop, left, right, temp);
  }
  return temp;
}





sym_index ast_equal::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    return binop2(q, q_ieq, q_req, this);
}

sym_index ast_notequal::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    return binop2(q, q_ine, q_rne, this);
}

sym_index ast_lessthan::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    return binop2(q, q_ilt, q_rlt, this);
}

sym_index ast_greaterthan::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    return binop2(q, q_igt, q_rgt, this);
}




/* Since an lvalue can be either an id or an array reference, we can't solve
   this the usual way since there's no instanceof operator in C++ to find out
   which class an object belongs to. So we define the method
   generate_assignment() in both ast_id and ast_indexed, and let the virtual
   mechanism figure out which one to call. */
void ast_id::generate_assignment(quad_list &q, sym_index rhs)
{
    if (type == integer_type) {
        q += new quadruple(q_iassign, rhs, NULL_SYM, sym_p);
    } else if (type == real_type) {
        q += new quadruple(q_rassign, rhs, NULL_SYM, sym_p);
    } else {
        fatal("Illegal type in ast_id::generate_assignment()");
    }
}

void ast_indexed::generate_assignment(quad_list &q, sym_index rhs)
{
    sym_index index_pos = index->generate_quads(q);
    sym_index address = sym_tab->gen_temp_var(integer_type);

    q += new quadruple(q_lindex, id->sym_p, index_pos, address);

    if (type == integer_type) {
        q += new quadruple(q_istore, rhs, NULL_SYM, address);
    } else if (type == real_type) {
        q += new quadruple(q_rstore, rhs, NULL_SYM, address);
    } else {
        fatal("Illegal type in ast_indexed::generate_assignment()");
    }
}


/* Statements of various kinds. */
sym_index ast_assign::generate_quads(quad_list &q)
{
    sym_index right_pos = rhs->generate_quads(q);
    lhs->generate_assignment(q, right_pos);
    return NULL_SYM;
}


/* Parameters need to be treated specially as well. What we do here is
   to recurse from the last parameter forward. In this process we use the
   nr_param pointer (which is incremented by one for each recursive call)
   to get the total number of parameters so we can generate a correct q_call
   quad for the new function/procedure that the parameters belong to.
    */
void ast_expr_list::generate_parameter_list(quad_list &q,
        parameter_symbol *last_param,
        int *nr_params)
{
    USE_Q;
    /* Your code here */
    sym_index para = last_expr->generate_quads(q); //gen quad of last exp in list q
    q += new quadruple(q_param, para, NULL_SYM, NULL_SYM);
    *nr_params += 1;
    if (preceding != NULL){
      preceding->generate_parameter_list(q, NULL, nr_params); // till prec = 0
    }

}


/* Generate quads for a procedure call. */
sym_index ast_procedurecall::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    //(q_call, sym_index, no.params, sym_index)
    int no_params = 0;
    //last parameter to pass in param list func or just use NULL
	  parameter_symbol* last_param = sym_tab->get_symbol(id->sym_p)->get_procedure_symbol()->last_parameter;
  	if (parameter_list != NULL) {
      parameter_list->generate_parameter_list(q, last_param, &no_params);
    }

    q += new quadruple(q_call, id->sym_p, no_params, NULL_SYM);
    return NULL_SYM;
}


/* Generate quads for a function call. */
sym_index ast_functioncall::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    //type will be returned temporary
    int no_params = 0;
    sym_index temp = sym_tab->gen_temp_var(type);

  	parameter_symbol* last_param =
  			sym_tab->get_symbol(id->sym_p)->get_function_symbol()->last_parameter;
  	if (parameter_list != NULL) {
  		parameter_list->generate_parameter_list(q, last_param, &no_params);
  	}
  	q += new quadruple(q_call, id->sym_p, no_params, temp); // last is temp
  	return temp;

}


/* Generate quads for a while statement.
    */
sym_index ast_while::generate_quads(quad_list &q)
{
    // We get two labels for jumps.
    int top = sym_tab->get_next_label();
    int bottom = sym_tab->get_next_label();

    // Here's the label for the top of the while body.
    q += new quadruple(q_labl, top, NULL_SYM, NULL_SYM);

    // Generate quads for the condition. After this code is being run, we
    // check if the result in the variable stored in 'pos' is 0. If it is,
    // we want to exit the loop, which is done via a conditional jump to the
    // 'bottom' label.
    sym_index pos = condition->generate_quads(q);
    q += new quadruple(q_jmpf, bottom, pos, NULL_SYM);

    // Generate quads for the body. Following these come an unconditional
    // jump to the 'top' label, ie, run the condition etc again.
    pos = body->generate_quads(q);
    q += new quadruple(q_jmp, top,  NULL_SYM, NULL_SYM);

    // This is where we jump to if the while condition evaluates to false.
    q += new quadruple(q_labl, bottom, NULL_SYM, NULL_SYM);

    return NULL_SYM;
}


/* Generate quads for an individual elsif statement, including an ending
   jump to an end label. See ast_if::generate_quads for more information. */
void ast_elsif::generate_quads_and_jump(quad_list &q, int label)
{
    USE_Q;
    /* Your code here */
    // just taking the steps of while
    int bottom = sym_tab->get_next_label(); // label for jump
    // Generate quads for the condition.
    //jump to bottom label
    sym_index pos = condition->generate_quads(q);
    //jmpf The jump is made if operand2 is zero (hence the name, “jump if false”).

    q += new quadruple(q_jmpf, bottom, pos, NULL_SYM);
    if (body != NULL) {
      body->generate_quads(q);
    }
    q += new quadruple(q_jmp, label, NULL_SYM, NULL_SYM); //uncond jump
    // This is where we jump to if  condition evaluates to false.
    q += new quadruple(q_labl, bottom, NULL_SYM, NULL_SYM);



}


/* Generate quads (with an ending jump to an end label) for an elsif list.
   See generate_quads for ast_if for more information. */
void ast_elsif_list::generate_quads_and_jump(quad_list &q, int label)
{
    USE_Q;
    /* Your code here */
    // check at least one item remain in the list
    if (preceding != NULL)
    {
      preceding->generate_quads_and_jump(q, label);
    }

    last_elsif->generate_quads_and_jump(q, label);
}


/* Generate quads for an if statement. */
sym_index ast_if::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
   
    sym_index bottom = sym_tab->get_next_label(); 
    sym_index pos = condition->generate_quads(q);
    q += new quadruple(q_jmpf, bottom, pos, NULL_SYM );
    body->generate_quads(q);
    sym_index end = sym_tab->get_next_label();
    q += new quadruple(q_jmp,end,NULL_SYM,NULL_SYM);
    q += new quadruple(q_labl,bottom,NULL_SYM,NULL_SYM);
    if(elsif_list!= NULL){
      elsif_list->generate_quads_and_jump(q,end);
    } 
    if(else_body != NULL) {
      else_body->generate_quads(q);
    }
    q += new quadruple(q_labl, end, NULL_SYM, NULL_SYM);
    
    return NULL_SYM;
}


/* Generate quads for a return statement. */
sym_index ast_return::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    //integer or real
    if (value != NULL)
    {
      sym_index temp_val = value->generate_quads(q); // results value
      if(value->type == integer_type)
        q += new quadruple(q_ireturn, q.last_label, temp_val, NULL_SYM);
      else if(value->type == real_type)
        q += new quadruple(q_rreturn, q.last_label, temp_val, NULL_SYM);
    }
    else
    {
      q += new quadruple(q_jmp, q.last_label, NULL_SYM, NULL_SYM);
    }

    return NULL_SYM;
}


/* Generate quads for an array reference. */
sym_index ast_indexed::generate_quads(quad_list &q)
{
    USE_Q;
    /* Your code here */
    sym_index pos = index->generate_quads(q);
    sym_index temp;
 // operand 1 is the array andd operand 2 is the index to array
	if (id->type == integer_type) {
    temp = sym_tab->gen_temp_var(integer_type);
		q += new quadruple(q_irindex, id->sym_p, pos, temp);
	} else {
    temp = sym_tab->gen_temp_var(real_type);
		q += new quadruple(q_rrindex, id->sym_p, pos, temp);
	}

    return temp;
}


/* Generate quads for a list of statements. Note that this is not necessarily
   the most efficient way to do it... Why not? */
sym_index ast_stmt_list::generate_quads(quad_list &q)
{
    if (preceding != NULL) {
        preceding->generate_quads(q);
    }
    if (last_stmt != NULL) {
        last_stmt->generate_quads(q);
    }
    return NULL_SYM;
}


/* These classes won't actually appear in the part of the AST we generate
   code for, but since we're using abstract virtual methods, these methods
   need to be defined. */
sym_index ast_procedurehead::generate_quads(quad_list &q)
{
    USE_Q;

    return NULL_SYM;
}

sym_index ast_functionhead::generate_quads(quad_list &q)
{
    USE_Q;

    return NULL_SYM;
}



/* These two methods actually start off the quad generation, also taking
   care of adding a last_label. The code is identical for the two methods. */
quad_list *ast_procedurehead::do_quads(ast_stmt_list *s)
{
    int last_label = sym_tab->get_next_label();
    quad_list *q = new quad_list(last_label);

    if (s != NULL) {
        s->generate_quads(*q);
    }

    (*q) += new quadruple(q_labl, last_label, NULL_SYM, NULL_SYM);

    return q;
}

quad_list *ast_functionhead::do_quads(ast_stmt_list *s)
{
    int last_label = sym_tab->get_next_label();
    quad_list *q = new quad_list(last_label);

    if (s != NULL) {
        s->generate_quads(*q);
    }

    (*q) += new quadruple(q_labl, last_label, NULL_SYM, NULL_SYM);

    return q;
}


/**********************************
 *** METHODS FOR PRINTING QUADS ***
 **********************************/


void quadruple::print(ostream &o)
{
    o << "    ";
    o.flags(ios::left);
    switch (op_code) {
    case q_rload:
        o << setw(11) << "q_rload"
          << setw(11) << int1
          << setw(11) << "-"
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_iload:
        o << setw(11) << "q_iload"
          << setw(11) << int1
          << setw(11) << "-"
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_inot:
        o << setw(11) << "q_inot"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << "-"
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_ruminus:
        o << setw(11) << "q_ruminus"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << "-"
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_iuminus:
        o << setw(11) << "q_iuminus"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << "-"
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_rplus:
        o << setw(11) << "q_rplus"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_iplus:
        o << setw(11) << "q_iplus"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_rminus:
        o << setw(11) << "q_rminus"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_iminus:
        o << setw(11) << "q_iminus"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_ior:
        o << setw(11) << "q_ior"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_iand:
        o << setw(11) << "q_iand"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_rmult:
        o << setw(11) << "q_rmult"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_imult:
        o << setw(11) << "q_imult"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_rdivide:
        o << setw(11) << "q_rdivide"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_idivide:
        o << setw(11) << "q_idivide"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_imod:
        o << setw(11) << "q_imod"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_req:
        o << setw(11) << "q_req"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_ieq:
        o << setw(11) << "q_ieq"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_rne:
        o << setw(11) << "q_rne"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_ine:
        o << setw(11) << "q_ine"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_rlt:
        o << setw(11) << "q_rlt"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_ilt:
        o << setw(11) << "q_ilt"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_rgt:
        o << setw(11) << "q_rgt"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_igt:
        o << setw(11) << "q_igt"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_rstore:
        o << setw(11) << "q_rstore"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << "-"
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_istore:
        o << setw(11) << "q_istore"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << "-"
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_rassign:
        o << setw(11) << "q_rassign"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << "-"
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_iassign:
        o << setw(11) << "q_iassign"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << "-"
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_call:
        o << setw(11) << "q_call"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << int2
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_rreturn:
        o << setw(11) << "q_rreturn"
          << setw(11) << int1
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << "-";
        break;
    case q_ireturn:
        o << setw(11) << "q_ireturn"
          << setw(11) << int1
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << "-";
        break;
    case q_lindex:
        o << setw(11) << "q_lindex"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_rrindex:
        o << setw(11) << "q_rrindex"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_irindex:
        o << setw(11) << "q_irindex"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_itor:
        o << setw(11) << "q_itor"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << "-"
          << setw(11) << sym_tab->get_symbol(sym3);
        break;
    case q_jmp:
        o << setw(11) << "q_jmp"
          << setw(11) << int1
          << setw(11) << "-"
          << setw(11) << "-";
        break;
    case q_jmpf:
        o << setw(11) << "q_jmpf"
          << setw(11) << int1
          << setw(11) << sym_tab->get_symbol(sym2)
          << setw(11) << "-";
        break;
    case q_param:
        o << setw(11) << "q_param"
          << setw(11) << sym_tab->get_symbol(sym1)
          << setw(11) << "-"
          << setw(11) << "-";
        break;
    case q_labl:
        o << setw(11) << "q_labl"
          << setw(11) << int1
          << setw(11) << "-"
          << setw(11) << "-";
        break;
    case q_nop:
        o << setw(11) << "q_nop"
          << setw(11) << "-"
          << setw(11) << "-"
          << setw(11) << "-";
        break;
    default:
        o << "unknown (" << (int)op_code << ")";
    }
    o.flags(ios::right);
}


void quad_list::print(ostream &o)
{
    quad_list_element *e;

    o << short_symbols;

    quad_nr = 1;
    e = head;
    while (e != NULL) {
        o << setw(5) << quad_nr << e->data << endl;
        e = e->next;
        quad_nr++;
    }

    o << long_symbols;
}


ostream &operator<<(ostream &o, quadruple *q)
{
    if (q != NULL) {
        q->print(o);
    } else {
        o << "   Quad: NULL";
    }
    return o;
}


ostream &operator<<(ostream &o, quad_list *q_list)
{
    if (q_list != NULL) {
        q_list->print(o);
    } else {
        o << "Quad list: NULL\n";
    }
    return o;
}
