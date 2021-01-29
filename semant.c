#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "env.h"
#include "semant.h"
#include "helper.h"
#include "translate.h"
#include "table.h"

/*Lab5: Your implementation of lab5.*/

struct expty
{
	Tr_exp exp;
	Ty_ty ty;
};

//In Lab4, the first argument exp should always be **NULL**.
struct expty expTy(Tr_exp exp, Ty_ty ty)
{
	struct expty e;

	e.exp = exp;
	e.ty = ty;

	return e;
}

Ty_ty actual_ty(Ty_ty t) {
	while (t && t->kind == Ty_name) {
		t = t->u.name.ty;
	}
	return t;
}

struct expty transVar(S_table venv, S_table tenv, A_var v, Tr_level l, Temp_label label) {
	switch (v->kind) {
	case A_simpleVar:
	{
		E_enventry x = S_look(venv, v->u.simple);

		if (!x || x->kind != E_varEntry) {
			EM_error(v->pos, "undefineformald variable %s", S_name(v->u.simple));
			return expTy(NULL, Ty_Int());
		}

		return expTy(Tr_simpleVar(x->u.var.access, l),
		             actual_ty(x->u.var.ty));
	}
	case A_fieldVar:
	{
		struct expty lvalue = transVar(venv, tenv, v->u.field.var, l, label);

		if (lvalue.ty->kind != Ty_record) {
			EM_error(v->pos, "not a record type");
			return expTy(NULL, Ty_Int());
		}

		Ty_fieldList fields = lvalue.ty->u.record;
		int field_order = 0;

		while (fields && fields->head->name != v->u.field.sym) {
			fields = fields->tail;
			field_order++;
		}
		if (fields == NULL) {
			EM_error(v->pos, "field %s doesn't exist", S_name(v->u.field.sym));
			return expTy(NULL, Ty_Int());
		}

		return expTy(Tr_fieldVar(lvalue.exp, field_order),
		             actual_ty(fields->head->ty));
	}
	case A_subscriptVar:
	{
		struct expty lvalue = transVar(venv, tenv, v->u.subscript.var, l, label);
		struct expty index = transExp(venv, tenv, v->u.subscript.exp, l, label);

		if (lvalue.ty->kind != Ty_array) {
			EM_error(v->pos, "array type required");
			return expTy(NULL, Ty_Int());
		}
		if (index.ty->kind != Ty_int) {
			EM_error(v->pos, "index is not an int");
			return expTy(NULL, Ty_Int());
		}
		return expTy(Tr_arrayVar(lvalue.exp, index.exp),
		             actual_ty(lvalue.ty->u.array));
	}
	}
	assert(0); /* should have returned from some clause of the switch */
}

void loopVar(S_table venv, A_var v) {
	switch (v->kind) {
	case A_simpleVar:
	{
		E_enventry x = S_look(venv, v->u.simple);

		if (x->readonly) {
			EM_error(v->pos, "loop variable can't be assigned");
			return;
		}
		return;
	}
	case A_fieldVar:
	{
		loopVar(venv, v->u.field.var);
		return;
	}
	case A_subscriptVar:
		loopVar(venv, v->u.subscript.var);
		return;
	}
	assert(0); /* should have returned from some clause of the switch */
}

struct expty transExp(S_table venv, S_table tenv, A_exp a, Tr_level l, Temp_label label) {
	switch (a->kind) {
	case A_varExp:
		return transVar(venv, tenv, a->u.var, l, label);
	case A_nilExp:
		return expTy(Tr_nil(), Ty_Nil());
	case A_intExp:
		return expTy(Tr_int(a->u.intt), Ty_Int());
	case A_stringExp:
		return expTy(Tr_string(a->u.stringg), Ty_String());
	case A_callExp:
	{
		E_enventry x = S_look(venv, a->u.call.func);

		if (!x || x->kind != E_funEntry) {
			EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
			return expTy(NULL, Ty_Int());
		}

		Ty_tyList params = x->u.fun.formals;
		A_expList args = a->u.call.args;
		Tr_expList head = Tr_ExpList(NULL, NULL),
		           tail = head;


		for (; args && params; args = args->tail, params = params->tail) {
			struct expty exp = transExp(venv, tenv, args->head, l, label);

			if (actual_ty(exp.ty)->kind != actual_ty(params->head)->kind && // magic judge
			        !(actual_ty(params->head)->kind == Ty_record && actual_ty(exp.ty)->kind == Ty_nil)) {
				EM_error(args->head->pos, "para type mismatch");
			}

			tail->tail = Tr_ExpList(exp.exp, NULL);
			tail = tail->tail;
		}
		if (params != NULL || args != NULL) {
			EM_error(a->pos, "too many params in function %s", S_name(a->u.call.func));
		}

		head = head->tail;
		return expTy(Tr_call(x->u.fun.label, head, l, x->u.fun.level),
		             actual_ty(x->u.fun.result));
	}
	case A_opExp:
	{
		A_oper oper = a->u.op.oper;
		struct expty left = transExp(venv, tenv, a->u.op.left, l, label);
		struct expty right = transExp(venv, tenv, a->u.op.right, l, label);

		if (oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp) {
			if (actual_ty(left.ty)->kind != Ty_int) {
				EM_error(a->u.op.left->pos, "integer required");
				return expTy(NULL, Ty_Int());
			}

			if (actual_ty(right.ty)->kind != Ty_int) {
				EM_error(a->u.op.right->pos, "integer required");
				return expTy(NULL, Ty_Int());
			}

			return expTy(Tr_arithmetic(oper, left.exp, right.exp),
			             Ty_Int());
		}
		else {
			if (actual_ty(left.ty) != actual_ty(right.ty) && // magic judge
			        !(actual_ty(left.ty)->kind == Ty_record && actual_ty(right.ty)->kind == Ty_nil)) {
				EM_error(a->u.op.left->pos, "same type required");
			}
			Tr_exp tr_exp;
			if (actual_ty(left.ty)  == Ty_String()) {
				E_enventry fun_entry = S_look(venv, S_Symbol("stringEqual"));
				Tr_expList args = Tr_ExpList(left.exp, Tr_ExpList(right.exp, NULL));
				Tr_exp cmp_call = Tr_call(fun_entry->u.fun.label, args, l, fun_entry->u.fun.level);
				tr_exp = Tr_strcmp(oper, cmp_call);
			} else {
				tr_exp = Tr_condition(oper, left.exp, right.exp);
			}

			return expTy(tr_exp, Ty_Int());
		}
	}
	case A_recordExp:
	{
		Ty_ty record = actual_ty(S_look(tenv, a->u.record.typ));
		// EM_error(a->pos, "record %s type %d", S_name(a->u.record.typ), record->kind == Ty_record);
		if (!record) {
			EM_error(a->pos, "undefined type %s", S_name(a->u.record.typ));
			return expTy(NULL, Ty_Int());
		}
		if (record->kind != Ty_record) {
			EM_error(a->pos, "not record type %s", S_name(a->u.record.typ));
			return expTy(NULL, record);
		}

		Ty_fieldList params = record->u.record;
		A_efieldList args = a->u.record.fields;
		Tr_expList head = Tr_ExpList(NULL, NULL),
		           tail = head;

		for (; args && params; args = args->tail, params = params->tail) {
			if (params->head->name != args->head->name) {
				EM_error(a->pos, "expected %s but get %s", S_name(params->head->name), S_name(args->head->name));
			}

			struct expty exp = transExp(venv, tenv, args->head->exp, l, label);

			if (actual_ty(params->head->ty) != actual_ty(exp.ty) &&
			        !(actual_ty(params->head->ty)->kind == Ty_record && actual_ty(exp.ty)->kind == Ty_nil)) {
				EM_error(a->pos, "type not match");
			}

			tail->tail = Tr_ExpList(exp.exp, NULL);
			tail = tail->tail;
		}
		if (params != NULL || args != NULL) {
			EM_error(a->pos, "fields number of record %s does not match", S_name(a->u.record.typ));
		}

		head = head->tail;

		return expTy(Tr_recordCreation(head), record);
	}
	case A_seqExp:
	{
		A_expList seq = a->u.seq;
		Tr_exp result_exp = Tr_nil();
		Ty_ty result_type = Ty_Void();
		while (seq) {
			struct expty exp = transExp(venv, tenv, seq->head, l, label);
			result_exp = Tr_eseq(result_exp, exp.exp);
			result_type = exp.ty;
			seq = seq->tail;
		}
		return expTy(result_exp, result_type);
	}
	case A_assignExp:
	{
		struct expty lvalue = transVar(venv, tenv, a->u.assign.var, l, label);
		struct expty exp = transExp(venv, tenv, a->u.assign.exp, l, label);

		loopVar(venv, a->u.assign.var);
		if (actual_ty(lvalue.ty) != actual_ty(exp.ty) &&
		        !(actual_ty(lvalue.ty)->kind == Ty_record && actual_ty(exp.ty)->kind == Ty_nil)) {
			EM_error(a->pos, "unmatched assign exp");
		}
		return expTy(Tr_assign(lvalue.exp, exp.exp),
		             Ty_Void());
	}
	case A_ifExp:
	{
		struct expty then = transExp(venv, tenv, a->u.iff.then, l, label);
		struct expty test = transExp(venv, tenv, a->u.iff.test, l, label);

		if (actual_ty(test.ty)->kind != Ty_int) {
			EM_error(a->u.iff.test->pos, "test exp should be an int");
		}

		if (a->u.iff.elsee) {
			struct expty elsee = transExp(venv, tenv, a->u.iff.elsee, l, label);
			if (actual_ty(then.ty) != actual_ty(elsee.ty) &&
			        !(actual_ty(then.ty)->kind == Ty_record && actual_ty(elsee.ty)->kind == Ty_nil)) {
				EM_error(a->u.iff.then->pos, "then exp and else exp type mismatch");
			}

			return expTy(Tr_ifthenelse(test.exp, then.exp, elsee.exp),
			             then.ty);
		} else {
			if (actual_ty(then.ty)->kind != Ty_void) {
				EM_error(a->u.iff.then->pos, "if-then exp's body must produce no value");
			}

			return expTy(Tr_ifthen(test.exp, then.exp),
			             then.ty);
		}
	}
	case A_whileExp:
	{
		Temp_label new_label = Temp_newNamedLabel("break");
		struct expty test = transExp(venv, tenv, a->u.whilee.test, l, label);
		struct expty body = transExp(venv, tenv, a->u.whilee.body, l, new_label);

		if (actual_ty(test.ty)->kind != Ty_int) {
			EM_error(a->u.whilee.test->pos, "test exp should be an int");
		}
		if (actual_ty(body.ty)->kind != Ty_void) {
			EM_error(a->u.whilee.body->pos, "while body must produce no value");
		}

		return expTy(Tr_while(test.exp, body.exp, new_label),
		             Ty_Void());
	}
	case A_forExp:
	{
		Temp_label new_label = Temp_newNamedLabel("break");
		struct expty low = transExp(venv, tenv, a->u.forr.lo, l, label);
		struct expty high = transExp(venv, tenv, a->u.forr.hi, l, label);

		if (actual_ty(low.ty)->kind != Ty_int) {
			EM_error(a->u.forr.lo->pos, "for exp's range type is not integer");
		}
		if (actual_ty(high.ty)->kind != Ty_int) {
			EM_error(a->u.forr.hi->pos, "for exp's range type is not integer");
		}

		S_beginScope(venv);
		Tr_access access = Tr_allocLocal(l, a->u.forr.escape, NULL);
		E_enventry enventry = E_ROVarEntry(access, Ty_Int());
		S_enter(venv, a->u.forr.var, enventry);

		struct expty body = transExp(venv, tenv, a->u.forr.body, l, new_label);
		struct expty whilebody = transExp(venv, tenv, a->u.forr.body, l, new_label);

		S_endScope(venv);
		if (actual_ty(body.ty)->kind != Ty_void) {
			EM_error(a->u.forr.body->pos, "body exp should be void");
		}

		return expTy(Tr_for(access, low.exp, high.exp, body.exp, whilebody.exp, new_label),
		             Ty_Void());
	}
	case A_breakExp:
		return expTy(Tr_break(label),
		             Ty_Void());
	case A_letExp:
	{
		S_beginScope(venv);
		S_beginScope(tenv);

		A_decList d;

		for (d = a->u.let.decs; d; d = d->tail) {
			transDec(venv, tenv, d->head, l, label);
		}

		struct expty exp = transExp(venv, tenv, a->u.let.body, l, label);

		S_endScope(tenv);
		S_endScope(venv);
		return exp;
	}
	case A_arrayExp:
	{
		Ty_ty array = S_look(tenv, a->u.array.typ);
		array = actual_ty(array);

		if (!array) {
			EM_error(a->pos, "undefined type %s", S_name(a->u.array.typ));
			return expTy(NULL, Ty_Int());
		}
		if (array->kind != Ty_array) {
			EM_error(a->pos, "not array type %s", S_name(a->u.record.typ));
			return expTy(NULL, array);
		}

		struct expty size = transExp(venv, tenv, a->u.array.size, l, label);
		struct expty init = transExp(venv, tenv, a->u.array.init, l, label);

		if (actual_ty(size.ty)->kind != Ty_int) {
			EM_error(a->u.array.size->pos, "type of size expression should be int");
		}
		if (actual_ty(init.ty) != actual_ty(array->u.array) &&
		        !(actual_ty(array->u.array)->kind == Ty_record && actual_ty(init.ty)->kind == Ty_nil)) {
			EM_error(a->u.array.init->pos, "type mismatch");
		}

		return expTy(Tr_arrayCreation(size.exp, init.exp),
		             array);
	}

	}
	assert(0); /* should have returned from some clause of the switch */
}

U_boolList makeEscList(A_fieldList params) {
	if (params == NULL) {
		return NULL;
	}

	return U_BoolList(params->head->escape, makeEscList(params->tail));
}

Ty_tyList makeTyList(S_table tenv, A_fieldList params) {
	if (params == NULL) {
		return NULL;
	}
	return Ty_TyList(S_look(tenv, params->head->typ), makeTyList(tenv, params->tail));
}

void transDec(S_table venv, S_table tenv, A_dec d, Tr_level l, Temp_label label) {
	switch (d->kind) {
	case A_varDec:
	{
		struct expty init = transExp(venv, tenv, d->u.var.init, l, label);

		if (d->u.var.typ) {
			Ty_ty type = S_look(tenv, d->u.var.typ);

			if (!type) {
				EM_error(d->u.var.init->pos, "type not exist %s", S_name(d->u.var.typ));
			}
			if (actual_ty(type) != actual_ty(init.ty) &&
			        !(actual_ty(type)->kind == Ty_record && actual_ty(init.ty)->kind == Ty_nil)) {
				EM_error(d->u.var.init->pos, "type mismatch");
			}
		}
		else if (actual_ty(init.ty)->kind == Ty_nil) {
			EM_error(d->u.var.init->pos, "init should not be nil without type specified");
		}
		S_enter(venv, d->u.var.var, E_VarEntry(Tr_allocLocal(l, d->u.var.escape, init.exp), init.ty));
		break;
	}
	case A_typeDec:
	{
		TAB_table name_table = TAB_empty();
		A_nametyList types = d->u.type;

		// head
		while (types) {
			if (TAB_look(name_table, types->head->name) != NULL) {
				EM_error(d->pos, "two types have the same name");
			}
			else {
				TAB_enter(name_table, types->head->name, (void *) 1);
			}

			types = types->tail;
		}

		// body
		types = d->u.type;
		while (types) {
			S_enter(tenv, types->head->name, Ty_Name(types->head->name, NULL));
			types = types->tail;
		}

		types = d->u.type;
		while (types) {
			Ty_ty type = S_look(tenv, types->head->name);
			type->u.name.ty = transTy(tenv, types->head->ty);
			types = types->tail;
		}

		// cycle
		types = d->u.type;
		while (types) {
			Ty_ty init = S_look(tenv, types->head->name);
			Ty_ty type = init;

			while ((type = type->u.name.ty)->kind == Ty_name) {
				if (type == init) {
					EM_error(d->pos, "illegal type cycle");
					init->u.name.ty = Ty_Int();
					break;
				}
			}
			types = types->tail;
		}

		break;
	}
	case A_functionDec:
	{
		TAB_table name_table = TAB_empty();
		A_fundecList funcs = d->u.function;

		while (funcs) {
			// EM_error(d->pos, "function dec %s", S_name(funcs->head->name));
			if (TAB_look(name_table, funcs->head->name) != NULL) {
				EM_error(d->pos, "two functions with the same name %s in batch declaration\n",
				         S_name(funcs->head->name));
			}
			TAB_enter(name_table, funcs->head->name, (void *) 1);
			funcs = funcs->tail;
		}

		// head
		funcs = d->u.function;
		while (funcs) {
			Ty_ty result = Ty_Void();
			if (funcs->head->result) {
				result = S_look(tenv, funcs->head->result);

				if (!result) {
					EM_error(funcs->head->pos, "undefined result type %s", S_name(funcs->head->result));
					result = Ty_Void();
				}
			}

			Temp_label new_label = Temp_newlabel();
			U_boolList escapes = makeEscList(funcs->head->params);
			Tr_level new_level = Tr_newLevel(l, new_label, escapes);

			Ty_tyList tys = makeTyList(tenv, funcs->head->params);
			E_enventry x = E_FunEntry(new_level, new_label, tys, result);
			S_enter(venv, funcs->head->name, x);

			funcs = funcs->tail;
		}

		// body
		funcs = d->u.function;
		while (funcs) {
			E_enventry fun_entry = S_look(venv, funcs->head->name);
			Tr_accessList accesses = Tr_formals(fun_entry->u.fun.level);
			A_fieldList params = funcs->head->params;

			S_beginScope(venv);

			for (; params; params = params->tail, accesses = accesses->tail) {
				Ty_ty type = S_look(tenv, params->head->typ);
				E_enventry var_entry = E_VarEntry(accesses->head, type);
				S_enter(venv, params->head->name, var_entry);
			}

			struct expty exp = transExp(venv, tenv, funcs->head->body, fun_entry->u.fun.level, label);

			S_endScope(venv);

			Ty_ty expected = actual_ty(fun_entry->u.fun.result);
			Ty_ty actual = actual_ty(exp.ty);

			if (expected->kind == Ty_void && actual->kind != Ty_void) {
				EM_error(funcs->head->pos, "procedure returns value");
			} else if (expected != actual && !(expected->kind == Ty_record && actual->kind == Ty_nil)) {
				EM_error(funcs->head->pos, "procedure returns unexpected type");
			}

			Tr_procEntryExit(fun_entry->u.fun.level, exp.exp, accesses);

			funcs = funcs->tail;
		}

		break;
	}
	}
}

Ty_fieldList makeFieldList(S_table tenv, A_fieldList fields) {
	Ty_ty type = S_look(tenv, fields->head->typ);

	if (!type) {
		EM_error(fields->head->pos, "undefined type %s", S_name(fields->head->typ));
		type = Ty_Int();
	}

	Ty_field field = Ty_Field(fields->head->name, type);

	if (fields->tail == NULL) {
		return Ty_FieldList(field, NULL);
	} else {
		return Ty_FieldList(field, makeFieldList(tenv, fields->tail));
	}
}

Ty_ty transTy (S_table tenv, A_ty a) {
	switch (a->kind) {
	case A_nameTy:
	{
		Ty_ty type = S_look(tenv, a->u.name);

		if (!type) {
			EM_error(a->pos, "undefined type %s", S_name(a->u.name));
			return Ty_Int();
		}
		return Ty_Name(a->u.name, type);
	}
	case A_recordTy:
		return Ty_Record(makeFieldList(tenv, a->u.record));
	case A_arrayTy:
	{
		Ty_ty type = S_look(tenv, a->u.array);

		if (!type) {
			EM_error(a->pos, "undefined type %s", S_name(a->u.array));
			return Ty_Int();
		}
		return Ty_Array(type);
	}
	}
	return NULL;
}

F_fragList SEM_transProg(A_exp exp) {
	Temp_label func_label = Temp_namedlabel("tigermain");
	Tr_level main_level = Tr_newLevel(Tr_outermost(), func_label, NULL);
	E_enventry fun_entry = E_FunEntry(main_level, func_label, NULL, Ty_Void());

	struct expty body_exp = transExp(E_base_venv(), E_base_tenv(), exp, main_level, NULL);

	Tr_procEntryExit(fun_entry->u.fun.level, body_exp.exp, NULL);

	return Tr_getResult();
}

