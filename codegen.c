#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "errormsg.h"
#include "tree.h"
#include "assem.h"
#include "frame.h"
#include "codegen.h"
#include "table.h"

int revernum = 0;
Temp_temp paramreg(int index) {
	switch (index) {
	case 0:
		return F_RDI();
	case 1:
		return F_RSI();
	case 2:
		return F_RDX();
	case 3:
		return F_RCX();
	case 4:
		return F_R8();
	case 5:
		return F_R9();
	}
}
struct exp_munch {
	AS_instrList list;
	Temp_temp temp;
};

struct exp_munch munchExp(F_frame frame, T_exp exp);
AS_instrList munchStm(F_frame frame, T_stm stm);

/*
*  helper
*/
T_expList reverse(T_expList original) {
	if (original == NULL)
		return NULL;
	revernum++;
	T_expList *last = &original;
	while ((*last)->tail) last = &((*last)->tail);

	T_exp exp = (*last)->head;
	*last = NULL;
	return T_ExpList(exp, reverse(original));
}

AS_instr reg_to_reg(Temp_temp src, Temp_temp dst) {
	return AS_Move(String("movq `s0, `d0"), Temp_TempList(dst, NULL), Temp_TempList(src, NULL));
}

Temp_tempList callerSaved() {
	return Temp_TempList(F_RAX(),
	                     Temp_TempList(F_RSI(),
	                                   Temp_TempList(F_RDI(),
	                                           Temp_TempList(F_RDX(),
	                                                   Temp_TempList(F_RCX(),
	                                                           Temp_TempList(F_R8(),
	                                                                   Temp_TempList(F_R9(),
	                                                                           Temp_TempList(F_R10(),
	                                                                                   Temp_TempList(F_R11(), NULL)))))))));
}

/*
*  munch
*/
AS_instrList munchStm(F_frame frame, T_stm stm) {
	switch (stm->kind) {
	case T_LABEL: {
		AS_instr instr = AS_Label(Temp_labelstring(stm->u.LABEL), stm->u.LABEL);
		return AS_InstrList(instr, NULL);
	}
	case T_JUMP: {
		AS_instr instr = AS_Oper(String("jmp `j0"), NULL, NULL, AS_Targets(stm->u.JUMP.jumps));
		return AS_InstrList(instr, NULL);
	}
	case T_CJUMP: {
		//return a AS_instr and a register the result is in the register
		struct exp_munch left = munchExp(frame, stm->u.CJUMP.left);
		struct exp_munch right = munchExp(frame, stm->u.CJUMP.right);
		AS_instr cmp_instr = AS_Oper(String("cmpq `s0, `s1"), NULL, Temp_TempList(right.temp, Temp_TempList(left.temp, NULL)), NULL);
		AS_instr jump_instr = NULL;
		switch (stm->u.CJUMP.op) {
		case T_eq:
			jump_instr = AS_Oper(String("je `j0"), NULL, NULL, AS_Targets(Temp_LabelList(stm->u.CJUMP.true, NULL)));
			break;
		case T_ne:
			jump_instr = AS_Oper(String("jne `j0"), NULL, NULL, AS_Targets(Temp_LabelList(stm->u.CJUMP.true, NULL)));
			break;
		case T_gt:
			jump_instr = AS_Oper(String("jg `j0"), NULL, NULL, AS_Targets(Temp_LabelList(stm->u.CJUMP.true, NULL)));
			break;
		case T_ge:
			jump_instr = AS_Oper(String("jge `j0"), NULL, NULL, AS_Targets(Temp_LabelList(stm->u.CJUMP.true, NULL)));
			break;
		case T_lt:
			jump_instr = AS_Oper(String("jl `j0"), NULL, NULL, AS_Targets(Temp_LabelList(stm->u.CJUMP.true, NULL)));
			break;
		case T_le:
			jump_instr = AS_Oper(String("jle `j0"), NULL, NULL, AS_Targets(Temp_LabelList(stm->u.CJUMP.true, NULL)));
			break;
		case T_ugt:
			jump_instr = AS_Oper(String("ja `j0"), NULL, NULL, AS_Targets(Temp_LabelList(stm->u.CJUMP.true, NULL)));
			break;
		case T_uge:
			jump_instr = AS_Oper(String("jae `j0"), NULL, NULL, AS_Targets(Temp_LabelList(stm->u.CJUMP.true, NULL)));
			break;
		case T_ult:
			jump_instr = AS_Oper(String("jb `j0"), NULL, NULL, AS_Targets(Temp_LabelList(stm->u.CJUMP.true, NULL)));
			break;
		case T_ule:
			jump_instr = AS_Oper(String("jbe `j0"), NULL, NULL, AS_Targets(Temp_LabelList(stm->u.CJUMP.true, NULL)));
			break;
		}
		AS_instrList jump_destination = AS_InstrList(jump_instr,  NULL);
		AS_instrList compare_jump_destination = AS_InstrList(cmp_instr, jump_destination );

		return AS_splice(left.list, AS_splice(right.list, compare_jump_destination));
	}
	case T_MOVE:
	{
		if (stm->u.MOVE.dst->kind == T_TEMP) {
			struct exp_munch src = munchExp(frame, stm->u.MOVE.src);
			Temp_temp dst = stm->u.MOVE.dst->u.TEMP;

			return AS_splice(src.list, AS_InstrList(AS_Move("movq `s0, `d0", Temp_TempList(dst, NULL), Temp_TempList(src.temp, NULL)), NULL)   );

		}

		/*
		* movq src, mem
		*/
		if (stm->u.MOVE.dst->kind == T_MEM) {
			struct exp_munch src = munchExp(frame, stm->u.MOVE.src);
			struct exp_munch mem = munchExp(frame, stm->u.MOVE.dst->u.MEM);
			AS_instrList op3 = AS_InstrList(AS_Oper("movq `s0, (`s1)", NULL, Temp_TempList(src.temp, Temp_TempList(mem.temp, NULL)), AS_Targets(NULL)), NULL);
			return AS_splice(mem.list, AS_splice(src.list, op3));

		}
	}
	case T_EXP:
		return munchExp(frame, stm->u.EXP).list;
	default:
		assert(0);
	}
}

struct exp_munch munchExp(F_frame frame, T_exp exp) {
	switch (exp->kind) {

	case T_BINOP: {

		if (exp->u.BINOP.op == T_plus) {
			Temp_temp d = Temp_newtemp();
			struct exp_munch left = munchExp(frame, exp->u.BINOP.left);
			struct exp_munch right = munchExp(frame, exp->u.BINOP.right);

			AS_instr instr1 = AS_Move("movq `s0, `d0", Temp_TempList(d, NULL), Temp_TempList(left.temp, NULL));
			AS_instr instr2 = AS_Oper("addq `s0, `d0", Temp_TempList(d, NULL),
			                          Temp_TempList(right.temp, Temp_TempList(d, NULL)), AS_Targets(NULL));
			AS_instrList instr3 = AS_InstrList(instr1, AS_InstrList(instr2, NULL));
			AS_instrList instr4 = AS_splice(left.list, AS_splice(right.list, instr3));
			struct exp_munch result = {.list = instr4, .temp = d};
			return result;
		}

		/*
		 * movq left, dst
		 * subq right, dst
		 */
		if (exp->u.BINOP.op == T_minus) {
			Temp_temp d = Temp_newtemp();
			struct exp_munch left = munchExp(frame, exp->u.BINOP.left);
			struct exp_munch right = munchExp(frame, exp->u.BINOP.right);

			AS_instr instr1 = AS_Move("movq `s0, `d0", Temp_TempList(d, NULL), Temp_TempList(left.temp, NULL));
			AS_instr instr2 = AS_Oper("subq `s0, `d0", Temp_TempList(d, NULL),
			                          Temp_TempList(right.temp, Temp_TempList(d, NULL)), AS_Targets(NULL));
			AS_instrList instr3 = AS_InstrList(instr1, AS_InstrList(instr2, NULL));
			AS_instrList instr4 = AS_splice(left.list, AS_splice(right.list, instr3));
			struct exp_munch result = {.list = instr4, .temp = d};
			return result;
		}

		/*
		 * movq left, dst
		 * imul right, dst
		 */
		if (exp->u.BINOP.op == T_mul) {
			Temp_temp d = Temp_newtemp();
			struct exp_munch left = munchExp(frame, exp->u.BINOP.left);
			struct exp_munch right = munchExp(frame, exp->u.BINOP.right);

			AS_instr instr1 = AS_Move("movq `s0, `d0", Temp_TempList(d, NULL), Temp_TempList(left.temp, NULL));
			AS_instr instr2 = AS_Oper("imul `s0, `d0", Temp_TempList(d, NULL),
			                          Temp_TempList(right.temp, Temp_TempList(d, NULL)), AS_Targets(NULL));
			AS_instrList instr3 = AS_InstrList(instr1, AS_InstrList(instr2, NULL));
			AS_instrList instr4 = AS_splice(left.list, AS_splice(right.list, instr3));
			struct exp_munch result = {.list = instr4, .temp = d};
			return result;
		}

		/*
		 * movq left, %rax
		 * cqto #use rax's sign bit to fill edx
		 * idivq right #now, result in rax and remainder in edx
		 */
		if (exp->u.BINOP.op == T_div) {
			Temp_temp d = Temp_newtemp();
			struct exp_munch left = munchExp(frame, exp->u.BINOP.left);
			struct exp_munch right = munchExp(frame, exp->u.BINOP.right);
			AS_instr instr1 = AS_Move("movq `s0, `d0", Temp_TempList(F_RAX(), NULL), Temp_TempList(left.temp, NULL));
			AS_instr instr2 = AS_Oper("cqto", Temp_TempList(F_RDX(), Temp_TempList(F_RAX(), NULL)), Temp_TempList(F_RAX(), NULL), AS_Targets(NULL));
			AS_instr instr3 = AS_Oper("idivq `s0", Temp_TempList(F_RDX(), Temp_TempList(F_RAX(), NULL)),
			                          Temp_TempList(right.temp, Temp_TempList(F_RDX(), Temp_TempList(F_RAX(), NULL))), AS_Targets(NULL));
			AS_instr instr4 = AS_Move("movq `s0, `d0", Temp_TempList(d, NULL), Temp_TempList(F_RAX(), NULL));

			AS_instrList opt5 = AS_InstrList(instr1, AS_InstrList(instr2, AS_InstrList(instr3, AS_InstrList(instr4, NULL))));
			AS_instrList opt6 = AS_splice(left.list, AS_splice(right.list, opt5));
			struct exp_munch result = {.list = opt6, .temp = d};
			return result;
		}
	}
	case T_MEM: {
		Temp_temp d = Temp_newtemp();
		struct exp_munch addr = munchExp(frame, exp->u.MEM);

		AS_instrList instr1 = AS_InstrList(AS_Oper("movq (`s0), `d0", Temp_TempList(d, NULL), Temp_TempList(addr.temp, NULL), AS_Targets(NULL)), NULL);
		AS_instrList opt6 = AS_splice(addr.list, instr1);
		struct exp_munch result = {.list = opt6, .temp = d};
		return result;
	}
	case T_TEMP: {
		struct exp_munch result = {.list = NULL, .temp = exp->u.TEMP};
		return result;
	}
	case T_ESEQ: {
		printf("munchExp: T_ESEQ should be eliminated after canonicalization\n");
		assert(0);
	}
	case T_NAME: {
		char *inst = checked_malloc(100 * sizeof(char));
		Temp_temp d = Temp_newtemp();

		sprintf(inst, "movq $%s, `d0", Temp_labelstring(exp->u.NAME));
		AS_instrList opt6 = AS_InstrList(AS_Oper(inst, Temp_TempList(d, NULL), NULL, AS_Targets(NULL)), NULL);
		struct exp_munch result = {.list = opt6, .temp = d};
		return result;
	}
	case T_CONST: {
		Temp_temp temp = Temp_newtemp();
		char *inst = checked_malloc(50 * sizeof(char));
		sprintf(inst, "movq $%d, `d0", exp->u.CONST);
		fprintf(stderr, " num %s\n", inst);
		struct exp_munch result = {.list = AS_InstrList(AS_Oper(inst, Temp_TempList(temp, NULL), NULL, AS_Targets(NULL)), NULL), .temp = temp};
		return result;
	}
	case T_CALL: {
		// put args to stack
		AS_instrList prepare_args = NULL;
		AS_instrList put_args = NULL;
		int arg_num = 0;
		revernum = 0;
		fprintf(stderr, "revernum : %d\n", revernum);
		T_expList args = reverse(exp->u.CALL.args);
		int pushnum = 0;
		while (args) {
			arg_num++;
			T_exp arg = args->head;
			int index = revernum - arg_num;
			fprintf(stderr, "munchExp T_call %s\n", Temp_labelstring(exp->u.CALL.fun->u.NAME));
			if (!strcmp(Temp_labelstring(exp->u.CALL.fun->u.NAME), "printi")
			        || (!strcmp(Temp_labelstring(exp->u.CALL.fun->u.NAME), "print"))
			        || (!strcmp(Temp_labelstring(exp->u.CALL.fun->u.NAME), "malloc"))
			        || (!strcmp(Temp_labelstring(exp->u.CALL.fun->u.NAME), "initArray"))
			        || (!strcmp(Temp_labelstring(exp->u.CALL.fun->u.NAME), "getchar"))
			        || (!strcmp(Temp_labelstring(exp->u.CALL.fun->u.NAME), "ord"))
			        || (!strcmp(Temp_labelstring(exp->u.CALL.fun->u.NAME), "chr"))
			        || (!strcmp(Temp_labelstring(exp->u.CALL.fun->u.NAME), "stringEqual")) )
			{
				fprintf(stderr, "munchExp T_call stdlibstdlibstdlibstdlibstdlibstdlibstdlibstdlib\n");
				if ((revernum - arg_num) <= 5)
				{
					fprintf(stderr, "munchExp,T_call is reg\n");
					struct exp_munch munched = munchExp(frame, arg);
					prepare_args = AS_splice(prepare_args, munched.list);
					AS_instr instr = AS_Move(String("movq `s0, `d0"), Temp_TempList(paramreg(index), NULL), Temp_TempList(munched.temp, NULL));

					put_args = AS_splice(put_args, AS_InstrList(instr, NULL));

				}
				else
				{
					fprintf(stderr, "munchExp,T_call is mem\n");
					struct exp_munch munched = munchExp(frame, arg);
					prepare_args = AS_splice(prepare_args, munched.list);
					AS_instr instr = AS_Oper(String("pushq `s0"), NULL, Temp_TempList(munched.temp, NULL), NULL);
					put_args = AS_splice(put_args, AS_InstrList(instr, NULL));
				}
			}
			else {
				if (arg_num == revernum) {
					fprintf(stderr, "munchExp,T_call is static link\n");
					pushnum++;
					struct exp_munch munched = munchExp(frame, arg);
					prepare_args = AS_splice(prepare_args, munched.list);
					AS_instr instr = AS_Oper(String("pushq `s0"), NULL, Temp_TempList(munched.temp, NULL), NULL);
					put_args = AS_splice(put_args, AS_InstrList(instr, NULL));
				}
				else if ((revernum - arg_num) <= 6) {
					fprintf(stderr, "munchExp,T_call is reg\n");
					struct exp_munch munched = munchExp(frame, arg);
					prepare_args = AS_splice(prepare_args, munched.list);
					AS_instr instr = AS_Move(String("movq `s0, `d0"), Temp_TempList(paramreg(index - 1), NULL), Temp_TempList(munched.temp, NULL));
					put_args = AS_splice(put_args, AS_InstrList(instr, NULL));
				}
				else {
					fprintf(stderr, "munchExp,T_call is mem\n");
					pushnum++;
					struct exp_munch munched = munchExp(frame, arg);
					prepare_args = AS_splice(prepare_args, munched.list);
					AS_instr instr = AS_Oper(String("pushq `s0"), NULL, Temp_TempList(munched.temp, NULL), NULL);
					put_args = AS_splice(put_args, AS_InstrList(instr, NULL));
				}
			}

			args = args->tail;
		}

		if (exp->u.CALL.fun->kind != T_NAME) {
			printf("munchExp: fun should be T_NAME for call exp, not %d\n", exp->u.CALL.fun->kind);
			assert(0);
		}// set caller save register as dst
		AS_instr call = AS_Oper(String("callq `j0"), callerSaved(),
		                        NULL, AS_Targets(Temp_LabelList(exp->u.CALL.fun->u.NAME, NULL)));
		// fetch result
		Temp_temp temp = Temp_newtemp();
		AS_instr fetch = AS_Move(String("movq `s0, `d0"), Temp_TempList(temp, NULL), Temp_TempList(F_RV(), NULL));
		// splice instrs together
		AS_instrList list = AS_splice(
		                        prepare_args, AS_splice(
		                            put_args, AS_InstrList(
		                                call, AS_InstrList(
		                                    fetch, NULL))));
		if (pushnum) {
			// resotre stack
			char *inst = checked_malloc(50 * sizeof(char));
			sprintf(inst, "addq $%d, %%rsp", pushnum * 8);
			AS_instr incr_esp = AS_Oper(String(inst), NULL, NULL, NULL);

			list = AS_splice(list, AS_InstrList(incr_esp, NULL));
		}

		struct exp_munch result = {.list = list, .temp = temp};
		return result;
	}
	default:
		assert(0);
	}
}


// use Maximal Munch
AS_instrList F_codegen(F_frame frame, T_stmList stm_list) {
	AS_instrList instr_list = NULL;

	// move callee-saved reg
	Temp_temp r12_temp = Temp_newtemp(),
	          r13_temp = Temp_newtemp(),
	          r14_temp = Temp_newtemp(),
	          rbx_temp = Temp_newtemp(),
	          r15_temp = Temp_newtemp();
	AS_instrList save_reg = AS_InstrList(reg_to_reg(F_R12(), r12_temp),
	                                     AS_InstrList(reg_to_reg(F_R13(), r13_temp),
	                                             AS_InstrList(reg_to_reg(F_R14(), r14_temp),
	                                                     AS_InstrList(reg_to_reg(F_RBX(), rbx_temp),
	                                                             AS_InstrList(reg_to_reg(F_R15(), r15_temp), NULL)))));

	// init local variable
	F_accessList procparams = frame->formals;
	int reg_index = 0;
	AS_instrList param_in_reg = NULL;
	while (procparams)
	{
		//it is the local
		F_access procparam_item = procparams->head;
		if (procparam_item->kind == inReg) {
			switch (reg_index) {
			case 1:
			{
				AS_instr fetch = AS_Move(String("movq `s0, `d0"), Temp_TempList(procparam_item->u.reg, NULL), Temp_TempList(F_RDI(), NULL));
				param_in_reg = AS_InstrList(fetch, NULL);
				break;
			}
			case 2:
			{
				AS_instr fetch = AS_Move(String("movq `s0, `d0"), Temp_TempList(procparam_item->u.reg, NULL), Temp_TempList(F_RSI(), NULL));
				param_in_reg = AS_InstrList(fetch, param_in_reg);
				break;
			}
			case 3:
			{
				AS_instr fetch = AS_Move(String("movq `s0, `d0"), Temp_TempList(procparam_item->u.reg, NULL), Temp_TempList(F_RDX(), NULL));
				param_in_reg = AS_InstrList(fetch, param_in_reg);
				break;
			}
			case 4:
			{
				AS_instr fetch = AS_Move(String("movq `s0, `d0"), Temp_TempList(procparam_item->u.reg, NULL), Temp_TempList(F_RCX(), NULL));
				param_in_reg = AS_InstrList(fetch, param_in_reg);
				break;
			}
			case 5:
			{
				AS_instr fetch = AS_Move(String("movq `s0, `d0"), Temp_TempList(procparam_item->u.reg, NULL), Temp_TempList(F_R8(), NULL));
				param_in_reg = AS_InstrList(fetch, param_in_reg);
				break;
			}
			case 6:
			{
				AS_instr fetch = AS_Move(String("movq `s0, `d0"), Temp_TempList(procparam_item->u.reg, NULL), Temp_TempList(F_R9(), NULL));
				param_in_reg = AS_InstrList(fetch, param_in_reg);
				break;
			}
			default:
				break;
			}
		}
		reg_index++;
		procparams = procparams->tail;
	}

	while (stm_list) {
		T_stm stm = stm_list->head;
		instr_list = AS_splice(instr_list, munchStm(frame, stm));
		stm_list = stm_list->tail;
	}

	// move saved callee-saved from temps to reg
	AS_instrList restore_reg = AS_InstrList(reg_to_reg(r12_temp, F_R12()),
	                                        AS_InstrList(reg_to_reg(r13_temp, F_R13()),
	                                                AS_InstrList(reg_to_reg(r14_temp, F_R14()),
	                                                        AS_InstrList(reg_to_reg(rbx_temp, F_RBX()),
	                                                                AS_InstrList(reg_to_reg(r15_temp, F_R15()), NULL)))));

	// put save-reg after first label
	if (param_in_reg != NULL) {
		return AS_InstrList(instr_list->head, AS_splice(save_reg, AS_splice(param_in_reg , AS_splice(instr_list->tail, restore_reg))));
	}
	else {
		return AS_InstrList(instr_list->head, AS_splice(save_reg, AS_splice(instr_list->tail, restore_reg)));
	}
}
