#include <stdio.h>
#include "util.h"
#include "table.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "printtree.h"
#include "frame.h"
#include "translate.h"

//LAB5: you can modify anything you want.

static int WORDSIZE = 8;
static struct F_fragList_ dummy = {NULL, NULL};
static F_fragList frag_head = &dummy,
                  frag_tail = &dummy;

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail) {
    Tr_accessList list = checked_malloc(sizeof(*list));
    list->head = head;
    list->tail = tail;

    return list;
}

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail) {
    Tr_expList list = checked_malloc(sizeof(*list));
    list->head = head;
    list->tail = tail;

    return list;
}

static patchList PatchList(Temp_label *head, patchList tail)
{
    patchList list;

    list = (patchList)checked_malloc(sizeof(struct patchList_));
    list->head = head;
    list->tail = tail;
    return list;
}

void doPatch(patchList tList, Temp_label label)
{
    for (; tList; tList = tList->tail)
        * (tList->head) = label;
}

patchList joinPatch(patchList first, patchList second)
{
    if (!first) return second;
    for (; first->tail; first = first->tail);
    first->tail = second;
    return first;
}

static Tr_exp Tr_Ex(T_exp exp) {
    Tr_exp tr_exp = checked_malloc(sizeof(*tr_exp));
    tr_exp->kind = Tr_ex;
    tr_exp->u.ex = exp;
    return tr_exp;
}

static Tr_exp Tr_Nx(T_stm stm) {
    Tr_exp tr_exp = checked_malloc(sizeof(*tr_exp));
    tr_exp->kind = Tr_nx;
    tr_exp->u.nx = stm;
    return tr_exp;
}

static Tr_exp Tr_Cx(struct Cx cx) {
    Tr_exp tr_exp = checked_malloc(sizeof(*tr_exp));
    tr_exp->kind = Tr_cx;
    tr_exp->u.cx = cx;
    return tr_exp;
}

static T_exp unEx(Tr_exp e) {
    switch (e->kind) {
    case Tr_ex:
        return e->u.ex;
    case Tr_nx:
        return T_Eseq(e->u.nx, T_Const(0));
    case Tr_cx: {
        Temp_temp r = Temp_newtemp();
        Temp_label t = Temp_newlabel(), f = Temp_newlabel();
        doPatch(e->u.cx.trues, t);
        doPatch(e->u.cx.falses, f);
        return T_Eseq(T_Move(T_Temp(r), T_Const(1)),
                      T_Eseq(e->u.cx.stm,
                             T_Eseq(T_Label(f),
                                    T_Eseq(T_Move(T_Temp(r), T_Const(0)),
                                           T_Eseq(T_Label(t), T_Temp(r))))));
    }
    default:
        assert(0);
    }
}

static T_stm unNx(Tr_exp e) {
    switch (e->kind) {
    case Tr_ex:
        return T_Exp(e->u.ex);
    case Tr_nx:
        return e->u.nx;
    case Tr_cx: {
        Temp_label label = Temp_newlabel();
        doPatch(e->u.cx.trues, label);
        doPatch(e->u.cx.falses, label);
        return T_Seq(e->u.cx.stm, T_Label(label));
    }
    default:
        assert(0);
    }
}

static struct Cx unCx(Tr_exp e) {
    switch (e->kind) {
    case Tr_ex: {
        // const exp
        if (e->u.ex->kind == T_CONST) {
            if (e->u.ex->u.CONST == 0) {  // false
                struct Cx direct_jump;
                direct_jump.stm = T_Jump(T_Name(NULL), Temp_LabelList(NULL, NULL));
                direct_jump.trues = PatchList(&direct_jump.stm->u.JUMP.exp->u.NAME,
                                              PatchList(&direct_jump.stm->u.JUMP.jumps->head, NULL));
                direct_jump.falses = NULL;
                return direct_jump;
            } else {  // true
                struct Cx direct_jump;
                direct_jump.stm = T_Jump(T_Name(NULL), Temp_LabelList(NULL, NULL));
                direct_jump.trues = NULL;
                direct_jump.falses = PatchList(&direct_jump.stm->u.JUMP.exp->u.NAME,
                                               PatchList(&direct_jump.stm->u.JUMP.jumps->head, NULL));
                return direct_jump;
            }
        }

        struct Cx conditional;
        conditional.stm = T_Cjump(T_ne, e->u.ex, T_Const(0), NULL, NULL);
        conditional.trues = PatchList(&conditional.stm->u.CJUMP.true, NULL);
        conditional.falses = PatchList(&conditional.stm->u.CJUMP.false, NULL);
        return conditional;
    }
    case Tr_nx:
        // printf("Translate: can not unCx a nx\n");
        assert(0);
    case Tr_cx:
        return e->u.cx;
    default:
        assert(0);
    }
}

Tr_level Tr_outermost(void) {
    static struct Tr_level_ outermost;
    outermost.frame = NULL;
    outermost.parent = NULL;

    return &outermost;
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals) {
    Tr_level level = checked_malloc(sizeof(*level));

    U_boolList escapes = U_BoolList(TRUE, formals);  // add static link as first argument
    F_frame frame = F_newFrame(name, escapes);
    level->frame = frame;
    level->parent = parent;

    return level;
}

Tr_access Tr_allocLocal(Tr_level level, bool escape, Tr_exp init) {
    F_access accessVar ;
    if (init) {
        accessVar = F_allocLocal(level->frame, escape, unEx(init));
    }
    else {
        accessVar = F_allocLocal(level->frame, escape, NULL);
    }

    Tr_access tr_access = checked_malloc(sizeof(*tr_access));
    tr_access->access = accessVar;
    tr_access->level = level;

    return tr_access;
}

static Tr_accessList makeFormalsList(F_accessList list, Tr_level level) {
    if (list == NULL) {
        return NULL;
    }

    Tr_access tr_access = checked_malloc(sizeof(*tr_access));
    tr_access->level = level;
    tr_access->access = list->head;

    return Tr_AccessList(tr_access, makeFormalsList(list->tail, level));

}

Tr_accessList Tr_formals(Tr_level level) {
    F_accessList f_access_list = F_formals(level->frame)->tail;  // skip static link
    return makeFormalsList(f_access_list, level);
}

void Tr_procEntryExit(Tr_level level, Tr_exp tr_body, Tr_accessList formals) {
    T_exp body = unEx(tr_body);
    F_accessList proclocals = level->frame->locals;
    while (proclocals)
    {
        F_access proclocal_item = proclocals->head;
        if (proclocal_item->init == NULL) {
            proclocals = proclocals->tail;
            continue;
        }

        if (proclocal_item->kind == inReg) {
            T_stm regVar = T_Move(T_Temp(proclocal_item->u.reg), proclocal_item->init);
            body = T_Eseq(regVar, body);
        }
        else {
            T_exp mem_addr = T_Binop(T_plus, T_Temp(F_FP()), T_Const(proclocal_item->u.offset));
            T_stm frame_var = T_Move(T_Mem(mem_addr), proclocal_item->init);
            body = T_Eseq(frame_var, body);
        }
        proclocals = proclocals->tail;
    }
    T_stm t_stm = T_Move(T_Temp(F_RV()), body);
    F_frag frag = F_ProcFrag(t_stm, level->frame);

    frag_tail->tail = F_FragList(frag, NULL);
    frag_tail = frag_tail->tail;
}

Tr_exp Tr_simpleVar(Tr_access access, Tr_level level) {
    // follow static link
    T_exp access_frame = T_Temp(F_FP());
    while (level != access->level) {
        access_frame = T_Mem(T_Binop(T_plus, access_frame, T_Const(WORDSIZE)));  // track up
        level = level->parent;
    }

    T_exp t_exp = F_Exp(access->access, access_frame);
    return Tr_Ex(t_exp);
}

Tr_exp Tr_fieldVar(Tr_exp ptr, int field_order) {
    if (ptr->kind != Tr_ex) {
        // printf("Translate: field var ptr should be expression\n");
        assert(0);
    }

    T_exp t_exp = T_Mem(T_Binop(T_plus, unEx(ptr), T_Const(WORDSIZE * field_order)));
    return Tr_Ex(t_exp);
}

Tr_exp Tr_arrayVar(Tr_exp ptr, Tr_exp index) {
    if (ptr->kind != Tr_ex) {
        // printf("Translate: array var ptr should be expression\n");
        assert(0);
    }

    T_exp t_exp = T_Mem(T_Binop(T_plus, unEx(ptr), T_Binop(T_mul, T_Const(WORDSIZE), unEx(index))));
    return Tr_Ex(t_exp);
}

Tr_exp Tr_nil() {
    return Tr_Ex(T_Const(0));
}

Tr_exp Tr_int(int value) {
    return Tr_Ex(T_Const(value));
}

Tr_exp Tr_string(string str) {
    Temp_label label = Temp_newlabel();
    F_frag frag = F_StringFrag(label, str);

    frag_tail->tail = F_FragList(frag, NULL);
    frag_tail = frag_tail->tail;

    return Tr_Ex(T_Name(label));
}

static T_expList unExList(Tr_expList tr_expList) {
    if (tr_expList == NULL)
        return NULL;

    return T_ExpList(tr_expList->head->u.ex, unExList(tr_expList->tail));
}

Tr_exp Tr_call(Temp_label func, Tr_expList args, Tr_level caller, Tr_level callee) {
    if (callee == Tr_outermost()){
        return Tr_Ex(F_externalCall(Temp_labelstring(func), unExList(args)));
    }

    T_exp static_link = T_Binop(T_plus, T_Temp(F_FP()), T_Const(0));  // point to current frame
    while (caller != callee->parent) {
        static_link = T_Mem(T_Binop(T_plus, static_link, T_Const(WORDSIZE)));  // point to upper level's frame
        caller = caller->parent;
    }

    T_expList t_expList = unExList(args);
    t_expList = T_ExpList(static_link, t_expList);  // add static link

    return Tr_Ex(T_Call(T_Name(func), t_expList));
}

Tr_exp Tr_arithmetic(A_oper oper, Tr_exp left, Tr_exp right) {
    T_exp t_exp;
    switch (oper) {
    case A_plusOp:
        t_exp = T_Binop(T_plus, unEx(left), unEx(right));
        break;
    case A_minusOp:
        t_exp = T_Binop(T_minus, unEx(left), unEx(right));
        break;
    case A_timesOp:
        t_exp = T_Binop(T_mul, unEx(left), unEx(right));
        break;
    case A_divideOp:
        t_exp = T_Binop(T_div, unEx(left), unEx(right));
        break;
    default:
        // printf("Translate: unexpected arithmetic operator %d", oper);
        t_exp = T_Const(0);
    }

    return Tr_Ex(t_exp);
}

Tr_exp Tr_recordCreation(Tr_expList fields) {
    // count field number
    int field_count = 0;
    Tr_expList iter = fields;
    while (iter) {
        ++field_count;
        iter = iter->tail;
    }

    // invoke external malloc to get heap memory
    Temp_temp record_ptr = Temp_newtemp();
    T_exp call_malloc = T_Call(T_Name(Temp_namedlabel("malloc")),
                               T_ExpList(T_Binop(T_mul,  T_Const(field_count), T_Const(WORDSIZE)), NULL));

    // initialize each field
    T_stm t_stm = T_Move(T_Temp(record_ptr), call_malloc);
    int i;
    for (i = 0; fields; ++i, fields = fields->tail) {
        T_exp dst = T_Binop(T_plus, T_Temp(record_ptr), T_Binop(T_mul, T_Const(WORDSIZE), T_Const(i)));  // ptr + WS * i
        T_stm stm = T_Move(T_Mem(dst), unEx(fields->head));
        t_stm = T_Seq(t_stm, stm);
    }

    T_exp t_exp = T_Eseq(t_stm, T_Temp(record_ptr));
    return Tr_Ex(t_exp);
}

Tr_exp Tr_eseq(Tr_exp first, Tr_exp second) {
    return Tr_Ex(T_Eseq(unNx(first), unEx(second)));
}

Tr_exp Tr_ifthenelse(Tr_exp test, Tr_exp then, Tr_exp elsee) {
    Temp_temp result = Temp_newtemp();

    // two branches join
    Temp_label join_label = Temp_newlabel();
    T_exp join_exp = T_Eseq(T_Label(join_label), T_Temp(result));

    // then
    Temp_label then_label = Temp_newlabel();
    T_stm then_stm = T_Seq(T_Move(T_Temp(result), unEx(then)),
                           T_Jump(T_Name(join_label), Temp_LabelList(join_label, NULL)));
    then_stm = T_Seq(T_Label(then_label), then_stm);

    // else
    Temp_label else_label = Temp_newlabel();
    T_stm else_stm = T_Seq(T_Move(T_Temp(result), unEx(elsee)),
                           T_Jump(T_Name(join_label), Temp_LabelList(join_label, NULL)));
    else_stm = T_Seq(T_Label(else_label), else_stm);

    // convert to conditional jump
    struct Cx conditional = unCx(test);
    doPatch(conditional.trues, then_label);
    doPatch(conditional.falses, else_label);

    T_exp t_exp = T_Eseq(T_Seq(conditional.stm, T_Seq(then_stm, else_stm)), join_exp);

    return Tr_Ex(t_exp);
}

Tr_exp Tr_arrayCreation(Tr_exp size_exp, Tr_exp init_exp) {
    T_exp t_exp = F_externalCall("initArray", T_ExpList(unEx(size_exp), T_ExpList(unEx(init_exp), NULL)));
    return Tr_Ex(t_exp);
}

Tr_exp Tr_condition(A_oper oper, Tr_exp left, Tr_exp right) {
    T_stm t_stm;
    switch (oper) {
    case A_eqOp:
        t_stm = T_Cjump(T_eq, unEx(left), unEx(right), NULL, NULL);
        break;
    case A_neqOp:
        t_stm = T_Cjump(T_ne, unEx(left), unEx(right), NULL, NULL);
        break;
    case A_ltOp:
        t_stm = T_Cjump(T_lt, unEx(left), unEx(right), NULL, NULL);
        break;
    case A_leOp:
        t_stm = T_Cjump(T_le, unEx(left), unEx(right), NULL, NULL);
        break;
    case A_gtOp:
        t_stm = T_Cjump(T_gt, unEx(left), unEx(right), NULL, NULL);
        break;
    case A_geOp:
        t_stm = T_Cjump(T_ge, unEx(left), unEx(right), NULL, NULL);
        break;
    default:
        // printf("Translate: unexpected condition operator %d", oper);
        assert(0);
    }

    struct Cx conditional;
    conditional.stm = t_stm;
    conditional.trues = PatchList(&t_stm->u.CJUMP.true, NULL);
    conditional.falses = PatchList(&t_stm->u.CJUMP.false, NULL);

    return Tr_Cx(conditional);
}

Tr_exp Tr_strcmp(A_oper oper, Tr_exp result) {
    T_stm t_stm;
    switch (oper) {
    case A_eqOp:
        t_stm = T_Cjump(T_eq, unEx(result), T_Const(0), NULL, NULL);
        break;
    case A_neqOp:
        t_stm = T_Cjump(T_ne, unEx(result), T_Const(0), NULL, NULL);
        break;
    case A_ltOp:
        t_stm = T_Cjump(T_lt, unEx(result), T_Const(0), NULL, NULL);
        break;
    case A_leOp:
        t_stm = T_Cjump(T_le, unEx(result), T_Const(0), NULL, NULL);
        break;
    case A_gtOp:
        t_stm = T_Cjump(T_gt, unEx(result), T_Const(0), NULL, NULL);
        break;
    case A_geOp:
        t_stm = T_Cjump(T_ge, unEx(result), T_Const(0), NULL, NULL);
        break;
    default:
        // printf("Translate: unexpected condition operator %d", oper);
        assert(0);
    }

    struct Cx conditional;
    conditional.stm = t_stm;
    conditional.trues = PatchList(&t_stm->u.CJUMP.true, NULL);
    conditional.falses = PatchList(&t_stm->u.CJUMP.false, NULL);

    return Tr_Cx(conditional);
}

Tr_exp Tr_assign(Tr_exp lvalue, Tr_exp value) {
    return Tr_Nx(T_Move(unEx(lvalue), unEx(value)));
}

Tr_exp Tr_ifthen(Tr_exp test, Tr_exp then) {
    // where if ends
    Temp_label end_label = Temp_newlabel();

    // then
    Temp_label then_label = Temp_newlabel();
    T_stm then_stm = T_Seq(T_Label(then_label), unNx(then));

    // convert to conditional jump
    struct Cx conditional = unCx(test);
    doPatch(conditional.trues, then_label);
    doPatch(conditional.falses, end_label);

    T_stm t_seq = T_Seq(conditional.stm, T_Seq(then_stm, T_Label(end_label)));

    return Tr_Nx(t_seq);
}

Tr_exp Tr_while(Tr_exp test, Tr_exp body, Temp_label done_label) {
    Temp_label test_label = Temp_newlabel();
    Temp_label body_label = Temp_newlabel();

    struct Cx conditional = unCx(test);
    doPatch(conditional.trues, body_label);
    doPatch(conditional.falses, done_label);

    T_stm test_stm = T_Seq(T_Label(test_label), conditional.stm);
    T_stm body_stm = T_Seq(T_Label(body_label),
                           T_Seq(unNx(body), T_Jump(T_Name(test_label), Temp_LabelList(test_label, NULL))));

    return Tr_Nx(T_Seq(test_stm, T_Seq(body_stm, T_Label(done_label))));
}

Tr_exp Tr_for(Tr_access loop_var_access, Tr_exp lo, Tr_exp hi, Tr_exp body, Tr_exp body_while, Temp_label done_label) {
    // init part
    T_exp limit = T_Temp(Temp_newtemp());
    T_exp loopi = F_Exp(loop_var_access->access, T_Temp(F_FP()));
    T_stm init = T_Seq(T_Move(loopi, unEx(lo)), T_Move(limit, unEx(hi)));

    // if part (to avoid overflow)
    Temp_label if_body_label = Temp_newlabel();
    T_stm if_stm = T_Seq(T_Cjump(T_le, loopi, limit, if_body_label, done_label),
                         T_Seq(T_Label(if_body_label), unNx(body)));

    Temp_label while_test_label = Temp_newlabel();
    Temp_label while_body_label = Temp_newlabel();
    T_stm jmp_body = T_Cjump(T_lt, loopi, limit, while_body_label, done_label);
    T_stm cond_stm = T_Seq(T_Label(while_test_label),  jmp_body);
    T_stm add_one = T_Move(loopi, T_Binop(T_plus, loopi, T_Const(1)));
    T_stm do_body = T_Seq(unNx(body_while),  T_Jump(T_Name(while_test_label), Temp_LabelList(while_test_label, NULL)));
    T_stm body_stm = T_Seq(T_Label(while_body_label), T_Seq(add_one, do_body));

    T_stm forpart = T_Seq(T_Seq(cond_stm, body_stm), T_Label(done_label));
    T_stm tstm = T_Seq(init, T_Seq(if_stm, forpart));
    return Tr_Nx(tstm);
}

Tr_exp Tr_break(Temp_label done_label) {
    return Tr_Nx(T_Jump(T_Name(done_label), Temp_LabelList(done_label, NULL)));
}

F_fragList Tr_getResult(void) {
    return frag_head->tail;  // skip dummy head
}
