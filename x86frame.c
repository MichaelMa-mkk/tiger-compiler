#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "tree.h"
#include "frame.h"

/*Lab5: Your implementation here.*/
static int WORDSIZE = 8;

//varibales

F_frag F_StringFrag(Temp_label label, string str) {
    int len = strlen(str);
    char *new_str = checked_malloc(len + 5);
    *(int *) new_str = len;
    strncpy(new_str + 4, str, len);

    F_frag frag = malloc(sizeof(*frag));
    frag->kind = F_stringFrag;
    frag->u.stringg.label = label;
    frag->u.stringg.str = new_str;
    return frag;
}

F_frag F_ProcFrag(T_stm body, F_frame frame) {
    F_frag frag = malloc(sizeof(*frag));
    frag->kind = F_procFrag;
    frag->u.proc.body = body;
    frag->u.proc.frame = frame;
    return frag;
}

F_fragList F_FragList(F_frag head, F_fragList tail) {
    F_fragList list = malloc(sizeof(*list));
    list->head = head;
    list->tail = tail;
    return list;
}

F_accessList F_AccessList(F_access head, F_accessList tail) {
    F_accessList list = malloc(sizeof(*list));
    list->head = head;
    list->tail = tail;
    return list;
}

static F_access InFrame(int offset) {
    F_access access = malloc(sizeof(struct F_access_));
    access->kind = inFrame;
    access->u.offset = offset;
    return access;
}

static F_access InReg(Temp_temp reg) {
    F_access access = malloc(sizeof(struct F_access_));
    access->kind = inReg;
    access->u.reg = reg;
    return access;
}

F_frame F_newFrame(Temp_label name, U_boolList formals) {
    F_frame frame = malloc(sizeof(*frame));

    frame->name = name;
    frame->locals = NULL;
    frame->frame_off = 0;

    // create access of formal parameters
    F_accessList head = malloc(sizeof(struct F_accessList_));
    F_accessList tail = head;
    int formal_off = 16;  // first argument stays at 8(%rsp) static link
    int k = 0;
    for (; formals; k++, formals = formals->tail) {
        if (k > 0 && k <= 6) {
            F_access access = InReg(Temp_newtemp());

            tail->tail = F_AccessList(access, NULL);
            tail = tail->tail;
        }
        else {
            F_access access = InFrame(formal_off);
            formal_off += WORDSIZE;

            tail->tail = F_AccessList(access, NULL);
            tail = tail->tail;
        }
    }
    frame->formals = head->tail;  // skip dummy head

    return frame;
}

F_access F_allocLocal(F_frame frame, bool escape, T_exp init) {
    F_access access;
    if (escape != TRUE) {
        access = InReg(Temp_newtemp());
    } else {
        frame->frame_off -= WORDSIZE;
        frame->in_frame_local_num ++;
        access = InFrame(frame->frame_off);
    }

    access->init = init;
    frame->locals = F_AccessList(access, frame->locals);

    return access;
}

Temp_label F_name(F_frame frame) {
    return frame->name;
}

F_accessList F_formals(F_frame frame) {
    return frame->formals;
}

Temp_temp F_FP() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%rbp"));
    }
    return reg;
}

Temp_temp F_SP() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%rsp"));
    }
    return reg;
}

Temp_temp F_RV() {
    return F_RAX();
}

Temp_temp F_RAX() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%rax"));
    }
    return reg;
}

Temp_temp F_RDX() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%rdx"));
    }
    return reg;
}

Temp_temp F_RBX() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%rbx"));
    }
    return reg;
}

Temp_temp F_RSI() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%rsi"));
    }
    return reg;
}

Temp_temp F_RDI() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%rdi"));
    }
    return reg;
}

Temp_temp F_R12() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%r12"));
    }
    return reg;
}

Temp_temp F_R13() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%r13"));
    }
    return reg;
}

Temp_temp F_R14() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%r14"));
    }
    return reg;
}

Temp_temp F_R15() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%r15"));
    }
    return reg;
}

Temp_temp F_RCX() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%rcx"));
    }
    return reg;
}

Temp_temp F_R8() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%r8"));
    }
    return reg;
}

Temp_temp F_R9() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%r9"));
    }
    return reg;
}

Temp_temp F_R10() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%r10"));
    }
    return reg;
}

Temp_temp F_R11() {
    static Temp_temp reg = NULL;
    if (reg == NULL) {
        reg = Temp_newtemp();
        Temp_enter(F_tempMap, reg, String("%r11"));
    }
    return reg;
}

T_exp F_Exp(F_access acc, T_exp frame_ptr) {
    switch (acc->kind) {
    case inFrame:
        return T_Mem(T_Binop(T_plus, frame_ptr, T_Const(acc->u.offset)));
    case inReg:
        return T_Temp(acc->u.reg);
    default:
        assert(0);
    }
}

T_exp F_externalCall(string s, T_expList args) {
    return T_Call(T_Name(Temp_namedlabel(s)), args);
}

T_stm F_procEntryExit1(F_frame frame, T_stm stm) {
    return stm;
}
