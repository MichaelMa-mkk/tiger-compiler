
/*Lab5: This header file is not complete. Please finish it with more definition.*/

#ifndef FRAME_H
#define FRAME_H

#include "tree.h"

extern const int F_wordSize;
Temp_map F_tempMap;

typedef struct F_frame_ *F_frame;

typedef struct F_access_ *F_access;
typedef struct F_accessList_ *F_accessList;

struct F_accessList_ {F_access head; F_accessList tail;};

struct F_access_ {
    enum {inFrame, inReg} kind;
    union {
        int offset; //inFrame
        Temp_temp reg; //inReg
    } u;
    T_exp init;
};

struct F_frame_ {
    Temp_label name;
    F_accessList formals;
    F_accessList locals;
    int frame_off;
    int in_frame_local_num;
};

/* declaration for fragments */
typedef struct F_frag_ *F_frag;
struct F_frag_ {enum {F_stringFrag, F_procFrag} kind;
			union {
				struct {Temp_label label; string str;} stringg;
				struct {T_stm body; F_frame frame;} proc;
			} u;
};

F_frag F_StringFrag(Temp_label label, string str);
F_frag F_ProcFrag(T_stm body, F_frame frame);

typedef struct F_fragList_ *F_fragList;
struct F_fragList_ 
{
	F_frag head; 
	F_fragList tail;
};

F_fragList F_FragList(F_frag head, F_fragList tail);
F_frag F_StringFrag(Temp_label label, string str);
F_frag F_ProcFrag(T_stm body, F_frame frame);

Temp_label F_name(F_frame frame);
F_frame F_newFrame(Temp_label name, U_boolList formals);
F_access F_allocLocal(F_frame frame, bool escape, T_exp init);
F_accessList F_formals(F_frame frame);
F_accessList F_AccessList(F_access head, F_accessList tail);

T_exp F_Exp(F_access acc, T_exp frame_ptr);
T_exp F_externalCall(string s, T_expList args);

Temp_temp F_FP();
Temp_temp F_SP();
Temp_temp F_RV();
Temp_temp F_RAX();
Temp_temp F_RDX();
Temp_temp F_RBX();
Temp_temp F_RSI();
Temp_temp F_RDI();
Temp_temp F_R12();
Temp_temp F_R13();
Temp_temp F_R14();
Temp_temp F_R15();
Temp_temp F_RCX();
Temp_temp F_R8();
Temp_temp F_R9();
Temp_temp F_R10();
Temp_temp F_R11();
T_stm F_procEntryExit1(F_frame frame, T_stm stm);

#endif
