#include <stdio.h>
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "liveness.h"
#include "color.h"
#include "regalloc.h"
#include "table.h"
#include "flowgraph.h"


static bool hasTemp(Temp_tempList list, Temp_temp temp) {
    for (; list; list = list->tail)
        if (list->head == temp)
            return 1;
    return 0;
}

static void replaceTemp(Temp_tempList list, Temp_temp old, Temp_temp new_) {
    for (; list; list = list->tail)
        if (list->head == old)
            list->head = new_;
}


AS_instrList rewriteProgram(F_frame frame, AS_instrList il, Temp_tempList spills) {
    AS_instrList result = il;
    // initial spills var num
    Temp_tempList spills_temp = spills;
    for (; spills_temp; spills_temp = spills_temp->tail) {
        frame->in_frame_local_num += 1;
    }
    for (; spills; spills = spills->tail) {
        Temp_temp spill = spills->head;
        // frame->in_frame_local_num += 1;
        frame->frame_off -= 8;
        int new_frame_off = frame->frame_off;

        AS_instrList instrs = result;
        for (; instrs; instrs = instrs->tail) {
            AS_instr instr = instrs->head;

            if (instr->kind == I_OPER) {
                int flag = 1;
                Temp_temp temp;
                if (hasTemp(instr->u.OPER.dst, spill)) {
                    flag = 0;
                    temp = Temp_newtemp();
                    replaceTemp(instr->u.OPER.dst, spill, temp);

                    // create a store
                    char inst[100];
                    sprintf(inst, "movq `s0, %d(%%rsp)", new_frame_off + frame->in_frame_local_num * 8);
                    AS_instr store = AS_Oper(String(inst), NULL, Temp_TempList(temp, NULL), NULL);

                    instrs->tail = AS_InstrList(store, instrs->tail);
                } if (hasTemp(instr->u.OPER.src, spill)) {
                    if (flag) temp = Temp_newtemp();
                    replaceTemp(instr->u.OPER.src, spill, temp);

                    // create a fetch
                    char inst[100];
                    sprintf(inst, "movq %d(%%rsp), `d0", new_frame_off + frame->in_frame_local_num * 8);
                    AS_instr fetch = AS_Oper(String(inst), Temp_TempList(temp, NULL), NULL, NULL);

                    instrs->head = fetch;
                    instrs->tail = AS_InstrList(instr, instrs->tail);
                }
            } else if (instr->kind == I_MOVE) {
                if (hasTemp(instr->u.MOVE.dst, spill)) {
                    char inst[100];
                    sprintf(inst, "movq `s0, %d(%%rsp)", new_frame_off + frame->in_frame_local_num * 8);
                    AS_instr store = AS_Oper(String(inst), NULL, instr->u.MOVE.src, NULL);

                    instrs->head = store;
                } if (hasTemp(instr->u.MOVE.src, spill)) {
                    char inst[100];
                    sprintf(inst, "movq %d(%%rsp), `d0", new_frame_off + frame->in_frame_local_num * 8);
                    AS_instr fetch = AS_Oper(String(inst), instr->u.MOVE.dst, NULL, NULL);

                    instrs->head = fetch;
                }
            }
        }
    }

    return result;
}


void showinfo(void *temp) {
    printf("temp %s, \n", Temp_look(Temp_name(), (Temp_temp) temp));
}


struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
    G_graph flow_graph = FG_AssemFlowGraph(il, f);
    struct Live_graph live_graph = Live_liveness(flow_graph);

    // G_show(stdout, G_nodes(live_graph.graph), showinfo);
    struct COL_result color = COL_color(live_graph.graph, F_tempMap, NULL, live_graph.moves);;

    if (color.spills != NULL) {
        Temp_map some_map = Temp_layerMap(F_tempMap, Temp_layerMap(color.coloring, Temp_name()));

        printf("=======================before rewrite====================\n");
        AS_printInstrList(stdout, il, some_map);
        printf("=======================spills===========================\n");
        Temp_tempList list = color.spills;
        for (; list; list = list->tail) {
            printf("%s,", Temp_look(some_map, list->head));
        } printf("\n");
        AS_instrList new_il = rewriteProgram(f, il, color.spills);
        printf("=======================after rewrite====================\n");
        AS_printInstrList(stdout, new_il, some_map);
        return RA_regAlloc(f, new_il);
    }

    // eliminate T_MOVE dst==src
    Temp_map final_result = Temp_layerMap(F_tempMap, Temp_layerMap(color.coloring, Temp_name()));
    AS_instrList *p = &il;
    while (*p) {
        AS_instr instr = (*p)->head;
        if (instr->kind == I_MOVE) {
            char *src = Temp_look(final_result, instr->u.MOVE.src->head);
            char *dst = Temp_look(final_result, instr->u.MOVE.dst->head);

            if (strncmp(src, dst, 4) == 0) {
                *p = (*p)->tail;
                continue;
            }
        }

        p = &((*p)->tail);
    }

    // eliminate useless jmp
    p = &il;
    while (*p) {
        AS_instr instr = (*p)->head;
        if (instr->kind == I_OPER && strncmp(instr->u.OPER.assem, "jmp", 3) == 0) {
            AS_instr next = (*p)->tail->head;
            if (next->kind == I_LABEL && next->u.LABEL.label == instr->u.OPER.jumps->labels->head) {
                *p = (*p)->tail;
                continue;
            }
        }

        p = &((*p)->tail);
    }

    // after assignment, add prologues
    AS_instrList prologue = NULL;
    // AS_instrList prologue =
    //     AS_InstrList(AS_Oper(String("pushq %%rbp"), NULL, NULL, NULL), AS_InstrList(
    //                      AS_Move(String("movq %rsp, %rbp"), NULL, NULL), NULL));

    if (f->in_frame_local_num) {
        char inst[100];
        sprintf(inst, "subq $%d, %rsp", f->in_frame_local_num * 8);
        // prologue = AS_splice(prologue,
        //                      AS_InstrList(AS_Oper(String(inst), NULL, NULL, NULL), NULL));
        prologue = AS_InstrList(AS_Oper(String(inst), NULL, NULL, NULL), NULL);
    }

    p = &il;
    while (*p) {
        AS_instr instr = (*p)->head;
        if ((*p)->tail == NULL) break;
        AS_instr next = (*p)->tail->head;
        if (next->kind == I_OPER || next->kind == I_MOVE) {
            if (hasTemp(next->u.OPER.dst, F_FP()) || hasTemp(next->u.OPER.src, F_FP())) {
                replaceTemp(next->u.OPER.dst, F_FP(), F_SP());
                replaceTemp(next->u.OPER.src, F_FP(), F_SP());
                if (f->in_frame_local_num) {
                    char inst1[100];
                    sprintf(inst1, "addq $%d, %rsp", f->in_frame_local_num * 8);
                    char inst2[100];
                    sprintf(inst2, "subq $%d, %rsp", f->in_frame_local_num * 8);
                    AS_instrList cal1 = AS_InstrList(AS_Oper(String(inst1), NULL, NULL, NULL), NULL);
                    AS_instrList cal2 = AS_InstrList(AS_Oper(String(inst2), NULL, NULL, NULL), NULL);

                    cal1->tail = (*p)->tail;
                    cal2->tail = (*p)->tail->tail;
                    (*p)->tail = cal1;
                    cal1->tail->tail = cal2;

                    p = &(cal2->tail);
                    continue;
                }
            }
        }
        p = &((*p)->tail);
    }
    // AS_instr leaveq = AS_Oper(String("leaveq"), NULL, NULL, NULL);
    AS_instrList epilogue = NULL;
    if (f->in_frame_local_num) {
        char inst[100];
        sprintf(inst, "addq $%d, %rsp", f->in_frame_local_num * 8);
        epilogue = AS_InstrList(AS_Oper(String(inst), NULL, NULL, NULL),
                                         AS_InstrList(AS_Oper("retq", NULL, NULL, NULL), NULL));
    }
    else {
        epilogue = AS_InstrList(AS_Oper("retq", NULL, NULL, NULL), NULL);
    }

    struct RA_result ret = {.coloring = color.coloring, .il = AS_splice(prologue, AS_splice(il, epilogue))};
    return ret;
}
