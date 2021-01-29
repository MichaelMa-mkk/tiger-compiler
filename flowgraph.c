#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "errormsg.h"
#include "table.h"

Temp_tempList FG_def(G_node n) {
    //get the dst src info of the such inst
    AS_instr instr = G_nodeInfo(n);
    Temp_tempList result = NULL;
    Temp_tempList list = instr->u.OPER.dst;
    while ( list) {
        if (list->head != F_FP() && list->head != F_SP()) {
            result = Temp_TempList(list->head, result);
        }
        list = list->tail;
    }

    return result;
}
//don't care about the fp and sp
Temp_tempList FG_use(G_node n) {
    AS_instr instr = G_nodeInfo(n);
    Temp_tempList result = NULL;
    Temp_tempList list = instr->u.OPER.src;
    while (list) {
        if (list->head != F_FP() && list->head != F_SP()) {
            result = Temp_TempList(list->head, result);
        }
        list = list->tail;
    }

    return result;
}

bool FG_isMove(G_node n) {
    AS_instr instr = G_nodeInfo(n);
    return instr->kind == I_MOVE;
}

G_graph FG_AssemFlowGraph(AS_instrList instrlist, F_frame frame) {
    G_graph graph = G_Graph();
    TAB_table label_jump_destination_tab = TAB_empty();

    Temp_labelList jump_label = NULL;
    G_node last_node = NULL;

    while (instrlist) {
        AS_instr instr = instrlist->head;
        if (instr->kind == I_LABEL) {
            jump_label = Temp_LabelList(instr->u.LABEL.label, jump_label);
            instrlist = instrlist->tail;
            continue;
        }
        //add the instr to the graph
        G_node now_node = G_Node(graph, instr);

        // add label mapping
        while (jump_label) {
            TAB_enter(label_jump_destination_tab, jump_label->head, now_node);
            jump_label = jump_label->tail;

        }
        jump_label = NULL;
        // add edge for fall-through
        if (instr->kind == I_OPER && strncmp(instr->u.OPER.assem, "jmp", 3) == 0) {
            if (last_node != NULL) {
                G_addEdge(last_node, now_node);
            }
            last_node = NULL;
        }
        else {
            if (last_node != NULL) {
                G_addEdge(last_node, now_node);
            }
            last_node = now_node;
        }
        instrlist = instrlist->tail;
    }

    // read all now_node in the grafp
    G_nodeList all_nodes = G_nodes(graph);
    while (all_nodes)
    {
        G_node now_node = all_nodes->head;
        AS_instr instr = G_nodeInfo(now_node);
        Temp_labelList jump_destination = NULL;

        if ( (instr->u.OPER.jumps != NULL) && (instr->kind == I_OPER)) {
            jump_destination = instr->u.OPER.jumps->labels;
        }
        else {
            all_nodes = all_nodes->tail;
            continue;
        }
        //add the jump destination to jump node in the graph
        while (jump_destination) {
            G_node target_node = TAB_look(label_jump_destination_tab, jump_destination->head);
            if (target_node != NULL) {
                G_addEdge(now_node, target_node);
            }

            jump_destination = jump_destination->tail;
        }
        //goto the next node
        all_nodes = all_nodes->tail;
    }

    return graph;
}
