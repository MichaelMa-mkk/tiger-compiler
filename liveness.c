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
#include "flowgraph.h"
#include "liveness.h"
#include "table.h"


/*
 * use tempList as set
 */
static Temp_tempList Set_add(Temp_tempList set, Temp_temp node) {
    Temp_tempList old = set;

    while (set) {
        if (set->head == node) {
            return old;
        }
        set = set->tail;
    }
    return Temp_TempList(node, old);
}


static bool exist_node(Temp_tempList set, Temp_temp node)
{
    while (set) {
        if (set->head == node) {
            return TRUE;
        }
        set = set->tail;
    }

    return FALSE;
}
// for graph node
static bool hasNode(G_nodeList set, G_node node) {
    while (set) {
        if (set->head == node) {
            return TRUE;
        }
        set = set->tail;
    }

    return FALSE;
}

/*
 * liveness
 */
Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail) {
    Live_moveList lm = (Live_moveList) checked_malloc(sizeof(*lm));
    lm->src = src;
    lm->dst = dst;
    lm->tail = tail;
    return lm;
}

Temp_temp Live_gtemp(G_node n) {
    return G_nodeInfo(n);
}

void update_in_out(G_node flow_node, Temp_temp temp, G_table in_set, G_table out_set, G_table has_doit) {
    // update out set
    Temp_tempList out = (Temp_tempList) G_look(out_set, flow_node);
    if (!exist_node(out, temp)) {  // if not in out yet
        G_nodeList succ_node = G_succ(flow_node);
        while (succ_node) {  // check all successor's in
            Temp_tempList succ_live_in = G_look(in_set, succ_node->head);

            if (exist_node(succ_live_in, temp)) {
                G_enter(out_set, flow_node, out = Set_add(out, temp));  // update out

                break;
            }
            succ_node = succ_node->tail;
        }
    }

    Temp_temp use_reg = FG_use(flow_node);
    Temp_temp def_reg = FG_def(flow_node);
    bool in_use = exist_node(use_reg, temp);
    bool in_def = exist_node(def_reg, temp);
    bool in_out = exist_node(out, temp);
    bool in_changed = FALSE;
    if (in_use || (in_out && !in_def)) {

        Temp_tempList in = G_look(in_set, flow_node);
        if (!exist_node(in, temp)) {
            G_enter(in_set, flow_node, in = Set_add(in, temp));
            in_changed = TRUE;
        }
    }
    G_enter(has_doit, flow_node, TRUE);  // mark itself as has_doit

    if (!in_def || (in_def && in_use)) {
        G_nodeList pred_node = G_pred(flow_node);
        while (pred_node) {
            if (in_changed) {
                update_in_out(pred_node->head, temp, in_set, out_set, has_doit);
            }
            pred_node = pred_node->tail;
        }
    }
}



// flow is the flow control graph
struct Live_graph Live_liveness(G_graph flow) {
    G_nodeList instrs = G_nodes(flow);
    Temp_tempList all_regs = NULL;
    while (instrs) {
        AS_instr instr = G_nodeInfo(instrs->head);
        Temp_tempList srcs = instr->u.OPER.src;
        Temp_tempList dsts = instr->u.OPER.dst;
        //add all reg in to the graph
        while (srcs) {
            all_regs = Set_add(all_regs, srcs->head);
            srcs = srcs->tail;
        }
        while (dsts) {
            all_regs = Set_add(all_regs, dsts->head);
            dsts = dsts->tail;
        }
        instrs = instrs->tail;
    }

    //build empty conflict_node_map graph
    //add all src or dst to a new graph
    G_graph conflict_node_map = G_Graph();
    TAB_table temp_to_node = TAB_empty();
    while (all_regs) {
        Temp_temp newreg = all_regs->head;
        G_node node = G_Node(conflict_node_map, newreg);  // use temp as node info
        //find the node by reg

        TAB_enter(temp_to_node, newreg, node);
        all_regs = all_regs->tail;
    }

    // cal live-in, live-out
    G_table in_set = G_empty();
    G_table out_set = G_empty();
    //flow is contain the  instr and conflict_node_map is contain the reg
    G_nodeList temps = G_nodes(conflict_node_map);
    for (; temps; temps = temps->tail) {
        instrs = G_nodes(flow);
        Temp_temp temp = G_nodeInfo(temps->head);  // temp to trace
        G_table has_doit = G_empty();  // mark has_doit instrs

        for (; instrs; instrs = instrs->tail) {
            //find all use set which has such reg
            if (exist_node(FG_use(instrs->head), temp)) {
                update_in_out(instrs->head, temp, in_set, out_set, has_doit);  // backtrace till def of that temp
            }
        }
    }

    instrs = G_nodes(flow);
    for (; instrs; instrs = instrs->tail) {
        G_node instr_node = instrs->head;

        Temp_tempList defs = FG_def(instr_node);
        for (; defs; defs = defs->tail) {
            G_node def_node = TAB_look(temp_to_node, defs->head);
            Temp_tempList outs = G_look(out_set, instr_node);

            for (; outs; outs = outs->tail) {
                G_node out_node = TAB_look(temp_to_node, outs->head);

                if ((FG_isMove(instr_node)                      // if is a move instr,
                        && exist_node(FG_use(instr_node), outs->head))   // and this out is the move src
                        || hasNode(G_adj(def_node), out_node)  // don't link to some node more than once
                        || def_node == out_node ) {
                    continue;
                }

                G_addEdge(def_node, out_node);
            }
        }


    }

    // build move list
    Live_moveList moves = NULL;
    instrs = G_nodes(flow);
    while ( instrs ) {
        //if it is the move operation
        if (FG_isMove(instrs->head)) {
            AS_instr instr = G_nodeInfo(instrs->head);
            bool srcrsp = TRUE;
            bool dstrsp = TRUE;
            //if it is not the rsp
            char *src_norsprbp = Temp_look(Temp_layerMap(F_tempMap, Temp_name()), instr->u.MOVE.src->head);
            if (strncmp(src_norsprbp, "%rsp", 4) == 0
                    || strncmp(src_norsprbp, "%rbp", 4) == 0) {
                srcrsp =  FALSE;
            }

            char *dst_norsprbp = Temp_look(Temp_layerMap(F_tempMap, Temp_name()), instr->u.MOVE.dst->head);
            if (strncmp(dst_norsprbp, "%rsp", 4) == 0
                    || strncmp(dst_norsprbp, "%rbp", 4) == 0) {
                dstrsp =  FALSE;
            }

            // just ignore move that involving fp/sp, to avoid unwanted coalesce
            if (srcrsp && dstrsp) {
                G_node src = TAB_look(temp_to_node, instr->u.MOVE.src->head);
                G_node dst = TAB_look(temp_to_node, instr->u.MOVE.dst->head);

                moves = Live_MoveList(src, dst, moves);
            }
        }
        instrs = instrs->tail;
    }

    // show conflict_node_map result
    struct Live_graph lg = {.graph = conflict_node_map, .moves = moves};
    return lg;
}
