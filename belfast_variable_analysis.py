from belfast_data import *
from belfast_triples import *
from typing import *

def color_interf_graph_simplicial(interf_graph: Dict[Any, List[Any]], coalesce_edges: Dict[Any, List[Any]], precolored_nodes: Dict[Any, int], k: int) -> Dict[Any, int]:
    graph_color = {}

    for p,v in precolored_nodes.items():
        graph_color[p] = v

    for i,reg in graph_color.items():
        interf = interf_graph[i]
        for a,reg2 in graph_color.items():
            if reg2 == reg and a in interf:
                print(f"Interfering values {i} and {a} assigned to register {reg}")
                sys.exit(1)

    remaining_values = {k:0 for k in set(interf_graph.keys()).difference(graph_color.keys())}
    ordering = []

    for i in range(len(remaining_values)):
        max_weight_nodes = [k for k,v in remaining_values.items() if v == max(remaining_values.values())]
        v = max_weight_nodes[0]
        for i in interf_graph[v]:
            if i in remaining_values:
                remaining_values[i] += 1
        del remaining_values[v]
        ordering.append(v)

    for v in set(interf_graph.keys()).difference(graph_color.keys()):
        neighbor_colors = [graph_color[e] for e in interf_graph[v] if e in graph_color]
        ind = 0
        while ind in neighbor_colors:
            ind += 1
        if ind > k:
            print(set(interf_graph.keys()).difference(graph_color.keys()))
            return None
        graph_color[v] = ind
    
    return graph_color

def color_interf_graph_chaitin_briggs(interf_graph: Dict[Any, List[Any]], coalesce_edges: Dict[Any, List[Any]], precolored_nodes: Dict[Any, int], k: int, force_no_spill=()) -> Dict[Any, int]:
    graph_color = {}

    for p,v in precolored_nodes.items():
        if p in interf_graph:
            graph_color[p] = v

    for i,reg in graph_color.items():
        interf = interf_graph[i]
        for a,reg2 in graph_color.items():
            if reg2 == reg and a in interf:
                print(f"Interfering values {i} and {a} assigned to register {reg}")
                sys.exit(1)

    G = {k:list(l) for k,l in interf_graph.items()}
    ordering = []
    potential_spill = set()

    for v in force_no_spill:
        for e in G[v]:
            if e in G:
                G[e].remove(v)
        del G[v]

    while len(G) > 0:
        val_weights = {v: len(e) for v,e in G.items()}
        valid_vertices = sorted([v for v in G if val_weights[v] < k], key=lambda x: val_weights[x], reverse=True)
        if len(valid_vertices) > 0:
            v = valid_vertices[0]
        else:
            v = list(G.keys())[0]
            potential_spill.add(v)
        ordering.append(v)
        for e in G[v]:
            if e in G:
                G[e].remove(v)
        del G[v]

    ordering.extend(force_no_spill)

    spilled_nodes = []

    while len(ordering) > 0:
        v = ordering.pop()
        if v in graph_color:
            continue
        neighbor_colors = [graph_color[e] for e in interf_graph[v] if e in graph_color]
        ind = 0
        while ind in neighbor_colors:
            ind += 1
        if ind >= k:
            graph_color[v] = None
            spilled_nodes.append(v)
        graph_color[v] = ind

    return graph_color, spilled_nodes

def color_interf_graph_rlf(interf_graph: Dict[Any, List[Any]], coalesce_edges: Dict[Any, List[Any]], precolored_nodes: Dict[Any, int], k: int) -> Dict[Any, int]:
    graph_color = {}

    M = dict(interf_graph)
    for p,v in precolored_nodes.items():
        graph_color[p] = v

    for i in list(graph_color.keys()):
        if i in coalesce_edges:
            for e in coalesce_edges[i]:
                if e not in graph_color:
                    existing_interfs = [reg for v,reg in graph_color.items() if v in interf_graph[e]]
                    if graph_color[i] not in existing_interfs:
                        graph_color[e] = graph_color[i]
    
    for i,reg in graph_color.items():
        interf = interf_graph[i]
        for a,reg2 in graph_color.items():
            if reg2 == reg and a in interf:
                print(f"Interfering values {i} and {a} assigned to register {reg}")
                sys.exit(1)

    for i,v in interf_graph.items():
        if len(v) >= k:
            print(f"{i} is a potential spill candidate ({len(v)})")
    
    ind = 0

    def get_all_edges(x):
        if x in coalesce_edges:
            e = set(M[x])
            for c in coalesce_edges[x]:
                e.update([i for i in interf_graph[c] if i in M])
            return e
        else:
            return M[x]

    def node_in_set(x, S: Set):
        # return x in S
        return x in S or (x in coalesce_edges and any([c in S for c in coalesce_edges[x]]))

    while len(M) > 0:
        S = set()
        for i,reg in graph_color.items():
            if reg == ind:
                S.add(i)

        while True:
            # select all nodes that have no neighbors in S
            valid_nodes = [x for x in M if x not in graph_color and not node_in_set(x, S) and all([e not in S for e in get_all_edges(x)])]
            # print(valid/s_nodes)
            if len(valid_nodes) == 0:
                break
            score_node = lambda x: len([i for i in get_all_edges(x) if i in S])
            node_scores = [(x, score_node(x)) for x in valid_nodes]
            max_score = max([x[1] for x in node_scores])
            best_nodes = sorted([n for n,s in node_scores if s == max_score], key = lambda x: (len(get_all_edges(x)),))
            selected_node = best_nodes[-1]
            if selected_node in coalesce_edges:
                S.update([e for e in coalesce_edges[selected_node] if e in M])
            S.add(selected_node)

        for n in S:
            del M[n]
            graph_color[n] = ind
        ind += 1
        if ind >= k:
            return None


    return graph_color

def evaluate_liveness(blocks: List[TripleBlock]):
    trip_liveness = {}
    use_count = {}

    for b in blocks:
        live_vals = set(b.out_vals)
        for t in reversed(b.trips):
            next_live_vals = set(live_vals)
            for d in get_defines(t):
                if d in next_live_vals:
                    next_live_vals.remove(d)
            for v in get_uses(t):
                if v not in use_count:
                    use_count[v] = 0
                use_count[v] += 1
                next_live_vals.add(v)
            trip_liveness[t] = next_live_vals
            live_vals = next_live_vals

    val_liveness = {}

    for t,v_l in trip_liveness.items():
        for v in v_l:
            if v not in val_liveness:
                val_liveness[v] = set()
            val_liveness[v].add(t.index)

    # print('\n'.join(map(lambda x: f"{print_triple(x[0])}: {x[1]}", sorted(trip_liveness.items(), key=lambda x: x[0].index))))
    # print('\n')

    # print('\n'.join(map(str, val_liveness.items())))

    # print()
    # print('\n'.join(map(str, sorted(use_count.items(), key=lambda x: x[1], reverse=True))))

    return val_liveness, use_count

def create_interference_graph(trips: List[Triple], val_liveness: Dict[TripleValue, Set[int]]) -> Dict[TripleValue, List[TripleValue]]:
    interf_graph: Dict[Any, Set[Any]] = {}
    # for v, live_nums in val_liveness.items():
    #     interf_graph[v] = set()
    #     for v2,ln2 in val_liveness.items():
    #         if v2 == v:
    #             continue
    #         inter = len(live_nums.intersection(ln2))
    #         if inter > 0:
    #             interf_graph[v].add(v2)

    for t in trips:
        d_l = get_defines(t)
        live_after = [v for v,l in val_liveness.items() if (t.index + 1) in l]
        pass
        for d in d_l:
            if d not in interf_graph:
                interf_graph[d] = set()
            for v in live_after:
                if v in d_l:
                    continue
                if v not in interf_graph:
                    interf_graph[v] = set()
                interf_graph[d].add(v)
                interf_graph[v].add(d)

    return interf_graph

def does_value_need_color(tv: TripleValue):
    return tv.typ in [TripleValueType.REGISTER, TripleValueType.VAR_REF, TripleValueType.TRIPLE_REF, TripleValueType.ADDRESS_COMPUTE]

def get_defines(triple: Triple):
    match triple.typ:
        case TripleType.ASSIGN:
            return (create_var_ref_value(triple.l_val.value),)
        case TripleType.REGMOVE:
            return (triple.l_val,)
        case TripleType.BINARY_OP | TripleType.UNARY_OP | TripleType.NOP_REF | TripleType.LOAD:
            if (triple.flags & TF_BOOL_FORWARDED) > 0:
                # Bool forwarded values are not stored
                return ()
            return (create_tref_value(triple),)
        case TripleType.CALL | TripleType.SYSCALL:
            return [create_tref_value(triple),] + [create_register_value(i) for i in CALLER_SAVED_REG]
        case TripleType.ARG:
            return (create_register_value(SYSCALL_ARG_REGISTERS[triple.data] if triple.flags & TF_SYSCALL else ARG_REGISTERS[triple.data]),)
    return ()

def get_uses(triple: Triple, colored_only=True):
    vals = []
    match triple.typ:
        case TripleType.ASSIGN | TripleType.REGMOVE:
            if not colored_only or does_value_need_color(triple.r_val):
                vals = [triple.r_val,]
        case TripleType.BINARY_OP | TripleType.STORE:
            vals = []
            if not colored_only or does_value_need_color(triple.r_val):
                vals.append(triple.r_val)
            if not colored_only or does_value_need_color(triple.l_val):
                vals.append(triple.l_val)
            if triple.typ == TripleType.BINARY_OP and triple.op in [Operator.DIVIDE, Operator.MODULUS, Operator.MULTIPLY]:
                vals.append(create_register_value(RDX_INDEX))
        case TripleType.UNARY_OP | TripleType.IF_COND | TripleType.NOP_USE | TripleType.NOP_REF | TripleType.LOAD | TripleType.ARG | TripleType.RETURN:
            if triple.typ == TripleType.IF_COND and triple.l_val.typ == TripleValueType.TRIPLE_REF and (triple.l_val.value.flags & TF_BOOL_FORWARDED) > 0:
                return ()
            if not colored_only or does_value_need_color(triple.l_val):
                vals = [triple.l_val,]
        case TripleType.SYSCALL | TripleType.CALL:
            vals = [create_register_value(v) for v in ARG_REGISTERS[:triple.data]]
        case TripleType.RETURN:
            vals = [create_register_value(v) for v in CALLEE_SAVED_REG]
    new_vals = []
    for v in vals:
        if v.typ == TripleValueType.ADDRESS_COMPUTE:
            if does_value_need_color(v.value[0]):
                new_vals.append(v.value[0])
            if does_value_need_color(v.value[1]):
                new_vals.append(v.value[1])
        else:
            new_vals.append(v)
    if len(new_vals) > 0:
        return tuple(new_vals)
    return ()

def identify_loops(opt_ctx) -> bool:
    did_change = False
    block_visit = {}
    dom_map = {}
    blocks = opt_ctx.blocks
    if len(blocks) == 0:
        return False
    trips = opt_ctx.trips
    open_block_set = [blocks[0]]
    while len(open_block_set) > 0:
        b = open_block_set.pop(0)
        block_visit[b] = set([b])
        for i in b.in_blocks:
            if i in block_visit:
                block_visit[b].update(block_visit[i])
        temp = None
        if len(b.in_blocks) > 0:
            for in_b in b.in_blocks:
                if in_b not in block_visit:
                    continue
                if temp is None:
                    temp = block_visit[in_b]
                else:
                    temp = temp.intersection(block_visit[in_b])
            max_block = sorted(list(temp), key= lambda x: x.index)[-1]
            dom_map[b] = max_block
        else:
            dom_map[b] = None
        for o_b in b.out_blocks:
            if o_b not in open_block_set and o_b not in dom_map:
                open_block_set.append(o_b)

    def is_dominated_by(b, dom):
        if b == dom:
            return True
        b1 = dom_map[b]
        while b1 is not None:
            if b1 == dom:
                return True
            b1 = dom_map[b1]
        return False

    loops: Dict[TripleBlock, TripleBlock] = {}

    for b in blocks:
        dom_edges = [e for e in b.out_blocks if is_dominated_by(b, e)]
        if len(dom_edges) > 0:
            assert len(dom_edges) == 1
            if dom_edges[0] not in loops or b.index > loops[dom_edges[0]].index:
                loops[dom_edges[0]] = b
    
    opt_ctx.loops = loops
    opt_ctx.block_dominance_map = dom_map
    opt_ctx.block_visit_in = block_visit

    for b1,b2 in loops.items():
        overlapping_loops = [(b3,b4) for b3,b4 in loops.items() if b3.index < b1.index and b4.index >= b2.index]
        opt_ctx.loop_prio[b1] = len(overlapping_loops)
    
def optimize_loop(header: TripleBlock, end: TripleBlock, opt_ctx):
    blocks_in = [b for b in opt_ctx.blocks if header.index <= b.index <= end.index]
    
    loop_defines = {}
    loop_uses = {}
    for b in blocks_in:
        for t in b.trips:
            defs = get_defines(t)
            for d in defs:
                if d not in loop_defines:
                    loop_defines[d] = []
                loop_defines[d].append(t)
            uses = get_uses(t)
            for u in uses:
                if u not in loop_uses:
                    loop_uses[u] = []
                loop_uses[u].append(t)
    
    loop_invariants = set()
    while True:
        len_invariants = len(loop_invariants)
        for b in blocks_in:
            for t in b.trips:
                uses = get_uses(t, colored_only=False)
                for u in uses:
                    if u.typ == TripleValueType.CONSTANT:
                        loop_invariants.add(u)
                    elif u.typ == TripleValueType.TRIPLE_REF:
                        if u.value.typ in [TripleType.LOAD,]:
                            continue
                        sub_uses = get_uses(u.value, colored_only=False)
                        if all([use in loop_invariants for use in sub_uses]):
                            loop_invariants.add(u)
                    elif u.typ == TripleValueType.VAR_REF and u not in loop_defines:
                        loop_invariants.add(u)
                
        if len(loop_invariants) == len_invariants:
            break

    invariant_pre_header = [v.value for v in loop_invariants if v.typ == TripleValueType.TRIPLE_REF and any([v.value in b.trips for b in blocks_in])]

    basic_induction_vars = {}

    for d,t_l in loop_defines.items():
        if len(t_l) == 1:
            if d.typ == TripleValueType.VAR_REF:
                assigned = t_l[0].r_val
                if assigned.typ == TripleValueType.TRIPLE_REF:
                    t = assigned.value
                    if t.typ == TripleType.BINARY_OP and t.op in [Operator.PLUS, Operator.MINUS]:
                        const_vals = [v for v in (t.l_val, t.r_val) if v in loop_invariants]
                        var_vals = [v for v in (t.l_val, t.r_val) if triple_values_equal(v, d)]
                        if len(const_vals) == 1 and len(var_vals) == 1:
                            basic_induction_vars[d] = const_vals[0]

    remove_basic_induction = []

    for b in list(basic_induction_vars.keys()):
        if b in loop_uses and len(loop_uses[b]) == 1 and b in header.in_vals:
            # Useless induction var within the loop, check outside the loop
            is_useless = True
            for bl in blocks_in:
                for out_bl in bl.out_blocks:
                    if out_bl not in blocks_in and b in out_bl.in_vals:
                        is_useless = False
                        break
            if is_useless:
                remove_basic_induction.append(loop_uses[b][0])
                del basic_induction_vars[b]

    linear_combinations = {b:LinearCombination(b) for b in basic_induction_vars}

    while True:
        old_len = len(linear_combinations)
        for k,v in list(linear_combinations.items()):
            if k in loop_uses:
                for t in loop_uses[k]:
                    if t.typ == TripleType.BINARY_OP:
                        is_lval = False
                        is_rval = False
                        other_val = None
                        if t.l_val == k:
                            is_lval = True
                            other_val = t.r_val
                        elif t.r_val == k:
                            is_rval = True
                            other_val = t.l_val
                        if other_val not in loop_invariants:
                            continue
                        if is_lval or is_rval:
                            new_l = None
                            match t.op:
                                case Operator.PLUS:
                                    new_l = v.add_operation(t.op, other_val)
                                case Operator.MINUS:
                                    if is_lval:
                                        new_l = v.add_operation(t.op, other_val)
                                    else:
                                        new_l = v.do_negate().add_operation(Operator.PLUS, other_val)
                                case Operator.SHIFT_LEFT:
                                    if other_val.typ == TripleValueType.CONSTANT:
                                        new_l = v.add_coefficient(create_const_value(2 ** other_val.value))
                                    else:
                                        # TODO: Can we handle this?
                                        pass
                                case Operator.MULTIPLY:
                                    new_l = v.add_coefficient(other_val)
                            if new_l:
                                linear_combinations[create_tref_value(t)] = new_l
        if len(linear_combinations) == old_len:
            break

    derived_induction_vars : Dict[TripleValue, LinearCombination] = {}

    for tv,lin in linear_combinations.items():
        if tv in basic_induction_vars:
            continue
        if lin.coefficient_val is None and not lin.negate and len(lin.operations) == 1 and lin.operations[0][1].typ == TripleValueType.CONSTANT:
            # x + c
            # This doesnt help us
            continue
        if len(loop_defines[tv]) > 1:
            continue
        if tv in loop_uses and all([create_tref_value(u) in linear_combinations for u in loop_uses[tv]]):
            continue
        derived_induction_vars[tv] = lin

    induction_pre_header = []

    for tv,lin in derived_induction_vars.items():
        linear_var_define = loop_defines[lin.linear_var][0]
        tv_define = loop_defines[tv][0]
        match tv.typ:
            case TripleValueType.TRIPLE_REF:
                inductive_var = f"$({tv.value.uid})_ind"
                ref_t = Triple(TripleType.NOP_REF, None, create_var_ref_value(inductive_var), None, uid=triple_uid())
                opt_ctx.retarget_triple_references(tv_define, create_tref_value(ref_t), "Retarget to Derived Induction Variable")
                opt_ctx.replace_triple(tv_define, ref_t, "Derived Induction Variable")
            case TripleValueType.VAR_REF:
                inductive_var = f"$({tv.value})_ind"
                tv_define.r_val = create_var_ref_value(inductive_var)
                CHANGE_HINTS[tv_define] = "Derived Induction Variable"
            case _:
                assert False

        ind_linvar = opt_ctx.trips.index(linear_var_define) + 1
        inductive_triple = Triple(TripleType.BINARY_OP, Operator.MINUS if lin.negate else Operator.PLUS, create_var_ref_value(inductive_var), lin.coefficient_val if lin.coefficient_val else create_const_value(1), uid=triple_uid())
        opt_ctx.insert_triple(ind_linvar, inductive_triple, "Inductive Step")
        ind_linvar += 1
        opt_ctx.insert_triple(ind_linvar, Triple(TripleType.ASSIGN, None, create_var_assign_value(inductive_var), create_tref_value(inductive_triple), uid=triple_uid()), "Inductive Step")

        val = lin.linear_var
        if lin.coefficient_val is not None:
            new_trip = Triple(TripleType.BINARY_OP, Operator.MULTIPLY, val, lin.coefficient_val, uid=triple_uid())
            val = create_tref_value(new_trip)
            induction_pre_header.append(new_trip)
        first_neg = lin.negate
        if lin.negate and (len(lin.operations) == 0 or not lin.operations[0][0]):
            new_trip = Triple(TripleType.UNARY_OP, Operator.NEGATE, val, None, uid=triple_uid())
            val = create_tref_value(new_trip)
            induction_pre_header.append(new_trip)
            first_neg = False
        for is_plus,op_val in lin.operations:
            if first_neg:
                new_trip = Triple(TripleType.BINARY_OP, Operator.MINUS, op_val, val, uid=triple_uid())
                first_neg = False
            else:
                new_trip = Triple(TripleType.BINARY_OP, Operator.PLUS if is_plus else Operator.MINUS, val, op_val, uid=triple_uid())
            val = create_tref_value(new_trip)
            induction_pre_header.append(new_trip)

        induction_pre_header.append(Triple(TripleType.ASSIGN, None, create_var_assign_value(inductive_var), val, uid=triple_uid()))
    
    preheader_index = opt_ctx.trips.index(header.trips[0])

    if len(invariant_pre_header) > 0 or len(induction_pre_header) > 0:
        preheader_triple = Triple(TripleType.LABEL, None, None, None, uid=triple_uid())
        opt_ctx.insert_triple(preheader_index, preheader_triple, "Loop Pre-Header Label")
        header_label = header.trips[0]
        for t in opt_ctx.label_references[header_label]:
            if t.index < header_label.index:
                val = get_triple_label_reference_value(t, header_label)
                val.value = preheader_triple
                CHANGE_HINTS[t] = "Retarget to Loop Pre-Header"
                opt_ctx.triples_dirty = True
        preheader_index += 1

    for t in invariant_pre_header:
        opt_ctx.remove_triple(t, "Loop Invariant")
        opt_ctx.insert_triple(preheader_index, t, "Loop Invariant")
        preheader_index += 1

    for t in induction_pre_header:
        opt_ctx.insert_triple(preheader_index, t, "Induction Preloop")
        preheader_index += 1

    for t in remove_basic_induction:
        opt_ctx.remove_triple(t, "Useless Basic Induction Variable")

    return len(invariant_pre_header) > 0 or len(remove_basic_induction) > 0