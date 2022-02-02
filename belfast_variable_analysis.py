from belfast_data import *
from belfast_triples import print_triple
from belfast_triples_opt import *
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
        case TripleType.UNARY_OP | TripleType.IF_COND | TripleType.PRINT | TripleType.NOP_USE | TripleType.NOP_REF | TripleType.LOAD | TripleType.ARG | TripleType.RETURN:
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

def identify_loops(trips: List[Triple], blocks: List[TripleBlock]) -> bool:
    did_change = False
    if len(blocks) == 0:
        return False
    block_visit = {}
    dom_map = {}
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

    for b1,b2 in loops.items():
        # print(f'Loop from {b1.trips[0].index} to {b2.trips[-1].index}')
        blocks_in = [b for b in blocks if b1.index <= b.index <= b2.index]
        # TODO: better block in loop checks
        # print(blocks_in)
        loop_invariants = set()
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
        
        # print(loop_defines)

        loop_pre_header = []
        triple_inserts = []

        for inv in loop_invariants:
            if inv.typ == TripleValueType.TRIPLE_REF and b1.trips[0].index <= inv.value.index <= b2.trips[-1].index :
                loop_pre_header.append(inv.value)
                
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
                                basic_induction_vars[d] = const_vals[0].value
        
        # print(basic_induction_vars)

        remove_induction = []

        for b in basic_induction_vars:
            if b in loop_uses and len(loop_uses[b]) == 1:
                # Useless induction var within the loop, check outside the loop
                is_useless = True
                for bl in blocks_in:
                    for out_bl in bl.out_blocks:
                        if out_bl not in blocks_in and b in out_bl.in_vals:
                            is_useless = False
                            break
                if is_useless:
                    remove_induction.append(loop_uses[b][0])

        derived_induction_vars = {}

        def is_linear_on_basic(t: Triple, shallow=False):
            if t.typ == TripleType.BINARY_OP:
                if t.op in [Operator.MULTIPLY, Operator.PLUS, Operator.SHIFT_LEFT, Operator.MINUS]:
                    # TODO: Support non-constant derived modifiers
                    const_vals = [v for v in (t.l_val, t.r_val) if v in loop_invariants]
                    var_vals = [v for v in (t.l_val, t.r_val) if v in basic_induction_vars]
                    trip_ref_vals = [v for v in (t.l_val, t.r_val) if v not in loop_invariants and v.typ == TripleValueType.TRIPLE_REF]
                    if len(const_vals) == 1:
                        if len(var_vals) == 1:
                            match t.op:
                                case Operator.MULTIPLY:
                                    return [(var_vals[0], 0, const_vals[0], 0, 0)]
                                case Operator.PLUS:
                                    return [(var_vals[0], 0, 1, const_vals[0], 0)]
                                case Operator.MINUS:
                                    if const_vals[0] == t.l_val:
                                        return [(var_vals[0], 0, -1, const_vals[0], 0)]
                                    else:
                                        return [(var_vals[0], 0, 1, 0, const_vals[0])]
                                case Operator.SHIFT_LEFT:
                                    return [(var_vals[0], const_vals[0], 1, 0, 0)]
                                case _:
                                    assert False, f"Unknown operator {t.op.name}"
                        elif not shallow and len(trip_ref_vals) == 1:
                            res = is_linear_on_basic(trip_ref_vals[0].value, shallow=True)
                            if res is not None:
                                res = res[0]
                                match t.op:
                                    case Operator.MULTIPLY:
                                        return [res,(res[0], 0, const_vals[0], 0, 0)]
                                    case Operator.PLUS:
                                        return [res,(res[0], 0, 1, const_vals[0], 0)]
                                    case Operator.MINUS:
                                        return [res,(res[0], 0, 1, 0, const_vals[0])]
                                    case Operator.SHIFT_LEFT:
                                        return [res,(res[0], const_vals[0], 1, 0, 0)]
                                    case _:
                                        assert False, f"Unknown operator {t.op.name}"
            return None

        for d,t_l in loop_defines.items():
            if len(t_l) == 1 and d not in basic_induction_vars:
                trip = None
                if d.typ == TripleValueType.VAR_REF:
                    assigned = t_l[0].r_val
                    if assigned.typ == TripleValueType.TRIPLE_REF:
                        trip = assigned.value
                elif d.typ == TripleValueType.TRIPLE_REF:
                    trip = d.value
                if trip is not None:
                    res = is_linear_on_basic(trip, shallow=True)
                    if res is not None:
                        a = 1
                        b = 0
                        c = None
                        d_ = None
                        v = None
                        for r in res:
                            v = r[0]
                            if isinstance(r[1], int):
                                a *= 2 ** r[1]
                            elif r[1].typ == TripleValueType.CONSTANT:
                                a *= 2 ** r[1].value
                            else:
                                assert False
                            if isinstance(r[2], int):
                                a *= r[2]
                            elif r[2].typ == TripleValueType.CONSTANT:
                                a *= r[2].value
                            else:
                                assert False
                            if isinstance(r[3], int):
                                b += r[3]
                            elif r[3].typ == TripleValueType.CONSTANT:
                                b += r[3].value
                            else:
                                c = r[3]
                            if isinstance(r[4], int):
                                b -= r[4]
                            elif r[4].typ == TripleValueType.CONSTANT:
                                b -= r[4].value
                            else:
                                d_ = r[4]
                        assert v is not None
                        derived_induction_vars[d] = (v, a, b, c, d_)

        # print(derived_induction_vars)
        ind_defines = []
        ind_step_trips = []
        for d,(v,a,b,c,d_) in derived_induction_vars.items():
            if d.typ == TripleValueType.TRIPLE_REF:
                if a == 1 and c is None and d_ is None:
                    continue
            elif d.typ != TripleValueType.VAR_REF:
                continue
            t = None
            basic_var = v
            new_varname = f"${d}_inductive"
            if a == -1 and b != 0:
                t = Triple(TripleType.BINARY_OP, Operator.MINUS, create_const_value(b), v)
                v = create_tref_value(t)
                loop_pre_header.append(t)
            else:
                if a != 1:
                    t = Triple(TripleType.BINARY_OP, Operator.MULTIPLY, v, create_const_value(a))
                    v = create_tref_value(t)
                    loop_pre_header.append(t)
                if b != 0:
                    t = Triple(TripleType.BINARY_OP, Operator.PLUS, v, create_const_value(b))
                    v = create_tref_value(t)
                    loop_pre_header.append(t)
            if c is not None:
                t = Triple(TripleType.BINARY_OP, Operator.PLUS, v, c)
                v = create_tref_value(t)
                loop_pre_header.append(t)
            if d_ is not None:
                t = Triple(TripleType.BINARY_OP, Operator.MINUS, v, d_)
                v = create_tref_value(t)
                loop_pre_header.append(t)
            t = Triple(TripleType.ASSIGN, None, create_var_assign_value(new_varname), v)
            v = create_tref_value(t)
            loop_pre_header.append(t)
            if d.typ == TripleValueType.VAR_REF:
                loop_define = loop_defines[d][0]
                loop_define.r_val = create_var_ref_value(new_varname)
                ind_defines.append(loop_define)
            elif d.typ == TripleValueType.TRIPLE_REF:
                loop_define = loop_defines[d][0]
                loop_define.typ = TripleType.NOP_REF
                loop_define.op = None
                loop_define.l_val = create_var_ref_value(new_varname)
                loop_define.r_val = None
                ind_defines.append(loop_define)
            else:
                assert False

            ind = loop_defines[basic_var][0].index + 1
            t = Triple(TripleType.BINARY_OP, Operator.PLUS, create_var_ref_value(new_varname), create_const_value(a * basic_induction_vars[basic_var]))
            t.index = ind
            triple_inserts.append(t)
            ind_step_trips.append(t)
            t = Triple(TripleType.ASSIGN, None, create_var_assign_value(new_varname), create_tref_value(t))
            t.index = ind + 1
            triple_inserts.append(t)
            ind_step_trips.append(t)

        for t in triple_inserts:
            trips.insert(t.index, t)
        new_labels = []
        if len(loop_pre_header) > 0:
            ind_offs = b1.trips[0].index
            new_label = Triple(TripleType.LABEL, None, None, None)
            assert b1.trips[0].typ == TripleType.LABEL
            for t in trips:
                l_ref = get_triple_label_reference_value(t, b1.trips[0])
                if l_ref is not None:
                    l_ref.value = new_label
                    ADD_HINTS[t] = "Retargeted to loop pre-header"
                if t == b1.trips[0]:
                    break
            trips.insert(ind_offs, new_label)
            new_labels.append(new_label)
            ind_offs += 1
            for t in loop_pre_header:
                if t.index != -1 and t in trips:
                    trips.remove(t)
                trips.insert(ind_offs, t)
                ind_offs += 1
        index_triples(trips)

        for t in loop_pre_header:
            ADD_HINTS[t] = "Loop Invariant"
        for t in ind_defines:
            ADD_HINTS[t] = "Derived Induction variable"
        for t in ind_step_trips:
            ADD_HINTS[t] = "Inductive step"
        for t in new_labels:
            ADD_HINTS[t] = "Loop pre-header"
        for t in remove_induction:
            trips.remove(t)
            REMOVAL_HINTS[t] = "Useluess induction variable"

        if len(triple_inserts) > 0 or len(loop_pre_header) > 0 or len(remove_induction) > 0:
            return True

    return False
    

            

