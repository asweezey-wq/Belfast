from belfast_triples_opt import *
from belfast_data import *
import belfast_data
from belfast_triples import FunctionTripleContext
from belfast_variable_analysis import *
from typing import *
import sys

DO_ADDRESS_COMPUTING = True

def get_forced_output_registers(triple: Triple):
    match triple.typ:
        case TripleType.BINARY_OP:
            match triple.op:
                case Operator.DIVIDE | Operator.MULTIPLY:
                    return (RAX_INDEX, (RDX_INDEX, ))
                case Operator.MODULUS:
                    return (RDX_INDEX, (RAX_INDEX, ))
        case TripleType.SYSCALL:
            return (RAX_INDEX, ())
        case TripleType.ARG:
            return (SYSCALL_ARG_REGISTERS[triple.data] if triple.flags & TF_SYSCALL else ARG_REGISTERS[triple.data], ())
    
    return None

def get_forced_input_registers(triple: Triple):
    match triple.typ:
        case TripleType.BINARY_OP:
            match triple.op:
                case Operator.DIVIDE | Operator.MODULUS | Operator.MULTIPLY:
                    return (RAX_INDEX, 0)
                case Operator.SHIFT_LEFT | Operator.SHIFT_RIGHT:
                    if triple.r_val.typ != TripleValueType.CONSTANT:
                        return (0, RCX_INDEX)

    return (0,0)

def insert_x86_regmoves(trips: List[Triple]):
    new_trips: List[Triple] = []
    trip_refs = get_reference_data(trips)
    for t in trips:
        if t.typ == TripleType.BINARY_OP:
            if t.op == Operator.DIVIDE or t.op == Operator.MODULUS or t.op == Operator.MULTIPLY:
                reg_val = TripleValue(TripleValueType.REGISTER, RAX_INDEX)
                new_trips.append(Triple(TripleType.REGMOVE, None, reg_val, t.l_val, uid=triple_uid()))
                t.l_val = reg_val
                if t.r_val.typ == TripleValueType.CONSTANT:
                    new_trips.append(Triple(TripleType.NOP_REF, None, t.r_val, None, uid=triple_uid()))
                    t.r_val = TripleValue(TripleValueType.TRIPLE_REF, new_trips[-1])
                new_trips.append(Triple(TripleType.REGMOVE, None, TripleValue(TripleValueType.REGISTER, RDX_INDEX), TripleValue(TripleValueType.CONSTANT, 0), uid=triple_uid()))
                new_trips.append(t)
                if t in trip_refs:
                    ref_triple = Triple(TripleType.NOP_REF, None, create_tref_value(t), None, flags=TF_DONT_FORWARD, uid=triple_uid())
                    new_trips.append(ref_triple)
                    for ref_t in trip_refs[t]:
                        val = get_triple_reference_value(ref_t, t)
                        val.value = ref_triple
                if t.op == Operator.DIVIDE or t.op == Operator.MULTIPLY:
                    new_trips.append(Triple(TripleType.REGMOVE, None, TripleValue(TripleValueType.REGISTER, RDX_INDEX), TripleValue(TripleValueType.UNKNOWN, 0), uid=triple_uid()))
                elif t.op == Operator.MODULUS:
                    new_trips.append(Triple(TripleType.REGMOVE, None, TripleValue(TripleValueType.REGISTER, RAX_INDEX), TripleValue(TripleValueType.UNKNOWN, 0), uid=triple_uid()))
                continue
        in_l, in_r = get_forced_input_registers(t)
        if in_l != 0:
            reg_val = TripleValue(TripleValueType.REGISTER, in_l)
            new_trips.append(Triple(TripleType.REGMOVE, None, reg_val, t.l_val, uid=triple_uid()))
            t.l_val = reg_val
        if in_r != 0:
            reg_val = TripleValue(TripleValueType.REGISTER, in_r)
            new_trips.append(Triple(TripleType.REGMOVE, None, reg_val, t.r_val, uid=triple_uid()))
            t.r_val = reg_val
 
        if t.typ == TripleType.ARG:
            arg_reg = get_forced_output_registers(t)
            new_trips.append(Triple(TripleType.REGMOVE, None, TripleValue(TripleValueType.REGISTER, arg_reg[0]), t.l_val, uid=triple_uid()))
            continue
        elif t.typ == TripleType.FUN_ARG_IN:
            new_trips.append(t)
            new_trips.append(Triple(TripleType.ASSIGN, None, t.l_val, TripleValue(TripleValueType.REGISTER, ARG_REGISTERS[t.data]), uid=triple_uid()))
        else:
            new_trips.append(t)
        out_r = get_forced_output_registers(t)
        if out_r is not None:
            # new_trips.append(Triple(TripleType.REGMOVE, None, TripleValue(TripleValueType.REGISTER, out_r[0]), TripleValue(TripleValueType.TRIPLE_REF, t)))
            for byp_r in out_r[1]:
                new_trips.append(Triple(TripleType.REGMOVE, None, TripleValue(TripleValueType.REGISTER, byp_r), TripleValue(TripleValueType.UNKNOWN, 0), uid=triple_uid()))
        if t.typ == TripleType.BINARY_OP and t.op in [Operator.SHIFT_RIGHT, Operator.SHIFT_LEFT]:
            if t.r_val.typ != TripleValueType.CONSTANT:
                new_trips.append(Triple(TripleType.NOP_USE, None, t.r_val, None, uid=triple_uid()))
        elif t.typ == TripleType.SYSCALL:
            new_trips.append(Triple(TripleType.NOP_USE, None, TripleValue(TripleValueType.TRIPLE_REF, t), None, uid=triple_uid()))
    return new_trips

def does_reference_as_memory(t:Triple, ref_t:Triple):
    match t.typ:
        case TripleType.STORE | TripleType.LOAD:
            return t.l_val.typ == TripleValueType.TRIPLE_REF and t.l_val.value == ref_t
    
    return False

def insert_lea(trips: List[Triple]):
    triple_references = get_reference_data(trips)
    lea_accum = []
    to_remove = []
    if DO_ADDRESS_COMPUTING:
        for t in trips:
            if t in triple_references and len(triple_references[t]) > 0 and all([does_reference_as_memory(t1, t) for t1 in triple_references[t]]):
                if t.typ == TripleType.BINARY_OP and t.op in (Operator.PLUS, Operator.MINUS):
                    new_v = TripleValue(TripleValueType.ADDRESS_COMPUTE, (t.l_val, t.r_val, 1 if t.op == Operator.PLUS else -1))
                    for t1 in triple_references[t]:
                        v = get_triple_reference_value(t1, t)
                        if t1.l_val == v:
                            t1.l_val = new_v
                        else:
                            t1.r_val = new_v
                    to_remove.append(t)

        for t in to_remove:
            trips.remove(t)
            CHANGE_HINTS[t] = "Replaced by address computation"

    return len(to_remove) > 0

def remove_redundant_moves(trips: List[Triple]):
    index_triples(trips)
    to_remove = []
    for i,t in enumerate(trips):
        if i == 0:
            continue
        if t.typ == TripleType.REGMOVE:
            if trips[i-1].typ == TripleType.ASSIGN:
                var_ref = create_var_ref_value(trips[i-1].l_val.value)
                if triple_values_equal(t.r_val, var_ref) and triple_values_equal(t.l_val, trips[i-1].r_val):
                    to_remove.append(t)

    for t in to_remove:
        trips.remove(t)

class Context_x86:

    def __init__(self) -> None:
        self.ctx_name = ''
        self.function_return_var = ''
        self.register_alloc: Dict[TripleValue, int] = {}
        self.val_liveness : Dict[TripleValue, Set[int]] = {}
        self.spilled_values : Dict[TripleValue, int] = {}
        self.memory_spill_register = None
        self.local_buffers : List[Buffer] = []

    def get_allocated_register(self, tv:TripleValue, tripl_num:int):
        if tv in self.register_alloc:
            return self.register_alloc[tv]
        return None

    def get_all_used_registers(self, index:int):
        reg = set()
        for v,s in self.val_liveness.items():
            if index in s and v in self.register_alloc:
                reg.add(self.register_alloc[v])
        return reg

def optimize_x86(trips: List[Triple], trip_ctx: FunctionTripleContext):
    if len(trips) == 0:
        return trips
    trips = insert_x86_regmoves(trips)

    remove_redundant_moves(trips)
    insert_lea(trips)

    ctx = Context_x86()
    ctx.ctx_name = trip_ctx.ctx_name
    ctx.local_buffers = trip_ctx.local_buffers
    ctx.function_return_var = trip_ctx.function_return_var
    while x86_block_analysis(trips, ctx):
        pass

    i = 8 * len(ctx.spilled_values)
    for lb in ctx.local_buffers:
        lb.rsp_offset = i
        i += lb.size

    x86_trips = convert_x86_triples(trips, ctx)
    index_triples(x86_trips)

    return x86_trips, ctx

def output_x86_trips_to_str(trips: List[Triple], trip_ctx):
    string = ""
    for t in trips:
        s = print_triple(t)
        r = trip_ctx.get_allocated_register(TripleValue(TripleValueType.TRIPLE_REF, t), t.index)
        if r is not None:
            s += f" -> {reg_str_for_size(r)}"
        string += s + '\n'
    return string

def x86_block_analysis(trips: List[Triple], ctx: Context_x86):
    index_triples(trips)
    annotate_triples(trips)
    x86_assign_registers(trips, ctx)
    did_change = False
    trips_to_remove = filter(lambda t: (t.flags & TF_REMOVE) > 0, trips)
    for t in trips_to_remove:
        trips.remove(t)
        did_change = True
    return did_change

def x86_assign_registers(trips: List[Triple], trip_ctx: Context_x86):
    trip_ctx.register_alloc.clear()
    blocks = build_control_flow(trips)

    all_vals : Set[TripleValue] = set()

    for b in blocks:
        v_use = evaluate_block_value_usage(b)
        all_vals.update(v_use)

    propagate_block_values(blocks)

    val_live, val_use_counts = evaluate_liveness(blocks)


    spilled_values = []
    memory_register_value = None
    interf_graph = create_interference_graph(trips, val_live)
    uses_globals = False

    for t in trips:
        if t.typ == TripleType.CALL or t.typ == TripleType.SYSCALL:
            tref = create_tref_value(t)
            for v,l in val_live.items():
                if not triple_values_equal(v, tref) and (t.index + 1) in l:
                    if tref not in interf_graph:
                        interf_graph[tref] = set()
                    interf_graph[tref].add(v)
                    interf_graph[v].add(tref)
        if not uses_globals and any([v.typ == TripleValueType.GLOBAL_REF for v in get_uses(t, colored_only=False)]):
            uses_globals = True

    precolors = {}
    coalesces_performed = {}
    values_coalesced = {}

    return_trips = [t for t in trips if t.typ == TripleType.RETURN]
    return_var = trip_ctx.function_return_var
    reg_order = DATA_REGISTERS if trip_ctx.ctx_name == 'main' else CALLER_SAVED_REG + CALLEE_SAVED_REG

    for v in interf_graph:
        match v.typ:
            case TripleValueType.REGISTER:
                precolors[v] = reg_order.index(v.value)
            case TripleValueType.VAR_REF:
                if return_var and v.value == return_var:
                    precolors[v] = reg_order.index(RAX_INDEX)
            case TripleValueType.TRIPLE_REF:
                t = v.value
                match t.typ:
                    case TripleType.BINARY_OP:
                        match t.op:
                            case Operator.MODULUS:
                                precolors[v] = reg_order.index(RDX_INDEX)
                            case Operator.DIVIDE | Operator.MULTIPLY:
                                precolors[v] = reg_order.index(RAX_INDEX)
                    case TripleType.SYSCALL | TripleType.CALL:
                        precolors[v] = reg_order.index(RAX_INDEX)
            case TripleValueType.GLOBAL_REF | TripleValueType.GLOBAL_LABEL:
                uses_globals = True

    if uses_globals:
        memory_register_value = TripleValue(TripleValueType.ON_STACK, 0)
        for k in interf_graph:
            interf_graph[k].add(memory_register_value)
        interf_graph[memory_register_value] = set(interf_graph.keys())

    while True:
        coalesce_nodes = {}

        for t in trips:
            match t.typ:
                case TripleType.ASSIGN:
                    lval = TripleValue(TripleValueType.VAR_REF, t.l_val.value)
                    if lval not in val_live:
                        t.flags |= TF_REMOVE
                    else:
                        while lval in values_coalesced:
                            lval = values_coalesced[lval]
                        rval = t.r_val
                        while rval in values_coalesced:
                            rval = values_coalesced[rval]
                        if lval != rval and lval in interf_graph and rval in interf_graph:
                            if rval not in interf_graph[lval]:
                                if lval not in coalesce_nodes:
                                    coalesce_nodes[lval] = []
                                coalesce_nodes[lval].append(rval)
                                if rval not in coalesce_nodes:
                                    coalesce_nodes[rval] = []
                                coalesce_nodes[rval].append(lval)
                case TripleType.REGMOVE:
                    lval = t.l_val
                    while lval in values_coalesced:
                        lval = values_coalesced[lval]
                    rval = t.r_val
                    while rval in values_coalesced:
                        rval = values_coalesced[rval]
                    if lval != rval and lval in interf_graph and rval in interf_graph:
                        if rval not in interf_graph[lval]:
                            if lval not in coalesce_nodes:
                                coalesce_nodes[lval] = []
                            coalesce_nodes[lval].append(rval)
                            if rval not in coalesce_nodes:
                                coalesce_nodes[rval] = []
                            coalesce_nodes[rval].append(lval)
                case _:
                    if does_triple_produce_data(t):
                        lval = t.l_val
                        while lval in values_coalesced:
                            lval = values_coalesced[lval]
                        rval = t.r_val
                        while rval in values_coalesced:
                            rval = values_coalesced[rval]
                        tref = TripleValue(TripleValueType.TRIPLE_REF, t)
                        while tref in values_coalesced:
                            tref = values_coalesced[tref]
                        if tref in interf_graph:
                            c_w = None
                            if tref != lval and lval in interf_graph and lval not in interf_graph[tref]:
                                c_w = lval
                            elif tref != rval and rval in interf_graph and rval not in interf_graph[tref]:
                                c_w = rval
                            if c_w is not None:
                                if c_w not in coalesce_nodes:
                                    coalesce_nodes[c_w] = []
                                coalesce_nodes[c_w].append(tref)
                                if tref not in coalesce_nodes:
                                    coalesce_nodes[tref] = []
                                coalesce_nodes[tref].append(c_w)

        num_regs = len(DATA_REGISTERS) if belfast_data.COMPILER_SETTINGS.register_limit == 0 else belfast_data.COMPILER_SETTINGS.register_limit
        register_alloc, spilled = color_interf_graph_chaitin_briggs(interf_graph, {}, precolors, num_regs, force_no_spill=(memory_register_value,) if memory_register_value else ())

        DO_COALESCE = True

        if len(spilled) == 0:
            if len(register_alloc) == 0:
                break
            did_coalesce = False
            if DO_COALESCE:
                cmax = max(register_alloc.values())
                for k,v_l in coalesce_nodes.items():
                    for v in v_l:
                        # Make sure they don't interfere
                        if v in interf_graph and k in interf_graph and v not in interf_graph[k]:
                            if k in precolors and v in precolors and precolors[k] != precolors[v]:
                                continue
                            c = 0
                            edge_cols = [register_alloc[e] for e in set(interf_graph[v]).union(set(interf_graph[k]))]
                            if k in precolors:
                                if precolors[k] in edge_cols:
                                    continue
                                else:
                                    c = precolors[k]
                            if v in precolors:
                                if precolors[v] in edge_cols:
                                    continue
                                else:
                                    c = precolors[v]

                            while c in edge_cols:
                                c += 1
                            if c > cmax:
                                continue

                            coalesced_node = TripleValue(TripleValueType.UNKNOWN, len(coalesces_performed))
                            if k in precolors or v in precolors:
                                precolors[coalesced_node] = c
                            coalesces_performed[coalesced_node] = (k, v)
                            interf_graph[coalesced_node] = set(interf_graph[v]).union(set(interf_graph[k]))
                            for e in interf_graph[coalesced_node]:
                                if e in interf_graph:
                                    if k in interf_graph[e]:
                                        interf_graph[e].remove(k)
                                    if v in interf_graph[e]:
                                        interf_graph[e].remove(v)
                                    interf_graph[e].add(coalesced_node)
                            did_coalesce = True
                            values_coalesced[k] = coalesced_node
                            values_coalesced[v] = coalesced_node
                            del interf_graph[k]
                            del interf_graph[v]
                            register_alloc[coalesced_node] = c
                            del register_alloc[k]
                            del register_alloc[v]
                            break
            if not did_coalesce:
                break
            else:
                continue
        elif memory_register_value is None:
            memory_register_value = TripleValue(TripleValueType.ON_STACK, 0)
            for k in interf_graph:
                interf_graph[k].add(memory_register_value)
            interf_graph[memory_register_value] = set(interf_graph.keys())
        elif memory_register_value in spilled:
            print("ERROR: No viable register allocation found", file=sys.stderr)
            sys.exit(1)
        for v in spilled:
            if v == memory_register_value:
                continue
            spilled_values.append(v)
            for e in interf_graph[v]:
                interf_graph[e].remove(v)
            del interf_graph[v]

    # print(spilled_values)

    if memory_register_value is not None:
        # print(f"MEMORY SPILL REG: {reg_str_for_size(reg_order[register_alloc[memory_register_value]])}")
        trip_ctx.memory_spill_register = reg_order[register_alloc[memory_register_value]]
        del register_alloc[memory_register_value]

    coal_nodes = list(coalesces_performed.keys())

    #Uncoalesce
    while len(coal_nodes) > 0:
        removed_nodes = []
        for c in coal_nodes:
            if c in register_alloc:
                v1,v2 = coalesces_performed[c]
                register_alloc[v1] = register_alloc[c]
                register_alloc[v2] = register_alloc[c]
                del register_alloc[c]
                removed_nodes.append(c)
        for c in removed_nodes:
            coal_nodes.remove(c)

    # print()
    # print('\n'.join(map(lambda x: f"{x[0]}: {reg_str_for_size(DATA_REGISTERS[x[1]])}", sorted(register_alloc.items(), key=lambda x: (x[0].typ.value, x[0].value.index if x[0].typ == TripleValueType.TRIPLE_REF else x[1])))))

    trip_ctx.register_alloc = {k:reg_order[v] for k,v in register_alloc.items()}
    trip_ctx.val_liveness = val_live
    trip_ctx.spilled_values = {v:i for i,v in enumerate(spilled_values)}

    pass

def convert_x86_triples(trips: List[Triple], trip_ctx: Context_x86):
    # x86_trips = []
    to_remove = []
    for t in trips:
        # x86_trip = copy(t)
        l_reg = -1
        r_reg = -1
        if t.l_val:
            lv = t.l_val
            if t.typ == TripleType.FUN_ARG_IN or t.typ == TripleType.NOP_USE:
                to_remove.append(t)
                continue
            if t.l_val.typ == TripleValueType.VAR_ASSIGN:
                lv = TripleValue(TripleValueType.VAR_REF, t.l_val.value)
                l_reg = trip_ctx.get_allocated_register(lv, t.index + 1)
                if l_reg is not None:
                    t.l_val = TripleValue(TripleValueType.REGISTER, l_reg)
                elif lv in trip_ctx.spilled_values:
                    t.l_val = TripleValue(TripleValueType.ON_STACK, trip_ctx.spilled_values[lv] * 8)
                    l_reg = 2000
            elif t.l_val.typ == TripleValueType.ADDRESS_COMPUTE:
                v1, v2, s = t.l_val.value
                v1_r = trip_ctx.get_allocated_register(v1, t.index)
                if v1_r is not None:
                    v1 = TripleValue(TripleValueType.REGISTER, v1_r)
                elif v1 in trip_ctx.spilled_values:
                    v1 = TripleValue(TripleValueType.ON_STACK, trip_ctx.spilled_values[v1] * 8)
                elif v1.typ != TripleValueType.CONSTANT and v1.typ != TripleValueType.REGISTER and v1.typ != TripleValueType.GLOBAL_REF:
                    assert False
                v2_r = trip_ctx.get_allocated_register(v2, t.index)
                if v2_r is not None:
                    v2 = TripleValue(TripleValueType.REGISTER, v2_r)
                elif v2 in trip_ctx.spilled_values:
                    v2 = TripleValue(TripleValueType.ON_STACK, trip_ctx.spilled_values[v2] * 8)
                elif v2.typ != TripleValueType.CONSTANT and v2.typ != TripleValueType.REGISTER and v2.typ != TripleValueType.GLOBAL_REF:
                    assert False
                t.l_val.value = (v1, v2, s)
            else:
                l_reg = trip_ctx.get_allocated_register(lv, t.index)
                if l_reg is not None:
                    t.l_val = TripleValue(TripleValueType.REGISTER, l_reg)
                elif lv in trip_ctx.spilled_values:
                    t.l_val = TripleValue(TripleValueType.ON_STACK, trip_ctx.spilled_values[lv] * 8)
                    l_reg = 2000
                elif lv.typ in [TripleValueType.TRIPLE_REF, TripleValueType.VAR_REF]:
                    if t.typ == TripleType.IF_COND and lv.typ == TripleValueType.TRIPLE_REF and (lv.value.flags & TF_BOOL_FORWARDED) > 0:
                        pass
                    else:
                        assert False
        if t.r_val:
            r_reg = trip_ctx.get_allocated_register(t.r_val, t.index)
            if r_reg is not None:
                t.r_val = TripleValue(TripleValueType.REGISTER, r_reg)
            elif t.r_val in trip_ctx.spilled_values:
                t.r_val = TripleValue(TripleValueType.ON_STACK, trip_ctx.spilled_values[t.r_val] * 8)
                r_reg = 2000
            elif t.r_val.typ == TripleValueType.ADDRESS_COMPUTE:
                v1, v2, s = t.r_val.value
                v1_r = trip_ctx.get_allocated_register(v1, t.index)
                if v1_r is not None:
                    v1 = TripleValue(TripleValueType.REGISTER, v1_r)
                elif v1.typ != TripleValueType.CONSTANT:
                    assert False
                v2_r = trip_ctx.get_allocated_register(v2, t.index)
                if v2_r is not None:
                    v2 = TripleValue(TripleValueType.REGISTER, v2_r)
                elif v2.typ != TripleValueType.CONSTANT:
                    assert False
                t.r_val.value = (v1, v2, s)
        if t.typ == TripleType.ASSIGN or t.typ == TripleType.REGMOVE:
            if t.r_val.typ == TripleValueType.UNKNOWN:
                to_remove.append(t)
            else:
                assert l_reg != -1 and r_reg != -1
                if l_reg == r_reg:
                    to_remove.append(t)
        if t.typ == TripleType.NOP_REF:
            tref_reg = trip_ctx.get_allocated_register(create_tref_value(t), t.index)
            if tref_reg is not None:
                if l_reg != -1 and l_reg == tref_reg:
                    to_remove.append(t)
                else:
                    t.typ = TripleType.REGMOVE
                    t.r_val = t.l_val
                    t.l_val = create_register_value(tref_reg)
        # trip_reg = trip_ctx.get_allocated_register(TripleValue(TripleValueType.TRIPLE_REF, t), t.index)
        # trip_str += print_triple(x86_trip) + (f" -> {reg_str_for_size(trip_reg)}" if trip_reg is not None else "") + '\n'
    
    for t in to_remove:
        trips.remove(t)
    
    # index_triples(trips)

    return trips


HEADER = """DEFAULT REL
    segment .text
"""

def triple_value_str(tv: TripleValue, trip_ctx: Context_x86, as_hex=False, size=64):
    match tv.typ:
        case TripleValueType.UNKNOWN | TripleValueType.BUFFER_REF:
            assert False
        case TripleValueType.CONSTANT:
            if as_hex:
                return hex(tv.value)
            else:
                return str(tv.value)
        case TripleValueType.REGISTER:
            return reg_str_for_size(tv.value, size)
        case TripleValueType.STRING_REF:
            assert tv.value.label is not None, "String was not assigned a label"
            return tv.value.label
        case TripleValueType.LOCAL_BUFFER_REF:
            assert tv.value.rsp_offset is not None, "Local buffer was not assigned stack space"
            if tv.value.rsp_offset == 0:
                return "[rsp]"
            return f"[rsp+{tv.value.rsp_offset}]"
        case TripleValueType.TRIPLE_TARGET:
            return f"{trip_ctx.ctx_name}_L{tv.value.index}"
        case TripleValueType.FUN_LABEL:
            return f"_{tv.value}"
        case TripleValueType.ON_STACK:
            return f"qword [rsp+{tv.value}]" if tv.value > 0 else "qword [rsp]"
        case TripleValueType.GLOBAL_REF:
            return f"qword [_{tv.value}]"
        case TripleValueType.GLOBAL_LABEL:
            return f"_{tv.value}"
        case TripleValueType.ADDRESS_COMPUTE:
            v1, v2, pos = tv.value
            assert v1.typ in (TripleValueType.REGISTER, TripleValueType.GLOBAL_LABEL) and (v2.typ == TripleValueType.REGISTER or v2.typ == TripleValueType.CONSTANT), "Invalid Address Compute args"
            if v2.typ == TripleValueType.CONSTANT and v2.value == 0:
                return f"[{triple_value_str(v1, trip_ctx)}]"
            return f"[{triple_value_str(v1, trip_ctx)}{'+' if pos == 1 else '-'}{triple_value_str(v2, trip_ctx)}]"
        case _:
            assert False, f"Type {tv.typ.name} not implemented"

def is_triple_value_in_memory(tv: TripleValue):
    return tv.typ == TripleValueType.ON_STACK

# implied other operand is a register
def stat_move(tv: TripleValue, s: CodeScoreStat):
    if is_triple_value_in_memory:
        s.mem_loads += 1
    s.mov_ops += 1

# implied other operand is a register
def stat_binop(tv: TripleValue, s: CodeScoreStat):
    if is_triple_value_in_memory:
        s.mem_loads += 1
    s.basic_ops += 1

BOP_MAP = {
    Operator.PLUS: 'add',
    Operator.MINUS: 'sub',
    Operator.BITWISE_AND: 'and',
    Operator.BITWISE_OR: 'or',
    Operator.BITWISE_XOR: 'xor',
}

UNOP_MAP = {
    Operator.BITWISE_NOT: "not",
    Operator.NEGATE: "neg",
}

class ValueLoc(Enum):
    UNKNOWN = auto()
    REGISTER = auto()
    CONSTANT = auto()
    ON_STACK = auto()
    AT_LABEL = auto() # e.g. the value is stored at the label address
    MEMORY_ADDR_LABEL = auto() # e.g. the value is the label address
    MEMORY_ADDR_STACK = auto() # e.g. the value is the stack address
    JMP_LABEL = auto()
    ADDRESS_COMPUTE = auto()
    IN_CMP_FLAGS = auto()

def get_value_loc(tv: TripleValue):
    match tv.typ:
        case TripleValueType.CONSTANT:
            return ValueLoc.CONSTANT
        case TripleValueType.REGISTER:
            return ValueLoc.REGISTER
        case TripleValueType.LOCAL_BUFFER_REF:
            return ValueLoc.MEMORY_ADDR_STACK
        case TripleValueType.ON_STACK:
            return ValueLoc.ON_STACK
        case TripleValueType.STRING_REF | TripleValueType.GLOBAL_LABEL:
            return ValueLoc.MEMORY_ADDR_LABEL
        case TripleValueType.GLOBAL_REF:
            return ValueLoc.AT_LABEL
        case TripleValueType.TRIPLE_TARGET | TripleValueType.FUN_LABEL:
            return ValueLoc.JMP_LABEL
        case TripleValueType.ADDRESS_COMPUTE:
            return ValueLoc.ADDRESS_COMPUTE
        case TripleValueType.TRIPLE_REF:
            if tv.value.flags & TF_BOOL_FORWARDED:
                return ValueLoc.IN_CMP_FLAGS
            else:
                return ValueLoc.UNKNOWN
        case _:
            return ValueLoc.UNKNOWN

def get_supported_modes(typ: TripleType):
    match typ:
        case TripleType.SYSCALL:
            return [(ValueLoc.CONSTANT, None),]
        case TripleType.BINARY_OP:
            a = []
            for lvt in (ValueLoc.REGISTER, ValueLoc.ON_STACK, ValueLoc.AT_LABEL, ValueLoc.CONSTANT):
                for rvt in (ValueLoc.CONSTANT, ValueLoc.REGISTER, ValueLoc.ON_STACK, ValueLoc.AT_LABEL):
                    a.append((lvt, rvt))
            return a
        case TripleType.UNARY_OP:
            return [(ValueLoc.REGISTER, None),]
        case TripleType.CALL | TripleType.GOTO:
            return [(ValueLoc.JMP_LABEL, None)]
        case TripleType.IF_COND:
            return [(ValueLoc.REGISTER, ValueLoc.JMP_LABEL),(ValueLoc.IN_CMP_FLAGS, ValueLoc.JMP_LABEL),]
        case TripleType.ASSIGN:
            return [(ValueLoc.REGISTER, ValueLoc.REGISTER),(ValueLoc.REGISTER, ValueLoc.CONSTANT),(ValueLoc.REGISTER, ValueLoc.MEMORY_ADDR_STACK),(ValueLoc.REGISTER, ValueLoc.MEMORY_ADDR_LABEL),(ValueLoc.REGISTER, ValueLoc.ON_STACK),(ValueLoc.REGISTER, ValueLoc.AT_LABEL),\
            (ValueLoc.ON_STACK, ValueLoc.REGISTER), (ValueLoc.ON_STACK, ValueLoc.CONSTANT), ]
        case TripleType.REGMOVE:
            return [(ValueLoc.REGISTER, ValueLoc.REGISTER),(ValueLoc.REGISTER, ValueLoc.CONSTANT),(ValueLoc.REGISTER, ValueLoc.ON_STACK),(ValueLoc.REGISTER, ValueLoc.AT_LABEL),(ValueLoc.REGISTER, ValueLoc.MEMORY_ADDR_LABEL),(ValueLoc.REGISTER, ValueLoc.MEMORY_ADDR_STACK),]
        case TripleType.ARG:
            return [(ValueLoc.REGISTER, None), (ValueLoc.CONSTANT, None)]
        case TripleType.STORE:
            a = []
            for lvt in (ValueLoc.REGISTER, ValueLoc.ON_STACK, ValueLoc.AT_LABEL, ValueLoc.MEMORY_ADDR_STACK, ValueLoc.MEMORY_ADDR_LABEL, ValueLoc.ADDRESS_COMPUTE):
                for rvt in (ValueLoc.CONSTANT, ValueLoc.REGISTER, ValueLoc.ON_STACK, ValueLoc.AT_LABEL, ValueLoc.MEMORY_ADDR_STACK):
                    a.append((lvt, rvt))
            return a
        case TripleType.LOAD:
            return [(v, None) for v in (ValueLoc.REGISTER, ValueLoc.ON_STACK, ValueLoc.AT_LABEL, ValueLoc.MEMORY_ADDR_STACK, ValueLoc.ADDRESS_COMPUTE)]
        case TripleType.RETURN:
            return [(ValueLoc.REGISTER, None),(ValueLoc.CONSTANT, None)]
        case TripleType.LABEL:
            return [(None, None)]
        case _:
            return []

SUPPORTED_MODES = {k:get_supported_modes(k) for k in TripleType._member_map_.values()}

def move_instr(reg:int, tv: TripleValue, trip_ctx: Context_x86):
    if tv.typ in [TripleValueType.BUFFER_REF, TripleValueType.STRING_REF, TripleValueType.LOCAL_BUFFER_REF]:
        return f"lea {reg_str_for_size(reg)}, {triple_value_str(tv, trip_ctx)}"
    else:
        return f"mov {reg_str_for_size(reg)}, {triple_value_str(tv, trip_ctx)}"

def convert_loc(from_v: TripleValue, to_v: TripleValue, trip_ctx: Context_x86):
    from_loc = get_value_loc(from_v)
    to_loc = get_value_loc(to_v)
    assert to_loc not in [ValueLoc.MEMORY_ADDR_LABEL, ValueLoc.CONSTANT, ValueLoc.JMP_LABEL, ValueLoc.MEMORY_ADDR_STACK], "Invalid location conversion destination"
    move_into_reg = to_loc != ValueLoc.REGISTER and from_loc not in [ValueLoc.CONSTANT, ValueLoc.REGISTER]
    asm = ""
    if triple_values_equal(from_v, to_v):
        return asm

    if from_v.typ == TripleValueType.CONSTANT and from_v.value == 0 and to_v.typ == TripleValueType.REGISTER:
        return f"xor {triple_value_str(to_v, trip_ctx)}, {triple_value_str(to_v, trip_ctx)}"

    if move_into_reg:
        asm += move_instr(trip_ctx.memory_spill_register, from_v, trip_ctx)
        from_loc = ValueLoc.REGISTER
        from_v = create_register_value(trip_ctx.memory_spill_register)
    
    match from_loc:
        case ValueLoc.REGISTER | ValueLoc.CONSTANT | ValueLoc.ON_STACK | ValueLoc.AT_LABEL:
            asm += f"mov {triple_value_str(to_v, trip_ctx)}, {triple_value_str(from_v, trip_ctx)}"
        case ValueLoc.MEMORY_ADDR_LABEL | ValueLoc.MEMORY_ADDR_STACK:
            asm += f"lea {triple_value_str(to_v, trip_ctx)}, {triple_value_str(from_v, trip_ctx)}"
        case _:
            assert False, "Invalid from location"

    return asm

def prep_address_compute(tv: TripleValue, trip_ctx: Context_x86):
    asm = []
    lv1 = tv.value[0]
    lv2 = tv.value[1]
    pos = tv.value[2]

    locs = (get_value_loc(lv1), get_value_loc(lv2))
    if locs[0] == ValueLoc.CONSTANT:
        if pos == -1:
            assert False
        else:
            locs = locs[locs[1], locs[0]]
            tmp = lv2
            lv2 = lv1
            lv1 = tmp

    # TODO: we can combine a stack address and register into one, but address compute doesn't support that rn
    match locs:
        case (ValueLoc.REGISTER, ValueLoc.REGISTER) | (ValueLoc.REGISTER, ValueLoc.CONSTANT) | (ValueLoc.MEMORY_ADDR_LABEL, ValueLoc.CONSTANT):
            pass
        case (ValueLoc.ON_STACK, ValueLoc.CONSTANT) | (ValueLoc.ON_STACK, ValueLoc.REGISTER) | (ValueLoc.AT_LABEL, ValueLoc.CONSTANT) | (ValueLoc.AT_LABEL, ValueLoc.REGISTER) | (ValueLoc.MEMORY_ADDR_STACK, ValueLoc.REGISTER):
            # If one value is on stack/in label and the other is a register/constant
            newv = create_register_value(trip_ctx.memory_spill_register)
            asm.append(convert_loc(lv1, newv, trip_ctx))
            lv1 = newv
        case (ValueLoc.REGISTER, ValueLoc.ON_STACK) | (ValueLoc.REGISTER, ValueLoc.AT_LABEL) | (ValueLoc.REGISTER, ValueLoc.MEMORY_ADDR_STACK):
            # If one value is on stack/in label and the other is a register/constant
            newv = create_register_value(trip_ctx.memory_spill_register)
            asm.append(convert_loc(lv2, newv, trip_ctx))
            lv2 = newv
        case (ValueLoc.MEMORY_ADDR_STACK, ValueLoc.CONSTANT):
            assert lv1.typ == TripleValueType.LOCAL_BUFFER_REF
            rsp_offset = lv1.value.rsp_offset
            lv1 = TripleValue(TripleValueType.LOCAL_BUFFER_REF, rsp_offset + lv2.value * pos)
            lv2 = create_const_value(0)
        case (ValueLoc.ON_STACK, ValueLoc.ON_STACK) | (ValueLoc.ON_STACK, ValueLoc.AT_LABEL) | (ValueLoc.ON_STACK, ValueLoc.MEMORY_ADDR_STACK) | \
            (ValueLoc.AT_LABEL, ValueLoc.ON_STACK) | (ValueLoc.AT_LABEL, ValueLoc.AT_LABEL) | (ValueLoc.AT_LABEL, ValueLoc.MEMORY_ADDR_STACK) | \
            (ValueLoc.MEMORY_ADDR_STACK, ValueLoc.ON_STACK) | (ValueLoc.MEMORY_ADDR_STACK, ValueLoc.AT_LABEL) | (ValueLoc.MEMORY_ADDR_STACK, ValueLoc.MEMORY_ADDR_STACK):
            newv = create_register_value(trip_ctx.memory_spill_register)
            asm.append(convert_loc(lv1, newv, trip_ctx))
            op = "add" if pos == 1 else "sub"
            asm.append(f"{op} {triple_value_str(newv, trip_ctx)}, {triple_value_str(lv2, trip_ctx)}")
            lv1 = newv
            lv2 = create_const_value(0)
        case _:
            assert False, f"Unhandled Mode {locs}"

    return TripleValue(TripleValueType.ADDRESS_COMPUTE, (lv1, lv2, pos)), asm

def convert_function_to_asm(fun_name: str, trips: List[Triple], trip_ctx: Context_x86, code_stats: CodeScoreStat):
    asm = ""
    asm += f"    global _{fun_name}\n_{fun_name}:\n"
    def write_asm(s):
        nonlocal asm
        if s != "":
            asm += f"    {s}\n"

    saved_registers = []

    if fun_name != 'main':
        for i in CALLEE_SAVED_REG:
            if i in trip_ctx.register_alloc.values():
                saved_registers.append(i)
                code_stats.mem_stores += 1
                write_asm(f"push {reg_str_for_size(i)}")
        if trip_ctx.memory_spill_register is not None and trip_ctx.memory_spill_register in CALLEE_SAVED_REG:
            saved_registers.append(trip_ctx.memory_spill_register)
            write_asm(f"push {reg_str_for_size(trip_ctx.memory_spill_register)}")

    stack_space_alloc = 0

    if len(trip_ctx.spilled_values) > 0:
        stack_space_alloc += len(trip_ctx.spilled_values)*8
    if len(trip_ctx.local_buffers) > 0:
        stack_space_alloc += sum([b.size for b in trip_ctx.local_buffers])

    if stack_space_alloc % 16 != 0:
        stack_space_alloc = ((stack_space_alloc // 16) + 1) * 16
    
    if stack_space_alloc > 0:
        code_stats.basic_ops += 1
        write_asm(f"sub rsp, {stack_space_alloc}")

    code_stats.registers_used = set(trip_ctx.register_alloc.values())

    for t in trips:
        if belfast_data.COMPILER_SETTINGS.asm_comments:
            asm += f"  ; {print_triple(t)}\n"
        try:
            lv = t.l_val
            rv = t.r_val
            mode = (get_value_loc(lv) if lv else None, get_value_loc(rv) if rv else None)
            if mode[0] == ValueLoc.UNKNOWN or mode[1] == ValueLoc.UNKNOWN:
                assert False
            if t.typ not in SUPPORTED_MODES:
                assert False, f"Invalid triple type {t.typ}"
            expected_modes = SUPPORTED_MODES[t.typ]
            if mode not in expected_modes:
                print(f"Mode {mode} not expected for type {t.typ}")
                mode = (get_value_loc(lv) if lv else None, get_value_loc(rv) if rv else None)
            trip_ref = create_tref_value(t)
            t_reg = trip_ctx.get_allocated_register(trip_ref, t.index)
            output_val = None
            output_mode = ValueLoc.UNKNOWN
            if t_reg is not None:
                output_mode = ValueLoc.REGISTER
                output_val = create_register_value(t_reg)
            elif trip_ref in trip_ctx.spilled_values:
                output_mode = ValueLoc.ON_STACK
                output_val = TripleValue(TripleValueType.ON_STACK, trip_ctx.spilled_values[trip_ref] * 8)
            elif t.flags & TF_BOOL_FORWARDED:
                output_mode = ValueLoc.IN_CMP_FLAGS
            match t.typ:
                case TripleType.REGMOVE | TripleType.ASSIGN:
                    write_asm(convert_loc(rv, lv, trip_ctx))
                case TripleType.BINARY_OP:
                    match t.op:
                        case Operator.PLUS:
                            assert output_mode in (ValueLoc.REGISTER,)
                            if triple_values_equal(output_val, rv):
                                write_asm(f"add {triple_value_str(output_val, trip_ctx)}, {triple_value_str(lv, trip_ctx)}")
                            else:
                                write_asm(convert_loc(lv, output_val, trip_ctx))
                                write_asm(f"add {triple_value_str(output_val, trip_ctx)}, {triple_value_str(rv, trip_ctx)}")
                        case Operator.MINUS:
                            assert output_mode in (ValueLoc.REGISTER,)
                            if triple_values_equal(output_val, rv):
                                write_asm(f"neg {triple_value_str(rv, trip_ctx)}")
                                write_asm(f"add {triple_value_str(rv, trip_ctx)}, {triple_value_str(lv, trip_ctx)}")
                            else:
                                write_asm(convert_loc(lv, output_val, trip_ctx))
                                write_asm(f"sub {triple_value_str(output_val, trip_ctx)}, {triple_value_str(rv, trip_ctx)}")
                        case Operator.GE | Operator.LE | Operator.GT | Operator.LT | Operator.NE | Operator.EQ:
                            assert output_mode in (ValueLoc.IN_CMP_FLAGS, ValueLoc.REGISTER, ValueLoc.AT_LABEL, ValueLoc.ON_STACK)
                            if mode[0] == ValueLoc.CONSTANT:
                                tmp = lv
                                lv = rv
                                rv = tmp
                                t.op = FLIP_CMP_OP[t.op]
                            if output_mode == ValueLoc.IN_CMP_FLAGS:
                                write_asm(f"cmp {triple_value_str(lv, trip_ctx)}, {triple_value_str(rv, trip_ctx)}")
                            else:
                                assert output_val is not None
                                write_asm(f"cmp {triple_value_str(lv, trip_ctx)}, {triple_value_str(rv, trip_ctx)}")
                                write_asm(f"mov {triple_value_str(output_val, trip_ctx)}, 0") # We must do a move so as not to set cmp flags
                                write_asm(f"set{CMP_OP_INSTR_MAP[t.op]} {triple_value_str(output_val, trip_ctx, size=8)}")
                        case Operator.SHIFT_LEFT | Operator.SHIFT_RIGHT:
                            assert output_mode in (ValueLoc.REGISTER,)
                            if triple_values_equal(output_val, rv):
                                assert False
                            write_asm(convert_loc(lv, output_val, trip_ctx))
                            assert mode[1] == ValueLoc.CONSTANT or (mode[1] == ValueLoc.REGISTER and rv.value == RCX_INDEX), "Expected shift RHS to be constant or in RCX"
                            op = 'shl' if t.op == Operator.SHIFT_LEFT else 'shr'
                            if t.flags & TF_SIGNED:
                                op = 'sal' if t.op == Operator.SHIFT_LEFT else 'sar'
                            write_asm(f"{op} {triple_value_str(output_val, trip_ctx)}, {triple_value_str(rv, trip_ctx, size=8)}")
                        case Operator.BITWISE_AND | Operator.BITWISE_OR | Operator.BITWISE_XOR:
                            assert output_mode in (ValueLoc.REGISTER,)
                            if triple_values_equal(output_val, rv):
                                write_asm(f"{BOP_MAP[t.op]} {triple_value_str(output_val, trip_ctx)}, {triple_value_str(lv, trip_ctx)}")
                            else:
                                write_asm(convert_loc(lv, output_val, trip_ctx))
                                write_asm(f"{BOP_MAP[t.op]} {triple_value_str(output_val, trip_ctx)}, {triple_value_str(rv, trip_ctx)}")
                        case Operator.MULTIPLY:
                            assert output_mode == ValueLoc.REGISTER, "Expected multiply to output to register"
                            assert output_val.value == RAX_INDEX, "Multiply must output to RAX"
                            if triple_values_equal(output_val, rv):
                                assert False
                            write_asm(convert_loc(lv, output_val, trip_ctx))
                            write_asm(f"imul {triple_value_str(rv, trip_ctx)}")
                        case Operator.DIVIDE:
                            assert output_mode == ValueLoc.REGISTER, "Expected divide to output to register"
                            assert output_val.value == RAX_INDEX, "Divide must output to RAX"
                            if triple_values_equal(output_val, rv):
                                assert False
                            write_asm(convert_loc(lv, output_val, trip_ctx))
                            write_asm(f"idiv {triple_value_str(rv, trip_ctx)}")
                        case Operator.MODULUS:
                            assert output_mode == ValueLoc.REGISTER, "Expected modulus to output to register"
                            assert output_val.value == RDX_INDEX, "Modulus must output to RDX"
                            assert lv.typ == TripleValueType.REGISTER and lv.value == RAX_INDEX, "Modulus must have RAX input"
                            if triple_values_equal(output_val, rv):
                                assert False
                            write_asm(f"idiv {triple_value_str(rv, trip_ctx)}")
                        case _:
                            assert False, f"Unimplmented operator {t.op.name}"
                case TripleType.UNARY_OP:
                    assert t.op in UNOP_MAP, f"Operator {t.op.name} not supported"
                    op = UNOP_MAP[t.op]
                    write_asm(convert_loc(lv, output_val, trip_ctx))
                    write_asm(f"{op} {triple_value_str(output_val, trip_ctx)}")
                case TripleType.LABEL:
                    write_asm(f"{trip_ctx.ctx_name}_L{t.index}:")
                case TripleType.GOTO:
                    write_asm(f"jmp {triple_value_str(lv, trip_ctx)}")
                case TripleType.IF_COND:
                    match mode:
                        case (ValueLoc.IN_CMP_FLAGS, _):
                            op = INVERT_CMP_OP[lv.value.op] if t.op == Operator.NE else lv.value.op
                            write_asm(f"j{CMP_OP_INSTR_MAP[op]} {triple_value_str(rv, trip_ctx)}")
                        case (ValueLoc.REGISTER, _):
                            code_stats.basic_ops += 1
                            write_asm(f"cmp {triple_value_str(lv, trip_ctx)}, 0")
                            if t.op == Operator.NE:
                                write_asm(f"je {triple_value_str(rv, trip_ctx)}")
                            elif t.op == Operator.EQ:
                                write_asm(f"jne {triple_value_str(rv, trip_ctx)}")
                            else:
                                assert False, f"Unimplemented IF_COND operator {t.op.name}"
                        case _:
                            assert False, f"Unimplemented mode {mode}"
                case TripleType.STORE:
                    # TODO: this \/\/
                    assert rv.typ in [TripleValueType.REGISTER, TripleValueType.CONSTANT], "Expected STORE RHS to be a constant or register"
                    mem_word = MEM_WORD_SIZE_MAP[t.size]                    
                    if mode[0] != ValueLoc.ADDRESS_COMPUTE:
                        address_compute_value, new_asm = prep_address_compute(TripleValue(TripleValueType.ADDRESS_COMPUTE, (lv, create_const_value(0), 1)), trip_ctx)
                    else:
                        address_compute_value, new_asm = prep_address_compute(lv, trip_ctx)
                    for a in new_asm:
                        write_asm(a)
                    write_asm(f"mov {mem_word} {triple_value_str(address_compute_value, trip_ctx)}, {triple_value_str(rv, trip_ctx, size=t.size)}")
                case TripleType.LOAD:
                    mem_word = MEM_WORD_SIZE_MAP[t.size]
                    instr = "mov" if t.size == 64 or t.size == 32 else ("movsx" if t.flags & TF_SIGNED else "movzx")
                    t_reg_size = 64 if t.size != 32 else 32
                    if mode[0] != ValueLoc.ADDRESS_COMPUTE:
                        address_compute_value, new_asm = prep_address_compute(TripleValue(TripleValueType.ADDRESS_COMPUTE, (lv, create_const_value(0), 1)), trip_ctx)
                    else:
                        address_compute_value, new_asm = prep_address_compute(lv, trip_ctx)
                    for a in new_asm:
                        write_asm(a)
                    if output_mode == ValueLoc.REGISTER:
                        write_asm(f"{instr} {triple_value_str(output_val, trip_ctx, size=t_reg_size)}, {mem_word} {triple_value_str(address_compute_value, trip_ctx)}")
                    elif output_mode == ValueLoc.ON_STACK:
                        memv = create_register_value(trip_ctx.memory_spill_register)
                        write_asm(f"{instr} {triple_value_str(memv, trip_ctx, size=t_reg_size)}, {mem_word} {triple_value_str(address_compute_value, trip_ctx)}")
                        write_asm(convert_loc(memv, output_val, trip_ctx))
                    else:
                        assert False, f"Invalid output mode {output_mode}"
                case TripleType.SYSCALL:
                    assert output_mode == ValueLoc.REGISTER and t_reg == RAX_INDEX, "Expected SYSCALL to be stored in RAX"
                    assert lv is not None and lv.typ == TripleValueType.CONSTANT, "SYSCALL expected a numerical syscall argument"
                    stat_move(lv, code_stats)
                    write_asm(convert_loc(lv, create_register_value(RAX_INDEX), trip_ctx))
                    code_stats.syscalls += 1
                    write_asm("syscall")
                case TripleType.NOP_REF:
                    assert output_mode != ValueLoc.UNKNOWN
                    write_asm(convert_loc(lv, output_val, trip_ctx))
                case TripleType.CALL:
                    assert lv is not None and lv.typ == TripleValueType.FUN_LABEL  
                    code_stats.fun_calls += 1                  
                    write_asm(f"call {triple_value_str(lv, trip_ctx)}")
                case TripleType.RETURN:
                    if mode[0] != ValueLoc.REGISTER or lv.value != RAX_INDEX:
                        write_asm(convert_loc(lv, create_register_value(RAX_INDEX), trip_ctx))
                case _:
                    assert False, f"Triple Type {t.typ.name} not implemented"
        except AssertionError as e:
            print('Error generating Triple:\n' + print_triple(t), file=sys.stderr)
            print(e, file=sys.stderr)
            sys.exit(1)

    if stack_space_alloc > 0:
        code_stats.basic_ops += 1
        write_asm(f"add rsp, {stack_space_alloc}")
    
    if fun_name != 'main' and len(saved_registers) > 0:
        for i in reversed(saved_registers):
            code_stats.mem_loads += 1
            write_asm(f"pop {reg_str_for_size(i)}")

    asm += "    ret\n\n"

    return asm

def get_asm_header():
    return HEADER

def get_asm_footer(trip_ctx: TripleContext):
    asm = ""

    all_strings = trip_ctx.strings
    all_global_vars = trip_ctx.parsectx.globals

    if len(all_global_vars) > 0:
        asm += "\n\tsegment .bss\n"
        for v in all_global_vars:
            asm += f"_{v}: resb 8\n"

    if len(all_strings) > 0:
        asm += "\tsegment .data\n"
        for s, labl in all_strings.items():
            asm += f"{labl}: db `{s.encode('unicode_escape').decode('utf-8')}`, 0\n"

    called_funs = set()
    for f_name in trip_ctx.parsectx.fun_signatures:
        f_ctx = trip_ctx.get_function(f_name)
        for t in f_ctx.triples:
            if t.typ == TripleType.CALL:
                called_funs.add(t.l_val.value)

    called_funs = called_funs.difference(trip_ctx.parsectx.fun_signatures.keys())

    for f in called_funs:
        asm += f"extern _{f}\n"

    return asm