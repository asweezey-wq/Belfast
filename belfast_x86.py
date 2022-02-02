from asyncore import write
from re import S
from tracemalloc import start
from belfast_triples_opt import *
from belfast_data import *
import belfast_data
from belfast_triples import TripleContext
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
    for t in trips:
        if t.typ == TripleType.BINARY_OP:
            if t.op == Operator.DIVIDE or t.op == Operator.MODULUS or t.op == Operator.MULTIPLY:
                reg_val = TripleValue(TripleValueType.REGISTER, RAX_INDEX)
                new_trips.append(Triple(TripleType.REGMOVE, None, reg_val, t.l_val))
                t.l_val = reg_val
                if t.r_val.typ == TripleValueType.CONSTANT:
                    new_trips.append(Triple(TripleType.NOP_REF, None, t.r_val, None))
                    t.r_val = TripleValue(TripleValueType.TRIPLE_REF, new_trips[-1])
                new_trips.append(Triple(TripleType.REGMOVE, None, TripleValue(TripleValueType.REGISTER, RDX_INDEX), TripleValue(TripleValueType.CONSTANT, 0)))
                new_trips.append(t)
                if t.op == Operator.DIVIDE or t.op == Operator.MULTIPLY:
                    new_trips.append(Triple(TripleType.REGMOVE, None, TripleValue(TripleValueType.REGISTER, RDX_INDEX), TripleValue(TripleValueType.UNKNOWN, 0)))
                elif t.op == Operator.MODULUS:
                    new_trips.append(Triple(TripleType.REGMOVE, None, TripleValue(TripleValueType.REGISTER, RAX_INDEX), TripleValue(TripleValueType.UNKNOWN, 0)))
                continue
        in_l, in_r = get_forced_input_registers(t)
        if in_l != 0:
            reg_val = TripleValue(TripleValueType.REGISTER, in_l)
            new_trips.append(Triple(TripleType.REGMOVE, None, reg_val, t.l_val))
            t.l_val = reg_val
        if in_r != 0:
            reg_val = TripleValue(TripleValueType.REGISTER, in_r)
            new_trips.append(Triple(TripleType.REGMOVE, None, reg_val, t.r_val))
            t.r_val = reg_val
 
        if t.typ == TripleType.ARG:
            arg_reg = get_forced_output_registers(t)
            new_trips.append(Triple(TripleType.REGMOVE, None, TripleValue(TripleValueType.REGISTER, arg_reg[0]), t.l_val))
            continue
        elif t.typ == TripleType.FUN_ARG_IN:
            new_trips.append(t)
            new_trips.append(Triple(TripleType.ASSIGN, None, t.l_val, TripleValue(TripleValueType.REGISTER, ARG_REGISTERS[t.data])))
        else:
            new_trips.append(t)
        out_r = get_forced_output_registers(t)
        if out_r is not None:
            # new_trips.append(Triple(TripleType.REGMOVE, None, TripleValue(TripleValueType.REGISTER, out_r[0]), TripleValue(TripleValueType.TRIPLE_REF, t)))
            for byp_r in out_r[1]:
                new_trips.append(Triple(TripleType.REGMOVE, None, TripleValue(TripleValueType.REGISTER, byp_r), TripleValue(TripleValueType.UNKNOWN, 0)))
        if t.typ == TripleType.BINARY_OP and t.op in [Operator.SHIFT_RIGHT, Operator.SHIFT_LEFT]:
            if t.r_val.typ != TripleValueType.CONSTANT:
                new_trips.append(Triple(TripleType.NOP_USE, None, t.r_val, None))
        elif t.typ == TripleType.SYSCALL:
            new_trips.append(Triple(TripleType.NOP_USE, None, TripleValue(TripleValueType.TRIPLE_REF, t), None))
    return new_trips

def does_reference_as_memory(t:Triple, ref_t:Triple):
    match t.typ:
        case TripleType.STORE | TripleType.LOAD:
            return t.l_val.typ == TripleValueType.TRIPLE_REF and t.l_val.value == ref_t
    
    return False

def insert_lea(trips: List[Triple], trip_ctx: TripleContext):
    triple_references, var_references, var_assignments = get_reference_data(trips, trip_ctx)
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
            REMOVAL_HINTS[t] = "Replaced by address computation"

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

def optimize_x86(trips: List[Triple], trip_ctx: TripleContext):
    if len(trips) == 0:
        return trips
    trips = insert_x86_regmoves(trips)

    remove_redundant_moves(trips)
    insert_lea(trips, trip_ctx)

    while x86_block_analysis(trips, trip_ctx):
        pass

    i = 8 * len(trip_ctx.spilled_values)
    for lb in trip_ctx.local_buffers:
        lb.rsp_offset = i
        i += lb.size

    x86_trips = convert_x86_triples(trips, trip_ctx)

    return x86_trips

def output_x86_trips_to_str(trips: List[Triple], trip_ctx):
    string = ""
    for t in trips:
        s = print_triple(t)
        r = trip_ctx.get_allocated_register(TripleValue(TripleValueType.TRIPLE_REF, t), t.index)
        if r is not None:
            s += f" -> {reg_str_for_size(r)}"
        string += s + '\n'
    return string

def x86_block_analysis(trips: List[Triple], trip_ctx: TripleContext):
    index_triples(trips)
    annotate_triples(trips, trip_ctx)
    x86_assign_registers(trips, trip_ctx)
    did_change = False
    trips_to_remove = filter(lambda t: (t.flags & TF_REMOVE) > 0, trips)
    for t in trips_to_remove:
        trips.remove(t)
        did_change = True
    return did_change

def x86_assign_registers(trips: List[Triple], trip_ctx: TripleContext):
    trip_ctx.register_alloc = {}
    blocks = build_control_flow(trips, trip_ctx)

    all_vals : Set[TripleValue] = set()

    for b in blocks:
        v_use = evaluate_block_value_usage(b)
        all_vals.update(v_use)

    propagate_block_values(blocks)

    val_live, val_use_counts = evaluate_liveness(blocks)


    spilled_values = []
    memory_register_value = None
    interf_graph = create_interference_graph(trips, val_live)

    for t in trips:
        if t.typ == TripleType.CALL or t.typ == TripleType.SYSCALL:
            tref = create_tref_value(t)
            for v,l in val_live.items():
                if not triple_values_equal(v, tref) and (t.index + 1) in l:
                    if tref not in interf_graph:
                        interf_graph[tref] = set()
                    interf_graph[tref].add(v)
                    interf_graph[v].add(tref)

    precolors = {}
    coalesces_performed = {}
    values_coalesced = {}

    return_trips = [t for t in trips if t.typ == TripleType.RETURN]
    return_var = None
    if len(return_trips) == 1:
        if return_trips[0].l_val.typ == TripleValueType.VAR_REF:
            return_var = return_trips[0].l_val.value
    elif len(return_trips) > 1:
        assert False
    reg_order = DATA_REGISTERS if trip_ctx.ctx_name == 'main' else CALLER_SAVED_REG + CALLEE_SAVED_REG

    for v in interf_graph:
        match v.typ:
            case TripleValueType.REGISTER:
                precolors[v] = reg_order.index(v.value)
            case TripleValueType.VAR_REF:
                if return_var and v.value == return_trips[0].l_val.value:
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

def convert_x86_triples(trips: List[Triple], trip_ctx: TripleContext):
    # x86_trips = []
    to_remove = []
    for t in trips:
        # x86_trip = copy(t)
        l_reg = -1
        r_reg = -1
        if t.l_val:
            lv = t.l_val
            if t.typ == TripleType.FUN_ARG_IN:
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
                elif v1.typ != TripleValueType.CONSTANT and v1.typ != TripleValueType.REGISTER:
                    assert False
                v2_r = trip_ctx.get_allocated_register(v2, t.index)
                if v2_r is not None:
                    v2 = TripleValue(TripleValueType.REGISTER, v2_r)
                elif v2 in trip_ctx.spilled_values:
                    v2 = TripleValue(TripleValueType.ON_STACK, trip_ctx.spilled_values[v2] * 8)
                elif v2.typ != TripleValueType.CONSTANT and v2.typ != TripleValueType.REGISTER:
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
        if t.typ == TripleType.ASSIGN:
            assert l_reg != -1 and r_reg != -1
            if l_reg == r_reg:
                to_remove.append(t)
        # trip_reg = trip_ctx.get_allocated_register(TripleValue(TripleValueType.TRIPLE_REF, t), t.index)
        # trip_str += print_triple(x86_trip) + (f" -> {reg_str_for_size(trip_reg)}" if trip_reg is not None else "") + '\n'
    
    for t in to_remove:
        trips.remove(t)
    
    # index_triples(trips)

    return trips


HEADER = """DEFAULT REL
    segment .text
"""

def triple_value_str(tv: TripleValue, trip_ctx: TripleContext, as_hex=False, size=64):
    match tv.typ:
        case TripleValueType.UNKNOWN:
            assert False
        case TripleValueType.CONSTANT:
            if as_hex:
                return hex(tv.value)
            else:
                return str(tv.value)
        case TripleValueType.REGISTER:
            return reg_str_for_size(tv.value, size)
        case TripleValueType.BUFFER_REF | TripleValueType.STRING_REF:
            return tv.value
        case TripleValueType.LOCAL_BUFFER_REF:
            assert tv.value.rsp_offset is not None, "Local buffer was not assigned stack space"
            return f"[rsp+{tv.value.rsp_offset}]"
        case TripleValueType.TRIPLE_TARGET:
            return f"{trip_ctx.ctx_name}_L{tv.value.index}"
        case TripleValueType.FUN_LABEL:
            return f"_{tv.value}"
        case TripleValueType.ON_STACK:
            return f"qword [rsp+{tv.value}]"
        case TripleValueType.GLOBAL_REF:
            return f"qword [_{tv.value}]"
        case TripleValueType.GLOBAL_LABEL:
            return f"_{tv.value}"
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

def move_instr(reg:int, tv: TripleValue, trip_ctx: TripleContext):
    if tv.typ in [TripleValueType.BUFFER_REF, TripleValueType.STRING_REF, TripleValueType.LOCAL_BUFFER_REF]:
        return f"lea {reg_str_for_size(reg)}, {triple_value_str(tv, trip_ctx)}"
    else:
        return f"mov {reg_str_for_size(reg)}, {triple_value_str(tv, trip_ctx)}"

def convert_function_to_asm(fun_name: str, trips: List[Triple], trip_ctx: TripleContext, code_stats: CodeScoreStat):
    asm = ""
    if any([t.typ == TripleType.PRINT for t in trips]) and not trip_ctx.has_generated_print_code:
        with open('./print_d.asm', 'r') as f:
            asm += f.read() + "\n"
        trip_ctx.has_generated_print_code = True
    asm += f"    global _{fun_name}\n_{fun_name}:\n"
    def write_asm(s):
        nonlocal asm
        asm += f"    {s}\n"

    saved_registers = []

    if fun_name != 'main':
        for i in CALLEE_SAVED_REG:
            if i in trip_ctx.register_alloc.values():
                saved_registers.append(i)
                code_stats.mem_stores += 1
                write_asm(f"push {reg_str_for_size(i)}")

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
            if rv is not None and rv.typ == TripleValueType.UNKNOWN:
                continue
            trip_ref = TripleValue(TripleValueType.TRIPLE_REF, t)
            t_reg = trip_ctx.get_allocated_register(trip_ref, t.index)
            match t.typ:
                case TripleType.REGMOVE | TripleType.ASSIGN:
                    if lv.typ == TripleValueType.REGISTER:
                        if rv.typ == TripleValueType.CONSTANT and rv.value == 0:
                            code_stats.basic_ops += 1
                            write_asm(f"xor {triple_value_str(lv, trip_ctx)}, {triple_value_str(lv, trip_ctx)}")
                        elif rv.typ == TripleValueType.REGISTER and rv.value == lv.value:
                            pass
                        else:
                            code_stats.mov_ops += 1
                            write_asm(move_instr(lv.value, rv, trip_ctx))
                    elif lv.typ == TripleValueType.ON_STACK:
                        assert rv.typ != TripleValueType.ON_STACK
                        if rv.typ not in (TripleValueType.REGISTER, TripleValueType.CONSTANT):
                            assert trip_ctx.memory_spill_register is not None
                            code_stats.mov_ops += 1
                            code_stats.mem_loads += 1
                            if is_triple_value_in_memory(lv):
                                code_stats.mem_stores += 1
                            write_asm(move_instr(trip_ctx.memory_spill_register, rv, trip_ctx))
                            write_asm(f"mov qword {triple_value_str(lv, trip_ctx)}, {reg_str_for_size(trip_ctx.memory_spill_register)}")
                        else:
                            code_stats.mov_ops += 1
                            if is_triple_value_in_memory(lv):
                                code_stats.mem_stores += 1
                            write_asm(f"mov qword {triple_value_str(lv, trip_ctx)}, {triple_value_str(rv, trip_ctx)}")
                    else:
                        assert False, f"Unhandled data type {lv.typ.name} in assign LHS"
                    
                case TripleType.BINARY_OP:
                    should_be_same_inout = t.op not in [Operator.MODULUS, Operator.PLUS] + list(CMP_OP_INSTR_MAP.keys())
                    switch_lr = False
                    can_handle_mem_lhs = t.op in CMP_OP_INSTR_MAP and t.flags & TF_BOOL_FORWARDED
                    if t.op != Operator.PLUS:
                        if (lv.typ in [TripleValueType.CONSTANT] or (lv.typ == TripleValueType.REGISTER and t_reg is not None and should_be_same_inout and lv.value != t_reg)):
                            if t_reg is not None:
                                if should_be_same_inout and rv.typ == TripleValueType.REGISTER and rv.value == t_reg:
                                    if t.op in [Operator.PLUS,Operator.BITWISE_AND, Operator.BITWISE_OR, Operator.BITWISE_XOR]:
                                        switch_lr = True
                                    else:
                                        code_stats.basic_ops += 2
                                        write_asm(f"xchg {triple_value_str(lv, trip_ctx)}, {triple_value_str(rv, trip_ctx)}")
                                        temp = rv
                                        rv = lv
                                        lv = temp
                                else:
                                    stat_move(lv, code_stats)
                                    write_asm(move_instr(t_reg, lv, trip_ctx))
                                    lv = TripleValue(TripleValueType.REGISTER, t_reg)
                            else:
                                if t.op in CMP_OP_INSTR_MAP:
                                    if rv.typ == TripleValueType.REGISTER:
                                        switch_lr = True
                                    else:
                                        assert False
                                else:
                                    assert False
                                    
                        if lv.typ == TripleValueType.ON_STACK:
                            # TODO: Binary operators can handle stack values 
                            if t_reg is not None:
                                stat_move(lv, code_stats)
                                write_asm(move_instr(t_reg, lv, trip_ctx))
                                lv = TripleValue(TripleValueType.REGISTER, t_reg)
                            else:
                                stat_move(lv, code_stats)
                                write_asm(move_instr(trip_ctx.memory_spill_register, lv, trip_ctx))
                                lv = TripleValue(TripleValueType.REGISTER, trip_ctx.memory_spill_register)
                        if switch_lr:
                            assert rv.typ == TripleValueType.REGISTER, "Expected RHS to be in a register"
                        else:
                            assert lv.typ == TripleValueType.REGISTER or (can_handle_mem_lhs and lv.typ in [TripleValueType.ON_STACK, TripleValueType.GLOBAL_REF]), "Expected LHS to be in a register"
                    match t.op:
                        case Operator.PLUS:
                            assert t_reg is not None, "Expected this value to be assigned to a register"
                            if lv.value != t_reg:
                                if rv.typ == TripleValueType.REGISTER and rv.value == t_reg:
                                    switch_lr = True
                                    stat_binop(lv, code_stats)
                                    write_asm(f"{BOP_MAP[t.op]} {reg_str_for_size(t_reg)}, {triple_value_str(lv, trip_ctx)}")
                                else:
                                    if DO_ADDRESS_COMPUTING and lv.typ == TripleValueType.REGISTER and rv.typ in [TripleValueType.CONSTANT, TripleValueType.REGISTER]:
                                        code_stats.basic_ops += 1
                                        write_asm(f"lea {reg_str_for_size(t_reg)}, [{reg_str_for_size(lv.value)}+{triple_value_str(rv, trip_ctx)}]")
                                    else:
                                        stat_move(lv, code_stats)
                                        write_asm(move_instr(t_reg, lv, trip_ctx))
                                        stat_binop(rv, code_stats)
                                        write_asm(f"{BOP_MAP[t.op]} {reg_str_for_size(t_reg)}, {triple_value_str(rv, trip_ctx)}")
                            else:
                                stat_binop(rv, code_stats)
                                write_asm(f"{BOP_MAP[t.op]} {reg_str_for_size(t_reg)}, {triple_value_str(rv, trip_ctx)}")
                        case Operator.MINUS | Operator.BITWISE_XOR | Operator.BITWISE_AND | Operator.BITWISE_OR:
                            assert t_reg is not None, "Expected this value to be assigned to a register"
                            assert lv.value == t_reg
                            stat_binop(lv if switch_lr else rv, code_stats)
                            if switch_lr:
                                write_asm(f"{BOP_MAP[t.op]} {reg_str_for_size(t_reg)}, {triple_value_str(lv, trip_ctx)}")
                            else:
                                write_asm(f"{BOP_MAP[t.op]} {reg_str_for_size(t_reg)}, {triple_value_str(rv, trip_ctx)}")
                        case Operator.GE | Operator.LE | Operator.GT | Operator.LT | Operator.NE | Operator.EQ:
                            assert t_reg is not None or (t.flags & TF_BOOL_FORWARDED) > 0, "Expected this value to be assigned to a register or forwarded to next operation"
                            if switch_lr:
                                t.op = FLIP_CMP_OP[t.op]
                                temp = lv
                                lv = rv
                                rv = temp
                            if t_reg is not None:
                                code_stats.basic_ops += 2
                                code_stats.mov_ops += 1
                                write_asm(f"cmp {triple_value_str(lv, trip_ctx)}, {triple_value_str(rv, trip_ctx)}")
                                write_asm(f"mov {reg_str_for_size(t_reg)}, 0")
                                write_asm(f"set{CMP_OP_INSTR_MAP[t.op]} {reg_str_for_size(t_reg, 8)}")
                            else:
                                code_stats.basic_ops += 1
                                write_asm(f"cmp {triple_value_str(lv, trip_ctx)}, {triple_value_str(rv, trip_ctx)}")
                        case Operator.SHIFT_LEFT | Operator.SHIFT_RIGHT:
                            assert rv.typ == TripleValueType.CONSTANT or (rv.typ == TripleValueType.REGISTER and rv.value == RCX_INDEX), "Expected RHS to be constant or RCX"
                            op = 'shl' if t.op == Operator.SHIFT_LEFT else 'shr'
                            if t.flags & TF_SIGNED:
                                op = 'sal' if t.op == Operator.SHIFT_LEFT else 'sar'
                            stat_binop(rv, code_stats)
                            write_asm(f"{op} {triple_value_str(lv, trip_ctx)}, {triple_value_str(rv, trip_ctx, size=8)}")
                        case Operator.MULTIPLY:
                            assert t_reg is not None and t_reg == RAX_INDEX and lv.typ == TripleValueType.REGISTER and lv.value == RAX_INDEX, "Expected mul to read and write from/to RAX"
                            assert rv.typ == TripleValueType.REGISTER, "Expected div RHS to be in a register"
                            code_stats.mul_ops += 1
                            write_asm(f"imul {triple_value_str(rv, trip_ctx)}")
                        case Operator.DIVIDE:
                            assert t_reg is not None and t_reg == RAX_INDEX and lv.typ == TripleValueType.REGISTER and lv.value == RAX_INDEX, "Expected div to read and write from/to RAX"
                            assert rv.typ == TripleValueType.REGISTER, "Expected div RHS to be in a register"
                            code_stats.div_ops += 1
                            write_asm(f"idiv {triple_value_str(rv, trip_ctx)}")
                        case Operator.MODULUS:
                            assert t_reg is not None and t_reg == RDX_INDEX, "Expected modulus write to RDX"
                            assert lv.typ == TripleValueType.REGISTER and lv.value == RAX_INDEX, "Expected modulus to read from RAX"
                            assert rv.typ == TripleValueType.REGISTER, "Expected modulus RHS to be in a register"
                            code_stats.div_ops += 1
                            write_asm(f"idiv {triple_value_str(rv, trip_ctx)}")
                        case _:
                            assert False, f"Unimplemented operator {t.op.name}"
                case TripleType.UNARY_OP:
                    if t_reg is not None and ((lv.typ in (TripleValueType.CONSTANT, TripleValueType.ON_STACK)) or (lv.typ == TripleValueType.REGISTER and lv.value != t_reg)):
                        stat_move(lv, code_stats)
                        write_asm(move_instr(t_reg, lv, trip_ctx))
                        lv = TripleValue(TripleValueType.REGISTER, t_reg)
                    assert lv.typ == TripleValueType.REGISTER, "Expected LHS to be in a register"
                    code_stats.basic_ops += 1
                    match t.op:
                        case Operator.NEGATE:
                            assert t_reg is not None, "Expected this value to be assigned to a register"
                            write_asm(f"neg {reg_str_for_size(t_reg)}")
                        case Operator.BITWISE_NOT:
                            assert t_reg is not None, "Expected this value to be assigned to a register"
                            write_asm(f"not {reg_str_for_size(t_reg)}")
                        case _:
                            assert False, f"Unimplemented operator {t.op.name}"
                case TripleType.LABEL:
                    write_asm(f"{trip_ctx.ctx_name}_L{t.index}:")
                case TripleType.GOTO:
                    assert lv.typ == TripleValueType.TRIPLE_TARGET, "Expected GOTO LHS to be a label"
                    code_stats.jmp_ops += 1
                    write_asm(f"jmp {triple_value_str(lv, trip_ctx)}")
                case TripleType.IF_COND:
                    assert rv.typ == TripleValueType.TRIPLE_TARGET, "IF_COND expected RHS value to be a label"
                    code_stats.cond_jmp_ops += 1
                    if lv.typ == TripleValueType.TRIPLE_REF and (lv.value.flags & TF_BOOL_FORWARDED) > 0:
                        assert lv.value.op in CMP_OP_INSTR_MAP, "Expected Bool forwarded triple to be a CMP op"
                        write_asm(f"j{CMP_OP_INSTR_MAP[INVERT_CMP_OP[lv.value.op]]} {triple_value_str(rv, trip_ctx)}")
                    else:
                        assert lv.typ == TripleValueType.REGISTER, "Expected LHS to be in a register"
                        code_stats.basic_ops += 1
                        write_asm(f"cmp {triple_value_str(lv, trip_ctx)}, 0")
                        if t.op == Operator.NE:
                            write_asm(f"je {triple_value_str(rv, trip_ctx)}")
                        elif t.op == Operator.EQ:
                            write_asm(f"jne {triple_value_str(rv, trip_ctx)}")
                        else:
                            assert False, f"Unimplemented IF_COND operator {t.op.name}"
                case TripleType.STORE:
                    assert rv.typ in [TripleValueType.REGISTER, TripleValueType.CONSTANT], "Expected STORE RHS to be a constant or register"
                    mem_word = MEM_WORD_SIZE_MAP[t.size]
                    if lv.typ in [TripleValueType.REGISTER, TripleValueType.STRING_REF, TripleValueType.BUFFER_REF, TripleValueType.LOCAL_BUFFER_REF, TripleValueType.GLOBAL_LABEL]:
                        code_stats.mem_stores += 1
                        code_stats.mov_ops += 1
                        write_asm(f"mov {mem_word} [{triple_value_str(lv, trip_ctx)}], {triple_value_str(rv, trip_ctx, size=t.size)}")
                    elif lv.typ == TripleValueType.ADDRESS_COMPUTE:
                        lv1 = lv.value[0]
                        lv2 = lv.value[1]
                        pos = lv.value[2]
                        regs = [v for v in (lv1, lv2) if v.typ == TripleValueType.REGISTER]
                        consts = [v for v in (lv1, lv2) if v.typ == TripleValueType.CONSTANT]
                        stack_vals = [v for v in (lv1, lv2) if v.typ == TripleValueType.ON_STACK]
                        
                        if len(stack_vals) == 2:
                            code_stats.basic_ops += 1
                            code_stats.mov_ops += 2
                            code_stats.mem_loads += 2
                            code_stats.mem_stores += 1
                            write_asm(move_instr(trip_ctx.memory_spill_register, stack_vals[0], trip_ctx))
                            write_asm(f"add {reg_str_for_size(trip_ctx.memory_spill_register)}, {triple_value_str(stack_vals[1], trip_ctx)}")
                            write_asm(f"mov {mem_word} [{reg_str_for_size(trip_ctx.memory_spill_register)}], {triple_value_str(rv, trip_ctx, size=t.size)}")
                        else:
                            if len(stack_vals) == 1:
                                code_stats.mov_ops += 1
                                code_stats.mem_loads += 1
                                write_asm(move_instr(trip_ctx.memory_spill_register, stack_vals[0], trip_ctx))
                                stack_vals.pop()
                                regs.append(create_register_value(trip_ctx.memory_spill_register))
                            if len(regs) == 2 or (len(regs) == 1 and len(consts) == 1):
                                la = regs[0]
                                ra = regs[1] if len(regs) > 1 else consts[0]
                                code_stats.mem_stores += 1
                                code_stats.mov_ops += 1
                                write_asm(f"mov {mem_word} [{triple_value_str(la, trip_ctx)}{'+' if pos == 1 else '-'}{triple_value_str(ra, trip_ctx)}], {triple_value_str(rv, trip_ctx, size=t.size)}")
                            else:
                                assert False
                    else:
                        assert False, f"Unhandled value type {lv.typ.name}"
                case TripleType.LOAD:
                    assert t_reg is not None, "Expected this value to be assigned to a register"
                    mem_word = MEM_WORD_SIZE_MAP[t.size]
                    instr = "mov" if t.size == 64 or t.size == 32 else ("movsx" if t.flags & TF_SIGNED else "movzx")
                    t_reg_size = 64 if t.size != 32 else 32
                    if lv.typ in [TripleValueType.REGISTER, TripleValueType.STRING_REF, TripleValueType.BUFFER_REF, TripleValueType.LOCAL_BUFFER_REF]:
                        code_stats.mov_ops += 1
                        code_stats.mem_loads += 1
                        write_asm(f"{instr} {reg_str_for_size(t_reg, t_reg_size)}, {mem_word} [{triple_value_str(lv, trip_ctx)}]")
                    elif lv.typ == TripleValueType.ADDRESS_COMPUTE:
                        lv1 = lv.value[0]
                        lv2 = lv.value[1]
                        pos = lv.value[2]
                        regs = [v for v in (lv1, lv2) if v.typ == TripleValueType.REGISTER]
                        consts = [v for v in (lv1, lv2) if v.typ == TripleValueType.CONSTANT]
                        stack_vals = [v for v in (lv1, lv2) if v.typ == TripleValueType.ON_STACK]
                        
                        if len(stack_vals) == 2:
                            code_stats.basic_ops += 1
                            code_stats.mov_ops += 2
                            code_stats.mem_loads += 3
                            write_asm(move_instr(trip_ctx.memory_spill_register, stack_vals[0], trip_ctx))
                            write_asm(f"add {reg_str_for_size(trip_ctx.memory_spill_register)}, {triple_value_str(stack_vals[1], trip_ctx)}")
                            write_asm(f"{instr} {reg_str_for_size(t_reg, t_reg_size)}, {mem_word} [{reg_str_for_size(trip_ctx.memory_spill_register)}]")
                        else:
                            if len(stack_vals) == 1:
                                code_stats.mem_loads += 1
                                code_stats.mov_ops += 1
                                write_asm(move_instr(trip_ctx.memory_spill_register, stack_vals[0], trip_ctx))
                                stack_vals.pop()
                                regs.append(create_register_value(trip_ctx.memory_spill_register))
                            if len(regs) == 2 or (len(regs) == 1 and len(consts) == 1):
                                la = regs[0]
                                ra = regs[1] if len(regs) > 1 else consts[0]
                                code_stats.mem_loads += 1
                                code_stats.mov_ops += 1
                                write_asm(f"{instr} {reg_str_for_size(t_reg, t_reg_size)}, {mem_word} [{triple_value_str(la, trip_ctx)}{'+' if pos == 1 else '-'}{triple_value_str(ra, trip_ctx)}]")
                            else:
                                assert False

                case TripleType.SYSCALL:
                    assert t_reg is not None and t_reg == RAX_INDEX, "Expected SYSCALL to be stored in RAX"
                    assert lv is not None and lv.typ == TripleValueType.CONSTANT, "SYSCALL expected a numerical syscall argument"
                    save_regs = list(filter(lambda x: x in [3, 12], trip_ctx.get_all_used_registers(t.index)))
                    # for r in save_regs:
                    #     code_stats.mem_stores += 1
                    #     write_asm(f"push {reg_str_for_size(r)}")
                    stat_move(lv, code_stats)
                    write_asm(move_instr(t_reg, lv, trip_ctx))
                    code_stats.syscalls += 1
                    write_asm("syscall")
                    # for r in reversed(save_regs):
                    #     code_stats.mem_loads += 1
                    #     write_asm(f"pop {reg_str_for_size(r)}")
                case TripleType.PRINT:
                    save_regs = list(filter(lambda x: x in DATA_REGISTERS, trip_ctx.get_all_used_registers(t.index+1)))
                    for r in save_regs:
                        code_stats.mem_stores += 1
                        write_asm(f"push {reg_str_for_size(r)}")
                    if lv.typ != TripleValueType.REGISTER or lv.value != RDI_INDEX:
                        stat_move(lv, code_stats)
                        write_asm(move_instr(RDI_INDEX, lv, trip_ctx))
                    code_stats.fun_calls += 1
                    write_asm("call _printd")
                    for r in reversed(save_regs):
                        code_stats.mem_loads += 1
                        write_asm(f"pop {reg_str_for_size(r)}")
                case TripleType.NOP_USE:
                    pass
                case TripleType.NOP_REF:
                    assert t_reg is not None, "Expected this value to be assigned to a register"
                    if lv.typ != TripleValueType.REGISTER or lv.value != t_reg:
                        stat_move(lv, code_stats)
                        write_asm(move_instr(t_reg, lv, trip_ctx))
                case TripleType.FUN_ARG_IN:
                    pass
                case TripleType.CALL:
                    # TODO: Optimize saves/loads
                    assert lv is not None and lv.typ == TripleValueType.FUN_LABEL  
                    code_stats.fun_calls += 1                  
                    write_asm(f"call {triple_value_str(lv, trip_ctx)}")
                case TripleType.RETURN:
                    l_reg = trip_ctx.get_allocated_register(t.l_val, t.index)
                    if l_reg is None or l_reg != RAX_INDEX:
                        if t.l_val.typ == TripleValueType.CONSTANT and t.l_val.value == 0:
                            code_stats.basic_ops += 1
                            write_asm(f"xor rax, rax")
                        else:
                            stat_move(t.l_val, code_stats)
                            write_asm(move_instr(RAX_INDEX, t.l_val, trip_ctx))
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

def get_asm_footer(trip_ctx: TripleContext, called_funs: Set[str]):
    did_segment = False
    asm = ""

    all_buffers = dict(trip_ctx.buffers)
    all_strings = dict(trip_ctx.strings)
    all_global_vars = set(trip_ctx.declared_vars)
    for f in called_funs:
        c = trip_ctx.function_ctx[f]
        all_buffers.update(c.buffers)
        all_strings.update(c.strings)

    if len(all_global_vars) > 0:
        asm += "\n\tsegment .bss\n"
        did_segment = True
        for v in all_global_vars:
            asm += f"_{v}: resb 8\n"
    
    # if len(all_buffers) > 0:
    #     if not did_segment:
    #         asm += "\tsegment .bss\n"
    #         did_segment = True
    #     for b,sz in all_buffers.items():
    #         asm += f"{b}: resb {sz}\n"

    if len(all_strings) > 0:
        asm += "\tsegment .data\n"
        for s, labl in all_strings.items():
            asm += f"{labl}: db `{s.encode('unicode_escape').decode('utf-8')}`, 0\n"

    return asm