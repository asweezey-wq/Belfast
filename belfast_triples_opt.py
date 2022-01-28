from os import remove
from re import T
from tkinter import E
from belfast_triples import *
from typing import *
from math import log2

OPTIMIZATION_FLAGS = {
    'const-eval': True,
    'unused-code': True,
    'cmp-forward': True,
    'strength-reduce': True,
    'common-exp': True,
    'value-forwarding': True,
    'null-op': True,
    "loop-optimization": True,
    'value-simplification': True,
}

REMOVAL_HINTS = {}
ADD_HINTS = {}

# For common expressions
def triples_match(t1: Triple, t2: Triple):
    if t1.typ != t2.typ or ((t1.l_val is None) != (t2.l_val is None)) or ((t1.r_val is None) != (t2 is None)):
        return False
    is_reflexive = False
    match t1.typ:
        case TripleType.BINARY_OP:
            if t1.op != t2.op:
                return False
            is_reflexive = t1.op in [Operator.PLUS, Operator.MULTIPLY, Operator.EQ, Operator.NE, Operator.BITWISE_OR, Operator.BITWISE_AND, Operator.BITWISE_XOR]
        case TripleType.UNARY_OP:
            if t1.op != t2.op:
                return False
    return (t1.l_val is None or triple_values_equal(t1.l_val, t2.l_val) or (is_reflexive and triple_values_equal(t1.l_val, t2.r_val))) and (t1.r_val is None or triple_values_equal(t1.r_val, t2.r_val) or (is_reflexive and (triple_values_equal(t1.r_val, t2.l_val))))

def is_zero(tv: TripleValue):
    return tv.typ == TripleValueType.CONSTANT and tv.value == 0

def is_one(tv: TripleValue):
    return tv.typ == TripleValueType.CONSTANT and tv.value == 1

def null_operation_eval(trip: Triple):
    match trip.typ:
        case TripleType.BINARY_OP:
            lv = trip.l_val
            rv = trip.r_val
            match trip.op:
                case Operator.PLUS | Operator.BITWISE_OR | Operator.BITWISE_OR:
                    if is_zero(lv):
                        return rv
                    elif is_zero(rv):
                        return lv
                case Operator.MINUS:
                    if is_zero(rv):
                        return lv
                case Operator.MULTIPLY:
                    if is_zero(lv) or is_zero(rv):
                        return create_const_value(0)
                    elif is_one(lv):
                        return rv
                    elif is_one(rv):
                        return lv
                case Operator.DIVIDE | Operator.MODULUS:
                    if is_zero(rv):
                        compiler_error(trip.loc, "Division by zero")
                    elif is_one(rv):
                        return create_const_value(0) if trip.op == Operator.MODULUS else lv
                    elif is_zero(lv):
                        return create_const_value(0)
                case Operator.BITWISE_AND:
                    if is_zero(lv) or is_zero(rv):
                        return create_const_value(0)
                case Operator.SHIFT_LEFT | Operator.SHIFT_RIGHT:
                    if is_zero(lv):
                        return create_const_value(0)
                    elif is_zero(rv):
                        return lv
                case Operator.EQ:
                    if triple_values_equal(lv, rv):
                        return create_const_value(1)
                case Operator.NE:
                    if triple_values_equal(lv, rv):
                        return create_const_value(0)
    return None

def strength_reduce(triple: Triple):
    # TODO: Be able to change the number of triples (e.g. magic number division)
    match triple.typ:
        case TripleType.BINARY_OP:
            match triple.op:
                case Operator.MINUS:
                    if is_zero(triple.l_val):
                        triple.typ = TripleType.UNARY_OP
                        triple.op = Operator.NEGATE
                        triple.l_val = triple.r_val
                        triple.r_val = None
                        REMOVAL_HINTS[triple] = "Strength Reduce"
                        return True
                case Operator.MULTIPLY:
                    # TODO: This only works when the value is positive
                    if triple.r_val.typ == TripleValueType.CONSTANT:
                        if triple.r_val.value > 0:
                            l2 = log2(triple.r_val.value)
                            if l2 == int(l2):
                                triple.op = Operator.SHIFT_LEFT
                                triple.r_val = create_const_value(int(l2))
                                REMOVAL_HINTS[triple] = "Strength Reduce"
                                return True
                        elif triple.r_val.value == -1:
                            triple.typ = TripleType.UNARY_OP
                            triple.op = Operator.NEGATE
                            triple.r_val = None
                            REMOVAL_HINTS[triple] = "Strength Reduce"
                            return True
                    elif triple.l_val.typ == TripleValueType.CONSTANT:
                        if triple.l_val.value > 0:
                            l2 = log2(triple.l_val.value)
                            if l2 == int(l2):
                                triple.op = Operator.SHIFT_LEFT
                                triple.l_val = triple.r_val
                                triple.r_val = create_const_value(int(l2))
                                REMOVAL_HINTS[triple] = "Strength Reduce"
                                return True
                        elif triple.l_val.value == -1:
                            triple.typ = TripleType.UNARY_OP
                            triple.op = Operator.NEGATE
                            triple.l_val = triple.r_val
                            triple.r_val = None
                            REMOVAL_HINTS[triple] = "Strength Reduce"
                            return True
                case Operator.DIVIDE:
                    # TODO: This only works when the value is positive
                    if triple.r_val.typ == TripleValueType.CONSTANT:
                        l2 = log2(triple.r_val.value)
                        if l2 == int(l2):
                            triple.op = Operator.SHIFT_RIGHT
                            triple.r_val = create_const_value(int(l2))
                            REMOVAL_HINTS[triple] = "Strength Reduce"
                            return True
                case Operator.MODULUS:
                    if triple.r_val.typ == TripleValueType.CONSTANT:
                        l2 = log2(triple.r_val.value)
                        if l2 == int(l2):
                            triple.op = Operator.BITWISE_AND
                            triple.r_val = create_const_value(triple.r_val.value - 1)
                            REMOVAL_HINTS[triple] = "Strength Reduce"
                            return True

    return False
                    
def evaluate_triple_const(triple: Triple):
    match triple.typ:
        case TripleType.BINARY_OP:
            if triple.l_val.typ == TripleValueType.CONSTANT and triple.r_val.typ == TripleValueType.CONSTANT:
                n1 = triple.l_val.value
                n2 = triple.r_val.value
                match triple.op:
                    case Operator.PLUS:
                        return n1 + n2
                    case Operator.MINUS:
                        return n1 - n2
                    case Operator.MULTIPLY:
                        return n1 * n2
                    case Operator.DIVIDE:
                        return n1 // n2
                    case Operator.MODULUS:
                        return n1 % n2
                    case Operator.EQ:
                        return 1 if n1 == n2 else 0
                    case Operator.NE:
                        return 1 if n1 != n2 else 0
                    case Operator.GT:
                        return 1 if n1 > n2 else 0
                    case Operator.GE:
                        return 1 if n1 >= n2 else 0
                    case Operator.LT:
                        return 1 if n1 < n2 else 0
                    case Operator.LE:
                        return 1 if n1 <= n2 else 0
                    case Operator.SHIFT_RIGHT:
                        return n1 >> n2
                    case Operator.SHIFT_LEFT:
                        return n1 << n2
                    case Operator.BITWISE_XOR:
                        return n1 ^ n2
                    case Operator.BITWISE_AND:
                        return n1 & n2
                    case Operator.BITWISE_OR:
                        return n1 | n2
                    case _:
                        return None
        case TripleType.UNARY_OP:
            if triple.l_val.typ == TripleValueType.CONSTANT:
                n1 = triple.l_val.value
                match triple.op:
                    case Operator.NEGATE:
                        return -n1
                    case Operator.BITWISE_NOT:
                        return ~n1
                    case _:
                        return None
    return None

def const_eval_pass(triple_references: Dict[Triple, List[Triple]]):
    did_pass_evaluate = True
    did_modify = False
    while did_pass_evaluate:
        did_pass_evaluate = False
        for t,v in list(triple_references.items()):
            n = evaluate_triple_const(t)
            if n is not None:
                did_pass_evaluate = True
                for ref_t in v:
                    val: TripleValue = get_triple_reference_value(ref_t, t)
                    if val:
                        assert val.typ == TripleValueType.TRIPLE_REF
                        val.typ = TripleValueType.CONSTANT
                        val.value = n
                        ADD_HINTS[ref_t] = "Constant Propagation"
                        REMOVAL_HINTS[ref_t] = "Constant Propagation"
                if len(v) > 0:
                    did_modify = True
                del triple_references[t]

    return did_modify

def branch_const_eval_pass(triples: List[Triple], triple_references: Dict[Triple, List[Triple]]):
    items_to_remove = []
    for t in triples:
        if t.typ == TripleType.IF_COND and t.l_val.typ == TripleValueType.CONSTANT:
            n = t.l_val.value
            if t.op == Operator.NE:
                if n == 0:
                    t.typ = TripleType.GOTO
                    t.l_val = t.r_val
                    t.r_val = None
                    REMOVAL_HINTS[t] = "Branch constant eval"
                else:
                    items_to_remove.append(t)
            else:
                assert False, f"Unknown Operator {t.op.name}"
    for t in items_to_remove:
        triples.remove(t)
        REMOVAL_HINTS[t] = "Branch constant eval"
    return len(items_to_remove) > 0

def does_triple_modify_state(triple: Triple):
    return triple.typ != TripleType.BINARY_OP and triple.typ != TripleType.UNARY_OP and triple.typ != TripleType.NOP_REF

def remove_unused_triples(trips: List[Triple], triple_references: Dict[Triple, List[Triple]]):
    unused_triples = filter(lambda t: not does_triple_modify_state(t) and (t not in triple_references or len(triple_references[t]) == 0), trips)
    did_remove = False
    for t in unused_triples:
        trips.remove(t)
        REMOVAL_HINTS[t] = "Unused"
        did_remove = True
        if t in triple_references:
            del triple_references[t]
    return did_remove

def forward_labels(trips: List[Triple], label_references: Dict[Triple, List[Triple]]):
    did_forward = False
    for t in list(label_references.keys()):
        assert t.typ == TripleType.LABEL
        original_index = trips.index(t)
        assert original_index >= 0
        next_index = original_index
        while next_index < len(trips) - 1 and trips[next_index + 1].typ == TripleType.LABEL:
            next_index += 1
        if next_index > original_index:
            forwarded_label = trips[next_index]
            for ref_t in label_references[t]:
                ref_val: TripleValue = get_triple_label_reference_value(ref_t, t)
                assert ref_val is not None
                ref_val.value = forwarded_label
                ADD_HINTS[ref_t] = "Forwarded Label"
            del label_references[t]
            did_forward = True
    return did_forward

def remove_unused_labels(trips: List[Triple], label_references: Dict[Triple, List[Triple]]):
    unused_triples = filter(lambda t: t.typ == TripleType.LABEL and (t not in label_references or len(label_references[t]) == 0), trips)
    did_remove = False
    for t in unused_triples:
        trips.remove(t)
        REMOVAL_HINTS[t] = "Unused"
        did_remove = True
        if t in label_references:
            del label_references[t]
    return did_remove

def remove_unreachable_triples(trips: List[Triple]):
    is_unreachable = False
    trips_to_remove = []
    for i, t in enumerate(trips):
        if t.typ == TripleType.LABEL:
            is_unreachable = False
        elif is_unreachable:
            trips_to_remove.append(t)
        elif t.typ == TripleType.GOTO:
            is_unreachable = True
    
    for t in trips_to_remove:
        trips.remove(t)
        REMOVAL_HINTS[t] = "Unreachable"

    return len(trips_to_remove) > 0

def remove_pointless_goto(trips: List[Triple]):
    to_remove = []
    for i, t in enumerate(trips):
        if t.typ == TripleType.GOTO and i < len(trips) - 1:
            next_trip = trips[i + 1]
            assert t.l_val.typ == TripleValueType.TRIPLE_TARGET
            if t.l_val.value == next_trip:
                to_remove.append(t)
    for t in to_remove:
        trips.remove(t)
        REMOVAL_HINTS[t] = "Useless GOTO"
    return len(to_remove) > 0

def simplify_binops(trips: List[Triple], triple_references: Dict[Triple, List[Triple]]):
    to_remove = {}
    for t in trips:
        match t.typ:
            case TripleType.BINARY_OP:
                trefs = [v for v in (t.l_val, t.r_val) if v.typ == TripleValueType.TRIPLE_REF]
                consts = [v for v in (t.l_val, t.r_val) if v.typ == TripleValueType.CONSTANT]

                if len(trefs) == 1 and len(consts) == 1:
                    tref = trefs[0].value
                    if len(triple_references[tref]) == 1 and triple_references[tref][0] == t:
                        if tref.typ == TripleType.BINARY_OP:
                            tref_consts = [v for v in (tref.l_val, tref.r_val) if v.typ == TripleValueType.CONSTANT]
                            if len(tref_consts) == 1:
                                match t.op:
                                    case Operator.PLUS:
                                        if tref.op == Operator.PLUS:
                                            tref_consts[0].value += consts[0].value
                                            ADD_HINTS[tref] = "Merged operations"
                                            to_remove[t] = tref
                                        elif tref.op == Operator.MINUS:
                                            if tref_consts[0] == tref.r_val:
                                                tref_consts[0].value += consts[0].value
                                                ADD_HINTS[tref] = "Merged operations"
                                                to_remove[t] = tref
                                    case Operator.MINUS:
                                        if tref.op == Operator.PLUS:
                                            tref_consts[0].value -= consts[0].value
                                            ADD_HINTS[tref] = "Merged operations"
                                            to_remove[t] = tref
                                        elif tref.op == Operator.MINUS:
                                            if tref_consts[0] == tref.r_val:
                                                tref_consts[0].value -= consts[0].value
                                                ADD_HINTS[tref] = "Merged operations"
                                                to_remove[t] = tref
    
    for t,t2 in to_remove.items():
        for t1 in triple_references[t]:
            tv = get_triple_reference_value(t1, t)
            tv.value = t2
        trips.remove(t)
    
    return len(to_remove) > 0


@dataclass
class TripleBlock:
    index: int
    trips: List[Triple]
    in_blocks: List['TripleBlock']
    out_blocks: List['TripleBlock']
    vals_assigned: Dict[TripleValue, Triple]
    vals_used: Dict[TripleValue, Triple]
    in_vals: Set[TripleValue]
    out_vals: Set[TripleValue]

    def __hash__(self) -> int:
        return self.index

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, TripleBlock) and self.index == __o.index

    def __repr__(self) -> str:
        return f"Block {self.index}: {self.trips[0].index}-{self.trips[-1].index}"

def does_triple_produce_data(triple: Triple):
    return triple.typ in [TripleType.BINARY_OP, TripleType.UNARY_OP, TripleType.SYSCALL, TripleType.LOAD, TripleType.NOP_REF, TripleType.CALL]

def build_control_flow(trips: List[Triple], trip_ctx: TripleContext) -> List[TripleBlock]:
    label_references: Dict[Triple, List[Triple]] = {}
    for t in filter(lambda x: x.typ == TripleType.LABEL, trips):
        label_references[t] = list(filter(lambda x: get_triple_label_reference_value(x, t) is not None, trips))

    blocks: List[TripleBlock] = []
    control_flow_triples = []

    index = 0
    this_block = TripleBlock(index, [], [], [], {}, {}, set(), set())
    for t in trips:
        if t.typ == TripleType.LABEL:
            control_flow_triples.append(t)
            new_block = TripleBlock(index, [], [], [], {}, {}, set(), set())
            if len(this_block.trips) > 0:
                blocks.append(this_block)
                index += 1
                new_block.in_blocks.append(this_block)
                this_block.out_blocks.append(new_block)
                new_block.index = index
                this_block = new_block
            this_block.trips.append(t)
            continue
        elif t.typ == TripleType.GOTO:
            this_block.trips.append(t)
            control_flow_triples.append(t)
            if len(this_block.trips) > 0:
                blocks.append(this_block)
                index += 1
            this_block = TripleBlock(index, [], [], [], {}, {}, set(), set())
        elif t.typ == TripleType.IF_COND:
            this_block.trips.append(t)
            control_flow_triples.append(t)
            index += 1
            new_block = TripleBlock(index, [], [], [], {}, {}, set(), set())
            blocks.append(this_block)
            new_block.in_blocks.append(this_block)
            this_block.out_blocks.append(new_block)
            this_block = new_block
        else:
            this_block.trips.append(t)
    
    if len(this_block.trips) > 0:
        blocks.append(this_block)

    for b in blocks:
        for t in b.trips:
            if t.typ == TripleType.LABEL and t in label_references:
                for ref_t in label_references[t]:
                    ref_block = None
                    for b2 in blocks:
                        if ref_t in b2.trips:
                            ref_block = b2
                            break
                    assert ref_block is not None
                    if ref_block not in b.in_blocks:
                        b.in_blocks.append(ref_block)
                    if b not in ref_block.out_blocks:
                        ref_block.out_blocks.append(b)

    return blocks

def evaluate_block_value_usage(b: TripleBlock) -> Set[TripleValue]:
    vals_used : Set[TripleValue] = set()
    vals_assigned: Set[TripleValue] = set()
    for t in b.trips:
        if t.typ == TripleType.LABEL or t.typ == TripleType.GOTO:
            continue
        if does_triple_produce_data(t):
            t_ref = create_tref_value(t)
            b.vals_assigned[t_ref] = t
            vals_assigned.add(t_ref)
        if t.typ == TripleType.SYSCALL:
            for r in range(t.data):
                reg = ARG_REGISTERS[r]
                val = create_register_value(reg)
                vals_used.add(val)
                if val not in b.vals_assigned:
                    b.vals_used[val] = t
            rax_ref = create_register_value(RAX_INDEX)
            if not rax_ref in vals_used:
                b.vals_assigned[rax_ref] = t
            vals_assigned.add(rax_ref)
        elif t.typ == TripleType.FUN_ARG_IN:
            reg = ARG_REGISTERS[t.data]
            val = create_register_value(reg)
            vals_assigned.add(val)
            if val not in b.vals_assigned:
                b.vals_assigned[val] = t
            else:
                assert False
            assert t.l_val.typ == TripleValueType.VAR_ASSIGN
            var_val = create_var_ref_value(t.l_val.value)
            vals_assigned.add(var_val)
            if var_val not in b.vals_assigned:
                b.vals_assigned[var_val] = t

        vals_used_by_triple = get_triple_referenced_values(t)
        vals_used.update(vals_used_by_triple)
        for v in vals_used_by_triple:
            if v not in b.vals_assigned:
                b.vals_used[v] = t
        match t.typ:
            case TripleType.ASSIGN:
                assert t.l_val.typ == TripleValueType.VAR_ASSIGN
                var_ref = create_var_ref_value(t.l_val.value)
                if not var_ref in vals_used:
                    # if var_ref in b.vals_assigned:
                    #     # If there was a previous assignment before use, remove this
                    #     b.vals_assigned[var_ref].flags |= TF_REMOVE
                    b.vals_assigned[var_ref] = t
                vals_assigned.add(var_ref)
            case TripleType.REGMOVE:
                assert t.l_val.typ == TripleValueType.REGISTER
                if not t.l_val in vals_used:
                    b.vals_assigned[t.l_val] = t
                vals_assigned.add(t.l_val)
    return vals_used.union(vals_assigned)

def propagate_block_values(blocks: List[TripleBlock]):
    changed = True
    while changed:
        changed = False
        for b in blocks:
            in1 = set(b.in_vals)
            out1 = set(b.out_vals)
            b.in_vals = set(b.vals_used).union(b.out_vals.difference(b.vals_assigned.keys()))
            b.out_vals = set()
            for b2 in b.out_blocks:
                b.out_vals = b.out_vals.union(b2.in_vals)
            if in1 != b.in_vals or out1 != b.out_vals:
                changed = True

def annotate_triples(trips: List[Triple], trip_ctx: TripleContext):
    triple_references, var_references, var_assignments = get_reference_data(trips, trip_ctx)
    for i, t in enumerate(trips):
        if t.typ == TripleType.IF_COND and i > 0:
            cond_val: TripleValue = t.l_val
            if cond_val.typ == TripleValueType.TRIPLE_REF and cond_val.value == trips[i - 1]:
                if cond_val.value.typ == TripleType.BINARY_OP and cond_val.value.op in CMP_OP_INSTR_MAP:
                    # If the condition for this branch is the preceding triple
                    if OPTIMIZATION_FLAGS["cmp-forward"]:
                        trips[i - 1].flags |= TF_BOOL_FORWARDED
        if t.typ == TripleType.FUN_ARG_IN or t.typ == TripleType.SYSCALL:
            continue

def get_reference_data(trips: List[Triple], trip_ctx: TripleContext):
    triple_references: Dict[Triple, List[Triple]] = {}
    for t in trips:
        if t.typ == TripleType.LABEL:
            continue
        triple_references[t] = list(filter(lambda x: triple_references_triple(x, t), trips))
    var_references: Dict[str, List[Triple]] = {}
    for v in trip_ctx.declared_vars:
        var_references[v] = list(filter(lambda x: triple_references_var(x, v), trips))
    var_assignments: Dict[str, List[Triple]] = {}
    for v in trip_ctx.declared_vars:
        var_assignments[v] = list(filter(lambda x: triple_assigns_var(x, v), trips))
    return triple_references, var_references, var_assignments

from belfast_variable_analysis import identify_loops

def create_dominance_map(blocks: List[TripleBlock]) -> Dict[Triple, Optional[Triple]]:
    dom_map: Dict[Triple, Triple] = {}
    block_queue = [blocks[0]]
    block_visit = {}
    while len(block_queue) > 0:
        b = block_queue.pop(0)
        block_visit[b.index] = set([b.index])
        for in_b in b.in_blocks:
            if in_b.index in block_visit:
                block_visit[b.index].update(block_visit[in_b.index])
        for i,t in enumerate(b.trips):
            if i == 0:
                if len(b.in_blocks) == 0:
                    dom_map[t] = None
                else:
                    temp = None
                    for in_b in b.in_blocks:
                        if in_b.index not in block_visit:
                            continue
                        if temp is None:
                            temp = block_visit[in_b.index]
                        else:
                            temp = temp.intersection(block_visit[in_b.index])
                    min_block = blocks[min(temp)]
                    dom_map[t] = min_block.trips[-1]
            else:
                dom_map[t] = b.trips[i - 1]
        for o_b in b.out_blocks:
            if o_b.index not in block_visit and o_b not in block_queue:
                block_queue.append(o_b)
    return dom_map

def block_analysis(trips: List[Triple], trip_ctx: TripleContext):
    blocks = build_control_flow(trips, trip_ctx)
    if len(blocks) == 0:
        return False
    for b in blocks:
        evaluate_block_value_usage(b)
    propagate_block_values(blocks)
    
    dominance_map: Dict[Triple, Triple] = create_dominance_map(blocks)

    def does_triple_dominate(dom_trip: Triple, sub_trip: Triple):
        assert dom_trip in dominance_map
        dt = dominance_map[sub_trip]
        while dt is not None:
            if dt == dom_trip:
                return True
            dt = dominance_map[dt]
        return False

    def find_last_dominating_assign(start_trip: Triple, var: str):
        t = dominance_map[start_trip]
        while t is not None:
            if t.typ == TripleType.ASSIGN and t.l_val.value == var:
                return t
            t = dominance_map[t]
        return None

    def find_assign_between(start: Triple, end: Triple, var: str):
        for i in range(trips.index(start) + 1, trips.index(end)):
            t = trips[i]
            if t.typ == TripleType.ASSIGN and t.l_val.value == var:
                return t
        return None

    did_change = False

    for b in blocks:
        for i,t in enumerate(b.trips):
            if OPTIMIZATION_FLAGS['value-forwarding']:
                if t.l_val is not None and t.l_val.typ == TripleValueType.VAR_REF:
                    assign_trip = find_last_dominating_assign(t, t.l_val.value)
                    if assign_trip and assign_trip.r_val.typ in [TripleValueType.CONSTANT, TripleValueType.VAR_REF]:
                        if assign_trip in b.trips or (len(b.in_blocks) == 1 and assign_trip in b.in_blocks[0].trips):
                            if find_assign_between(assign_trip, t, t.l_val.value) is None:
                                if assign_trip.r_val.typ == TripleValueType.CONSTANT or find_assign_between(assign_trip, t, assign_trip.r_val.value) is None:
                                    t.l_val = assign_trip.r_val
                                    REMOVAL_HINTS[t] = "Value forwarded"
                                    ADD_HINTS[t] = "Value forwarded"
                                    did_change = True
                if t.r_val is not None and t.r_val.typ == TripleValueType.VAR_REF:
                    assign_trip = find_last_dominating_assign(t, t.r_val.value)
                    if assign_trip and assign_trip.r_val.typ in [TripleValueType.CONSTANT, TripleValueType.VAR_REF]:
                        if assign_trip in b.trips or (len(b.in_blocks) == 1 and assign_trip in b.in_blocks[0].trips):
                            if find_assign_between(assign_trip, t, t.r_val.value) is None:
                                if assign_trip.r_val.typ == TripleValueType.CONSTANT or find_assign_between(assign_trip, t, assign_trip.r_val.value) is None:
                                    t.r_val = assign_trip.r_val
                                    REMOVAL_HINTS[t] = "Value forwarded"
                                    ADD_HINTS[t] = "Value forwarded"
                                    did_change = True
            if t.typ == TripleType.ASSIGN and OPTIMIZATION_FLAGS['unused-code']:
                assert t.l_val.typ == TripleValueType.VAR_ASSIGN
                variable = t.l_val.value
                var_ref = create_var_ref_value(variable)
                if var_ref in b.vals_assigned and b.vals_assigned[var_ref] != t:
                    trips.remove(t)
                    REMOVAL_HINTS[t] = "Assignment without use"
                    did_change = True
                elif var_ref not in b.out_vals and all([not triple_references_var(t1, variable) for t1 in b.trips[i + 1:]]):
                    trips.remove(t)
                    REMOVAL_HINTS[t] = "Assignment without use"
                    did_change = True
            if OPTIMIZATION_FLAGS['common-exp']:
                # TODO: create a table for faster common exp lookups
                lv = t.l_val
                rv = t.r_val
                lref = lv.value if lv and lv.typ == TripleValueType.TRIPLE_REF else None
                rref = rv.value if rv and rv.typ == TripleValueType.TRIPLE_REF else None
                def common_exp_match(tref: Triple, tv: TripleValue):
                    nonlocal did_change
                    if not does_triple_modify_state(tref):
                        ld = dominance_map[tref]
                        last_match = None
                        while ld is not None:
                            if triples_match(tref, ld):
                                # triple matched
                                last_match = ld
                            ld = dominance_map[ld]
                        if last_match is not None:
                            has_changed = False
                            if last_match.l_val and last_match.l_val.typ == TripleValueType.VAR_REF:
                                if find_assign_between(last_match, tref, last_match.l_val.value) is not None:
                                    has_changed = True
                            if last_match.r_val and last_match.r_val.typ == TripleValueType.VAR_REF:
                                if find_assign_between(last_match, tref, last_match.r_val.value) is not None:
                                    has_changed = True
                            if not has_changed:
                                tv.value = last_match
                                REMOVAL_HINTS[t] = "Common expression"
                                did_change = True
                if lref is not None:
                    common_exp_match(lref, lv)
                if rref is not None:
                    common_exp_match(rref, rv)
    
    if not did_change:
        if OPTIMIZATION_FLAGS["loop-optimization"]:
            did_change |= identify_loops(trips, blocks)
        
    return did_change

def output_triple_delta_to_file(d, filename):
    with open(filename, 'a') as f:
        at, rt = d
        ri = 0
        ai = 0
        rt = sorted(rt, key=lambda x: x.index)
        at = sorted(at, key=lambda x: x.index)
        while ri < len(rt) or ai < len(at):
            if ri >= len(rt) or (ai < len(at) and at[ai].index < rt[ri].index):
                f.write(f" + {print_triple(at[ai])}")
                if at[ai] in ADD_HINTS:
                    f.write(f" ({ADD_HINTS[at[ai]]})")
                f.write("\n")
                ai += 1
            else:
                f.write(f" - {print_triple(rt[ri])}")
                if rt[ri] in REMOVAL_HINTS:
                    f.write(f" ({REMOVAL_HINTS[rt[ri]]})")
                f.write("\n")
                ri += 1
        f.write("\n")
                

def shallowcopy_trips(trips: List[Triple], triple_references, label_references):
    def shallowcopy_triple(t: Triple):
        new_t = Triple(t.typ, t.op, None, None, t.index, flags=t.flags, data=t.data, size=t.size)
        if t.l_val:
            new_t.l_val = TripleValue(t.l_val.typ, t.l_val.value)
        if t.r_val:
            new_t.r_val = TripleValue(t.r_val.typ, t.r_val.value)
        return new_t
    
    return [shallowcopy_triple(t) for t in trips]

def get_triple_delta(old_trips: List[Triple], new_trips: List[Triple]):
    removed_triples = []
    changed_triples = []
    added_triples = []

    def shallow_trips_equal(t1, t2):
        if t1.typ != t2.typ or t1.op != t2.op:
            return False
        if (t1.l_val is not None) != (t2.l_val is not None) or (t1.r_val is not None) != (t2.r_val is not None):
            return False
        if t1.l_val is not None and (t1.l_val.typ != t2.l_val.typ or t1.l_val.value != t2.l_val.value):
            return False
        if t1.r_val is not None and (t1.r_val.typ != t2.r_val.typ or t1.r_val.value != t2.r_val.value):
            return False
        return True

    C = {}
    for i in range(len(old_trips)+1):
        C[(i,0)] = 0
    for j in range(len(new_trips)+1):
        C[(0,j)] = 0
    for i in range(1, len(old_trips)+1):
        for j in range(1, len(new_trips)+1):
            old_t = old_trips[i-1]
            new_t = new_trips[j-1]
            if shallow_trips_equal(old_t, new_t):
                C[(i, j)] = C[(i - 1, j - 1)] + 1
            else:
                C[(i, j)] = max(C[(i, j - 1)], C[(i - 1, j)])

    def print_diff(i, j):

        if i >= 0 and j >= 0 and shallow_trips_equal(old_trips[i-1], new_trips[j-1]):
            print_diff(i - 1, j - 1)
        elif j > 0 and (i == 0 or C[(i, j - 1)] >= C[(i-1, j)]):
            added_triples.append(new_trips[j-1])
            print_diff(i, j - 1)
        elif i > 0 and (j == 0 or C[(i, j - 1)] < C[(i-1, j)]):
            removed_triples.append(old_trips[i-1])
            print_diff(i - 1, j)
        else:
            pass

    print_diff(len(old_trips), len(new_trips))

    return added_triples, removed_triples

def optimize_triples(trips: List[Triple], trip_ctx: TripleContext):
    did_modify = True

    orig_len = len(trips)

    prev_trips: List[Triple] = None

    with open(f"./tripstr/{trip_ctx.ctx_name}_tripopt.tripstr", 'w') as f:
        for t in trips:
            f.write(f"{print_triple(t)}\n")
        f.write("\n")

    while did_modify:
        did_modify = False
        index_triples(trips)
        triple_references, var_references, var_assignments = get_reference_data(trips, trip_ctx)
        label_references: Dict[Triple, List[Triple]] = {}
        for t in filter(lambda x: x.typ == TripleType.LABEL, trips):
            label_references[t] = list(filter(lambda x: get_triple_label_reference_value(x, t) is not None, trips))
        if prev_trips is not None:
            d = get_triple_delta(prev_trips, trips)
            output_triple_delta_to_file(d, f"./tripstr/{trip_ctx.ctx_name}_tripopt.tripstr")
            with open(f"./tripstr/{trip_ctx.ctx_name}_tripopt.tripstr", 'a') as f:
                for t in trips:
                    f.write(f"{print_triple(t)}\n")
                f.write("\n")

        REMOVAL_HINTS.clear()
        ADD_HINTS.clear()
        prev_trips = shallowcopy_trips(trips, triple_references, label_references)
        # for v in trip_ctx.declared_vars:
        #     print(f'Var "{v}":')
        #     print('References:')
        #     print('\n'.join([f"\t{print_triple(t)}" for t in var_references[v]]))
        #     print('Assignments:')
        #     print('\n'.join([f"\t{print_triple(t)}" for t in var_assignments[v]]))

        if OPTIMIZATION_FLAGS["const-eval"]:
            did_modify |= const_eval_pass(triple_references)
            did_modify |= branch_const_eval_pass(trips, triple_references)
        
        if OPTIMIZATION_FLAGS["value-simplification"]:
            did_modify |= simplify_binops(trips, triple_references)

        if OPTIMIZATION_FLAGS["unused-code"]:
            did_modify |= remove_unused_triples(trips, triple_references)
            did_modify |= remove_unreachable_triples(trips)

        if OPTIMIZATION_FLAGS['null-op']:
            for t in trips:
                new_v = null_operation_eval(t)
                if new_v is not None:
                    for ref_t in triple_references[t]:
                        val: TripleValue = get_triple_reference_value(ref_t, t)
                        if val == ref_t.l_val:
                            ref_t.l_val = new_v
                        elif val == ref_t.r_val:
                            ref_t.r_val = new_v
                    trips.remove(t)
                    REMOVAL_HINTS[t] = "Null-Op"
                    did_modify = True
                

        if OPTIMIZATION_FLAGS['strength-reduce']:
            did_pass_evaluate = True
            while did_pass_evaluate:
                did_pass_evaluate = False
                for t in trips:
                    did_modify |= strength_reduce(t)

        did_modify |= remove_pointless_goto(trips)

        label_references = {}
        for t in filter(lambda x: x.typ == TripleType.LABEL, trips):
            label_references[t] = list(filter(lambda x: get_triple_label_reference_value(x, t) is not None, trips))

        did_modify |= forward_labels(trips, label_references)
        did_modify |= remove_unused_labels(trips, label_references)

        if not did_modify:
            did_modify |= block_analysis(trips, trip_ctx)

    # print(f"\nOptimization removed {orig_len - len(trips)} triples")

    return trips
