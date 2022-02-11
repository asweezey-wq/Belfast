from copy import copy
import belfast_data
from belfast_triples import *
from typing import *
from math import log2
import os

from belfast_variable_analysis import identify_loops, optimize_loop

OPTIMIZATION_FLAGS_DEFAULTS = {
    'const-eval': True,
    'unused-code': True,
    'cmp-forward': True,
    'strength-reduce': True,
    'common-exp': True,
    'value-forwarding': True,
    'null-op': True,
    "loop-optimization": True,
    'value-simplification': True,
    'code-hoisting': True,
    "code-motion": True,
    "linear-combinations": True,
}

OPTIMIZATION_FLAGS = dict(OPTIMIZATION_FLAGS_DEFAULTS)

def set_opt_flags(f: dict):
    global OPTIMIZATION_FLAGS
    OPTIMIZATION_FLAGS = f


class OptimizationContext:

    def __init__(self, trips) -> None:
        self.trips = trips
        self.triple_references = None
        self.label_references = None
        self.blocks = None
        self.dominance_map = {}
        self.triples_dirty = False
        self.block_dominance_map = {}
        self.loops = {} # Map loop headers to loop tail
        self.loop_prio = {} # Map loop headers to priority -- higher priority to inner loops
        self.block_visit_in = {}
        self.block_visit_out = {}
    
    def recalculate_blocks(self):
        self.blocks = build_control_flow(self.trips)
        for b in self.blocks:
            evaluate_block_value_usage(b)
        propagate_block_values(self.blocks)
        calc_block_dominance(self)
        self.dominance_map = create_dominance_map(self.blocks)

    def evaluate_triple_references(self):
        self.triple_references = get_reference_data(self.trips)
    
    def evaluate_label_references(self):
        self.label_references = {}
        for t in filter(lambda x: x.typ == TripleType.LABEL, self.trips):
            self.label_references[t] = list(filter(lambda x: get_triple_label_reference_value(x, t) is not None, self.trips))

    def retarget_triple_references(self, t: Triple, new_tv: TripleValue, change_hint=None):
        cnt = len(self.triple_references[t])
        for ref_t in self.triple_references[t]:
            val = get_triple_reference_value(ref_t, t)
            if val:
                if val == ref_t.l_val:
                    ref_t.l_val = copy(new_tv)
                elif val == ref_t.r_val:
                    ref_t.r_val = copy(new_tv)
                else:
                    assert False
                if change_hint:
                    CHANGE_HINTS[ref_t] = change_hint
        del self.triple_references[t]
        self.triples_dirty = True
        return cnt

    def retarget_label_references(self, t: Triple, new_triple: Triple, change_hint=None):
        cnt = len(self.label_references[t])
        for ref_t in self.label_references[t]:
            val = get_triple_label_reference_value(ref_t, t)
            val.value = new_triple
            if change_hint:
                CHANGE_HINTS[ref_t] = change_hint
        del self.label_references[t]
        self.triples_dirty = True
        return cnt

    def get_unused_triples(self):
        unused_triples = filter(lambda t: not does_triple_modify_state(t) and (t not in self.triple_references or len(self.triple_references[t]) == 0), self.trips)
        return unused_triples

    def get_unused_labels(self):
        unused_triples = filter(lambda t: t.typ == TripleType.LABEL and (t not in self.label_references or len(self.label_references[t]) == 0), self.trips)
        return unused_triples

    def remove_triple(self, t: Triple, change_hint=None):
        if t.l_val and t.l_val.typ == TripleValueType.TRIPLE_REF and t.l_val.value in self.triple_references:
            self.triple_references[t.l_val.value].remove(t)
        if t.r_val and t.r_val.typ == TripleValueType.TRIPLE_REF and t.r_val.value in self.triple_references:
            self.triple_references[t.r_val.value].remove(t)
        if t in self.triple_references:
            del self.triple_references[t]
        if t.l_val and t.l_val.typ == TripleValueType.TRIPLE_TARGET and t.l_val.value in self.label_references and t in self.label_references[t.l_val.value]:
            self.label_references[t.l_val.value].remove(t)
        if t.r_val and t.r_val.typ == TripleValueType.TRIPLE_TARGET and t.r_val.value in self.label_references and t in self.label_references[t.r_val.value]:
            self.label_references[t.r_val.value].remove(t)
        if t in self.label_references:
            del self.label_references[t]
        self.trips.remove(t)
        self.triples_dirty = True
        if change_hint:
            CHANGE_HINTS[t] = change_hint

    def insert_triple(self, idx: int, t: Triple, change_hint=None):
        if t.l_val and t.l_val.typ == TripleValueType.TRIPLE_REF and t.l_val.value in self.triple_references:
            self.triple_references[t.l_val.value].append(t)
        if t.r_val and t.r_val.typ == TripleValueType.TRIPLE_REF and t.r_val.value in self.triple_references:
            self.triple_references[t.r_val.value].append(t)
        if t.l_val and t.l_val.typ == TripleValueType.TRIPLE_TARGET and t.l_val.value in self.label_references:
            self.label_references[t.l_val.value].append(t)
        if t.r_val and t.r_val.typ == TripleValueType.TRIPLE_TARGET and t.r_val.value in self.label_references:
            self.label_references[t.r_val.value].append(t)
        self.trips.insert(idx, t)
        self.triples_dirty = True
        if change_hint:
            CHANGE_HINTS[t] = change_hint

    def replace_triple(self, old_t: Triple, new_t: Triple, change_hint=None):
        idx = self.trips.index(old_t)
        self.remove_triple(old_t, change_hint)
        self.insert_triple(idx, new_t, change_hint)

    def move_triple(self, t: Triple, new_ind: int, change_hint=None):
        self.trips.remove(t)
        self.trips.insert(new_ind - 1, t)
        if change_hint:
            CHANGE_HINTS[t] = change_hint
        self.triples_dirty = True

    def does_triple_dominate(self, dom_trip: Triple, sub_trip: Triple):
        if dom_trip not in self.dominance_map:
            return False
        dt = self.dominance_map[sub_trip]
        while dt is not None:
            if dt == dom_trip:
                return True
            dt = self.dominance_map[dt]
        return False

    def find_last_dominating_assign(self, start_trip: Triple, var:str):
        t = self.dominance_map[start_trip]
        while t is not None:
            if t.typ == TripleType.ASSIGN and t.l_val.value == var:
                return t
            t = self.dominance_map[t]
        return None

    def find_assign_between(self, start: Triple, end: Triple, var: str):
        for i in range(self.trips.index(start) + 1, self.trips.index(end)):
            t = self.trips[i]
            if t.typ == TripleType.ASSIGN and t.l_val.value == var:
                return t
        return None

    def common_exp_match(self, tref: Triple):
        ld = self.dominance_map[tref]
        last_match = None
        while ld is not None:
            if triples_match(tref, ld):
                last_match = ld
            ld = self.dominance_map[ld]
        if last_match is not None:
            has_changed = False
            if last_match.l_val:
                if last_match.l_val.typ == TripleValueType.VAR_REF:
                    if self.find_assign_between(last_match, tref, last_match.l_val.value) is not None:
                        has_changed = True
                elif last_match.l_val.typ in [TripleValueType.GLOBAL_REF,]:
                    has_changed = True
            if last_match.r_val:
                if last_match.r_val.typ == TripleValueType.VAR_REF:
                    if self.find_assign_between(last_match, tref, last_match.r_val.value) is not None:
                        has_changed = True
                elif last_match.r_val.typ in [TripleValueType.GLOBAL_REF,]:
                    has_changed = True
                
            if not has_changed:
                return last_match
        return None

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
                        CHANGE_HINTS[triple] = "Strength Reduce"
                        return True
                case Operator.MULTIPLY:
                    # TODO: This only works when the value is positive
                    if triple.r_val.typ == TripleValueType.CONSTANT:
                        if triple.r_val.value > 0:
                            l2 = log2(triple.r_val.value)
                            if l2 == int(l2):
                                triple.op = Operator.SHIFT_LEFT
                                triple.flags |= TF_SIGNED
                                triple.r_val = create_const_value(int(l2))
                                CHANGE_HINTS[triple] = "Strength Reduce"
                                return True
                        elif triple.r_val.value == -1:
                            triple.typ = TripleType.UNARY_OP
                            triple.op = Operator.NEGATE
                            triple.r_val = None
                            CHANGE_HINTS[triple] = "Strength Reduce"
                            return True
                    elif triple.l_val.typ == TripleValueType.CONSTANT:
                        if triple.l_val.value > 0:
                            l2 = log2(triple.l_val.value)
                            if l2 == int(l2):
                                triple.op = Operator.SHIFT_LEFT
                                triple.flags |= TF_SIGNED
                                triple.l_val = triple.r_val
                                triple.r_val = create_const_value(int(l2))
                                CHANGE_HINTS[triple] = "Strength Reduce"
                                return True
                        elif triple.l_val.value == -1:
                            triple.typ = TripleType.UNARY_OP
                            triple.op = Operator.NEGATE
                            triple.l_val = triple.r_val
                            triple.r_val = None
                            CHANGE_HINTS[triple] = "Strength Reduce"
                            return True
                case Operator.DIVIDE:
                    # TODO: This only works when the value is positive
                    if triple.r_val.typ == TripleValueType.CONSTANT:
                        l2 = log2(triple.r_val.value)
                        if l2 == int(l2):
                            triple.op = Operator.SHIFT_RIGHT
                            triple.flags |= TF_SIGNED
                            triple.r_val = create_const_value(int(l2))
                            CHANGE_HINTS[triple] = "Strength Reduce"
                            return True
                case Operator.MODULUS:
                    if triple.r_val.typ == TripleValueType.CONSTANT:
                        l2 = log2(triple.r_val.value)
                        if l2 == int(l2):
                            triple.op = Operator.BITWISE_AND
                            triple.r_val = create_const_value(triple.r_val.value - 1)
                            CHANGE_HINTS[triple] = "Strength Reduce"
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
                        return int(n1 / n2)
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

def does_triple_modify_state(triple: Triple):
    return triple.typ != TripleType.BINARY_OP and triple.typ != TripleType.UNARY_OP and triple.typ != TripleType.NOP_REF

def remove_unused_triples(opt_ctx: OptimizationContext):
    unused_triples = opt_ctx.get_unused_triples()
    did_change = False
    for t in unused_triples:
        did_change = True
        opt_ctx.remove_triple(t, "Unused")

    return did_change

def forward_labels(opt_ctx: OptimizationContext):
    did_forward = False
    for t in list(opt_ctx.label_references.keys()):
        assert t.typ == TripleType.LABEL
        original_index = opt_ctx.trips.index(t)
        assert original_index >= 0
        next_index = original_index
        while next_index < len(opt_ctx.trips) - 1 and opt_ctx.trips[next_index + 1].typ == TripleType.LABEL:
            next_index += 1
        if next_index > original_index:
            forwarded_label = opt_ctx.trips[next_index]
            opt_ctx.retarget_label_references(t, forwarded_label, "Forwarded Label")
            did_forward = True
    return did_forward

def remove_unused_labels(opt_ctx: OptimizationContext):
    unused_triples = opt_ctx.get_unused_labels()
    did_change = False
    for t in unused_triples:
        did_change = True
        opt_ctx.remove_triple(t, "Unused")
    return did_change

def remove_unreachable_triples(opt_ctx: OptimizationContext):
    # TODO: Can this be moved to the block phase?
    is_unreachable = False
    trips_to_remove = []
    for t in opt_ctx.trips:
        if t.typ == TripleType.LABEL:
            is_unreachable = False
        elif is_unreachable:
            trips_to_remove.append(t)
        elif t.typ == TripleType.GOTO:
            is_unreachable = True
    
    for t in trips_to_remove:
        opt_ctx.remove_triple(t, "Unreachable")

    return len(trips_to_remove) > 0

def remove_pointless_goto(opt_ctx: OptimizationContext):
    to_remove = []
    for i, t in enumerate(opt_ctx.trips):
        if t.typ == TripleType.GOTO and i < len(opt_ctx.trips) - 1:
            next_trip = opt_ctx.trips[i + 1]
            assert t.l_val.typ == TripleValueType.TRIPLE_TARGET
            if t.l_val.value == next_trip:
                to_remove.append(t)
    for t in to_remove:
        opt_ctx.remove_triple(t, "Useless GOTO")
    return len(to_remove) > 0

def simplify_binops(opt_ctx: OptimizationContext):
    to_remove = {}
    for t in opt_ctx.trips:
        match t.typ:
            case TripleType.BINARY_OP:
                trefs = [v for v in (t.l_val, t.r_val) if v.typ == TripleValueType.TRIPLE_REF]
                consts = [v for v in (t.l_val, t.r_val) if v.typ == TripleValueType.CONSTANT]

                if len(trefs) == 1 and len(consts) == 1:
                    tref = trefs[0].value
                    if len(opt_ctx.triple_references[tref]) == 1 and opt_ctx.triple_references[tref][0] == t:
                        if tref.typ == TripleType.BINARY_OP:
                            tref_consts = [v for v in (tref.l_val, tref.r_val) if v.typ == TripleValueType.CONSTANT]
                            if len(tref_consts) == 1:
                                match t.op:
                                    case Operator.PLUS:
                                        if tref.op == Operator.PLUS:
                                            tref_consts[0].value += consts[0].value
                                            CHANGE_HINTS[tref] = "Merged operations"
                                            to_remove[t] = tref
                                        elif tref.op == Operator.MINUS:
                                            if tref_consts[0] == tref.r_val:
                                                tref_consts[0].value += consts[0].value
                                                CHANGE_HINTS[tref] = "Merged operations"
                                                to_remove[t] = tref
                                    case Operator.MINUS:
                                        if tref.op == Operator.PLUS:
                                            tref_consts[0].value -= consts[0].value
                                            CHANGE_HINTS[tref] = "Merged operations"
                                            to_remove[t] = tref
                                        elif tref.op == Operator.MINUS:
                                            if tref_consts[0] == tref.r_val:
                                                tref_consts[0].value -= consts[0].value
                                                CHANGE_HINTS[tref] = "Merged operations"
                                                to_remove[t] = tref
    
    for t,t2 in to_remove.items():
        for t1 in opt_ctx.triple_references[t]:
            tv = get_triple_reference_value(t1, t)
            tv.value = t2
            CHANGE_HINTS[t1] = "Retarged to merge operation"
        opt_ctx.remove_triple(t, "Merged Operations")
    
    return len(to_remove) > 0

def does_triple_produce_data(triple: Triple):
    return triple.typ in [TripleType.BINARY_OP, TripleType.UNARY_OP, TripleType.SYSCALL, TripleType.LOAD, TripleType.NOP_REF, TripleType.CALL]

def build_control_flow(trips: List[Triple]) -> List[TripleBlock]:
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

def calc_block_dominance(opt_ctx: OptimizationContext):
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

    opt_ctx.block_dominance_map = dom_map
    opt_ctx.block_visit_in = block_visit

def does_triple_kill_expression(t: Triple, exp: Expression):
    d = get_defines(t)
    return exp.l_val in d or exp.r_val in d

def does_triple_use_expression(t: Triple, exp: Expression):
    u = get_uses(t)
    return any([i.typ == TripleValueType.TRIPLE_REF and triple_matches_exp(i.value, exp) for i in u])

def triple_uses_expressions(t: Triple):
    exp = []
    if t.l_val and t.l_val.typ == TripleValueType.TRIPLE_REF and t.l_val.value.typ == TripleType.BINARY_OP:
        exp.append(triple_to_exp(t.l_val.value))
    if t.r_val and t.r_val.typ == TripleValueType.TRIPLE_REF and t.r_val.value.typ == TripleType.BINARY_OP:
        exp.append(triple_to_exp(t.r_val.value))
    return exp

def triple_generates_expressions(t: Triple):
    if t.typ == TripleType.BINARY_OP:
        return [triple_to_exp(t)]
    return []

def expression_analysis(opt_ctx: OptimizationContext):
    # Code hoisting
    blocks = opt_ctx.blocks

    temp_blocks = []
    # Transform blocks
    for b in list(blocks):
        if len(b.out_blocks) == 2:
            new_b = TripleBlock(len(blocks), [b.trips[-1]], [], [], {}, {}, b.in_vals, b.out_vals)
            new_b.out_blocks = b.out_blocks
            b.out_blocks = [new_b]
            for child in new_b.out_blocks:
                child.in_blocks.remove(b)
                child.in_blocks.append(new_b)
            new_b.in_blocks = [b]
            b.trips.pop(-1)
            blocks.insert(blocks.index(b) + 1, new_b)
            temp_blocks.append(new_b)

    anticipated = {}
    block_kills = {}
    block_gens = {}

    changed = True
    while changed:
        changed = False
        for b in reversed(blocks):
            orig = set(anticipated[b]) if b in anticipated else None
            in_next = set()
            if len(b.out_blocks) > 0:
                in_next = None
                for ob in b.out_blocks:
                    if ob in anticipated and blocks.index(ob) > blocks.index(b):
                        in_next = in_next.intersection(anticipated[ob]) if in_next else anticipated[ob]
                if not in_next:
                    in_next = set()
            used = {}
            killed_e = set()
            block_kills[b] = set()
            for i,t in enumerate(b.trips):
                el = triple_uses_expressions(t)
                for e in el:
                    if e not in used:
                        used[e] = i
            for i,t in enumerate(b.trips):
                for e in in_next:
                    if does_triple_kill_expression(t, e):
                        killed_e.add(e)
                k = []
                for e,j in used.items():
                    if i < j and does_triple_kill_expression(t, e):
                        k.append(e)
                        block_kills[b].add(e)
                for e in k:
                    del used[e]
            block_kills[b].update(killed_e)
            anticipated[b] = in_next.difference(killed_e).union(used.keys())
            if orig is None or anticipated[b] != orig:
                changed = True

    available_in = {}
    available_out = {}

    changed = True
    while changed:
        changed = False
        for b in blocks:
            orig = set(available_out[b]) if b in available_out else None
            in_exps = set()
            if len(b.in_blocks) > 0:
                in_exps = None
                for ib in b.in_blocks:
                    if ib in available_out:
                        in_exps = in_exps.intersection(available_out[ib]) if in_exps else available_out[ib]
                if not in_exps:
                    in_exps = set()
            available_in[b] = in_exps
            varkill = set()
            dexpr = set()
            for t in reversed(b.trips):
                if t.typ == TripleType.ASSIGN:
                    varkill.add(create_var_ref_value(t.l_val.value))
                elif t.typ == TripleType.BINARY_OP:
                    e = triple_to_exp(t)
                    if e.l_val not in varkill and e.r_val not in varkill:
                        dexpr.add(e)
            ekill = set()
            for e in dexpr:
                if e.l_val in varkill or e.r_val in varkill:
                    ekill.add(e)
            block_gens[b] = dexpr
            available_out[b] = dexpr.union(in_exps.difference(ekill))
            if orig is None or orig != available_out[b]:
                changed = True

    for b in blocks:
        b.available_exp_in = available_in[b]
        b.available_exp_out = available_out[b]

    hoist = {}

    for b in blocks:
        pre_hoist = anticipated[b].difference(available_out[b])
        hoist[b] = set()
        for e in pre_hoist:
            if len(b.out_blocks) > 1 and all([e in block_gens[c] for c in b.out_blocks]):
                hoist[b].add(e)

    visited_blocks = set()

    def retarget_exp(b: TripleBlock, e: Expression, tv: TripleValue):
        visited_blocks.add(b)
        for t in b.trips:
            if does_triple_kill_expression(t, e):
                break
            if does_triple_use_expression(t, e):
                if t.l_val.typ == TripleValueType.TRIPLE_REF and triple_matches_exp(t.l_val.value, e):
                    t.l_val = copy(tv)
                elif t.r_val.typ == TripleValueType.TRIPLE_REF and triple_matches_exp(t.r_val.value, e):
                    t.r_val = copy(tv)
                CHANGE_HINTS[t] = "Retarget to Non-Redundant Expression"
        else:
            for ob in b.out_blocks:
                if ob not in visited_blocks:
                    retarget_exp(ob, e, tv)

    for b,v in hoist.items():
        for e in v:
            new_trip = exp_to_triple(e)
            opt_ctx.insert_triple(opt_ctx.trips.index(b.trips[0]), new_trip, "Redundant Expression Motion")
            visited_blocks.clear()
            retarget_exp(b, e, create_tref_value(new_trip))

    for b in temp_blocks:
        assert len(b.in_blocks) == 1
        parent = b.in_blocks[0]
        parent.trips.extend(b.trips)
        parent.out_blocks = b.out_blocks
        for child in parent.out_blocks:
            child.in_blocks.remove(b)
            child.in_blocks.append(parent)
        blocks.remove(b)
    
    pass

def code_motion(b: TripleBlock, opt_ctx: OptimizationContext):
    move_before = {}
    for i,t in enumerate(b.trips):
        if t.typ == TripleType.ASSIGN:
            var_ref = create_var_ref_value(t.l_val.value)
            if var_ref in b.in_vals:
                continue
            was_assigned = False
            for j,t2 in enumerate(b.trips[i+1:]):
                if triple_assigns_var(t2, var_ref.value):
                    was_assigned = True
                    break
                if triple_references_var(t2, var_ref.value):
                    break
            else:
                continue
            if not was_assigned and j > 4:
                significant_values = set(get_triple_referenced_values(t2))
                for k in reversed(range(1,j+1)):
                    tk = b.trips[i+k]
                    should_defer = False
                    if tk.typ == TripleType.ARG:
                        should_defer = True
                    elif any([(v.typ == TripleValueType.VAR_REF and triple_assigns_var(tk, v.value)) or (v.typ == TripleValueType.TRIPLE_REF and v.value == tk) for v in significant_values]):
                        significant_values.update(get_triple_referenced_values(tk))
                        should_defer = True
                    if not should_defer:
                        move_before[t] = b.trips[i+k+1]
                        break
        elif t.typ == TripleType.BINARY_OP and t in opt_ctx.triple_references:
            exp = triple_to_exp(t)
            was_killed = False
            for j,t2 in enumerate(b.trips[i+1:]):
                if does_triple_kill_expression(t2, exp):
                    was_killed = True
                    break
                if does_triple_use_expression(t2, exp):
                    break
            else:
                continue
            if not was_killed and j > 4:
                significant_values = set(get_triple_referenced_values(t2))
                for k in reversed(range(1,j+1)):
                    tk = b.trips[i+k]
                    should_defer = False
                    if tk.typ == TripleType.ARG:
                        should_defer = True
                    elif any([(v.typ == TripleValueType.VAR_REF and triple_assigns_var(tk, v.value)) or (v.typ == TripleValueType.TRIPLE_REF and v.value == tk) for v in significant_values]):
                        significant_values.update(get_triple_referenced_values(tk))
                        should_defer = True
                    if not should_defer:
                        move_before[t] = b.trips[i+k+1]
                        break

    pass
    for t,t2 in move_before.items():
        opt_ctx.move_triple(t, opt_ctx.trips.index(t2), "Code Motion")  

    pass          

def annotate_triples(trips: List[Triple]):
    for i, t in enumerate(trips):
        if t.typ == TripleType.IF_COND and i > 0:
            cond_val: TripleValue = t.l_val
            if cond_val.typ == TripleValueType.TRIPLE_REF and cond_val.value == trips[i - 1]:
                if cond_val.value.typ == TripleType.BINARY_OP and cond_val.value.op in CMP_OP_INSTR_MAP:
                    # If the condition for this branch is the preceding triple
                    if OPTIMIZATION_FLAGS["cmp-forward"]:
                        trips[i - 1].flags |= TF_BOOL_FORWARDED
        elif t.typ == TripleType.FUN_ARG_IN or t.typ == TripleType.SYSCALL:
            continue

def get_reference_data(trips: List[Triple]):
    triple_references: Dict[Triple, List[Triple]] = {}
    for t in trips:
        if t.typ == TripleType.LABEL:
            continue
        triple_references[t] = list(filter(lambda x: triple_references_triple(x, t), trips))
    return triple_references

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

def block_local_optimize(b: TripleBlock, opt_ctx: OptimizationContext):
    linear_combinations: Dict[TripleValue, LinearCombination] = {}
    for i,t in enumerate(b.trips):
        if t.typ == TripleType.ASSIGN:
            # TODO: Global value forwarding
            var = create_var_ref_value(t.l_val.value)
            var_uses = [rt for rt in b.trips[i:] if triple_references_var(rt, var.value)]
            if OPTIMIZATION_FLAGS["unused-code"]:
                var_used = var in b.out_vals or len(var_uses) > 0
                if not var_used or (var in b.vals_assigned and b.trips.index(b.vals_assigned[var]) > i):
                    opt_ctx.remove_triple(t, "Assignment Without Use")
                    continue
            if OPTIMIZATION_FLAGS["value-forwarding"]:
                if t.r_val.typ in [TripleValueType.CONSTANT, TripleValueType.VAR_REF, TripleValueType.TRIPLE_REF]:
                    # No point in forwarding triples, that just causes problems
                    next_assign = opt_ctx.find_assign_between(t, b.trips[-1], var.value)
                    last_ind = b.trips.index(next_assign) if next_assign else len(b.trips)
                    removed_all_uses = True
                    if t.r_val.typ == TripleValueType.TRIPLE_REF and var in b.out_vals:
                        continue
                    for rt in var_uses:
                        rt_ind = b.trips.index(rt)
                        if i < rt_ind < last_ind:
                            has_value_changed = True
                            if t.r_val.typ == TripleValueType.CONSTANT or t.r_val.typ == TripleValueType.TRIPLE_REF:
                                has_value_changed = False
                            elif t.r_val.typ == TripleValueType.VAR_REF:
                                has_value_changed = opt_ctx.find_assign_between(t, rt, t.r_val.value) is not None
                            if not has_value_changed:
                                if rt.l_val and triple_values_equal(rt.l_val, var):
                                    rt.l_val = copy(t.r_val)
                                    CHANGE_HINTS[rt] = "Value Fowarded"
                                if rt.r_val and triple_values_equal(rt.r_val, var):
                                    rt.r_val = copy(t.r_val)
                                    CHANGE_HINTS[rt] = "Value Fowarded"
                            else:
                                removed_all_uses = False
                    if var not in b.out_vals and next_assign is None and removed_all_uses:
                        opt_ctx.remove_triple(t, "Value Forwarded")
                        continue
        elif t.typ == TripleType.NOP_REF and (t.flags & TF_DONT_FORWARD) == 0:
            if OPTIMIZATION_FLAGS["value-forwarding"]:
                opt_ctx.retarget_triple_references(t, t.l_val, "Value Forwarded")
                opt_ctx.remove_triple(t, "Value Forwarded")
                continue
        if OPTIMIZATION_FLAGS['const-eval']:
            c = evaluate_triple_const(t)
            if c is not None:
                opt_ctx.retarget_triple_references(t, create_const_value(c), "Constant Propagation")
                continue
            if t.typ == TripleType.IF_COND:
                c = None
                if t.l_val.typ == TripleValueType.TRIPLE_REF:
                    c = evaluate_triple_const(t.l_val.value)
                elif t.l_val.typ == TripleValueType.CONSTANT:
                    c = t.l_val.value
                if c is not None:
                    if (c == 0) == (t.op == Operator.NE):
                        opt_ctx.replace_triple(t, Triple(TripleType.GOTO, None, t.r_val, None, uid=triple_uid()))
                    else:
                        opt_ctx.remove_triple(t)
                    continue
        if OPTIMIZATION_FLAGS["null-op"]:
            nullop_val = null_operation_eval(t)
            if nullop_val is not None:
                opt_ctx.retarget_triple_references(t, nullop_val, "Null-Op Retarget")
                opt_ctx.remove_triple(t)
                continue
        if OPTIMIZATION_FLAGS["strength-reduce"]:
            strength_reduce(t)
        if OPTIMIZATION_FLAGS["linear-combinations"]:
            if t.typ == TripleType.BINARY_OP:
                if t.l_val.typ == TripleValueType.VAR_REF and t.l_val not in linear_combinations:
                    linear_combinations[t.l_val] = LinearCombination(create_var_ref_value(t.l_val.value))
                if t.r_val.typ == TripleValueType.VAR_REF and t.r_val not in linear_combinations:
                    linear_combinations[t.r_val] = LinearCombination(create_var_ref_value(t.r_val.value))
                var_vals = [v for v in (t.l_val, t.r_val) if v in linear_combinations]
                other_vals = [v for v in (t.l_val, t.r_val) if v not in var_vals]
                if len(var_vals) == 1 and len(other_vals) == 1:
                    lc = linear_combinations[var_vals[0]]
                    new_lc = None
                    if t.op == Operator.PLUS:
                        new_lc = lc.add_operation(t.op, other_vals[0])
                    elif t.op == Operator.MINUS:
                        if other_vals[0] == t.r_val:
                            new_lc = lc.add_operation(t.op, other_vals[0])
                        else:
                            new_lc = lc.do_negate().add_operation(Operator.PLUS, other_vals[0])
                    if new_lc:
                        new_lc.last_triple = t
                        linear_combinations[create_tref_value(t)] = new_lc
                elif len(var_vals) == 2:
                    if t.op in (Operator.PLUS, Operator.MINUS):
                        if triple_values_equal(linear_combinations[var_vals[0]].linear_var, linear_combinations[var_vals[1]].linear_var):
                            new_lc = linear_combinations[var_vals[0]].try_merge_linear_combination(linear_combinations[var_vals[1]], positive=t.op == Operator.PLUS)
                            if new_lc:
                                new_lc.last_triple = t
                                linear_combinations[create_tref_value(t)] = new_lc

    if OPTIMIZATION_FLAGS["linear-combinations"]:
        for v,lc in linear_combinations.items():
            if v.typ == TripleValueType.TRIPLE_REF:
                trip = v.value
                if len(lc.operations) > 1:
                    olen = len(lc.operations)
                    lc.merge_operations()
                    if len(lc.operations) < olen:
                        # If we merged
                        trefs = opt_ctx.triple_references[trip]
                        if not all([create_tref_value(t) in linear_combinations for t in trefs]):
                            # If this triple isn't solely a part of other linear combinations
                            # Materialize this LC
                            materialize_trips = []
                            v = lc.linear_var
                            if lc.coefficient_val:
                                materialize_trips.append(Triple(TripleType.BINARY_OP, Operator.MULTIPLY, v, lc.coefficient_val, flags=TF_SIGNED, uid=triple_uid()))
                                v = create_tref_value(materialize_trips[-1])
                            if lc.negate and (len(lc.operations) == 0 or not lc.operations[0][0]):
                                materialize_trips.append(Triple(TripleType.UNARY_OP, Operator.NEGATE, v, None, uid=triple_uid()))
                                v = create_tref_value(materialize_trips[-1])
                            else:
                                do_negate = lc.negate
                                for pos,v1 in lc.operations:
                                    if do_negate:
                                        materialize_trips.append(Triple(TripleType.BINARY_OP, Operator.MINUS, v1, v, flags=TF_SIGNED, uid=triple_uid()))
                                        do_negate = False
                                    else:
                                        materialize_trips.append(Triple(TripleType.BINARY_OP, Operator.PLUS if pos else Operator.MINUS, v, v1, flags=TF_SIGNED, uid=triple_uid()))
                                    v = create_tref_value(materialize_trips[-1])
                            ind = opt_ctx.trips.index(trip)
                            for t in reversed(materialize_trips):
                                opt_ctx.insert_triple(ind, t, "Materialize Linear Operation")
                            opt_ctx.retarget_triple_references(trip, v, "Combined Linear Operation")

    if OPTIMIZATION_FLAGS["code-motion"]:
        code_motion(b, opt_ctx)

def optimize_by_block(opt_ctx: OptimizationContext):
    opt_ctx.evaluate_triple_references()
    opt_ctx.evaluate_label_references()
    
    forward_labels(opt_ctx)
    remove_unused_labels(opt_ctx)
    remove_pointless_goto(opt_ctx)
    remove_unreachable_triples(opt_ctx)

    if OPTIMIZATION_FLAGS["unused-code"]:
        remove_unused_triples(opt_ctx)

    if len(opt_ctx.trips) == 0:
        return

    opt_ctx.recalculate_blocks()

    for b in opt_ctx.blocks:
        block_local_optimize(b, opt_ctx)

    pass

def optimize_regional(opt_ctx: OptimizationContext):

    if OPTIMIZATION_FLAGS["code-hoisting"]:
        index_triples(opt_ctx.trips)
        opt_ctx.recalculate_blocks()
        expression_analysis(opt_ctx)

    if OPTIMIZATION_FLAGS["common-exp"]:
        opt_ctx.recalculate_blocks()
        common_removed = {}

        for t in opt_ctx.trips:
            if does_triple_produce_data(t):
                match = opt_ctx.common_exp_match(t)
                if match:
                    while match in common_removed:
                        match = common_removed[match]
                    opt_ctx.retarget_triple_references(t, create_tref_value(match), "Common Expression")
                    common_removed[t] = match
        
        for t in common_removed:
            opt_ctx.remove_triple(t, "Common Expression")

    if OPTIMIZATION_FLAGS["loop-optimization"]:
        opt_ctx.evaluate_triple_references()
        while True:
            index_triples(opt_ctx.trips)
            opt_ctx.recalculate_blocks()
            identify_loops(opt_ctx)

            loops_by_prio = sorted(opt_ctx.loops.items(), key=lambda x: opt_ctx.loop_prio[x[0]], reverse=True)
            for h,e in loops_by_prio:
                if optimize_loop(h, e, opt_ctx):
                    break
            else:
                break

def optimize_triples(trip_ctx: FunctionTripleContext):
    did_modify = True
    trips = trip_ctx.triples

    start_len = len(trips)

    tripopt_file = os.path.join(belfast_data.COMPILER_SETTINGS.tripopt_dir, f"{trip_ctx.ctx_name}_tripopt.tripstr")

    index_triples(trips)
    prev_trips: List[Triple] = deepcopy_trips(trips) if belfast_data.COMPILER_SETTINGS.generate_tripstr else None

    opt_ctx = OptimizationContext(trips)

    if belfast_data.COMPILER_SETTINGS.generate_tripstr and belfast_data.COMPILER_SETTINGS.generate_diff:
        with open(tripopt_file, 'w') as f:
            for t in trips:
                f.write(f"{print_triple(t)}\n")
            f.write("\n")

    passes = 0

    while True:
        passes += 1
        opt_ctx.triples_dirty = False
        if len(opt_ctx.trips) == 0:
            break
        optimize_by_block(opt_ctx)

        if not opt_ctx.triples_dirty:
            optimize_regional(opt_ctx)
        
        if not opt_ctx.triples_dirty:
            break

        index_triples(trips)
        if belfast_data.COMPILER_SETTINGS.generate_diff:
            if belfast_data.COMPILER_SETTINGS.generate_tripstr and prev_trips is not None:
                d = get_triple_delta(prev_trips, trips)
                if d == ([], [], []):
                    break
                output_triple_delta_to_file(d, tripopt_file)
                with open(tripopt_file, 'a') as f:
                    for t in trips:
                        f.write(f"{print_triple(t)}\n")
                    f.write("\n")
                prev_trips = deepcopy_trips(trips)
                CHANGE_HINTS.clear()

    if belfast_data.COMPILER_SETTINGS.verbose >= 1:
        print(f"[INFO] [{trip_ctx.ctx_name}] Optimization passes: {passes}")
        print(f"[INFO] [{trip_ctx.ctx_name}] Optimization removed {start_len - len(trips)} triples")

    return trips

def output_triple_delta_to_file(d, filename):
    with open(filename, 'a') as f:
        at, ct, rt = d
        ri = 0
        ci = 0
        ai = 0
        rt = sorted(rt, key=lambda x: x.index)
        ct = sorted(ct, key=lambda x: x[0].index)
        at = sorted(at, key=lambda x: x.index)
        while ri < len(rt) or ai < len(at) or ci < len(ct):
            wr_t = []
            if ri < len(rt):
                wr_t.append((0, rt[ri]))
            if ci < len(ct):
                wr_t.append((1, ct[ci][0]))
            if ai < len(at):
                wr_t.append((2, at[ai]))
            min_index = min([t[1].index for t in wr_t])
            min_item = [t for t in wr_t if t[1].index == min_index][0]
            trip = min_item[1]
            if min_item[0] == 0:
                f.write(f" - {print_triple(trip)}")
                if trip in CHANGE_HINTS:
                    f.write(f" ({CHANGE_HINTS[trip]})")
                f.write("\n")
                ri += 1
            elif min_item[0] == 1:
                trip1, trip2 = ct[ci]
                f.write(f" < {print_triple(trip1)}\n > {print_triple(trip2)}")
                if trip1 in CHANGE_HINTS:
                    f.write(f" ({CHANGE_HINTS[trip1]})")
                f.write("\n")
                ci += 1
            else:
                f.write(f" + {print_triple(trip)}")
                if trip in CHANGE_HINTS:
                    f.write(f" ({CHANGE_HINTS[trip]})")
                f.write("\n")
                ai += 1
        f.write("\n")
                
def deepcopy_trips(trips: List[Triple]):
    deferred_refs = {} # uid: triplevalue list 
    new_trips_by_uid = {}
    def deepcopy_triple(t: Triple):
        new_t = Triple(t.typ, t.op, None, None, t.index, flags=t.flags, data=t.data, size=t.size, uid=t.uid)
        new_trips_by_uid[t.uid] = new_t
        if t.uid in deferred_refs:
            for tv in deferred_refs[t.uid]:
                tv.value = new_t
            del deferred_refs[t.uid]
        if t.l_val:
            if t.l_val.typ == TripleValueType.TRIPLE_REF:
                ref_uid = t.l_val.value.uid
                if ref_uid in new_trips_by_uid:
                    new_t.l_val = TripleValue(TripleValueType.TRIPLE_REF, new_trips_by_uid[ref_uid])
                else:
                    tv = TripleValue(TripleValueType.TRIPLE_REF, None)
                    if ref_uid not in deferred_refs:
                        deferred_refs[ref_uid] = []
                    deferred_refs[ref_uid].append(tv)
                    new_t.l_val = tv
            else:
                new_t.l_val = TripleValue(t.l_val.typ, t.l_val.value)
        if t.r_val:
            if t.r_val.typ == TripleValueType.TRIPLE_REF:
                ref_uid = t.r_val.value.uid
                if ref_uid in new_trips_by_uid:
                    new_t.r_val = TripleValue(TripleValueType.TRIPLE_REF, new_trips_by_uid[ref_uid])
                else:
                    tv = TripleValue(TripleValueType.TRIPLE_REF, None)
                    if ref_uid not in deferred_refs:
                        deferred_refs[ref_uid] = []
                    deferred_refs[ref_uid].append(tv)
                    new_t.r_val = tv
            else:
                new_t.r_val = TripleValue(t.r_val.typ, t.r_val.value)
        return new_t

    new_trips = [deepcopy_triple(t) for t in trips]
    # if len(deferred_refs):
    #     tl = [t for t in trips if t.uid in deferred_refs]
    #     assert False, "Unhandled deferred triple references"
    
    return new_trips

def get_triple_delta(old_trips: List[Triple], new_trips: List[Triple]):
    trips_by_uid = {t.uid: t for t in old_trips}
    added_trips = []
    changed_trips = []
    removed_trips = []

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

    for t in new_trips:
        eq_trip = trips_by_uid[t.uid] if t.uid in trips_by_uid else None
        if eq_trip:
            del trips_by_uid[t.uid]
            if not shallow_trips_equal(t, eq_trip):
                changed_trips.append((eq_trip, t))
        else:
            added_trips.append(t)

    removed_trips = list(trips_by_uid.values())
    return added_trips, changed_trips, removed_trips
