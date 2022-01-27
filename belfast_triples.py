from belfast_data import *

class TripleContext:

    def __init__(self):
        self.declared_vars: Set[str] = set()
        self.functions = {}
        self.function_ctx = {}
        self.buffers: Dict[str, int] = {}
        self.buffer_offs = 0
        self.string_offs = 0
        self.strings: Dict[str, str] = {}
        self.register_alloc: Dict[TripleValue, int] = {}
        self.val_liveness : Dict[TripleValue, Set[int]] = {}
        self.spilled_values : Dict[TripleValue, int] = {}
        self.memory_spill_register = None
        self.active_break_label = None
        self.active_continue_label = None
        self.ctx_name = ''
        self.has_generated_print_code = False

    def variable_exists(self, name:str):
        return name in self.declared_vars

    def declare_variable(self, name:str):
        self.declared_vars.add(name)

    def declare_function(self, name:str, trips: List[Triple], trip_ctx: 'TripleContext'):
        self.functions[name] = trips
        self.function_ctx[name] = trip_ctx

    def create_subctx(self):
        return self
        # tctx = TripleContext()
        # tctx.declared_vars.update(self.declared_vars)
        # return tctx

    def allocate_buffer(self, amt: int):
        name = f'_BUF{len(self.buffers) + self.buffer_offs}'
        self.buffers[name] = amt
        return name

    def allocate_string(self, string: str):
        if string not in self.strings:
            self.strings[string] = f"_S{len(self.strings) + self.string_offs}"
        return self.strings[string]

    def get_allocated_register(self, tv:TripleValue, tripl_num:int):
        if tv in self.register_alloc:
            return self.register_alloc[tv]
        return None

    def get_all_used_registers(self, index:int):
        reg = set()
        for v,s in self.val_liveness.items():
            if index in s:
                reg.add(self.register_alloc[v])
        return reg


def print_triple(t:Triple):
    ind_str = str(t.index)
    trip_str = f"{t.index}:{' ' * (4 - len(ind_str))}{t.typ.name}"
    if t.typ == TripleType.BINARY_OP or t.typ == TripleType.UNARY_OP or t.typ == TripleType.IF_COND:
        trip_str += f" {t.op.name}"
    if t.typ == TripleType.STORE or t.typ == TripleType.LOAD:
        trip_str += f"{t.size}"

    trip_str += " "
    
    if t.l_val is not None:
        trip_str += trip_val_to_str(t.l_val, as_hex=t.typ == TripleType.SYSCALL) + ' '

    if t.typ == TripleType.IF_COND:
        trip_str += "GOTO "

    if t.r_val is not None:
        trip_str += trip_val_to_str(t.r_val) + ' '
    
    return trip_str


def index_triples(trips:List[Triple]):
    for i,val in enumerate(trips):
        val.index = i

def triples_parse_program(ast_list: List[ASTNode_Base]):
    ctx = TripleContext()
    ctx.ctx_name = 'main'
    trips = []
    for a in ast_list:
        t, _ = ast_to_triples(a, ctx)
        trips.extend(t)
    return trips, ctx

def ast_to_triples(ast:ASTNode_Base, ctx:TripleContext):
    triples = []
    trip_val:TripleValue = TripleValue(TripleValueType.UNKNOWN, 0, ast.value)
    match ast.typ:
        case ASTType.NUMBER:
            trip_val = TripleValue(TripleValueType.CONSTANT, ast.num_value, ast.value)
        case ASTType.STRING:
            labl = ctx.allocate_string(ast.ident_str)
            trip_val = TripleValue(TripleValueType.STRING_REF, labl, ast.value)
        case ASTType.BINARY_OP:
            l_trips, l_trip_val = ast_to_triples(ast.l_ast, ctx)
            r_trips, r_trip_val = ast_to_triples(ast.r_ast, ctx)
            triples.extend(l_trips)
            triples.extend(r_trips)
            triples.append(Triple(TripleType.BINARY_OP,op=TOKEN_OP_MAP[ast.value.typ], l_val=l_trip_val, r_val=r_trip_val))
            trip_val = TripleValue(TripleValueType.TRIPLE_REF, triples[-1], ast.value)
        case ASTType.UNARY_OP:
            exp_trips, exp_trip_val = ast_to_triples(ast.ast_ref, ctx)
            triples.extend(exp_trips)
            op = TOKEN_OP_MAP[ast.value.typ]
            if op == Operator.MINUS:
                # Unary minus is a negation
                op = Operator.NEGATE
            
            if op == Operator.LOGICAL_NOT:
                triples.append(Triple(TripleType.BINARY_OP, op=Operator.EQ, l_val=exp_trip_val, r_val=TripleValue(TripleValueType.CONSTANT, 0)))
            else:
                triples.append(Triple(TripleType.UNARY_OP, op=op, l_val=exp_trip_val, r_val=None))
            trip_val = TripleValue(TripleValueType.TRIPLE_REF, triples[-1], ast.value)
        case ASTType.PRINT:
            exp_trips, exp_trip_val = ast_to_triples(ast.ast_ref, ctx)
            triples.extend(exp_trips)
            triples.append(Triple(TripleType.PRINT, op=Keyword.PRINT, l_val=exp_trip_val, r_val=None))
            trip_val = None
        case ASTType.VAR_DECL:
            ctx.declare_variable(ast.ident_str)
        case ASTType.VAR_DECL_ASSIGN:
            ctx.declare_variable(ast.ident_str)
            trips, trip_val = ast_to_triples(ast.ast_ref, ctx)
            triples.extend(trips)
            triples.append(Triple(TripleType.ASSIGN, None, TripleValue(TripleValueType.VAR_ASSIGN, ast.ident_str), trip_val))
        case ASTType.VAR_REF:
            assert ctx.variable_exists(ast.ident_str), "This may be a bug in the parsing step"
            trip_val = TripleValue(TripleValueType.VAR_REF, ast.ident_str, ast.value)
        case ASTType.BUFFER_ALLOC:
            trip_val = TripleValue(TripleValueType.BUFFER_REF, ctx.allocate_buffer(ast.num_value), ast.value)
        case ASTType.ASSIGN:
            l_trips, l_trip_val = ast_to_triples(ast.l_ast, ctx)
            assert len(l_trips) == 0, "Multiple triples on Assign LHS not supported"
            assert l_trip_val.typ == TripleValueType.VAR_REF, "Expected variable ref on LHS of Assign"
            r_trips, r_trip_val = ast_to_triples(ast.r_ast, ctx)
            triples.extend(r_trips)
            triples.append(Triple(TripleType.ASSIGN, op=None, l_val=TripleValue(TripleValueType.VAR_ASSIGN, value=l_trip_val.value), r_val=r_trip_val))
            trip_val = TripleValue(TripleValueType.TRIPLE_REF, triples[-1], ast.value)
        case ASTType.IF:
            cond_trips, cond_val = ast_to_triples(ast.cond_ast, ctx)
            scoped_ctx = ctx.create_subctx()
            triples.extend(cond_trips)
            end_label_triple = Triple(TripleType.LABEL, None, None, None)
            end_goto_triple = None
            if ast.else_ast_block or ast.else_if_ast:
                end_goto_triple = Triple(TripleType.LABEL, None, None, None)
            triples.append(Triple(TripleType.IF_COND, op=Operator.NE, l_val=cond_val, r_val=TripleValue(TripleValueType.TRIPLE_TARGET, end_label_triple)))
            for a in ast.then_ast_block:
                a_trips, _ = ast_to_triples(a, scoped_ctx)
                triples.extend(a_trips)
            if end_goto_triple is not None:
                triples.append(Triple(TripleType.GOTO, None, TripleValue(TripleValueType.TRIPLE_TARGET, end_goto_triple), None))
            if ast.else_ast_block is not None:
                else_scoped_ctx = ctx.create_subctx()
                triples.append(end_label_triple)
                for a in ast.else_ast_block:
                    a_trips, _ = ast_to_triples(a, else_scoped_ctx)
                    triples.extend(a_trips)
                triples.append(end_goto_triple)
            elif ast.else_if_ast is not None:
                triples.append(end_label_triple)
                elif_trips, _ = ast_to_triples(ast.else_if_ast, ctx)
                triples.extend(elif_trips)
                triples.append(end_goto_triple)
            else:
                triples.append(end_label_triple)
        case ASTType.WHILE:
            cond_trips, cond_val = ast_to_triples(ast.cond_ast, ctx)
            scoped_ctx = ctx.create_subctx()
            end_label_triple = Triple(TripleType.LABEL, None, None, None)
            scoped_ctx.active_break_label = end_label_triple
            cond_eval_label = Triple(TripleType.LABEL, None, None, None)
            scoped_ctx.active_continue_label = cond_eval_label
            triples.append(cond_eval_label)
            triples.extend(cond_trips)
            triples.append(Triple(TripleType.IF_COND, op=Operator.NE, l_val=cond_val, r_val=TripleValue(TripleValueType.TRIPLE_TARGET, end_label_triple)))
            for a in ast.do_ast_block:
                a_trips, _ = ast_to_triples(a, scoped_ctx)
                triples.extend(a_trips)
            triples.append(Triple(TripleType.GOTO, op=None, l_val=TripleValue(TripleValueType.TRIPLE_TARGET, cond_eval_label), r_val=None))
            triples.append(end_label_triple)
        case ASTType.BREAK:
            if ctx.active_break_label:
                triples.append(Triple(TripleType.GOTO, op=None, l_val=TripleValue(TripleValueType.TRIPLE_TARGET, ctx.active_break_label), r_val=None))
            else:
                compiler_error(ast.value.loc, "Break statement must be inside of a loop")
        case ASTType.CONTINUE:
            if ctx.active_continue_label:
                triples.append(Triple(TripleType.GOTO, op=None, l_val=TripleValue(TripleValueType.TRIPLE_TARGET, ctx.active_continue_label), r_val=None))
            else:
                compiler_error(ast.value.loc, "Continue statement must be inside of a loop")
        case ASTType.SYSCALL:
            syscall_num_val = ast.args[0]
            s_trips, s_val = ast_to_triples(syscall_num_val, ctx)
            triples.extend(s_trips)
            reg_index = 0
            for a in ast.args[1:]:
                a_trips, a_val = ast_to_triples(a, ctx)
                triples.extend(a_trips)
                triples.append(Triple(TripleType.ARG, op=None, l_val=a_val, r_val=None, flags=reg_index))
                reg_index += 1
            triples.append(Triple(TripleType.SYSCALL, op=None, l_val=s_val, r_val=None, flags=len(ast.args)-1))
            trip_val = TripleValue(TripleValueType.TRIPLE_REF, triples[-1])
        case ASTType.LOAD:
            ptr_exp_trips, ptr_exp_val = ast_to_triples(ast.ptr_exp, ctx)
            triples.extend(ptr_exp_trips)
            triples.append(Triple(TripleType.LOAD, None, ptr_exp_val, None, size=ast.size))
            trip_val = TripleValue(TripleValueType.TRIPLE_REF, triples[-1])
        case ASTType.STORE:
            ptr_exp_trips, ptr_exp_val = ast_to_triples(ast.ptr_exp, ctx)
            triples.extend(ptr_exp_trips)
            val_exp_trips, val_exp_val = ast_to_triples(ast.val_exp, ctx)
            triples.extend(val_exp_trips)
            triples.append(Triple(TripleType.STORE, None, ptr_exp_val, val_exp_val, size=ast.size))
        case ASTType.FUN_DEF:
            fun_name = ast.fun_name
            args = ast.args
            fun_triples = []
            scoped_ctx = TripleContext()
            scoped_ctx.buffer_offs = len(ctx.buffers) + ctx.buffer_offs
            scoped_ctx.string_offs = len(ctx.strings) + ctx.string_offs
            scoped_ctx.declared_vars.update(args)
            scoped_ctx.ctx_name = fun_name
            for i,a in enumerate(args):
                fun_triples.append(Triple(TripleType.FUN_ARG_IN, None, TripleValue(TripleValueType.VAR_ASSIGN, a), None, flags=i))
            for a in ast.body:
                a_trips, _ = ast_to_triples(a, scoped_ctx)
                fun_triples.extend(a_trips)
            ctx.buffer_offs += len(scoped_ctx.buffers)
            ctx.string_offs += len(scoped_ctx.strings)
            ctx.declare_function(fun_name, fun_triples, scoped_ctx)
        case ASTType.FUN_CALL:
            fun_name = ast.fun_name
            for i in range(len(ast.args)):
                arg_trips, arg_val = ast_to_triples(ast.args[i], ctx)
                triples.extend(arg_trips)
                triples.append(Triple(TripleType.ARG, None, arg_val, None, flags=i))
            triples.append(Triple(TripleType.CALL, None, TripleValue(TripleValueType.FUN_LABEL, fun_name), None, flags=len(ast.args)))
        case _:
            assert False, f"Unhandled AST Type {ast.typ.name}"
    return triples, trip_val

def triple_value_uses_triple(tv:TripleValue, triple:Triple):
    return tv.typ == TripleValueType.TRIPLE_REF and tv.value == triple

def triple_uses_triple(t:Triple, used_triple:Triple):
    return (t.l_val is not None and triple_value_uses_triple(t.l_val, used_triple)) or (t.r_val is not None and triple_value_uses_triple(t.r_val, used_triple))

def get_triple_loc_str(tloc: TripleLoc, size=64):
    match tloc.typ:
        case TripleLocType.CONSTANT:
            return str(tloc.value)
        case TripleLocType.REGISTER:
            return reg_str_for_size(tloc.value, size)
        case TripleLocType.IN_MEMORY_AT_LABEL:
            return f"qword [{tloc.value}]"
        case TripleLocType.MEMORY_ADDR_LABEL:
            return f"{tloc.value}"
        case _:
            assert False, f"Unhandled Triple Loc Type {tloc.typ}"

def get_triple_loc(tv:TripleValue, ctx:'ASMContext') -> TripleLoc:
    reg = ctx.get_value_register(tv)
    if reg != 0:
        return TripleLoc(TripleLocType.REGISTER, reg)
    match tv.typ:
        case TripleValueType.CONSTANT:
            return TripleLoc(TripleLocType.CONSTANT, tv.value)
        case TripleValueType.VAR_REF | TripleValueType.VAR_ASSIGN:
            assert tv.value in ctx.var_table, "Variable was not put into var table"
            return ctx.var_table[tv.value]
        case TripleValueType.BUFFER_REF:
            assert tv.value in ctx.buffer_table, "Buffer was not put into buffer table"
            return ctx.buffer_table[tv.value][1]
        case TripleValueType.STRING_REF:
            return TripleLoc(TripleLocType.MEMORY_ADDR_LABEL, tv.value)
        case TripleValueType.TRIPLE_REF:
            assert isinstance(tv.value, Triple), "Expected Triple Ref to reference Triple"
            trip : Triple = tv.value
            if trip.loc is not None:
                return trip.loc
            else:
                assert False, "Reference to unevaluated value"
        case _:
            assert False, f"Unhandled Triple Value Type {tv.typ.name}"


class ASMContext:

    def __init__(self):
        self.register_datas = [RegisterData(i, registers[i] in data_registers, False, None, False) for i in range(len(registers))]
        self.temp_registers = [r for r in self.register_datas if r.is_data_reg]
        self.var_table: Dict[str, TripleLoc] = {}
        self.vars_dirty: Set[str] = set()
        self.arg_count = 0
        self.buffer_table : Dict[str, Tuple[int, TripleLoc]] = {}
        self.string_table: Dict[str, str] = {}
        self.current_trip_eval = 0

    def next_arg(self):
        assert self.arg_count < len(ARG_REGISTERS), "Only function calls with 6 arguments or less are supported right now"
        reg = ARG_REGISTERS[self.arg_count]
        self.arg_count += 1
        return reg

    def reset_args(self):
        self.arg_count = 0

    def build_var_table(self, trip_ctx:TripleContext):
        for v in trip_ctx.declared_vars:
            self.var_table[v] = TripleLoc(TripleLocType.IN_MEMORY_AT_LABEL, f"_VAR_{v}")
        for b,sz in trip_ctx.buffers.items():
            self.buffer_table[b] = (sz, TripleLoc(TripleLocType.MEMORY_ADDR_LABEL, b))
        self.string_table.update(trip_ctx.strings)

    def mark_variable_dirty(self, var:str):
        self.vars_dirty.add(var)

    def get_value_register(self, tv:TripleValue):
        for rd in self.temp_registers:
            if rd.has_data and triple_values_equal(rd.triple_value_in, tv):
                return rd.index
        return 0

    def get_free_register(self, exclude_reg=()):
        for rd in self.temp_registers:
            if (rd.index not in exclude_reg) and (not rd.has_data or rd.data_not_needed):
                return rd.index

        print('\n'.join([f"{reg_str_for_size(rd.index)}: {trip_val_to_str(rd.triple_value_in)}" for rd in self.temp_registers]))
        assert False, "All registers full"

    def put_value_in_free_register(self, tv:TripleValue, exclude_reg=()):
        reg = self.get_free_register(exclude_reg)
        # print(f"Found free register {registers[reg]} for value {trip_val_to_str(tv)}")
        return self.put_value_in_register(reg, tv)

    def put_value_in_register(self, index:int, tv:TripleValue):
        rd = self.register_datas[index]
        if rd.has_data and triple_values_equal(rd.triple_value_in, tv):
            return ""
        asm = self.save_value_in_register(index)
        existing_reg = self.get_value_register(tv)
        if existing_reg != 0:
            # If this value is already in a register
            self.free_register(existing_reg, do_save=False)
        l = get_triple_loc(tv, self)
        if l.typ == TripleLocType.MEMORY_ADDR_LABEL:
            asm += f"\tlea {reg_str_for_size(rd.index)}, {l.value}\n"
        else:
            asm += f"\tmov {reg_str_for_size(rd.index)}, {get_triple_loc_str(l)}\n"
        rd.triple_value_in = tv
        rd.has_data = True
        rd.data_not_needed = False
        return asm

    def save_value_in_register(self, index:int):
        rd = self.register_datas[index]
        # print(f"Saving value in register {registers[rd.index]}")
        if rd.has_data and not rd.data_not_needed:
            tv_in: TripleValue = rd.triple_value_in
            assert tv_in is not None, "Expected data in register"
            # print(f"[Data is {trip_val_to_str(tv_in)}]")
            match tv_in.typ:
                case TripleValueType.CONSTANT:
                    return ""
                case TripleValueType.VAR_REF:
                    if tv_in.value in self.vars_dirty:
                        assert tv_in.value in self.var_table, "Variable not in var table"
                        self.vars_dirty.remove(tv_in.value)
                        return f"\tmov {get_triple_loc_str(self.var_table[tv_in.value])}, {get_triple_loc_str(get_triple_loc(tv_in, self))}\n"
                    else:
                        return ""
                case TripleValueType.BUFFER_REF | TripleValueType.STRING_REF:
                    return ""
                case TripleValueType.TRIPLE_REF:
                    assert isinstance(tv_in.value, Triple), "Expected Triple in Triple Ref value"
                    trip:Triple = tv_in.value
                    if trip.last_use > self.current_trip_eval:
                        # Try moving to a new register for now if we use this later
                        asm = self.put_value_in_free_register(tv_in)
                        trip.loc = get_triple_loc(tv_in, self)
                        return asm
                    return ""
                case _:
                    assert False, f"Unhandled Triple Value Type {tv_in.typ} in register"

        return ""

    def register_value_updated(self, index:int, tv:TripleValue):
        rd = self.register_datas[index]
        rd.has_data = True
        rd.triple_value_in = tv
        rd.data_not_needed = False

    def update_reg_triple(self, index:int, t:Triple):
        tv:TripleValue = TripleValue(TripleValueType.TRIPLE_REF, t, None)
        self.register_value_updated(index, tv)

    def free_register(self, index:int, do_save=True):
        rd = self.register_datas[index]
        asm = ""
        if rd.has_data and do_save:
            asm += self.save_value_in_register(index)
        rd.has_data = False
        rd.data_not_needed = False
        rd.triple_value_in = None
        return asm

    def flush_registers(self, do_save=False, except_reg=()):
        asm = ""
        for rd in self.temp_registers:
            if rd.index in except_reg:
                continue
            asm += self.free_register(rd.index, do_save)
        return asm

    def flush_variable_registers(self):
        for rd in self.temp_registers:
            if rd.has_data and rd.triple_value_in.typ == TripleValueType.VAR_REF:
                self.free_register(rd.index, do_save=False)

    def value_used(self, tv:TripleValue):
        reg = self.get_value_register(tv)
        if reg > 0:
            if tv.typ == TripleValueType.TRIPLE_REF:
                trip: Triple = tv.value
                if trip.flags & TF_EPHEMERAL:
                    self.register_datas[reg].data_not_needed = True
                    # print(f"Freeing value {trip_val_to_str(tv)} from reg {registers[reg]}")

def convert_triple_to_asm(triple:Triple, ctx:ASMContext, trip_ctx:TripleContext, no_comments=False):
    if not no_comments:
        asm = f"\t; {print_triple(triple)}\n"
    else:
        asm = ""
    def write_asm(s):
        nonlocal asm
        asm += '\t' + s + '\n'

    used_values = []

    ctx.current_trip_eval = triple.index

    # print(print_triple(triple))

    match triple.typ:
        case TripleType.BINARY_OP:
            lv: TripleValue = triple.l_val
            rv: TripleValue = triple.r_val
            used_values.append(lv)
            used_values.append(rv)
            loc_l: TripleLoc = get_triple_loc(lv, ctx)
            if loc_l.typ != TripleLocType.REGISTER:
                if triple.op == Operator.DIVIDE or triple.op == Operator.MODULUS:
                    asm += ctx.put_value_in_register(RAX_INDEX, lv)
                elif triple.op == Operator.SHIFT_RIGHT or triple.op == Operator.SHIFT_LEFT:
                    asm += ctx.put_value_in_free_register(lv, exclude_reg=(RCX_INDEX,))
                else:
                    asm += ctx.put_value_in_free_register(lv)
                loc_l = get_triple_loc(lv, ctx)
            loc_r: TripleLoc = get_triple_loc(rv, ctx)
            target_loc = None
            match triple.op:
                case Operator.PLUS:
                    assert loc_l.typ == TripleLocType.REGISTER, "Expected LHS to be register"
                    asm += ctx.save_value_in_register(loc_l.value)
                    write_asm(f"add {get_triple_loc_str(loc_l)}, {get_triple_loc_str(loc_r)}")
                    ctx.update_reg_triple(loc_l.value, triple)
                    triple.loc = loc_l
                case Operator.MINUS:
                    assert loc_l.typ == TripleLocType.REGISTER, "Expected LHS to be register"
                    asm += ctx.save_value_in_register(loc_l.value)
                    write_asm(f"sub {get_triple_loc_str(loc_l)}, {get_triple_loc_str(loc_r)}")
                    ctx.update_reg_triple(loc_l.value, triple)
                    triple.loc = loc_l
                case Operator.MULTIPLY:
                    assert loc_l.typ == TripleLocType.REGISTER, "Expected LHS to be register"
                    if loc_r.typ == TripleLocType.CONSTANT and loc_r.value < (2 ** 32):
                        write_asm(f"imul {get_triple_loc_str(loc_l)}, {get_triple_loc_str(loc_l)}, {get_triple_loc_str(loc_r)}")
                    else:
                        if loc_r.typ != TripleLocType.REGISTER:
                            # TODO: Implement memory sourcing
                            asm += ctx.put_value_in_free_register(rv)
                            loc_r = get_triple_loc(rv, ctx)
                        assert loc_r.typ == TripleLocType.REGISTER, "Expected RHS to be register"
                        write_asm(f"imul {get_triple_loc_str(loc_l)}, {get_triple_loc_str(loc_r)}")
                    ctx.update_reg_triple(loc_l.value, triple)
                    triple.loc = loc_l
                case Operator.DIVIDE | Operator.MODULUS:
                    assert loc_l.typ == TripleLocType.REGISTER, "Expected LHS to be register"
                    assert loc_l.value == RAX_INDEX, "Expected LHS to be in RAX"
                    if loc_r.typ != TripleLocType.REGISTER:
                        asm += ctx.put_value_in_free_register(rv)
                        loc_r = get_triple_loc(rv, ctx)
                    assert loc_r.typ == TripleLocType.REGISTER, "Expected RHS to be register"
                    ctx.free_register(RDX_INDEX, do_save=True)
                    write_asm("xor rdx, rdx")
                    write_asm(f"idiv {get_triple_loc_str(loc_r)}")
                    ctx.free_register(RAX_INDEX, do_save=False)
                    if triple.op == Operator.DIVIDE:
                        ctx.update_reg_triple(loc_l.value, triple)
                        triple.loc = loc_l
                    else:
                        ctx.update_reg_triple(RDX_INDEX, triple)
                        triple.loc = TripleLoc(TripleLocType.REGISTER, RDX_INDEX)
                case Operator.GE | Operator.LE | Operator.GT | Operator.LT | Operator.NE | Operator.EQ:
                    assert loc_l.typ == TripleLocType.REGISTER, "Expected LHS to be register"
                    # TODO: Handle 64-bit imm
                    # TODO: This operation does not need to overwrite l value
                    asm += ctx.save_value_in_register(loc_l.value)
                    write_asm(f"cmp {get_triple_loc_str(loc_l)}, {get_triple_loc_str(loc_r)}")
                    if triple.flags & TF_BOOL_FORWARDED == 0:
                        write_asm(f"mov {get_triple_loc_str(loc_l)}, 0")
                        write_asm(f"set{CMP_OP_INSTR_MAP[triple.op]} {get_triple_loc_str(loc_l, size=8)}")
                        ctx.update_reg_triple(loc_l.value, triple)
                        triple.loc = loc_l
                case Operator.SHIFT_RIGHT | Operator.SHIFT_LEFT:
                    asm_instr = "shr" if triple.op == Operator.SHIFT_RIGHT else "shl"
                    asm += ctx.save_value_in_register(loc_l.value)
                    if loc_r.typ == TripleLocType.CONSTANT:
                        write_asm(f"{asm_instr} {get_triple_loc_str(loc_l)}, {get_triple_loc_str(loc_r, 8)}")
                    else:
                        if loc_r.typ != TripleLocType.REGISTER or loc_r.value != RCX_INDEX:
                            if triple.index == 66:
                                print()
                            asm += ctx.put_value_in_register(RCX_INDEX, rv)
                            loc_r = get_triple_loc(rv, ctx)
                        assert loc_r.typ == TripleLocType.REGISTER and loc_r.value == RCX_INDEX, "Expected shift operand to be in CL"
                        write_asm(f"{asm_instr} {get_triple_loc_str(loc_l)}, {get_triple_loc_str(loc_r, 8)}")
                    ctx.update_reg_triple(loc_l.value, triple)
                    triple.loc = loc_l
                case Operator.BITWISE_AND | Operator.BITWISE_OR | Operator.BITWISE_XOR:
                    asm_instr = {Operator.BITWISE_AND: 'and', Operator.BITWISE_OR: 'or', Operator.BITWISE_XOR: 'xor'}[triple.op]
                    assert loc_l.typ == TripleLocType.REGISTER, "Expected LHS to be register"
                    asm += ctx.save_value_in_register(loc_l.value)
                    write_asm(f"{asm_instr} {get_triple_loc_str(loc_l)}, {get_triple_loc_str(loc_r)}")
                    ctx.update_reg_triple(loc_l.value, triple)
                    triple.loc = loc_l
                case _:
                    assert False, f"Unhandled Triple Operator {triple.op.name}"
        case TripleType.UNARY_OP:
            v: TripleValue = triple.l_val
            used_values.append(v)
            v_loc: TripleLoc = get_triple_loc(v, ctx)
            match triple.op:
                case _:
                    assert False, f"Unhandled Triple Operator {triple.op.name}"
        case TripleType.PRINT:
            v = triple.l_val
            used_values.append(v)
            asm += ctx.put_value_in_register(RDI_INDEX, v)
            asm += ctx.flush_registers(do_save=True, except_reg=(RDI_INDEX,))
            write_asm(f"call _printd")
            ctx.flush_registers(do_save=False)
        case TripleType.ASSIGN:
            var_val: TripleValue = triple.l_val
            rhs_val: TripleValue = triple.r_val
            used_values.append(rhs_val)
            loc_r: TripleLoc = get_triple_loc(rhs_val, ctx)
            if loc_r.typ != TripleLocType.REGISTER and loc_r.typ != TripleLocType.CONSTANT:
                asm += ctx.put_value_in_free_register(rhs_val)
                loc_r = get_triple_loc(rhs_val, ctx)
                assert loc_r.typ == TripleLocType.REGISTER
            assert var_val.typ == TripleValueType.VAR_ASSIGN, "Expected Assignment variable on LHS of Assign triple"
            var_loc: TripleLoc = get_triple_loc(var_val, ctx)
            write_asm(f"mov {get_triple_loc_str(var_loc)}, {get_triple_loc_str(loc_r)}")
            if var_loc.typ == TripleLocType.REGISTER:
                ctx.mark_variable_dirty(var_val.value)
            elif var_loc.typ != TripleLocType.IN_MEMORY_AT_LABEL:
                assert False, "Variable locations should only be in register or in memory"
            triple.loc = loc_r
            if loc_r.typ == TripleLocType.REGISTER:
                ctx.register_value_updated(loc_r.value, TripleValue(TripleValueType.VAR_REF, var_val.value))
        case TripleType.LABEL:
            write_asm(f"_L{triple.index}:")
            ctx.flush_registers(do_save=False)
        case TripleType.IF_COND:
            cond_val: TripleValue = triple.l_val
            used_values.append(cond_val)
            goto_val: TripleValue = triple.r_val
            assert goto_val.typ == TripleValueType.TRIPLE_TARGET and goto_val.value.typ == TripleType.LABEL, "Expected IF to point to LABEL"
            goto_triple = goto_val.value
            if cond_val.typ == TripleValueType.TRIPLE_REF and cond_val.value.flags & TF_BOOL_FORWARDED > 0:
                # If this if statements references a bool forwarded triple, we don't need to compare
                write_asm(f"j{CMP_OP_INSTR_MAP[INVERT_CMP_OP[cond_val.value.op]]} _L{goto_triple.index}")
            else:
                cond_loc: TripleLoc = get_triple_loc(cond_val, ctx)
                if cond_loc.typ not in [TripleLocType.REGISTER, TripleLocType.IN_MEMORY_AT_LABEL]:
                    asm += ctx.put_value_in_free_register(cond_val)
                    cond_loc = get_triple_loc(cond_val, ctx)
                write_asm(f"cmp {get_triple_loc_str(cond_loc)}, 0")
                write_asm(f"je _L{goto_triple.index}")
        case TripleType.GOTO:
            goto_val: TripleValue = triple.l_val
            assert goto_val.typ == TripleValueType.TRIPLE_TARGET and goto_val.value.typ == TripleType.LABEL, "Expected IF to point to LABEL"
            goto_triple = goto_val.value
            write_asm(f"jmp _L{goto_triple.index}")
        case TripleType.ARG:
            next_reg = ctx.next_arg()
            asm += ctx.put_value_in_register(next_reg, triple.l_val)
        case TripleType.SYSCALL:
            s_num_val: TripleValue = triple.l_val
            asm += ctx.put_value_in_register(RAX_INDEX, s_num_val)
            write_asm("syscall")
            ctx.reset_args()
            ctx.flush_registers(do_save=False)
            ctx.update_reg_triple(RAX_INDEX, triple)
            triple.loc = TripleLoc(TripleLocType.REGISTER, value=RAX_INDEX)
        case TripleType.LOAD:
            ptr_val: TripleValue = triple.l_val
            ptr_loc: TripleLoc = get_triple_loc(ptr_val, ctx)
            if ptr_loc.typ != TripleLocType.REGISTER:
                asm += ctx.put_value_in_free_register(ptr_val)
                ptr_loc = get_triple_loc(ptr_val, ctx)
                assert ptr_loc.typ == TripleLocType.REGISTER, "Expected pointer to be in register"
            asm += ctx.save_value_in_register(ptr_loc.value)
            write_asm(f"movzx {get_triple_loc_str(ptr_loc)}, {ASM_SIZE_WORDS[triple.size]} [{get_triple_loc_str(ptr_loc)}]")
            ctx.update_reg_triple(ptr_loc.value, triple)
            triple.loc = ptr_loc
        case TripleType.STORE:
            ptr_val: TripleValue = triple.l_val
            ptr_loc: TripleLoc = get_triple_loc(ptr_val, ctx)
            if ptr_loc.typ != TripleLocType.REGISTER:
                asm += ctx.put_value_in_free_register(ptr_val)
                ptr_loc = get_triple_loc(ptr_val, ctx)
            assert ptr_loc.typ == TripleLocType.REGISTER, "Expected pointer to be in register"
            exp_val: TripleValue = triple.r_val
            exp_loc: TripleLoc = get_triple_loc(exp_val, ctx)
            if exp_loc.typ not in [TripleLocType.CONSTANT, TripleLocType.REGISTER]:
                asm += ctx.put_value_in_free_register(exp_val)
                exp_loc = get_triple_loc(exp_val, ctx)
                assert exp_loc.typ == TripleLocType.REGISTER, "Expected value to be in register"
            write_asm(f"mov {ASM_SIZE_WORDS[triple.size]} [{get_triple_loc_str(ptr_loc)}], {get_triple_loc_str(exp_loc, size=triple.size)}")
        case TripleType.REGMOVE:
            assert False, "Not implemented"
        case _:
            assert False, f"Unhandled Triple Type {triple.typ.name}"

    for v in used_values:
        ctx.value_used(v)

    return asm

def triples_to_asm(trips:List[Triple], trip_ctx:TripleContext, no_comments=False):
    asm = "DEFAULT REL\n\tsegment .text\n"
    # with open('print_d.asm', 'r') as f:
    #     asm += f.read() + '\n'

    asm += "\tglobal _main\n"
    asm += "_main:\n"

    ctx = ASMContext()
    ctx.build_var_table(trip_ctx)

    for t in trips:
        asm += convert_triple_to_asm(t, ctx, trip_ctx, no_comments)

    asm += "\txor rax,rax\n"
    asm += "\tret\n"

    did_segment = False

    if len(ctx.var_table) > 0:
        asm += "\n\tsegment .bss\n"
        did_segment = True
        for v,loc in ctx.var_table.items():
            asm += f"{loc.value}: resb 8\n"
    
    if len(ctx.buffer_table) > 0:
        if not did_segment:
            asm += "\n\tsegment .bss\n"
        for b,(sz, loc) in ctx.buffer_table.items():
            asm += f"{b}: resb {sz}\n"

    if len(ctx.string_table) > 0:
        asm += "\n\tsegment .data\n"
        for s, labl in ctx.string_table.items():
            asm += f"{labl}: db `{s.encode('unicode_escape').decode('utf-8')}`, 0\n"


    return asm