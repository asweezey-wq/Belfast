from belfast_data import *

class Buffer:

    def __init__(self, size) -> None:
        self.size = size
        self.rsp_offset = None

class TripleContext:

    def __init__(self):
        self.declared_vars: Set[str] = set()
        self.globals : Set[str] = set()
        self.functions = {}
        self.func_flags = {}
        self.function_ctx = {}
        self.buffers: Dict[str, int] = {}
        self.local_buffers: List[Buffer] = []
        self.buffer_offs = 0
        self.string_offs = 0
        self.strings: Dict[str, str] = {}
        self.register_alloc: Dict[TripleValue, int] = {}
        self.val_liveness : Dict[TripleValue, Set[int]] = {}
        self.spilled_values : Dict[TripleValue, int] = {}
        self.memory_spill_register = None
        self.active_break_label = None
        self.active_continue_label = None
        self.function_return_label = None
        self.function_return_var = None
        self.ctx_name = ''
        self.has_generated_print_code = False

    def variable_exists(self, name:str):
        return name in self.declared_vars or name in self.globals

    def declare_variable(self, name:str):
        self.declared_vars.add(name)

    def declare_function(self, name:str, flags: int, trips: List[Triple], trip_ctx: 'TripleContext'):
        self.functions[name] = trips
        self.func_flags[name] = flags
        self.function_ctx[name] = trip_ctx

    def create_subctx(self):
        tctx = TripleContext()
        tctx.buffers.update(self.buffers)
        tctx.strings.update(self.strings)
        tctx.string_offs = self.string_offs + len(self.strings)
        tctx.buffer_offs = self.buffer_offs + len(self.buffers)
        tctx.declared_vars.update(self.declared_vars)
        tctx.active_continue_label = self.active_continue_label
        tctx.active_break_label = self.active_break_label
        tctx.function_return_label = self.function_return_label
        tctx.function_return_var = self.function_return_var
        tctx.globals = self.globals
        return tctx

    def return_from_subctx(self, subctx: 'TripleContext'):
        self.buffers.update(subctx.buffers)
        self.strings.update(subctx.strings)

    def allocate_buffer(self, amt: int):
        name = f'_BUF{len(self.buffers) + self.buffer_offs}'
        self.buffers[name] = amt
        return name

    def allocate_local_buffer(self, amt: int):
        buf = Buffer(amt)
        self.local_buffers.append(buf)
        return buf

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
            if index in s and v in self.register_alloc:
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
    ret_label = Triple(TripleType.LABEL, None, None, None, uid=triple_uid())
    ctx.function_return_label = ret_label
    ctx.function_return_var = "$main_return"
    trips = []
    for a in ast_list:
        t, _ = ast_to_triples(a, ctx)
        trips.extend(t)
    trips.append(Triple(TripleType.ASSIGN, None, create_var_assign_value(ctx.function_return_var), create_const_value(0), uid=triple_uid()))
    trips.append(ret_label)
    trips.append(Triple(TripleType.RETURN, None, create_var_ref_value(ctx.function_return_var), None, uid=triple_uid()))
    return trips, ctx

def get_call_graph(trips: List[Triple], funs: Dict[str, List[Triple]], visited_funs=()):
    vis = set(visited_funs)
    new_funs = []
    for t in trips:
        if t.typ == TripleType.CALL:
            assert t.l_val.value in funs
            if t.l_val.value not in vis:
                new_funs.append(t.l_val.value)
                vis.add(t.l_val.value)
    ret_funs = set()
    for t in new_funs:
        ret_funs.update(get_call_graph(funs[t], funs, tuple(vis)))
        ret_funs.add(t)
    return ret_funs

def ast_to_triples(ast:ASTNode_Base, ctx:TripleContext):
    triples = []
    trip_val:TripleValue = TripleValue(TripleValueType.UNKNOWN, 0)
    match ast.typ:
        case ASTType.NUMBER:
            trip_val = create_const_value(ast.num_value)
        case ASTType.STRING:
            labl = ctx.allocate_string(ast.ident_str)
            trip_val = TripleValue(TripleValueType.STRING_REF, labl)
        case ASTType.BINARY_OP:
            l_trips, l_trip_val = ast_to_triples(ast.l_ast, ctx)
            r_trips, r_trip_val = ast_to_triples(ast.r_ast, ctx)
            op = TOKEN_OP_MAP[ast.value.typ]
            if op == Operator.LOGICAL_AND:
                var_name = f"_T{len(triples)}_ss"
                var_assign = create_var_assign_value(var_name)
                var_ref = create_var_ref_value(var_name)
                short_circuit_label = Triple(TripleType.LABEL, None, None, None, uid=triple_uid())
                end_label = Triple(TripleType.LABEL, None, None, None, uid=triple_uid())
                triples.extend(l_trips)
                triples.append(Triple(TripleType.IF_COND, Operator.NE, l_trip_val, create_target_value(short_circuit_label), uid=triple_uid()))
                triples.extend(r_trips)
                triples.append(Triple(TripleType.BINARY_OP, Operator.NE, r_trip_val, create_const_value(0), uid=triple_uid()))
                triples.append(Triple(TripleType.ASSIGN, None, var_assign, create_tref_value(triples[-1]), uid=triple_uid()))
                triples.append(Triple(TripleType.GOTO, None, create_target_value(end_label), None, uid=triple_uid()))
                triples.append(short_circuit_label)
                triples.append(Triple(TripleType.ASSIGN, None, var_assign, create_const_value(0), uid=triple_uid()))
                triples.append(end_label)
                trip_val = var_ref
            elif op == Operator.LOGICAL_OR:
                var_name = f"_T{len(triples)}_ss"
                var_assign = create_var_assign_value(var_name)
                var_ref = create_var_ref_value(var_name)
                short_circuit_label = Triple(TripleType.LABEL, None, None, None, uid=triple_uid())
                end_label = Triple(TripleType.LABEL, None, None, None, uid=triple_uid())
                triples.extend(l_trips)
                triples.append(Triple(TripleType.IF_COND, Operator.EQ, l_trip_val, create_target_value(short_circuit_label), uid=triple_uid()))
                triples.extend(r_trips)
                triples.append(Triple(TripleType.BINARY_OP, Operator.NE, r_trip_val, create_const_value(0), uid=triple_uid()))
                triples.append(Triple(TripleType.ASSIGN, None, var_assign, create_tref_value(triples[-1]), uid=triple_uid()))
                triples.append(Triple(TripleType.GOTO, None, create_target_value(end_label), None, uid=triple_uid()))
                triples.append(short_circuit_label)
                triples.append(Triple(TripleType.ASSIGN, None, var_assign, create_const_value(1), uid=triple_uid()))
                triples.append(end_label)
                trip_val = var_ref
            else:
                triples.extend(l_trips)
                triples.extend(r_trips)
                triples.append(Triple(TripleType.BINARY_OP,op=op, l_val=l_trip_val, r_val=r_trip_val, flags=TF_SIGNED, uid=triple_uid()))
                trip_val = create_tref_value(triples[-1])
        case ASTType.UNARY_OP:
            exp_trips, exp_trip_val = ast_to_triples(ast.ast_ref, ctx)
            triples.extend(exp_trips)
            op = TOKEN_OP_MAP[ast.value.typ]
            if op == Operator.MINUS:
                # Unary minus is a negation
                op = Operator.NEGATE
            
            if op == Operator.LOGICAL_NOT:
                triples.append(Triple(TripleType.BINARY_OP, op=Operator.EQ, l_val=exp_trip_val, r_val=TripleValue(TripleValueType.CONSTANT, 0), uid=triple_uid()))
            else:
                triples.append(Triple(TripleType.UNARY_OP, op=op, l_val=exp_trip_val, r_val=None, uid=triple_uid()))
            trip_val = create_tref_value(triples[-1])
        case ASTType.PRINT:
            exp_trips, exp_trip_val = ast_to_triples(ast.ast_ref, ctx)
            triples.extend(exp_trips)
            triples.append(Triple(TripleType.PRINT, op=Keyword.PRINT, l_val=exp_trip_val, r_val=None, uid=triple_uid()))
            trip_val = None
        case ASTType.VAR_DECL:
            ctx.declare_variable(ast.ident_str)
        case ASTType.VAR_DECL_ASSIGN:
            ctx.declare_variable(ast.ident_str)
            trips, trip_val = ast_to_triples(ast.ast_ref, ctx)
            triples.extend(trips)
            triples.append(Triple(TripleType.ASSIGN, None, create_var_assign_value(ast.ident_str), trip_val, uid=triple_uid()))
        case ASTType.VAR_REF:
            if not ctx.variable_exists(ast.ident_str):
                # TODO: Move this to parsing step?
                compiler_error(ast.value.loc, f"Use of undeclared variable {ast.ident_str}")
            if ast.ident_str in ctx.declared_vars:
                trip_val = create_var_ref_value(ast.ident_str)
            elif ast.ident_str in ctx.globals:
                trip_val = create_global_ref_value(ast.ident_str)
        case ASTType.BUFFER_ALLOC:
            trip_val = TripleValue(TripleValueType.LOCAL_BUFFER_REF, ctx.allocate_local_buffer(ast.num_value))
        case ASTType.ASSIGN:
            l_trips, l_trip_val = ast_to_triples(ast.l_ast, ctx)
            assert len(l_trips) == 0, "Multiple triples on Assign LHS not supported"
            if l_trip_val.typ == TripleValueType.GLOBAL_REF:
                r_trips, r_trip_val = ast_to_triples(ast.r_ast, ctx)
                triples.extend(r_trips)
                triples.append(Triple(TripleType.STORE, op=None, l_val=create_global_label_value(l_trip_val.value), r_val=r_trip_val, uid=triple_uid()))
            else:
                assert l_trip_val.typ == TripleValueType.VAR_REF, "Expected variable ref on LHS of Assign"
                r_trips, r_trip_val = ast_to_triples(ast.r_ast, ctx)
                triples.extend(r_trips)
                triples.append(Triple(TripleType.ASSIGN, op=None, l_val=create_var_assign_value(l_trip_val.value), r_val=r_trip_val, uid=triple_uid()))
            # trip_val = create_tref_value(triples[-1])
        case ASTType.IF:
            cond_trips, cond_val = ast_to_triples(ast.cond_ast, ctx)
            scoped_ctx = ctx.create_subctx()
            triples.extend(cond_trips)
            end_label_triple = Triple(TripleType.LABEL, None, None, None, uid=triple_uid())
            end_goto_triple = None
            if ast.else_ast_block or ast.else_if_ast:
                end_goto_triple = Triple(TripleType.LABEL, None, None, None, uid=triple_uid())
            triples.append(Triple(TripleType.IF_COND, op=Operator.NE, l_val=cond_val, r_val=create_target_value(end_label_triple), uid=triple_uid()))
            for a in ast.then_ast_block:
                a_trips, _ = ast_to_triples(a, scoped_ctx)
                triples.extend(a_trips)
            if end_goto_triple is not None:
                triples.append(Triple(TripleType.GOTO, None, create_target_value(end_goto_triple), None, uid=triple_uid()))
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
            ctx.return_from_subctx(scoped_ctx)
        case ASTType.WHILE:
            cond_trips, cond_val = ast_to_triples(ast.cond_ast, ctx)
            scoped_ctx = ctx.create_subctx()
            end_label_triple = Triple(TripleType.LABEL, None, None, None, uid=triple_uid())
            scoped_ctx.active_break_label = end_label_triple
            cond_eval_label = Triple(TripleType.LABEL, None, None, None, uid=triple_uid())
            scoped_ctx.active_continue_label = cond_eval_label
            triples.append(cond_eval_label)
            triples.extend(cond_trips)
            triples.append(Triple(TripleType.IF_COND, op=Operator.NE, l_val=cond_val, r_val=create_target_value(end_label_triple), uid=triple_uid()))
            for a in ast.do_ast_block:
                a_trips, _ = ast_to_triples(a, scoped_ctx)
                triples.extend(a_trips)
            triples.append(Triple(TripleType.GOTO, op=None, l_val=create_target_value(cond_eval_label), r_val=None, uid=triple_uid()))
            triples.append(end_label_triple)
            ctx.return_from_subctx(scoped_ctx)
        case ASTType.DO_WHILE:
            loop_start_label = Triple(TripleType.LABEL, None, None, None, uid=triple_uid())
            triples.append(loop_start_label)
            scoped_ctx = ctx.create_subctx()
            end_label_triple = Triple(TripleType.LABEL, None, None, None, uid=triple_uid())
            scoped_ctx.active_break_label = end_label_triple
            cond_eval_label = Triple(TripleType.LABEL, None, None, None, uid=triple_uid())
            scoped_ctx.active_continue_label = cond_eval_label
            for a in ast.do_ast_block:
                a_trips, _ = ast_to_triples(a, scoped_ctx)
                triples.extend(a_trips)
            cond_trips, cond_val = ast_to_triples(ast.cond_ast, ctx)
            triples.append(cond_eval_label)
            triples.extend(cond_trips)
            triples.append(Triple(TripleType.IF_COND, op=Operator.EQ, l_val=cond_val, r_val=create_target_value(loop_start_label), uid=triple_uid()))
            triples.append(end_label_triple)
            ctx.return_from_subctx(scoped_ctx)
        case ASTType.BREAK:
            if ctx.active_break_label:
                triples.append(Triple(TripleType.GOTO, op=None, l_val=create_target_value(ctx.active_break_label), r_val=None, uid=triple_uid()))
            else:
                compiler_error(ast.value.loc, "Break statement must be inside of a loop")
        case ASTType.CONTINUE:
            if ctx.active_continue_label:
                triples.append(Triple(TripleType.GOTO, op=None, l_val=create_target_value(ctx.active_continue_label), r_val=None, uid=triple_uid()))
            else:
                compiler_error(ast.value.loc, "Continue statement must be inside of a loop")
        case ASTType.SYSCALL:
            syscall_num_val = ast.args[0]
            s_trips, s_val = ast_to_triples(syscall_num_val, ctx)
            triples.extend(s_trips)
            assert s_val.typ == TripleValueType.CONSTANT
            arg_vals = []
            for a in ast.args[1:]:
                a_trips, a_val = ast_to_triples(a, ctx)
                triples.extend(a_trips)
                arg_vals.append(a_val)
            for i,a in enumerate(arg_vals):
                triples.append(Triple(TripleType.ARG, None, a, None, data=i, flags=TF_SYSCALL, uid=triple_uid()))
            triples.append(Triple(TripleType.SYSCALL, op=None, l_val=s_val, r_val=None, data=len(ast.args)-1, uid=triple_uid()))
            triples.append(Triple(TripleType.NOP_REF, None, create_tref_value(triples[-1]), None, flags=TF_DONT_FORWARD, uid=triple_uid()))
            trip_val = create_tref_value(triples[-1])
        case ASTType.LOAD:
            ptr_exp_trips, ptr_exp_val = ast_to_triples(ast.ptr_exp, ctx)
            triples.extend(ptr_exp_trips)
            triples.append(Triple(TripleType.LOAD, None, ptr_exp_val, None, size=ast.size, uid=triple_uid()))
            if ast.signed:
                triples[-1].flags |= TF_SIGNED
            trip_val = create_tref_value(triples[-1])
        case ASTType.STORE:
            ptr_exp_trips, ptr_exp_val = ast_to_triples(ast.ptr_exp, ctx)
            triples.extend(ptr_exp_trips)
            val_exp_trips, val_exp_val = ast_to_triples(ast.val_exp, ctx)
            triples.extend(val_exp_trips)
            triples.append(Triple(TripleType.STORE, None, ptr_exp_val, val_exp_val, size=ast.size, uid=triple_uid()))
        case ASTType.FUN_DEF:
            fun_name = ast.fun_name
            args = ast.args
            fun_triples = []
            scoped_ctx = TripleContext()
            scoped_ctx.buffer_offs = len(ctx.buffers) + ctx.buffer_offs
            scoped_ctx.string_offs = len(ctx.strings) + ctx.string_offs
            scoped_ctx.declared_vars.update(args)
            scoped_ctx.globals = ctx.declared_vars
            scoped_ctx.func_flags = ctx.func_flags
            scoped_ctx.functions = ctx.functions
            scoped_ctx.ctx_name = fun_name
            end_label = Triple(TripleType.LABEL, None, None, None, uid=triple_uid())
            scoped_ctx.function_return_label = end_label
            scoped_ctx.function_return_var = f"${fun_name}_return"
            for i,a in enumerate(args):
                fun_triples.append(Triple(TripleType.FUN_ARG_IN, None, create_var_assign_value(a), None, data=i, uid=triple_uid()))
            for a in ast.body:
                a_trips, _ = ast_to_triples(a, scoped_ctx)
                fun_triples.extend(a_trips)
            fun_triples.append(Triple(TripleType.ASSIGN, None, create_var_assign_value(scoped_ctx.function_return_var), create_const_value(0), uid=triple_uid()))
            fun_triples.append(end_label)
            fun_triples.append(Triple(TripleType.RETURN, None, create_var_ref_value(scoped_ctx.function_return_var), None, uid=triple_uid()))
            ctx.buffer_offs += len(scoped_ctx.buffers)
            ctx.string_offs += len(scoped_ctx.strings)
            ctx.declare_function(fun_name, ast.fun_flags, fun_triples, scoped_ctx)
        case ASTType.FUN_CALL:
            fun_name = ast.fun_name
            arg_vals = []
            for i in range(len(ast.args)):
                arg_trips, arg_val = ast_to_triples(ast.args[i], ctx)
                triples.extend(arg_trips)
                arg_vals.append(arg_val)
            for i,a in enumerate(arg_vals):
                triples.append(Triple(TripleType.ARG, None, a, None, data=i, uid=triple_uid()))
            triples.append(Triple(TripleType.CALL, None, TripleValue(TripleValueType.FUN_LABEL, fun_name), None, data=len(ast.args), uid=triple_uid()))
            triples.append(Triple(TripleType.NOP_REF, None, create_tref_value(triples[-1]), None, flags=TF_DONT_FORWARD, uid=triple_uid()))
            trip_val = create_tref_value(triples[-1])
        case ASTType.RETURN:
            assert ctx.function_return_label is not None and ctx.function_return_var is not None
            exp_trips, exp_val = ast_to_triples(ast.ast_ref, ctx)
            triples.extend(exp_trips)
            triples.append(Triple(TripleType.ASSIGN, None, create_var_assign_value(ctx.function_return_var), exp_val, uid=triple_uid()))
            triples.append(Triple(TripleType.GOTO, None, create_target_value(ctx.function_return_label), None, uid=triple_uid()))
        case _:
            assert False, f"Unhandled AST Type {ast.typ.name}"
    return triples, trip_val

def create_tref_value(t: Triple):
    return TripleValue(TripleValueType.TRIPLE_REF, t)

def create_target_value(t: Triple):
    return TripleValue(TripleValueType.TRIPLE_TARGET, t)

def create_const_value(i: int):
    return TripleValue(TripleValueType.CONSTANT, i)

def create_register_value(reg: int):
    return TripleValue(TripleValueType.REGISTER, reg)

def create_var_ref_value(var: str):
    return TripleValue(TripleValueType.VAR_REF, var)

def create_global_ref_value(var: str):
    return TripleValue(TripleValueType.GLOBAL_REF, var)

def create_global_label_value(var: str):
    return TripleValue(TripleValueType.GLOBAL_LABEL, var)

def create_var_assign_value(var: str):
    return TripleValue(TripleValueType.VAR_ASSIGN, var)

def triple_value_reference_value(tv: TripleValue, ref: TripleValue):
    if tv is not None and ref is not None:
        if triple_values_equal(tv, ref):
            return tv
        elif tv.typ == TripleValueType.ADDRESS_COMPUTE:
            if triple_values_equal(tv.value[0], ref):
                return tv.value[0]
            elif triple_values_equal(tv.value[1], ref):
                return tv.value[1]
    return None

def get_triple_values(tv: TripleValue):
    if tv.typ == TripleValueType.ADDRESS_COMPUTE:
        return tv.value[0], tv.value[1]
    return (tv,)

# Returns true if the triple param contains a TripleRef value that references the ref_trip param
def triple_references_triple(triple: Triple, ref_trip: Triple):
    tref = create_tref_value(ref_trip)
    return triple_value_reference_value(triple.l_val, tref) is not None or triple_value_reference_value(triple.r_val, tref) is not None

def get_triple_reference_value(triple: Triple, ref_trip: Triple):
    tref = create_tref_value(ref_trip)
    lr = triple_value_reference_value(triple.l_val, tref)
    if lr:
        return lr
    return triple_value_reference_value(triple.r_val, tref)

def get_triple_label_reference_value(triple: Triple, ref_trip: Triple):
    targ = create_target_value(ref_trip)
    lr = triple_value_reference_value(triple.l_val, targ)
    if lr:
        return lr
    return triple_value_reference_value(triple.r_val, targ)

def triple_references_var(triple: Triple, var: str):
    varref = create_var_ref_value(var)
    return triple_value_reference_value(triple.l_val, varref) is not None or triple_value_reference_value(triple.r_val, varref) is not None

def triple_assigns_var(triple: Triple, var: str):
    varassign = create_var_assign_value(var)
    return triple_value_reference_value(triple.l_val, varassign) is not None or triple_value_reference_value(triple.r_val, varassign) is not None

def is_value_dataref(tv: TripleValue):
    return tv.typ in [TripleValueType.VAR_REF, TripleValueType.REGISTER, TripleValueType.TRIPLE_REF, TripleValueType.ADDRESS_COMPUTE]

def get_triple_referenced_values(triple: Triple):
    vals: Set[TripleValue] = set()
    if triple.typ != TripleType.ASSIGN and triple.typ != TripleType.REGMOVE:
        if triple.l_val is not None and is_value_dataref(triple.l_val):
            vals.update([v for v in get_triple_values(triple.l_val) if is_value_dataref(v)])
    if triple.r_val is not None:
        vals.update([v for v in get_triple_values(triple.r_val) if is_value_dataref(v)])
    if triple.typ == TripleType.SYSCALL:
        pass
    elif triple.typ == TripleType.BINARY_OP:
        match triple.op:
            case Operator.DIVIDE | Operator.MODULUS:
                vals.add(create_register_value(RAX_INDEX))
                vals.add(create_register_value(RDX_INDEX))
    return vals
