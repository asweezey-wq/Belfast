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