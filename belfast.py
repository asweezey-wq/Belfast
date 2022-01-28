from ast import arg
import os, sys
from belfast_data import *
from belfast_triples import *
from belfast_triples_opt import optimize_triples
from belfast_x86 import convert_function_to_asm, get_asm_header, get_asm_footer, optimize_x86, output_x86_trips_to_str
import re
import copy

keyword_regex = r'(?:(' + ('|'.join(KEYWORD_NAMES.keys())) + r')(?=\s|$|;))'
builtins_regex = r'(' + ('|'.join(BUILTINS_NAMES.keys())) + r')'
lang_regex = keyword_regex + r'|' + builtins_regex + r'|(0x[a-fA-F0-9]+)|(".*")|(\'(?:.|\\[nt0])\')|(-?[0-9]+)|(\|\||&&|<<|>>|[<>!=]=|[\+\-\*\/\;\(\)\%\>\<\=\,\&\|\^!~])|([_A-Za-z][_A-Za-z0-9]*)|(\S+)'
# print(lang_regex)
regex_type_map = [
    TokenType.KEYWORD,
    TokenType.IDENTIFIER,
    TokenType.NUMBER
]

def tokenize_string(filepath:str, input_string: str):
    index = 0
    lr = re.compile(lang_regex)
    tokens = []
    line_num = 1
    for l in input_string.splitlines():
        loc = (filepath, line_num, 1)
        if not l.startswith('//'):
            if '//' in l:
                l = l.split('//')[0]
            for m in lr.finditer(l):
                t = m.groups()
                loc = (filepath, line_num, m.start() + 1)
                typ = TokenType.UNKNOWN
                val = None
                if t[0] is not None:
                    if t[0] in KEYWORD_NAMES:
                        typ = TokenType.KEYWORD
                        val = KEYWORD_NAMES[t[0]]
                    else:
                        compiler_error(loc, f"Invalid keyword {t[0]}")
                elif t[1] is not None:
                    if t[1] in BUILTINS_NAMES:
                        typ = TokenType.KEYWORD
                        val = BUILTINS_NAMES[t[1]]
                    else:
                        compiler_error(loc, f"Invalid builtin {t[1]}")
                elif t[3] is not None:
                    typ = TokenType.STRING
                    assert len(t[3]) >= 3, "Error in string literal regex"
                    string = t[3][1:-1]
                    val = string.encode('utf-8').decode('unicode_escape')
                elif t[4] is not None:
                    typ = TokenType.CHARACTER
                    assert len(t[4]) >= 3, "Error in character literal regex"
                    char = t[4][1:-1]
                    val = char.encode('utf-8').decode('unicode_escape')
                    if len(val) > 1:
                        compiler_error(loc, "Character literals can only contain a single character")
                elif t[7] is not None:
                    typ = TokenType.IDENTIFIER
                    val = t[7]
                elif t[5] is not None:
                    typ = TokenType.NUMBER
                    val = int(t[5])
                elif t[2] is not None:
                    typ = TokenType.NUMBER
                    val = int(t[2], base=16)
                elif t[6] is not None:
                    match t[6]:
                        case ';':
                            typ = TokenType.SEMICOLON
                        case '+':
                            typ = TokenType.PLUS
                        case '-':
                            typ = TokenType.MINUS
                        case '*':
                            typ = TokenType.MULTIPLY
                        case '/':
                            typ = TokenType.DIVIDE
                        case '%':
                            typ = TokenType.MODULUS
                        case '=':
                            typ = TokenType.ASSIGN
                        case '(':
                            typ = TokenType.OPEN_PAREN
                        case ')':
                            typ = TokenType.CLOSE_PAREN
                        case '>=':
                            typ = TokenType.GE
                        case '<=':
                            typ = TokenType.LE
                        case '!=':
                            typ = TokenType.NE
                        case '>':
                            typ = TokenType.GT
                        case '<':
                            typ = TokenType.LT
                        case '==':
                            typ = TokenType.EQ
                        case ',':
                            typ = TokenType.COMMA
                        case '<<':
                            typ = TokenType.SHIFT_LEFT
                        case '>>':
                            typ = TokenType.SHIFT_RIGHT
                        case '&':
                            typ = TokenType.BITWISE_AND
                        case '|':
                            typ = TokenType.BITWISE_OR
                        case '^':
                            typ = TokenType.BITWISE_XOR
                        case '~':
                            typ = TokenType.BITWISE_NOT
                        case '!':
                            typ = TokenType.LOGICAL_NOT
                        case '||':
                            typ = TokenType.LOGICAL_OR
                        case '&&':
                            typ = TokenType.LOGICAL_AND
                        case _:
                            assert False, f"Unhandled token '{t[6]}'"
                elif t[8] is not None:
                    compiler_error(loc, f"Invalid token '{t[8]}'")
                    assert False, "Empty regex match"
                if typ != TokenType.UNKNOWN:
                    tokens.append(Token(typ=typ, loc=loc, value=val))
        
            tokens.append(Token(TokenType.EOL, loc, None))
        
        line_num += 1

    tokens.append(Token(TokenType.EOF, loc, None))
    return tokens

def parse_tokens(tokens: List[Token]):
    index = 0
    def expect_token(t:TokenType):
        nonlocal index
        tok = tokens[index]
        if tok.typ != t:
            compiler_error(tok.loc, f"Expected token {t.name}, got {tok.typ.name}")
        index += 1
        return tok
    def expect_keyword(k:Keyword):
        nonlocal index
        tok = tokens[index]
        if tok.typ != TokenType.KEYWORD:
            compiler_error(tok.loc, f"Expected keyword {k.name}, got {tok.typ.name}")
        elif tok.value != k:
            compiler_error(tok.loc, f"Expected keyword {k.name}, got keyword {tok.value.name}")
        index += 1
        return tok

    ast = []

    declared_vars: Set[str] = set()

    declared_funs: Dict[str, ASTNode_Base] = {}
    defining_function = False
    defining_fun_body = []
    defining_function_args = []

    declared_consts : Dict[str, ASTNode_Base] = {}

    def evaluate_const(exp: ASTNode_Base):
        match exp.typ:
            case ASTType.NUMBER:
                return exp.num_value
            case ASTType.BINARY_OP:
                lhs = evaluate_const(exp.l_ast)
                rhs = evaluate_const(exp.r_ast)
                match TOKEN_OP_MAP[exp.value.typ]:
                    case Operator.PLUS:
                        return lhs + rhs
                    case Operator.MINUS:
                        return lhs - rhs
                    case Operator.MULTIPLY:
                        return lhs * rhs
                    case Operator.DIVIDE:
                        return lhs // rhs
                    case Operator.MODULUS:
                        return lhs % rhs
                    case Operator.SHIFT_LEFT:
                        return lhs << rhs
                    case Operator.SHIFT_RIGHT:
                        return lhs >> rhs
                    case _:
                        compiler_error(exp.value.loc, f"Unsupported operator {exp.value.typ.name} in const expression")
            case _:
                compiler_error(exp.value.loc, f"Invalid token {exp.value.typ.name} in const expression")

    def parse_var_decl():
        var_tok = expect_keyword(Keyword.VAR)
        ident_tok = expect_token(TokenType.IDENTIFIER)
        assert isinstance(ident_tok.value, str), "Expected string identifier value"
        if ident_tok.value in declared_vars:
            compiler_error(ident_tok.loc, f"Redeclaration of existing variable {ident_tok.value}")
        declared_vars.add(ident_tok.value)
        tok = tokens[index]
        if tok.typ == TokenType.ASSIGN:
            expect_token(TokenType.ASSIGN)
            exp = parse_expression()
            return ASTNode_VardecAssign(ASTType.VAR_DECL_ASSIGN, var_tok, ident_tok.value, exp)
        return ASTNode_Ident(ASTType.VAR_DECL, var_tok, ident_tok.value)

    def parse_print_stmt():
        print_tok = expect_keyword(Keyword.PRINT)
        exp = parse_expression()
        return ASTNode_Single(ASTType.PRINT, value=print_tok, ast_ref = exp)

    def parse_if_stmt(elif_tok=False):
        nonlocal index
        if_tok = expect_keyword(Keyword.IF if not elif_tok else Keyword.ELIF)
        exp = parse_expression()
        then_tok = expect_keyword(Keyword.THEN)
        body: List[ASTNode_Base] = []
        while True:
            tok = tokens[index]
            if tokens[index].typ == TokenType.EOL:
                index += 1
                continue
            if tok.typ == TokenType.EOF or (tok.typ == TokenType.KEYWORD and tok.value in [Keyword.END, Keyword.ELSE, Keyword.ELIF]):
                break
            s = parse_statement()
            if s and s.typ != ASTType.NONE:
                body.append(s)

        tok = tokens[index]
        if tok.typ == TokenType.KEYWORD:
            if tok.value == Keyword.ELSE:
                else_body: List[ASTNode_Base] = []
                expect_keyword(Keyword.ELSE)
                while True:
                    tok = tokens[index]
                    if tokens[index].typ == TokenType.EOL:
                        index += 1
                        continue
                    if tok.typ == TokenType.EOF or (tok.typ == TokenType.KEYWORD and tok.value == Keyword.END):
                        break
                    s = parse_statement()
                    if s and s.typ != ASTType.NONE:
                        else_body.append(s)
                expect_keyword(Keyword.END)
                return ASTNode_If(ASTType.IF, if_tok, exp, body, else_body)
            elif tok.value == Keyword.ELIF:
                elif_stmt = parse_if_stmt(elif_tok=True)
                return ASTNode_If(ASTType.IF, if_tok, exp, body, None, elif_stmt)
            elif tok.value == Keyword.END:
                expect_keyword(Keyword.END)
                return ASTNode_If(ASTType.IF, if_tok, exp, body)
            else:
                assert False, "This is a bug in the parsing of the if statement body"
        else:
            compiler_error(tok.loc, f"Expected END, ELSE, or ELIF at the end of IF statement, got {tok.typ.name}")

    def parse_while_loop():
        nonlocal index
        tok = expect_keyword(Keyword.WHILE)
        cond_exp = parse_expression()
        expect_keyword(Keyword.DO)
        body: List[ASTNode_Base] = []
        while True:
            tok = tokens[index]
            if tokens[index].typ == TokenType.EOL:
                index += 1
                continue
            if tok.typ == TokenType.EOF or (tok.typ == TokenType.KEYWORD and tok.value == Keyword.END):
                break
            s = parse_statement()
            if s and s.typ != ASTType.NONE:
                body.append(s)
        expect_keyword(Keyword.END)
        return ASTNode_While(ASTType.WHILE, tok, cond_exp, body)

    def parse_syscall():
        nonlocal index
        tok = expect_keyword(Keyword.SYSCALL)
        expect_token(TokenType.OPEN_PAREN)
        args = []
        while True:
            tok = tokens[index]
            if tok.typ == TokenType.EOF:
                expect_token(TokenType.CLOSE_PAREN)
                break
            elif tok.typ == TokenType.EOL:
                index += 1
                continue
            elif tok.typ == TokenType.CLOSE_PAREN:
                expect_token(TokenType.CLOSE_PAREN)
                break
            else:
                args.append(parse_expression())
                tok = tokens[index]
                if tok.typ == TokenType.COMMA:
                    expect_token(TokenType.COMMA)
                elif tok.typ == TokenType.CLOSE_PAREN:
                    continue
                else:
                    expect_token(TokenType.COMMA)
                    break
        return ASTNode_Syscall(ASTType.SYSCALL, tok, args)

    def parse_buffer_alloc():
        tok = expect_keyword(Keyword.BUFFER)
        expect_token(TokenType.OPEN_PAREN)
        exp = parse_expression()
        expect_token(TokenType.CLOSE_PAREN)
        return ASTNode_Number(ASTType.BUFFER_ALLOC, tok, evaluate_const(exp))

    def parse_load():
        tok = tokens[index]
        assert tok.typ == TokenType.KEYWORD and tok.value in [Keyword.LOAD8, Keyword.LOAD64], "Shouldnt be here"
        expect_keyword(tok.value)
        expect_token(TokenType.OPEN_PAREN)
        exp = parse_expression()
        expect_token(TokenType.CLOSE_PAREN)
        sz = KW_SIZE_MAP[tok.value]
        return ASTNode_Load(ASTType.LOAD, tok, exp, sz)

    def parse_store():
        tok = tokens[index]
        assert tok.typ == TokenType.KEYWORD and tok.value in [Keyword.STORE8, Keyword.STORE64], "Shouldnt be here"
        expect_keyword(tok.value)
        expect_token(TokenType.OPEN_PAREN)
        exp = parse_expression()
        expect_token(TokenType.COMMA)
        exp2 = parse_expression()
        expect_token(TokenType.CLOSE_PAREN)
        sz = KW_SIZE_MAP[tok.value]
        return ASTNode_Store(ASTType.STORE, tok, exp, exp2, sz)

    def parse_const():
        expect_keyword(Keyword.CONST)
        ident_tok = expect_token(TokenType.IDENTIFIER)
        expect_token(TokenType.ASSIGN)
        exp = parse_expression()
        declared_consts[ident_tok.value] = exp

    def parse_function_def():
        nonlocal index, defining_function, defining_fun_body, defining_function_args
        tok = expect_keyword(Keyword.FUN)
        if len(declared_vars):
            compiler_error(tok.loc, "Variables declared outside of function")
        
        declared_vars.clear()

        if defining_function:
            compiler_error(tok.loc, "Nested functions are not supported")
        ident_tok = expect_token(TokenType.IDENTIFIER)

        if ident_tok.value in declared_funs:
            compiler_error(tok.loc, f"Redefinition of existing function {ident_tok.value}")

        args = []
        while True:
            tok = tokens[index]
            if tok.typ != TokenType.IDENTIFIER:
                break
            expect_token(TokenType.IDENTIFIER)
            args.append(tok.value)
        expect_keyword(Keyword.DO)

        defining_function = True
        defining_fun_body = []
        defining_function_args = args

        while True:
            tok = tokens[index]
            if tokens[index].typ == TokenType.EOL:
                index += 1
                continue
            if tok.typ == TokenType.EOF or (tok.typ == TokenType.KEYWORD and tok.value == Keyword.END):
                break
            s = parse_statement()
            if s and s.typ != ASTType.NONE:
                defining_fun_body.append(s)

        expect_keyword(Keyword.END)

        defining_function = False
        fundef = ASTNode_Fundef(ASTType.FUN_DEF, ident_tok, ident_tok.value, args, defining_fun_body)
        declared_funs[ident_tok.value] = fundef
        defining_fun_body = []
        defining_function_args = []

        declared_vars.clear()

        return fundef

    def parse_funcall(t: Token):
        nonlocal index
        assert t.typ == TokenType.IDENTIFIER and t.value in declared_funs
        expect_token(TokenType.OPEN_PAREN)
        func = declared_funs[t.value]
        num_expected_args = len(func.args)
        arg_exp = []
        while True:
            tok = tokens[index]
            if tok.typ == TokenType.CLOSE_PAREN or tok.typ == TokenType.EOF:
                break
            if tok.typ == TokenType.COMMA:
                index += 1
            arg_exp.append(parse_expression())
            tok = tokens[index]
        
        expect_token(TokenType.CLOSE_PAREN)
        if len(arg_exp) != num_expected_args:
            compiler_error(t.loc, f"Function {t.value} expected {num_expected_args}, got {len(arg_exp)}")
        
        return ASTNode_Funcall(ASTType.FUN_CALL, t, t.value, arg_exp)

    op_assoc = [
        [Operator.LOGICAL_AND, Operator.LOGICAL_OR],
        [Operator.BITWISE_AND, Operator.BITWISE_XOR, Operator.BITWISE_OR],
        [Operator.EQ, Operator.NE],
        [Operator.GE, Operator.GT, Operator.LE, Operator.LT],
        [Operator.SHIFT_LEFT, Operator.SHIFT_RIGHT],
        [Operator.PLUS, Operator.MINUS],
        [Operator.MULTIPLY, Operator.DIVIDE, Operator.MODULUS],
        # [Operator.ASSIGN],
    ]

    unary_ops = [Operator.MINUS, Operator.LOGICAL_NOT, Operator.BITWISE_NOT]

    def parse_base():
        tok = tokens[index]
        match tok.typ:
            case TokenType.OPEN_PAREN:
                expect_token(TokenType.OPEN_PAREN)
                exp = parse_expression()
                expect_token(TokenType.CLOSE_PAREN)
                return exp
            case TokenType.STRING:
                t = expect_token(TokenType.STRING)
                assert isinstance(t.value, str), "Expected string value in string token"
                return ASTNode_Ident(ASTType.STRING, value=t, ident_str=t.value)
            case TokenType.NUMBER:
                t = expect_token(TokenType.NUMBER)
                assert isinstance(t.value, int), "Expected int value in number token"
                return ASTNode_Number(ASTType.NUMBER, value=t, num_value=t.value)
            case TokenType.CHARACTER:
                t = expect_token(TokenType.CHARACTER)
                assert isinstance(t.value, str), "Expected char value in number token"
                return ASTNode_Number(ASTType.NUMBER, value=t, num_value=ord(t.value))
            case TokenType.IDENTIFIER:
                t = expect_token(TokenType.IDENTIFIER)
                if t.value in declared_vars:
                    return ASTNode_Ident(ASTType.VAR_REF, value=t, ident_str=t.value)
                elif defining_function and t.value in defining_function_args:
                    return ASTNode_Ident(ASTType.VAR_REF, value=t, ident_str=t.value)
                elif t.value in declared_funs:
                    return parse_funcall(t)
                elif t.value in declared_consts:
                    return declared_consts[t.value]
                else:
                    compiler_error(tok.loc, f"Reference to undefined variable '{t.value}'")
            case _:
                compiler_error(tok.loc, f"Unexpected token type {tok.typ.name}")

    def parse_kw():
        tok = tokens[index]
        if tok.typ == TokenType.KEYWORD:
            match tok.value:
                case Keyword.SYSCALL:
                    return parse_syscall()
                case Keyword.BUFFER:
                    return parse_buffer_alloc()
                case Keyword.STORE8 | Keyword.STORE64:
                    return parse_store()
                case Keyword.LOAD8 | Keyword.LOAD64:
                    return parse_load()

        return parse_base()

    def parse_assign():
        l_exp = parse_base()
        assert l_exp.typ == ASTType.VAR_REF, "Assign expected var on LHS"
        tok = tokens[index]
        assert tok.typ == TokenType.ASSIGN, "Assign expected '=' after variable"
        expect_token(TokenType.ASSIGN)
        return ASTNode_Assign(ASTType.ASSIGN, value=tok, l_ast=l_exp, r_ast=parse_expression())

    def parse_unary():
        tok = tokens[index]
        if tok.typ in TOKEN_OP_MAP and TOKEN_OP_MAP[tok.typ] in unary_ops:
            op_tok = expect_token(tok.typ)
            exp: ASTNode_Base = parse_unary()

            return ASTNode_Single(ASTType.UNARY_OP, op_tok, exp)
        else:
            return parse_kw()


    def parse_expression(level=0):
        if level == len(op_assoc):
            return parse_unary()
        l_exp = parse_expression(level + 1)
        while index < len(tokens):
            tok = tokens[index]
            if tok.typ in TOKEN_OP_MAP:
                op = TOKEN_OP_MAP[tok.typ]
                if op in op_assoc[level]:
                    op_tok = expect_token(tok.typ)
                    r_subexp = parse_expression(level + 1)
                    l_exp = ASTNode_BinaryOp(typ=ASTType.BINARY_OP, value=op_tok, l_ast=l_exp, r_ast=r_subexp)
                    continue
            break
        return l_exp

    def parse_include():
        tok = expect_keyword(Keyword.INCLUDE)
        file_tok = expect_token(TokenType.STRING)
        inc_a, inc_vars, inc_funs, inc_consts = file_to_ast(file_tok.value)
        ast.extend(inc_a)
        declared_vars.update(inc_vars)
        declared_funs.update(inc_funs)
        declared_consts.update(inc_consts)

    def parse_statement():
        tok = tokens[index]
        return_ast = None
        match tok.typ:
            case TokenType.KEYWORD:
                match tok.value:
                    case Keyword.VAR:
                        return_ast = parse_var_decl()
                    case Keyword.PRINT:
                        return_ast = parse_print_stmt()
                    case Keyword.IF:
                        return_ast = parse_if_stmt()
                    case Keyword.SYSCALL:
                        return_ast = parse_syscall()
                    case Keyword.WHILE:
                        return_ast = parse_while_loop()
                    case Keyword.BUFFER:
                        return_ast = parse_buffer_alloc()
                    case Keyword.STORE8 | Keyword.STORE64:
                        return_ast = parse_store()
                    case Keyword.LOAD8 | Keyword.LOAD64:
                        return_ast = parse_load()
                    case Keyword.INCLUDE:
                        parse_include()
                    case Keyword.CONST:
                        parse_const()
                    case Keyword.FUN:
                        return_ast = parse_function_def()
                    case Keyword.BREAK:
                        return_ast = ASTNode_Base(ASTType.BREAK, expect_keyword(Keyword.BREAK))
                    case Keyword.CONTINUE:
                        return_ast = ASTNode_Base(ASTType.CONTINUE, expect_keyword(Keyword.CONTINUE))
                    case Keyword.RETURN:
                        return_ast = ASTNode_Single(ASTType.RETURN, expect_keyword(Keyword.RETURN), parse_expression())
                    case _:
                        compiler_error(tok.loc, f"Unexpected keyword {tok.value.name}")
            case _:
                if tok.typ == TokenType.IDENTIFIER and tokens[index + 1].typ == TokenType.ASSIGN:
                    return_ast = parse_assign()
                else:
                    return_ast = parse_expression()
        
        if tokens[index].typ in [TokenType.SEMICOLON, TokenType.EOL, TokenType.EOF]:
            # Consume some end of statement token
            expect_token(tokens[index].typ)
        else:
            compiler_error(tokens[index].loc, f"Expected end of statement token, got {tokens[index].typ.name}")
    
        return return_ast

    while index < len(tokens):
        if tokens[index].typ == TokenType.EOF:
            break
        if tokens[index].typ == TokenType.EOL:
            index += 1
            continue
        s = parse_statement()
        if s and s.typ != ASTType.NONE:
            ast.append(s)
    
    return ast, declared_vars, declared_funs, declared_consts

def print_ast(ast:ASTNode_Base, indent=0):
    indent_str = ' | ' * indent
    name_str = indent_str + ast.typ.name
    if isinstance(ast, ASTNode_Ident):
        name_str += f" \"{ast.ident_str.encode('unicode_escape').decode('utf-8')}\""
    elif isinstance(ast, ASTNode_Number):
        name_str += f" {ast.num_value}"
    elif isinstance(ast, ASTNode_BinaryOp) or ast.typ == ASTType.UNARY_OP:
        name_str += f" {ast.value.typ.name}"
    elif ast.typ == ASTType.LOAD or ast.typ == ASTType.STORE:
        name_str += f" {ast.size}"
    elif ast.typ == ASTType.FUN_DEF:
        name_str += f" {ast.fun_name} {', '.join(ast.args)}"
    
    print(name_str)

    match ast.typ:
        case ASTType.BINARY_OP:
            assert isinstance(ast, ASTNode_BinaryOp), "Expected Binary Op AST"
            print_ast(ast.l_ast, indent + 1)
            print_ast(ast.r_ast, indent + 1)
        case ASTType.UNARY_OP:
            assert isinstance(ast, ASTNode_Single), "Expected Single Ref AST"
            print_ast(ast.ast_ref, indent + 1)
        case ASTType.ASSIGN:
            assert isinstance(ast, ASTNode_Assign), "Expected Assign AST"
            print_ast(ast.l_ast, indent + 1)
            print_ast(ast.r_ast, indent + 1)
        case ASTType.VAR_DECL | ASTType.VAR_REF | ASTType.STRING:
            assert isinstance(ast, ASTNode_Ident), "Expected Ident AST"
        case ASTType.NUMBER | ASTType.BUFFER_ALLOC:
            assert isinstance(ast, ASTNode_Number), "Expected Number AST"
        case ASTType.PRINT:
            print_ast(ast.ast_ref, indent+1)
        case ASTType.IF:
            assert isinstance(ast, ASTNode_If), "Expected If AST"
            print_ast(ast.cond_ast, indent+1)
            print(f'{indent_str}THEN')
            for a in ast.then_ast_block:
                print_ast(a, indent+1)
            if ast.else_if_ast:
                print(f'{indent_str}ELIF')
                print_ast(ast.else_if_ast)
            if ast.else_ast_block:
                print(f"{indent_str}ELSE")
                for a in ast.else_ast_block:
                    print_ast(a, indent+1)
        case ASTType.WHILE:
            assert isinstance(ast, ASTNode_While), "Expected While AST"
            print_ast(ast.cond_ast, indent+1)
            print(f'{indent_str}DO')
            for a in ast.do_ast_block:
                print_ast(a, indent+1)
        case ASTType.FUN_DEF:
            assert isinstance(ast, ASTNode_Fundef), "Expected Fundef AST"
            for a in ast.body:
                print_ast(a, indent+1)
        case ASTType.SYSCALL:
            assert isinstance(ast, ASTNode_Syscall), "Expected Syscall AST"
            for a in ast.args:
                print_ast(a, indent+1)
        case ASTType.LOAD:
            assert isinstance(ast, ASTNode_Load), "Expected Load AST"
            print_ast(ast.ptr_exp, indent+1)
        case ASTType.STORE:
            assert isinstance(ast, ASTNode_Store), "Expected Store AST"
            print_ast(ast.ptr_exp, indent+1)
            print_ast(ast.val_exp, indent+1)
        case ASTType.NONE:
            pass
        case _:
            assert False, f"Unhandled AST Type {ast.typ}"

def file_to_ast(filename: str):
    with open(filename, 'r') as f:
        code_str = f.read()
    toks = tokenize_string(os.path.abspath(filename), code_str)
    return parse_tokens(toks)

import argparse

if __name__ == '__main__':
    argp = argparse.ArgumentParser(description='The Belfast Compiler')
    argp.add_argument('file', help='The file input to the compiler')
    argp.add_argument('-o', '--output', dest='output', help='The output assembly file', default='prog.asm')
    argp.add_argument('--no-comments', action='store_true', help='Turn off the comments generated in assembly')
    argp.add_argument('--ir-only', action='store_true', help='Turn off the comments generated in assembly')
    args = argp.parse_args()

    filename = args.file

    if args.no_comments:
        DO_ASM_COMMENTS = False

    ast = file_to_ast(filename)[0]
    # for a in ast:
    #     print_ast(a)
    
    trips, trip_ctx = triples_parse_program(ast)

    asm = get_asm_header()

    x86_tripstr = ""
    prog_tripstr = ""

    called_funs = get_call_graph(trips, trip_ctx.functions)

    for f_name in called_funs:
        f_trips = trip_ctx.functions[f_name]
        prog_tripstr += f"FUNCTION {f_name}\n"
        index_triples(f_trips)
        trip_ctx.ctx_name = f_name
        f_trips = optimize_triples(f_trips, trip_ctx)
        index_triples(f_trips)
        for t in f_trips:
            prog_tripstr += f"{print_triple(t)}\n"
        f_trips = optimize_x86(f_trips, trip_ctx)
        x86_tripstr += f"FUNCTION {f_name}\n"
        x86_tripstr += output_x86_trips_to_str(f_trips, trip_ctx)
        x86_tripstr += "\n"
        if not args.ir_only:
            asm += convert_function_to_asm(f_name, f_trips, trip_ctx, args.no_comments)
        prog_tripstr += "\n"

    # with open('print_d.asm') as f:
    #     asm += f.read() + '\n'
    trip_ctx.ctx_name = "main"
    prog_tripstr += "MAIN\n"
    index_triples(trips)
    trips = optimize_triples(trips, trip_ctx)
    index_triples(trips)
    for t in trips:
        prog_tripstr += f"{print_triple(t)}\n"
    trips = optimize_x86(trips, trip_ctx)
    x86_tripstr += "MAIN\n"
    x86_tripstr += output_x86_trips_to_str(trips, trip_ctx)
    if not args.ir_only:
        asm += convert_function_to_asm("main", trips, trip_ctx, args.no_comments)

    with open('prog.tripstr', 'w') as f:
        f.write(prog_tripstr)
    with open('prog_x86.tripstr', 'w') as f:
        f.write(x86_tripstr)

    asm += get_asm_footer(trip_ctx, called_funs)
    
    if not args.ir_only:
        with open(args.output, 'w') as f_asm:
            f_asm.write(asm)

    # print('\nEVALUATION:')
    # eval_ctx = EvaluationContext()
    # for a in ast:
    #     evaluate_ast(a, eval_ctx)
