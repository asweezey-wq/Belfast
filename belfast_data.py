from enum import Enum, auto
from typing import *
from dataclasses import dataclass, asdict
import sys
import itertools

DO_ASM_COMMENTS = True

Loc = Tuple[str, int, int]

class Keyword(Enum):
    VAR = auto()
    PRINT = auto()
    IF = auto()
    THEN = auto()
    END = auto()
    ELSE = auto()
    ELIF = auto()
    SYSCALL = auto()
    WHILE = auto()
    DO = auto()
    BUFFER = auto()
    INCLUDE = auto()
    CONST = auto()
    FUN = auto()
    BREAK = auto()
    CONTINUE = auto()
    RETURN = auto()
    INLINE = auto()

    STRUCT = auto()
    SIZEOF = auto()
    OFFSET = auto()

    LOAD = auto()
    SLOAD = auto()
    STORE = auto()

    LOADF = auto()
    SLOADF = auto()
    STOREF = auto()

    LOAD8 = auto()
    SLOAD8 = auto()
    STORE8 = auto()

    LOAD16 = auto()
    SLOAD16 = auto()
    STORE16 = auto()

    LOAD32 = auto()
    SLOAD32 = auto()
    STORE32 = auto()

    LOAD64 = auto()
    STORE64 = auto()

class Operator(Enum):
    ASSIGN = auto()
    PLUS = auto()
    MINUS = auto()
    MULTIPLY = auto()
    DIVIDE = auto()
    MODULUS = auto()
    EQ = auto()
    NE = auto()
    GE = auto()
    GT = auto()
    LE = auto()
    LT = auto()
    SHIFT_RIGHT = auto()
    SHIFT_LEFT = auto()
    BITWISE_AND = auto()
    BITWISE_OR = auto()
    BITWISE_XOR = auto()
    BITWISE_NOT = auto()
    NEGATE = auto()

    LOGICAL_NOT = auto()
    LOGICAL_AND = auto()
    LOGICAL_OR = auto()

KEYWORD_NAMES = {
    'var': Keyword.VAR,
    'print': Keyword.PRINT,
    'if': Keyword.IF,
    'then': Keyword.THEN,
    'end': Keyword.END,
    'else': Keyword.ELSE,
    'elif': Keyword.ELIF,
    'while': Keyword.WHILE,
    'do': Keyword.DO,
    'include': Keyword.INCLUDE,
    'const': Keyword.CONST,
    'return': Keyword.RETURN,
    'fun': Keyword.FUN,
    'break': Keyword.BREAK,
    'continue': Keyword.CONTINUE,
    'struct': Keyword.STRUCT,
    'inline': Keyword.INLINE,
}

BUILTINS_NAMES = {
    'syscall': Keyword.SYSCALL,
    'buffer': Keyword.BUFFER,
    'loadf': Keyword.LOADF,
    'sloadf': Keyword.SLOADF,
    'storef': Keyword.STOREF,
    'load64': Keyword.LOAD64,
    'store64': Keyword.STORE64,
    'load8': Keyword.LOAD8,
    'sload8': Keyword.SLOAD8,
    'store8': Keyword.STORE8,
    'load16': Keyword.LOAD16,
    'sload16': Keyword.SLOAD16,
    'store16': Keyword.STORE16,
    'load32': Keyword.LOAD32,
    'sload32': Keyword.SLOAD32,
    'store32': Keyword.STORE32,
    'load': Keyword.LOAD,
    'sload': Keyword.SLOAD,
    'store': Keyword.STORE,
    'sizeof': Keyword.SIZEOF,
    'offset': Keyword.OFFSET,
}

class TokenType(Enum):
    UNKNOWN = auto()
    EOF = auto()
    EOL = auto()
    NUMBER = auto()
    STRING = auto()
    CHARACTER = auto()
    IDENTIFIER = auto()
    KEYWORD = auto()
    SEMICOLON = auto()
    PLUS = auto()
    MINUS = auto()
    MULTIPLY = auto()
    DIVIDE = auto()
    MODULUS = auto()
    SHIFT_RIGHT = auto()
    SHIFT_LEFT = auto()
    BITWISE_AND = auto()
    BITWISE_OR = auto()
    BITWISE_XOR = auto()
    BITWISE_NOT = auto()
    LOGICAL_NOT = auto()
    LOGICAL_AND = auto()
    LOGICAL_OR = auto()

    EQ = auto()
    NE = auto()
    GE = auto()
    GT = auto()
    LE = auto()
    LT = auto()

    ASSIGN = auto()
    OPEN_PAREN = auto()
    CLOSE_PAREN = auto()
    COMMA = auto()
    PERIOD = auto()

class ASTType(Enum):
    NONE = auto()
    NUMBER = auto()
    STRING = auto()
    VAR_DECL = auto()
    VAR_DECL_ASSIGN = auto()
    VAR_REF = auto()
    UNARY_OP = auto()
    BINARY_OP = auto()
    ASSIGN = auto()
    PRINT = auto()
    IF = auto()
    WHILE = auto()
    DO_WHILE = auto()
    SYSCALL = auto()
    BUFFER_ALLOC = auto()
    LOAD = auto()
    STORE = auto()
    FUN_DEF = auto()
    FUN_CALL = auto()
    RETURN = auto()
    BREAK = auto()
    CONTINUE = auto()

@dataclass
class Token:
    typ: TokenType
    loc: Loc
    value: Optional[Union[int, str, Keyword]]

@dataclass
class ASTNode_Base:
    typ: ASTType
    value: Token

@dataclass
class ASTNode_Ident(ASTNode_Base):
    ident_str: str

@dataclass
class ASTNode_Number(ASTNode_Base):
    num_value: int

@dataclass
class ASTNode_BinaryOp(ASTNode_Base):
    l_ast: ASTNode_Base
    r_ast: ASTNode_Base

@dataclass
class ASTNode_Assign(ASTNode_Base):
    l_ast: ASTNode_Base
    r_ast: ASTNode_Base

@dataclass
class ASTNode_Single(ASTNode_Base):
    ast_ref: ASTNode_Base

@dataclass
class ASTNode_VardecAssign(ASTNode_Base):
    ident_str: str
    ast_ref: ASTNode_Base

@dataclass
class ASTNode_If(ASTNode_Base):
    cond_ast: ASTNode_Base
    then_ast_block: List[ASTNode_Base]
    else_ast_block: Optional[List[ASTNode_Base]] = None
    else_if_ast: Optional['ASTNode_If'] = None

@dataclass
class ASTNode_While(ASTNode_Base):
    cond_ast: ASTNode_Base
    do_ast_block: List[ASTNode_Base]

@dataclass
class ASTNode_Syscall(ASTNode_Base):
    args: List[ASTNode_Base]

@dataclass
class ASTNode_Store(ASTNode_Base):
    ptr_exp: ASTNode_Base
    val_exp: ASTNode_Base
    size: int

@dataclass
class ASTNode_Load(ASTNode_Base):
    ptr_exp: ASTNode_Base
    size: int
    signed: bool

@dataclass
class ASTNode_Fundef(ASTNode_Base):
    fun_name: str
    fun_flags: int
    args: List[str]
    body: List[ASTNode_Base]

@dataclass
class ASTNode_Funcall(ASTNode_Base):
    fun_name: str
    args: List[ASTNode_Base]

TOKEN_OP_MAP = {
    TokenType.PLUS: Operator.PLUS,
    TokenType.MINUS: Operator.MINUS,
    TokenType.MULTIPLY: Operator.MULTIPLY,
    TokenType.DIVIDE: Operator.DIVIDE,
    TokenType.ASSIGN: Operator.ASSIGN,
    TokenType.MODULUS: Operator.MODULUS,
    TokenType.EQ: Operator.EQ,
    TokenType.NE: Operator.NE,
    TokenType.GT: Operator.GT,
    TokenType.GE: Operator.GE,
    TokenType.LT: Operator.LT,
    TokenType.LE: Operator.LE,
    TokenType.BITWISE_AND: Operator.BITWISE_AND,
    TokenType.BITWISE_OR: Operator.BITWISE_OR,
    TokenType.BITWISE_XOR: Operator.BITWISE_XOR,
    TokenType.BITWISE_NOT: Operator.BITWISE_NOT,
    TokenType.SHIFT_LEFT: Operator.SHIFT_LEFT,
    TokenType.SHIFT_RIGHT: Operator.SHIFT_RIGHT,
    TokenType.LOGICAL_NOT: Operator.LOGICAL_NOT,
    TokenType.LOGICAL_AND: Operator.LOGICAL_AND,
    TokenType.LOGICAL_OR: Operator.LOGICAL_OR,
}

KW_SIZE_MAP = {
    Keyword.LOAD8:      8,
    Keyword.SLOAD8:     8,
    Keyword.STORE8:     8,
    Keyword.LOAD16:      16,
    Keyword.SLOAD16:     16,
    Keyword.STORE16:     16,
    Keyword.LOAD32:      32,
    Keyword.SLOAD32:     32,
    Keyword.STORE32:     32,
    Keyword.LOAD64:     64,
    Keyword.STORE64:    64,
}

ASM_SIZE_WORDS = {
    8: 'byte',
    64: 'qword'
}

def compiler_error(loc:Loc, message):
    print(':'.join(map(str, loc)) + f': {message}', file=sys.stderr)
    sys.exit(1)


class TripleType(Enum):
    BINARY_OP = auto()
    UNARY_OP = auto()
    PRINT = auto()
    ASSIGN = auto()
    IF_COND = auto()
    GOTO = auto()
    LABEL = auto()
    ARG = auto()
    SYSCALL = auto()
    LOAD = auto()
    STORE = auto()
    REGMOVE = auto()

    NOP_USE = auto()
    NOP_REF = auto()

    FUN_ARG_IN = auto()
    CALL = auto()
    RETURN = auto()

    LEA = auto()

class TripleValueType(Enum):
    UNKNOWN = auto()
    CONSTANT = auto()
    VAR_REF = auto()
    BUFFER_REF = auto()
    LOCAL_BUFFER_REF = auto()
    STRING_REF = auto()
    TRIPLE_REF = auto()
    TRIPLE_TARGET = auto() # for use as a triple jump target
    VAR_ASSIGN = auto()
    REGISTER = auto()
    FUN_LABEL = auto()
    ON_STACK = auto()
    ADDRESS_COMPUTE = auto()
    GLOBAL_REF = auto()
    GLOBAL_LABEL = auto()

@dataclass
class TripleValue:
    typ: TripleValueType
    value: Union[int, str, 'Triple', Tuple[int, int]]

    def __repr__(self) -> str:
        return trip_val_to_str(self)

    def __hash__(self) -> int:
        return hash(f"{self.typ} {hash(self.value)}")

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, TripleValue) and __o.typ == self.typ and __o.value == self.value

def triple_values_equal(tv1:TripleValue, tv2:TripleValue):
    return tv1.typ == tv2.typ and tv1.value == tv2.value

def trip_val_to_str(tv:TripleValue, as_hex=False):
    match tv.typ:
        case TripleValueType.CONSTANT:
            if as_hex:
                return hex(tv.value)
            else:
                return str(tv.value)
        case TripleValueType.VAR_REF | TripleValueType.VAR_ASSIGN | TripleValueType.BUFFER_REF | TripleValueType.STRING_REF:
            return str(tv.value)
        case TripleValueType.LOCAL_BUFFER_REF:
            return f"buffer[{tv.value.size}]"
        case TripleValueType.TRIPLE_REF | TripleValueType.TRIPLE_TARGET:
            if tv.value is None:
                return "(NONE)"
            assert isinstance(tv.value, Triple), "Expected Triple Ref to reference Triple value"
            return f"({tv.value.index})"
        case TripleValueType.REGISTER:
            return reg_str_for_size(tv.value)
        case TripleValueType.UNKNOWN:
            return "UNKNOWN"
        case TripleValueType.FUN_LABEL:
            return f"_{tv.value}"
        case TripleValueType.GLOBAL_REF:
            return f"[_{tv.value}]"
        case TripleValueType.GLOBAL_LABEL:
            return f"_{tv.value}"
        case TripleValueType.ON_STACK:
            return f"[rsp+{tv.value}]"
        case TripleValueType.ADDRESS_COMPUTE:
            return f"[{trip_val_to_str(tv.value[0])}{'+' if tv.value[2] == 1 else '-'}{trip_val_to_str(tv.value[1])}]"
        case _:
            assert False, f"Unhandled Triple Value Type {tv.typ.name}"

TF_SIGNED = 1 # Indicates a signed operation
TF_BOOL_FORWARDED = 2 # Forwarded booleans are used immediately afterwards in a jump
TF_REMOVE = 4 # Should remove
TF_SYSCALL = 8 # to specify a syscall arg
TF_DONT_FORWARD = 16

SF_INLINE = 1

triple_uid = itertools.count().__next__
@dataclass(eq=False)
class Triple:
    typ:TripleType
    op:Optional[Union[Operator, Keyword]]
    l_val:Optional[TripleValue]
    r_val:Optional[TripleValue]
    index:int = -1
    flags:int = 0
    size:int = 64
    data:int = 0
    uid:int = -1

    def __hash__(self) -> int:
        return self.uid

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Triple) and __o.uid == self.uid

    def __repr__(self) -> str:
        return f"{str(self.index) + ': ' if self.index >= 0 else ''}" + f"{self.typ.name} " + (f"{self.op.name} " if self.op is not None else "") + f"{str(self.l_val) if self.l_val is not None else ''} {str(self.r_val if self.r_val is not None else '')}"

RDI_INDEX = 6
RAX_INDEX = 1
RCX_INDEX = 3
RDX_INDEX = 4

registers = [
    'error',
    'rax',
    'rbx',
    'rcx',
    'rdx',
    'rsi',
    'rdi',
    'rbp',
    'rsp',
    'r8',
    'r9',
    'r10',
    'r11',
    'r12',
    'r13',
    'r14',
    'r15',
]

dword_registers = [
    'error',
    'eax',
    'ebx',
    'ecx',
    'edx',
    'esi',
    'edi',
    'ebp',
    'esp',
    'r8d',
    'r9d',
    'r10d',
    'r11d',
    'r12d',
    'r13d',
    'r14d',
    'r15d',
]

word_registers = [
    'error',
    'ax',
    'bx',
    'cx',
    'dx',
    'si',
    'di',
    'bp',
    'sp',
    'r8w',
    'r9w',
    'r10w',
    'r11w',
    'r12w',
    'r13w',
    'r14w',
    'r15w',
]

byte_registers = [
    'error',
    'al',
    'bl',
    'cl',
    'dl',
    'sil',
    'dil',
    'bpl',
    'spl',
    'r8b',
    'r9b',
    'r10b',
    'r11b',
    'r12b',
    'r13b',
    'r14b',
    'r15b',
]

ARG_REGISTERS = [6, 5, 4, 3, 9, 10]
SYSCALL_ARG_REGISTERS = [6, 5, 4, 11, 9, 10]
DATA_REGISTERS = [1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16]

CALLER_SAVED_REG = [1, 3, 4, 5, 6, 9, 10, 11, 12]
CALLEE_SAVED_REG = [2, 7, 13, 14, 15, 16]

def reg_str_for_size(index:int, size:int=64):
    if size == 64:
        return registers[index]
    elif size == 32:
        return dword_registers[index]
    elif size == 16:
        return word_registers[index]
    elif size == 8:
        return byte_registers[index]
    else:
        assert False, f"Size {size} not supported"

data_registers = ['rax', 'rbx', 'rcx', 'rdx', 'rsi', 'rdi']

CMP_OP_INSTR_MAP = {Operator.GE: 'ge', Operator.LE: 'le', Operator.GT: 'g', Operator.LT: 'l', Operator.EQ: 'e', Operator.NE: 'ne'}
INVERT_CMP_OP = {
    Operator.GE: Operator.LT,
    Operator.GT: Operator.LE,
    Operator.LE: Operator.GT,
    Operator.LT: Operator.GE,
    Operator.EQ: Operator.NE,
    Operator.NE: Operator.EQ,
}
FLIP_CMP_OP = {
    Operator.GE: Operator.LE,
    Operator.GT: Operator.LT,
    Operator.LE: Operator.GE,
    Operator.LT: Operator.GT,
    Operator.EQ: Operator.EQ,
    Operator.NE: Operator.NE,
}
MEM_WORD_SIZE_MAP = {
    8: 'byte',
    16: 'word',
    32: 'dword',
    64: 'qword'
}

@dataclass
class CompilerSettings:
    output_filename: str = ''
    generate_tripstr: bool = True
    tripstr_filename: str = 'prog.tripstr'
    generate_diff: bool = False
    generate_asm: bool = True
    verbose: int = 0
    asm_comments: bool = False
    register_limit: int = 0
    const_propagation: bool = True

COMPILER_SETTINGS = None

def set_compiler_settings(c: CompilerSettings):
    global COMPILER_SETTINGS
    COMPILER_SETTINGS = c

@dataclass
class CodeScoreStat:
    mov_ops: int = 0
    basic_ops: int = 0
    mem_loads: int = 0
    mem_stores: int = 0
    mul_ops: int = 0
    div_ops: int = 0
    jmp_ops: int = 0
    cond_jmp_ops: int = 0
    syscalls: int = 0
    fun_calls: int = 0
    registers_used: List[int] = ()

def evaluate_stat_score(s: CodeScoreStat):
    score = 0
    score += s.mov_ops
    score += s.basic_ops
    score += s.mem_loads * 2
    score += s.mem_stores * 2
    score += s.mul_ops * 4
    score += s.div_ops * 50
    score += s.jmp_ops * 2
    score += s.cond_jmp_ops * 2
    score += s.syscalls * 3
    score += s.fun_calls * 3
    return score

