from enum import Enum, auto
from typing import *
from dataclasses import dataclass
import sys

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

    LOAD8 = auto()
    STORE8 = auto()

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
    NEGATE = auto()

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
    'continue': Keyword.CONTINUE
}

BUILTINS_NAMES = {
    'syscall': Keyword.SYSCALL,
    'buffer': Keyword.BUFFER,
    'load64': Keyword.LOAD64,
    'store64': Keyword.STORE64,
    'load8': Keyword.LOAD8,
    'store8': Keyword.STORE8,
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

@dataclass
class ASTNode_Fundef(ASTNode_Base):
    fun_name: str
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
    TokenType.SHIFT_LEFT: Operator.SHIFT_LEFT,
    TokenType.SHIFT_RIGHT: Operator.SHIFT_RIGHT,
}

KW_SIZE_MAP = {
    Keyword.LOAD8:      8,
    Keyword.STORE8:     8,
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
    STRING_REF = auto()
    TRIPLE_REF = auto()
    TRIPLE_TARGET = auto() # for use as a triple jump target
    VAR_ASSIGN = auto()
    REGISTER = auto()
    FUN_LABEL = auto()
    ON_STACK = auto()
    ADDRESS_COMPUTE = auto()

@dataclass
class TripleValue:
    typ: TripleValueType
    value: Union[int, str, 'Triple', Tuple[int, int]]
    token: Optional[Token] = None

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
        case TripleValueType.TRIPLE_REF | TripleValueType.TRIPLE_TARGET:
            assert isinstance(tv.value, Triple), "Expected Triple Ref to reference Triple value"
            return f"({tv.value.index})"
        case TripleValueType.REGISTER:
            return reg_str_for_size(tv.value)
        case TripleValueType.UNKNOWN:
            return "UNKNOWN"
        case TripleValueType.FUN_LABEL:
            return f"_{tv.value}"
        case TripleValueType.ON_STACK:
            return f"[rsp+{tv.value}]"
        case TripleValueType.ADDRESS_COMPUTE:
            return f"[{trip_val_to_str(tv.value[0])}{'+' if tv.value[2] == 1 else '-'}{trip_val_to_str(tv.value[1])}]"
        case _:
            assert False, f"Unhandled Triple Value Type {tv.typ.name}"

TF_EPHEMERAL = 1 # Ephemeral triples are only used in one computation, after which they are not used
TF_BOOL_FORWARDED = 2 # Forwarded booleans are used immediately afterwards in a jump
TF_REMOVE = 4 # Should remove

@dataclass(eq=False)
class Triple:
    typ:TripleType
    op:Optional[Union[Operator, Keyword]]
    l_val:Optional[TripleValue]
    r_val:Optional[TripleValue]
    index:int = -1
    loc:Optional['TripleLoc'] = None
    flags:int = 0
    last_use:int = 0
    size:int = 64

    def __hash__(self) -> int:
        return self.index

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Triple) and __o.index == self.index

    def __repr__(self) -> str:
        return f"{str(self.index) + ': ' if self.index >= 0 else ''}" + f"{self.typ.name} " + (f"{self.op.name} " if self.op is not None else "") + f"{str(self.l_val) if self.l_val is not None else ''} {str(self.r_val if self.r_val is not None else '')}"

class TripleLocType(Enum):
    CONSTANT = auto()
    REGISTER = auto()
    MEMORY_ADDR_LABEL = auto()
    IN_MEMORY_AT_LABEL = auto()
    IN_MEMORY_AT_ADDRESS = auto()

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
DATA_REGISTERS = [1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 13, 14, 15, 16]

def reg_str_for_size(index:int, size:int=64):
    if size == 64:
        return registers[index]
    elif size == 8:
        return byte_registers[index]
    else:
        assert False, f"Size {size} not supported"

data_registers = ['rax', 'rbx', 'rcx', 'rdx', 'rsi', 'rdi']

@dataclass
class TripleLoc:
    typ: TripleLocType
    value: Union[int, str]
    offset_from: Optional['TripleLoc'] = None

@dataclass
class RegisterData:
    index: int
    is_data_reg: bool
    has_data: bool
    triple_value_in: Optional[TripleValue]
    data_not_needed: bool

CMP_OP_INSTR_MAP = {Operator.GE: 'ge', Operator.LE: 'le', Operator.GT: 'g', Operator.LT: 'l', Operator.EQ: 'e', Operator.NE: 'ne'}
INVERT_CMP_OP = {
    Operator.GE: Operator.LT,
    Operator.GT: Operator.LE,
    Operator.LE: Operator.GT,
    Operator.LT: Operator.GE,
    Operator.EQ: Operator.NE,
    Operator.NE: Operator.EQ,
}
MEM_WORD_SIZE_MAP = {
    8: 'byte',
    16: 'word',
    32: 'dword',
    64: 'qword'
}