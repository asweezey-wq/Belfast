from io import BytesIO

from belfast_data import *
import belfast_data
import struct
from typing import *
from belfast_triples_opt import deepcopy_trips

from belfast_triples import Buffer, FunctionTripleContext, StringRef, TripleContext

def serialize_triplevalue(tv: TripleValue):
    if tv is None:
        return b''
    tv_typ_bytes = struct.pack('B', tv.typ.value)
    data_bytes = b''
    match tv.typ:
        case TripleValueType.UNKNOWN | TripleValueType.BUFFER_REF | TripleValueType.REGISTER | TripleValueType.ADDRESS_COMPUTE | TripleValueType.ON_STACK:
            assert False
        case TripleValueType.CONSTANT:
            data_bytes = struct.pack('q', tv.value)
        case TripleValueType.VAR_REF | TripleValueType.LOCAL_BUFFER_REF | TripleValueType.VAR_ASSIGN:
            data_bytes = struct.pack('2s', tv.value)
        case TripleValueType.TRIPLE_REF | TripleValueType.TRIPLE_TARGET:
            data_bytes = struct.pack('I', tv.value.uid)
        case TripleValueType.FUN_LABEL | TripleValueType.GLOBAL_LABEL | TripleValueType.GLOBAL_REF:
            data_bytes = tv.value.encode('utf-8')
            data_bytes = struct.pack('B', len(data_bytes)) + data_bytes
        case TripleValueType.STRING_REF:
            data_bytes = tv.value.label.encode('utf-8')
            data_bytes = struct.pack('B', len(data_bytes)) + data_bytes
        case _:
            assert False
    return tv_typ_bytes + data_bytes

def serialize_triple(t: Triple):
    uid_bytes = struct.pack('I', t.uid)
    typ_bytes = struct.pack('B', t.typ.value)
    op_typ = None
    if t.op is None:
        op_typ = 0
    elif isinstance(t.op, Operator):
        op_typ = 1
    elif isinstance(t.op, Keyword):
        op_typ = 2
    else:
        assert False, "Invalid op type"
    op_typ_bytes = struct.pack('B', op_typ)
    op_val_bytes = struct.pack('B', t.op.value) if op_typ > 0 else b'\x00'
    val_flags = 0
    if t.l_val is not None:
        val_flags |= 1
    if t.r_val is not None:
        val_flags |= 2
    val_flags_bytes = struct.pack('B', val_flags) 
    l_val_bytes = serialize_triplevalue(t.l_val)
    r_val_bytes = serialize_triplevalue(t.r_val)
    flags_bytes = struct.pack('B', t.flags)
    size_bytes = struct.pack('B', t.size)
    data_bytes = struct.pack('B', t.data)
    return uid_bytes + typ_bytes + op_typ_bytes + op_val_bytes + val_flags_bytes + flags_bytes + size_bytes + data_bytes + l_val_bytes + r_val_bytes

def serialize_function(f: FunctionTripleContext, f_sig: FunctionSignature):
    fun_trips = deepcopy_trips(f.triples)

    # Create mappings
    bytestr_mappings = {}
    buf_mappings = {}
    for t in fun_trips:
        lv = t.l_val
        rv = t.r_val
        for tv in (lv, rv):
            if tv is not None:
                if tv.typ in [TripleValueType.VAR_REF, TripleValueType.VAR_ASSIGN]:
                    if tv.value not in bytestr_mappings:
                        bytestr_mappings[tv.value] = struct.pack('H', len(bytestr_mappings))
                    tv.value = bytestr_mappings[tv.value]
                elif tv.typ == TripleValueType.LOCAL_BUFFER_REF:
                    if tv.value not in buf_mappings:
                        buf_mappings[tv.value] = struct.pack('H', f.local_buffers.index(tv.value))
                    tv.value = buf_mappings[tv.value]

    bytestring = b'\xFF\xFA'
    f_bytes = f.ctx_name.encode('utf-8')
    bytestring += struct.pack('B', len(f_bytes))
    bytestring += f_bytes
    bytestring += struct.pack('B', f_sig.flags)

    bytestring += struct.pack('H', len(f.local_buffers))
    for b in f.local_buffers:
        bytestring += struct.pack('Q', b.size)

    bytestring += struct.pack('H', len(fun_trips))
    for t in fun_trips:
        bytestring += serialize_triple(t)
    bytestring += b'\xFF\xFB'
    return bytestring

def serialize_program(filename: str, trip_ctx: TripleContext):
    parsectx : ParseContext = trip_ctx.parsectx
    bytestring = b''
    # Consts
    bytestring += b'\xAA' + struct.pack('I', len(parsectx.consts))
    for k,v in parsectx.consts.items():
        name_bytes = k.encode('utf-8')
        bytestring += struct.pack('B', len(name_bytes)) + name_bytes + struct.pack('q', v)
    
    # Globals
    bytestring += b'\xBB' + struct.pack('I', len(parsectx.globals))
    for k in parsectx.globals:
        name_bytes = k.encode('utf-8')
        bytestring += struct.pack('B', len(name_bytes)) + name_bytes

    # Strings
    bytestring += b'\xCC' + struct.pack('I', len(trip_ctx.strings))
    for k,v in trip_ctx.strings.items():
        name_bytes = v.encode('utf-8')
        s_bytes = k.encode('utf-8')
        bytestring += struct.pack('B', len(name_bytes)) + name_bytes + struct.pack('I', len(s_bytes)) + s_bytes
    
    for f_name in trip_ctx.parsectx.fun_signatures:
        f_ctx = trip_ctx.get_function(f_name)
        bytestring += serialize_function(f_ctx, parsectx.get_fun_signature(f_name))
    with open(filename, 'wb') as f:
        f.write(bytestring)

def unpack(fmt, b):
        return struct.unpack(fmt, b.read(struct.calcsize(fmt)))[0]

def deserialize_triplevalue(b: BinaryIO):
    typ = TripleValueType._value2member_map_[unpack('B', b)]
    data = None
    match typ:
        case TripleValueType.CONSTANT:
            data = unpack('q', b)
        case TripleValueType.VAR_REF | TripleValueType.LOCAL_BUFFER_REF | TripleValueType.VAR_ASSIGN:
            data = unpack('2s', b)
        case TripleValueType.TRIPLE_REF | TripleValueType.TRIPLE_TARGET:
            data = unpack('I', b)
        case TripleValueType.FUN_LABEL | TripleValueType.GLOBAL_LABEL | TripleValueType.GLOBAL_REF:
            length = unpack('B', b)
            data = b.read(length).decode('utf-8')
        case TripleValueType.STRING_REF:
            length = unpack('B', b)
            data = StringRef('')
            data.label = b.read(length).decode('utf-8')
        case _:
            assert False

    return TripleValue(typ, data)

def deserialize_triple(b: BinaryIO):
    data_format = 'IBBBBBBB'
    dat = b.read(struct.calcsize(data_format))
    uid, typ, op_typ, op_val, val_flags, flags, size, data = struct.unpack_from(data_format, dat)
    typ = TripleType._value2member_map_[typ]
    if op_typ == 0:
        op = None
    elif op_typ == 1:
        op = Operator._value2member_map_[op_val]
    elif op_typ == 2:
        op = Keyword._value2member_map_[op_val]
    else:
        assert False
    has_left = (val_flags & 1) > 0
    has_right = (val_flags & 2) > 0
    lv = None
    if has_left:
        lv = deserialize_triplevalue(b)
    rv = None
    if has_right:
        rv = deserialize_triplevalue(b)

    return Triple(typ, op, lv, rv, -1, flags, size, data, uid)

def deserialize_function(b: BinaryIO):
    if b.read(2) != b'\xFF\xFA':
        return None

    len_name = unpack('B', b)
    f_name = b.read(len_name).decode('utf-8')

    f_flags = unpack('B', b)

    num_buffers = unpack('H', b)
    local_buffers = []
    for i in range(num_buffers):
        local_buffers.append(Buffer(unpack('Q', b)))

    num_trips = unpack('H', b)

    trips = []
    trips_by_uid = {}
    deferred_refs = {}
    deserialize_names = {}
    num_vars = 0
    num_strings = 0
    for i in range(num_trips):
        t = deserialize_triple(b)
        t.index = i
        for tv in (t.l_val, t.r_val):
            if tv:
                if tv.typ in [TripleValueType.TRIPLE_REF, TripleValueType.TRIPLE_TARGET]:
                    if tv.value in trips_by_uid:
                        tv.value = trips_by_uid[tv.value]
                    else:
                        if tv.value not in deferred_refs:
                            deferred_refs[tv.value] = []
                        deferred_refs[tv.value].append(tv)
                elif tv.typ == TripleValueType.VAR_REF or tv.typ == TripleValueType.VAR_ASSIGN:
                    if tv.value not in deserialize_names:
                        deserialize_names[tv.value] = f'var{num_vars}'
                        num_vars += 1
                    tv.value = deserialize_names[tv.value]
                elif tv.typ == TripleValueType.LOCAL_BUFFER_REF:
                    tv.value = local_buffers[struct.unpack('H', tv.value)[0]]
        trips.append(t)
        trips_by_uid[t.uid] = t
        if t.uid in deferred_refs:
            for tv in deferred_refs[t.uid]:
                tv.value = t
            del deferred_refs[t.uid]

    assert len(deferred_refs) == 0

    for t in trips:
        t.uid = belfast_data.triple_uid()

    signature = b.read(2)
    if signature != b'\xFF\xFB':
        return None

    return f_name, f_flags, trips, local_buffers

def deserialize_program(filename: str):
    bytestring = b''
    with open(filename, 'rb') as f:
        bytestring = f.read()

    b = BytesIO(bytestring)

    assert b.read(1) == b'\xAA'
    
    consts = {}

    num_consts = unpack('I', b)
    for _ in range(num_consts):
        name_len = unpack('B', b)
        name = b.read(name_len)
        consts[name.decode('utf-8')] = unpack('q', b)
    
    assert b.read(1) == b'\xBB'

    num_globals = unpack('I', b)
    globals = set()
    for _ in range(num_globals):
        name_bytes = unpack('B', b)
        globals.add(b.read(name_bytes).decode('utf-8'))

    assert b.read(1) == b'\xCC'

    num_strings = unpack('I', b)
    strings = {}
    for _ in range(num_strings):
        name_bytes = unpack('B', b)
        name = b.read(name_bytes).decode('utf-8')
        s_bytes = unpack('I', b)
        string = b.read(s_bytes).decode('utf-8')
        strings[string] = name

    functions = {}
    func_signatures = {}
    while True:
        d = deserialize_function(b)
        if not d:
            break
        f_name, f_flags, f_trips, lbufs = d
        fctx = FunctionTripleContext(None)
        fctx.ctx_name = f_name
        fctx.local_buffers = lbufs
        fctx.triples = f_trips
        functions[f_name] = fctx
        num_args = len([t for t in f_trips if t.typ == TripleType.FUN_ARG_IN])
        func_signatures[f_name] = FunctionSignature(f_name, num_args, (), f_flags)

    ctx = ParseContext()
    ctx.triple_fun_definitions = functions
    ctx.globals = globals
    ctx.consts = consts
    ctx.fun_signatures = func_signatures
    ctx.strings = strings
    
    return ctx

if __name__ == '__main__':
    deserialize_program('std/stdlib.blc')