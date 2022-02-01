# Belfast

Belfast is a compiled programming language written in Python. It aims to give the programmer total control over memory accesses and addresses, as there is only one type -- a 64-bit number. This creates a lot of simplicity for both the user and the language and allows the user to write more efficient code, with more control over the memory they are using.

- [Getting Started](#getting-started)
- [Compiling Belfast](#compiling-belfast)

### Getting Started
***
**Making your first Belfast program (.bl)**

Every Belfast program enters from a main function, like in C. We can declare that function like so
```
fun main do
  return 0
end
```

### Variables
***
We can create a variable by declaring
```var x```
or we can immediately assign it a value
```var x = 3```

We can change the variable's value using the `=` operator
```
var x = 1
x = 3
```

### Operators
***
Belfast currently has the following operators:

**Arithmetic Operators**

- `+` - Addition
- `-` - Subtraction
- `*` - Multiplication
- `/` - Integer Division
- `%` - Modulo

**Comparison Operators**

Comparison operators evaluate to either 1 (for true) or 0 (for false)
- `>` - Greater Than
- `>=` - Greater Than or Equals
- `<` - Less Than
- `<=` - Less Than or Equals
- `==` - Equals
- `!=` - Not Equals

**Bitwise Operators**

- `&` - Bitwise AND
- `|` - Bitwise OR
- `^` - Bitwise XOR
- `<<` - Bitwise Shift Left
- `>>` - Bitwise Shift Right

**Logical Operators**

- `&&` - Logical AND, short circuits if the first expression evaluates to 0
- `||` - Logical OR, short circuits if the first expression evaluates to 1

**Unary Operators**

- `!` - Logical NOT, evaluates to 1 if the operand is 0, otherwise evaluates to 0
- `~` - Bitwise NOT, takes the ones complement of the operand

### Data Types
***

Belfast has one data type: a 64-bit integer. We can write constants in code in decimal, or in hexadecimal using the `0x` prefix. 

**Characters**

We can define a character literal using `'`. These are simply 8-bit constants of the unicode representation of that character.
Escape characters supported as of now are `\n`, `\t`, and `\0`, but this will be expanded.

**String Literals**

These 64-bit integers can also be pointers to an address in memory. We can use this to expand our data types to an extent.

We can define a string literal using `"`. This gives us a pointer to this string in memory. All string literals are null-terminated.
```
// Here, s is a pointer to the beginning of the string
var s = "Hello, World!"
```

String literals are immutable, and trying to edit these will result in undefined behavior

**Constants**

We can define constants using the `const` keyword
```
const MY_CONST = 24
```

The value of a const expression must be determinable at compile-time. Therefore we cannot do something like
```
fun foo a do
  // a cannot be determined at runtime, so this is not valid
  const FOO_CONST = a
end
```
But we can reference other constants:
```
const CONST_A = 2
const CONST_B = CONST_A
// We can also using +, -, /, *, %, <<, and >>
const CONST_C = CONST_B + CONST_A * 4
```

### Control Flow
***
**If statements**

If statements are defined as so
```
if ... then
  ...
end
```
The if statement will only execute the contained code if the conditional expression evaluates to a non-zero value. We can also add `else` and `elif` blocks
```
if ... then
  ...
elif ... then
  ...
else
  ...
end
```
If statements can also be declared inline, but the statements must be separated by semicolons
```
if ... then break; end
```

**While loops**

While loops are defined as so
```
while ... do
  ...
end
```
The body of the loop will continue to be executed as long as the condition evaluates to a non-zero value.

The `break` statement will immediately exit the loop, and the `continue` statement will immediately skip to the next loop iteration

### Functions
***

Functions in Belfast are declared using the `fun` keyword
```
fun foo do
  ...
end
```
We can define up to 6 arguments by listing them before the `do` keyword
```
fun foo x y do
  // Here we can use x and y, the function arguments
  ...
end
```
All functions have a return value, which is always a 64-bit number. We can return from a function using the `return` keyword, which requires a value to return
```
return 0
// We can also provide an expression as the return value
return 1 + 2
```
_Note: functions do not need a return statement, by default all functions return 0_

We can call this function using the regular C-style calling syntax
```
foo(2, 3)
```
This passes 2 as the `x` argument and 3 as the `y` argument, and evaluates to the return value of `foo`

There is currently no support for recursion yet-- this is a work in progress.

### Memory Control
***

**Declaring Buffers**

Because all values in Belfast are 64-bit numbers, we must have a way to represent more complex data types. 64-bit numbers can be pointers to memory locations as well, which can hold arbitrary data with arbitrary size.

We can allocate stack memory **inside of a function** using the `buffer` keyword
```
var buf = buffer(32)
```
This statement will create a local buffer of size 32 bytes on the stack, and the variable buf will hold a pointer to this buffer. This buffer can be used in arithmetic operations like a regular number:
```
// This expression gets a pointer to the address 2 bytes after the start of 'buf'
buf + 2
```

Buffers are function local, so they cannot be referenced outside the function in which they are declared. They are also not scope-local, so a buffer declared anywhere inside a function, at any scope, will be available at any point in that function. Therefore in a function like this
```
fun foo x do
  if x then
    var b = buffer(32)
  end
  return 0
end
```
Will still allocate a 32-byte buffer for the whole function, regardless of the value of x. It is best practice to declare buffers at the top scope of the function to avoid confusion.

**Accessing Memory**

Now that we have a pointer to a location in memory, we have to do something with that memory. We can use `load` and `store` for this.

###### Load
We can read a value from memory using the `load` built-in function. There are a couple flavors of `load`:
- `load8` - load 8 bits (1 byte)
- `load16` - load 16 bits (2 bytes)
- `load32` - load 32 bits (4 bytes)
- `load64` - load 64 bits (8 bytes)

`load[8/16/32/64]` takes one argument: a pointer to the memory to load from
```
load64(<memory pointer>)
```
For example:
```
var buf = buffer(16)
...
// This will load a 32-bit number from the buffer
var x = load32(buf)
```
Even though it is a 16-byte buffer, we only read the first 4 bytes and put them in `x`.

We can also use `load` without a size-hint, but we need an extra argument: the number of bytes to load
```
load(<number of bytes>, <memory pointer>)
```
Therefore ```load8(...)``` is the same as ```load(1, ...)```, ```load16(...)``` is equivalent to ```load(2, ...)```,  and so on.

###### SLoad

All loads are unsigned, so loading an 8-bit value will zero-extend that value into a 64-bit value. To load signed numbers, use `sload`. `sload` has all the same sizes as `load`
```
var buf = buffer(16)
...
// This will load a signed 8-bit number from the buffer
var x = sload8(buf)
// Equivalently, using just sload
var y = sload(1, buf)
```

###### Store

To write values to memory, we use the `store` built-in function. The `store` function has the same size-hints as `load`. This takes two arguments: the address to store to, and the value to store.
```
store64(<memory pointer>, <value>)
```
For example:
```
var buf = buffer(16)
...
// This will store a 32-bit number into the buffer
store32(buf, 56)
```

### Structs
***

A struct in Belfast is simply a template for a layout of memory. Structs have no effect on the code other than to provide the programmer with a way to organize memory. We can use the `struct` keyword to declare a struct
```
struct <name>
  <field> <size in bytes>
  ...
end
```
We can list an arbitrary number of fields of this struct, and each field must define its size in bytes, which must be computable at compile-time. We can use structs to get offsets and field sizes when handling memory.

Given a struct `foo`
```
struct foo
  bar 2
  baz 8
  temp 1
end
```
We now have 3 fields we can access in `foo`: `bar`, `baz`, and `temp`. There are two key built-in functions that we can now use:

**Offset**

`offset` is a built-in function to offset a pointer by a struct offset. 
```
// This returns the memory pointer + the field offset
offset(<memory pointer>, <struct name>.<field name>)
```
This offset can be computed at compile time, so it is equivalent to simply adding to the pointer, given the programmer knows the offset of that field in the struct. So, for example,
```
// Given some pointer p
offset(p, foo.baz)
```
This evaluates to `p + 2` because the `baz` field is 2 bytes offset into the `foo` struct (it is after the 2 byte field `bar`).

**Sizeof**

`sizeof` is a built-in function to get the size of a struct or field in a struct
```
sizeof(<struct name>)
sizeof(<struct name>.<field_name>)
```
This simply evaluates to the size of the argument, in bytes. 
```
// This expression evaluates to 11, since foo is 11 bytes long
sizeof(foo)
// This expression evaluates to 8, since baz is an 8 byte field
sizeof(foo.baz)
```

**Putting it all together**

We can use the offset and sizeof fields to use structs in a more effective way.
```
// We first allocate a buffer with the size of foo, in bytes
var p = buffer(sizeof(foo))
// Now p points to a location in memory that we are inferring to contain a struct foo

// We can set the field baz like so
// We calculate the offset of baz in this struct, so now we have the pointer to the field baz of the allocated foo instance
var baz_ptr = offset(p, foo.baz)
// We then store a value, making sure we only store as many bytes as foo.baz is defined to be
store(sizeof(foo.baz), baz_ptr, 90)

// We can load baz in the same way
var baz_value = load(sizeof(foo.baz), baz_ptr)
```

We can infer any region of memory to have a given structure using these `offset` and `sizeof` functions. However, this gets quite cumbersome.

**LoadF and StoreF**

`loadf` and `storef` exist to get rid of the redundancy required by the previous example.
```
loadf(<struct name>.<field name>, <memory pointer>)
storef(<struct name>.<field name>, <memory pointer>, <value>)
```
Where the memory pointer is a pointer to the beginning of the `struct` instance. 

Therefore to store a value into `foo.baz` or load a value from `foo.baz`, like in the previous example, we can do
```
storef(foo.baz, p, 90)
loadf(foo.baz, p)
```
With these functions, the programmer can layout the memory neatly yet still have complete control over the values that they are reading and writing. 

### Including other Belfast Files
***

We can include other Belfast files using `include`
```
include "stdlib.bl"
```

This will prepend the current file with any definitions from `stdlib.bl`. `include` will include
- Function definitions
- `const` declarations
- includes from the included file (will add flags to fix this)
- `struct` declarations

### Syscalls
***

`syscall` is a built-in function to Belfast. Its first argument, the syscall number, must be a compile-time constant, and then the user can pass up to 6 arguments to the syscall. This call returns the return value of the syscall.

## Compiling Belfast
***

`belfast.py` is the entry point, which we can use to compile `.bl` files.
```
python3 belfast.py [file]
```
This will compile the given `.bl` file into an assembly file, which can be assembled with `nasm` and linked with `ld`. 
```
nasm -fmacho64 prog.asm -o prog.o
ld -lSystem prog.o -o prog
```

**Command Line Arguments**

- `-o [output file]` - Specify the file to output the generated assembly to
- `-v` - Verbose mode
- `-r` - Assemble, link, and run after compilation. This will generate `prog.asm`, `a.out.o`, and `a.out`
- `-c` - Include comments in the assembly, which associate generated x86 instructions with their IR instruction (for debugging)
- `-nc` - Prevents the compiler from evaluating constant expressions at compile time (for debugging)
- `-s` - Provides code metrics for efficiency of generated x86 (for debugging)
- `-ir` - Stops the compiler from generating the assembly, it will only output the IR files

**Generated Files**

By default, the compiler will output to `prog.asm` if it is not given an output file.

The compiler will also generate `prog.tripstr`, which shows the IR of the program, and `prog.tripstr.x86`, which shows the IR of the program once it has been converted to x86 and registers have been allocated, etc.

The compiler will also generate `..._tripopt.tripstr` files for each function (e.g. `main` would be `main_tripopt.tripstr`) in the `./tripstr/` directory. These show the IR of the given function after each optimization pass, with a diff to show what was added/removed and why

TODO: Added more CLI arguments to control generated files

