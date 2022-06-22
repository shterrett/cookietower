# Cookie Tower

Is a stack-based, bytecode compiler and interpreter. The goal of this project is
to learn the basics of stack-based bytecode compilers and interpreters in a
hurry.

## The Plan

1. Basic Math
2. Numeric Comparisons
3. If/Else
4. Name Binding
5. Function Definitions and Calls

## Overview

The AST is a simple lambda calculus extended with primitive `int` and `bool`
types, `+`, `>`, `if-else` expressions, and `let-in` bindings.

```
pub enum AST {
    ILit(i64),
    BLit(bool),
    Var(String),
    Add(Box<AST>, Box<AST>),
    Gt(Box<AST>, Box<AST>),
    If(Box<AST>, Box<AST>, Box<AST>),
    Let(String, Box<AST>, Box<AST>),
    Lambda(String, Box<AST>),
    Apply(Box<AST>, Box<AST>),
}
```

Variable names are global scope (ie no attempt at renaming or deBruijn to
prevent name collisions across lambdas), but the variables themselves are
lexically scoped by the `let-in` block that they are bound in. The system also
supports name shadowing.

The following opcodes are used, including primitive addition addition and
greater-than comparison.

```
pub enum Opcode {
    LoadConst(Term),
    Jump(usize),
    JumpIfTrue(usize),
    BindLocal(String),
    DropLocal,
    LookupLocal(String),
    MakeFn,
    Return,
    Call,
    Add,
    Gt,
}
```

Compiling the AST returns a single flat vector of opcodes, with `Jump` used to
enter and exit function application and handle flow-control in `if-else`
expressions.

A single program stack is used to store all values, with a secondary stack of
local variable identifiers that keep an index into the variable location on the
stack. Referencing a local variable clones it and pushes it on top of the stack
for use; thus variables are immutable.

Functions are compiled into bytecode that includes a jump over the body of the
function and a return at the end. The jump ensures that the function is not
executed linearly during program execution. Instead, a `MakeFunction` opcode
causes a `Function` to be pushed onto the stack, and this `Function` includes a
pointer to the program instruction where the body of the function begins. A
`Call` instruction then pops the function off the stack and resets the program
counter to the function's body, also pushing the return address to the stack.
The `Return` statement pops the return pointer, pushes the final value of the
function, and then resets the program counter to the return pointer.

Functions close over their environment: the compiler inspects the body of the
the function and extracts a list of all free variables not bound by that
function (or any sub-terms). At runtime, when the function is created (via `MakeFunction`),
the values of those variables are copied off of the stack into the `Function`
struct, and when the function is called those variables are pushed onto the
stack and bound. Once the function returns, they are popped back off the stack
and dropped.

## References

Inspired and guided by

+ [Max Bernstein](https://bernsteinbear.com/blog/bytecode-interpreters/)
+ [_Crafting Interpreters_](https://craftinginterpreters.com)
