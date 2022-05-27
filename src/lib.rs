/// The Abstract Syntax Tree we will be using to model our language
#[derive(Debug, Eq, PartialEq)]
pub enum AST {
    ILit(i64),
    Add(Box<AST>, Box<AST>),
}

/// Convenience constructor for AST::ILit
pub fn int_lit(i: i64) -> AST {
    AST::ILit(i)
}

/// Convenience constructor for AST::Add
pub fn add(x: AST, y: AST) -> AST {
    AST::Add(Box::new(x), Box::new(y))
}

/// The opcodes that will be emitted by the compiler and interpreted by the vm to execute the
/// program
#[derive(Debug, Eq, PartialEq)]
pub enum Opcode {
    /// Pushes a constant value onto the stack
    LoadConst(Term),
    /// Primitive Add. Will add opcodes for primitive operations for now, and will remove and
    /// replace with functions if/when I get around to defining functions
    Add,
}

/// Terms that will be processed in the vm and eventually returrned
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Term {
    Int(i64),
    Bool(bool),
}

/// A thin wrapper around a Vec just to allow pop to be re-implemented
#[derive(Debug, Eq, PartialEq)]
pub struct Stack {
    stack: Vec<Term>,
}

impl Stack {
    pub fn new() -> Self {
        Stack { stack: vec![] }
    }

    fn push(&mut self, t: Term) {
        self.stack.push(t);
    }

    /// In theory (lol) we will only ever pop what we have pushed, so we're unwrapping here and
    /// crashing the program.
    fn pop(&mut self) -> Term {
        self.stack
            .pop()
            .expect("Error -- pop called on empty stack. This should not be possible")
    }
}

/// This compiles the AST into a Vec of Opcodes that can be executed by the vm
/// It's implemented recursively because that makes everything easier, but there's probably a way
/// to use a stack or queue to avoid potential issues with stack overflow.
pub fn compile(ast: AST) -> Vec<Opcode> {
    match ast {
        AST::ILit(i) => vec![Opcode::LoadConst(Term::Int(i))],
        AST::Add(x, y) => {
            let mut left = compile(*x);
            let mut right = compile(*y);
            // Evaluate the left operand first, then the right, then add them together.
            // By calling convention, after the two operands are evaluated, they will be the top
            // two items on the stack, and Add can then pop them add add them together (and push
            // the result back on)
            left.append(&mut right);
            left.push(Opcode::Add);
            left
        }
    }
}

/// This runs the bytecode vm. It takes a reference to the stack to expose it for testing
pub fn run(program: Vec<Opcode>, stack: &mut Stack) -> Term {
    // The program counter points to the current instruction
    let mut pc = 0;
    let end = program.len();
    // Use a while loop instead of simply iterating through because instructions can jump to
    // arbitrary locations
    while pc < end {
        let instr = &program[pc];
        match instr {
            Opcode::LoadConst(t) => {
                stack.push(t.clone());
                pc += 1;
            }
            Opcode::Add => {
                let x = assert_int(stack.pop());
                let y = assert_int(stack.pop());
                stack.push(Term::Int(x + y));
                pc += 1;
            }
        }
    }
    stack.pop()
}

/// Throw a runtime type error if the term's type is not what is expected
fn assert_int(t: Term) -> i64 {
    match t {
        Term::Int(i) => i,
        Term::Bool(_) => panic!("Type Error: Expected Int, but got Bool"),
    }
}

/// Throw a runtime type error if the term's type is not what is expected
fn assert_bool(t: Term) -> bool {
    match t {
        Term::Int(_) => panic!("Type Error: Expected Bool, but got Int"),
        Term::Bool(b) => b,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn just_a_constant() {
        let mut stack = Stack::new();
        let program = int_lit(5);
        let c = compile(program);
        let result = run(c, &mut stack);
        assert_eq!(result, Term::Int(5));
    }

    #[test]
    fn simple_addition() {
        let mut stack = Stack::new();
        let program = add(int_lit(2), int_lit(3));
        let c = compile(program);
        let result = run(c, &mut stack);
        assert_eq!(result, Term::Int(5));
    }

    #[test]
    fn more_addition() {
        let mut stack = Stack::new();
        let program = add(
            add(int_lit(2), int_lit(5)),
            add(int_lit(3), add(int_lit(1), int_lit(4))),
        );
        let c = compile(program);
        let result = run(c, &mut stack);
        assert_eq!(result, Term::Int(1 + 2 + 3 + 4 + 5));
    }
}
