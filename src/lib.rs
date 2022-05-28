/// The Abstract Syntax Tree we will be using to model our language
#[derive(Debug, Eq, PartialEq)]
pub enum AST {
    ILit(i64),
    BLit(bool),
    Add(Box<AST>, Box<AST>),
    /// Greater than
    Gt(Box<AST>, Box<AST>),
    /// If expressions. Order of arguments is
    /// (test expression, expression if true, expression if false)
    If(Box<AST>, Box<AST>, Box<AST>),
}

/// Convenience constructor for AST::ILit
pub fn int_lit(i: i64) -> AST {
    AST::ILit(i)
}

/// Convenience constructor for AST::BLit
pub fn bool_lit(b: bool) -> AST {
    AST::BLit(b)
}

/// Convenience constructor for AST::Add
pub fn add(x: AST, y: AST) -> AST {
    AST::Add(Box::new(x), Box::new(y))
}

/// Convenience constructor for AST::Gt
pub fn gt(x: AST, y: AST) -> AST {
    AST::Gt(Box::new(x), Box::new(y))
}

/// Convenience constructor for AST::If
pub fn if_e(test: AST, if_true: AST, if_false: AST) -> AST {
    AST::If(Box::new(test), Box::new(if_true), Box::new(if_false))
}

/// The opcodes that will be emitted by the compiler and interpreted by the vm to execute the
/// program
#[derive(Debug, Eq, PartialEq)]
pub enum Opcode {
    /// Pushes a constant value onto the stack
    LoadConst(Term),
    /// Relative jump of program counter
    Jump(usize),
    /// Relative jump if the item on the top of the stack is `true`. This is used to implement if
    /// statements
    JumpIfTrue(usize),
    /// Primitive Add. Will add opcodes for primitive operations for now, and will remove and
    /// replace with functions if/when I get around to defining functions
    Add,
    Gt,
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
        AST::BLit(i) => vec![Opcode::LoadConst(Term::Bool(i))],
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
        AST::Gt(x, y) => {
            let mut left = compile(*x);
            let mut right = compile(*y);
            // Same as Add, but with Greater Than
            left.append(&mut right);
            left.push(Opcode::Gt);
            left
        }
        AST::If(x, y, z) => {
            let mut test = compile(*x);
            let mut if_true = compile(*y);
            let true_instrs = if_true.len();
            let mut if_false = compile(*z);
            let false_instrs = if_false.len();
            // test contains all the instructions for the boolean test
            // when evaluated, it will push the boolean result onto the stack
            test.push(Opcode::JumpIfTrue(2)); // Jump to the beginning of if_true when the value on the stack is true
            test.push(Opcode::Jump(true_instrs + 1 + 1)); // If we don't jump above, jump over the if_true section plus one extra instruction for the jump at the end of the section and one extra to get past the last instruction of true and to the first instruction of false
            test.append(&mut if_true); // code executed if true
            test.push(Opcode::Jump(false_instrs + 1)); // jump over the false section if the true section executed plue one to get past the last instruction of false
            test.append(&mut if_false); // jump into the false section if the true section is skipped
            test
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
                let right = assert_int(stack.pop());
                let left = assert_int(stack.pop());
                stack.push(Term::Int(left + right));
                pc += 1;
            }
            Opcode::Gt => {
                // It wasn't obeservable in Add because Add is commutative, but the order in which
                // arguments are being pushed to the stack matter, and are "opposite" of the order
                // they are required by the operator.
                // Because `compile` puts the `left` instructions before the `right` instructions,
                // `left` ends up being pushed onto the stack first, and therefore `right` is popped
                // first
                let right = assert_int(stack.pop());
                let left = assert_int(stack.pop());
                stack.push(Term::Bool(left > right));
                pc += 1;
            }
            Opcode::JumpIfTrue(n) => {
                let test = assert_bool(stack.pop());
                if test {
                    pc += n
                } else {
                    pc += 1
                };
            }
            Opcode::Jump(n) => {
                pc += n;
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

    #[test]
    fn greater_than() {
        let mut stack = Stack::new();
        let program = gt(int_lit(2), int_lit(1));
        let c = compile(program);
        let result = run(c, &mut stack);
        assert_eq!(result, Term::Bool(true));
    }

    #[test]
    fn less_than() {
        let mut stack = Stack::new();
        let program = gt(int_lit(1), int_lit(2));
        let c = compile(program);
        let result = run(c, &mut stack);
        assert_eq!(result, Term::Bool(false));
    }

    #[test]
    fn if_true() {
        let mut stack = Stack::new();
        let program = if_e(bool_lit(true), int_lit(1), int_lit(0));
        let c = compile(program);
        let result = run(c, &mut stack);
        assert_eq!(result, Term::Int(1));
    }

    #[test]
    fn if_false() {
        let mut stack = Stack::new();
        let program = if_e(bool_lit(false), int_lit(1), int_lit(0));
        let c = compile(program);
        let result = run(c, &mut stack);
        assert_eq!(result, Term::Int(0));
    }
}
