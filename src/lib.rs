/// The Abstract Syntax Tree we will be using to model our language
#[derive(Debug, Eq, PartialEq)]
pub enum AST {
    ILit(i64),
    BLit(bool),
    /// Variable Bindings; this holds the name of the variable
    /// No attempt is made at renaming / deBruijn to prevent collisions for this exercise.
    Var(String),
    Add(Box<AST>, Box<AST>),
    /// Greater than
    Gt(Box<AST>, Box<AST>),
    /// If expressions. Order of arguments is
    /// (test expression, expression if true, expression if false)
    If(Box<AST>, Box<AST>, Box<AST>),
    /// Let varname = expression in body
    Let(String, Box<AST>, Box<AST>),
    /// Function of one argument
    Lambda(String, Box<AST>),
    /// Apply a function to an argument
    /// The first argument is the lambda, the second is the argument
    Apply(Box<AST>, Box<AST>),
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

/// Convenience constructor for AST::Let
pub fn let_in(name: &str, bind: AST, body: AST) -> AST {
    AST::Let(name.to_string(), Box::new(bind), Box::new(body))
}

/// Convenience constructor for AST::Var
pub fn var(name: &str) -> AST {
    AST::Var(name.to_string())
}

/// Convenience constructor for AST::Lambda
pub fn lambda(name: &str, body: AST) -> AST {
    AST::Lambda(name.to_string(), Box::new(body))
}

/// Convenience constructor for AST::Apply
pub fn apply(l: AST, arg: AST) -> AST {
    AST::Apply(Box::new(l), Box::new(arg))
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
    /// Bind the current head of the stack to the given local variable name
    BindLocal(String),
    /// Unbind the local variable (and pop the value off the stack)
    DropLocal,
    /// Look up a local variable from the environment
    LookupLocal(String),
    /// Creates a `Function` and pushes it onto the stack
    /// It contains the name of the local variable to bind
    MakeFn,
    /// Pushes the value onto the stack and then jumps back to the given address
    Return,
    /// Calls a function, pushing the current location onto the stack for return to pop and jump to
    Call,
    /// Primitive Add. Will add opcodes for primitive operations for now, and will remove and
    /// replace with functions if/when I get around to defining functions
    Add,
    Gt,
}

/// Represents a function
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Function {
    /// The index of the first instruction in the function
    enter: usize,
}

/// Terms that will be processed in the vm and eventually returrned
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Term {
    Int(i64),
    Bool(bool),
    Func(Function),
    /// Should never be obeservable to a user, but allows function calls to push the return value
    /// onto the stack
    Return(usize),
}

/// Represents all of the state the bytecode virtual machine needs to hold.
/// 1. The program stack
/// 2. Local variable mappings
/// 3. Function mappings
#[derive(Debug, Eq, PartialEq)]
pub struct Stack {
    stack: Vec<Term>,
    /// Only one variable is bound in each let-in expression. Binding a variable will involve
    /// pushing its name and the current tip of the stack onto `locals`. Dropping a binding will
    /// simply pop the most recent local off the locals
    locals: Vec<(String, usize)>,
}

impl Stack {
    pub fn new() -> Self {
        Stack {
            stack: vec![],
            locals: vec![],
        }
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

    /// BindLocal is called directly after the bind expression in a let-in, so the local variable
    /// is the current head of the stack
    fn bind_local(&mut self, v: String) {
        let sp = self.stack.len() - 1;
        self.locals.push((v, sp));
    }

    /// DropLocal is called directly after the body expression in a let-in, when the stack looks like
    /// `[..., localvar, bodyresult]`
    fn drop_local(&mut self) {
        self.locals
            .pop()
            .expect("Error -- tried to drop an unbound local");
        let result = self.pop(); // result of body
        self.pop(); // local variable
        self.push(result);
    }

    fn lookup(&self, name: &str) -> Term {
        let (_, pos) = self
            .locals
            .iter()
            .rfind(|(binding, _)| binding == name)
            .expect(&format!("Error -- unbound variable {}", name));
        self.stack[*pos].clone()
    }
}

/// This compiles the AST into a Vec of Opcodes that can be executed by the vm
/// It's implemented recursively because that makes everything easier, but there's probably a way
/// to use a stack or queue to avoid potential issues with stack overflow.
pub fn compile(ast: AST) -> Vec<Opcode> {
    match ast {
        AST::ILit(i) => vec![Opcode::LoadConst(Term::Int(i))],
        AST::BLit(i) => vec![Opcode::LoadConst(Term::Bool(i))],
        AST::Var(s) => vec![Opcode::LookupLocal(s)],
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
        AST::Let(v, x, y) => {
            let mut bind = compile(*x);
            let mut body = compile(*y);
            // Evaluate the binding. Then bind the variable so it can be referenced in the body.
            // After the body has been evaluated, drop the binding so the variable is no longer in
            // scope.
            bind.push(Opcode::BindLocal(v));
            bind.append(&mut body);
            bind.push(Opcode::DropLocal);
            bind
        }
        AST::Lambda(v, x) => {
            let mut body = compile(*x);
            // Jump past the body of the function during execution
            // the function body will only be executed when `Call` jumps into it
            // plus one extra for the BindLocal, DropLocal, and Return instructions
            let jmp = body.len() + 4;
            let mut f = vec![
                Opcode::MakeFn,
                Opcode::Jump(jmp),
                Opcode::BindLocal(v.clone()),
            ];
            f.append(&mut body);
            f.push(Opcode::DropLocal);
            f.push(Opcode::Return);
            f
        }
        AST::Apply(x, y) => {
            let mut func = compile(*x);
            let mut arg = compile(*y);
            arg.append(&mut func);
            arg.push(Opcode::Call);
            arg
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
            Opcode::BindLocal(s) => {
                stack.bind_local(s.clone());
                pc += 1;
            }
            Opcode::DropLocal => {
                stack.drop_local();
                pc += 1;
            }
            Opcode::LookupLocal(name) => {
                // The variable is looked up and cloned, and then pushed onto the top of the stack
                // to be referenced by the next operation
                let l = stack.lookup(name);
                stack.push(l);
                pc += 1;
            }
            Opcode::MakeFn => {
                // The address of the first instruction in the function body
                // The next instruction is a `Jump` over the body, so the beginning of the body is
                // two instructions away
                let enter = pc + 2;
                let f = Function { enter };
                stack.push(Term::Func(f));
                // This will jump across the function body
                pc += 1;
            }
            Opcode::Call => {
                // First pop the function
                let f = assert_fn(stack.pop());
                // Then the argument
                let x = stack.pop();
                // Then push the return pointer
                stack.push(Term::Return(pc + 1));
                // Then push the argument to be bound as a local variable
                stack.push(x);
                // Set the current program counter to the entry of the function body
                pc = f.enter;
            }
            Opcode::Return => {
                // the result will be the topmost value of the stack
                let result = stack.pop();
                // the return pointer is the next value on the stack
                let ret_ptr = assert_return(stack.pop());
                // push the result back onto the stack so the caller has access to it
                stack.push(result);
                // set the program counter to the return pointer to continue from where the
                // function was called
                pc = ret_ptr;
            }
        }
    }
    stack.pop()
}

/// Throw a runtime type error if the term's type is not what is expected
fn assert_int(t: Term) -> i64 {
    match t {
        Term::Int(i) => i,
        t => panic!("Type Error: Expected Int, but got {:?}", t),
    }
}

/// Throw a runtime type error if the term's type is not what is expected
fn assert_bool(t: Term) -> bool {
    match t {
        Term::Bool(b) => b,
        t => panic!("Type Error: Expected Bool, but got {:?}", t),
    }
}

/// Throw a runtime type error if the term's type is not what is expected
fn assert_fn(t: Term) -> Function {
    match t {
        Term::Func(f) => f,
        t => panic!("Type Error: Expected Function, but got {:?}", t),
    }
}

/// Throw a runtime type error if the term's type is not what expected
fn assert_return(t: Term) -> usize {
    match t {
        Term::Return(i) => i,
        t => panic!("Type Error: Expected Return Address, but got {:?}", t),
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

    #[test]
    fn local_add() {
        let mut stack = Stack::new();
        let program = let_in("x", int_lit(5), add(int_lit(1), var("x")));
        let c = compile(program);
        let result = run(c, &mut stack);
        assert_eq!(result, Term::Int(6));
    }

    #[test]
    fn nested_let() {
        let mut stack = Stack::new();
        let program = let_in(
            "x",
            int_lit(5),
            let_in("y", int_lit(1), add(var("y"), var("x"))),
        );
        let c = compile(program);
        let result = run(c, &mut stack);
        assert_eq!(result, Term::Int(6));
    }

    #[test]
    fn surrounded_let() {
        let mut stack = Stack::new();
        let program = let_in(
            "x",
            int_lit(3),
            add(let_in("y", int_lit(1), add(var("y"), var("x"))), int_lit(2)),
        );
        let c = compile(program);
        let result = run(c, &mut stack);
        assert_eq!(result, Term::Int(6));
    }

    #[test]
    fn immediate_function() {
        let mut stack = Stack::new();
        let program = apply(lambda("x", add(var("x"), int_lit(1))), int_lit(2));
        let c = compile(program);
        let result = run(c, &mut stack);
        assert_eq!(result, Term::Int(3));
    }

    #[test]
    fn let_bound_function() {
        let mut stack = Stack::new();
        let program = let_in(
            "inc",
            lambda("x", add(var("x"), int_lit(1))),
            apply(var("inc"), int_lit(2)),
        );
        let c = compile(program);
        let result = run(c, &mut stack);
        assert_eq!(result, Term::Int(3));
    }
}
