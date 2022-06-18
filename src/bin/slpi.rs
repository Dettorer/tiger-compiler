//! A simple interpreter for a straight-line program (Andrew Appel's book's first exercise)

type Id = String;
type Num = i64;

#[derive(Clone)]
struct Environment(Vec<(Id, Num)>);

enum BinOp {
    Div,
    Minus,
    Plus,
    Times,
}

enum Stm {
    Compound(Box<Stm>, Box<Stm>),
    Assign(Id, Box<Exp>),
    Print(Vec<Exp>),
}

enum Exp {
    Id(Id),
    Num(Num),
    Op(Box<Exp>, BinOp, Box<Exp>),
    Eseq(Box<Stm>, Box<Exp>),
}

impl Environment {
    fn lookup(&self, wanted_id: &Id) -> Option<Num> {
        self.0
            .iter()
            .find(|&(id, _val)| wanted_id == id)
            .map(|(_id, val)| *val)
    }

    fn new() -> Self {
        Environment(Vec::new())
    }

    fn add(&self, id: Id, val: Num) -> Self {
        let mut new_env = self.clone();
        new_env.0.push((id, val));
        new_env
    }
}

impl BinOp {
    fn eval(&self, lhs: &Num, rhs: &Num) -> Num {
        match self {
            BinOp::Div => lhs / rhs,
            BinOp::Minus => lhs - rhs,
            BinOp::Plus => lhs + rhs,
            BinOp::Times => lhs * rhs,
        }
    }
}

fn interprate_statement(stm: Stm, env: &Environment) -> Environment {
    match stm {
        Stm::Compound(a, b) => {
            let new_env = interprate_statement(*a, env);
            interprate_statement(*b, &new_env)
        }
        Stm::Assign(id, exp) => {
            let val = interprate_expression(*exp, env);
            env.add(id, val)
        }
        Stm::Print(exps) => {
            for exp in exps {
                print!("{} ", interprate_expression(exp, env));
            }
            println!();
            env.clone()
        }
    }
}

fn interprate_expression(exp: Exp, env: &Environment) -> Num {
    match exp {
        Exp::Id(id) => env
            .lookup(&id)
            .unwrap_or_else(|| panic!("Could not find any variable with name {}", id)),
        Exp::Num(num) => num,
        Exp::Op(a, op, b) => op.eval(
            &interprate_expression(*a, env),
            &interprate_expression(*b, env),
        ),
        Exp::Eseq(stm, exp) => {
            let new_env = interprate_statement(*stm, env);
            interprate_expression(*exp, &new_env)
        }
    }
}

fn main() {
    let prog: Stm;
    {
        use BinOp::{Div, Minus, Plus, Times};
        use Exp::{Eseq, Id, Num, Op};
        use Stm::{Assign, Compound, Print};

        prog = Compound(
            Assign(
                "a".to_string(),
                Op(Num(5).into(), Plus, Num(3).into()).into(),
            )
            .into(),
            Compound(
                Assign(
                    "b".into(),
                    Eseq(
                        Print(vec![
                            Id("a".into()),
                            Op(Id("a".into()).into(), Minus, Num(1).into()),
                        ])
                        .into(),
                        Op(Num(10).into(), Times, Id("a".into()).into()).into(),
                    )
                    .into(),
                )
                .into(),
                Print(vec![Op(Id("b".into()).into(), Div, Num(5).into())]).into(),
            )
            .into(),
        );
    }

    println!("Should print 8, 7 on one line, then 16 on another line");
    println!("---");
    interprate_statement(prog, &Environment::new());
}
