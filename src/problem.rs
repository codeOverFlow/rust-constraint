use crate::constraint::Constraint;

pub trait Solver {}

pub struct Problem {
    solver: dyn Solver,
    constraint: Vec<dyn Constraint>

}