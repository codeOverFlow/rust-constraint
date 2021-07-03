use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

use crate::domain::Domain;
use crate::variable::Variable;
use std::fmt::{self, Display, Formatter};
use std::error::Error;


#[derive(Debug)]
pub struct ConstraintError {
    msg: &'static str,
}

impl ConstraintError {
    pub fn new(msg: &'static str) -> Self {
        ConstraintError {
            msg
        }
    }
}

impl Display for ConstraintError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self.msg)
    }
}

impl Error for ConstraintError {}


pub struct ConstraintVariable<'a, C: Constraint + PartialEq> {
    pub constraint: &'a C,
    pub variables: Vec<&'a Variable>,
}

impl<'a, C: Constraint + PartialEq> ConstraintVariable<'a, C> {
    pub fn new(constraint: &'a C, variables: &[&'a Variable]) -> Self {
        ConstraintVariable {
            constraint,
            variables: Vec::from(variables),
        }
    }
}

struct UnassignedVariable<'a>(&'a Variable);
static UNASSIGNED: UnassignedVariable = UnassignedVariable(&Variable::unassigned());


pub trait Constraint {
    fn call<'a>(&self,
            variables: &[&'a Variable],
            domains: &mut HashMap<&'a Variable, &mut Domain>,
            assignments: &mut HashMap<&'a Variable, i32>,
            forward_check: bool) -> Result<bool, ConstraintError>;


    fn pre_process<'a, C>(&self,
                      variables: &[&'a Variable],
                      domains: &mut HashMap<&'a Variable, &mut Domain>,
                      constraints: &mut Vec<&ConstraintVariable<C>>,
                      vconstraints: &mut HashMap<&'a Variable, Vec<&mut ConstraintVariable<C>>>)
        where
            C: Constraint + PartialEq + PartialEq<Self>,
    {
        self.default_pre_process(variables, domains, constraints, vconstraints)
    }

    fn default_pre_process<'a, C>(&self,
                              variables: &[&'a Variable],
                              domains: &mut HashMap<&'a Variable, &mut Domain>,
                              constraints: &mut Vec<&ConstraintVariable<C>>,
                              vconstraints: &mut HashMap<&'a Variable, Vec<&mut ConstraintVariable<C>>>)
        where
            C: Constraint + PartialEq + PartialEq<Self>,
    {
        if variables.len() == 1 {
            let variable = variables[0];
            let domain_values: Vec<i32>;

            // to satisfy the borrow checker
            {
                let domain = domains.get(variable).unwrap();
                domain_values = domain.values.clone();
            }

            let mut to_removes: Vec<usize> = Vec::default();

            for (i, &value) in domain_values.iter().enumerate() {
                let res = self.call(variables, domains, &mut HashMap::from_iter(vec![(variable, value)]), false);
                if let Ok(boolean) = res {
                    if !boolean {
                        to_removes.push(i);
                    }
                }
            }


            let domain = domains.get_mut(variable).unwrap();
            for index in to_removes {
                domain.values.remove(index);
            }


            constraints.remove(constraints.iter().position(|cv| cv.constraint == self && cv.variables == variables).unwrap());

            let index_to_remove = vconstraints[variable].iter().position(|cv| cv.constraint == self && cv.variables == variables).unwrap();
            vconstraints.get_mut(variable).unwrap().remove(index_to_remove);
        }
    }

    fn forward_check<'a>(&self,
                     variables: &[&'a Variable],
                     domains: &mut HashMap<&'a Variable, &mut Domain>,
                     assignments: &mut HashMap<&'a Variable, i32>,
                     unassigned: &'a Variable) -> bool
    {
        let mut unassigned_variable = unassigned;
        let mut flag = false;
        for variable in variables {
            if assignments.contains_key(variable) {
                if unassigned_variable == unassigned {
                    unassigned_variable = variable;
                } else {
                    flag = true;
                    break;
                }
            }
        }

        if !flag {
            if unassigned_variable != unassigned {
                // Remove from the unassigned variable domain's all
                // values which break our variable's constraints.
                let domain_values: Option<Vec<i32>>;
                {
                    let domain = domains.get_mut(unassigned_variable);
                    domain_values = match domain {
                        Some(dom) => Some(dom.values.clone()),
                        None => None,
                    }
                }

                let mut values_to_hide: Vec<i32> = Vec::default();
                if let Some(values) = domain_values {
                    for value in values {
                        assignments.insert(unassigned_variable,value);
                        let res = self.call(variables, domains, assignments, false);
                        if let Ok(boolean) = res {
                            if !boolean{
                                values_to_hide.push(value);
                            }
                        }
                    }

                    let domain = domains.get_mut(unassigned_variable).unwrap();
                    for value in values_to_hide {
                        domain.hide_value(value);
                    }

                    assignments.remove(&unassigned_variable);
                } else {
                    return false;
                }
            }
        }
        true
    }
}


#[derive(Debug)]
pub struct FunctionConstraint<F>
    where
        F: FnOnce(Vec<i32>) -> Result<bool, ConstraintError>
{
    function: F,
    assigned: bool,
}

impl<F> FunctionConstraint<F>
    where
        F: Fn(Vec<i32>) -> Result<bool, ConstraintError>
{
    pub fn new(function: F, assigned: bool) -> Self {
        FunctionConstraint {
            function,
            assigned,
        }
    }
}

impl<F> Constraint for FunctionConstraint<F>
    where
        F: Fn(Vec<i32>) -> Result<bool, ConstraintError>
{
    fn call<'a>(&self,
            variables: &[&'a Variable],
            domains: &mut HashMap<&'a Variable, &mut Domain>,
            assignments: &mut HashMap<&'a Variable, i32>,
            forward_check: bool) -> Result<bool, ConstraintError> {
        let mut parms: Vec<i32> = Vec::default();
        let mut missing = 0;
        for v in variables.iter() {
            if let Some(&value) = assignments.get(v) {
                parms.push(value);
            } else {
                missing += 1;
            }
        }

        let UnassignedVariable(unassigned_var) = UNASSIGNED;

        if missing != 0 {
            Ok((self.assigned || (self.function)(parms)?)
                && (
                !forward_check
                    || missing != 1
                    || self.forward_check(variables, domains, assignments, unassigned_var)))
        } else {
            (self.function)(parms)
        }
    }
}


#[derive(Debug)]
pub struct AllDifferentConstraint {}

impl AllDifferentConstraint {
    pub fn new() -> Self {
        AllDifferentConstraint {}
    }
}

impl Constraint for AllDifferentConstraint {
    fn call<'a>(&self,
                variables: &[&'a Variable],
                domains: &mut HashMap<&'a Variable, &mut Domain>,
                assignments: &mut HashMap<&'a Variable, i32>,
                forward_check: bool) -> Result<bool, ConstraintError>
    {
        let mut seen: HashMap<i32, bool> = HashMap::default();
        for variable in variables {
            if let Some(&value) = assignments.get(variable) {
                if seen.contains_key(&value) {
                    return Ok(false);
                }
                seen.insert(value, true);
            }
        }

        if forward_check {
            for variable in variables {
                if !assignments.contains_key(variable) {
                    if let Some(domain) = domains.get_mut(variable) {
                        for &value in seen.keys() {
                            if domain.values.contains(&value) {
                                domain.hide_value(value);
                                if domain.values.len() == 0 {
                                    return Ok(false);
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(true)
    }
}


#[derive(Debug)]
pub struct AllEqualConstraint {}

impl AllEqualConstraint {
    pub fn new() -> Self {
        AllEqualConstraint {}
    }
}

impl Constraint for AllEqualConstraint {
    fn call<'a>(&self,
            variables: &[&'a Variable],
            domains: &mut HashMap<&'a Variable, &mut Domain>,
            assignments: &mut HashMap<&'a Variable, i32>,
            forward_check: bool) -> Result<bool, ConstraintError>
    {
        let mut single_value = i32::MIN;
        for &variable in variables.iter() {
            if let Some(&value) = assignments.get(variable) {
                if single_value == i32::MIN {
                    single_value = value;
                } else if value != single_value {
                    return Ok(false);
                }
            }
        }

        if forward_check && single_value != i32::MIN {
            for &variable in variables {
                let mut to_hides: Vec<i32> = Vec::default();

                if !assignments.contains_key(variable) {
                    if let Some(domain) = domains.get_mut(variable) {
                        if !domain.values.contains(&single_value) {
                            return Ok(false);
                        }

                        for &value in domain.values.iter() {
                            if value != single_value {
                                to_hides.push(value);
                            }
                        }

                        for value in to_hides {
                            domain.hide_value(value);
                        }
                    }
                }
            }
        }

        Ok(true)
    }
}


#[derive(Debug)]
pub struct MaxSumConstraint {
    max_value: i32,
    multipliers: Option<Vec<i32>>,
}

impl MaxSumConstraint {
    pub fn new(max_value: i32, multipliers: Option<Vec<i32>>) -> Self {
        MaxSumConstraint {
            max_value,
            multipliers,
        }
    }
}

impl Constraint for MaxSumConstraint {
    fn call<'a>(&self,
            variables: &[&'a Variable],
            domains: &mut HashMap<&'a Variable, &mut Domain>,
            assignments: &mut HashMap<&'a Variable, i32>,
            forward_check: bool) -> Result<bool, ConstraintError>
    {
        let max_sum = self.max_value;
        let mut sum = 0;
        if self.multipliers.is_some() {
            for (variable, multiplier) in variables.iter().zip(self.multipliers.as_ref().unwrap().clone()).collect::<Vec<(&&Variable, i32)>>()
            {
                if assignments.contains_key(variable) {
                    sum += assignments[variable] * multiplier;
                }
            }

            if sum > max_sum {
                return Ok(false);
            }

            if forward_check {
                for (variable, multiplier) in variables.iter().zip(self.multipliers.as_ref().unwrap().clone()).collect::<Vec<(&&Variable, i32)>>() {
                    if !assignments.contains_key(variable) {
                        if let Some(domain) = domains.get_mut(variable) {
                            let mut to_hides: Vec<i32> = Vec::default();

                            for &value in domain.values.iter() {
                                if sum + value * multiplier > max_sum {
                                    to_hides.push(value);
                                }
                            }

                            for value in to_hides {
                                domain.hide_value(value);
                            }
                        } else {
                            return Ok(false);
                        }
                    }
                }
            }
        } else {
            for variable in variables.iter() {
                if assignments.contains_key(variable) {
                    sum += assignments[variable]
                }
            }

            if sum > max_sum {
                return Ok(false);
            }
            if forward_check {
                for variable in variables {
                    if !assignments.contains_key(variable) {
                        if let Some(domain) = domains.get_mut(variable) {
                            let mut to_hides: Vec<i32> = Vec::default();

                            for &value in domain.values.iter() {
                                if sum + value > max_sum {
                                    to_hides.push(value);
                                }
                            }

                            for value in to_hides {
                                domain.hide_value(value);
                            }
                        } else {
                            return Ok(false);
                        }
                    }
                }
            }
        }
        Ok(true)
    }

    fn pre_process<'a, C>(&self,
                      variables: &[&'a Variable],
                      domains: &mut HashMap<&'a Variable, &mut Domain>,
                      constraints: &mut Vec<&ConstraintVariable<C>>,
                      vconstraints: &mut HashMap<&'a Variable, Vec<&mut ConstraintVariable<C>>>)
        where
            C: Constraint + PartialEq + PartialEq<Self>,
    {
        self.default_pre_process(variables, domains, constraints, vconstraints);

        let max_sum = self.max_value;
        if self.multipliers.is_some() {
            for (variable, multiplier) in variables.iter().zip(self.multipliers.as_ref().unwrap().clone()).collect::<Vec<(&&Variable, i32)>>() {
                if let Some(domain) = domains.get_mut(variable) {
                    let mut to_removes: Vec<usize> = Vec::default();

                    for &value in domain.values.iter() {
                        if value * multiplier > max_sum {
                            to_removes.push(domain.values.iter().position(|&v| v == value).unwrap());
                        }
                    }
                    for index in to_removes {
                        domain.values.remove(index);
                    }
                }
            }
        } else {
            for variable in variables.iter() {
                if let Some(domain) = domains.get_mut(variable) {
                    let mut to_removes: Vec<usize> = Vec::default();

                    for &value in domain.values.iter() {
                        if value > max_sum {
                            to_removes.push(domain.values.iter().position(|&v| v == value).unwrap());
                        }
                    }

                    for index in to_removes {
                        domain.values.remove(index);
                    }
                }
            }
        }
    }
}


#[derive(Debug)]
pub struct ExactSumConstraint {
    exact_value: i32,
    multipliers: Option<Vec<i32>>,
}

impl ExactSumConstraint {
    pub fn new(exact_value: i32, multipliers: Option<Vec<i32>>) -> Self {
        ExactSumConstraint {
            exact_value,
            multipliers,
        }
    }
}

impl Constraint for ExactSumConstraint {
    fn call<'a>(&self,
            variables: &[&'a Variable],
            domains: &mut HashMap<&'a Variable, &mut Domain>,
            assignments: &mut HashMap<&'a Variable, i32>,
            forward_check: bool) -> Result<bool, ConstraintError>
    {
        let exact_sum = self.exact_value;
        let mut sum = 0;
        let mut missing = false;

        if self.multipliers.is_some() {
            for (variable, multiplier) in variables.iter().zip(self.multipliers.as_ref().unwrap().clone()).collect::<Vec<(&&Variable, i32)>>() {
                if assignments.contains_key(variable) {
                    sum += assignments[variable] * multiplier
                } else {
                    missing = true
                }
            }

            if sum > exact_sum {
                return Ok(false);
            }

            if forward_check && missing {
                for (variable, multiplier) in variables.iter().zip(self.multipliers.as_ref().unwrap().clone()).collect::<Vec<(&&Variable, i32)>>() {
                    if !assignments.contains_key(variable) {
                        if let Some(domain) = domains.get_mut(variable) {
                            let mut to_hides: Vec<i32> = Vec::default();

                            for &value in domain.values.iter() {
                                if sum + value * multiplier > exact_sum {
                                    to_hides.push(value);
                                }
                            }

                            for value in to_hides {
                                domain.hide_value(value);
                            }

                            if domain.values.len() == 0 {
                                return Ok(false);
                            }
                        }
                    }
                }
            }
        } else {
            for variable in variables {
                if assignments.contains_key(variable) {
                    sum += assignments[variable];
                } else {
                    missing = true;
                }
            }

            if sum > exact_sum {
                return Ok(false);
            }

            if forward_check && missing {
                for variable in variables {
                    if !assignments.contains_key(variable) {
                        if let Some(domain) = domains.get_mut(variable) {
                            let mut to_hides: Vec<i32> = Vec::default();

                            for &value in domain.values.iter() {
                                if sum + value > exact_sum {
                                    to_hides.push(value);
                                }
                            }

                            for value in to_hides {
                                domain.hide_value(value);
                            }

                            if domain.values.len() == 0 {
                                return Ok(false);
                            }
                        }
                    }
                }
            }
        }

        if missing {
            Ok(sum <= exact_sum)
        } else {
            Ok(sum == exact_sum)
        }
    }

    fn pre_process<'a, C>(&self,
                      variables: &[&'a Variable],
                      domains: &mut HashMap<&'a Variable, &mut Domain>,
                      constraints: &mut Vec<&ConstraintVariable<C>>,
                      vconstraints: &mut HashMap<&'a Variable, Vec<&mut ConstraintVariable<C>>>)
        where
            C: Constraint + PartialEq + PartialEq<Self>,
    {
        self.default_pre_process(variables, domains, constraints, vconstraints);

        let multipliers = self.multipliers.as_ref();
        let exact_sum = self.exact_value;
        if multipliers.is_some() {
            for (variable, multiplier) in variables.iter().zip(multipliers.unwrap().clone()).collect::<Vec<(&&Variable, i32)>>() {
                if let Some(domain) = domains.get_mut(variable) {
                    let mut to_removes: Vec<usize> = Vec::default();

                    for &value in domain.values.iter() {
                        if value * multiplier > exact_sum {
                            to_removes.push(domain.values.iter().position(|&v| v == value).unwrap());
                        }
                    }

                    for index in to_removes {
                        domain.values.remove(index);
                    }
                }
            }
        } else {
            for variable in variables.iter() {
                if let Some(domain) = domains.get_mut(variable) {
                    let mut to_removes: Vec<usize> = Vec::default();

                    for &value in domain.values.iter() {
                        if value > exact_sum {
                            to_removes.push(domain.values.iter().position(|&v| v == value).unwrap());
                        }
                    }

                    for index in to_removes {
                        domain.values.remove(index);
                    }
                }
            }
        }
    }
}


#[derive(Debug)]
pub struct MinSumConstraint {
    min_value: i32,
    multipliers: Option<Vec<i32>>,
}

impl MinSumConstraint {
    pub fn new(min_value: i32, multipliers: Option<Vec<i32>>) -> Self {
        MinSumConstraint {
            min_value,
            multipliers,
        }
    }
}

impl Constraint for MinSumConstraint {
    fn call<'a>(&self,
            variables: &[&'a Variable],
            _domains: &mut HashMap<&'a Variable, &mut Domain>,
            assignments: &mut HashMap<&'a Variable, i32>,
            _forward_check: bool) -> Result<bool, ConstraintError>
    {
        for &variable in variables {
            if !assignments.contains_key(variable) {
                return Ok(true);
            }
        }

        let multipliers = self.multipliers.as_ref();
        let min_sum = self.min_value;
        let mut sum = 0;
        if multipliers.is_some() {
            for (variable, multiplier) in variables.iter().zip(multipliers.unwrap().clone()).collect::<Vec<(&&Variable, i32)>>() {
                sum += assignments[variable] * multiplier;
            }
        } else {
            for variable in variables {
                sum += assignments[variable];
            }
        }

        Ok(sum >= min_sum)
    }
}


#[derive(Debug)]
pub struct InSetConstraint {
    set: HashSet<i32>,
}

impl InSetConstraint {
    pub fn new(set: HashSet<i32>) -> Self {
        InSetConstraint {
            set
        }
    }
}

impl Constraint for InSetConstraint {
    fn call<'a>(&self,
            _variables: &[&'a Variable],
            _domains: &mut HashMap<&'a Variable, &mut Domain>,
            _assignments: &mut HashMap<&'a Variable, i32>,
            _forward_check: bool) -> Result<bool, ConstraintError>
    {
        Err(ConstraintError::new("Can't happen because of preprocess."))
    }

    fn pre_process<'a, C>(&self,
                      variables: &[&'a Variable],
                      domains: &mut HashMap<&'a Variable, &mut Domain>,
                      constraints: &mut Vec<&ConstraintVariable<C>>,
                      vconstraints: &mut HashMap<&'a Variable, Vec<&mut ConstraintVariable<C>>>)
        where
            C: Constraint + PartialEq + PartialEq<Self>,
    {
        for variable in variables {
            if let Some(domain) = domains.get_mut(variable) {
                let mut to_removes: Vec<usize> = Vec::default();
                for &value in domain.values.iter() {
                    if !self.set.contains(&value) {
                        to_removes.push(domain.values.iter().position(|&v| v == value).unwrap());
                    }
                }

                for index in to_removes {
                    domain.values.remove(index);
                }
            }
            let to_remove = vconstraints[variable].iter().position(|cv| cv.constraint == self && cv.variables == variables);
            if let Some(index) = to_remove {
                vconstraints.get_mut(variable).unwrap().remove(index);
            }
        }

        let to_remove = constraints.iter().position(|cv| cv.constraint == self && cv.variables == variables);
        if let Some(index) = to_remove {
            constraints.remove(index);
        }
    }
}


#[derive(Debug)]
pub struct NotInSetConstraint {
    set: HashSet<i32>,
}

impl NotInSetConstraint {
    pub fn new(set: HashSet<i32>) -> Self {
        NotInSetConstraint {
            set
        }
    }
}

impl Constraint for NotInSetConstraint {
    fn call<'a>(&self,
            _variables: &[&'a Variable],
            _domains: &mut HashMap<&'a Variable, &mut Domain>,
            _assignments: &mut HashMap<&'a Variable, i32>,
            _forward_check: bool) -> Result<bool, ConstraintError>
    {
        Err(ConstraintError::new("Can't happen because of preprocess."))
    }

    fn pre_process<'a, C>(&self,
                      variables: &[&'a Variable],
                      domains: &mut HashMap<&'a Variable, &mut Domain>,
                      constraints: &mut Vec<&ConstraintVariable<C>>,
                      vconstraints: &mut HashMap<&'a Variable, Vec<&mut ConstraintVariable<C>>>)
        where
            C: Constraint + PartialEq + PartialEq<Self>,
    {
        for variable in variables {
            if let Some(domain) = domains.get_mut(variable) {
                let mut to_removes: Vec<usize> = Vec::default();

                for &value in domain.values.iter() {
                    if self.set.contains(&value) {
                        to_removes.push(domain.values.iter().position(|&v| v == value).unwrap());
                    }
                }

                for index in to_removes {
                    domain.values.remove(index);
                }
            }

            let to_remove = vconstraints[variable].iter().position(|cv| cv.constraint == self && cv.variables == variables);
            if let Some(index) = to_remove {
                vconstraints.get_mut(variable).unwrap().remove(index);
            }
        }
        let to_remove = constraints.iter().position(|cv| cv.constraint == self && cv.variables == variables);
        if let Some(index) = to_remove {
            constraints.remove(index);
        }
    }
}


#[derive(Debug)]
pub struct SomeInSetConstraint {
    set: HashSet<i32>,
    n: i32,
    exact: bool,
}

impl SomeInSetConstraint {
    pub fn new(set: HashSet<i32>, n: i32, exact: bool) -> Self {
        SomeInSetConstraint {
            set,
            n,
            exact,
        }
    }
}

impl Constraint for SomeInSetConstraint {
    fn call<'a>(&self,
            variables: &[&'a Variable],
            domains: &mut HashMap<&'a Variable, &mut Domain>,
            assignments: &mut HashMap<&'a Variable, i32>,
            forward_check: bool) -> Result<bool, ConstraintError>
    {
        let mut missing = 0;
        let mut found = 0;
        for variable in variables {
            if assignments.contains_key(variable) {
                found += if self.set.contains(&assignments[variable]) { 1 } else { 0 };
            } else {
                missing += 1;
            }
        }

        if missing != 0 {
            if self.exact {
                if !(found <= self.n && self.n <= missing + found) {
                    return Ok(false);
                }
            } else {
                if self.n > missing + found {
                    return Ok(false);
                }
            }

            if forward_check && self.n - found == missing {
                for variable in variables {
                    if !assignments.contains_key(variable) {
                        let mut to_hides: Vec<i32> = Vec::default();

                        if let Some(domain) = domains.get_mut(variable) {
                            for &value in domain.values.iter() {
                                if !self.set.contains(&value) {
                                    to_hides.push(value);
                                }
                            }

                            for value in to_hides {
                                domain.hide_value(value);
                            }
                        } else {
                            return Ok(false);
                        }
                    }
                }
            }
        } else {
            if self.exact {
                if found != self.n {
                    return Ok(false);
                }
            } else {
                if found < self.n {
                    return Ok(false);
                }
            }
        }

        Ok(true)
    }
}


#[derive(Debug)]
pub struct SomeNotInSetConstraint {
    set: HashSet<i32>,
    n: i32,
    exact: bool,
}

impl SomeNotInSetConstraint {
    pub fn new(set: HashSet<i32>, n: i32, exact: bool) -> Self {
        SomeNotInSetConstraint {
            set,
            n,
            exact,
        }
    }
}

impl Constraint for SomeNotInSetConstraint {
    fn call<'a>(&self,
            variables: &[&'a Variable],
            domains: &mut HashMap<&'a Variable, &mut Domain>,
            assignments: &mut HashMap<&'a Variable, i32>,
            forward_check: bool) -> Result<bool, ConstraintError>
    {
        let mut missing = 0;
        let mut found = 0;
        for variable in variables {
            if assignments.contains_key(variable) {
                found += if !self.set.contains(&assignments[variable]) { 1 } else { 0 };
            } else {
                missing += 1;
            }
        }

        if missing != 0 {
            if self.exact {
                if !(found <= self.n && self.n <= missing + found) {
                    return Ok(false);
                }
            } else {
                if self.n > missing + found {
                    return Ok(false);
                }
            }

            if forward_check && self.n - found == missing {
                for variable in variables {
                    if !assignments.contains_key(variable) {
                        let mut to_hides: Vec<i32> = Vec::default();

                        if let Some(domain) = domains.get_mut(variable) {
                            for &value in domain.values.iter() {
                                if self.set.contains(&value) {
                                    to_hides.push(value);
                                }
                            }

                            for value in to_hides {
                                domain.hide_value(value);
                            }
                        } else {
                            return Ok(false);
                        }
                    }
                }
            }
        } else {
            if self.exact {
                if found != self.n {
                    return Ok(false);
                }
            } else {
                if found < self.n {
                    return Ok(false);
                }
            }
        }

        Ok(true)
    }
}