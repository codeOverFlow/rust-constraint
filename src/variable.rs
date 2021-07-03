use std::fmt::{self, Display, Formatter};
use std::hash::{Hash, Hasher};

#[derive(Debug, Eq)]
pub struct Variable {
    name: &'static str
}

impl PartialEq for Variable {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Hash for Variable {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state)
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self.name)
    }
}

impl Variable {
    pub fn new(name: &'static str) -> Self {
        Variable {
            name
        }
    }

    pub const fn unassigned() -> Self {
        Variable {
            name: "UNASSIGNED"
        }
    }
}