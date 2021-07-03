#[derive(Debug)]
pub struct Domain {
    pub values: Vec<i32>,
    pub hidden: Vec<i32>,
    pub states: Vec<usize>
}

impl Domain {
    pub fn new(set: &[i32]) -> Self {
        Domain {
            values: Vec::from(set),
            hidden: Vec::default(),
            states: Vec::default()
        }
    }

    pub fn reset_state(&mut self) {
        self.values.extend(self.hidden.iter());
        self.hidden.clear();
        self.states.clear()
    }

    pub fn push_state(&mut self) {
        self.states.push(self.values.len())
    }

    pub fn pop_state(&mut self) {
        if let Some(size) = self.states.pop() {
            let diff = size - self.values.len();
            if diff > 0 {
                let bound = self.hidden.len() - diff;
                self.values.extend(self.hidden[bound..].iter().cloned());

                for i in bound..self.hidden.len() {
                    self.hidden.remove(i);
                }
            }
        }
    }

    pub fn hide_value(&mut self, value: i32) {
        self.values.remove(self.values.iter().position(|x| *x == value).unwrap());
        self.hidden.push(value)
    }
}