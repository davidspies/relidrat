pub mod primitives;

pub use crate::primitives::{Assig, RuleIndex};
use standing_relations::{CreationContext, ExecutionContext, Input, Op, Output};
use std::{
    collections::{hash_map, HashMap, HashSet},
    iter::FromIterator,
};

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Debug)]
enum Level {
    LevelZero,
    LevelOne,
    LevelTwo,
}

pub enum RuleInstruction {
    Add(Vec<Assig>),
    Del(Vec<Assig>),
}

#[derive(PartialEq, Eq)]
pub enum Outcome {
    UnvalidatedRule(usize, Vec<Assig>),
    NoConflictStep,
    UnvalidatedConflictStep,
    Validated,
}

pub fn validate(
    program: impl IntoIterator<Item = Vec<Assig>>,
    proof: impl IntoIterator<Item = RuleInstruction>,
) -> Outcome {
    validate_from(CreationContext::new(), program, proof)
}

pub fn validate_from(
    mut context: CreationContext,
    program: impl IntoIterator<Item = Vec<Assig>>,
    proof: impl IntoIterator<Item = RuleInstruction>,
) -> Outcome {
    let (rule_input, rule) = context.new_input::<(RuleIndex, Assig)>();
    let rule = rule.named("rule").save();
    let (select_input, selected) = context.new_input::<(Assig, Level)>();
    let selected = selected.named("selected").collect();

    let rule_index = rule.get().fsts().distinct().named("rule_index").collect();
    let lit_conflict = selected
        .get()
        .fsts()
        .intersection(selected.get().map(|(x, _)| !x).dynamic())
        .named("lit_conflict")
        .dynamic()
        .get_output(&context);
    context.interrupt(lit_conflict, |_| ());

    let sat_index = rule
        .get()
        .swaps()
        .semijoin(selected.get().fsts())
        .dynamic()
        .snds()
        .distinct()
        .named("sat_index")
        .collect();
    let rem_index = rule_index
        .get()
        .minus(sat_index.get())
        .named("rem_index")
        .dynamic();
    let rem_rule = rule
        .get()
        .antijoin(sat_index.get())
        .swaps()
        .dynamic()
        .antijoin(selected.get().map(|(x, _)| !x))
        .dynamic()
        .swaps()
        .named("rem_rule")
        .collect();
    let rule_conflict = rem_index
        .minus(rem_rule.get().fsts().distinct())
        .named("rule_conflict")
        .dynamic()
        .get_output(&context);
    context.interrupt(rule_conflict, |_| ());

    let update_level = rule_index
        .get()
        .map(|i| (i, Level::LevelZero))
        .dynamic()
        .concat(
            rule.get()
                .swaps()
                .join_values(selected.get().map(|(x, level)| (!x, level)).dynamic())
                .dynamic(),
        )
        .dynamic()
        .group_max()
        .named("update_level")
        .dynamic();
    let unit_rules = rem_rule
        .get()
        .fsts()
        .counts()
        .dynamic()
        .flat_map(|(i, count)| if count == 1 { Some(i) } else { None })
        .named("unit_rules")
        .dynamic();
    let units = rem_rule.get().semijoin(unit_rules).named("units").dynamic();
    let next_selection = units
        .join_values(update_level)
        .group_min()
        .named("next_selection")
        .dynamic();
    context.feed_while(next_selection.get_output(&context), select_input.clone());

    let revert = selected.get().swaps().dynamic().get_kv_output(&context);

    let mut context = context.begin();

    let mut holder = RuleHolder::new(rule_input);
    for rule in program {
        if rule.is_empty() {
            return Outcome::Validated;
        }
        holder.add(rule, &context);
    }

    for (instr, n) in proof.into_iter().zip(1..) {
        log::info!("Validing instruction {:?}", n);
        match instr {
            RuleInstruction::Add(rule) => {
                if rule.is_empty() {
                    log::debug!("Checking empty rule");
                    return if context.commit().is_some() {
                        Outcome::Validated
                    } else {
                        Outcome::UnvalidatedConflictStep
                    };
                }
                log::debug!("Checking for AT");
                select_input.add_all(&context, rule.iter().map(|&x| (!x, Level::LevelOne)));
                if context.commit().is_none() {
                    log::debug!("No AT found; Checking for RAT");
                    for &i in &holder.containing_rules[&!rule[0]] {
                        select_input.add_all(
                            &context,
                            holder.rules_hm[&i].iter().flat_map(|&x| {
                                if x == !rule[0] {
                                    None
                                } else {
                                    Some((!x, Level::LevelTwo))
                                }
                            }),
                        );
                        if context.commit().is_none() {
                            return Outcome::UnvalidatedRule(n, rule);
                        }
                        remove_level(Level::LevelTwo, &revert, &select_input, &context);
                        debug_assert!(context.commit().is_none());
                    }
                    log::debug!("RAT found");
                } else {
                    log::debug!("AT found");
                }
                remove_level(Level::LevelOne, &revert, &select_input, &context);

                holder.add(rule, &context);
            }
            RuleInstruction::Del(rule) => holder.del(rule, &context),
        }
    }
    Outcome::NoConflictStep
}

fn remove_level<'a, I>(
    level: Level,
    revert: &Output<
        (Level, Assig),
        impl Op<D = (Level, Assig)>,
        HashMap<Level, HashMap<Assig, isize>>,
    >,
    select_input: &Input<'a, (Assig, Level)>,
    context: &ExecutionContext<'a, I>,
) {
    select_input.remove_all(
        context,
        revert
            .get(context)
            .get(&level)
            .unwrap()
            .iter()
            .map(|(&x, &count)| {
                assert_eq!(count, 1);
                (x, level)
            }),
    );
}

struct RuleHolder<'a> {
    rule_input: Input<'a, (RuleIndex, Assig)>,
    rules_hm: HashMap<RuleIndex, HashSet<Assig>>,
    rules_by_val: HashMap<Vec<Assig>, RuleIndex>,
    containing_rules: HashMap<Assig, HashSet<RuleIndex>>,
    rule_counter: usize,
}

impl<'a> RuleHolder<'a> {
    fn new(rule_input: Input<'a, (RuleIndex, Assig)>) -> Self {
        RuleHolder {
            rule_input,
            rules_hm: HashMap::new(),
            rules_by_val: HashMap::new(),
            containing_rules: HashMap::new(),
            rule_counter: 0,
        }
    }
    fn add<I>(&mut self, mut rule: Vec<Assig>, context: &ExecutionContext<'a, I>) {
        let i = RuleIndex::new(self.rule_counter);
        self.rule_counter += 1;
        self.rules_hm.insert(i, HashSet::from_iter(rule.clone()));
        for &x in &rule {
            self.containing_rules.entry(x).or_default().insert(i);
        }
        self.rule_input
            .add_all(&context, rule.iter().map(|&x| (i, x)));
        rule.sort();
        self.rules_by_val.insert(rule, i);
    }
    fn del<I>(&mut self, mut rule: Vec<Assig>, context: &ExecutionContext<'a, I>) {
        rule.sort();
        match self.rules_by_val.entry(rule) {
            hash_map::Entry::Vacant(vac) => panic!(
                "Attempting to delete rule not present: {}",
                primitives::assignment_line(vac.key())
            ),
            hash_map::Entry::Occupied(occ) => {
                let (r, i) = occ.remove_entry();
                log::debug!("Deleting rule {}", i);
                self.rules_hm.remove(&i);
                for &x in &r {
                    self.containing_rules.get_mut(&x).unwrap().remove(&i);
                }
                self.rule_input
                    .remove_all(&context, r.into_iter().map(|x| (i, x)));
            }
        }
    }
}
