mod parse;

use relidrat::{primitives, validate_from, Outcome};
use standing_relations::CreationContext;
use std::{env, fs::File, io::BufReader};

fn main() {
    env_logger::init();

    let args = env::args().collect::<Vec<_>>();
    let prog_file = File::open(&args[1]).expect("Could not read program file");
    let program = parse::program(BufReader::new(prog_file));

    let proof_file = File::open(&args[2]).expect("Could not read proof file");
    let proof = parse::proof(BufReader::new(proof_file));

    let context = CreationContext::new();
    let tracker = context.get_tracker();
    match validate_from(context, program, proof) {
        Outcome::UnvalidatedRule(i, rule) => {
            println!("Proof step {} not validated:", i);
            println!("{}", primitives::assignment_line(&rule));
        }
        Outcome::NoConflictStep => {
            println!("All proof steps validated, but no conflict step exists")
        }
        Outcome::UnvalidatedConflictStep => println!("Conflict not validated"),
        Outcome::Validated => println!("Proof validated"),
    }
    tracker
        .dump_dot(File::create("stats.dot").expect("Stats file not created"))
        .expect("Failed to write to stats file");
}
