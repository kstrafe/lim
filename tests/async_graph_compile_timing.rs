//! Manual graph-route timing sampler, not a machine-dependent CI threshold.
mod support;

use std::{collections::BTreeMap, time::Instant};

const SAMPLES: usize = 7;

fn source(functions: usize) -> String {
    let mut source = String::from(
        "(#enum Child (#linear) ((Start #u64) (Resume #u64)))
      (#enum ChildPoll () ((Pending Child) (Ready #u64)))
      (#fn child-poll (: task Child : waker (#ref #u64)) ChildPoll
        (#return (#match task
          (#case (Start value) (Pending (Resume value)))
          (#case (Resume value) (Ready value)))))\n",
    );
    for index in 0..128 {
        source.push_str(&format!(
            "(#struct Record{index} () (: x #u64 : y #u64 : z #u64))\n"
        ));
    }
    for index in 0..functions {
        source.push_str(&format!(
            "(@#async-fn (: protocol Work{index}Await : waker #u64
          : function (#fn work{index} (: seed #u64) #u64
            (#return (#await Child Pending Ready child-poll (Start seed))))))\n"
        ));
    }
    source.push_str("(#fn main () #u64 (#return 42u64))");
    source
}

fn measure(
    source: &str,
    path: &std::path::Path,
    cache: &std::path::Path,
) -> (f64, Vec<lim::TimingEvent>) {
    let mut config = lim::CompileConfig::default();
    config.set("async-lowering", "graph");
    let session = lim::TimingSession::start();
    let started = Instant::now();
    let assembly = lim::compile_source_to_assembly(
        source,
        path,
        &config,
        cache,
        lim::TargetDescription::X86_64_SYSTEM_V,
    )
    .unwrap_or_else(|error| panic!("{error:?}"));
    let wall = started.elapsed().as_secs_f64() * 1000.0;
    assert!(assembly.contains(".globl main"));
    (wall, session.finish())
}

fn median(values: &mut [f64]) -> f64 {
    values.sort_by(f64::total_cmp);
    values[values.len() / 2]
}

#[test]
#[ignore = "manual release graph compile benchmark; run with --ignored --nocapture"]
fn graph_many_functions_cold_and_warm() {
    println!(
        "graph API compile, {SAMPLES} samples, in-process; includes assembly emission,
              excludes native encoding/linking and process startup; 128 unrelated records"
    );
    for functions in [1, 8] {
        let text = source(functions);
        // Warm executable code paths without populating any measured cache.
        let warmup = support::Scratch::new("graph-timing-warmup");
        measure(
            &text,
            &warmup.path().join("input.lim"),
            &warmup.path().join("cache"),
        );
        for warm in [false, true] {
            let mut walls = Vec::new();
            let mut stages = BTreeMap::<String, Vec<f64>>::new();
            for _ in 0..SAMPLES {
                let scratch = support::Scratch::new("graph-timing-sample");
                let path = scratch.path().join("input.lim");
                let cache = scratch.path().join("cache");
                if warm {
                    measure(&text, &path, &cache);
                }
                let (wall, events) = measure(&text, &path, &cache);
                walls.push(wall);
                for event in events {
                    stages
                        .entry(event.stage)
                        .or_default()
                        .push(event.duration_ns as f64 / 1_000_000.0);
                }
            }
            let report = stages
                .into_iter()
                .map(|(stage, mut values)| format!("{stage}={:.3}ms", median(&mut values)))
                .collect::<Vec<_>>()
                .join(" ");
            println!(
                "functions={functions} warm={warm} wall={:.3}ms {report}",
                median(&mut walls)
            );
        }
    }
}
