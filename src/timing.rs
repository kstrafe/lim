//! Opt-in, thread-local compiler timing collection.
use std::{cell::RefCell, time::Instant};

#[derive(Clone, Debug, PartialEq)]
pub struct TimingEvent {
    pub stage: String,
    pub duration_ns: u128,
}

#[derive(Default)]
struct Collector {
    events: Vec<TimingEvent>,
    details: Vec<(&'static str, u128)>,
    depth: usize,
}

thread_local! { static COLLECTOR: RefCell<Option<Collector>> = const { RefCell::new(None) }; }

pub struct TimingSession {
    started: Instant,
    previous: Option<Collector>,
    finished: bool,
}

impl TimingSession {
    pub fn start() -> Self {
        let previous = COLLECTOR.with(|slot| slot.borrow_mut().replace(Collector::default()));
        Self {
            started: Instant::now(),
            previous,
            finished: false,
        }
    }

    pub fn finish(mut self) -> Vec<TimingEvent> {
        let collector = COLLECTOR.with(|slot| slot.borrow_mut().take().unwrap_or_default());
        COLLECTOR.with(|slot| *slot.borrow_mut() = self.previous.take());
        self.finished = true;
        let mut events = collector.events;
        events.extend(
            collector
                .details
                .into_iter()
                .map(|(name, duration_ns)| TimingEvent {
                    stage: name.into(),
                    duration_ns,
                }),
        );
        events.push(TimingEvent {
            stage: "total".into(),
            duration_ns: self.started.elapsed().as_nanos(),
        });
        events
    }
}

impl Drop for TimingSession {
    fn drop(&mut self) {
        if !self.finished {
            COLLECTOR.with(|slot| *slot.borrow_mut() = self.previous.take());
        }
    }
}

pub struct Stage {
    name: &'static str,
    started: Option<Instant>,
}

/// Aggregate inclusive semantic substage times, even inside an outer stage.
/// Repeated function solves produce one event, not one event per function.
/// Nested categories overlap; their durations must not be added to total time.
pub(crate) fn detail(name: &'static str) -> Detail {
    let started = COLLECTOR.with(|slot| slot.borrow().as_ref().map(|_| Instant::now()));
    Detail { name, started }
}

pub(crate) struct Detail {
    name: &'static str,
    started: Option<Instant>,
}

impl Drop for Detail {
    fn drop(&mut self) {
        let Some(started) = self.started else { return };
        let elapsed = started.elapsed().as_nanos();
        COLLECTOR.with(|slot| {
            if let Some(collector) = slot.borrow_mut().as_mut() {
                if let Some((_, duration)) = collector
                    .details
                    .iter_mut()
                    .find(|(name, _)| *name == self.name)
                {
                    *duration += elapsed;
                } else {
                    collector.details.push((self.name, elapsed));
                }
            }
        });
    }
}

pub fn stage(name: &'static str) -> Stage {
    let started = COLLECTOR.with(|slot| {
        let mut slot = slot.borrow_mut();
        if let Some(collector) = slot.as_mut() {
            collector.depth += 1;
            Some(Instant::now())
        } else {
            None
        }
    });
    Stage { name, started }
}

impl Drop for Stage {
    fn drop(&mut self) {
        let Some(started) = self.started else {
            return;
        };
        let duration_ns = started.elapsed().as_nanos();
        COLLECTOR.with(|slot| {
            if let Some(collector) = slot.borrow_mut().as_mut() {
                collector.depth = collector.depth.saturating_sub(1);
                if collector.depth == 0 {
                    collector.events.push(TimingEvent {
                        stage: self.name.into(),
                        duration_ns,
                    });
                }
            }
        });
    }
}

pub fn render(events: &[TimingEvent], json: bool) -> String {
    if json {
        let entries = events
            .iter()
            .map(|event| {
                format!(
                    "{{\"stage\":{},\"duration_ns\":{}}}",
                    crate::diagnostic_json::quoted(&event.stage),
                    event.duration_ns
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        format!("{{\"timings\":[{entries}]}}")
    } else {
        events
            .iter()
            .map(|event| {
                format!(
                    "timing {:<24} {:.3} ms",
                    event.stage,
                    event.duration_ns as f64 / 1_000_000.0
                )
            })
            .collect::<Vec<_>>()
            .join("\n")
    }
}

#[cfg(all(test, not(feature = "proof-kernel-tests")))]
mod tests {
    use super::*;
    #[test]
    fn details_aggregate_inside_stages_without_hiding_outer_stage() {
        let session = TimingSession::start();
        {
            let _outer = stage("semantic_validate");
            for _ in 0..3 {
                let _detail = detail("semantic.provenance");
                let _suppressed = stage("inner");
            }
        }
        let events = session.finish();
        assert_eq!(
            events
                .iter()
                .filter(|e| e.stage == "semantic.provenance")
                .count(),
            1
        );
        assert!(events.iter().any(|e| e.stage == "semantic_validate"));
        assert!(!events.iter().any(|e| e.stage == "inner"));
        assert_eq!(events.last().unwrap().stage, "total");
    }

    #[test]
    fn disabled_details_do_not_start_a_clock() {
        assert!(detail("disabled").started.is_none());
    }

    #[test]
    fn detail_sessions_are_isolated_and_restore_on_drop() {
        let outer = TimingSession::start();
        {
            let _d = detail("outer");
        }
        {
            let inner = TimingSession::start();
            {
                let _d = detail("inner");
            }
            assert!(inner.finish().iter().any(|e| e.stage == "inner"));
        }
        {
            let _inner = TimingSession::start();
            let _d = detail("discarded");
        }
        {
            let _d = detail("outer");
        }
        let events = outer.finish();
        assert_eq!(events.iter().filter(|e| e.stage == "outer").count(), 1);
        assert!(!events
            .iter()
            .any(|e| e.stage == "inner" || e.stage == "discarded"));
    }
    #[test]
    fn only_outermost_nested_stage_is_reported_and_failures_still_record() {
        let session = TimingSession::start();
        {
            let _outer = stage("pipeline");
            let _inner = stage("inner");
        }
        let events = session.finish();
        assert_eq!(events.iter().filter(|e| e.stage == "pipeline").count(), 1);
        assert!(!events.iter().any(|e| e.stage == "inner"));
    }

    #[test]
    fn nested_sessions_restore_the_outer_collector() {
        let outer = TimingSession::start();
        {
            let inner = TimingSession::start();
            let _ = inner.finish();
        }
        {
            let _outer_stage = stage("outer_after_inner");
        }
        let events = outer.finish();
        assert!(events
            .iter()
            .any(|event| event.stage == "outer_after_inner"));
    }

    #[test]
    fn dropping_session_restores_the_previous_collector() {
        let outer = TimingSession::start();
        {
            let _inner = TimingSession::start();
        }
        {
            let _outer_stage = stage("outer_after_drop");
        }
        let events = outer.finish();
        assert!(events.iter().any(|event| event.stage == "outer_after_drop"));
    }

    #[test]
    fn json_stage_names_use_diagnostic_json_escaping() {
        let rendered = render(
            &[TimingEvent {
                stage: "stage\"\nname".into(),
                duration_ns: 1,
            }],
            true,
        );
        assert_eq!(
            rendered,
            "{\"timings\":[{\"stage\":\"stage\\\"\\nname\",\"duration_ns\":1}]}"
        );
    }
}
