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

#[cfg(test)]
mod tests {
    use super::*;
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
