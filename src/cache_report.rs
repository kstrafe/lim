use std::{cell::RefCell, path::Path};

thread_local! { static EVENTS: RefCell<Option<Vec<String>>> = const { RefCell::new(None) }; }

/// Observe cache decisions on this thread without changing cache identity.
/// Nested observations are isolated and the previous observer is restored.
pub fn with_cache_report<R>(operation: impl FnOnce() -> R) -> (R, String) {
    struct Restore(Option<Vec<String>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            EVENTS.with(|events| {
                events.replace(self.0.take());
            });
        }
    }
    let _restore = Restore(EVENTS.with(|events| events.replace(Some(Vec::new()))));
    let result = operation();
    let records = EVENTS.with(|events| events.borrow_mut().take().unwrap());
    (
        result,
        format!(
            "{{\"schema_version\":1,\"events\":[{}]}}",
            records.join(",")
        ),
    )
}

pub(crate) fn record(kind: &str, path: &Path, key: &str, decision: &str) {
    EVENTS.with(|events| {
        let mut events = events.borrow_mut();
        let Some(events) = events.as_mut() else { return };
        let quote = crate::diagnostic_json::quoted;
        events.push(format!("{{\"kind\":{},\"artifact\":{},\"decision\":{},\"key\":\"{:032x}\",\"key_material\":{}}}",
            quote(kind), quote(&path.to_string_lossy()), quote(decision),
            crate::generator::stable_hash(key.as_bytes()), quote(key)));
    });
}
