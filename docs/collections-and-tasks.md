# Collections and cooperative tasks

These are initial, closed-world facilities. They do not implement dynamic
plugins, a linker-section registration ABI, a work-stealing scheduler, an OS
I/O reactor, or suspension at arbitrary points in ordinary functions.

## Frozen syntax collections

```lisp syntax
(#syntax-collection ApplicationErrors)
(#syntax-contribute ApplicationErrors filesystem (FileFailure u32))
(#syntax-contribute ApplicationErrors parser (ParseFailure u64))
(#import "library/collections.lim")
(@error-enum (#syntax-distribute ApplicationErrors) ApplicationError)
```

Contributions can live in different imported files. The compiler first loads
the active cfg-selected import graph, then freezes collections, then runs
generators. Registration order and import traversal order do not determine
entry order: entries are sorted lexicographically by their explicit keys.
Repeated imports contribute once. Identical values under the same key are
deduplicated; conflicting values are errors. Unknown collections and duplicate
collection declarations are errors. Generators cannot add collections or
contributions after freezing.

A call-site argument `(#syntax-distribute Collection)` explicitly requests its
frozen snapshot. Generator parameters are plain syntax bindings; passing a
bare collection name passes that symbol, not its contents. A literal list can
also be supplied, allowing generators to forward snapshots. Helpers declared
with `#gn-fn` receive the same syntax values. Generator cache keys and
invocation deduplication include the resolved list.
The existing broader cfg/import dependency context is also still included.

`#gn-length` takes one syntax list and produces an integer literal containing
its length. The user-defined generators in `library/collections.lim` use these
facilities to produce ordinary inspectable declarations in `.lim`:

- `(@error-enum (#syntax-distribute Collection) Type)` emits a concrete enum
  with inline payloads.
  Allocation freedom also depends on the payload types. The largest variant
  determines payload storage, with tag and alignment overhead.
- `(@distributed-slice (#syntax-distribute Collection) StaticName ElementType)`
  emits a homogeneous static array. Its length and contents are fixed before
  type checking. Use `#slice-of` to borrow the array; access requires `#unsafe`
  like other statics.

Adding or removing a contribution can change enum layout and discriminants.
These generated types are build-local, not stable serialization or FFI schemas.

## Explicit task protocol

Import `library/tasks.lim`. A task has a concrete state enum and a concrete
poll-result enum. The task generator emits `#linear` for the state type, so
even an all-numeric state cannot be implicitly copied or silently abandoned.

```lisp syntax
(@task (Count CountPoll CountPending CountReady) u64 ((Counting u64)))
```

Write a free-standing poll function with exactly the named argument `task`:
`Count -> CountPoll`. Each call consumes the old state and returns either
`(CountPending next-state)` or `(CountReady result)`. No function pointers,
trait objects, hidden allocations, implicit captures, or recursive calls are
introduced. Explicit `#clone` remains governed by the normal language rules;
resource-owning task implementations must not promise invalid clone behavior.

`(#linear Type)` applies to a concrete struct or enum and disables implicit
structural Copy for that type and aggregates containing it. It does not change
layout or Send/Sync. Reference values themselves retain their existing rules.

## Fixed-capacity executors

```lisp syntax
(@executor run-counts Counts
  ((first Count CountPoll CountPending CountReady count-poll u64 first-input)
   (second Count CountPoll CountPending CountReady count-poll u64 second-input)))
```

Each job descriptor is
`(name Task Poll Pending Ready poll-function Result input-parameter)`.
The generator emits a result struct with one field per job and a function
accepting one task per job. This is a statically sized, heterogeneous join:
capacity is the number of descriptors, with no dynamic spawn queue. Job lists
can also come from frozen syntax collections via an explicit
`(#syntax-distribute Jobs)` argument.

The executor polls each pending job once per round using direct calls, retains
completed results, and returns when every job is ready. Poll functions must
return promptly for cooperative fairness. A permanently pending task keeps
the executor running. This initial driver busy-polls: it has no wake queue,
blocking I/O integration, timeout, or preemption. Task and result storage is
inline; task implementations can still explicitly allocate if they choose.
The local name `lim.executor.waiting` is reserved by this generator.

## Bounded ready queue foundation

```lisp syntax
(@ready-queue ReadyQueue QueueEnqueue QueueDequeue
  queue-create queue-enqueue queue-dequeue
  QueueEnqueued QueueFull QueueItem QueueEmpty
  (worker-a worker-b worker-c))
```

Import `library/ready_queue.lim` to use this generator. Every generated type,
function, and variant name is an explicit literal argument, so multiple
concrete queues can coexist. The final literal list fixes capacity; its
entries identify slots for generation but are not runtime queue contents.
`queue-create` makes an empty queue. `queue-enqueue` takes a mutable queue
reference and a `u64` `task-id`, returning `QueueEnqueued` or `QueueFull`.
`queue-dequeue` takes the mutable reference and returns `(QueueItem task-id)`
or `QueueEmpty`. The queue is FIFO, fixed-size, and has no dynamic allocation.
Its generated type is `#linear`: a queue owner must be consumed or explicitly
forgotten, and an implicit copy cannot duplicate its scheduling state.
Its current aggregate-value update copies the fixed array on each operation,
so this is a correctness foundation, not a constant-time scheduler queue.

These `u64` values are not wake handles. There is no generation check, OS
readiness registration, non-busy wait, or cancellation acknowledgment yet;
none of the safe asynchronous-I/O guarantees in ASYNC-02 are provided by this
queue alone. See `examples/ready_queue.lim` for a runnable wraparound case.

`library/wake_tokens.lim` adds a separate concrete `WakeTable4` protocol.
Registration returns a `WakeToken4` containing a slot and generation;
validity and retirement reject stale or out-of-range tokens. An active slot
cannot be registered twice. Retirement advances the generation with
saturation, so exhausted slots cannot wrap back to an old generation. The
table is linear and opaque outside its defining module. Callers cannot forge
tokens or mutate generation state. Non-busy waiting and OS-operation ownership
remain separate work.
`examples/wake_tokens.lim` exercises retirement and re-registration.

`library/wake_ready4.lim` owns a `WakeTable4` and a four-slot coalescing ready
set. Register a slot *before* polling. A local-waker callback calls
`wake-ready4-notify` with its registered token; the queue validates the
generation before recording a ready bit. After Pending, `wake-ready4-take`
consumes the bit. A wake during polling remains visible, duplicates occupy
one bit, and a retired token cannot affect a reused slot. Registration and
retirement require a mutable queue reference; notify and take use a shared
one. The opaque queue is local-only, not a cross-thread notifier.
`examples/wake_ready4.lim` covers capacity, duplicates, and stale handles;
`examples/async_registered_wake.lim` connects it to `@async-wake`. There is
still no non-busy wait, OS readiness, or general task scheduler.

## Borrowed local wakers

Import `library/local_waker.lim` to generate a concrete, single-threaded wake
handle with no function pointers:

```lisp syntax
(@local-waker
  (CounterWaker counter-waker-create counter-waker-wake
    counter-waker-wake-by-ref counter-waker-clone counter-waker-destroy)
  (WakeCounter WakeMetadata)
  (counter-notify metadata-clone metadata-destroy))
```

The generated linear `CounterWaker` owns a `WakeMetadata` and holds a
`(#ref WakeCounter)`. Its reference cannot outlive the executor. The
`#ptr u8` field is an unused marker that makes it neither Send nor Sync under
the current structural rules; it is never dereferenced. `wake-by-ref` calls
`counter-notify`, retaining the handle; `wake` calls it and then destroys the
handle. `clone` calls `metadata-clone` to create independent owned metadata.
`destroy` passes the owned metadata to `metadata-destroy`, which must consume
or explicitly forget it. Callers must explicitly wake or destroy every owned
handle. All generated declarations appear in the ordinary `.lim` cache.

The three user-supplied callbacks are ordinary functions with these exact
signatures (substitute the concrete type names):

```lisp syntax
(#fn counter-notify ((executor (#ref WakeCounter))
                     (metadata (#ref WakeMetadata))) () ...)
(#fn metadata-clone ((metadata (#ref WakeMetadata))) WakeMetadata ...)
(#fn metadata-destroy ((executor (#ref WakeCounter))
                       (metadata WakeMetadata)) () ...)
```

The handle is only a *local wake adapter*. Its fields are public, so callback
metadata should carry an opaque `WakeToken4` and validate it against live
registration state. The `wake_ready4` protocol supplies a bounded ready set;
the adapter alone does not provide OS I/O registration or non-busy waiting.
See `examples/local_waker.lim` for a complete runnable example.

## Explicit async composition

```lisp syntax
(@async (Pipeline PipelinePoll PipelinePending PipelineReady pipeline-poll) u64
  ((Begin (#await Count CountPending CountReady count-poll)
     (#then Finish next-count))
   (Finish (#await Count CountPending CountReady count-poll)
     (#return))))
```

Each stage stores exactly one concrete child task. Polling the parent polls
that child once. When the child finishes, `#then` calls its named continuation
with a `value` argument to construct the next stage's child. `#return` completes
the parent. The parent yields Pending after a transition, preventing an
unbounded chain of transitions within one parent poll. Continuations and poll
functions are ordinary strongly checked functions.

Here `#await`, `#then`, and `#return` are syntax interpreted by the user-defined
`@async` generator. This is **not** `#async-fn` or arbitrary suspension inside
ordinary function bodies. State names and continuation functions are explicit.
To carry additional data, put it in concrete child states and result types.
No local stack reference is silently captured: generated enums and functions
undergo the existing borrow checks. Self-referential movable task frames are
not added, and no pinning guarantee is provided.

An arbitrary async function will need its body lowered into a concrete state
machine with an explicit poll context carrying a local waker. Each `#await`
must preserve live locals and loans in that state; poll returns Pending only
after the awaited operation has registered the wake. Ready returns its value,
and cancellation consumes the suspended state and its resources. A first
version should reject borrows that cross suspension if they would make the
frame self-referential; supporting those later requires immovable frame
storage and a corresponding borrow-checker rule. The current `@async` and
`@local-waker` do not perform this lowering.

For explicit state composition that already needs a wake context, use
`@async-wake` with the same stage descriptors as `@async` and one additional
concrete waker type:

```lisp syntax
(@async-wake
  (Pipeline PipelinePoll PipelinePending PipelineReady pipeline-poll) u64
  ((Only (#await Step StepPending StepReady step-poll) (#return)))
  LocalWaker)
```

The generated `pipeline-poll` takes `task` and `waker (#ref LocalWaker)`.
Every named child poll must take those same argument names and waker type;
the generated code forwards the borrow without retaining it. The child can
use `wake-by-ref` before returning Pending. The poll driver must register a
token before polling and consult its ready bit after Pending; see
`examples/async_registered_wake.lim` for a runnable validated cycle. The
bare `@async-wake` expansion does not perform registration itself. See
`examples/async_wake_pipeline.lim` for the adapter-only cycle.

## Compiler-lowered async functions (sequential subset)

`@async-fn` is a built-in inspectable code generator. It reads a `#fn` form
whose declared result type is the eventual value, then emits an ordinary
linear frame enum, poll-result enum, start function (using the source function
name), and named poll/stage helpers. `@async-fn-pinned` emits the same concrete
state machine with a different polling ABI: pin the returned frame in a
mutable local, and each Pending result carries the same `#pin-ref-mut Frame`
into the next poll. A Ready result consumes that pin reference; the frame
remains in its Done state until explicitly forgotten or destroyed. Its
`poll-cancel` helper consumes the pin reference, marks the frame Done, and
returns the previous state so caller-defined cleanup can release captured
values. Neither generator currently supports self-references inside frames.
The emitted Lim is cached in `.lim/cache` and undergoes normal type, borrow,
linearity, and code generation checks:

```lisp syntax
(@async-fn (: names (Work WorkPoll WorkPending WorkReady work-poll) : waker LocalWaker : function (#fn work ((offset u64)) u64
    (#let child Step (Waiting 1u64))
    (#let value u64
      (#await (offset) Step StepPending StepReady step-poll child))
    (#return (#u64.+.wrap value offset)))))
```

`(#call work (: offset 1u64))` creates a `Work` frame. It does not
execute the body. With `@async-fn`, `work-poll` takes `(task Work)` and
`(waker (#ref LocalWaker))`, consumes the old frame, and returns `WorkPending`
with a new frame or `WorkReady` with the result. With `@async-fn-pinned`,
poll instead takes `(task (#pin-ref-mut Work))`; Pending carries that same
pin reference, keeping the frame at its original address. The child poll must
accept the named arguments `task` and `waker`. The first poll runs the body up to
`#await`; if the child is already Ready, execution continues in that poll.
Later polls resume the stored state. Multiple sequential awaits are allowed.

At a top-level binding, `#await` has the form
`(#await ChildTask PendingVariant ReadyVariant poll-function child-expression)`.
When nested inside another value expression, put the awaited result type
immediately after `#await`. Values live after suspension are inferred from the
continuation; there is no capture list. Unused linear values must be consumed
before suspension. Sequential stages
preserve `#mut` parameters and `#let-mut` local state across suspension;
assignments to captured mutable locals run in the resume helper. Each async
body still ends with one explicit `#return`; a direct `#await` in that return
is lowered as a final stage.
`#await` in a binding must still be the entire initializer of a top-level
binding. An `#if`, `#match`, or `#block` that contains no nested `#await` may
run between stages. Control flow whose branches themselves suspend and loops
crossing a suspension are not yet lowered. At most 32 awaits are accepted.
References into pre-suspension locals cannot be retained in the frame; the
ordinary borrow checker rejects them.

Cancellation is still explicit and caller-defined: a free-standing function
must match each generated frame state, consume its captured values, and call
the relevant child cancellation function. With `@async-fn-pinned`, first call
`poll-cancel` to consume the pinned handle and recover the state to clean up.
Adding a new `#await` adds a state and makes an old exhaustive cancellation
match fail compilation until it is updated. `examples/async_fn.lim` shows the
movable frame API; `examples/async_fn_pinned.lim` shows in-place Pending/resume
and cancellation; `examples/async_fn_two_awaits.lim` exercises sequential
awaits. These lowerings do not themselves add a scheduler or OS readiness.
The explicit `wake_ready4` protocol can prevent lost wakes when used around
polling.

## Cancellation and threads

`(@task-cancel cancel-function Task ((State handler) ...))` generates an
exhaustive match consuming a task. Every state must have one payload; each
handler accepts that payload as `task`, consumes its owned resources, and
returns `()`. Cleanup occurs only when this function is explicitly called.
There is no automatic cancellation when a task goes out of scope. `#forget`
intentionally bypasses cleanup; it is not a cancellation operation.

A handler for an external operation must finish cancellation before releasing
any borrowed storage the operation can still access. The compiler checks
types, consumption, and borrows, not OS cancellation completion.
`library/timer_reactor1.lim` provides a concrete one-shot Linux timer
operation. It owns a timer fd, scratch mapping, and validated wake token.
`timer-reactor1-wait` blocks in the kernel's `poll` rather than spinning;
`timer-reactor1-poll` reads expiration only after readiness. The kernel does
not retain the scratch buffer between calls, and `timer-reactor1-cancel`
consumes the owner, closes the fd, and unmaps the buffer.
`timer-reactor1-create` returns `TimerCreated1` or `TimerCreateFailed1`;
failure paths clean up any acquired fd or mapping. Multi-operation readiness
is available for two distinct borrowed timers through `timer-reactor2-wait`:
one blocking kernel poll marks each ready token independently, without moving
either owner or exposing its fd. `examples/timer_pair.lim` exercises both
owners, including the same-owner rejection. Arbitrary registration, general
owners, including the same-owner rejection. `timer-reactor-many-wait` accepts
a runtime slice of one to four shared timer borrows, rejects duplicate owners,
and reports each ready slot in a bit mask after one blocking poll. The
three-timer case is exercised by `examples/timer_reactor_many.lim`. Registration
for other descriptor types, joining timer and I/O sources in one wait,
executor shutdown, and externally interrupting a blocking run remain open.

`(@threaded-executor run Result jobs Worker)` expands an executor plus
`(@thread-spawn (: task Worker : worker run))`. Each job names both its result
field/state binding and a distinct worker-input parameter, for example
`(number NumberTask NumberPoll NumberPending NumberReady number-poll u64 number-input)`.
The spawn call uses that worker-input name as its named argument; the result
field keeps the first name (`number` in this example).
Each explicit spawn transfers the fixed job set to one OS worker. Multiple
spawns can run concurrently; this is not task
migration or a worker pool. Structural Send/Sync, spawn failures, mandatory
joins, and captured-reference restrictions come from the existing thread
implementation. OS thread creation still uses its existing allocation path.

Runnable examples: `distributed_errors.lim`, `distributed_slice.lim`,
`local_waker.lim`, `async_wake_pipeline.lim`, `async_registered_wake.lim`,
`wake_ready4.lim`, `timer_reactor1.lim`, `timer_pair.lim`,
`timer_reactor_many.lim`, `async_fn.lim`,
`async_fn_two_awaits.lim`,
`cooperative_tasks.lim`, `async_pipeline.lim`, `task_cancellation.lim`, and
`threaded_tasks.lim` in `examples/`.
