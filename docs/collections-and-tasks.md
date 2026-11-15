# Collections and cooperative tasks

These are initial, closed-world facilities. They do not implement dynamic
plugins, a linker-section registration ABI, a work-stealing scheduler, a
general-purpose OS I/O reactor, or suspension at arbitrary points in ordinary
functions.

Async function forms are handled by the built-in Rust generator. `#await` is
input to that generator; its emitted `.lim` declarations contain ordinary
functions, enums, and ownership operations. The compiler checks and builds
those declarations through the same rules as handwritten Lim. Generator
validation witnesses are internal bookkeeping: they are not emitted and do
not grant generated functions special borrowing or typechecking privileges.

## Distributed enums

```lisp syntax
#distributed-enum ApplicationError ()
#enum-contribute ApplicationError (ApplicationError.FileFailure #u32)
#enum-contribute ApplicationError (ApplicationError.ParseFailure #u64)
```

Contributions can live in different imported files or be emitted by generators.
The compiler expands generators (or replays their cached code), then assembles
ordinary enum declarations and compiles the complete program. There are no
collection snapshots, expansion dependencies, or fixed-point iterations.

Each contribution declares exactly one variant. Its name is its key. Identical
definitions deduplicate; conflicting definitions are errors with both source
locations. Variants are sorted lexicographically by name, independently of
import order. A contribution may precede the central declaration. Unknown
targets and duplicate central declarations are errors.
The completed enum requires at least one variant, like an ordinary enum.
Declaration-only modules must be checked through an entry that imports their
contributors; the example manifest records that context explicitly.

The central declaration owns the property list, including optional `#linear`
and `#repr-c`. Owned linear payloads propagate linearity normally. Payloads are
inline, so the enum itself needs no allocation; payload types may still allocate.
Generators may refer to the final enum and its constructors, but cannot inspect
an unfinished list of variants. Generator arguments remain literal syntax.

For fixed tables use ordinary static arrays. For executor generation pass an
explicit literal list of task descriptors at the composition site.

Adding or removing a contribution can change enum layout and discriminants.
These generated types are build-local, not stable serialization or FFI schemas.

## Explicit task protocol

Use `#std/tasks.lim::task`. A task has a concrete state enum and a concrete
poll-result enum. The task generator emits `#linear` for the state type, so
even an all-numeric state cannot be implicitly copied or silently abandoned.

```lisp syntax
#generate #std/tasks.lim::task {
  names = (Count CountPoll CountPoll.CountPending CountPoll.CountReady);
  result = #u64;
  states = ((Count.Counting #u64));
}
```

Write a free-standing poll function with exactly the named argument `task`:
`Count -> CountPoll`. Each call consumes the old state and returns either
`(CountPending next-state)` or `(CountReady result)`. No function pointers,
trait objects, hidden allocations, implicit captures, or recursive calls are
introduced. Explicit `#clone` remains governed by the normal language rules;
resource-owning task implementations must not promise invalid clone behavior.

`#linear` is a type property written in the struct or enum declaration's
property list. Structs and enums become linear automatically when they own a
linear field or any enum variant has a linear payload. References do not
transfer linearity because they do not own their referents. Explicit `#linear`
forces linearity even when every field or payload is plain data. It does not
change layout or Send/Sync. Reference values themselves retain their existing
rules.

## Fixed-capacity executors

```lisp syntax
#generate #std/tasks.lim::executor {
  run = run-counts;
  result = Counts;
  jobs = ((first Count CountPoll CountPending CountReady count-poll #u64 first-input)
     (second Count CountPoll CountPending CountReady count-poll #u64 second-input));
}
```

Each job descriptor is
`(name Task Poll Pending Ready poll-function Result input-parameter)`.
The generator emits a result struct with one field per job and a function
accepting one task per job. This is a statically sized, heterogeneous join:
capacity is the number of descriptors, with no dynamic spawn queue. The complete
job list is an explicit literal generator argument.

The executor polls each pending job once per round using direct calls, retains
completed results, and returns when every job is ready. Poll functions must
return promptly for cooperative fairness. A permanently pending task keeps
the executor running. This basic driver busy-polls; use
`#std/tasks.lim::wake-executor` when tasks can register wake handles.
Task and result storage is inline; task
implementations can still explicitly allocate if they choose. The local name
`lim.executor.waiting` is reserved by this generator.

## Bounded ready queue foundation

```lisp syntax
#generate #std/ready_queue.lim::ready-queue {
  name = ReadyQueue;
  enqueue-result = QueueEnqueue;
  dequeue-result = QueueDequeue;
  create = queue-create;
  enqueue = queue-enqueue;
  dequeue = queue-dequeue;
  enqueued = QueueEnqueue.QueueEnqueued;
  full = QueueEnqueue.QueueFull;
  item = QueueDequeue.QueueItem;
  empty = QueueDequeue.QueueEmpty;
  slots = (worker-a worker-b worker-c);
}
```

The `#std/ready_queue.lim` path selects this library generator. Every generated type,
function, and variant name is an explicit literal argument, so multiple
concrete queues can coexist. The final literal list fixes capacity; its
entries identify slots for generation but are not runtime queue contents.
`queue-create` makes an empty queue. `queue-enqueue` takes a mutable queue
reference and a `#u64` `task-id`, returning `QueueEnqueued` or `QueueFull`.
`queue-dequeue` takes the mutable reference and returns `(QueueItem task-id)`
or `QueueEmpty`. The queue is FIFO, fixed-size, and has no dynamic allocation.
Its generated type is `#linear`: a queue owner must be consumed or explicitly
forgotten, and an implicit copy cannot duplicate its scheduling state.
Its current aggregate-value update copies the fixed array on each operation,
so this is a correctness foundation, not a constant-time scheduler queue.

These `#u64` values are not wake handles. There is no generation check, OS
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
`examples/async_registered_wake.lim` connects it to
`#std/tasks.lim::async-wake`. The bounded `#std/tasks.lim::wake-executor`
below composes the ready set with task polling and blocking readiness.

## Borrowed local wakers

Use `#std/local_waker.lim::local-waker` to generate a concrete, single-threaded wake
handle with no function pointers:

```lisp syntax
#generate #std/local_waker.lim::local-waker {
  names = (CounterWaker counter-waker-create counter-waker-wake
      counter-waker-wake-by-ref counter-waker-clone counter-waker-destroy);
  types = (WakeCounter WakeMetadata);
  callbacks = (counter-notify metadata-clone metadata-destroy);
}
```

The generated linear `CounterWaker` owns a `WakeMetadata` and holds a
`(#ref WakeCounter)`. Its reference cannot outlive the executor. The
`#ptr #u8` field is an unused marker that makes it neither Send nor Sync under
the current structural rules; it is never dereferenced. `wake-by-ref` calls
`counter-notify`, retaining the handle; `wake` calls it and then destroys the
handle. `clone` calls `metadata-clone` to create independent owned metadata.
`destroy` passes the owned metadata to `metadata-destroy`, which must consume
or explicitly forget it. Callers must explicitly wake or destroy every owned
handle. All generated declarations appear in the ordinary `.lim` cache.

The three user-supplied callbacks are ordinary functions with these exact
signatures (substitute the concrete type names):

```lisp syntax
#fn counter-notify {
  #params = ((executor (#ref WakeCounter))
                       (metadata (#ref WakeMetadata)));
  #returns = ();
  #body = ( ...
  );
}
#fn metadata-clone {
  #params = ((metadata (#ref WakeMetadata)));
  #returns = WakeMetadata;
  #body = ( ...
  );
}
#fn metadata-destroy {
  #params = ((executor (#ref WakeCounter))
                         (metadata WakeMetadata));
  #returns = ();
  #body = ( ...
  );
}
```

The handle is only a *local wake adapter*. Its fields are public, so callback
metadata should carry an opaque `WakeToken4` and validate it against live
registration state. The `wake_ready4` protocol supplies a bounded ready set;
the adapter alone does not provide OS I/O registration or non-busy waiting.
See `examples/local_waker.lim` for a complete runnable example.

## Wake-driven fixed task set

Use `#std/tasks.lim::wake-executor` when all task slots have the same concrete
task, poll-result, output, and waker types:

```lisp syntax
#generate #std/tasks.lim::wake-executor {
  run = run-jobs;
  outputs = (JobResults JobOutcome JobLifecycle JobLifecycle.JobRunning
      JobOutcome.JobComplete JobLifecycle.JobCancelling JobOutcome.JobStopped);
  task-spec = (JobTask JobPoll JobPending JobReady #u64 job-poll LocalWaker);
  wait-spec = (WaitResult WaitReady WaitStopped #i64 wait-ready
      (sources (#slice AsyncPollSource4)));
  cancel-function = cancel-poll;
  jobs = ((first-state first-task first-waker first 0u32)
     (second-state second-task second-waker second 1u32));
}
```

Each job descriptor names its generated poll-state local, task input, borrowed
waker input, output field, and slot. Slots must be consecutive from zero and
there may be one to four jobs. The generated function polls every task once at
startup, then calls `wait-ready` only while tasks remain Pending. That function
returns the generated `WaitResult`: `(WaitReady mask)` when one or more tasks
are ready, or `(WaitStopped reason)` for shutdown or a wait error. The executor
directly calls the named poll function only for selected pending slots and
retains Ready values. It returns `JobOutcome` as either `(JobComplete results)`
or `(JobStopped reason)`. Repeated wakes can coalesce into one bit. There are
no function pointers, heap allocations, or worker threads.

`cancel-poll` has signature `((state JobPoll)) -> ()`. On shutdown or wait
failure, polling stops and the executor calls this function once for every
slot, in descriptor order, including slots already Ready. It must explicitly
consume the Pending task or Ready result and release any owned wakers or OS
operation state. Only after all handlers return does the executor return
`JobStopped`. On normal completion, cancellation handlers are not called.
The caller still owns each borrowed base waker and must destroy it after the
executor returns.

The wait context is an ordinary named function parameter, so callers can
adapt `async-poll4-wait` or another bounded reactor without hidden global
state. The callback maps OS errors and shutdown to `WaitStopped`; the
executor itself has no timeout policy, since a callback may represent timeout
as a stop reason. A `WaitReady` result must contain at least one valid pending
slot bit. The executor does not validate the callback's mask: zero masks and
bits for unregistered or completed tasks are ignored, and the callback is
invoked again while any task remains Pending. Thus a zero mask or a mask with
no bit for a Pending task can repeatedly wait without progress; callbacks must
return a nonzero mask intersecting the currently pending slots. Poll functions
must return promptly, and the single-threaded executor does not preempt them.
`examples/wake_executor.lim` demonstrates two tasks, per-task generational
wake tokens, duplicate-wake coalescing, timer-backed blocking wait, and
explicit waker destruction. The shutdown test verifies cancellation of both
a Pending state with an owned waker and an already-Ready result.

## Explicit async composition

```lisp syntax
#generate #std/tasks.lim::async {
  names = (Pipeline PipelinePoll PipelinePoll.PipelinePending PipelinePoll.PipelineReady pipeline-poll);
  result = #u64;
  stages = ((Pipeline.Begin (#await Count CountPending CountReady count-poll)
       (#then Pipeline.Finish next-count))
     (Pipeline.Finish (#await Count CountPending CountReady count-poll)
       (#return)));
}
```

Each stage stores exactly one concrete child task. Polling the parent polls
that child once. When the child finishes, `#then` calls its named continuation
with a `value` argument to construct the next stage's child. `#return` completes
the parent. The parent yields Pending after a transition, preventing an
unbounded chain of transitions within one parent poll. Continuations and poll
functions are ordinary strongly checked functions.

Here `#await`, `#then`, and `#return` are syntax interpreted by the user-defined
`#std/tasks.lim::async` generator. This is **not** `#async-fn` or arbitrary
suspension inside ordinary function bodies. State names and continuation functions are explicit.
To carry additional data, put it in concrete child states and result types.
No local stack reference is silently captured: generated enums and functions
undergo the existing borrow checks. Self-referential movable task frames are
not added, and no pinning guarantee is provided.

`#generate #async-fn` and `#generate #async-fn-pinned` lower the original function body through
the production graph planner and emitter into a concrete state machine with an
explicit poll context carrying a local waker. Suspension preserves the live
locals and checked loans in the frame; cancellation consumes the suspended
state through its explicit cleanup interface. Movable frames reject internal
references that remain live across Pending; use pinned frame storage when
references into the frame must survive suspension. The staged
`#std/tasks.lim::async` generator described above remains explicit state composition and does not
lower an arbitrary function body.

For explicit state composition that already needs a wake context, use
`#std/tasks.lim::async-wake` with the same stage descriptors as
`#std/tasks.lim::async` and one additional concrete waker type:

```lisp syntax
#generate #std/tasks.lim::async-wake {
  names = (Pipeline PipelinePoll PipelinePoll.PipelinePending PipelinePoll.PipelineReady pipeline-poll);
  result = #u64;
  stages = ((Pipeline.Only (#await Step StepPoll.StepPending StepPoll.StepReady step-poll) (#return)));
  waker = LocalWaker;
}
```

The generated `pipeline-poll` takes `task` and `waker (#ref LocalWaker)`.
Every named child poll must take those same argument names and waker type;
the generated code forwards the borrow without retaining it. The child can
use `wake-by-ref` before returning Pending. The poll driver must register a
token before polling and consult its ready bit after Pending; see
`examples/async_registered_wake.lim` for a runnable validated cycle. The
bare `#generate #std/tasks.lim::async-wake` expansion does not perform registration itself. See
`examples/async_wake_pipeline.lim` for the adapter-only cycle.

## Compiler-lowered async functions

`#generate #async-fn` is a built-in inspectable code generator. It reads a `#fn` form
whose result type is the eventual value, then emits an ordinary linear frame
struct with an explicit program counter and tagged storage cells, a poll-result
enum, the source-named constructor, and one dispatcher poll function. Pending
retains the already evaluated child; Ready advances to the next block in the
same poll. Calls to ordinary functions and separate child futures remain calls.

`#generate #async-fn-pinned` uses stationary frame storage. Pin the constructed frame in
a mutable local (or use a checked owned pin wrapper), then poll its
`#pin-ref-mut`. Pending returns the same capability for the next poll. Owner
fields do not move while their internal references or borrowing children live.
Ready consumes the poll capability and retires the frame's program counter;
polling a completed or cancelled frame traps instead of restarting its body.

Both generators provide `poll-cleanup`, returning source-named Empty/Full cells
for explicit destruction. Pinned cleanup consumes the poll capability and
empties the stationary frame before transferring independent owning values.
Dependent children are cancelled in place before their referents are extracted.
There is no public `Frame-state` or raw-state cancellation export.
`examples/async_single_poll.lim` shows repeated polling through an opaque
`#std/pin.lim::pin` handle whose storage is owned by `#std/pin.lim::pin-scope`;
its low-level adapter requires `#unsafe`, and cleanup completes before the
scope releases storage.

The emitted Lim is stored in `.lim/generated`, with cache metadata in
`.lim/cache`, and undergoes normal type, borrow, linearity, and code generation
checks.

Materialized generated `.lim` files begin with a `Generated from:` comment
listing the distinct `file:line` call sites that contributed to that artifact,
sorted for stable output. Cache hits append newly observed call sites without
rerunning generation. If all current sites are already recorded, neither the
source file nor its cache metadata is rewritten; earlier records are retained.

```lisp syntax
#generate #async-fn ((protocol WorkAwait) (waker LocalWaker) (function (#fn work ((offset #u64)) #u64
      (#let child Step (Waiting 1u64))
      (#let value #u64
        (#await Step StepPoll.StepPending StepPoll.StepReady step-poll child))
      (#return (#u64::add-wrap value offset)))))
```

`(#call work ((offset 1u64)))` creates a `Work` frame. It does not
execute the body. With `#generate #async-fn`, `Work::poll` takes `(task Work)` and
`(waker (#ref LocalWaker))`, consumes the old frame, and returns `WorkPending`
with a new frame or `WorkReady` with the result. With `#generate #async-fn-pinned`,
poll instead takes `(task (#pin-ref-mut Work))`; Pending carries that same
pin reference, keeping the frame at its original address. The child poll must
accept the named arguments `task` and `waker`. The first poll runs the body up to
`#await`; if the child is already Ready, execution continues in that poll.
Later polls resume the stored state. Multiple sequential awaits are allowed.

At a top-level binding, `#await` has the form
`(#await ChildTask PendingVariant ReadyVariant poll-function child-expression)`.
The shorter form is `(#await Protocol child-expression)`. A protocol bundle
includes the result type, task type, Pending/Ready variants and poll function,
so this spelling also works in supported nested value expressions without
repeating the result type. Declare a bundle for a handwritten task, or let
`#generate #async-fn` export it:

```lisp syntax
#generate #async-fn ((protocol WorkAwait) (waker LocalWaker)
    (function (#fn work ((offset #u64)) #u64
      (#return (#await StepAwait (Waiting offset))))))
// Inside another generated async function:
#let value #u64 (#await WorkAwait (#call work (($ offset))))
```

The generated names come from the source function name: `Work::Task`,
`Work::Poll`, `Work::Pending`, `Work::Ready`, and `Work::poll`.
Generated type names capitalize the first letter of the function name;
function and public variant names retain their original spelling. A pinned
function uses `Work::Frame` instead of `Work::Task`, and its bundle requires
`(#pin-ref-mut Work::Frame)`; pinning remains explicit. Supply `: protocol`
to name the exported bundle. Generated protocols are available across internal
and external imports, including forward references, and are inspectable in
the function's cached `.lim/generated/` file. Cancellation handlers remain
explicit. See `examples/async_composition.lim` for a parent task awaiting a
separate child through two polls.
When nested inside another value expression, put the awaited result type
immediately after `#await` when using the expanded spelling. Values live after suspension are inferred from the
continuation; there is no capture list. Unused linear values must be consumed
before suspension. Sequential stages
preserve `#mut` parameters and `#let-mut` local state across suspension;
assignments to captured mutable locals run in the corresponding dispatch arm.
Each async body still ends with one explicit `#return`; a direct `#await` in that return
is lowered as a final stage.
`#await` in a binding must still be the entire initializer of a top-level
binding unless it is nested in a supported value expression such as the right
hand side of `#set`; nested awaits require an explicit result type. For example,
`(#set total (#await #u64 Child Pending Ready child-poll task))` suspends before
assigning the result to the mutable local, whose value is retained in the frame.
An `#if`, `#match`, or `#block` may contain suspension. Awaited branches and
loop bodies are lowered from the checked control-flow graph, including
`#while` and `#for` conditions, initializers, bodies, and steps. For both loop
forms, a short-circuit
`#bool::and`/`#bool::or` condition may put an await on its right-hand side; the
child is polled only when that branch is selected. An awaited condition is
polled before each body decision, and Ready(false) skips the body. Loop
transfers follow the source control-flow and cleanup rules.
Value-producing awaited `#loop` expressions can exit through conditional or
match branches without a final direct `#break`. Result storage uses explicitly
declared binding and function types, concrete constructors, casts, and builtin
operation contracts; comparisons return `#bool`, not their operand type. The
ordinary checker still validates all break payloads and their ownership.
`examples/async_loop_results.lim` passes a linear struct produced by a function
call out of a suspended loop and consumes it explicitly. Branches, loop exits,
and their payload ownership are checked against the original function body.
Conditional await continuations may likewise change result type: a branch can
await a `#u64` and then yield a `#bool`, reference, or concrete linear aggregate.
Its generated Ready payload uses the branch's declared expression contract,
not the first awaited value's type. Returned and suspended references retain
their source loans; explicitly consuming a cancelled frame releases those
loans without implicitly destroying resources. See
`examples/async_branch_results.lim` for selected and immediate linear results.
Conditional expression helpers return changes to captured mutable locals
alongside their value, including changes through explicit mutable borrows.
Linear owners move into the selected child and are restored from its Ready
payload, not also stored in the parent. Replacing a local after suspension
does not silently consume its previous owner: that owner must have been
explicitly consumed or transferred before suspension.
Child-task expressions execute before the frame snapshots their captures,
both for the first await and after resume. Their side effects execute once,
not again when a Pending task is polled. A `#while` condition can await the
task needed by its outer boolean await; both dependencies run anew for each
condition evaluation. See `examples/async_condition_dependencies.lim` for
three condition evaluations, an early continue, and a suspending body. These
effects run at their corresponding source evaluation points in the graph plan.
Sequential suspension points have no fixed language-level count limit.
A movable `#generate #async-fn` cannot retain references into its own frame across
Pending. Poll-local borrows are allowed when checked physical storage proves
all internal handles retired before suspension. Use `#generate #async-fn-pinned` for
references into parent-owned storage that survive an await.

Pinned functions may borrow caller-owned storage or their own locals, including
owners initialized after an await or inside branches and loops. Shared and
exclusive references retain their actual selected field, tuple, array, or slice
projection. Index selection is checked and evaluated once; changing an index
later does not retarget a retained reference. Original-source borrow checking
still forbids conflicting access, moving referents, or exporting local loans.

Cancellation is explicit. `poll-cleanup` retires internal handles and returns
source-slot cleanup cells; consume these cells before accessing any external
referents they retain. A borrowing child requires a checked cancellation handler
that finishes before the parent's referents are destroyed. Pinned children are
cancelled through a pinned mutable reference, not moved out of their storage.
With a `:cancel` mapping, the generated dispatcher consumes independent Full
cells, and pinned `poll-destroy` performs cancellation and destruction in place.
`examples/async_fn.lim` shows the movable-frame protocol;
`examples/async_fn_cancel_dispatch.lim` shows generated dispatch;
`examples/async_fn_pinned.lim` shows in-place Pending/resume and cancellation;
`examples/async_fn_two_awaits.lim` exercises sequential awaits;
`examples/async_fn_self_reference.lim` exercises a pinned internal reference
across Pending and cancellation. These lowerings do not themselves add a
scheduler or OS readiness.
The explicit `wake_ready4` protocol can prevent lost wakes when used around
polling. `examples/async_fn_while_condition.lim` carries a mutable counter
through Pending, advances it after Ready(true), then skips the body on
Ready(false).

## Cancellation and threads

The task cancellation generator takes an exhaustive named record:

```lisp syntax
#generate #std/tasks.lim::task-cancel {
  cancel = cancel-function;
  task = Task;
  states = ((State handler));
}
```

The `states` list contains one `(State handler)` entry per state. The generated
function exhaustively matches and consumes a task. Every state must have one
payload; each handler accepts that payload as `task`, consumes its owned resources, and
returns `()`. Cleanup occurs only when this function is explicitly called.
There is no automatic cancellation when a task goes out of scope. `#forget`
intentionally bypasses cleanup; it is not a cancellation operation.

`#generate #async-fn` and `#generate #async-fn-pinned` can generate a cleanup dispatcher with an
optional `cancel` field. Map source binding names and `await-N` identities
to concrete handlers, not private program-counter states:

```lisp syntax
#generate #async-fn-pinned
    ((protocol WorkAwait)
     (waker LocalWaker)
     (cancel (cancel-work ((owner destroy-owner) (await-0 cancel-child))))
     (function
     (#fn work ((owner Owner)) #u64
       ...)))
```

Every exposed owning slot requires a handler. Missing, duplicate, unknown,
unsafe, or incorrectly typed handlers are rejected. Independent handlers consume
one concrete owned value and return `()`. Only Full cells invoke them, so
repeated pinned cleanup does not repeat destruction. `Work::poll::cleanup` returns
`Work::Frame::Cleanup`; pass that aggregate to `cancel-work`, or use the generated
pinned `Work::poll::destroy` entry point to perform both operations in place.
Dependent children are retired before their lenders, rather than returned beside
their borrowed parent storage. A pinned dependent handler takes a pinned mutable
reference and returns `()`.

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
owners, including the same-owner rejection. `timer-reactor-many-wait` accepts
a runtime slice of one to four shared timer borrows, rejects duplicate owners,
and reports each ready slot in a bit mask after one blocking poll. The
three-timer case is exercised by `examples/timer_reactor_many.lim`.

`library/async_stdin_byte.lim` demonstrates a cancellable one-shot readiness
read. `async-byte-read1-create` retains an exclusive borrow of the destination
and duplicates the supplied descriptor with close-on-exec into an opaque
linear task. The task closes that owned descriptor during destruction; if
scratch allocation fails after duplication, creation closes it before
returning the setup or cleanup error. Creation requires an already nonblocking
descriptor and returns `-22` otherwise. Call `async-byte-read1-enable-nonblocking`
explicitly first; this changes status flags on the shared open-file description,
so aliases observe the change and it remains set after task destruction. A
readiness race then returns `EAGAIN`/Pending instead of blocking. The wait blocks
in Linux `poll` and records a generation-checked wake. A later poll
performs one synchronous byte read only after readiness, returning a byte, EOF,
or an OS error. The OS never retains the destination pointer, so destroying a
pending task retires its wake and releases the borrow immediately; callers must
not poll or wait after destruction. `examples/async_stdin_byte.lim` echoes one
byte after closing the caller's original stdin descriptor, and
`examples/async_stdin_cancel.lim` verifies that the destination can
be mutated after cancellation while the input stream is still open.
`examples/async_stdin_race.lim` steals the byte that made the descriptor ready
and verifies that the operation remains Pending until a later byte arrives.
These examples use `library/async_poll4.lim`, which waits on one to four borrowed
poll sources with one blocking syscall and notifies each corresponding token.
Timer and byte-read adapters share this interface; `examples/async_mixed_wait.lim`
tests both sources becoming ready first and verifies that a fifth source is
rejected. Descriptor ownership and
executor shutdown remain open. Externally interrupting a blocking run also
remains open.

```lisp syntax
#generate #std/tasks.lim::threaded-executor {
  run = run;
  result = Result;
  jobs = ((number NumberTask NumberPoll NumberPending NumberReady number-poll #u64 number-input));
  thread = Worker;
}
```

This expands an executor plus
`#generate #thread-spawn ((task Worker) (worker run))`. Each job names both its result
field/state binding and a distinct worker-input parameter, for example
`(number NumberTask NumberPoll NumberPending NumberReady number-poll #u64 number-input)`.
The spawn call uses that worker-input name as its named argument; the result
field keeps the first name (`number` in this example).
Each explicit spawn transfers the fixed job set to one OS worker. Multiple
spawns can run concurrently; this is not task
migration or a worker pool. Structural Send/Sync, spawn failures, mandatory
joins, and captured-reference restrictions come from the existing thread
implementation. OS thread creation still uses its existing allocation path.

Runnable examples: `distributed_errors.lim`, `static_table.lim`,
`local_waker.lim`, `async_wake_pipeline.lim`, `async_registered_wake.lim`,
`wake_ready4.lim`, `timer_reactor1.lim`, `timer_pair.lim`,
`timer_reactor_many.lim`, `async_stdin_byte.lim`, `async_stdin_cancel.lim`,
`async_mixed_wait.lim`, `async_fn.lim`,
`async_fn_two_awaits.lim`,
`cooperative_tasks.lim`, `async_pipeline.lim`, `task_cancellation.lim`, and
`threaded_tasks.lim` in `examples/`.
# Suspending conditional returns

An async function may await inside an early-returning `#if` or `#match`
branch while its fall-through path also awaits. Only that fall-through path
runs the common tail. See `examples/async_conditional_return.lim`.
Pending tasks retain captured loans until consumed or explicitly cancelled;
linear inputs must be consumed on every return path. Branch-local bindings
do not become visible in the common tail.

`#while-let` may return from the enclosing async function after suspending
in its body. A matched pattern runs the body; a mismatch skips its awaits
and continues after the loop. Body helpers carry distinct continuation and
return outcomes, preserving reference origins and linear cleanup checks.
See `examples/async_while_let_return.lim` for two body awaits followed by
an explicit return. The example also exercises the nonmatching path.

The scrutinee's task expression may itself await another task. Dependencies
are evaluated in order on every pattern test, never hoisted out of the loop.
Generated body helpers obtain pattern payload types from the scrutinee's
declaration, and those names remain scoped to the successful arm. Shared
payload references stay borrowed through nested Pending frames; explicit
cancellation consumption releases them. See
`examples/async_while_let_dependencies.lim` for repeated factory calls,
two body awaits, and once-per-construction mutations (exit 40).

Those capture declarations also support tuple, array, and struct payload
patterns, aliases to structural types, and nesting. Struct pattern positions
follow field declaration order, even when construction uses reordered named
fields. The generated-source cache includes that declaration order.
Ready helpers use explicit tuple
destructuring to restore mutable outputs via ordinary binding assignments.
`examples/async_pattern_payloads.lim` demonstrates carrying one destructured
field across a suspension while awaiting another field's computation.
`examples/async_struct_patterns.lim` uses differently sized fields declared
in nonalphabetical order. Shared-reference fields retain their source loans
while suspended; mutating the referent before completion is rejected.

Ordinary `#let` and `#let-mut` destructuring can appear before or between
awaits too. Every nested leaf gets its type from the explicit binding type,
including aliased array elements and nested struct fields. Mutable patterns
keep their mutable slots across suspension, and linear fields still require
explicit consumption. `examples/async_destructure.lim` destructures a nested
tuple in a struct and awaits each element in turn (exit 42).
`examples/async_resume_destructure.lim` declares and updates nested mutable
locals after the first await, then suspends again (exit 45). Updates write
the existing slots; lowering must not turn them into shadowing declarations.

Inside an `#generate #async-fn` body, an awaited result may be destructured directly
in `#let` or `#let-mut` (types and protocol from the example below):

```lisp
(#let (Values (#tuple left right) bias) Values
  (#await Values InputTask InputPoll.InputPending InputPoll.InputReady input-poll (InputTask.InputStart values)))
```

Lowering evaluates the await once into an explicitly typed temporary, then
uses ordinary destructuring. Nested leaves can cross later awaits with the
same ownership and borrow rules as ordinary locals. For enum patterns use
`#let-else` with an explicit diverging failure path; a mismatch skips the
successful continuation and its awaits. Both await spellings are accepted
there, with or without a redundant result type before the child protocol.
See `examples/async_await_destructure.lim` (exit 42). Linear payloads still
require explicit consumption; a plain-data test payload must be marked
`#linear` to exercise this constraint.

Nested destructuring also works in the prefix of a suspending value `#block`
or a selected `#if` branch. Each leaf keeps its explicitly declared type and
mutability; branch-local names do not escape into the other branch. A block's
result type comes from its tail, not its first awaited value. Type names in
casts, aggregate constructors, layout queries, and assembly declarations
are not captured as local values. Reference leaves retain their loans while
Pending, and linear leaves require explicit consumption on every path.
`examples/async_pattern_blocks.lim` runs both the selected and skipped branch
and exits with 47. These extensions do not remove the remaining general
control-flow and pinned-frame restrictions.

A selected branch can explicitly consume a prefix-local linear owner before
its first await. The generated helper captures only values needed to construct
the child or run the continuation, not already-consumed owners. Unused linear
prefix values still require explicit consumption; using a consumed value in
the child or continuation remains an error. `examples/async_prefix_cleanup.lim`
calls a destruction function before awaiting and retains only its plain result
(exit 47). The prefix runs once, not again on each Pending poll.

An async `#for` initializer may use ordinary `#let`/`#let-mut` aggregate
patterns, including nested structs, tuples, arrays and declared aliases.
Each leaf gets its type and mutability from that declaration. Initialization
can itself await; the initializer runs once before the first condition, while
condition, body and step suspensions preserve the loop's local slots. The
initializer's names remain scoped to the loop, so an independent later binding
may reuse a name. `examples/async_for_patterns.lim` demonstrates a nested
mutable struct pattern and exits with 42. Reference leaves retain their source
loans while suspended; returning a reference transfers its loan rather than
ending it at Ready.

An explicit `#await` result annotation is a checked contract, not a hint that
lowering may discard. It must agree with an explicitly declared destination,
function result, condition or named parameter contract. The compiler checks
these source contracts before expanding the state machine, resolves aliases
for comparison, and underlines the specific offending `#await`. An unrelated
earlier await is not substituted as the diagnostic location. This check does
not infer local types or replace ordinary type, ownership and borrow checking
of the generated declarations.

An awaited block must preserve writes to its enclosing mutable bindings,
including writes made through a named function argument's mutable borrow.
Generated block helpers return changed captures alongside the logical result;
the parent restores those values before executing its continuation. A linear
capture belongs to the child while it is Pending, rather than being duplicated
in the parent's loop state, and still requires explicit consumption after it
is returned. `examples/async_block_loop.lim` demonstrates a block-owned labeled
loop with Pending/resume and independent bindings after the block's scope ends.
Its regression also checks enclosing scalar and linear aggregate mutations,
immediate completion, skipped loops, and protocol-only awaits whose local result
type is explicitly declared.
