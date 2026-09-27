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
(@error-enum ApplicationErrors ApplicationError)
```

Contributions can live in different imported files. The compiler first loads
the active cfg-selected import graph, then freezes collections, then runs
generators. Registration order and import traversal order do not determine
entry order: entries are sorted lexicographically by their explicit keys.
Repeated imports contribute once. Identical values under the same key are
deduplicated; conflicting values are errors. Unknown collections and duplicate
collection declarations are errors. Generators cannot add collections or
contributions after freezing.

A generator parameter `(values #syntax-collection)` explicitly requests a
snapshot. At invocation, a collection-name literal resolves to its frozen list.
A literal list can also be supplied, allowing generators to forward snapshots.
Ordinary parameters still receive their original literal syntax. Helpers
declared with `#gn-fn` receive values, not collection-name resolution.
Generator cache keys and invocation deduplication include the resolved list.
The existing broader cfg/import dependency context is also still included.

`#gn-length` takes one syntax list and produces an integer literal containing
its length. The user-defined generators in `library/collections.lim` use these
facilities to produce ordinary inspectable declarations in `.lim`:

- `(@error-enum collection Type)` emits a concrete enum with inline payloads.
  Allocation freedom also depends on the payload types. The largest variant
  determines payload storage, with tag and alignment overhead.
- `(@distributed-slice collection StaticName ElementType)` emits a homogeneous
  static array. Its length and contents are fixed before type checking. Use
  `#slice-of` to borrow the array; access requires `#unsafe` like other statics.

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
  ((first Count CountPoll CountPending CountReady count-poll u64)
   (second Count CountPoll CountPending CountReady count-poll u64)))
```

Each job descriptor is `(name Task Poll Pending Ready poll-function Result)`.
The generator emits a result struct with one field per job and a function
accepting one task per job. This is a statically sized, heterogeneous join:
capacity is the number of descriptors, with no dynamic spawn queue. Job lists
can also come from frozen syntax collections.

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

## Cancellation and threads

`(@task-cancel cancel-function Task ((State handler) ...))` generates an
exhaustive match consuming a task. Every state must have one payload; each
handler accepts that payload as `task`, consumes its owned resources, and
returns `()`. Cleanup occurs only when this function is explicitly called.
There is no automatic cancellation when a task goes out of scope. `#forget`
intentionally bypasses cleanup; it is not a cancellation operation.

A handler for an external operation must finish cancellation before releasing
any borrowed storage the operation can still access. The compiler checks
types, consumption, and borrows, not OS cancellation completion. There are no
new safe asynchronous OS-operation builtins in this implementation. An
executor's blocking run call cannot currently be externally interrupted.

`(@threaded-executor run Result jobs Worker)` expands an executor plus
`(@thread-spawn Worker run)`. Each explicit spawn transfers the fixed job set
to one OS worker. Multiple spawns can run concurrently; this is not task
migration or a worker pool. Structural Send/Sync, spawn failures, mandatory
joins, and captured-reference restrictions come from the existing thread
implementation. OS thread creation still uses its existing allocation path.

Runnable examples: `distributed_errors.lim`, `distributed_slice.lim`,
`cooperative_tasks.lim`, `async_pipeline.lim`, `task_cancellation.lim`, and
`threaded_tasks.lim` in `examples/`.
