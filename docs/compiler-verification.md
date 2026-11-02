# Compiler verification

This document describes the **current fragment compiler and its proved
boundaries**. The target is a complete compiler for all Solidity in the approved
profile, with kernel-checked source-to-executable-EVM correctness. The
[full compiler roadmap](coverage-plan.md) owns the VM groups and final proof
obligations. The fragment restrictions below are implementation/proof work to
remove, not additional user exclusions; this page does not claim that endpoint
has been reached.

`Solidity/Evm/` compiles a fragment of the scoped syntax (`Stmt C Γ Γ'`,
`Solidity/Syntax/Scoped.lean`) to an EVM-style stack machine and proves that
the compiled code does what the typed run (`Stmt.run`,
`Solidity/Semantics/Run.lean`) does. It is mini-solkey's
`Ch08_EVM`–`Ch10_Correctness` scaled up to the typed calculus: control flow,
reverts, checked arithmetic (signed too, and `**`), arrays (`push` and `pop`,
copies, aliases into elements), internal calls and `transfer`.
`docs/module-map.md` lists the modules.

`Evm.Compiler.compile` is the checked entry for the core fragment below and
the memory fragment for primitive arrays, primitive struct fields, and
finite nonrecursive struct default/literal construction with supported reference
members, and primitive-member copies from storage roots. It returns code together with a fragment
certificate; `Compiler.Compilation.correct` (`Main.compiler_checked`) proves
their common source/machine agreement. The selected path determines its
explicit input and output state relation; `inFragP` and `compile_correct`
describe the core path.

## Memory operations

`Compiler.compile` selects one compiler for the whole program, trying the core,
first memory, reference-array, full-object, construction, direct-loop, scoped-loop
and internal memory-call paths in order.
Each has its own input and output relation. The core path's output relation is
`Sim` only; using it as a prefix to memory compilation needs separate
preservation evidence. The finite struct defaults below use the first memory
path. Programs requiring both its struct-default representation and the later
reference-array or full-object representations remain refused.

**What the memory path accepts.** Dynamic arrays of primitive values and
structs whose members are primitive (or reference-valued, reserved as one
cell each), through typed pointer locals: element and field reads and
writes, lengths, array reads composed in indices and RHS values (`a[a[0]]`),
checked operators, short-circuit and conditional expressions over memory
operands, primitive storage writes, `require`/`revert`, blocks and
statement-level `if`. Sequential programs may also contain checked loops whose
conditions and bodies belong to this finite memory fragment (below). Allocation: `new T[](n)` with a simple length (the
elaborator captures effects first), a declaration without initializer (the
same as `new T[](0)`), default and literal construction of finite nonrecursive
structs with primitive members, nested structs and primitive dynamic arrays
(the elaborator lowers literals to default declarations and field writes), and
allocating rebinding. A primitive `new T[](n)` may also initialize a reference
field after allocating the child and then resolving its receiver. Older aliases keep their objects. `delete`
of an element, a field, a whole array local (a fresh empty array) or a whole
struct local (a fresh default object). Numeric `+=` `-=` `*=` `/=` `%=` and
standalone or captured `++`/`−−` on elements, fields and locals (the result
word stays on the stack during the checked bump, so `i = xs[i]++` and
`i = i++` are right). Nested paths through reference-valued fields
(`Evm/MemoryPaths.lean`) for reads, aliases and primitive writes;
reference-field assignment redirects a member to an existing child
(`Evm/MemoryRefWrite.lean`); deleting a reference member allocates a fresh
empty array or a supported finite default struct
(`Evm/MemoryRefDelete.lean`, `Evm/MemoryStructDefaultSource.lean`); copies
of a primitive-member struct from a storage root (`Record memory fresh =
stored;`, `Evm/MemoryStructCopyCode.lean`).

**The representation.** `Memory.StateRepr` extends the core simulation with
an identity-to-base map, disjoint bounded array intervals (length cell then
elements), separated headerless struct intervals (one word per member in
order, `StructHeapRepr`, `StructArraySeparated`), initialized pointer locals,
reference-member words (`RefFieldsRepr`) and a reserved frame limit
(`frameNeedProg`: the largest context anywhere in the program). Arrays and
structs lie above every reserved local cell. Reads and writes revert on the
same out-of-bounds accesses as the typed run. The machine stays
word-addressed: this is no bytecode or gas equivalence claim.

**The allocator.** A bump allocator with its cursor in cell zero and zeroed
free memory (`Evm/MemoryAlloc.lean`). The array-only allocator cannot be
reused once structs exist: a zero-valued struct can sit in the "unused" zero
tail (`legacy_write_breaks_allocator` is the counterexample), so
`StructAllocatorRepr` requires every live struct interval to end before the
cursor. `Memory.GrowingResult` threads the extended map through the program
(`BaseExtends`); `GrowsAllocator` records the exact cursor advance. A struct
reserves `max 1 memberCount` cells, so every reached allocation costs
something. **Capacity is a theorem premise** (`AllocationInput`: an inhabited
allocator, frame base `0 < b`, room for the cost the source run reaches,
`cursor + size + 1 < 2^256`); the generated code does no runtime capacity
check. The cost follows successful source prefixes only: an earlier revert
needs no capacity for an unreachable allocation, and without allocation the
premise is vacuous. solc can panic on an allocation size the typed run
permits, which is why this is evidence and not a check.

**Evaluation order.** Compound updates read their operands in a different
order on the two sides; each evaluator either returns or reverts, so no
other halt can be hidden by the reordering. Reference RHS values are
evaluated before the parent path; a deletion resolves its parent before
allocating.

**Dynamic reference-element arrays (nonallocating checkpoint).** The public
entry falls back to `Memory.ReferenceArrays.compileProg` when the older paths
refuse a program. `Compilation.isReferenceArray` identifies this path;
`isMemory` continues to identify the older allocating memory variant.
`RefArrayStateRepr` supplements the existing state relation with each dynamic
reference array's bounded header, actual child pointer words, frame separation,
separation from other reference arrays, primitive arrays and structs. Its
fallible pointer certificates admit initialized locals, reference fields and
indexed reference elements with core-fragment indices. The supported statements
are alias rebinding, reference-element assignment, and primitive dynamic-array
writes through these paths; sequences preserve the supplementary relation and
stack. Bounds failures on either a parent or child revert on both runs.
Redirecting a parent retains old child objects and aliases. This path allocates
nothing and makes no allocator-preservation claim.

`Evm/MemoryRefArrayExamples.lean` inhabits the public input with two populated
children and a two-element parent. Indexed rebinding changes an existing local,
parent redirection leaves its old alias intact, and old/new child writes yield
matching source/machine observations. Three bounds controls, a corrupt-pointer
refutation, and explicit allocation/default/fixed-index registration are checked by
the kernel. The new theorem and witness names are in the enforcing axiom audit.
Independent read-only finder and skeptic reviews found no soundness defect;
their requests for observable rebinding, refusal controls and enforced witness
auditing were incorporated.

**Complete object ownership and fixed-array checkpoint.** A further public
fallback, `Memory.Objects.compileProg` (`Compilation.isObject`), accepts
headerless fixed-array indexing as well as dynamic indexing. Its additive
`Objects.StateRepr` requires positive, pairwise disjoint reservations for every
actual typed heap object, typed primitive/child-pointer element words, pointer
locals, primitive struct fields and `RefFieldsRepr`. Existing compiler input
relations retain their earlier premises. Fixed bounds come from the source type;
a model bound at least `2^256` is handled without wrapping it into a zero word.
Indices remain core-fragment values. Primitive value reads compose with existing
checked operators; linear local assignments/declarations and alias declarations
are supported alongside indexed writes and rebinding. No loops or calls are
admitted by this path.

Successful object programs preserve a supplied **complete** allocator, whose live
intervals include reference arrays, fixed arrays, and even empty objects. The
public input/output helpers expose these assumptions without reducing a computed
compiler certificate. Both `Evm/MemoryObjectArrayExamples.lean` and
`Evm/MemoryFixedChildArrayExamples.lean` inhabit the state and allocator premises,
instantiate public allocator preservation, and check source/machine observations
for retained aliases, value reads, alias declarations and three bounds failures.
An overlapping cursor and a corrupt child pointer are rejected. The generic
adoption theorem preserves old typed child identities across heap growth.
`Objects.defaultEmpty_correct` additionally relates the actual source default
copy to empty-array allocation and complete allocator preservation. A populated
input instantiates it with source/machine observations `[40,32,24,0,9]` and
advances the cursor from 40 to 41. These helpers preceded the public construction
path described below.

`tests/memory-reference-arrays/ReferenceArrays.sol` and
`scripts/check-memory-reference-arrays.mjs` provide 92 independent solc 0.8.34 /
EVM executions across legacy/viaIR and optimizer off/on: retained-alias results
11013/17000/13, empty fixed-child arrays, distinct fixed defaults, and bounds
panic `0x32`. These are independent behavior observations; the separately
checked constructor paths are specified below. Reference-bearing struct
constructor setup remains upstream evidence only. The checked compiler's existing
coarse revert observation remains unchanged. Run the script with the published
soljson and an external node_modules directory containing the optional EVM test
dependencies; these are not Lean dependencies.

**Runtime-length reference-array construction checkpoint.** The additive public
`Memory.Construction.compileProg` fallback (`Compilation.isConstruction`) carries
full object state, reserved-frame and reached-capacity premises. It accepts
empty dynamic defaults, ordinary primitive-array allocation, and
`new T[][](n)` when the immediate child is a dynamic array (its element may be
any permitted map-free type). The length is a core-fragment `Simple`, including
a local runtime value. Literal `new T[](0)` also works at any permitted element
type, including fixed-array and struct references, since it invokes no child
constructor. Both declaration and allocating rebinding are checked. These
constructors compose with the full-object linear statements above; source loops,
blocks, branches and other statements remain outside this narrow fallback.

For `n` dynamic-array children, capacity is exactly `n + 1 + n`: one parent
header/element interval and one positive reservation for each distinct empty
child. The target reserves the parent first; the actual source copy appends
children first. `Gap`, the actual typed `childrenCopy` fold and final parent
adoption relate those orders without shared dummy pointers. A finite
`loopIterN` witness proves target termination in `n+1` condition turns, without
fuel or budget assumptions. Successful composition extends bases for old
identities, preserves retained aliases and all unrelated machine fields, and
threads the complete allocator with exact reached cost. A reverted prefix
omits unreachable allocation suffixes from its capacity premise.

`Evm/MemoryObjectConstructionExamples.lean` splices actual source syntax and
inhabits public inputs for empty defaults, local-length construction, primitive
children, alias mutation, and allocating rebinding. Source and actual target
runs yield 11013; the target observation follows from kernel simulation rather
than reducing the noncomputable loop through native execution. Actual default
children have distinct source identities and distinct represented pointers.
Separate public zero-length and fixed-child literal-zero inputs, source/machine
observations, three bounds failures, a `W-1` final-cursor boundary, rejection at
`cursor+cost=W`, and an inhabited reverting prefix before a uint256-max
allocation are checked. The last control consumes only five cells and reverts
before the oversized suffix.

`Evm/MemoryStructArrayInputExamples.lean` supplies a populated fixed parent of
`Holder { uint[] items; }` objects. Its public input includes genuine reference
fields; parent redirection and writes through retained/new field aliases yield
`[48,32,40,40,32,11,13,16,24]` on both runs. Bounds and corrupt-field controls
are checked. Nonempty arrays of reference-bearing structs remain refused by
this full-object/construction fallback: they require a separate child-constructor
API. Direct finite struct construction is supported by the first memory path;
this populated array-input path does not compose with that representation. The source/EVM fixture's constructor setup is independent
behavior evidence, not checked compiler constructor coverage.

**Nonrecursive reference defaults.** `Memory.ReferenceDefaults.compileDefault`
now recursively compiles finite fixed-array type structure, using empty dynamic
objects, headerless primitive fixed objects, and the existing primitive-member
struct default API as leaves. It refuses structs with reference members. The
certificate is indexed by the intrinsic `RefTy`, map-free proof and exact cost;
its result is the actual `Heap.allocDefault`, not a separate arithmetic model.
No intrinsic representation, SolKey rule or dependency boundary changes.

The public construction fallback accepts nonempty runtime arrays of certified
reference children and default declarations of certified fixed reference parents.
Allocating reference-array rebinding is also checked. Child cost `d(R)` is 1 for
an empty dynamic array, `max 1 n` for a primitive fixed child, the padded member
count for a primitive-member struct, and `max 1 n + n*d(R)` for a reference
fixed array. Runtime reference arrays cost exactly `n+1+n*d(R)`. Fixed parents
are headerless; zero-sized intrinsic fixed objects reserve one positive cell.
Each default child receives its actual separately allocated source identity.
Pending parent gaps survive recursively allocated children, old pointer bases
and positive lower memory cells survive growth, and the target loop has a
finite turn witness. Primitive struct fields can be written through indexed
reference paths while retaining the complete allocator and reference fields.

Six additive public fixtures cover `Box[]` defaults, `uint[1][2]`, nonempty
`uint[1][]`, `uint[1][2][2]`, fixed parents of default dynamic children, and
allocating rebinding. Inhabited complete state/allocator inputs yield actual
source and target observations 11013, 13 and 17000 as appropriate. Twelve
bounds cases check exact source/machine reverts. A further exact-capacity control
includes child cost and rejects `cursor+cost=W`. Historical default-struct
fixtures and counterexamples are retained unchanged. The old two fixed-default
refusal names are explicitly replaced by positive registration controls.

The assignment's independent reference-array layout and construction increment
is implemented. Default construction of reference-bearing struct elements
inside those arrays remains a dependency of the construction fallback: the
populated `Holder` input above proves its array/field path without claiming
that child-constructor support. Direct finite struct defaults use the first
memory path and do not extend this fallback. Source blocks, branches,
loops and unsupported expressions retain the existing narrow fragment refusal.
No universal source coverage or inventory promotion is claimed.

Validation uses the published Lean 4.24.0 / Lake 5.0.0-src+797c613,
`LEAN_NUM_THREADS=1`, explicit `-j1`, and verified 12 GiB/no-swap cgroups.
The first `./run-lean.sh` passed 691 library and 259 TestSuite jobs and the
377/131 SolKey comparison in 8032.865 seconds. Its whole validation group
peaked at 12 GiB (reclaim pressure, no OOM/kills). Executor reconnects released
its external writer-lock holder; no repository edits occurred during that
build. A protected repeat with the lock held inside the container passed the
official run in 5.492 seconds; its final full validation group took 97.152 seconds
and peaked at 3,199,209,472 bytes with zero limit/OOM events. These are observed
cache states, not a clean-build performance guarantee. The enforcing audit
passed 546 headlines; the new simulation/agreement axioms are exactly
`propext`, `Classical.choice`, `Quot.sound`. Source trust scanned 720 sources
and 240 inventoried sites with zero findings. Orphan, layer, strict automatic
and trust-script test gates passed. Documentation path checking still exits 1:
20 missing references in unchanged existing files were verified unresolved at
base `f4dee4a29c2e208b36db4a4161a4723c735cd775`; no new missing reference was
found. That gate is not reported as passed.

A single warm paired per-file check of the public compiler measured 0.999 s /
164,806,656 bytes before and 1.062 s / 164,990,976 bytes after. The indexed
pointer compiler retains structural recursion over the full endpoint type;
no speed-driven intrinsic representation decision was reversed. Full commands,
terminal logs, hashes, measured cgroups and review outcomes are exported with
the checkpoint handoff.

**Finite default layouts.** `Evm/MemoryStructDefaultLayout.lean` defines the
recursive cost: primitive children cost zero, empty primitive dynamic arrays
cost one header cell, and a struct costs its children plus
`max 1 memberCount`. Children are allocated in field order before their parent;
relative pointer stores initialize the parent with the actual child addresses.
`Evm/MemoryStructReferenceAlloc.lean` proves preservation of older objects, reference
words, separation and the zeroed free region. `Evm/MemoryStructDefaultPlan.lean`
connects every reached child allocation to the actual typed `Heap.allocDefault`
and its capacity premise. `Evm/MemoryStructDefaultCode.lean` keeps executable data
indexed by the original reference type and proves erasure, soundness and cost
equivalence to those certificates. Its structural traversal uses the existing
type rank, proved sufficient for the finite specification; no evaluator/search
budget is increased. Local/member deletion allocates fresh children as well as
a fresh parent, retaining objects reached through old aliases. Literal lowering
may leave replaced default children allocated; those costs remain included.

**Out of the first memory path**: reference-element arrays, fixed-array and
mapping memory layouts, recursive reference graphs, uncertified reference-member
default layouts, and copies other than the primitive-member storage-root clause
(including memory back to storage and runtime-length objects, which need
iteration), loops, `assert`, calls, payments and compound storage writes in a
mixed memory program. The later fallbacks accept their separately documented
array/object fragments; they do not compose those representations with this
path's finite struct construction.

## Ordinary internal calls with memory

After the published core, memory, reference-array, object and construction
backends refuse a program, the public checked entry also accepts direct nonrecursive internal calls whose
parameters are primitive values or supported memory-pointer paths, returning
nothing, one primitive (assigned or discarded), or a supported memory
reference. Calls may nest and occur inside blocks/branches. They may mutate a
shared argument, rebind their own pointer, allocate objects, and return either
an alias or an object allocated in the callee. Primitive-member storage-root
copies into memory parameters remain fresh copies; memory parameters and
memory returns retain identity.

`Evm/MemoryCalls.lean` reuses the intrinsic `Args.declsThen`, `CallRet` and
body-frame expansion used by `internalCallExpand`, including the existing
primitive code generators at the leaves. The original core call compiler is
still selected first when its whole-program fragment applies. A memory call
never uses core-only `Sim` as a memory prefix: every caller local stays in the
full `StateRepr` during the inlined body. Scope exit drops private locals;
a returned reference copies its pointer into the exported local cell, without
copying its object. `GrowingResult` retains stack restoration, the grown heap,
`BaseExtends`, and the exact allocator cursor advance through every frame.
The syntax-derived call height bounds structural expansion; it is not a
configurable search, recursion or execution budget.

The call certificate records `Compilation.requiredFrame`, the largest
expanded context, including caller locals plus all nested parameter/return
frames. `Compilation.allocationCost` counts only reached source prefixes in
the exact intrinsic expansion. Failed arguments reach neither return-default
allocation nor the body; an earlier revert requires no capacity for later
allocations. Default memory-return objects are still allocated by
`CallRet.enterT`, even when the body subsequently aliases another object.
Certificates carry a syntax-derived allocation flag and a proof that a
false flag means zero cost. `reachedCost_eq` proves the optimized cost is the
same reached-prefix formula: nonallocating suffixes and branches do not force
the source evaluator just to compute capacity. This preserves the existing
memory compiler's deliberate short-circuit (already in commit `3b03ac58`).
The existing `AllocationInput` policy, nonzero allocating frame base and
no-runtime-capacity-check policy are unchanged. Both frame and capacity
refusals have negative controls with inhabited positive inputs.

For compatibility `isMemory` remains the original memory-certificate
discriminator. `isMemoryCalls` identifies the expanded-call certificate;
`usesMemory` includes every published heap backend, each with its distinct
input/output relation. `memoryCalls_input` exposes its reserved-frame
and reached-cost premises without unfolding the compiler result.
`Compilation.correct` is the common kernel-checked source/machine agreement
for the call and published backend certificates, retaining the stronger memory output relation.

**Call refusal boundaries:** external/world/callback calls, recursive-call
contracts (`callRec`), payments, storage-alias parameters/returns, exported
primitive tuple returns (`CallRet.rets`), and memory returns whose default
allocation/layout is outside the existing fragment. Function-value
reference-argument elaboration is separate; these examples use direct names.
The bodies and argument conversions must themselves be in the memory
fragment. No source halt, allocation input, SolKey rule or printer changes.

`Evm/MemoryCallExamples.lean` checks inhabited public inputs and both actual
source and compiled observations: nested primitive/void calls, alias mutation,
parameter rebinding, new-object memory returns, nested reference forwarding,
primitive-member struct returns, implicit storage-to-memory argument copying,
true/false branches, callee and bounds reverts, failed return arguments,
zero-cost reverts without an allocator, and frame/capacity/refusal controls.
The renewed controls add a body-local array escaping by reference across later
frame reuse, a discarded primitive return, signed `int` and `bool` parameters
and returns through a memory-using branch, and an isolated private-frame
refusal. For the latter, all representation and capacity premises are inhabited
at frame `5`, which fits base `1` plus caller-only need `4`; the expanded
`requiredFrame` is exactly `12`, so the checked input needs frame at least `13`.
The stack starts with `77`; a reserved untouched cell holds `99`.
The callee's mutation and allocation are observed independently on both runs.
A 4,096-element cost regression also has an inhabited public input and both
source/machine observations. The identical bounded kernel cost benchmark
before/after short-circuiting passed at unchanged limits: 2.518/1.014 seconds,
1,112,559,616/873,324,544 bytes peak sampled group RSS. These are warm measured
checks, not cold-build bounds.
The transitive axioms of the public theorem, pointer-return theorem and
inhabited agreement examples are only `propext`, `Classical.choice`,
`Quot.sound`.

The matching `tests/solc/MemoryInternalCalls.sol` fixture is replayed by
`node scripts/check-memory-internal-calls.mjs SOLJSON MODULES_DIR [cancun|osaka]` against
SHA-pinned solc 0.8.34 (`c8649f8d…cfd11d8`) and optional external EthereumJS
packages, in legacy/viaIR and optimizer off/on modes: 60 executions on the
original Cancun default and 60 additional Osaka compatibility executions,
using identical expected vectors and unchanged gas limits.
The external `largeCost` vector is only call-execution smoke; its literal return
is not an independent allocator/capacity observation. The inhabited Lean
source/heap/cursor checks carry that cost evidence. These source reference
observations supplement the kernel theorem against this repository's typed
run and word-addressed machine; they are not universal solc or bytecode
refinement. Dependencies remain outside the core package.

**Validation and remaining blocker (2026-10-29).** The original gap was
reproduced against the exact recorded base compiler
`f4dee4a29c2e208b36db4a4161a4723c735cd775`: the same native direct-call source
is refused there and accepted here. The bounded default build passed all 687
jobs, including the old memory regressions and all new inhabited examples.
The refreshed default build passed in 41.362 seconds with
1,497,014,272 bytes peak sampled group RSS. The refreshed kernel trust audit
passed (529 headline theorems; 131.332 seconds). Its serialized final gate
group took 145.707 seconds with 1,495,232,512 bytes peak sampled group RSS.
Orphan, layer, strict automatic, trust lint, 26 affected script tests and all
60 Cancun plus 60 Osaka external EVM observations passed. The independent SolKey check matched 377 taclets and all 131
read-bearing annotations. The optional documentation-path check still fails
on 20 historical references in files unchanged from the recorded base.

The required full `./run-lean.sh` is **validation BLOCKED**, not passed: after
the successful default build its SolKey test-suite phase encountered runtime
allocation/thread failures. Synchronous elaboration repaired all affected
modules except unchanged `Solidity.TestSuite.Derived17`. Its final isolated
attempt, after allocator-purge and clean-page-cache headroom repairs, stopped
at the **12 GiB whole-VM current guard**, exit 75, after 87.017 seconds with
10,491,265,024 bytes peak group RSS. This is a resource stop, not a demonstrated
proof failure. Its transitive imports reach none of the task-changed modules.
The maximal proved compiler increment is retained; original-assignment
completion remains false pending this required validation. The shared
`memory-loops` lane owns the prerequisite performance repair; this lane must
consume only its validated merged result before rerunning `SolkeyTestSuite`
and the full script without changing claims or budgets. This dependency did
not stop independent own-scope work: the renewed audit and controls below
were completed while the repair was pending.

Every Lean/Lake operation used the checkout writer lock and the managed VM's
`bounded.py`: inherited 12 GiB per-process address-space ceiling, sampled
10 GiB workload RSS stop, 12 GiB whole-VM current stop, existing hard 16 GiB VM
cgroup, actual swap disabled. This is a measured guard, **not** a writable
12 GiB cgroup guarantee. `LEAN_NUM_THREADS=1` and `-j1` were explicit. Temporary
untracked Lake configs selected ordinary asynchronous elaboration for the
default build and synchronous elaboration for thread-sensitive test-suite
modules; neither changed proof budgets. Clean page-cache reclamation retained
all cache files on disk. Interrupted transport-supervisor attempts, failed
checks, exact configs and all resource results are retained in
`/workspace/solidity-compiler10-20261028-memory-internal-calls` with the handoff.

Independent read-only finder and skeptic reviews used no Lean process/server.
No soundness finding remains. Their confirmed fixes added successful void-call
coverage and an allocation-cost shortcut with a zero-cost proof and a native
thunk (generated C inspected), plus the inhabited 4,096-element regression.
The skeptic independently confirmed the final validation-blocked classification.

A second independent read-only audit found no implementation defect and three
concrete control gaps: caller-only versus private-frame reservation, discarded
primitive returns, and signed/Boolean calls. All three are now covered by
inhabited kernel proofs and corresponding real compiler/runtime controls;
both reviewers confirmed the findings addressed. The escaping-local/frame-reuse
control adds a fourth ownership observation without broadening the fragment.
No intrinsic representation, compiler policy, expected old observation, proof
budget or SolKey pin changed. The initial added Solidity fixture used reserved
identifier `alias`; its failing compiler log is retained, and the identifier
was corrected to `shared` without changing expected values.

Published-master compatibility was kernel-checked in a detached worktree at
`cc155f36dc163e221b1f8279c56fb2006113ee7d`, overlaying only the exact task
compiler modules and expanded controls: `Solidity.KeySort` plus
`Solidity.Evm.MemoryCallExamples`, 132 jobs, exit 0, 404.065 seconds,
1,826,172,928 bytes peak sampled group RSS. This is focused compatibility
against published dependencies, not a claim that the required combined full
script passed. The original task branch/base and existing commits were retained.


The call certificate retains its original primitive-array and primitive-member
struct layouts. Published aggregate/default-construction backends coexist but
are not coerced into this call relation; programs requiring their additional construction/access clauses are not
coerced into the call relation. The new-array prefix followed by a reference-array
call has an explicit refusal control. Existing opaque pointer-alias clauses
remain available where the original memory certificate already admits them. The
separate byte-addressed failure emitter is not connected to this word-machine
agreement and does not change its existing revert outcomes.

**Published-base reconciliation (2026-10-30).** The exported original task
checkpoint `6885b749846c536d925a89cdcbaf09163043b756` remains unchanged. An
isolated task branch at published base
`8445c3fc203144251b9d1fc9181f7f61a8189522` combines the cumulative task diff
with the already published aggregate paths. Dispatch preserves their order:
core, legacy memory, reference arrays, objects, construction, then calls.
Every published input, output and correctness branch is retained; no aggregate
relation is coerced into the call relation. `allocationCost` uses the published
construction cost for that certificate, with an exact three-word positive
control; `usesMemory` is classification only and includes all heap backends.

The reconciled compiler built 156 jobs, exit 0, in 56.868 seconds with
1,133,510,656 bytes peak group RSS. Call/aggregate witnesses and the published
failure observation, slice and unwind controls built 186 jobs, exit 0,
in 39.658 seconds with 1,489,522,688 bytes peak group RSS. The exact published
compiler was copied into a separate namespace for a before/after kernel probe:
it refuses the same ordinary memory call accepted here; actual source and
compiled observations also pass (exit 0, 1.911 seconds, 947,277,824 bytes peak).

The existing inhabited `require(false)` call still observes an empty source
revert and rejects a panic observation. A separate nonempty-payload internal
call has its exact intrinsic source bytes observed by the published failure
relation while the word compiler still refuses it. These are coexistence and
refusal controls, not byte/payload refinement for `Evm.Out.revert`. The current
common compiler and observation theorems print only the standard axioms.
An initial observation proof tried decidable equality on function-valued
states; its failed log is retained. The repaired helper recovers the exact
error from its halt projection without changing outcomes or adding axioms.

The changed default/root build was attempted once under the 300-second group
limit and stopped at 300.044 seconds, exit 75, peak group RSS 3,744,534,528
bytes. It is **not passed**. The last completed line was the checked frontend
certificate; the newest pending setup file was checked frontend `TypeExamples`.
This records build progress, not a claim of a false theorem or a per-proof
300-second failure. The required combined full build and its expanded trust
audit remain outstanding. The separately owned `Derived17` repair remains
unpublished and unavailable; no sibling branch was imported or unchanged
expensive failure retried. All current checks use the authorized measured
fallback and explicit `-j1`; neither resource nor proof/time budgets increased.

The additional published emission/composition/artifact and legacy memory
registrations passed 188 jobs (exit 0, 44.310 seconds, 1,392,836,608 bytes peak
RSS). The expanded `TrustAudit.lean` was attempted once as a distinct mandatory
check and also stopped during import building at the 300-second group limit
(exit 75, 300.059 seconds, peak RSS 2,166,366,208 bytes); it is not passed.
Orphan/layer/strict automatic/trust lint checks passed (914 sources, 241
inventoried sites, zero trust-lint findings), as did all 26 affected script
tests, the unchanged 60 Cancun and 60 Osaka observations, and the frozen
377-taclet/131-read-bearing SolKey comparison. The documentation-path checker
retains the same 20 historical missing references. Both read-only reviewers
confirmed no compiler/representation/halt regression and the module-map
omission they identified was corrected. These independent passes do not
replace either stopped broader gate.

**Pending-import performance investigation (2026-10-30).** Fresh fetch still
records published master `8445c3fc`; checkpoint `98103415` and the original
`6885b749` are preserved. The pending `Frontend.Checked.TypeExamples` has a
13-module source closure, all unchanged from that published base and containing
none of this task's files. Every one of its 12 saved imported artifact identities
exists and matches its producer trace. No completed target trace was identified;
anonymous cache entries alone cannot establish a valid prior exact-input build.
Library producers use `Elab.async=true`; the trust command's `false` applies to
its final file. Lake excludes these `weakLeanArgs` from the input key, so that
flag difference does not demonstrate cache invalidation. The expensive Taclet
rebuild also has published source/import changes.

One diagnostic checked the exact source and saved setup with profiling, explicit
`-j1`, the same resource guard and a 300-second ceiling. It requested no compiled
outputs and populated no reusable target cache. It finished in 81.084 seconds,
peak aggregate RSS 5,218,258,944 bytes, **exit 1**: theorem traces completed, but
profiler messages interfered with the two existing `#guard_msgs` expectations.
This is diagnostic evidence, not a passing validation. The earlier default and
trust logs list approximately 245.552 and 293.029 seconds of completed build-job
durations respectively. These rounded job durations are not a wall-time
decomposition; the evidence is consistent with cumulative published prerequisite
work, without proving the complete cause or predicting a successful full run.
No task-induced import/cache defect or single 300-second proof was demonstrated.

Both read-only reviewers confirmed those limits and no new implementation defect.
Neither unchanged gate was retried, nor were prerequisites prebuilt to evade its
cumulative budget. Both timeout obligations remain open. A retry requires a
concrete published performance repair affecting the measured prerequisite work,
legitimate exact-input cache evidence, or an authorized validation procedure that
accounts for cumulative prerequisite work. Frontend proof changes belong to the
G09 parser owner; this task must not take them over. Derived17 publication is an
additional independent condition for TestSuite/full-script validation. The
`perf1030-investigation.json` and failed diagnostic log retain source/setup/input
hashes, producer traces, effective options and reviewer conclusions. No semantic,
proof, resource, time or search budget changed.

**Published-base preservation check (2026-10-31).** Fresh published master is
`89ce50152255d6dc82ab733cecacb903b91e948e`. An isolated task branch reapplies
the reconciled changes; both older exported candidates remain preserved. All
177 repository sources in the memory-call controls' import closure are
byte-identical to the October 30 candidate and intersect none of the newly
published changes. Four additional imports belong to the Lean toolchain. The
initial naive regex count of 182 also included a token from prose; it is not
the source-module count. All published root registrations survive, with just
the two call modules added. No compiler, call proof, fixture or expected
observation changed, and unchanged proof/EVM controls were not rerun. This is
source-preservation evidence, not a new kernel validation of the broader base.

The restored same VM reconfirmed Lean 4.24.0 (`797c613`), Lake 5.0.0-src+797c613
and the actual KeySort build: exit 0, two jobs, 0.304 seconds, peak group RSS
48,553,984 bytes. Changed-base orphan, layer, strict automation and trust-lint
gates passed under the same guard (combined 10.666 seconds, peak RSS
305,029,120 bytes; 1,013 sources, 246 inventoried trust sites, zero findings).
The documentation-path gate fails with 48 missing references, exactly the
same byte-for-byte output and exit 1 as an unmodified published-base checkout.
This expanded published debt is distinct from the older 20-reference baseline;
it includes archived-log references and prospective inline-assembly paths.
The first baseline command accidentally ran in the candidate; its separate
failed log is retained, and the actual baseline was then checked correctly.

Both earlier 300-second default/trust timeouts remain open: this publication
provides no measured repair to their unchanged pending frontend/printer
prerequisites, while root/audit imports expand. No unchanged expensive gate
was retried and no prerequisites were prewarmed. The published Derived17 file
is still the migration checkpoint; the memory-loops repair is still unavailable.
The next required condition is a genuine published performance/cache/procedure
change accounting for cumulative gate work, plus publication of that independent
repair for TestSuite/full-script validation. Two independent read-only reviews
found no own-scope compatibility defect. Full original-assignment completion
remains false; exact source hashes and current/baseline checks are retained in
`compat1031-status.json` with the cumulative delivery.

### Checked memory loops and enclosing scopes

`Evm/MemoryLoop.lean` proves an unbounded simulation of `Stmt.loop`
using `Instr.loop`. The condition carries `ValFrag`; the body carries
the existing finite `ProgFrag`, and its output flags must restrict to
the entry flags. Every next turn therefore has the same checked fragment.
`Evm/MemoryLoopCompile.lean` composes those loops with finite statements.

The additive `Evm/MemoryLoopScope.lean` certificates compose these programs
under enclosing typed blocks and statement-level conditionals. The selected
branch alone contributes allocation demands and costs. Scope exit drops local
bindings while retaining the actual heap extension and address map; the join
weakens flags with the existing restrict/meet operations. Both branches must
compile, including an unselected branch. Loop bodies still use the original
finite certificate: a loop inside another loop's BODY remains refused.

`Compiler.compile` tries the core, finite-memory, reference-array, object and
construction paths first, then direct/sequential `memoryLoops`, then
`memoryLoopScopes`. Existing
discriminators retain their meaning; `isMemoryLoopScopes`,
`memoryLoopScopesResult` and `memoryLoopScopes_input` expose the new result
and its premises without normalizing a whole computed certificate.

The input is `StateRepr`, a bound covering every temporary frame in either
branch/body, and reached-prefix `Room`. `LoopPrefix` records actual successful
turns with their exact allocation cost. A reached true-condition turn requires
capacity for allocations before a later revert too. Program demands shift a
reachable suffix by the exact successful prefix cost; unreachable suffixes
contribute nothing. A zero-iteration loop needs no body capacity.
`room_nonallocating` is inhabited even for divergence. Scope helpers preserve
the selected branch's `Room`; an unselected allocating branch needs no capacity.
The result retains `StateRepr`, stack equality, `BaseExtends`, an exact
typed `Cost` witness on success, and `GrowsAllocator`.

`MemoryLoopScopeBudget.prefixBudget` is a sufficient, partial recognizer.
It can bound a finite allocating prefix before a syntactically nonallocating
suffix without evaluating that suffix. It returns `none` at a scope or loop
head it cannot bound; manual checked room lemmas handle allocating turns and
selected/unselected scopes. It is not a termination or universal allocation
oracle. Cost/demand views are kernel eliminators for the typed certificates.

Normal exit, revert and divergence remain distinct. Absent any finite normal or reverting outcome, the certified loop has
source `diverge` and machine `fault`; no iteration fuel or successful
termination premise is added. Continuously allocating divergence generally
cannot inhabit finite-word capacity. Source exhaustion is not reclassified:
The memory-loop certificates continue to refuse exhaustion-producing clauses
such as `assumeFalse`,
including in unselected branches, and `not_exhausted` follows from the full
simulation. Existing layout, copy, reference-array, reference-struct, call,
payment and assembly boundaries are unchanged. This is word-memory compiler
refinement, not raw bytecode/layout/gas refinement or universal source coverage.

`MemoryLoopScopeMeta` and `MemoryLoopScopeCompile` use generalized kernel
recursors with native indexed-match twins and universal kernel equality links.
The compiler's constructor equations share already checked results instead of
normalizing complete certificates twice. No proof, search, node or timing
limit was raised.

The original `MemoryLoopExamples`, `MemoryLoopAllocExamples` and
`MemoryLoopSourceExamples` controls are retained. The additive scope examples
check inhabited public simulation and actual source/compiled observations for
arrays, aliases and primitive structs in legacy and viaIR source orders;
zero iterations with a genuinely reverting body; selected revert; exact
exhaustion with refusal; unsupported nested loop bodies even when unselected;
one reached allocation; allocation before revert; a nontrivial enclosing
local drop (literal `7`, positive scope depth); full temporary-frame
reservation; and a last-word unselected allocating branch with an actual
`StateRepr` and public agreement. Selected divergence, an unreachable revert
suffix, and allocation before nonallocating divergence have kernel-checked
exact outcomes and inhabited room. Their infinite executions are not run by
native evaluation. The allocating divergent prefix is also refused without
its one required cell.

Bare source blocks can flatten during elaboration. Ordinary source regressions
use retained `if` nodes; typed regressions exercise actual `Stmt.block`.
`tests/solc/MemoryCompilerLoops.sol` retains the four original functions and
adds scoped variants. `scripts/memory-loop-evm.mjs` and
`scripts/memory-loop-scope-evm.mjs` actually execute calls through the pinned
EthereumJS adapter in all four legacy/viaIR × optimizer-off/on modes with
published solc 0.8.34. Both sets observe arrays `4`, records `3`,
allocateTurn `0`, and empty-data revert before return. Wrong-value,
wrong-halt and unchanged host instruction-budget refusals remain controls.
These sampled upstream executions complement kernel simulation; they are not
a solc/EVM refinement theorem. No feature inventory status is promoted.

Integration worktrees must install the optional EVM package from its existing
lockfile and populate both pinned compiler files in `.lake/soljson/` before
running these regressions; see [compiler setup](solidity-upstream-tests.md#reproduce).
Dependencies and compiler caches are local to each worktree. The memory-loop
runners use `MEMORY_LOOP_SOLC` for the 0.8.34 file; the replay tests discover
the 0.8.38 file in `.lake/soljson/` (or use `SOLC_REFERENCE`). With those
prerequisites present, run these checks sequentially under the resource scope:

```sh
npm ci --ignore-scripts --prefix scripts/evm-reference
node --test scripts/check-memory-loop-timing.test.mjs scripts/check-automatic.test.mjs scripts/evm-reference/replay.test.mjs
MEMORY_LOOP_SOLC="$PWD/.lake/soljson/soljson-v0.8.34+commit.80d5c536.js" node scripts/memory-loop-evm.mjs
MEMORY_LOOP_SOLC="$PWD/.lake/soljson/soljson-v0.8.34+commit.80d5c536.js" node scripts/memory-loop-scope-evm.mjs
```

The combined integration at `4d5f5d61a3ec252d5b1b5a25488f5c214a51bc2d`
passed its first 16 gates, then failed to load `@ethereumjs/util` in the
replay tests. Installing the unchanged dependency lock exposed a second absent
prerequisite, the pinned 0.8.38 compiler. After restoring both compiler caches
with their existing SHA-256 checks, the affected tests and both four-mode EVM
runners exited 0. This repaired checkout setup; no observations, proofs,
assertions or budgets changed. The full combined gate sequence still requires
a fresh controller run. Local repair receipts are retained in
`.lake/integration-repair/resources.json`, `gate-0.log` through `gate-2.log`,
and the two `memory-loop*-evm.json` reports. Read-only finder and skeptic
reviews used no Lean server and found no remaining setup defect or changed
semantic gate. Their request to make the focused evidence discoverable is
resolved by these paths; full combined validation remains pending.

Current validation, batch `solidity-compiler10-20261028`, original base
`f4dee4a29c2e208b36db4a4161a4723c735cd775`:

| Check | Actual result |
|---|---|
| Runtime | Lean 4.24.0, Lake 5.0.0-src+797c613; versions and KeySort build exited 0. |
| All eleven scope modules | Exit 0, 14.39 s in the dedicated multi-target build, including original imported controls. |
| Original/scoped four-mode EVM runners | Each exited 0 (1.54/1.52 s); 32 expected fixture-call observations in total, plus negative controls. |
| Affected script tests | All 22 passed, exit 0. |
| Orphans/layers/classification/complete TestSuite/trust | Each exited 0; 152 core modules, zero elaborator reach; 491 automatic + 61 budgeted, zero manual/pending; 552 derived + 11 refuted + 1 excluded; 753 sources / 250 trust sites / zero findings. |
| Fresh original Derived17 group | All 24 modules freshly checked, exit 0, 262.03 s whole guarded workload, peak group RSS 2,944,225,280 bytes. |
| Public/scope/capacity/divergence axioms | Only `propext`, `Classical.choice`, `Quot.sound`. |
| Documentation paths | Exit 1: the same 20 historical references, byte-identical to the recorded failing baseline. This gate is not passed. |
| Full repository | `./run-lean.sh` exited 0 in 377.01 s: 702 default-build jobs, 282 TestSuite jobs, and all 377 pinned taclets / 131 read-bearing annotations match. Separate final axiom audit exited 0 in 6.97 s. |

The preflight command receipt is `memory-loop-scope-preflight-56`: all
individual terminal codes are recorded, including the failing documentation
baseline; total 26.93 s, peak aggregate RSS 1,139,437,568 bytes.
The complete `memory-loop-scope-full-57` operation (runtime, full script,
axioms) exited 0 in 384.30 s, peak aggregate RSS 2,914,099,200 bytes and
kernel build-group memory peak 3,253,170,176 bytes. The fresh
timing receipt is `memory-loop-scope-derived17-fresh-36`.
The reproducible timing command is
`lake -f lakefile.memory-loops.toml env python3 scripts/check-memory-loop-timing.py --output <new-directory> --results <receipt.json>`,
under one outer 300-second guard. The validator rejects stale, partial,
cached, failed and over-budget group evidence.

These current heavy checks use a working Docker hard build-group scope:
actual `memory.max=12884901888` and `memory.swap.max=0`, independently
verified in each receipt, alongside the unchanged measured guard
(12 GiB per-process address space, 10 GiB sampled group-RSS stop, 12 GiB
current-memory stop, 100 ms samples). The parent VM has a hard 16 GiB cgroup
and disabled swap. Historical worker fallback runs had only that parent
limit plus sampled/per-process guards; they are not relabeled hard 12 GiB.
The writer lock stays held inside the container for the whole workload.
All runs set `LEAN_NUM_THREADS=1`, use explicit Lean `-j1` through an
archived untracked Lake config, keep caches on disk, and run no Lean server.

The before-scope bounded check of the old compile module/public entry/examples
and actual refusal took 8.78 s / peak 868,950,016 bytes. Dedicated new module
checks were approximately 1–2 s for certificate/metadata/soundness/room/budget/
compiler modules, 2–8 s for examples; these are bounded per-file/cache-state
measurements, not clean-build speed ratios. Nontrivial computed-certificate
comparison hit the unchanged 200,000-heartbeat limit. Sharing component
success equations with `Option.some_get` repaired it; automatic compilation
is proved to return the shared certificate, not merely sampled equal code.

Historical resource stops, address-space failures, interrupted runs, 300-second
timeouts and proof-heartbeat failures are retained in the cumulative evidence,
never counted as passes. In particular the earlier 1110.96/965.51-second replay
groups and fresh-31 timeout failed the original timing gate. The standalone
shared repair is commit `082efb3183e66af30d7324a0291a9b45458460d1`, independently
reviewed and exported against published `040e59d30a6726fa4f9fee831695eeaa4027ede1`;
its complete fresh group passed in 288.65 s. The original worktree's separate
fresh 262.03-second pass above includes the same original nine remaining
proofs, 1024-step walk, 903 visits, refusal controls and unchanged bounds.
Since the VA2 merge (2026-11-02) the walk has 987 visits; its fresh group
passed in 275.67 s (`docs/loops.md`).

Independent read-only finder/skeptic reviews used no Lean server. They found
no semantic defect and identified missing nontrivial outer-drop and scoped
divergence controls, which were added and checked. Final source reviews found no outstanding defect after those controls and
wording corrections. The cumulative handoff records the final gate and artifact
verification decisions. Full logs, hashes, exact commits, receipts,
failed attempts and review outcomes accompany the cumulative handoff.

## What is proved

For a program `P : Prog C Γ Γ'` of the fragment (`inFragP F P = some F'`), a
machine `m` representing the typed state `σ` with its frame at base `b` and
every dynamic array below `L` elements (`Sim C L b F σ m`, `L ≤ 2^64`), and room for its pushes:

```lean
theorem compile_correct {P : Solidity.Prog C Γ Γ'} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ m) (hL : L + Prog.pushes P ≤ Lmax) :
    (∃ o m', Solidity.Prog.run σ P = .ok o ∧ run (compileProg b P) m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Sim C (L + Prog.pushes P) b F' o.st m') ∨
    ((Solidity.Prog.run σ P = .error .revert ∨
        (Prog.asserts P = true ∧ Solidity.Prog.run σ P = .error .panic)) ∧
      run (compileProg b P) m = .revert) ∨
    (Prog.pays P = true ∧ run (compileProg b P) m = .revert ∧ ∃ o m',
      Solidity.Prog.run σ P = .ok o ∧
      Sim C (L + Prog.pushes P) b F' o.st m') ∨
    (Solidity.Prog.run σ P = .error .diverge ∧ (run (compileProg b P) m = .fault ∨
      (Prog.pays P = true ∧ run (compileProg b P) m = .revert)))
```

Both succeed, the machine's stack as it was and its storage, locals and
balances representing the run's final state; or both halt, the run by a
revert or a panic (a failed `assert`), the machine by a revert, as solc's
`Panic(0x01)` is one; or the program pays (`Prog.pays`) and the machine
alone reverts. No proof reaches that third case: the typed run checks the
contract's funds and the recipient's `sendKey` response (`TRun.transfer`,
`State.canPay`), and `Sim.funds` and `Sim.oracle` make the machine's `CALL`
agree with it, so `transfer_sim` gives agreement on both success and refusal
and `StmtOut.refused` is only propagated from an inner `refused`, never originated. The third case, and the
refused-payment alternative of the fourth, are a stale weakening of the
statement ([G04 R32](feature-work/roadmap-g04-restrictions.md#27-payments),
owned by G43). What the machine does when it succeeds, the run did
(`compile_box`), and a program that pays no one agrees exactly
(`compile_exact`).  The fourth case is a loop no number of turns ends:
the typed run diverges, and the machine has no outcome (`loopRun`'s fault),
or, as stated, a refused payment before the loop. The typed run has no stuck outcome, so no `not_stuck` is
needed, and `inFragP` says only what the compiler covers.

**The ledger is the money that moved.** KeY's `net` is a ghost of the
interpreter: the machine has no ledger, only every account's balance `bal`
(the Yellow Paper's `σ[a].b`), the balances `bal₀` when the transaction
began (a ghost no instruction touches), and the contract's address `self`.
`Sim` ties them: `net(a) = bal₀ a - bal a` at every word `a` but the
contract's own address (what `a`'s account lost), and the contract's own
entry is `0` (`Sim.netSelf`): it is never moved. A payment of `v` to `a`
books `net(a) - v` unless `a` is the contract itself, which books nothing
(`State.pay`, solkey's `\if(sadr = self) \then(net)`), since nothing moves.
So a wrong booking (a `+` for a `-`, the wrong address, a debit the machine
does not make) breaks the proof, where the ledger the machine used to carry
beside the interpreter's would have matched it whatever it was; and so does
dropping the `if`: a payment to the contract itself would then move its own
entry, which `Sim.netSelf` pins. Read off a run that succeeds:

```lean
theorem compile_net {P : Solidity.Prog C Γ Γ'} {m' : Machine} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ m) (hL : L + Prog.pushes P ≤ Lmax)
    (hrun : run (compileProg b P) m = .ok m' 0) :
    ∃ o, Solidity.Prog.run σ P = .ok o ∧
      (∀ a : Fin W, a ≠ m'.self → netAt o.st.net a.1 = (m'.bal₀ a : Int) - m'.bal a) ∧
      netAt o.st.net m'.self = 0
```

`Evm/Examples.lean` runs `owner = 5; owner.transfer(30);` on a contract
holding `100` (`payOwner_run`: `70` left, `30` in `5`'s account), and
`Evm/Interpreter.lean` reads the run's `net(5) = -30` and `net(this) = 0` off
it (`payOwner_interpreter`).

From a fresh contract (`Sim.init`, every slot `0`, `L = 1`, balances agreeing on the contract's funds, at
any address `self < 2^256`, which `address(this)` reads and `ADDRESS`
pushes):

```lean
theorem compile_storage {P : Solidity.Prog C [] Γ'} (hP : inFragP (Frag.init []) P = some F')
    (hL : Prog.pushes P < Lmax) (balance : Nat) (hb : balance < W) (bal : Fin W → Nat)
    (self : Fin W) (hbalance : balance = bal self) :
    (∃ o m', Solidity.Prog.run (freshT C balance hb self) P = .ok o ∧
        run (compileProg 0 P) (Machine.init bal self) = .ok m' 0 ∧
      ∀ (r : SRef C (.prim .uint)) s (v : PrimTy.uint.Denote),
        PathSlot C false r s →
        o.st.storage.findLive r = some (.prim v) → m'.store s = v.1.toNat) ∨
    ((Solidity.Prog.run (freshT C balance hb self) P = .error .revert ∨
        (Prog.asserts P = true ∧
          Solidity.Prog.run (freshT C balance hb self) P = .error .panic)) ∧
      run (compileProg 0 P) (Machine.init bal self) = .revert) ∨
    (Prog.pays P = true ∧ run (compileProg 0 P) (Machine.init bal self) = .revert ∧
      ∃ o, Solidity.Prog.run (freshT C balance hb self) P = .ok o) ∨
    (Solidity.Prog.run (freshT C balance hb self) P = .error .diverge ∧
      (run (compileProg 0 P) (Machine.init bal self) = .fault ∨ (Prog.pays P = true ∧
        run (compileProg 0 P) (Machine.init bal self) = .revert)))
```

every `uint` path the typed storage holds, the machine holds at its slot.
None uses more than `propext`, `Classical.choice` and `Quot.sound`; no
`sorry`, no `native_decide`.

**The bound.** solc's `push` reverts when an array already holds `2^64`
elements (`Panic(0x41)`); the run's arrays are bounded only by `2^256`. The
two agree while no array reaches the limit, and that is the hypothesis: `Sim`
carries a bound `L ≤ 2^64` on every dynamic array's length (`ReprAt.array`),
each `push` raises it by one, and a loop of the fragment pushes nothing
(`inFrag`), so a program raises it by
at most `Prog.pushes P`, its number of `push` statements outside loops. From a fresh contract
the hypothesis is `Prog.pushes P < 2^64`, which `decide` discharges for any
program one can write. The compiled `push` emits solc's check all the same;
under the hypothesis it never fires.

## The machine

Instruction meanings follow the EVM as [EVMYulLean](https://github.com/NethermindEth/EVMYulLean)
formalises it: arithmetic on words below `2^256` wraps, `DIV`/`MOD` by `0` give
`0`, comparisons push `1`/`0`, `SLT`/`SGT`/`SDIV`/`SMOD` read words as two's
complement (`SDIV` truncates, `-2^255 / -1` wraps, `SMOD` takes the dividend's
sign), `JUMPI` jumps on non-zero, `REVERT` aborts, `CALL` with a value the
contract cannot cover, or the recipient refuses, pushes `0`, and one to the
contract itself moves nothing. Deliberately simplified (`Evm/Machine.lean`
says why):

- **slots are terms** — `root o`, `hash k s o` (`keccak256(k ‖ s) + o`),
  `data s o` (`keccak256(s) + o`) — so keccak never collides, solc's assumption
  made structural; an offset added to a slot does not wrap. This is global
  injectivity, which the [user decisions](solidity-scope.md#user-decisions-2026-10-29)
  forbid in the final theorem: there, only a per-run collision premise over
  the preimages a run hashes, extended to hashed regions of length at most
  L (second round), is approved (G04 R34, owned by G27.05/G46.05);
- **relative forward jumps** (`exec` carries the instructions still to skip,
  so it is structural; a source loop is one structured instruction,
  `LOOP cond body` (`Instr.loop`, `loopRun`), and the loop solc emits inside
  `**`, `checked_exp_helper`'s, is unrolled: it runs at most 255 times);
- **locals in memory cells** addressed by their level in the context (`cell`,
  `lvl`; solc keeps them on the stack); `KECCAK256` takes its inputs from the stack;
- **the world is the accounts' balances** (`bal`, `self`); a recipient's code
  is not run, and whether it accepts a payment is `accepts`, which no
  instruction changes and the theorem quantifies over (a fixed, history-free
  oracle; the user decisions require any outcome, depending on history, for
  untyped recipients, and actual execution for typed ones: G04 R33, G43/G47); `CALL` takes an
  address and a value only, and an address is a word, not cut to 160 bits;
- no gas, no stack limit.

## The layout, and why it is injective

solc's: state variables in declaration order, a struct's members consecutive,
`uint`/`int`/`bool`/dynamic arrays/mappings one slot, an array's length at its
slot and element `i` at `keccak(slot) + i·size(E)`, entry `k` at
`keccak(k ‖ slot)`. A fixed-size array `T[n]` is laid out inline, as a struct
of `n` members: `size (T[n]) = n · size T` (`size_fixed`), element `i` at
`slot + i·size(T)`, no length slot (`Occ.felem`, `ReprAt.fixed`); its bound is
the constant `n` (`fixedCheck`), and the element's slot is an `ADD`
(`fixedSlot`). An `int` is stored as its two's complement word.
`Occ T s x` says slot `x` belongs to a value of type `T` laid out at `s`.
Two members, two mapping entries, two array elements, and an array's length and
its elements occupy disjoint slots: every slot `Occ T s` names descends from
`s` plus an offset below `size T` (`occ_desc`), a slot has one ancestor per
`keccak` depth (`Desc.unique`), and the rest is prefix sums (`offsetIn_disjoint`).
`save_repr` is where it is used: writing one subtree leaves every other
represented. `OccAt.kind_unique` is the same argument once more: the slot of a
primitive is never an array's length slot, whichever state variables the two
paths start from (`len_prim_disjoint`).

## The fragment, and what is out

In (`inFrag`): `uint`, `int` and `bool` values; storage of any shape (structs,
dynamic and fixed-size arrays, mappings keyed by `uint`, nested); literals (a
`uint` below `2^256`, an `int` in `[-2^255, 2^255)`), locals, storage reads,
every operator (`**` at `uint`, `-x` at `int`), `?:`, short-circuit
`&&`/`||`, `.length` of a storage array (a fixed one is folded to its literal
by the elaborator); `=` of a value into storage, a copy of a *static* value
(no dynamic array and no mapping in it: `bob = alice;`, `triple2 = triple;`,
`persons[0] = alice;`), `=` to a local, `uint x = e;`, `T storage p = …;`
through members, keys and indices, `op=`, `x++;`/`total++;`, `v = x++;` and
`v = ++x;`, `push()` of a primitive element, `push(e)`, `push(sp)` of a static
element, `delete` at any type, `pop()`, `transfer`, `if`, `require`,
`assert`, `revert();`, `msg.sender`, `msg.value`, `block.timestamp`,
`address(this)`, a loop (`while`, `for`, `do … while`, lowered to
`Stmt.loop`) whose body pushes, pays (`transfer`) and shrinks (`pop`,
`delete`) nothing and leaves the fragment's flags as it found them, and a
call of an internal function, compiled inlined
(its arguments stored in its parameters' cells, its return variable zeroed,
its body, the result copied: `argsCode`), when its parameters, return variable
and body are in.

Every guard solc emits is emitted: checked `+`/`-`/`*` (the unsigned `*` check
is solc's `a == 0 || (a·b)/a == b`, `mul_ok_iff`; the signed ones are
`checked_add_t_int256` and its siblings, the `*` one dividing the wrapped
product back with `SDIV`, `smul_ok`), `/` and `%` by zero, `-2^255 / -1`,
`-(-2^255)`, `**` on overflow (`checked_exp_unsigned`), array bounds, `pop` on
an empty array, `push` at `2^64` elements, a refused `transfer`.

An alias bound through an array index (`Person storage p = persons[i];`) is
*fragile* (a flag of `Frag Γ`): the run checks the index once, when `p` is
bound, as solc does, and a later `pop` or `delete` could leave `p` naming a
slot past the end, which it still reads and writes. The representation
relates live elements only, so the fragment forgets fragile aliases at every
`pop` and `delete` (`Frag.dropFragile`);
until then no array shrinks, the machine only ever raises a length slot
(`LenSlot`: a primitive write never lands on one, `len_prim_disjoint`), and the
alias's path stays in bounds (carried by `Sim.flags`).

Out, and why:

| Construct | Why |
| --- | --- |
| memory on the core path | The checked entry selects the memory path instead (above). |
| loops whose body pushes, pays or shrinks | A loop is one structured instruction, `LOOP cond body` (`Instr.loop`, `loopRun`: its turns, a fault where none ends it; an assembler writes the `JUMPDEST` and the `JUMP` back), simulated turn by turn (`loop_sim`, `TurnRel`, by induction on the turns). Its body may not push (the bound `L + Prog.pushes P ≤ 2^64` counts each push once), pay (`StmtOut` keeps the stale `refused` case of the third disjunct, which the turn relation `TurnRel` does not mirror), or shrink (the fragile aliases a turn forgets must be forgotten before every turn). |
| storage copies of a value holding a dynamic array (`basketA = basketB;`, `matrix = …`) | solc copies element by element and clears the old tail: a loop over a run-time length, which the compiler does not emit. Copies of static values (`staticF`) are in. |
| `push()` of a struct or an array element | solc does not clear the slot it grows into (a `pop` cleared it), and the interpreter revives the popped value there (`pushSlot`); the representation does not relate slots past the end (relating them would need `delete` and `pop` to clear them, which for a dynamic array is a loop). `push()` of a primitive (solc writes `0`) and `push(e)`/`push(sp)` (every slot written) are in. |
| a fragile alias used after a `pop` or `delete` | See above: it may name a slot past the end, which the representation does not relate. |
| `address(this).balance` | Transfers debit the typed balance and the machine account together; `Sim.funds` records their agreement. Direct compilation of the balance read remains outside the fragment. |
| mappings keyed by `bool`/`int` | `ReprAt` relates a mapping keyed by `uint` only (`ReprAt.map` claims its entries only when the key type is `uint`): a `bool` key, which the typed run hashes as `0`/`1`, and an `int` key's two's complement are not related yet. |

The run evaluates an `op=`'s right-hand side before its target; the
compiled code resolves the target first. The simulation lemmas are
dichotomies (a value or a revert; the typed run has no stuck outcome), so the two orders agree on
every outcome. A copy loads every word of the source before it resolves the
target and stores; solc interleaves the two member by member. The two agree
whenever source and target do not overlap; loading first is right even when
they do, so the proof needs no argument about it.

## Build cost

`lake build Solidity.Evm.Interpreter` builds the modules. `Evm/Examples.lean`
is the slowest (the `decide +kernel` runs, the unrolled `**` code under a
raised `maxRecDepth`); `Evm/Correct.lean`'s `stmt_sim` dispatches one lemma
per family, held to `maxHeartbeats 11000`.

The fixed-array increment checked its two inhabited public fixtures in 10.439 s /
361,484,288 bytes aggregate peak, generic array adoption in 1.727 s /
191,942,656 bytes, empty-default simulation in 2.172 s / 197,185,536 bytes,
and the 32 upstream fixture runs in 2.568 s / 258,355,200 bytes. All used the
same 12 GiB/no-swap bound with zero limit/OOM events. An initial optional npm
installation stalled and was stopped (exit -15, **blocked**, not a pass); adding
the documented proxy CA and explicit proxy routing completed the dependency
installation in 5.201 s. Independent finder/skeptic reviews requested root/audit
registration, fixed-child/read/alias witnesses and inhabited allocator
preservation; those requests were incorporated. Full milestone gate evidence
is exported separately from the immutable first-checkpoint logs.

The full fixed-array milestone run passed 704 library jobs, 259 TestSuite jobs
and the SolKey comparison in 129.035 s; its 598-headline axiom audit passed in
94.160 s. The complete validation group took 231.556 s and peaked at
2,976,473,088 bytes, with zero limit/OOM events. Orphan, layer, strict automatic,
source-trust (733 sources, 240 inventoried sites, zero findings) and trust-script
tests passed. The documentation-path output was byte-for-byte identical to the
20 historical missing-reference failures recorded above; that gate remains
failed. Adding the inhabited empty-default witness checked in 3.271 s /
343,101,440 bytes before final confirmation.

The construction increment's populated scalar/struct and boundary fixtures
checked in 9.479 s / 316,563,456 bytes; the literal-zero fixed-child public
fixture checked in 5.277 s / 304,128,000 bytes. The 52 upstream source cases
passed in 3.084 s / 275,841,024 bytes, all under the same 12 GiB/no-swap bound.
An initial child-loop proof hit the unchanged 200,000-heartbeat limit and is
recorded as blocked, not passed. Abstracting loop control from concrete evaluator
bodies repaired it: that module checked in 1.350 s / 182,513,664 bytes, and the
strengthened finite simulation in 1.757 s / 198,868,992 bytes. No budget was
raised. Finder and skeptic read-only reviews found no soundness defect; their
zero-length, capacity and unreachable-suffix requests were incorporated.

The complete construction milestone passed the official 715-library/259-TestSuite
build and SolKey comparison in 125.027 s, plus the enforcing 662-headline axiom
audit in 103.401 s. New loop/construction/public-observation theorems use exactly
`propext`, `Classical.choice`, `Quot.sound`; no axiom declaration was added.
Source trust scanned 744 sources and the unchanged 240 inventoried sites with
zero findings. Orphan, layer, strict automatic and trust-script tests passed.
The bounded group took 236.179 s / 2,190,204,928 bytes aggregate peak with no
limit/OOM events. Documentation-path checking still exits 1 with the identical
20 historical missing references; it is not reported as passed. Both independent
reviewers confirmed their findings closed after the public zero-length,
capacity, unreachable-suffix and populated reference-field fixtures were added.

The final nonrecursive-default increment passed `./run-lean.sh` (733 library
and 259 TestSuite jobs, 377/131 SolKey comparison) in 137.829 s. The enforcing
747-headline audit passed in 125.779 s; new default/array simulations and target
observations use exactly `propext`, `Classical.choice`, `Quot.sound`. Source
trust scanned 762 files and 240 inventoried sites with zero findings. Orphan,
layer, strict automatic and trust-script tests passed. The full validation
group took 271.391 s and peaked at 2,199,785,472 bytes under actual
`memory.max=12884901888`, `memory.swap.max=0`, with zero limit/OOM events.
The 92 source/EVM fixtures passed in 3.428 s / 299,343,872 bytes. Logs retain
all failed development attempts as failures; no timeout is counted as a pass.
The documentation-path gate still exits 1 for the same 20 historical missing
references, byte-for-byte identical to the previous checkpoint output.

Independent read-only finder and skeptic reviews used no Lean server. Both
caught an accidental overwrite of the historical struct-default example module;
it was restored exactly and the new fixture moved to an additive module. The
reviewed allocator/source proofs had no remaining soundness findings. Broad
simp cleanup, audit registration and two stale descriptions were corrected.
Full terminal logs, cgroup measurements, review outcomes, cumulative bundle and
SHA256 manifests are exported in the task handoff. No master merge or push was
performed. No source coverage inventory was regenerated or promoted.

### Reference-array integration audit conflict

The merge of `f93e1e981f0eeed1e51b132bea669f92d74955e9` into
`9b6d1c2990209edbe5220a08f30d04d472dfee03` retained both additive
`TrustAudit.lean` headline blocks. Read-only local finder checks against both
index parents found no missing imports, headline entries or axiom prints;
the combined list has 757 unique entries. A local skeptic comparison confirmed
that the standard-axiom whitelist, transitive collection and rejection logic
are identical to both parents. No proof or target predicate changed.
Independent agent review was unavailable because the service could not load
the session rollout. Per-file Lean MCP diagnostics remained partial after
three 30-second polls, with no diagnostics or failed dependencies returned;
this is pending validation, not a passing Lean audit. `git diff --check` passed.
The coordinator must complete the combined audit under its resource scope.


## Memory-storage-copy recovery checkpoint

The recovery base is `8445c3fc203144251b9d1fc9181f7f61a8189522`, branch
`codex/solidity-copy-recovery-20261030/memory-storage-copy`. The isolated
predecessor at `/workspace/memory-storage-copy-preserved` reproduces the exact
original HEAD and porcelain-v1 NUL-delimited index/worktree status. Recovery
archive SHA256 is `5d4432ab8541e9b1669a464c9e1d350921f769a8e996308614971843f51a6f9e`;
all five member size/hash pairs, four untracked files and 381 evidence files
were verified, with safe paths and no links. Original ready inputs and extracted
recovery members are read-only. Other owners' broad staging remains isolated.

Only this task's algorithms, proof/admission changes, controls and additive
root/trust/docs integration were reconciled onto the pinned base. The complete
source and artifact hash inventory is
`/workspace/memory-storage-copy-evidence/restored-source-sha256.json`. Historical
`/workspace/memorycopy-*` log references below map to preserved basenames under
`/workspace/memory-storage-copy-recovery/evidence`; they are not fresh passes.

Fresh runtime: Lean 4.24.0 (797c613), Lake 5.0.0-src+797c613;
`lake -f lakefile.memorycopy-recovery.toml build Solidity.KeySort` exited 0.
The task-only alternate config preserves all proof/search budgets and supplies
explicit Lean `-j1`, with `LEAN_NUM_THREADS=1`. A network-disabled local Docker
container enforces `memory.max=12884901888`, `memory.swap.max=0`; no new VM or
worker is created. The source-host systemd user bus is unavailable, and its
16 GiB cgroup alone is not claimed as the required build cap.

`lake -f lakefile.memorycopy-recovery.toml build
Solidity.Evm.MemoryStorageCopyExamples Solidity.Evm.MemoryFixedCopyExamples
Solidity.Evm.MemoryFixedMixedExamples Solidity.Evm.MemoryStorageLifecycleExamples`
exited 0 (165 jobs, 518 seconds). Peak cgroup memory: 1,153,257,472 bytes;
sampled aggregate RSS: 1,227,550,720 bytes (shared pages may be counted twice).
The headroom monitor observed no reserve stop. Full logs and monitor JSON live
under `/workspace/memory-storage-copy-evidence`. Lean MCP diagnostics are not
available; installed per-file Lean checks are used instead.

Independent read-only finder and skeptic verified recovery bytes/status and
selective task ownership, and found no copy-semantic defect. Both found four
TrustAudit imports appended after commands; they were moved into the import
header before the audit. Current assurance/module-map summaries were corrected.
Neither reviewer used Lean or a server. Fresh audit, per-file, full/import,
TestSuite/corpus/sort, strict/trust/layers/orphans, external modes and exact-base
doc-debt checks remain pending. This is a partial checkpoint, not completion.

### Recovery checkpoint terminal checks

The first full-run attempt was deliberately interrupted (exit 137, not OOM)
after 185.01 seconds to repair missing explicit `-j1` on executable and LeanTeX
sections of the task-only configuration. All library/executable sections now
include it; source and proof budgets are unchanged and caches were retained.
That interrupted attempt is not a pass.

The local recovery/source checkpoint is reviewable and kernel-proved. All
edited/new Evm Lean files have successful installed Lean diagnostics: the first
batch stopped only because `MemoryCompileExamples.olean` had not been produced;
building the five affected legacy examples repaired that dependency, and the
remaining three diagnostics passed (65.05 s, 2,204,811,264-byte cgroup peak).
The failed batch is retained. The five legacy targets passed in 77.36 s.

The independent reference test passed all four legacy/viaIR × optimizer modes,
with exact observations and deliberately wrong-observation rejection saved in
`/workspace/memory-storage-copy-evidence/external-observations.json` (5.54 s,
343,310,336-byte cgroup peak). The task-only transitive audit checks 90 theorem
heads; its printed main axioms are exactly `propext`, `Classical.choice`,
`Quot.sound` (14.33 s). This does not replace the pending combined TrustAudit.

Orphans (915 reachable, 0 orphaned), layers (169 core, 0 elaborator reach),
strict automation (491 automatic, 61 replay budgets, 0 manual, 0 pending),
source trust (930 sources, 0 findings), trust-script tests (2/2), and the
TestSuite inventory all pass. The inventory's first attempt used an activation
snapshot whose sibling pin file was absent; selecting the existing repository
snapshot repaired setup without changing its pin. The unchanged 274-file
snapshot verifies at `473da8944ca7329e6b76819863591407db26e7ec`.

Sort alignment passes: 377 taclets parsed, 131 read-bearing, 131 covered;
annotations match the pinned rules (4.29 s). Exact-base doc checks both fail
with the identical 72 missing/ambiguous findings; zero new or removed findings
(`docs-comparison.json`). These failing historical gates remain failures.

Finder and skeptic re-reviewed the import, documentation, immutable-input and
checkpoint-accuracy fixes and found no remaining confirmed local finding.
Full `./run-lean.sh`, direct full/import/combined audit, TestSuite kernel build
and corpus validation remain mandatory and pending. The entire assignment
remains incomplete.

### Reattached audit and terminal validation (2026-10-30)

Audit `98afd51b-d8c1-4814-bc44-01c887ff8bf5` reattached this same VM/thread;
no replacement, goal reset, push or merge was performed. Transport loss had
left the original `memorycopy-testsuite` container running after its Python
supervisor exited. The stale original live JSON and file log are retained.
The recovered supervisor verified the same container ID, `memory.max=12884901888`
and `memory.swap.max=0`, reacquired the writer lock and restored the 12 GiB
OS-reserve/RSS guard. A detached watchdog stops only that owned container if
its supervisor fails. Exact Docker command metadata and the supervision gap
are recorded separately; the orphaned attempt is never counted as a pass.

Supported Docker wait/status recovered its true exit 137, `OOMKilled=false`,
with a reserve stop during `Solidity.TestSuite.Derived17`. After recovery the
observed peak aggregate RSS was 5,745,340,416 bytes and minimum available RAM
12,842,168,320 bytes, below the required 12,884,901,888. Container timestamps
are 11:31:30.363944529Z to 12:04:04.773292456Z. Actual complete Docker output
retains passing Derived1–16 results; Derived17 did not finish. No second
checker was launched while the surviving build ran.

A distinct resource repair checked unchanged `Frontend.Checked.UnitExamples`
alone in a fresh Lake/cgroup, avoiding the previous full run's measured
461,766,656-byte retained Lake RSS. It still stopped at the reserve guard
(wrapper 75/container 137, no OOM), in 49.30 s: peak aggregate RSS
4,232,019,968 bytes; minimum available 12,860,588,032 bytes. This is not a
passing dependency or full gate. The already-tried asynchronous-checking
change was not presented as a new repair. No unchanged full/TestSuite retry,
source takeover, increased budget or relaxed resource limit followed.

All seven source gates were then run individually: frozen snapshot verification,
TestSuite inventory, orphans, layers, strict automation, static trust and the
two trust-script tests passed. Snapshot/rules/examples use the repository's
existing `tests/migration/solkey` paths and unchanged pin
`473da8944ca7329e6b76819863591407db26e7ec` (274 verified files). The original
static batch's missing `/workspace/.setup/solkey.pin.json` exit 1 remains failed.

Actual root/import diagnostics fail because the unfinished full build has no
`Solidity.Semantics.RecursiveStorage` artifact; combined `TrustAudit` diagnostics
fail on missing `Solidity.Examples.LexMetrics`. Neither audit is passed by the
separate task-only 90-headline standard-axiom check. An initial serialization
wrapper used an unmounted `/tmp` lock path and failed before Lean; its exit 66
logs and failed corpus inputs are retained. Moving only that lock to the mounted
evidence directory repaired setup, with new result labels and no source or
expectation edits.

`Solidity.Corpus.Basic` kernel-built successfully. The original corpus probe
and all four generated-table/module/scoreboard comparisons passed in 31.83 s
(898,801,664-byte sampled aggregate RSS). Spawned probe checkers were serialized
with explicit `-j1`; no proof or test budget changed. The mandatory full corpus
script/kernel target remains blocked by Derived17; probe agreement is not
corpus kernel completion. Full/import, combined trust and TestSuite/corpus
kernel validation remain unfulfilled. The entire assignment is **BLOCKED**,
not done. Current exact-base documentation debt remains 46 missing references
and 26 ambiguities, with zero new/removed findings; raw doc gates remain failed.

Read-only finder/skeptic reviews confirmed safe same-container recovery,
unchanged kernel trust under synchronous scheduling, and exact-base source
identity for UnitExamples (24 local dependencies), Derived17 and OpenLoops
(227 each). Identity is not a baseline pass or proof of no resource regression.
The final blocked-handoff review and checksum-bound artifact locations are
recorded in `/workspace/memory-storage-copy-HANDOFF.json`. Resume only after
a legitimate resource/dependency repair under the original constraints,
inspecting surviving processes and the writer lock first. The owning modules
are not silently repaired or excluded by this task.

## Independent prerequisite validation, audit caf9

Audit `caf9c155-32cf-4079-b009-e3fb757bbd97` continued in this same VM,
thread and task branch from `7f825a4b`. No source algorithm, claim, observation,
proof/search/test budget, pin or ownership boundary changed. The exact saved
alternate configuration supplied explicit `-j1` and synchronous scheduling;
every checker used the writer lock, one Lean worker, hard 12 GiB/no-swap cgroup
and unchanged 12 GiB OS-reserve guard. Read-only reviewers found a watchdog
startup exception gap; it was fixed before the independent queues ran.

`Solidity.Semantics.RecursiveStorage` passed 29 jobs in 12.89 s (peak aggregate
RSS 748,720,128 bytes); `Solidity.Examples.LexMetrics` passed 44 jobs in 4.05 s
(785,158,144 bytes). The actual import DAG identified 193 missing independent
targets outside the original UnitExamples/Derived17 failure cones. Serial
queues stopped and investigated every new failure, then continued only outside
its dependency cone. Together with the two initial prerequisites, **182 unique
kernel-build targets passed**, including remaining EVM regression controls,
source/import controls, independent corpus modules, Derived19 (74.69 s),
Derived20 (181.45 s), and Refuted (16.98 s). These are prerequisite passes,
not a reduced substitute for any mandatory full gate. Nine further targets
remain blocked by DecisionHashes. All other queued independent work finished.

New terminal failures are retained separately:

- `Solidity.Examples.DecisionHashes`: OS-reserve stop, wrapper 75/container
  137, no OOM, 299.14 s; peak aggregate RSS 4,996,681,728 bytes. Its 319-source
  closure matches the pinned base; identity is not a baseline pass.
- `Solidity.Examples.Tactics.AllLeftLater`: checker exit 1 in 10.50 s,
  line 37: `sol_close_nonlin: bounded search stopped; original goal retained`.
  Its 215-source closure matches base. No tactic or budget was changed.
- `Solidity.Examples.Tactics.OpenLoops`: reserve stop, 137/no OOM, 152.15 s,
  peak aggregate RSS 4,493,791,232 bytes; unchanged owner-source closure.
- `Solidity.TestSuite.Derived21`: reserve stop, 137/no OOM, 69.47 s,
  peak aggregate RSS 5,299,404,800 bytes; unchanged 229-source closure.

CallSummary first failed after kernel output while publishing Lake cache
artifact `17490822145939138609.olean`: exit 1, 57.16 s, ENOSPC. Its build-tree
artifact was not promoted into a passing target. The 32 GiB filesystem had zero
user-available bytes. A copy-on-write probe was unsupported; byte-preserving
zero-block sparsing kept all four file hashes but overlay copy-up consumed
space. Two normal Git commit attempts and attempted artifact-only root-container
export startup also failed ENOSPC; no root checker or root commit ran.

Investigation found Docker uses `vfs`: stopped scopes retain full filesystem
copies, not merely the tiny writable-diff sizes. For 129 scopes created only
by this continuation, exact terminal metadata and timestamped stdout/stderr
were exported, hashed and verified before removal. Every diff contained only
empty mountpoint directories; workspace/source/caches, all original containers,
base image and recovery inputs remained intact. At zero free space, reversible
compressed envelopes preserved exact prior record bytes inside allocated
evidence blocks; the prior DAG was restored byte for byte. This concrete repair
recovered 20,303,544,320 user-available bytes. CallSummary then genuinely returned
exit 0 using its already checked artifacts, and the remaining independent queue
resumed. The original ENOSPC failure and staged documentation draft are retained.
Disk exhaustion is historical, not the current blocker.

Installed runtime evidence and a nonproof probe verified mimalloc's run-local
`MIMALLOC_PURGE_DELAY=0` setting (10 ms to immediate purging). This distinct
execution-only repair was tried once on each memory blocker, without changing
checker/source budgets or trust. All five attempts still ended at the unchanged
OS-reserve guard, exit 137 and no OOM:

| Target | Seconds | Peak aggregate RSS bytes | Minimum available bytes |
| --- | ---: | ---: | ---: |
| UnitExamples | 24.23 | 3,855,794,176 | 12,863,696,896 |
| Derived17 | 69.64 | 5,297,598,464 | 12,867,358,720 |
| DecisionHashes | 140.74 | 5,965,639,680 | 12,882,427,904 |
| OpenLoops | 268.30 | 5,643,522,048 | 12,850,393,088 |
| Derived21 | 74.11 | 5,092,384,768 | 12,838,055,936 |

The actual root and combined TrustAudit directly import UnitExamples; their
remaining dependency cones also contain other failed controls. Corpus/TestSuite
need Derived17 and Derived21. Root, combined audit, full run and corpus/TestSuite
were not blindly replayed. Six current failed targets and nine dependent
unattempted targets are recorded in the final DAG/terminal ledger. Source
identity, 90-headline task axiom audit, sampled EVM agreement and partial
prerequisite passes do not establish the missing mandatory gates.

Live `git ls-remote` still reports the exact frozen base. Local `origin/master`
was a stale October-24 non-descendant ref and was neither adopted nor used as
publication evidence. No validated owner fix is available. Further dependency
source repair requires the existing owners or separate explicit authorization;
no semantic decision, exclusion, premise or budget was weakened. The temporary
configuration was removed only after byte comparison with its retained copy.
Documentation checking still exits 1 with the base's 46 missing references and
26 ambiguities, zero new/removed findings. This milestone remains **BLOCKED**.

Versioned cumulative exports and the machine-readable handoff use
`/workspace/memory-storage-copy-auditcaf9-*`; earlier checkpoint exports and
both original checksum manifests remain unchanged. Independent finder/skeptic
reviews approve blocked-handoff accuracy only, not all-gates completion. All
raw attempts, failed setup/commit observations, resource measurements and safe
scope-cleanup snapshots remain in the evidence directory.

## Preserved memory-storage-copy recovery history

The following ledger is preserved historical task evidence from original HEAD `0f1039dac4e032c4e2c4030ee0d35b38c8393f80` and its recovered WIP. Its passes and failures describe that predecessor, not validation of the recovery base. Current recovery evidence is recorded separately.

## Certified memory-to-storage copies (2026-10-28)

`MemoryStorageCopyLoop` proves the actual `Instr.loop` traversals for arbitrary
runtime lengths. `MemoryStorageCopyCode.memoryArrayCopy_run` proves their exact
store effect: copy `[0,newLength)`, clear `[newLength,oldLength)`, then replace
the length. `MemoryStorageCopyLaws` connects that effect to the actual
`MVal.copyMToSt` heap snapshot and `Storage.write` overlay, including destination
frames. `MemoryStorageCopySource.assignMemoryArray_correct` and
`MemoryStorageStructCopy.assignMemoryStruct_correct` give the typed statement
simulations used by the checked compiler. No equality between unrelated heaps
or sampled-equivalence premise replaces execution. Neither traversal uses
scratch memory, changes the caller stack, or moves the allocator cursor.

The existing storage representation has a strict length bound `L ≤ 2^64`.
`Compilation.memory_copy_input` exposes `copyBoundProg P σ ≤ L`, separately
from allocation capacity: every reached successful array copy needs
`sourceLength + 1 ≤ L`. Demand is zero after a reverting prefix or failed source
or destination resolution. This is an explicit representation premise; the code
does not emit a new runtime length check. `Compilation.memory_input` retains
the old premise shape for programs with no array copies. Its optional copy-free
proof is explicit in the existing parameterized failure fixtures. Output claims,
halt policies and the source semantics are unchanged. The demand traversals use
generalized `casesOn`, structural recursion and named equations (Gate G0).

The source/target regressions exercise growing, shrinking, empty and recycled
array destinations, primitive signed/Boolean payloads, independent memory
mutation after copying, struct roots/nested fields/mapping entries, destination
bounds reversion, invalid representation bounds, unreachable copies,
reference-element refusal and retained storage outside the copied region.
`tests/solc/MemoryStorageCopies.sol` is also executed by
`scripts/evm-reference/memory-storage-copy.test.mjs` with the unchanged SHA-pinned
0.8.34 compiler in legacy/viaIR × optimizer off/on. All four modes pass; an
intentionally wrong observation fails the adapter. Its exact `Panic(0x32)` check
is independent reference evidence; the typed compiler theorem claims ordinary
reversion, not bytecode/panic-payload equivalence. No source coverage inventory
status is promoted by these compiler refinements.

Read-only finder and skeptic reviews independently found an overly eager
failed-destination length demand and indexed matching in the initial demand
traversal. Both were fixed and re-reviewed; the length-3/L=1 failing-destination
input is inhabited. Neither reviewer used the Lean server. No blocking semantic finding
remained; mandatory global validation remains blocked as recorded below. All proof/search budgets are unchanged. Keeping loop evaluation opaque
to proof unification repaired an intermediate heartbeat timeout; the complete
array-code proof then built in 1.41 seconds at 0.73 GiB aggregate RSS.

Validation uses the installed measured VM guard: inherited per-process
`RLIMIT_AS=12 GiB`, sampled process-group RSS stop at 10 GiB (100 ms), and
whole-VM `memory.current` stop at 12 GiB, inside the existing hard 16 GiB VM
cgroup with actual swap disabled. This is not a 12 GiB cgroup guarantee or a
claim that `MemorySwapMax=0` was set. Final validation commands source the published activation,
then export `LEAN_NUM_THREADS=1`; the untracked task Lake configuration supplies
explicit Lean `-j1`. Logs and resource JSON are exported with the handoff.

| Check | Exit | Elapsed | Peak aggregate RSS | Guard stop |
|---|---:|---:|---:|---|
| KeySort runtime | 0 | 0.30 s | 0.045 GiB | none |
| Baseline compiler dependencies | 0 | 172.70 s | 3.075 GiB | none |
| Compiler after copy integration | 0 | 30.85 s | 1.124 GiB | none |
| New Lean source/target witnesses | 0 | 6.37 s | 0.932 GiB | none |
| Four-mode Solidity reference | 0 | 3.43 s | 0.342 GiB | none |
| First full run (repaired failures below) | 1 | 1931.55 s | 7.141 GiB | none |

The first full run failed on unchanged `Calculus.LinearDecision` and
`Calculus.TermSize` with thread-creation errors, and on legacy fixture input
proof plumbing after the public memory input gained its copy bound. The two
unchanged modules passed with a smaller temporary stack (65536) and
`MALLOC_ARENA_MAX=2`, under the same guard: 33.03 s, 1.278 GiB. Affected legacy
fixtures and new controls then built together in 68.10 s at 1.300 GiB. Their
programs, capacity premises and expected observations did not change. The final
finder caught three further direct input tuples and one overbroad post-rewrite
tuple edit; their repairs passed both the default build and direct per-file
kernel diagnostics.

Two tool-session terminations orphaned intermediate full runs; their task-owned
groups were stopped and are not passing evidence. Another confirmation was
explicitly interrupted for the reviewed fixture repair. Persistent `setsid`
guards and the writer lock were used thereafter. One full attempt stopped at
the 12 GiB whole-VM threshold (exit 75, 2695.41 s, 7.394 GiB peak workload RSS)
during unchanged `Examples/Tactics/OpenLoops.lean`. Reclaimable file cache was
released using per-file `POSIX_FADV_DONTNEED` advice: whole-VM current fell from
4.34 GiB to 0.15 GiB. Disk caches were retained, all limits/budgets stayed the
same, and the isolated target then passed.

The next full attempt passed all 692 default jobs, then unchanged
`TestSuite/Derived7.lean`, `TestSuite/Derived15.lean` and
`TestSuite/Derived17.lean` exited 134 with `std::bad_alloc`. Their 226-file local
import closure has zero changes against the recorded base. A temporary smaller
stack (65536) and `MALLOC_ARENA_MAX=1`, `MALLOC_MMAP_THRESHOLD_=131072`,
`MALLOC_TRIM_THRESHOLD_=131072` made Derived7 and Derived15 pass. Derived17
still failed. A process snapshot showed 44 Lean task threads despite `-j1`,
with the actual inherited 12 GiB address-space limit. A further temporary
32768 stack and `-DElab.async=false` serialized theorem elaboration and kernel
checking. Installed Lean sources and the independent finder confirm this is a
scheduling change, not a trust or search-limit change. It reached the whole-VM
stop; after a second non-destructive cache reclamation (4.11 GiB to 0.16 GiB),
it reached the 10 GiB aggregate-RSS stop instead. No TestSuite source changed.

**Completion decision: the copy implementation and its targeted validation are
proved; original mandatory validation is BLOCKED.** The final unchanged
Derived17/TestSuite attempt stopped at the required aggregate-RSS ceiling.
The full script is not called passed. The next step is an owner-reviewed
performance decomposition/profile of that existing TestSuite replay under the
same limits, rather than raising budgets or changing its claim. This assignment
does not take over corpus work. Default/core build, SolKey rule check, all 15
edited-file kernel diagnostics, explicit axioms and the trust audit passed
independently. Both final read-only reviewers found no new semantic blocker or
scope drift; the skeptic required precisely this blocked validation decision.
Neither reviewer used the Lean server.

| Terminal check/attempt | Exit | Elapsed | Peak aggregate RSS | Guard stop |
|---|---:|---:|---:|---|
| Default/core `lake build` | 0 | 0.61 s | 0.058 GiB | none |
| SolKey rule check | 0 | 0.61 s | 0.211 GiB | none |
| Direct per-file diagnostics (15 edited files) | 0 | 116.26 s | 2.634 GiB | none |
| `TrustAudit.lean` (554 headline theorems) | 0 | 89.37 s | 1.392 GiB | none |
| Explicit `#print axioms` for copy laws/witnesses | 0 | 2.22 s | 0.759 GiB | none |
| Unchanged open-loop target after cache-headroom repair | 0 | 503.53 s | 8.523 GiB | none |
| Full `./run-lean.sh`: default passed; TestSuite failed | 1 | 3023.99 s | 9.046 GiB | none |
| TestSuite: smaller stack/allocator; Derived7/15 passed,17 failed | 1 | 322.34 s | 9.578 GiB | none |
| TestSuite: 32 MiB stack and synchronous elaboration | 75 | 73.66 s | 8.539 GiB | 12GiB-whole-VM-current-guard |
| Same TestSuite after reclaiming file cache | 75 | 87.87 s | 10.011 GiB | 10GiB-aggregate-RSS-guard |

The explicit axiom report gives `[propext, Classical.choice, Quot.sound]` for
the loop, array representation/source correctness, struct source correctness
and inhabited public compiler witnesses; `primitiveStruct_copy_repr` uses
`[propext, Quot.sound]`. There are no added axioms. The four Solidity reference
modes and negative observation control passed as recorded above.

Orphan, import-layer, strict automatic, source trust, trust-script regression
and TestSuite inventory checks pass. The published environment omitted the
sibling snapshot pin; restoring the byte-identical existing tracked pin repaired
inventory validation without changing its revision. The documentation-path
check exits 1 on 20 historical references in unchanged `Solidity/Eqns.lean`,
`tests/upstream/group03-validation.json` and `tests/upstream/group10-validation.json`.
No tracked file was deleted and no new citation is among those failures. This
is retained documentation debt, not a passing gate. Full command logs, resource
JSON, independent reviews and hashes accompany the cumulative committed export.

Resumed prerequisite check (2026-10-29): a successful fresh fetch found
`origin/master` at `127c2ee59de16971e45b08a2def54f4e5fae8e2a`. The shared Derived17
performance repair is owned by `memory-loops`; it is not yet a validated merged
prerequisite at this head. The source blob is still
`e05598503e3aa2700d5e250c47f390da6dfc4743`, identical to this task's blocked
version, and its last source change remains `1f02521bc4be2275f3cc659e3a17ad047dad48bf`.
The only Derived17-named upstream history records the resource stop. No new
Lean retry was run against that unchanged failure. The existing successful
Lean/Lake/KeySort runtime evidence and all independent copy checks remain
preserved. Resume full acceptance after consuming the owner's validated repair
from `origin/master`; do not duplicate the shared repair, import an unmerged
branch, or mark the current full gate passed. The task is not integrated at
this upstream head and the worker has not pushed or merged master.


### Whole-assignment continuation (2026-10-29)

The first checkpoint omitted primitive fixed arrays. The resumed whole-scope
finder/skeptic audit identified that omission and missing meaningful padding and
mixed-family controls; these are now implemented and kernel checked. The earlier
tables are historical checkpoint evidence, not acceptance results for this head.

`MemoryFixedStorageCopy` adds `FixedArrayRepr`, `FixedHeapRepr` and the separate
`FixedStateRepr` refinement. A fixed source has exactly its typed `n` primitive
words at `base..base+n`, no header, a no-wrap extent, and lies above the reserved
frame. Existing `StateRepr` fields and all old memory-input equivalences stay
unchanged. No cross-layout ownership is assumed. Consequently the new route is
memory preserving: initialized local/reference-field source paths, supported
finite storage destinations, copies, guards, branches and scopes are admitted;
fixed allocation, heap mutation, unset sources, array-element reference paths,
reference-element layouts and recursive types remain refused. General memory
loops remain separately owned. This is a copy refinement over represented
inputs, not universal source-program coverage or bytecode refinement.

`MemoryFixedShapeCode` emits actual structured copying/cleanup loops for
same-size fixed copies, fixed-to-larger-fixed padding and fixed-to-dynamic
replacement. `MemoryFixedShapeLaws` and `MemoryFixedShapeSource` connect their
exact stores to `MVal.copyMToSt`, `FixedCopy.apply` and the actual storage overlay.
Fixed destinations clear every padding word and retain slots outside their
inline extent. Dynamic destinations clear the discarded old live tail and
replace the length last. Source pointers precede destination bounds checks;
failed destinations perform no copy and have zero length demand. Successful
fixed-to-dynamic copies require `n+1 <= L`, using the same strict representation
bound as dynamic sources. No emitted length check or weaker premise is invented.

`MemoryFixedMixedCopy` proves that the existing dynamic-array and primitive-struct
copy algorithms preserve the fixed refinement too. `MemoryFixedCompile` composes
all copy families with intrinsic statement/program certificates. Its `FixedResult`
derives successful source heap equality and target memory preservation from
actual executions; neither is an input shortcut. `Compilation.fixed_input`
exposes the additional representation and reached demand. `isMemory` retains
its old legacy-route meaning; `isFixedMemory` identifies the refinement and
`usesMemory` includes both routes. No old input theorem is weakened.

`MemoryStorageCopyExamples.RuntimeLength` runs one compiled program at input
lengths 0, 1 and 3, and a guard failure at 4, including root and mapping copies
and independent later memory mutation. `MemoryFixedCopyExamples` supplies
inhabited public fixed inputs, both branches, root/member/mapping endpoints,
shape conversions, successful-bound refusal, failed-destination demand zero at
L=1, and explicit mutation/reference-element refusals. Padding starts with an
old word 88, so observing zero detects missing cleanup. Dynamic cleanup starts
with a nonzero discarded tail. `MemoryFixedMixedExamples` initializes fixed,
dynamic and primitive-struct objects at 128, 160 and 192, proves the public
fixed-route input/agreement, and observes source `[31,47,2,91,92,77]` together
with the actual compiled copy values and retained memory cells.

The four-mode reference script really deploys and invokes compiled solc bytecode;
it is not compilation-only evidence. The final extended run executes dynamic,
runtime-length, fixed, padded and mixed cases in legacy/viaIR with optimizer
both off/on, with every earlier expected value retained. It also checks bounds
revert data and deliberately wrong replay observations. These executions
supplement the kernel simulations rather than replace them.

The skeptic found indexed matching on `FixedCopy` in the first shape admission
and demand helpers. Generalized `FixedCopy.casesOn` with destination-index motives
repaired it; the remaining kind tests inspect only ordinary types. Both final
read-only reviewers confirmed the nonzero-padding and inhabited mixed-input
repairs and found no remaining confirmed own-scope semantic/admission/control
issue. Neither reviewer ran Lean, a build or a server.

Published compatibility was integrated only into the existing feature branch,
from `cc155f36dc163e221b1f8279c56fb2006113ee7d`, preserving the original
`f4dee4a29c2e208b36db4a4161a4723c735cd775` base and task commits. A further
fresh fetch found `040e59d30a6726fa4f9fee831695eeaa4027ede1`: it changes no
EVM compiler/source semantics or Derived17 file relative to that compatibility
base, so no further compatibility edit is required. No sibling branch, push or
master merge was used. The shared Derived17 performance repair remains owned
by memory-loops. Its unchanged failed full validation was not rerun to fill time.

The original resource guard and all proof/search/test budgets remain unchanged.
One resumed core confirmation was deliberately interrupted after reviewers
required the mixed/padding controls (exit75, reason `interrupted`); its log is
retained and is not a pass. Twelve final edited-file kernel diagnostics all
exited0. The following initial trust-audit attempt failed because the newly
published `Calculus.MemoryWitness.olean` had not yet been built; it is retained
and requires a real prerequisite build before retry, not a false pass.

| Resumed check | Exit | Elapsed | Peak aggregate RSS |
|---|---:|---:|---:|
| Actual Lean/Lake/KeySort runtime | 0 | 0.30 s | 0.045 GiB |
| Published compatibility baseline (117 jobs) | 0 | 237.32 s | 1.096 GiB |
| Fixed payload/source simulation | 0 | 1.71 s | 0.741 GiB |
| Fixed shape loops | 0 | 1.51 s | 0.731 GiB |
| Fixed snapshot/padding laws | 0 | 1.42 s | 0.744 GiB |
| Fixed shape source and demand | 0 | 7.97 s | 0.865 GiB |
| Compiler shape/mixed admission | 0 | 4.13 s | 0.802 GiB |
| G0 repair and source witnesses | 0 | 42.22 s | 1.132 GiB |
| Inhabited mixed and nonzero-padding controls | 0 | 3.43 s | 0.845 GiB |
| Final actual four-mode execution | 0 | 5.44 s | 0.375 GiB |

Final core/trust/gate terminal evidence and the explicit completion decision are recorded below and in the cumulative handoff; a pending or failed gate is never a pass.


#### Terminal checkpoint before the published reference-array integration

Current copy implementation and kernel/source controls pass on compatibility
base `cc155f36`. Fixed copy and padding loop extents must be strictly below
`W = 2^256`; fixed payloads also have the explicit no-wrap/frame assumptions
above. These are represented-input compiler claims, not general fixed-array
allocation/mutation or universal source/bytecode coverage claims.

The first resumed full core attempt stopped at the whole-VM guard during the
unchanged OpenLoops fixture: exit75, 5258.26s, 8428961792-byte aggregate RSS.
It is not a pass. Under the writer lock, `fsync` and `POSIX_FADV_DONTNEED` on
5961 regular generated checkout build files retained every disk artifact and
reduced VM current from4305002496 to2293972992 bytes (zero errors). The same
OpenLoops target then passed under its unchanged600s limit, in577.94s with
9174196224-byte peak RSS. No source, proof/search/test limit or resource ceiling
changed. The recovered default build passed737 jobs, exit0 in2438.42s at
6900506624-byte peak RSS. Its temporary configuration preserves all published
library/executable declarations, including the unaffected optional solcases
runner; default targets are identical. One trailing-space cleanup changed no
terms or expected observations and was kernel rechecked by that full build.

Final diagnostics: twelve edited-file checks exited0; the final trust audit
exited0 in106.70s and checked616 headline theorems. Explicit copy, shape, mixed
and inhabited agreement axioms are only `propext`, `Classical.choice`,
`Quot.sound` (fixed/padded snapshot representation uses just `propext` and
`Quot.sound`). The final audit/axiom/static group exited0 in121.04s with
1816711168-byte peak RSS. Orphans752/0 disallowed, layers156/0 elaborator paths,
strict automatic491/61 budgeted/0 manual/0 pending, source trust767 sources and
241 inventoried sites/0 findings, trust-script regressions, TestSuite inventory
and frozen SolKey377/131 checks all pass. Documentation paths explicitly fail
exit1 with46 missing references, all in the five published files listed in the
handoff; none changed from the compatibility base. Ambiguous citations are also
retained. This is published documentation debt, not a passing path gate.

Fresh fetch now finds `109ba72ac8cf62f4aa4c13ae5590802244400bd0`, whose published
reference-array/object compiler routes change the common entry API. This
checkpoint preserves the proved copy work; integration and its required checks
continue on this same branch. It is not original-assignment completion.

The strict shared-blocker audit also corrects the older closure statement:
current compatibility closure is227 files,26 changed from original base; the
historical226-unchanged figure applies only to the earlier checkpoint.
Derived17 itself remains blob `e05598503e3aa2700d5e250c47f390da6dfc4743`, last
source commit `1f02521bc4be2275f3cc659e3a17ad047dad48bf`. Published recovery
`b7801b00` reports a successful full run, but its11022848000-byte RSS exceeds
this worker's10737418240-byte stop. It is not a validated repair under this
worker policy; its cache-reclamation mechanism was already tried here before
the actual10GiB group-RSS stop. No unchanged failed full replay is run merely
to wait, and memory-loops retains ownership of the needed performance repair.


Published reference-array compatibility integration is in progress on this same feature branch; checkpoint figures above retain their exact baseline.


### Published object ownership and copy lifecycle integration (2026-10-29)

The compatibility union consumes published `109ba72ac8cf62f4aa4c13ae5590802244400bd0`
without importing an unpublished sibling branch. It preserves core, legacy
memory, reference-array, owned-object and construction route priority and every
published discriminated input/output helper. The legacy memory route retains
its necessary reached-copy bound and copy-free helper. The existing read-only
`fixedMemory` route follows the published routes; the new `copyConstruction`
route follows it. Thus earlier initialized-object route observations are stable.

The new owning APIs make a complete fixed lifecycle available. The earlier
checkpoint's allocation/mutation refusal applies specifically to its weaker
read-only route; it is not a global limitation after this integration.
`MemoryStorageObjectCopy.Objects.StateRepr.fixedCopy` derives fixed payloads
from the actual typed full-object array words. `FixedResult.objects` uses
execution-derived unchanged source heap and target memory to restore complete
object ownership and preserve any supplied allocator (`HeapRepr.mem_eq`,
`AllocatorRepr.mem_eq`). Neither equality is assumed as an input. The complete
object relation is retained, not discarded after projecting the old relation.

`MemoryStorageConstructionCompile` composes published construction/mutation
certificates with the copy certificates. Its common `Objects.GrowingResult`
keeps exact source-computed construction cost, allocation capacity, base-map
extension, allocator growth and reached successful-copy bounds. Owner default,
allocation and mutation algorithms are reused unchanged. Public
`Compilation.copyConstruction_input` exposes all these premises; existing route
claims are unchanged. Source/machine run and storage representations remain the
same intrinsic, dependency-free definitions, with no new axioms or proof budgets.

Admission boundary: this new route composes construction and copying in a
top-level sequence. A block/branch containing both construction/mutation and
copies internally remains refused; existing read-only copy blocks/branches
remain supported. Reference-element storage copies, whole reference-bearing
struct copies, recursive-copy layouts and general memory-source loops are not
added. The former fixed-mutation refusal control now explicitly targets
`Fixed.compileProg`, preserving the weaker route's refusal while separately
proving the stronger public lifecycle admission. No earlier source/machine
expected value is changed.

`MemoryStorageLifecycleExamples` supplies an inhabited public owned allocator
input: fixed array default allocation and zero-copy, initialization31/47,
fixed/padded copies, dynamic3 copy followed by fixed2 replacement (discarded88
becomes shadow/tail0), independent source fixed mutation99, primitive struct
copy77 followed by source mutation88. Kernel source observation is
`[31,47,31,47,0,2,31,47,0,77,99,88]`; actual machine observation also checks
free cursor135, sentinel99 and caller stack77. Source allocation cost is7 and
copy demand4. Insufficient storage boundL=3 is refused; a failed destination
still has demand0 and inhabited L=1 input after actual fixed allocation.
The corresponding Solidity lifecycle executes in all four pinned legacy/viaIR
optimizer modes, returning `[31,47,0,2,31,47,77,99,88]`. The complete reference
run passes exit0 in6.55s at401051648-byte peak RSS, retaining all previous
expected values, bounds/revert data and deliberately wrong-observation control.

Finder and skeptic reviewed the ownership projection/restoration, actual-prefix
cost/bound composition and lifecycle inputs read-only, without Lean/server/builds.
Neither found a confirmed semantic bug; both required root/trust registration
and precise documentation of the sequential composition boundary. Those modules
and theorem heads are registered. The source-level kernel checks pass under the
unchanged guard; final integrated global checks and original completion remain
pending until their actual terminal evidence is recorded.
### Finite reference-struct validation (2026-10-28–29)

The memory-reference-structs task uses the published Lean 4.24.0 toolchain.
The runtime KeySort smoke passed (exit 0, 0.303 s, 48,545,792 bytes sampled
group RSS). The original typed nested declaration was refused by the public
compiler while its source run allocated four objects. The extension accepts
that same shape. No new axioms are introduced: printed headline correctness
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Concrete target computation initially exhausted the inherited address-space
limit (about 10.44 GB sampled RSS); extracting opaque proof lemmas alone did
not resolve it. Separating typed executable layout data from proof records
preserved the same observations and passed the examples in 7.45 s with
1,157,050,368 bytes sampled RSS, without raising proof budgets. All failed
attempts are retained as failures in the delivered logs.

The resource guard is `/workspace/.cloudvm-solidity-compiler10/bounded.py`: a
12 GiB inherited per-process address-space limit, 10 GiB sampled process-group
RSS stop and 12 GiB whole-VM memory-current stop, on an existing 16 GiB hard
VM cgroup with actual swap disabled. This is a measured guard, not a writable
12 GiB cgroup guarantee. Builds use `LEAN_NUM_THREADS=1` and `-j1` through a
temporary untracked Lake configuration, with `-DElab.async=false`. The initial
full-build attempt failed creating threads in unchanged `LinearDecision` and
`TermSize` modules: `-j1` alone still allowed asynchronous elaboration. Disabling
async elaboration passed both modules under the same guard in 38.55 s at
1,098,969,088 bytes sampled RSS; no proof/search budget changed.
An initial complete-default attempt stopped at the 12 GiB whole-VM guard
after 600 jobs (exit 75, 4,415.11 s, 7,695,233,024 bytes peak build-group RSS);
this is BLOCKED, not an OS OOM or a pass. Its last observed module was the
unchanged `Examples/Tactics/OpenLoops.lean`, whose repository import closure
contains no task-modified module. Read-only best-effort `POSIX_FADV_DONTNEED`
advice for build/toolchain files reduced measured VM usage from
4,897,751,040 to 2,623,434,752 bytes while keeping caches on disk. The same
OpenLoops target then passed in 512 s under unchanged limits. Targeted success
does not replace the full build; its subsequent terminal result is recorded
separately in the handoff.
Full commands, exit codes, timings,
peaks and hashes are delivered in
`/workspace/solidity-compiler10-memory-reference-structs/`.

Independent final read-only finder and skeptic reviews found no confirmed
semantic defect; neither used a Lean server or ran builds. Earlier requests
for inhabited viaIR observations, literal rebinding, empty children and
unreached-capacity controls were implemented. This compiler refinement does
not promote universal source coverage or change feature inventory status.

#### Final terminal results and remaining blocker

The implementation and its inhabited kernel simulations are complete for the
finite STRUCT composition over existing primitive-array/struct children.
Original-assignment completion remains **BLOCKED** because the mandatory
`./run-lean.sh` TestSuite stage was not completed under the fixed resource limits in the attempted configurations. No
statement, premise, expected observation, search/step budget or resource limit
was weakened to make that gate green.

| Check | Actual result |
| --- | --- |
| `lake -f lakefile.struct-default.toml build Solidity.Evm.MemoryStructReferenceDefaultBoundaries` | Exit 0; 121 jobs; 235.05 s; 1,373,937,664 bytes sampled build-group RSS. Includes all four new control modules. |
| Complete default `lake build` | Exit 0; 709 jobs, using checked disk caches (1.62 s; 1,591,160,832 bytes sampled group RSS). The previous bounded-search failure in unchanged `Examples/Tactics/AllLeftLater.lean` passed with default async elaboration, still `-j1`, in 7.66 s. |
| `./run-lean.sh` | Exit 75 at the 12 GiB whole-VM guard during TestSuite validation; not passed. Its supervisor-group peak is not the nested Lake build's peak. |
| Unchanged `TestSuite/Derived17.lean` controls | Async check: `std::bad_alloc`, Lean exit 134 / Lake exit 1. Serial smaller-arena/immediate-purge check: exit 75 at whole-VM guard, 88.99 s, 10,289,602,560 bytes sampled group RSS. Combined async/allocator check: `std::bad_alloc`, exit 1, 73.35 s, 8,472,776,704 bytes sampled group RSS. |
| SolKey conformance | Exit 0, independently checked after the blocked TestSuite stage. |
| Orphan, layer, strict automatic and trust gates | Each exit 0. |
| Relevant script suites | Utility/aggregate/runner/trust suites: 29 passed. Focused existing constructor/fresh-array tests: 2 passed, 144.26 s; original expectations retained, including their negative controls. |
| Relevant pinned source fixture | `memory_structs_nested.sol`: exit 0, one working fixture, zero broken/blocked, all required fixture pipelines. The compiler controls separately check inhabited legacy/viaIR observations. No generated-EVM, native gas or optimizer-equivalence claim is made. |
| Broad extra source suite | The additional `struct\|memory\|fresh arrays` selection hit its original 1,800 s guard: BLOCKED, not passed. Focused tests do not erase that record. |
| Extra upstream fixture | `memory_structs_nested_load.sol` remained blocked by the runner's unsupported `gas irOptimized: 110769` expectation. Its fixed-array/storage-copy shape is outside this compiler extension. |
| Global documentation paths | Exit 1: 46 pre-existing missing references. The canonical check on detached base `fd35566ee3138dd93d456191cc3447c021b1a87b` produced byte-identical output; no new missing reference is attributed to this task. No exclusions or old evidence files were edited. |

The allocator-only controls used installed mimalloc's verified
`MIMALLOC_ARENA_RESERVE=64MiB` and `MIMALLOC_PURGE_DELAY=0`, with the original
12 GiB per-process address-space limit and unchanged RSS/VM guards. Broader
read-only cache advice reduced measured VM usage from 3,393,245,184 to
270,503,936 bytes, keeping all files on disk; this still did not complete
`Derived17`. A first numeric-unit probe was corrected using explicit `MiB`
after inspecting actual verbose option output. All probe/failure logs remain
in the evidence archive.

The next concrete step is a separate performance repair of the existing
`Derived17` loop proofs under these same limits (for example, investigate
existing chunked replay while retaining statements and step/heartbeat budgets),
then rerun `./run-lean.sh`. That prover/TestSuite work is outside the assigned
memory-STRUCT construction area and was not taken over. The committed task
increment retains its complete child-first allocation proof, reached cost,
old aliases, separation, zero tail, public compiler observations and named
refusals. The handoff records this blocker rather than claiming full completion.


### Published-master struct compatibility: initial checkpoint (2026-10-30)

The preserved worker checkpoint is `2cfb116c64237cee48e954bd338f90d48467556a`.
An isolated worktree applies only its implementation to freshly fetched published
master `8445c3fc203144251b9d1fc9181f7f61a8189522`. The original checkout and
exports remain unchanged. No Lean implementation or theorem needed a compatibility
edit: the first memory compiler still selects these finite struct programs before
the published reference-array/object/construction fallbacks. Documentation conflicts
were resolved without removing those published descriptions; finder and skeptic
identified and reviewed the corrected path-specific refusal wording.

The resumed saved VM actually reports Lean 4.24.0 and Lake 5.0.0-src+797c613;
KeySort passed. The same fallback guard verifies the 16 GiB hard VM cgroup and
actual disabled swap, imposes 12 GiB per-process address space, and samples a
10 GiB group-RSS / 12 GiB whole-VM stop. This is not a 12 GiB workload cgroup.
All checks below ran serially under the writer lock, with `LEAN_NUM_THREADS=1`,
explicit Lean `-j1`, unchanged proof/search allowances and a 300-second whole-check
timeout. No competing Lean server or unpublished sibling branch was used.

| Current-base check | Exit | Elapsed seconds | Sampled group peak bytes |
|---|---:|---:|---:|
| Lean/Lake and KeySort | 0 | 0.512 | 48627712 |
| Four task control modules, 158 jobs | 0 | 82.703 | 1136996352 |
| Adjacent public compiler controls, 157 jobs | 0 | 24.266 | 1110126592 |
| Orphan gate | 0 | 0.227 | 41193472 |
| Layer gate, 169 core modules | 0 | 0.204 | 73011200 |
| Strict automatic gate | 0 | 0.102 | 86016 |
| Trust source gate | 0 | 4.529 | 257986560 |
| Pinned nested-struct fixture, legacy and viaIR | 0 | 60.204 | 235376640 |
| Default aggregate, timeout | 75 | 300.052 | 2021281792 |
| Frontend.Testing prerequisite, timeout | 75 | 300.053 | 1785544704 |
| Initial utility suites, 28/29 passed | 1 | 2.621 | 200822784 |
| Initial affected source tests, 0/2 passed | 1 | 1.511 | 108167168 |

The task controls retain their inhabited compiler inputs, actual source/compiled
observations, alias/capacity/failure cases and kernel simulation. Printed headline
axioms remain exactly `propext`, `Classical.choice`, `Quot.sound`. The adjacent
controls preserve primitive struct/fixed defaults and the published `Holder[]`
refusal. The upstream fixture retains vectors 1, 2, 3, 4 in both required modes;
it is source-interpreter diagnostic evidence, not generated-EVM equivalence.

The default aggregate stopped after its fixed 300 seconds, without a reported
Lean error or memory-guard stop; it did not reach TestSuite. The initial script
runs actually failed because `--no-build` found stale `SolcJson.Body`,
`RuleSyntax.Grammar` and `TermSize` prerequisites. A concrete repair built
`Frontend.Testing` with the explicit serial configuration, but that separate
build also timed out at its fixed 300 seconds. Conditional script reruns were
therefore skipped. Neither timeout nor initial script failure is a pass, a
semantic counterexample, or evidence of memory exhaustion. No unchanged retry
or budget increase followed. These current aggregate/prerequisite obligations
are additional to the historical Derived17 dependency; its source is identical
to the preserved checkpoint, and its reported unpublished repair was not used.

Documentation path checks on the combined tree and exact published base both
exit 1 with byte-identical output: 46 historical missing references, no new task
path failure. Independent read-only finder/skeptic reviews found no remaining
own-scope implementation defect; they require the full completion decision to
remain **BLOCKED** while the current aggregate and source-script prerequisites,
reruns and mandatory full TestSuite validation remain unresolved. Full logs,
resource JSONs, original cumulative checkpoint, current-base task patch/bundle
and checksums are exported under
`/workspace/solidity-compiler10-memory-reference-structs-8445-compat`.


#### Completed affected checks and remaining aggregate blockers

The initial API prerequisite failures above were resolved by checking its import
closure in dependency order: 203 selected targets passed, including cached
artifact confirmations; the final `Frontend.Testing` confirmation passed.
Selection used absent local `.olean` paths, which can still have valid artifacts
in Lake's disk cache. Lake itself checked freshness. No proof was weakened or
given another search allowance inside a declaration. The unchanged affected
source tests then passed 2/2, and the utility suites passed 29/29.

The Node runner detaches Lake into another process group. Its outer RSS values
therefore describe the supervisor group, not the detached Lean workload. The
compatibility wrapper was corrected to invoke the installed guard separately
for every Lake call, with the same shared monotonic whole-test deadline. Exact
source/utility/upstream checks were rerun successfully: six inner Lake groups
all exited 0. Their largest measured group RSS was 2,388,586,496 bytes. The
wrapper also refuses an expired deadline before spawning Lake; its negative
control exits 75 with `notStarted: true`, not a claimed runtime or proof pass.
Earlier supervisor-only records remain preserved and qualified in the handoff.

| Final affected check | Exit | Elapsed seconds | Measurement scope |
|---|---:|---:|---|
| API checked-cache confirmation | 0 | 0.202 | direct guarded group |
| Utility suites, 29/29 | 0 | 26.483 | supervisor group; separate inner Lake logs |
| Affected source tests, 2/2 | 0 | 160.811 | supervisor group; separate inner Lake logs |
| Pinned nested struct, legacy and viaIR | 0 | 5.241 | supervisor group; separate inner Lake logs |
| SolKey conformance | 0 | 0.606 | direct guarded group |

The published `Frontend.Checked.UnitExamples` initially stopped at the whole-VM
12 GiB guard (107.509 s, 8,350,715,904 group-RSS bytes). Measured read-only
file-cache advice reduced idle VM charge from 2,320,809,984 to 620,150,784 bytes,
retaining every disk artifact. The unchanged module then passed in 144.653 s,
with 8,871,657,472 peak group-RSS bytes. The retained 100 ms memory trace sampled
at most 11,898,302,464 VM-charge bytes and zero OOM events. This operational repair
changed neither its proof nor any guard threshold. It does not imply RSS and
whole-VM charge are interchangeable.

The full default aggregate nevertheless remained above its fixed cumulative
300-second window. Its imports were then checked separately in dependency
order, stopping at the first individual failure: 279 selected targets passed
before unchanged `Examples.Tactics.Recursion` timed out. A normal asynchronous
elaboration control retained `-j1` and all proof/resource/time limits and also
timed out. The import closure contains zero task-modified files.

The independent kernel `TrustAudit` excludes that recursion example and
Derived17, so it was investigated separately. After its initial cumulative
300-second timeout, 252 selected import targets passed before unchanged
`Examples.Decision` timed out. Its normal async control also timed out; its
321-module repository import closure likewise contains zero task-modified
files. The source trust script's passing result does not replace this unfinished
kernel audit.

| Unresolved individual check | Mode | Exit | Seconds | Peak group RSS bytes |
|---|---|---:|---:|---:|
| Recursion | serial | 75 | 300.092 | 2040156160 |
| Recursion | normal async | 75 | 300.021 | 2119651328 |
| Decision | serial | 75 | 300.092 | 2241052672 |
| Decision | normal async | 75 | 300.060 | 2241359872 |

These are observed timeout blockers under this worker's fixed limits, not
memory/OOM findings, semantic counterexamples or a claim that every possible
performance repair is impossible. No unrelated prover/theorem source was edited.
The original checkpoint's mandatory TestSuite/Derived17 blocker also remains;
its reported repair was still unpublished at the final fetch, which confirmed
master `8445c3fc203144251b9d1fc9181f7f61a8189522` at
2026-10-30T12:55:01Z. No unmerged sibling was imported.

Both independent read-only reviewers found no remaining own-scope construction,
alias, separation, capacity, failure-control or compatibility-code gap. The
original assignment's completion decision remains **BLOCKED** until the shared
root, kernel trust and mandatory full `./run-lean.sh` gates pass. Their next step
is a budget-preserving repair by the appropriate proof owners/coordinator,
followed by bounded gate confirmation. No worker push or merge of master occurred.
The cumulative original checkpoint and current-base task export, full failed and
passing logs, resource records, reviews and checksums are retained together in
`/workspace/solidity-compiler10-memory-reference-structs-8445-compat`.

### Historical review1 evidence (superseded)

These results describe the earlier review1 checkpoint in the same VM/branch.
The failures and incomplete decision are preserved as history; see the
[current validation](#checked-memory-loops-and-enclosing-scopes) for the
complete fresh 262.03-second pass and final full-repository confirmation.

At that checkpoint:

* `node scripts/memory-loop-evm.mjs --output <results.json>` executes actual
  EthereumJS deployment and calls in legacy/viaIR × optimizer-off/on modes.
  `arrays`, `records`, `allocateTurn` return 4, 3, 0; `allocationBeforeRevert`
  actually reverts with empty data. Corrected run exited 0 in 1.52 s,
  sampled aggregate peak 277,245,952 bytes. Wrong-value and wrong-halt controls fail.
  Separate instruction-limit controls stop deployment and a call as BLOCKED;
  these host refusals do not establish source `THalt.exhausted` behavior.
  Bytecode provenance hashes decoded bytes and checks deployed runtime code.
  These sampled upstream observations are separate from kernel simulation;
  they do not establish universal solc compiler refinement.
* The coordinator correction authorizes the measured fallback described above;
  its host-side record is not visible in this VM. The handoff preserves the
  supplied instruction as a labelled transcription. Subsequent local Docker
  checks additionally verify actual `memory.max=12884901888` and
  `memory.swap.max=0`, with the unchanged sampled guard nested inside.
  No earlier fallback run is relabelled as a hard-cgroup run.
* `check-memory-loop-timing.py` and `check-memory-loop-timing.mjs` enforce
  cumulative accounting for the entire original 24-module proof workload.
  The earlier per-stage timing claim was insufficient. Full fresh attempts
  then still stopped at 300 seconds; see `loops.md` and the archived review1 handoff for exact
  command/result records. No timeout, allocation failure or cached partial
  workload is a pass. The original assignment could not be marked complete at that checkpoint.

The review1 terminal checks reported Lean 4.24.0 / Lake 5.0.0-src+797c613,
`lake build Solidity.KeySort`, `./run-lean.sh`, and compiler/replay axiom
queries each exited 0 under the verified hard Docker scope. The warm full
script took 1.05 s; the complete runtime/build/axiom group took 9.29 s with
sampled aggregate peak 1,227,821,056 bytes. These are cached build/audit costs,
not a fresh proof timing pass. The retained-source fresh group stopped at
300.024 s, exit 75, sampled peak 1,591,115,776 bytes; only the helper and
Discover00–03 completed before Discover04 was interrupted. The cumulative
gate and timed automatic gate correctly exited 1 at that checkpoint. All 22 affected script tests,
trust (742 sources / 246 sites / zero findings), layers (152 core / zero
elaborator reach), orphans (728 reachable / zero orphaned) and complete
TestSuite audit passed. Documentation paths remain failed with the same
20 byte-identical baseline findings. Independent finder/skeptic final reviews
confirmed these distinctions and found no further defect; original completion
remained false at that checkpoint. Current validation supersedes that decision.
Full historical commands, resource peaks, failures, reviews and hashes are
preserved in the cumulative evidence.

### Memory-loop integration conflict resolution

The uncommitted merge of `5b3446c835a362dbd12e40314849f763136df17d` into
`443d1f614ebf92d5c553c014a07ee3553bb5058a` retains all seven checked compiler
branches. Existing reference-array, object and construction dispatch precedes
the new direct/scoped loop fallbacks. Each branch keeps its original input,
output and agreement proof; selector eliminations cover the combined datatype.
Both parents' documentation and trust entries are retained.

Per-file Lean MCP error diagnostics completed successfully for the compiler,
the direct/scoped source fixtures, direct/scoped allocation fixtures,
reference-array rebinding and object construction fixtures. Compiler warning
diagnostics are empty; its `Compilation.correct` audit reports only `propext`,
`Classical.choice`, `Quot.sound`, with no source warnings. Source trust
(1050 sources, 256 sites), layers (172 core modules), orphans (1035 reachable)
and whitespace checks pass. The repository documentation-path check exits 1
with 46 missing references, none in the five resolved files; it remains failed.
No combined full build or original fresh-proof timing gate was run here.

Independent read-only finder and skeptic reviews used no Lean server.
The finder requested the complete dispatch order in this document and the
module map, and clarification that the construction fallback refuses all
loops; both findings were corrected and rechecked. Neither review has an
outstanding finding. The coordinator retains responsibility for combined
validation and committing the merge.


### Published-master memory-call/loop conflict resolution (2026-10-31)

The pending merge of `91e94ab57305ca055127934fd9e68fe9ea5e6be3` into
`0256f578904247911482ae2f9b4703a7ee6bb270` retains all eight checked
compiler branches. Dispatch remains core, finite memory, reference arrays,
objects, construction, direct loops, scoped loops, then internal memory calls.
The call fallback retains its zero-push guard. Both parents' `Input`, `Rep`,
and correctness branches, and the common `Agrees` predicate, are unchanged.
The loop certificate eliminators now cover calls, and the call eliminator
covers loops. The combined `requiredFrame` reports each loop certificate's
need; loop capacity and allocation growth still use `Room` and `Cost`, rather
than the finite-path `allocationCost` metric. The module map retains both
families of entries.

Per-file Lean MCP diagnostics completed without errors for `Evm/Compiler.lean`,
`Evm/MemoryCallExamples.lean`, `Evm/MemoryLoopSourceExamples.lean`, and
`Evm/MemoryLoopScopeSourceExamples.lean`. The compiler's complete diagnostics
had no warnings; a temporary `#print axioms` reported only `propext`,
`Classical.choice`, and `Quot.sound` for `Compilation.correct`, then was removed.
Layer and orphan checks passed (172 core modules, zero elaborator reach;
1037 reachable modules, zero orphaned or disallowed). Focused module-map EVM
paths and whitespace checks passed. These focused checks do not replace the
coordinator's required combined full validation and timing gates.

Read-only finder and skeptic review passes used no Lean server. The finder
checked every public declaration from both parents and all mapped EVM paths.
The skeptic compared every original `Input`, `Rep`, and correctness arm and
`Agrees` against both parents, checked dispatch order and the zero-push guard,
and found no added `sorry` or axiom. The helper documentation now explicitly
states that the finite allocation metric does not replace loop `Cost`/`Room`.
No outstanding review finding or semantic decision remains. The coordinator
retains responsibility for combined validation and committing the merge.

## Published prerequisite integration, 2026-11-01

The memory-storage-copy worker resumed on its original VM/thread/branch after
publication of memory-loops source `5b3446c835a362dbd12e40314849f763136df17d`
through master `22073f4445e7cab7560812a5ef4e081bf8ff5e87`. The task integrates
published master `5f6a75b6038371a3917dbe08b660d5f2d1207c58`; all four task
commits through `3483fb2c` and all prior sealed artifacts remain preserved.

Read-only finder/skeptic review identified a genuine proof-interface conflict:
the task had broadened the published finite certificate with a copy-bound
premise, while published loop/call consumers require its original contract.
The integration restores `Evm/MemoryCompile.lean` byte-for-byte from publication
and puts copy-bearing certificates in additive `Evm/MemoryStorageCopyCompile.lean`.
They reuse the published value compiler/frame functions and retain the same
reached-copy bound, allocation relation and simulation. No published loop/call
`Room`, input, result, push guard or source semantics was strengthened or weakened.
The public dispatcher retains published priority before task copy fallbacks.
Actual runtime `new(n)`, primitive-struct production and lifecycle controls
remain proved; no missing primitive producer declaration was identified.

The warned certificate refactor measured 19.62 s / 1,001,938,944-byte aggregate
RSS before and 14.35 s / 1,000,390,656 bytes after in bounded warm-import
per-file checks. These are not clean-build speed ratios. A first moved-file
check failed on private frame-helper visibility; definitional block/branch
frame equations fixed it without changing any frame bound. Every failed
attempt remains in the new evidence directory.

The old temporary forced-synchronous profile also failed unchanged published
`Evm.Correct` at its 11,000-heartbeat limit. The exact published/default CLI
profile passed a fresh per-file check in 13.11 s with that same limit. Subsequent
checks use the original published profile plus explicit `-j1`, not a raised
proof budget. Both configuration snapshots and the failed receipt are retained.
No owner proof was modified. Hard build-group 12 GiB/no swap, one Lean thread,
the 12 GiB OS reserve, pins, fixtures, invariants and observations are unchanged.

Focused local results before the integration checkpoint:

| Gate | Actual terminal result |
| --- | --- |
| Runtime/KeySort | Lean 4.24.0; Lake 5.0.0-src+797c613; KeySort exit 0, 2 jobs. |
| Public dispatcher | Exit 0, 30.46 s, peak aggregate RSS 1,194,016,768 bytes. |
| Four original copy/control targets | Exit 0, 26.45 s, peak aggregate RSS 1,176,121,344 bytes. |
| Seven original source gates | All individually exit 0; pin unchanged; 491 automatic/61 budgeted/11 refuted/0 pending; 1105 sources, 258 trust sites, zero findings. |
| Published Derived17 build | Exit 0, 247.07 s, peak aggregate RSS 2,938,273,792 bytes. |
| Fresh original Derived17 workload | All 24 modules fresh, exit 0, 244.17 s under unchanged cumulative 300 s; validator passed; peak aggregate RSS 2,857,463,808 bytes, minimum available RAM 15,802,159,104 bytes. |
| Task axiom audit | 93 headlines, exit 0; only propext/Classical.choice/Quot.sound. |
| Four EVM modes | Exit 0; all 15 ordered calls per mode and wrong-observation controls unchanged. |

Dependency preparation for the timing gate took 925.58 s and is explicitly
outside the fresh 24-module workload, as required by its published runner.
Preparation is not substituted for the actual fresh timing receipt.
Independent read-only reviews found no remaining source/ownership regression;
this supports an integration checkpoint, **not assignment completion**. The
mandatory full/import, combined trust, complete TestSuite/corpus and final
handoff gates still require actual local terminal results. Published host
success is not counted as this VM's pass. New evidence is retained separately
in `/workspace/memory-storage-copy-published-20261101-evidence`.

Checkpoint documentation checking exits 1 on both published base and task tree:
48 missing references and 37 ambiguities, byte-identical findings, zero delta.
No historical/vendor debt was rewritten or relabeled passed.


### Local validation after publication (2026-11-01)

The five legacy memory example modules now match published `5f6a75b6` exactly.
Their task-added copy-bound adapters were obsolete after restoring the legacy
API; independent finder and skeptic reviews confirmed that restoring the
published witnesses changes no program, theorem statement, expected observation,
control or budget. The first repaired module passed in 5.07 s; the other four
passed in 72.34 s, peak aggregate RSS 2,665,639,936 bytes. Commit `832540456`
records this compatibility repair.

Independent prerequisites were checked serially after each new resource stop,
without dropping the failed target from the mandatory roster. The final import
DAG has 1,096 required modules across the six original roots. Eight failed
prerequisites block 27 modules; all remaining 1,069 modules are covered by
successful independent target builds, including both executable roots. The
source-elaboration prerequisites exposed by the final coverage audit also pass.
This dependency coverage is not a passing full build.

The allocator-only repair `MIMALLOC_PURGE_DELAY=0` allowed unchanged published
`Backend.Scalar.PowerBounds` to pass in 231.49 s, peak aggregate RSS
1,853,415,424 bytes. The full workflow then stopped at `Frontend.Checked.UnitExamples`.
Recognized demand-commit allocator options were subsequently measured on that
same prerequisite: exit 137, no OOM, OS-reserve stop after 50.79 s. Neither
allocator experiment changes source checking options, proof budgets or guards.
The failed full builds, interrupted target records and their terminal group
receipts remain failed and preserved.

The exact remaining resource failures are `Frontend.Checked.UnitExamples`,
`Examples.DecisionHashes`, `Examples.Tactics.OpenLoops`,
`Counterexamples.PreFixSortAnnotations`, `SortCheck.Faithfulness`,
`Examples.Tactics.RevertData`, `Source.Horizon` and `TestSuite.Derived21`.
Their source closures match publication; identity is not a passing baseline.
Root/import needs the first seven; combined TrustAudit needs UnitExamples,
DecisionHashes, OpenLoops and Horizon; complete TestSuite and corpus need
Derived21. Owner source algorithms and claims were not changed. These mandatory
checks remain blocked, so the assignment and persistent goal are not complete.

Both native executable targets and actual taclet-sort alignment pass: 377
taclets parsed, all 131 read-bearing annotations match the exact frozen rules.
The timing validator tests pass 3/3. Corpus source probing and all generated
verdict/module/root/scoreboard comparisons pass in 29.14 s; this does not replace
the blocked full corpus build. The 93-headline kernel axiom audit and four-mode
EVM observations above remain separate evidence, with unchanged inputs.

All logs and the exact dependency ledger are in
`/workspace/memory-storage-copy-published-20261101-evidence`. Old recovery inputs,
failed attempts and checksum-bound exports remain untouched. Terminal owned
container layers were reclaimed only after preserving status, configuration,
timestamped logs and mountpoint-only filesystem differences; source, caches,
base image and recovery bytes were retained.


### Published importer prerequisite checkpoint (2026-11-02)

Commit `b8160cd5e` consumes only published `9ff01fd7`, which defines the
source-declaration metadata table in chunks of 64 and appends them in order.
No additional owner source or newer backend work was imported. Independent
read-only finder and skeptic reviews found no source, compatibility or ownership
defect. This is a published recursion-depth repair; it did not clear the local
resource failures.

Runtime remains Lean 4.24.0 / Lake 5.0.0-src+797c613; KeySort exits 0. The edited
importer passes its per-file fallback check in 9.31 s (no Lean MCP available).
OpenLoops then exits 137 at the unchanged OS-reserve guard after 233.73 s,
peak aggregate RSS 5,771,780,096 bytes; Derived21 exits 137 at that guard after
110.28 s, peak 5,156,323,328 bytes. Neither is an OOM or a pass. All prior failed
receipts remain preserved.

All 70 planned independent regression targets affected by this importer change
pass, with exact target/log reconciliation: 1,987.60 s, peak aggregate RSS
4,004,704,256 bytes, no OOM or resource stop. These cover 115 affected eligible
modules. The other 954 eligible modules retain source-identical earlier evidence;
the combined coverage of 1,069 modules is not a successful full build. The same
eight failed prerequisites still block 27 modules. Full/root/import, combined
TrustAudit, complete compiled TestSuite and full corpus remain mandatory and
blocked; unchanged failed closures were not retried.

The eight source gates, both executable targets, frozen taclet-sort alignment,
timing-validator tests and corpus source/generated-output comparisons pass.
The fresh original 24-module Derived17 workload passes in 281.90 s under the
unchanged cumulative 300 s limit; its validator passes. The guarded outer run
is 282.31 s, peak aggregate RSS 2,305,978,368 bytes. Original group 12 GiB/no swap,
OS reserve 12 GiB, single-thread checking, profiles and proof/test budgets remain
unchanged. The prior 93-headline kernel audit and four-mode 15-call EVM evidence
retain unchanged task sources and inputs and remain separate evidence.

The dependency-owner performance-repair question remains unanswered. This
checkpoint does not authorize changes to other owners' proofs or sources.
New evidence is saved separately in
`/workspace/memory-storage-copy-import-chunks-20261102-evidence`; earlier source,
failed checks, capacity-failure records, caches and sealed artifacts are retained.
Work remains blocked; the persistent goal remains incomplete.


### H1 native validation and published parser certificates (2026-11-02)

The human authorized "Free disk + 4 GiB reserve": only the available-host
admission floor changes from 12 GiB to 4 GiB. The build-group cap remains
12 GiB, swap remains disabled, and checking remains serial with
`LEAN_NUM_THREADS=1` and explicit `-j1`. No proof, search, node, parser-fuel or
existing time budget is reset or raised. Owned exited containers were
snapshotted before reclamation; source, caches, every commit and the latest
sealed handoff were retained. Read-only page-cache reclamation hints preceded
admission after direct reclaim writes proved unavailable.

All eight original resource-failed targets now pass on unchanged source under
H1: PreFixSortAnnotations, DecisionHashes, OpenLoops, RevertData, UnitExamples,
Faithfulness, Horizon and Derived21. The serial group exits 0 in 1,872.87 s,
peak aggregate RSS 9,146,687,488 bytes, with no OOM or reserve stop. Horizon and
strategy source were not edited. These new results do not relabel any older
failure as passed.

The acceptance-only private UnitExamples experiment remains UNVALIDATED: its
old-reserve check stopped at 47.33 s. Its complete plain-source packet, original
and candidate sources, 21 identical public headers, 13 unchanged inputs,
24-module producer closure, failed receipts and budget/admission metadata are
sealed separately. Source-reviewed preservation commit `be2dd1e9f` was explicitly
reverted before adopting the published repair; it is not in the task branch.
The packet discloses the producer's older function-type canonicalization body
rather than claiming untested current-master compatibility.

Published `60dd172d` supplies 13 private acceptance certificates and 59 exact
kernel-checked constructor-list equalities, assembling aggregate equalities
before rewriting coverage lambdas. Its exact source hash is
`7ce56ab95b0085c2bfabaa726db4ad6f6f72064d6be4d90682877b725a60e832`.
The local private per-file check passes in 166.97 s, peak RSS 1,845,415,936 bytes;
this is separate from the coordinator's check. Public statements, definition
bodies, inputs, controls and propext-only pins remain unchanged. Commit
`b471d1785` consumes only this published source and its owning documentation.
No native value is used as an unchecked proof oracle.

Current-task native results after that consumption:

| Gate | Actual result |
| --- | --- |
| `./run-lean.sh` | Exit 0, 1,006.30 s, peak aggregate RSS 5,535,825,920 bytes; default/core 1,053 jobs, compiled TestSuite 285 jobs, frozen sort check 377 taclets/131 read-bearing/131 covered. |
| Explicit root import | Exit 0, 2.66 s. |
| Combined TrustAudit | Exit 0, 258.05 s. |
| Full corpus script | Exit 0, 91.00 s; unchanged pinned verdicts and generated outputs. |
| Task axiom audit | All 93 headlines pass; only propext, Classical.choice and Quot.sound. |
| Four-mode EVM observations | All four legacy/viaIR × optimizer modes pass 15 complete ordered calls each, exact return/revert bytes and wrong-observation controls. |
| Source gates | Pin, inventory, orphans, layers, strict automatic, static trust, trust-script tests and complete inventory all exit 0. |

The post-full serial validation group exits 0 in 386.29 s, peak RSS
2,204,094,464 bytes, without OOM or reserve stop. The earlier fresh original
24-module Derived17 receipt remains 281.90 s within its unchanged 300 s;
its source/dependency inputs are unchanged by this test-only parser-proof fix,
and that workload was not rerun or given a new allowance.

Independent read-only finder and skeptic reviews found no missing owned copy
implementation/proof obligation within the documented finite primitive fragment.
The loops and source simulations are generic, with inhabited lifecycle,
independence, replacement/tail, failure, bounds and refusal controls; heap and
memory preservation are derived. Explicit representation/capacity premises are
not presented as emitted runtime checks. The kernel result is source-interpreter
to EVM-style-machine correctness; four-mode solc/EVM runs are distinct bounded
observations, not universal bytecode/world refinement. No source-coverage or
excluded-layout claim is promoted.

Current strict documentation checking still exits 1: 48 missing references and
37 ambiguities, identical ordered findings to the published baseline and zero
new findings. This historical failure is not called passed.

Current evidence is retained in
`/workspace/memory-storage-copy-h1-20261102-evidence`. All historical failures
and earlier seals remain available. No default-branch integration, push, goal
transition or VM archival is performed. The original goal remains open as
instructed for controller integration and original adequacy review.

### Finite reference-struct published-base continuation (2026-11-01)

The same saved worker VM integrated published `5f6a75b6` (containing the
`22073f44` memory-loop publication), preserving checkpoints `8276936e` and
`2cfb116c`. The task's Lean implementation and its original observations are
unchanged. The eight public dispatch paths and the separate first-memory versus
construction-fallback refusal boundaries were reconciled in the owning docs.
No recursive graph copying, reference-element array representation, source
struct admission, intrinsic representation or optional Bridge import was added.

The actual resumed runtime was Lean 4.24.0 (`797c613`), Lake
5.0.0-src+797c613; KeySort exited 0 in 0.905 seconds. The original publication
wait is resolved: all 24 Derived17 modules were freshly checked together in
240.084 seconds, peak aggregate RSS 2,841,796,608 bytes, under one unchanged
300-second guard. The full TestSuite target subsequently passed 285 jobs in
32.260 seconds after bounded dependency scheduling. Cached confirmations are
not described as fresh proof replays.

All inhabited public struct controls and adjacent registration/refusal controls
passed 189 jobs in 45.608 seconds, peak group RSS 1,155,915,776 bytes. They retain
nested/default/empty children, literal modes, alias rebinding, deletion, exact
reverts, unreached allocation, bad-pointer and capacity controls. The selected
source tests passed 2/2, affected utility tests 31/31, the pinned upstream nested
fixture passed legacy/viaIR, and the actual 377-taclet/131-read-bearing SolKey
comparison passed. Printed allocation/source/public correctness axioms remain
`propext`, `Classical.choice`, and `Quot.sound`.

A shared scheduling-profile issue was investigated without changing proof
limits. The exact published 44-module `Evm/Correct.lean` closure, containing no
task edits, hit its pinned 11,000 heartbeats under forced serial elaboration.
Normal async elaboration with the same `-j1`, source, heartbeat and resource
limits passed both an exact-source replay (13.492 seconds) and the actual Lake
target (14.305 seconds). Its genuinely kernel-checked artifact then unblocked
the unchanged serial public controls. The serial failure remains a failure;
no source option, axiom, theorem, expected observation or budget was changed.

UnitExamples first stopped at the whole-VM guard (exit 75, 109.213 seconds,
7,906,447,360 bytes sampled workload RSS). Between jobs, read-only file-cache
advice reduced idle VM charge from 2,709,127,168 to 383,901,696 bytes while
retaining all 21,681 disk files. The unchanged check then passed in 136.337
seconds, peak group RSS 8,871,755,776 bytes; its retained 100 ms trace measured
VM charge up to 12,027,527,168 bytes. Recursion passed after dependency
scheduling in 296.673 seconds, peak RSS 2,336,432,128 bytes. DecisionHashes
also passed with ready imports in 235.233 seconds, peak RSS 6,587,949,056 bytes.

Full original-assignment completion remains **BLOCKED**, with two measured
shared prerequisites. `Examples/Decision.lean` reached its own source file and
timed out in both existing profiles (serial 300.031 seconds / 2,245,287,936 bytes
RSS; normal async 300.060 seconds / 2,238,099,456 bytes RSS).
`Examples/Tactics/OpenLoops.lean` likewise timed out in both profiles (serial
300.067 seconds / 6,763,208,704 bytes RSS; normal async 300.038 seconds /
6,774,714,368 bytes RSS). These are elapsed-time stops, not OOMs or proofs of
false claims. Both closures are byte-identical to the published base and contain
no task-owned changes. Their budget-preserving shared proof repair belongs to
the appropriate owners/coordinator. No unchanged expensive retry, sibling
implementation, target exclusion, proof refactor or limit increase was used.
The root, actual kernel TrustAudit and mandatory full `./run-lean.sh` gates
remain nonpassing; the source trust lint is a separate passing check. Initial
aggregate/trust timeouts during prerequisite builds are retained, not promoted
to passes. The initial run-lean outer RSS measured only its supervisor; its
interrupted inner guard did not leave a terminal resource record, so that inner
peak/result is UNKNOWN. All later Node/Lake checks retain separate inner logs.

The existing authorized fallback remained unchanged: hard inherited per-process
12 GiB address space, sampled 10 GiB workload-group RSS stop, sampled 12 GiB VM
charge stop, existing hard 16 GiB VM cgroup and actually disabled swap. This is
not a claim of a 12 GiB workload cgroup or a configured swap-max of zero. There
was no existing Docker workload group or image on this resumed VM.
`LEAN_NUM_THREADS=1`, explicit `-j1`, one heavy operation at a time and the
existing writer lock were retained. Source orphan/layer/strict-automatic/trust
lint gates passed; strict automation still reports 491 automatic, 61 with a
step budget, 11 refuted and zero pending. Documentation-path checks retain
48 byte-identical published-base missing references; that gate remains failed.

Independent read-only finder and skeptic source reviews, without a Lean server,
found no own-scope correctness, alias, separation, capacity, refusal or dispatch
defect. They verified the fresh24 source hashes and the valid normal-async
kernel artifact provenance. The source milestone is implemented and validated;
this does not substitute for the remaining whole-assignment gates. Cumulative
commits, original immutable checkpoints, terminal logs, resource traces, review
records and checksums are exported in
`/workspace/solidity-compiler10-memory-reference-structs-22073-compat`.
