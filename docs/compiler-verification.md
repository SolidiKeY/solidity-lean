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
primitive-member struct construction and copies from storage roots. It returns code together with a fragment
certificate; `Compiler.Compilation.correct` (`Main.compiler_checked`) proves
their common source/machine agreement. The selected path determines its
explicit input and output state relation; `inFragP` and `compile_correct`
describe the core path.

## Memory operations

`Compiler.compile` selects one compiler for the whole program: the core path
(no memory) or the memory path. The core path's output relation is `Sim`
only; using it as a prefix to memory compilation needs separate preservation
evidence.

**What the memory path accepts.** Dynamic arrays of primitive values and
structs whose members are primitive (or reference-valued, reserved as one
cell each), through typed pointer locals: element and field reads and
writes, lengths, array reads composed in indices and RHS values (`a[a[0]]`),
checked operators, short-circuit and conditional expressions over memory
operands, primitive storage writes, `require`/`revert`, blocks and
statement-level `if`. Allocation: `new T[](n)` with a simple length (the
elaborator captures effects first), a declaration without initializer (the
same as `new T[](0)`), default and literal construction of primitive-member
structs (the elaborator lowers literals to a default declaration and field
writes), and allocating rebinding. Older aliases keep their objects. `delete`
of an element, a field, a whole array local (a fresh empty array) or a whole
struct local (a fresh default object). Numeric `+=` `-=` `*=` `/=` `%=` and
standalone or captured `++`/`−−` on elements, fields and locals (the result
word stays on the stack during the checked bump, so `i = xs[i]++` and
`i = i++` are right). Nested paths through reference-valued fields
(`Evm/MemoryPaths.lean`) for reads, aliases and primitive writes;
reference-field assignment redirects a member to an existing child
(`Evm/MemoryRefWrite.lean`); deleting a reference member allocates a fresh
empty array or primitive-member struct (`Evm/MemoryRefDelete.lean`); copies
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
are checked. Nonempty reference-bearing struct construction remains refused:
it requires the separate constructor API, and this input path does not claim to
implement that API. The source/EVM fixture's constructor setup is independent
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
is implemented. Reference-bearing struct construction remains the explicit
other-lane dependency: the populated `Holder` input above proves its meaningful
array/field path without claiming constructor support. Source blocks, branches,
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

**Out of the construction fallback**: construction of structs
with reference members, other uncertified reference-member default layouts, copies other
than the primitive-member storage-root clause (including memory back to
storage and runtime-length objects, which need iteration), loops, `assert`,
calls, payments, and compound storage writes in a mixed memory program.

**Regressions** (each runs the actual source program and the public
compiler's code, with an inhabited public input):
`Evm/MemoryCompileExamples.lean`, `Evm/MemoryExprExamples.lean`,
`Evm/MemoryAllocExamples.lean`, `Evm/MemoryAllocSourceExamples.lean`,
`Evm/MemoryStructDefaultExamples.lean`, `Evm/MemoryPathExamples.lean`. The
large computed compiler results there are marked irreducible for
elaboration; kernel checks still unfold them, and the pointer compiler
recurses structurally so acceptance reduces in the kernel (no native
reduction is trusted).

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
