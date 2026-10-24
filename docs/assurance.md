# Assurance and automation work

This tracks the implementation requested from the two October 2026 audit
screenshots. Compiler extension work prioritizes memory operations. The core
package remains dependency-free.

## M1: trust gates, non-vacuity and the landed-state closer

`bash scripts/check-trust.sh` scans repository Lean sources, including the
corpus, TestSuite, root modules and vendored LeanTeX. It rejects `sorry`, bare
`admit`, native proof reduction and explicit axioms in code. Nested comments,
raw string text is blanked. Ordinary, potentially interpolated and literal-text
views are combined conservatively, so mixed nested strings and arbitrary
interpolation introducers cannot rely on one view to conceal a source finding.
Suspicious intentional literal text uses raw strings; generated proof-script
markers and diagnostics keep the same runtime strings. This is a conservative
source lint, not a complete Lean parser or a replacement for the theorem audit.
Matching spans newlines and retains source line numbers. Its tests run
with `node scripts/check-trust.test.mjs`.

`tests/trust-inventory.json` records existing `implemented_by`, unsafe,
opaque, error-recovery and kernel-option sites by file, code and occurrence
count. A changed or added site fails the gate. This inventory makes the
remaining implementation boundary reviewable; it does **not** prove that a
compiled override implements its logical definition. In particular, the
opaque cryptographic primitive remains a model assumption, recursive thunk
elaboration uses unsafe code, and error-recovery tactics can introduce a
synthetic sorry while reporting an error. No such escape is allowed in the
audited theorem dependency sets.

Six parser assertions previously used `native_decide` to create proofs about
executable parser output. They are now `#guard` checks: executable tests,
without native-reduction proof axioms. Parser correctness is not proved.

`lake env lean --tstack=131072 TrustAudit.lean` follows the transitive axioms
of the headline theorems, including ordinary/callback correctness,
symbolic execution, compilation and the new non-vacuity witnesses. Every
axiom must be `propext`, `Classical.choice` or `Quot.sound`; another axiom
fails elaboration. The existing printed axiom pins remain in the headline
module, and CI runs both the source gate and this dependency gate after its
whole-library build and axiom audit.

`Examples/Tactics/Nonvacuity.lean` proves the result of `uint x = 7;` and
refutes `x = 8` at an actual typed initial state. Soundness proves that the
false specification's translation has no calculus derivation. The execution
returns normally, so revert and exhaustion cannot explain either witness.
Signed and Boolean result specifications exercise the same positive path.

`sol_close` previously quoted `CloseS.landedAll_def` before that declaration
existed. Its delayed `sol_close_landed` macro now expands where the lemma is
available. Landed-state global observations rewrite directly. Proven
primitive-capture realizability equivalences prevent strict Spec equality
from leaving an unproved existence of its captured states. These rules are
specialized at each primitive type for dependent simplifier matching. The
positive witnesses use the public closer, and a focused example checks the
delayed macro itself.

The required read-only finder and skeptic reviews found scanner gaps for
multiline native reduction, Unicode opaque names, raw strings and executable
interpolation and escaped identifiers, plus a missing public-closer regression and stale defect
documentation. The implementation and regressions address those findings. A final review
also found mixed literal/interpolated nesting; scanning nonraw literal text
as a third conservative view covers it without a keyword-introducer list.

Focused module checks and the source-audit tests pass. The headline axiom
gate passed for the public-closer witnesses; rerun it after later proof changes. Whole-library and full runner confirmation remain due after the
remaining milestones.

## M2: primitive-array compiler path

`Evm/Memory.lean` adds runtime-address memory instructions and checked
primitive-array access sequences. An array's length cell precedes its
elements. The representation has an explicit word-address no-wrap bound;
an out-of-bounds index reverts before reading or writing an element.

`Evm/MemoryHeap.lean` uses one base map indexed by source heap identity.
Aliases therefore share a base. Distinct arrays have disjoint intervals,
including their length cells, and every interval lies above the reserved
local-frame limit. Proven element writes preserve the representation of
every array and all reserved local cells. Local writes preserve the heap.

`Evm/MemorySource.lean` augments the existing core simulation with that heap
relation and actual typed pointer locals. Source reads and writes evaluate
their operands in source order, use the existing core expression compiler
for indices and RHS values, and preserve the combined relation on success.
Both sides revert together when those expressions fail or an index is out
of bounds. Reads can assign their result to a typed primitive local.
The pointer relation currently requires every primitive-array memory local
to be initialized. Unset declarations need explicit representation rules
or a live-pointer condition before they can be admitted.

At M2, `Memory.compileProg` in `Evm/MemoryCompile.lean` was an additive compiler
path over the existing scoped `Prog`. Its successful result carries an
erased fragment certificate, whose composition theorem proves agreement
with `Prog.run`, including evaluation-stack preservation. Unsupported
statements were explicitly refused. This did not change the original
`Evm.inFrag` or its compiler theorem: it still refuses memory. Allocation,
declarations, length expressions and a unified compiler entry were still due.

`Evm/MemoryCompileExamples.lean` proves that the full representation has a
populated witness: two real source locals alias one array, and another
local points at an independent array. A program accepted by the compiler
writes through one alias and reads through the other. Kernel checks pin
both source and generated-code results, independent-object and other-element
preservation, pointer and length preservation, and matching reversion at
the length boundary. The earlier shared-base machine examples remain local
instruction tests, rather than being presented as source-alias coverage.

The first read-only finder/skeptic review required global object separation,
pointer-local representation, semantic local-frame preservation and actual
source-alias regressions; the new modules address those findings. The final
review found no concrete soundness defect and required an exact source
revert regression, now present, plus explicit documentation of initialized
pointer locals. Focused module checks and the compiled-program build pass.
The transitive gate checks all 26 headline theorems with only the standard
three axioms. The source gate reports 488 sources, 201 inventoried sites
and zero findings; its regression tests pass.

The orphan checker finds all new modules reachable, but fails on 25 existing
ignored `Solidity/Scratch/` files. The prose-path checker reports 13 existing
missing paths in vendored-source references and the Eqns module's Mathlib reference; neither
check is claimed green. Whole-library/full-runner confirmation remains due.

## M3: local operations, composed memory values and the checked entry

`Evm/MemoryLocals.lean` proves array-length reads, primitive declarations
(including defaults), local assignments and memory alias declarations and
rebinding. Local declarations require the final frame to fit the reserved
region. Every admitted statement preserves or grows its context; the program
proof uses that monotonicity to bound each intermediate frame from the final
context's bound. Unset memory locals are not admitted: alias declarations
bind initialized references, and default primitive declarations produce the
typed default represented by zero.

Value certificates recursively compose array reads in indices. Array writes
carry separate index and RHS certificates; the generated code evaluates the
RHS, receiver pointer and index in source order. The generalized operation
lemmas apply the index proof at the exact stack containing saved temporary
operands. Successful `ValOutT` premises preserve every machine field apart
from pushing the returned word. Memory reads and lengths therefore work in
write RHS/index positions and in nested indexed reads.

`Compiler.compile` (`Evm/Compiler.lean`) is a single checked entry. It selects
the existing core compiler when its fragment applies, otherwise the memory
compiler. The result keeps code and fragment evidence together. Its common
agreement theorem preserves the core state and evaluation stack on the core
path, and the full primitive-array heap/pointer relation on the memory path.
`Main.compiler_checked` restates this public theorem and pins its axioms.
The memory input explicitly includes the layout and final-frame bound.

The populated regressions go through the actual compiler: alias declaration,
length capture, rebinding to a distinct object, default and core-initialized
primitive declarations, a write whose index and RHS read arrays, and a nested
`a[a[0]]` read. They pin source and target values, independent-object and
pointer preservation, exact reversion for failed RHS/index reads, and failure
of a post-state claim with insufficient frame capacity. Both public compiler
dispatch paths are exercised.

The required read-only finder/skeptic reviews found no concrete soundness
defect. Their missing core-value regression and default/composed-expression
coverage findings were addressed and reviewed again. Allocation remains
unsupported. At M3, selection was per whole program: mixed memory with
legacy guards, branches, storage statements or calls is not yet supported;
arithmetic whose operands contain memory reads is also refused. Regressions
pin those refusals. A core-path result retains only `Sim`, so it cannot be
composed into a later memory compilation without additional heap/pointer
preservation evidence. These are remaining compiler work, not proven coverage.

Focused file diagnostics and the compiler/public-theorem build pass. The
headline dependency gate checks 39 theorems using only `propext`,
`Classical.choice` and `Quot.sound`. Whole-library/full-runner confirmation
remains due after the other requested work.

## M4: memory expressions, guards and storage writes

`Evm/MemoryExpr.lean` lifts the core compiler's checked operator proofs to
recursively certified memory operands. Binary/unary operators, short-circuit
Boolean operators and conditional expressions retain exact operand stacks
and preserve every nonstack field. The memory value compiler recursively
composes these clauses with array reads and lengths.

`Evm/MemoryStatements.lean` proves primitive storage writes preserve the
heap/pointer relation, using the existing storage representation and
length-slot preservation lemmas. Generic `require` guards and plain reverts
compose with memory statements. `assert`, statement-level branches and calls
remain unsupported on this path.

`Solidity/Evm/MemoryExprExamples.lean` runs actual source programs and code
returned by the public compiler. It covers arithmetic over reads, signed
negation, checked underflow/overflow/division failure, true/false guards,
and a memory-to-storage write checked by a guard and read back into memory.
Other elements, the independent array and pointer locals are pinned.

Both required read-only reviews found no concrete soundness defect. They
identified missing Boolean fallthrough and false-conditional coverage;
regressions now pin exact reversion for evaluated failing right operands and
successful selection of the else expression while skipping an invalid then
expression. Per-file diagnostics and the focused compiler build pass. The
transitive gate passes for 49 headline theorems with only the standard three
axioms. The source gate passes for 493 sources and 201 inventoried sites, and
its two regression tests pass. The orphan and prose-path checks retain their
25 ignored scratch-file and 13 missing-reference baselines. Whole-library
and full-runner confirmation remain due.

## M5: quantified premises at later counters

`Calculus/CloseAll.lean` adds bounded `allLeft` applications after the closer
opens its state and value binders. A later local or anonymised loop counter
is then an ordinary numeric term, including a typed value projection. No
term is inserted into an older formula scope. Propositional arguments are
proved before application; unavailable guards remain implications. Data
functions returning propositions are excluded from the premise candidates.

The quantified fallback retains Theory equations so that earlier premises
and later conclusions read the same observations. It runs only for a leaf
with a quantified premise. The existing scoped `allLeftHide` pre-pass remains
available for literals and locals already in the premise's scope. Range and
witness enrichment now retains its facts when its simplifier makes no
further progress.

`Examples/Tactics/AllLeftLater.lean` proves later universally bound indices,
a program local initialized from a parameter, and an actual invariant loop
whose body checks `balances[i]` using a premise stated before `i` existed.
It also checks proved/unavailable guards, rejection of data functions as
universal proofs, and recovery from expensive candidate-result reduction.
`sol_close_all?` prints checked proof applications; both ordinary and
inaccessible-binder suggestions are pinned and replayed without search in
`Examples/ProofTree.lean`.

Both required read-only reviews identified a reduction-cost gap in the first
version's count budgets. Each normalization, candidate/guard, replay/note and
clear step now has bounded heartbeat recovery and saved-state rollback.
The complete search and quantified fallback have separate limits as well.
The dependent-result regression reaches the formerly unprotected reduction
before guard solving, confirms a normal failure and continues with a fallback
proof. Both reviewers accepted the repair. The affected-area build passed
(259 jobs, including the existing loop and import regressions), and the
transitive gate passed for 52 headline theorems with only the standard three
axioms. The source gate passed for 495 sources and 201 inventoried sites;
its two regression tests passed. The 25 scratch-orphan and 13 prose-path
baseline failures remain. Whole-library/full-runner confirmation is still due.

That build also exposed existing panic output in the closer's bare-term
reflexivity test: `atomE?` read constructor arguments from a free variable
before checking its shape. It now checks the two admitted constructor heads
and arities first. The existing regression requires no diagnostic messages.
Both read-only reviewers accepted the shape guard. Focused diagnostics,
the refreshed affected-area build (241 jobs) and the 52-theorem axiom gate
pass, with no panic output in the build log.

This does not infer loop invariants, solve the four large open loop ports,
or finish arbitrary ABI memory-array scans. Their memory read/length
normalization still leaves obligations beyond the new instance selection.

## M6: symbolic nonlinear bounds and squares

`Calculus/CloseNonlin.lean` now instantiates the frozen SolKey rules
`multiply_inEq0`, `square_nonneg` and `add_non_neg_square`, alongside the
existing `multiply_2_inEq0`. Relevant symbolic comparisons, including literal
coefficients, can be multiplied with sign-guarded order reversal. Squares of
compound factors and pairwise atom differences provide inequalities without
literal upper bounds. The selector remains incomplete and dependency-free.

The selector examines at most 256 declarations, 8,192 expression nodes and
16 products, then uses at most four atoms, eight factors, twelve comparisons
and 128 checked facts. Each expensive step and the complete search have
heartbeat recovery and rollback. Products in the target seed the search
before unrelated premise products; premise products seed it only when the
target contains none. A comparison is accepted as syntactically linear only
after its product scan completes. `sol_close_nonlin?` prints explicit proof
applications, with the suggestion pinned and replayed.

`Examples/Tactics/Nonlinear.lean` proves symbolic scaling by either sign,
strict and coefficient bounds, four-variable product order, compound squares,
`2*x*y <= x*x+y*y`, and a scoped program with checked Solidity multiplications.
Regressions enforce the atom budget and keep sixteen irrelevant products
from exhausting the target's factor budget.

The required read-only reviews found coefficient rejection, target-budget
starvation and an incomplete-scan linearity check in the first version.
These were repaired and reviewed again. New file diagnostics pass, and the
existing recursion regression passed (158 seconds for the complete file in
the final run, including its triangular-number contract). The first broader
build found a namespace-spelling mismatch in the new replay pin, now corrected.
The final affected-area build passes all 248 jobs, including the recursion
and replay regressions; per-file diagnostics pass. The transitive gate passes
for 63 headline theorems with only the standard three axioms. The source gate
passes for 496 sources and 201 inventoried sites; its two regression tests
pass. Orphan and prose-path checks retain their 25 ignored scratch-file and
13 missing-reference baselines. Whole-library/full-runner confirmation is
still due after the remaining work.

These are checked arithmetic instances, not general nonlinear decision
procedures. `#verify`'s exact-fragment limitations remain explicit.

## M7: quantified ABI memory scans

`CloseScoped` now rewrites memory reads and lengths through local pushes
and counter assignments for ordinary input arrays, as well as allocated
objects. A rebuilt index normalizes to the same typed index independently
of its range proof. After `allLeft` instantiation, the closer exposes the
existential element witnesses and simplifies their reads. A captured value
whose integer observation is known is reused through a proved subtype law.
The final constructor pass is iterative, visits at most 128 constructors,
and bounds each step at 1,000 heartbeats with rollback. Arithmetic is tried
before reflexivity, avoiding reduction of large dependent state terms.

`tests/solc/ArrayScans.sol` and its hash-checked pinned-solc AST supply three
public-strategy regressions: unsigned upper bounds under a box, both signed
bounds with a diamond and decreasing `xs.length - i`, and signed upper
bounds under a box. Their element premises come from ABI import. Their
invariants and the diamond's variant are supplied explicitly. The combined
two-assert signed diamond now proves through `sol_symex; sol_close`, keeping
the weakest precondition together. Its `sol_prove` walk still exceeds the
declaration budget by expanding each leaf separately; no heartbeat limit
was raised. This does not establish arbitrary array-loop automation or
invariant inference.

Both required read-only reviewers found no concrete soundness or goal-loss
defect. Their suggested regressions now check that an unsupported existential
survives beside a supported capture, and that the 128-step limit retains its
unfinished tail. Per-file checks pass for the closer, imported proofs and
these regressions. The affected-area build passed 243 jobs, and the transitive
gate passed for 68 headline theorems using only the standard three axioms.
The source gate passes for 497 sources and 201 inventoried sites, with both
regression tests passing. Orphan/prose-path checks retain their 25 ignored
scratch modules and 13 missing-reference baselines. The goal-retention
regressions also pass their final focused build and axiom check. The follow-up
reviews confirm the retained-tail test; the supported sibling's reduced
`True` target is explicitly pinned before it closes.

M7 follow-up: the combined signed fixture was restored with both assertions.
The public symbolic-execution proof checks its shared weakest precondition;
the earlier split fixtures are no longer the only evidence for signed bounds.
The updated fixture build passes 153 jobs and the 68-headline axiom audit passes. Both read-only reviewers confirm the restored source/AST and full obligation.

## M8: memory allocation foundation

`Evm/MemoryAlloc.lean` uses existing machine instructions for primitive-array
bump allocation. Its kernel proofs establish the exact stack/header/cursor
behavior, primitive defaults in the actual fresh typed heap object, preservation
of old objects, and the address map's extension at exactly the new identity.
`AllocatorRepr` bundles separated arrays below the cursor, a reserved frame,
and a zeroed free tail. Allocation and intervening in-bounds writes preserve
these conditions, supporting repeated allocation. Capacity is the explicit
strict bound `cursor + size + 1 < 2^256`; the next cursor must itself fit.

The inhabited fixture in `MemoryAllocExamples.lean` allocates a uint array,
writes seven into it, then allocates an empty bool array. Kernel computations
check the distinct returned pointer, old nonzero alias read, cursor, reserved
cell, headers/defaults, and an out-of-bounds read from the second array.

Both read-only reviewers found no false foundation statement. They identified
an integration requirement: positive frame size alone does not reserve cell
zero from locals based at `b = 0`. The future combined source relation must
require `0 < b` or change the local layout. At this milestone the public compiler continued to
refuse allocation until that relation, extensible output address maps and
source execution/capacity proofs were integrated (completed for declarations
in M10 below). This milestone establishes
the allocation lemmas rather than claiming the compiler extension complete.
Per-file diagnostics and the final focused build pass (164 jobs). The transitive
gate checks 77 headline theorems using only the standard three axioms. Both
read-only reviewers confirmed the nonzero-write and repeated-allocation
fixtures, dirty-tail rejection and strict cursor-capacity boundary. The source
audit passes; the orphan check still reports 25 existing unimported scratch
modules, and the prose path check retains its 13 existing missing references.

## M9: scoped source allocation

`Evm/MemoryAllocSource.lean` proves that primitive `new T[](n)` copies exactly
one default object, then matches the actual scoped declaration run with
length evaluation, bump allocation and pointer-local storage. The local
simulation retains both the typed state and allocator relations, extends the
address map at the fresh identity and preserves the evaluation stack. Its
premises explicitly require `0 < b`, local-frame space and the strict
allocation-capacity bound. `AllocatorRepr.localWrite` keeps the cursor and
free tail intact when the pointer is stored in its nonzero reserved cell.

The joint source/machine fixture reads its first length from an existing
local, allocates an int array and then an empty bool array. Actual runs check
source identities/lengths, old local values, distinct runtime pointers,
cursor/defaults, a reserved sentinel, the signed default read and empty-array
reversion. At this milestone the local source simulation preceded public program support;
M10 below integrates growing-map results, allocator preservation through mixed
statements and reached-allocation capacity into the public certificate.

Per-file diagnostics and the focused serial build pass (66 jobs). The axiom
gate passes for 89 headline theorems, using only the standard three axioms;
the source gate passes for 501 sources and 201 inventoried sites with both
regression tests passing. Both read-only reviewers confirm the source step,
joint witness, actual runs and stated scope. The orphan check reports the
25 existing unimported scratch modules (488 modules reachable), and the
prose path check retains its 13 existing missing references. No new module
is orphaned or cited by a missing path. The memory guard remains active;
idle proof workers were released after verification.

## M10: allocating declarations through the public compiler

The public memory path now accepts primitive `new T[](n)` declarations and
composes them with its existing local/array/storage writes, alias operations,
lengths, checked expressions and guards. Allocation is rejected at frame base
zero. Existing nonallocating programs retain their state requirements and
can still use that base.

`ResultRepr` now preserves an available allocator across existing statements.
`GrowingResult` carries the output address map, preserves every older typed
reference's address, and records the exact cursor advance. The compiler's
cost is computed from typed source syntax and successful execution prefixes,
not from its erased proof certificate. Each reached allocation costs its
length plus a header, including empty arrays. The public input supplies a
joint state/allocator witness and enough space for that cost. Unreachable
suffixes after a revert contribute no cost. Capacity remains a theorem
premise; generated code has no runtime capacity check.

The public fixture compiles consecutive int/empty-bool allocations. A mixed
fixture allocates an int array, binds another alias, writes seven, changes
the length local from two to three, allocates a bool array using that local,
and checks the old alias. Actual source and target runs pin the written
value, updated length, distinct pointers, cursor, defaults and reserved
sentinel. A revert followed by a maximal allocation has a zero-cost input
and reverts without an allocator premise; a reached whole-address-space
request cannot satisfy the actual public capacity input. The cost skips
interpretation when its suffix has no allocations, so this rejection does
not construct the enormous source heap. A theorem proves this optimization
equal to the reached-prefix cost. The earlier frame-base-zero
allocation refusal regression remains in place.

Per-file checks and the focused serial build pass (144 jobs), including the
existing public memory/compiler regressions and headline theorems. The
transitive audit passes for 107 headline theorems with only the standard
three axioms. The source gate passes for 502 sources and 201 inventoried
sites; both audit regression tests pass. Both read-only reviewers confirm
allocator preservation, reached-cost composition and its lazy optimization,
the actual public capacity rejection, mixed fixtures and stated scope. The
orphan/path checks retain the 25 existing unimported scratch modules and
13 missing references; every new module is reachable. The RAM guard stayed
active, and idle proof workers were released before serial builds. Allocating
rebinding was completed in M11 below; statement-level control flow, structs/
copies and remaining mixed operations still require extension.

## M11: allocating rebinding

The public memory compiler now accepts `xs = new T[](n)` for primitive
arrays. The source proof matches the actual `MRhs` allocation and
`TRun.rebindMem`, then changes the destination's typed reference and runtime
pointer together. All other locals and older heap objects retain their
representation; old aliases continue to use their old identity-to-address
mapping. Rebinding is rejected at frame base zero and contributes its length
plus header to the same reached-capacity input as a declaration.

The public fixture keeps an alias to the first array, writes seven, replaces
the original with a new array containing nine, checks both references, then
replaces the original again with an empty array. Actual source/target runs
check three identities, distinct pointers, cursor, local length and reserved
sentinel. The older alias still reads seven; the empty destination rejects
index zero; the intermediate object retains nine in both the actual typed
heap and target memory after losing its last local reference. The actual
public input rejects a maximal rebinding request without constructing its
source heap. An ordinary `sol{…}` program with declaration, alias, nonzero
write, allocating rebinding and a read-based guard also compiles, pinning the
elaborator's path into the new clause.

Per-file errors/warnings and the focused serial build pass (144 jobs),
including existing public-memory regressions and headline proofs. The axiom
audit passes for 118 headline theorems using only the standard three axioms.
The source gate passes for 502 sources and 201 inventoried sites, with both
regression tests passing. Both read-only reviewers confirm source ordering,
old-alias/object preservation, capacity accounting, actual fixtures and the
surface-acceptance claim. Their final prose check found a stale introductory
audit count; that count is now omitted to avoid future drift. Orphan/path
checks retain 25 existing unimported scratch modules and 13 missing-reference
baselines. Idle proof workers were released, and the RAM guard remains active.
Statement-level control flow and the other remaining original requirements
are still open.

## M12: memory blocks and branches

The certified memory path now compiles explicit scoped blocks and
statement-level `if`. Scope exit drops temporary value/pointer locals while
preserving older local updates, the grown heap and the address-map extension.
Both branches start from the same input fragment, and their retained core
alias flags meet at the join. The checked condition can read memory and
revert. Only the selected branch contributes allocation cost; neither body
contributes when evaluating the condition fails.

`frameNeedProg` reserves the maximum context used anywhere in the program,
including temporary locals in either branch. A final-context bound alone
would permit temporary locals to overwrite heap cells, so the public memory
input now uses this peak bound. Mutual fragment certificates carry proofs for
nested bodies, and their generated induction principle proves program
composition without a trusted recursive checker. `Compilation.memory_input`
opens the public premises without normalizing the entire compiler result;
larger existing examples otherwise hit the fixed heartbeat budget. No
heartbeat limit was raised.

The inhabited public fixtures run two explicit blocks, retain the outer
length update, reuse temporary local cells, retain two allocated arrays and
their nonzero elements, and reject an insufficient temporary frame even when
the final context fits. Ordinary `sol{…}` fixtures exercise both choices of
`if`, escape an inner array pointer through an outer local, preserve an old
alias, reuse branch-local cells and skip oversized allocations in the other
branch. Standalone surface blocks retain hidden locals in the current
elaborator; the explicit-block fixture tests actual context dropping. Further
fixtures pin either branch reverting before a maximal request, and an
out-of-bounds condition that skips both maximal requests. All use actual
source states and machine runs, with public agreement and capacity premises.

Per-file compiler, scope and fixture diagnostics pass without errors or
warnings. The focused serial build passes (145 jobs), and all 140 audited
headline proofs use only the standard three axioms. The source gate reports
503 sources, 201 inventoried sites and zero findings; its regression test
passes. Both read-only reviewers confirm the peak frame bound, selected costs,
scope/map/allocator preservation, branch jumps, inhabited fixtures and stated
scope. Orphan/path checks retain the existing 25 scratch orphans and 13 missing
references; the new module is reachable. The RAM guard stopped two checks at
its 16 GiB process budget while system memory remained available. After
rearming it and releasing idle workers, final checks passed serially; the
chat's Lean processes then used about 0.6 GiB, with 32.5 GiB available.

## M13: demanded memory reads in loop proofs

The scoped reducer now applies the existing proved memory taclets when a
primitive read, array length or identity read is formed, before subsequent
writes duplicate it. `foldMem2` bounds the input by `normalizationSize` and
retains the reduction only when it has no more nodes than the original.
`foldMem2_eval` proves equality of the complete optional result, so failed
writes and invalid reads retain their definedness conditions. The stores
themselves remain lazy. This extends the existing early storage-read and
checked-index folding rather than changing the formula representation.

The actual runner now proves `binomialFaithfulRowsSmall` in about seven
seconds, where it previously timed out after 57 seconds. The original source
is copied into `tests/solc/OpenLoops.sol`, compiled by pinned solc 0.8.34, and
hash-checked by `Examples/Tactics/OpenLoops.lean`; its public `sol_prove`
theorem needs neither an invariant annotation nor a heartbeat override.
`Examples/Tactics/Decide.lean` also proves a diamond with eight repeated
doublings through memory writes. Regressions retain oversized inputs and
initial heap reads, keep a possibly failing write's guard, and refuse an
empty-array read as a diamond witness.

The nine-row binomial still times out at the declaration budget (about 58
seconds), and the nested storage-push loop still times out after its 512-step
stage (about 37 seconds). The 43-push loop still times out at kernel reduction
(about 59 seconds) under the runner's clean-tail premise. Both read-only
reviewers confirm semantic preservation, the node bound, exact source/AST
fidelity and the stated scope. Their suggested concrete failing-write test
now proves that the reduced observation evaluates to `none`. The final
affected-area build passes all 275 jobs, including memory decisions, loops,
ABI scans, recursion, proof-tree pins and `TestSuite/Derived17`; the final
definedness-test refresh also passes (162 jobs). All 144 audited headline
proofs use only the standard three axioms. The source gate reports 504
sources, 201 inventoried sites and zero findings; its regression test passes.
The final original-source runner measurement is 6870 ms, status `proved`.
Orphan/path checks retain the existing 25 scratch orphans and 13 missing
references, with the new proof module reachable. The RAM guard stayed active
without triggering during final validation. This milestone resolves one of
the four original timeouts; the others remain required work.

## M14: computed memory revert operands

`RevPart.mem` carries a typed memory local and the reason/raw distinction.
The typed run copies its current heap bytes into revert data: reason operands
use the existing `Error(string)` ABI encoding, raw operands retain the buffer
unchanged, and an empty raw buffer yields the ordinary empty-data revert.
Quoting, weakening, no-panic and payload-overapproximation proofs handle the
new operand. No formula or statement constructor was added. Computed
`revert(reason)` and `require(c, reason)` lower to it; require captures the
condition before reason effects and evaluates the reason even on success.
The existing literal lowering is preserved, including its self-frame limit.

The solc importer recognizes the canonical whole-buffer assembly rethrow
`revert(add(data, 32), mload(data))`. Its AST must contain exactly that one
statement, the offset must be 32, both operands must reference the same local
declaration, and the local must have a byte-buffer shape. Other offsets,
mismatched length sources, extra statements and `uint[]` buffers have pinned
unsupported reports. A local named `by` tests source renaming. The positive
fixture retains public self-call bodies using the existing `testing` option.

`Semantics/RevertMemory.lean` proves that set operands read the exact current
object, unset operands revert, the statement returns exactly those bytes,
and a non-divergent finite execution certifies the unbounded run.
`Examples/Tactics/ComputedRevert.lean` proves the actual pinned source's
computed `Error("boom!")` outcome and eager reason evaluation. It also proves
alias writes, raw-empty versus Error-empty data, condition capture and the
renamed source buffer. The complete 100-byte nested raw catch/rethrow and
outer Error decode have executable guards; these are regression checks, not
kernel proofs of the full nested source run. Whole-buffer kernel reduction
proved too costly as one certificate and was stopped without raising budgets.

The required finder/skeptic review found that the initial shape check also
accepted a bytes local as a string reason. A source-kind check now runs before
byte erasure and hoisting, and require captures its reason in a fresh string
local. Negative surface regressions reject both bytes-reason spellings; an
explicit `string(data)` remains accepted. Literal conversions also check UTF-8,
including nested casts/concats, while runtime byte-to-string casts retain
arbitrary bytes; both cases have regression coverage. The source's false-condition concat
and eager reason failure now have exact unbounded execution certificates.
Both reviewers confirm the focused fix and the conservative catch fallback;
stale self-frame and assembly-scope documentation was corrected as well.

Exact symbolic catch reasoning remains required: `RevPart.pat?` returns
`none` for computed operands and `catchDataBox` uses the existing arbitrary
byte allocation goal. This is a conservative fallback, not the requested
exact relationship between callee memory and catch data. Broader panic/error
class alignment also remains open.

Final validation passes the default build (479 jobs), TestSuite (175 jobs),
the frozen SolKey sort check (377 taclets, all 131 read-bearing annotations)
and all 162 headline axiom checks. The source trust gate reports 507 sources,
201 inventoried sites and zero findings; its regression test passes. The
finder and skeptic also confirm the refreshed constructor diagnostics and
copied-field printer pins: unsupported constructors remain unsupported, and
memory normalization retains the definedness guard and copy antecedent.
The orphan/path checks retain the existing 25 scratch orphans and 13 missing
references. The separate static TestSuite audit still rejects the pre-existing
205000-heartbeat override in `TestSuite/Derived15.lean`; it is not relaxed here.
The first full build was stopped by the RAM guard at 16.08 GiB; individually
requested remaining modules and the final build/TestSuite/audit retry passed
without another cutoff.

## M15: primitive memory deletion

The public compiler accepts `delete xs[i]` and `delete xs` for primitive
arrays. `Evm/MemoryDelete.lean` proves element deletion equals a write of the
typed default, including index failure. Its generated code runs the index
once and writes zero through the existing heap-preserving write simulation.
Array-local deletion instead equals allocating rebinding to a fresh empty
array. Its fragment certificate reuses the checked rebinding certificate;
the source execution, reserved-frame bound and one-cell allocation cost
agree definitionally. Existing aliases keep their object and address.

Surface regressions through the public entry use an inhabited allocator and
initial state. A computed index deletes through one alias, later writes
remain visible through the old alias, and two whole-local deletions leave
two fresh empty objects. Exact source/target observations retain the older
object, zeroed element, second-element write, pointers and sentinel. Signed
and Boolean arrays test both default elements and whole-local deletion.
Empty/nonempty boundary failures revert, and a failed nested index skips a
later array deletion and maximal allocation; only the reached two-cell
prefix contributes to its capacity input. Local deletion at frame base zero
is explicitly refused.

The finder and skeptic independently confirm the source semantics, certificate
reuse, allocation accounting, alias preservation and concrete public-entry
coverage, with no defects or weakened checks found. Per-file checks report no
errors or warnings. Final validation passes the default build (480 jobs),
TestSuite (175 jobs), the frozen sort check and all 179 headline axiom checks.
The source gate reports 508 sources, 201 inventoried sites and zero findings;
its regression test and whitespace check pass. The new module is reachable;
the existing 25 scratch orphans and 13 missing prose references remain.
The legacy invariant replay now also checks under the default heartbeat
budget. Its stale 205000 override was removed without changing the theorem
or proof; both read-only reviewers confirmed the diff. The separate static
TestSuite audit now passes: 27 modules, 546 derived functions, 17 pending and
one excluded. The RAM guard did not trigger during this milestone's checks.

## M16: compound updates with memory operands

The checked entry accepts all five numeric compound operators on dynamic
primitive-array elements and primitive locals. `Evm/MemoryCompound.lean`
expresses the checked result in the existing value language and proves the
complete source-result equalities needed to reuse ordinary memory/local
write certificates. Reads are pure and evaluator errors are only reverts;
the proof treats failing RHS, address and old-value reads explicitly rather
than assuming their different evaluation orders commute for arbitrary halts.
No target instruction, source evaluator or error class was changed.

Public-entry regressions have inhabited state/allocator premises. A local
index and memory RHS values compose all five operators, update shared aliases
and retain an independent object, lengths and pointer locals. Nine unsigned
failure cases cover bad bounds, bad RHS, both together, range errors, zero
divisors and local failures. Signed surface code tests all five operations,
truncation toward zero, negative remainders and a local consuming memory.
The signed minimum divided by minus one and addition above the signed maximum
both have source/target failure and public simulation certificates.

An initial implicit reduction of the larger simulation input hit the RAM
guard at 16.66 GiB combined RSS while 19.89 GiB remained available. Revealing
the same premises with `Compilation.memory_input` avoided expanding the whole
certified compiler result; the file then checked in about four seconds. The
guard was rearmed and now continues monitoring after a cutoff, covering later
language-server restarts too.

The finder and skeptic independently confirm the read-order argument,
certificate reuse, zero allocation cost, alias/capacity preservation and
stated regression scope; no fixes were required. Per-file checks are clean.
Final validation passes all 481 default-build jobs, all 175 TestSuite jobs,
the frozen sort check and all 195 headline axiom checks. The source trust
gate reports 509 sources, 201 inventoried sites and zero findings; its
regression test, static TestSuite audit and whitespace check pass. Both new
memory modules are reachable; orphan/path checks retain the existing 25
scratch orphans and 13 missing references. Final serial validation did not
trigger the guard; after worker cleanup Lean uses about 0.7 GiB.

## M17: standalone memory and local increments/decrements

The checked memory entry accepts standalone prefix/postfix increment and
decrement on numeric array elements and primitive locals. `Evm/MemoryCompound.lean`
proves the complete source-result equality with checked compound addition or
subtraction by one. The compiler wraps the existing compound/write certificates;
target code, failure classes, allocation costs and frame requirements are reused.
Bumps whose expression result is captured (`assignIncDec`) remain outside this
memory path.

The public-entry tests cover all four forms, shared aliases and an independent
object, unchanged lengths/pointers/neighbouring elements, and local updates.
A surface computed index reads the very aliased element being incremented.
Signed surface programs exercise array/local updates below zero. Five unsigned
failure cases cover bounds and both local/array range edges; four signed cases
cover both limits for locals and array elements. A failed computed index skips
a later maximal allocation and needs only the reached two-cell capacity prefix.
Every simulation has an inhabited state/allocator input.

The first combined target-observation certificate crossed the RAM guard at
16.73 GiB summed Lean RSS while 20.02 GiB remained available. The guard stopped
those processes. Splitting the same coverage into smaller programs checked
without raising budgets. The monitor stays armed after a cutoff.

Three bounded loop-repair experiments were rejected: guarded numeric folding,
retaining only successfully captured literals, and dropping large positive
premises for ground branch refutations left the original nine-row timeout at
about 58 seconds. None of those code changes is retained. A scratch timing
probe attributes almost all of the 512-step walk's roughly 13 seconds to
branch refutations. The large memory guards are diamond landing conjuncts,
which cannot be dropped as ordinary premises. The three loop gaps remain open.

The finder and skeptic independently confirm the complete result equalities,
certificate reuse, failure/index ordering, capacity/frame accounting, inhabited
inputs and stated scope; no defects or overclaims were found. Per-file checks
report no errors or warnings. Final validation passes all 481 default-build
jobs, all 175 TestSuite jobs, the frozen 377-taclet/131-annotation sort check
and all 215 headline axiom checks. The source gate reports 509 sources, 201
inventoried sites and zero findings; its regression test, static TestSuite
audit and whitespace check pass. Orphan/path checks retain the existing 25
scratch orphans and 13 missing prose references. Final serial validation did
not trigger the RAM guard; after releasing workers Lean uses about 0.7 GiB.

## M18: captured memory and local bump results

The memory compiler accepts `assignIncDec` for primitive-array elements and
numeric locals. `Evm/MemoryCapture.lean` proves full source-result equalities
with a value capture, a standalone bump, and the final destination assignment.
A prefix captures the checked new value; a postfix captures the old one.
Generated code retains that result word below the bump's working stack and
stores it only after the bump succeeds. Thus `i = xs[i]++` uses the original
index and `i = i++` restores the old value. The generic composition theorem
preserves the entire typed state relation, stack, address map and allocator.
It adds no local cell or allocation cost. `compileBump` shares the already
certified standalone code between both forms.

Public tests check all four forms, destination/index overlap, shared aliases,
an independent object, unchanged neighbours/headers/pointers and local
self-assignment. Surface declarations capture signed old/new values, and two
post-increments in one unsigned expression capture seven then eight and leave
nine. Five unsigned failure cases and four signed cases cover bounds and both
local/array range edges. A failed captured computed index skips a later maximal
allocation with an inhabited two-cell capacity prefix. Every simulation has
a concrete public-entry input. One existing failed-increment target replay now
uses a kernel-checked Boolean inversion to prove the same exact reversion
instead of expanding the larger compiler certificate through `rfl`; its
statement and budget are unchanged.

The finder and skeptic independently confirm the full source-result
semantics, old-index and self-assignment behaviour, stack/allocator composition,
certificate reuse, inhabited regressions and documentation; neither found a
defect or overclaim. Per-file checks report no errors or warnings. Final
validation passes all 482 default-build jobs, 175 TestSuite jobs, the frozen
377-taclet/131-annotation sort check and all 240 headline axiom checks. The
source trust gate reports 510 sources, 201 inventoried sites and zero findings;
its regression test, static TestSuite audit and whitespace check pass. The new
module is reachable. The existing 25 scratch orphans and 13 missing prose
references remain. No RAM cutoff was recorded during this milestone's checks; completed workers
were released. Final process inspection found the old watchdog had ended, so
it was restarted and its new live process verified before further work.

## M19: bounded rigid branch pruning

Literal-local branch conditions are substituted backward through their scoped
updates by `Hyps.rigid`, reusing `applyOnRigidFormula`'s `Fml.substU` and the
existing binder-thinning law. `Hyps.rigid_lift` proves that a projected fact
can strengthen a sequent while keeping its original context. In particular,
`Seq.refuteLanded_sound` uses the surviving sibling's derivation; it does not
assume away a diamond prefix's failed update or exhaustion. The generic walk
passes that actual sibling proof in both split and guarded-update branches.
No `Proves` constructor or semantic rule changed.

The read-only finder and skeptic both identified an initially unbounded
substitution path: repeated `x := x + x` could expand the condition before
the closer checked its bounds. The repair checks the condition and update
against a 512-node cap before each substitution and checks the final result
as well. Ground projections that refuse or fail leave both branches, without
falling back to the same expensive contextual expansion. Non-ground guards
retain the previous closer. This deliberately loses some pruning from unused
contradictory premises; a regression pins that conservative choice.

Regressions prove an eight-iteration memory-writing diamond loop and prove a
division-by-zero prefix invalid, while checking that its walk retains a leaf.
Forty repeated self-doublings remain classified as ground but refuse bounded
projection and pruning, before a trillion-node expansion could accumulate.
The new compiled twin has a kernel-checked equivalence theorem and a source
inventory entry. Five additional transitive-axiom headlines cover the
projection, transport, refutation and positive/negative examples.

Two prior experiments were discarded: successful memory-payload capture did
not improve the nine-row timeout (61.4 seconds after the 1024-step stage),
and boxing/slicing full contextual refutations still expanded unrelated
histories. Rigid-condition substitution instead reached two leaves at 2048
steps in roughly five seconds in the isolated compiled walk. The public
proof construction remains open: it crossed the RAM guard both with idle
workers present (16.06 GiB summed RSS, 20.73 GiB available) and alone (16.49
GiB summed RSS, 15.20 GiB available). Both runs were stopped, the idle workers
released, and the guard retained. This is progress on the walk, not a proof
of `binomialRowsNine`, and none of the three remaining original timeouts is
reported fixed here (`binomialRowsNine` is proved since, `docs/loops.md`).

Validation: the full library build passed 484 jobs, the imported TestSuite
passed 182 jobs, and the frozen SolKey check passed all 377 taclets and 131
read-bearing annotations. The transitive audit passed 245 headline theorems
using only the standard axioms. The source gate checked 512 sources and 202
inventoried sites with zero findings; both scanner tests and the static
TestSuite audit passed. The proof suggestion and replay are pinned at 128
steps. Per-file MCP diagnostics are clean for the implementation, integration,
regressions, suggestion pins and audit. The bounded non-quoting nine-row walk
measured 58 ms at 512 steps, 142 ms at 1024 and 4705 ms at 2048 (two leaves).

Both read-only reviewers confirmed the resource-bound repair and found no
remaining code issues. Their final documentation findings were repaired:
the twelve-squaring example now describes conservative refusal, and the new
example module has a module-map row. Reachability reports 499 modules and
the unchanged 25 baseline Scratch orphans; the prose-path check retains its
13 baseline missing references. `git diff --check` is clean. The serial
validation stayed below the RAM cutoff, including its larger TestSuite
worker; the guard remained active after releasing completed workers.

## M20: primitive struct-memory simulation and ownership

The new memory-struct foundation proves exact runtime-pointer field reads
and writes against the actual typed heap, with one word per member and no
array length header. Field offsets are bounded and distinct for distinct
present member names. `StructRepr.set` preserves the other primitive members;
`StructHeapRepr` keeps aliases on one base, distinct structs apart and local
cells below their regions. Cross-separation preserves arrays during struct
writes and structs during array writes, including their source heap values.
These theorems are generic in the primitive type and struct definition.

A new allocator relation is necessary before compiler integration. The
concrete `legacy_allocator` and `legacy_struct_repr` witnesses simultaneously
satisfy the array-only allocator and a zero-valued source struct located in
its unused tail. `legacy_write_breaks_allocator` proves a struct write breaks
that allocator's zero-tail assertion. `StructAllocatorRepr` adds ownership
of every live struct interval, plus both heap relations and cross-separation.
Its stack, local, struct and array writes preserve the cursor, zero tail,
layouts and ownership. `misplaced_invalid` rejects the old counterexample.

The positive allocator witness has two populated Boolean/unsigned structs,
an independent array, a reserved local and a nonempty evaluation stack.
It survives a struct write followed by an array write. Instruction checks
retain all other observed fields, array cells, cursor and local cells.
A second actual typed heap represents a negative signed field; its read
instantiates the general simulation. A wrapping base is proved invalid.
All 32 new public theorems are included in the transitive-axiom audit.

This is a compiler prerequisite, not claimed public compiler coverage.
`Compiler.compile` is unchanged. Source-pointer representation, allocation
preservation and the field/declaration clauses through the checked entry
remain required; the remaining-work table retains the struct gap.

The original nine-row investigation also narrowed the resource problem:
its two leaves have only 4415 and 4412 scoped syntax nodes, but both closer
reductions exceed a million tree nodes. Quoting the two leaves alone finished
in 6456 ms, pointing to subsequent replay work as the large-memory phase.
Combining prior memory-payload capture with the new rigid walk still left
both oversized reductions (22.2 seconds); additionally erasing heap writes
from fresh-identity skeletons and capturing locals did not resolve them
(49.1 seconds). These experiments were not integrated. The guard remained
active and no new cutoff occurred during these bounded experiments.

Validation: the full library build passed 488 jobs, the imported TestSuite
passed 182 jobs, and the frozen SolKey check passed all 377 taclets and 131
read-bearing annotations. The transitive audit passed 277 headline theorems
using only the standard axioms. The source gate checked 516 sources and 202
inventoried sites with zero findings; both scanner tests and the static
TestSuite audit passed. All four new modules have clean per-file error and
warning diagnostics. Reachability reports 503 modules and the unchanged 25
baseline Scratch orphans; the prose-path check retains its 13 baseline
missing references. `git diff --check` is clean.

The finder and skeptic reviewed the code and final documentation read-only;
neither found a remaining issue. Both confirmed the explicit boundary between
the proved struct foundation and pending public compiler integration. No RAM
cutoff occurred during this milestone's validation. Completed workers were
released, leaving 0.72 GiB owned Lean RSS with 28.11 GiB available; the
16 GiB process-budget / 8 GiB available-memory watchdog remained active.

## M21: mixed struct/array allocation ownership

The combined struct allocator now survives both kinds of typed heap growth.
Array allocation preserves every live struct field, identity base and
interval; the new array lies above the old structs. A headerless struct
allocator returns the old cursor and advances cell zero by its member count.
Its generic instruction theorem records the exact target run. The zero tail
represents the fresh object's actual primitive defaults, while every old
struct and array remains represented and separated. `StructRepr.keeps`
transports older primitive fields through typed heap growth. Capacity keeps
the new cursor strictly below the word modulus; empty structs consume zero
cells, whereas empty arrays still consume their header cell.

The inhabited mixed fixture allocates a three-element array after a populated
struct write, allocates a default struct and writes its Boolean field.
Separate continuations reuse an older source array reference and allocate an
empty Boolean array while preserving the newly written struct. An actual instruction
sequence pins the old stack, reserved local, all previous fields/elements,
array headers, new struct fields and final cursor. A negative boundary check
shows why merely fitting the last struct member is insufficient when the
next cursor would wrap to zero. All 13 new public implementation theorems and
five positive allocation witnesses enter the transitive audit.

These are allocator and typed-heap simulations, not source compiler coverage.
Reference-member pointer values and recursive source construction remain
outside the struct allocator relation. The public compiler is unchanged;
source pointer representation, declarations and field clauses remain due.

Validation: the full library build passed 489 jobs, the imported TestSuite
passed 182 jobs, and the frozen SolKey sort gate passed all 377 taclets and
131 read-bearing annotations. The transitive audit passed 295 headline
theorems using only the standard axioms. The source gate checked 517 sources
and 202 inventoried sites with zero findings; both scanner tests and the
static TestSuite audit passed. Per-file error and warning diagnostics are
clean for the new allocation module and expanded examples. Reachability
reports 504 modules and the unchanged 25 baseline Scratch orphans; the
prose-path check retains its 13 baseline missing references.

The finder and skeptic reviewed the implementation and documentation
read-only. No code issue remained; their documentation precision finding
was fixed by describing the old-reference write and empty-array allocation
as separate continuations. `git diff --check` is clean. The serial checks
did not trigger the RAM cutoff. Completed workers were released, leaving
0.72 GiB owned Lean RSS and 28.07 GiB available; the watchdog stayed active.

## M22: primitive struct fields through the public compiler

The existing memory compiler now accepts typed primitive struct-field reads
and writes, alias declarations and rebinding. This uses the same value and
statement certificates as arrays, with compositional checked RHS expressions.
`MemoryStructSource` proves their actual `Val.evalT` and `TRun.assignMem`
meanings, preserving the complete state and optional allocator on success
and agreeing on RHS reversion.

`StateRepr` now includes struct regions and array/struct cross-separation;
every memory-local pointer is represented at its actual reference type.
Local writes, array writes, primitive storage writes, alias declarations,
scopes, branch meets and captures retain these fields. `KeepsAllocator`,
`GrowsAllocator` and `AllocationInput` now use `StructAllocatorRepr`, so
array allocations through the existing public path also preserve live
struct ownership. The original array-only allocator remains a lower-level
relation; `AllocatorRepr.withoutStructs` supplies the inhabited bridge when
the typed heap contains no structs. This strengthens the memory compiler's
input relation; it does not add a separate struct compiler path.

The populated public fixture has two aliases to one struct, a distinct
struct and an array. Its program declares a scoped alias, combines field
and array reads in addition, writes both layouts, rebinds the temporary
alias to the distinct struct and reads through the older alias. Scope exit
retains all heap effects; a subsequent array allocation retains those
objects and their pointers. Concrete source/target observations pin the
values, stack, cursor and reserved cell. A second accepted program's field
RHS divides by zero and both runs revert. Both programs have actual public
input witnesses and kernel-checked public agreement theorems.

The larger computed compilation initially exceeded the default 200000
elaboration heartbeats while unification opened its input. Marking that
fixture's compiler-result constant irreducible prevents repeated unfolding;
kernel reduction still checks the computed result. No heartbeat override
or new trust escape was added. Alias-cost extraction now examines the RHS
before its reference type, so the zero cost of a generic alias computes
without splitting the unknown type.

Struct source construction/allocation, reference-member values, copies,
deletion and compound/increment field updates remain due. The lower-level
headerless allocation proof does not yet establish their source clauses.

Validation: the final full library build passed 490 jobs, the imported
TestSuite passed 182 jobs, and the frozen SolKey gate passed all 377 taclets
and 131 read-bearing annotations. The transitive audit passed 307 headline
theorems using only the standard axioms. The source gate checked 518 sources
and 202 inventoried sites with zero findings; both scanner tests and the
static TestSuite audit passed. Per-file diagnostics are clean for the
strengthened state/allocator plumbing, field simulation, compiler and public
witnesses. The field implementation and compiler have clean warning checks.
Reachability reports 505 modules and the unchanged 25 baseline Scratch
orphans; the prose-path check retains its 13 baseline missing references.

Both read-only reviewers found no code defect. Their confirmed documentation
findings were repaired: module introductions now describe the generic memory
and public field scope, and the compiler exclusions name only unsupported
struct operations. They also verified the final Boolean witness now flips
the field from true to false and observes the change on both sides.
`git diff --check` is clean. Serial validation did not trigger the RAM guard;
completed workers were released, leaving 0.73 GiB owned Lean RSS and
28.33 GiB available with the watchdog active.

## M23: source constructors and primitive struct allocation

The public compiler now accepts default allocation for structs whose members
are all primitive. `MemoryStructDefault` identifies the actual source
default-copy fold with one fresh typed object, proves its primitive defaults,
and connects `TRun.declMem` to the target allocation and local pointer store.
The shared state, older identity bases, mixed heap regions, zero tail and
stack survive the operation. The ordinary source elaborator's positional
and named literals build on this clause and subsequent field writes, so
constructor declarations and allocating rebinding compile through the same
public entry. Structs with reference members are explicitly refused here.

Source struct allocation reserves `max 1 memberCount` cells. The model can
admit an encoded name whose rejected definition has no fields; giving its
allocation zero cost would bypass `AllocationInput`'s allocator requirement.
The new `advance`/`reserveStruct` lemmas prove the harmless tail reservation
while preserving every live object. A model-only empty encoded-layout
fixture reserves one cell and has an inhabited public input/agreement proof.
The ordinary source elaborator refuses that fixture's duplicate-member name.

The ordinary `sol{…}` fixture declares positional and named records with
Boolean, unsigned and negative signed values, retains an old alias through
literal rebinding, and writes/allocates a primitive array between structs.
Its source and target observations pin all three struct objects, array data,
signed words, stack, reserved cell and exact twelve-cell cursor growth.
An insufficient-capacity input is refuted, and base-zero allocation is refused.
A constructor field RHS dividing by zero is observed after the elaborator's
three-cell object allocation; an earlier `require(false)` reaches no later
allocation and has a public input even with an unusable zero cursor.

The implementation and public input/agreement theorems are included in the
transitive audit. Exact allocation-cost regressions are kernel-checked
examples. No dependency, heartbeat override or new trusted implementation/
recovery site was added.

Validation: the full library build passed 492 jobs, the imported TestSuite
passed 182 jobs, and the frozen SolKey check passed all 377 taclets and
131 read-bearing annotations. The transitive audit passed 325 headline
theorems using only the standard axioms. The source gate checked 520 sources
and 202 inventoried sites with zero findings; both scanner tests and the
static TestSuite audit passed. Per-file error and warning diagnostics are
clean for the allocation/default implementation, compiler and new source
witnesses; older array, alias and field regressions remain clean.

The read-only finder and skeptic found no code defect. The documentation
review's allocation-cost clarifications were applied: the general description
includes array elements and struct member/padding reservations, and audit
wording distinguishes named audited theorems from kernel-checked examples. Reachability
reports 507 modules and the unchanged 25 baseline Scratch orphans; the prose
path check retains its 13 baseline missing references. `git diff --check` is
clean. The serial validation did not trigger the RAM cutoff; releasing its
completed workers left 0.73 GiB owned Lean RSS and 28.20 GiB available with
the watchdog active.

## M24: primitive field deletion, compound updates and captured bumps

The public memory path now compiles primitive field deletion, all numeric
compound operators and standalone/captured prefix/postfix field increments
and decrements. Three source equalities extend the existing memory helpers
to fields and retain complete typed results, including errors. The new
certificates reuse the existing checked value, field-write and stack-capture
proofs, preserving aliases, independent objects, frame cells and allocator
ownership. These operations have zero allocation cost; deleting a field
writes its default into the same object.

The ordinary-source fixture exercises `+=`, `-=`, `*=`, `/=` and `%=` at
both numeric types, all four unsigned standalone/captured bump forms, signed
captures, aliases, a distinct struct and an array. Its guards pin the saved
prefix/postfix values separately; source/target observations retain the
independent object's values and the array data. Boolean, unsigned and signed
fields are changed from nondefault values by deletion. Seven accepted
failure programs have inhabited public inputs and source/target reversion
checks: unsigned/signed upper/lower boundaries, division/modulo by zero and
signed minimum divided by minus one. The implementation equalities and
named public input/agreement/reversion theorems enter the transitive audit.

Whole-struct deletion, copies, reference-valued members/elements and loops
remain outside these clauses. No dependency, heartbeat override or trusted
implementation/recovery site was added.

Validation: the full library build passed 492 jobs, the imported TestSuite
passed 182 jobs, and the frozen SolKey check passed all 377 taclets and
131 read-bearing annotations. The transitive audit passed 333 headline
theorems with only the standard axioms. The source gate checked 520 sources
and 202 inventoried sites with zero findings; both scanner tests and the
static TestSuite audit passed. All edited implementation and example files
have clean error and warning diagnostics, and the older expression and
allocation source regressions remain clean.

The required read-only finder and skeptic found no code or documentation
defect. Reachability remains 507 modules with the same 25 baseline Scratch
orphans; the prose path check retains its 13 baseline missing references.
`git diff --check` is clean. The serial build did not trigger the RAM guard;
afterward the audit worker and server used 2.47 GiB with 27.92 GiB available.

## M25: allocating deletion of primitive-member struct locals

Whole-local struct deletion now compiles through the public checked entry.
Its source theorem follows `TRun.deleteMem`: allocate a fresh default object,
weaken older locals to the grown heap and rebind only the destination. Its
target allocates the same positive member/padding reservation and stores the
fresh pointer. The complete state relation, old reference addresses, mixed
heap separation, allocator cursor, reserved cells and evaluation stack survive.
Primitive field deletion remains a write into the existing object.

The ordinary-source fixture deletes repeatedly, retains earlier aliases,
deletes a scoped alias and a selected conditional branch,
and keeps an independent populated struct and array. Named source/target
observations pin each fresh identity's contents, the older objects, signed
values, stack and reserved cell. The exact reached reservation is twenty
cells. Public input/agreement witnesses are inhabited; insufficient capacity
is refuted and frame base zero is refused. An earlier revert charges the
three-cell constructor but none of the later deletion. Its input/agreement
and exact cost are checked separately. The new implementation and named
witness theorems enter the transitive audit. Reference-valued members and
whole-struct copies remain outside this clause.

Validation: the full library build passed 492 jobs, the imported TestSuite
passed 182 jobs, and the frozen SolKey check passed all 377 taclets and
131 read-bearing annotations. The transitive audit passed 344 headline
theorems with only the standard axioms. The source gate checked 520 sources
and 202 inventoried sites with zero findings. All three edited implementation/
example files have clean error and warning diagnostics; `git diff --check`
is clean.

The required read-only finder and skeptic found no code defect. Their final
documentation review caught an overstated alias-write claim; the corrected
text describes retention and reads of earlier aliases. Coverage is explicitly
the selected conditional branch. The serial build did not trigger the RAM
cutoff; after releasing its workers the server used 0.74 GiB with 26.92 GiB
available. Module reachability and prose paths retain the same baseline
Scratch orphans and missing vendor references recorded at M24.

## M26: default primitive-array declarations

The public memory compiler now accepts `uint[] memory xs;` and its signed
and Boolean counterparts. The complete typed source result is definitionally
that of allocating `new T[](0)`, so a small certificate wrapper reuses the
existing proof. Allocation recognition and reached cost charge one header
cell; the allocator, strict capacity bound and nonzero frame base are still
required for every reached declaration.

An inhabited ordinary-source program checks all three element types, retains
an old alias after allocating rebinding, deletes another local and combines
a populated struct, a scoped empty array and a selected conditional branch.
Named source/target observations pin object identities and contents, the
stack/reserved cell and the exact fourteen-cell cursor advance. Insufficient
capacity is refuted and frame base zero is refused. A separate prior-revert
program has zero allocation cost and a valid public input with an unusable
zero cursor; its source/target reversion is checked. Implementation and named
witness theorems enter the transitive audit. Fixed-array defaults and
reference-element arrays remain outside this clause.

Validation: the full library build passed 492 jobs, the imported TestSuite
passed 182 jobs, and the frozen SolKey check passed all 377 taclets and
131 read-bearing annotations. The transitive audit passed 354 headline
theorems with only the standard axioms. The source gate checked 520 sources
and 202 inventoried sites with zero findings. Edited implementation/example
files have clean error and warning diagnostics; `git diff --check` is clean.

The required read-only finder and skeptic found no code or documentation
defect. The serial build did not trigger the RAM guard; releasing its workers
left 0.74 GiB owned Lean RSS and 27.17 GiB available. Module reachability and
prose paths retain the same baseline Scratch orphans and missing vendor
references recorded at M24.

## M27: typed reference-field paths through existing memory objects

The source/target state relation now also records every reference-valued
struct member's actual child identity and target pointer word. This separate
`RefFieldsRepr` is preserved through local operations, scope exit, storage and
primitive memory writes, stack capture and primitive allocations. Growing
heaps retain both parent and child addresses. Existing fixtures now supply
this stronger premise; it is explicit in the public compiler input.

A typed pointer certificate follows initialized locals and reference-valued
struct fields. The checked compiler uses it for nested primitive-field reads,
primitive-array reads/lengths and child alias declarations/rebinding. Writes
through those aliases use the existing local-receiver clauses. Its recursive
compiler keeps the full endpoint type variable to permit structural recursion:
the initial restricted version ran at runtime but could not reduce in kernel
acceptance checks. The structural version passes those checks without trusting
native evaluation.

The new typed `Prog` fixture supplies populated wrapper, holder, leaf and
array objects, concrete pointer words, separated intervals and an allocator.
It follows two field pointers, writes through child aliases, changes a scoped
primitive member and allocates a later array and primitive struct. Public
input/agreement and source/target observations pin actual source identities,
old object contents, retained pointer words, stack/reserved cells and the
four-cell reservation. A false pointer word is refuted, and a nested
out-of-bounds array read reverts on both sides with inhabited public input.
These are typed-program regressions. Reference-bearing source construction,
reference-element paths, direct nested writes and reference-member mutation
remain outside the new clauses. All named implementation/witness theorems
enter the transitive audit.

Validation: the full library build passed 495 jobs, the imported TestSuite
passed 182 jobs, and the frozen SolKey check passed all 377 taclets and
131 read-bearing annotations. The transitive audit passed 383 headline
theorems with only the standard axioms. The source gate checked 523 sources
and 202 inventoried sites with zero findings; both scanner tests and the
static TestSuite audit passed. Per-file error and warning checks are clean
for the changed implementation and the new populated path fixture; existing
array/allocation/expression and struct fixtures also pass their error checks.

The required read-only finder and skeptic found no code or documentation
defect. Reachability reports 510 modules and the same 25 baseline Scratch
orphans; prose paths retain the same 13 baseline vendor references.
`git diff --check` is clean. Serial validation did not trigger the RAM guard;
the audit worker and server used 2.46 GiB with 27.73 GiB available afterward.

## M28: direct primitive updates through reference-field paths

The public checked compiler now writes primitive struct fields and primitive
array elements directly through the typed paths introduced at M27. The two
write lemmas preserve the complete source result, evaluate the RHS first and
retain arbitrary stack contents, pointer words, mixed heap separation and an
available allocator. Three small certificates connect these writes and
primitive deletion; existing compound/increment source equalities provide
all five numeric operators and standalone prefix/postfix increments/decrements.

The typed `PathExamples.Direct` fixture exercises all five operators and all
four standalone bump forms at a nested unsigned field and array element,
nondefault unsigned/Boolean field deletion and element deletion. A later
array allocation retains those changes and the old pointer words. Inhabited
public input/agreement and named source/target observations pin two-cell
cursor growth, child values and reserved stack/frame cells. Three accepted
failure programs have inhabited inputs and source/target reversion checks:
nested out-of-bounds assignment, unsigned maximum pre-increment and a
zero-divisor RHS. Implementation and named witness theorems enter the audit.

Captured direct nested bumps do not form a new typed case: `assignIncDec`
requires a simple receiver. The existing elaborator captures the receiver
into an alias, whose compiler path remains supported. Reference-valued member
mutation/deletion, recursive construction and reference-element array paths
remain outside these clauses. No dependency, heartbeat override or new
trusted implementation/recovery site was added.

Validation: the full library build passed 495 jobs, the imported TestSuite
passed 182 jobs, and the frozen SolKey check passed all 377 taclets and
131 read-bearing annotations. The transitive audit passed 394 headline
theorems with only the standard axioms. The source gate checked 523 sources
and 202 inventoried sites with zero findings. All three edited implementation/
example files have clean error and warning diagnostics; `git diff --check`
is clean. Module reachability and prose paths retain the baseline results
recorded at M27.

The required read-only finder and skeptic found no code or documentation
defect. Their check also confirmed the elaborator's receiver capture, keeping
that behavior distinct from the typed fixture's standalone nested bumps.
Serial validation did not trigger the RAM guard; the audit worker and server
used 2.47 GiB with 28.04 GiB available afterward.

## M29: assigning existing references to struct members

The checked compiler now accepts reference-valued struct-field assignment
from a certified typed pointer path. The source and target evaluate the RHS
before the parent path, then update the actual child identity and its one
pointer word. No object is copied or allocated by the assignment. New local
and global preservation lemmas retain primitive values, independent arrays,
other pointer words, interval separation, frame/stack cells and an available
allocator. The result keeps the full strengthened state relation.

The typed `PathExamples.ReferenceWrite` fixture redirects struct and array
members to fresh populated children and writes through their updated paths.
It self-assigns a nested pointer, restores the earlier links and checks older
aliases and fresh child contents separately. A later allocation retains these
relationships. Named source/target observations pin the final source child
identities, old/fresh data, target pointer words, reserved cells and exact
six-cell growth; the public input and agreement are inhabited. Implementation
and named witness theorems enter the transitive audit. Reference-member
deletion, recursive reference-bearing construction, copies and reference-
element array paths remain outside the new clause.

Validation: the full library build passed 496 jobs, the imported TestSuite
passed 182 jobs, and the frozen SolKey check passed all 377 taclets and
131 read-bearing annotations. The transitive audit passed 410 headline
theorems with only the standard axioms. The source gate checked 524 sources
and 202 inventoried sites with zero findings. All three edited implementation/
example files have clean error and warning diagnostics. Reachability reports
511 modules and the same 25 baseline Scratch orphans; prose paths retain the
same 13 baseline vendor references. `git diff --check` is clean.

The required read-only finder and skeptic found no code defect. The final
docs review caught one stale reference-member mutation exclusion in the M28
paragraph. The attempted replacement missed its target; M30 corrected the
exact sentence to mark that historical boundary and name its later extensions.
Serial validation did not trigger
the RAM guard; the audit worker and server used 2.48 GiB with 28.05 GiB
available afterward.

## M30: fresh defaults for reference-valued struct members

Deleting a reference-valued struct member now compiles when its child is a
primitive array or a struct with only primitive members. Source equalities
identify the actual `clearT` allocation, weakened parent and fresh child
store. The target saves the resolved parent before allocation and restores
the pointer order for its member store. Full source/target state, old address
maps, mixed ownership, stack and allocator/cursor results are retained. Cost
charges a header or positive member/padding reservation only after the parent
path succeeds; compilation requires a nonzero frame base.

The typed `ReferenceDelete` fixture repeatedly deletes both kinds of child,
retains older aliases and earlier fresh children, deletes again within a
scope, writes through an older array alias and allocates a later Boolean
array. Inhabited public input/agreement and named source/target observations
pin all relevant identities, default/changed contents, pointer words,
reserved cells and eleven-cell growth. Insufficient capacity is refuted and
frame base zero is refused. An unset parent reverts at zero cost and fails
the public pointer premise. A separate earlier-revert program has zero cost
and valid public agreement even with an unusable zero cursor. New
implementation and named witness theorems enter the transitive audit.

Reference-bearing struct defaults, fixed/reference-element child arrays,
copies and their broader paths remain outside these clauses. No dependency,
heartbeat override or new trusted implementation/recovery site was added.

Validation: the full library build passed 497 jobs, the imported TestSuite
passed 182 jobs, and the frozen SolKey check passed all 377 taclets and
131 read-bearing annotations. The transitive audit passed 429 headline
theorems with only the standard axioms. The source gate checked 525 sources
and 202 inventoried sites with zero findings. All three edited implementation/
example files have clean error and warning diagnostics. Reachability reports
512 modules with the same 25 baseline Scratch orphans; prose paths retain the
same 13 baseline vendor references. `git diff --check` is clean.

The required read-only finder and skeptic found no code defect. Their final
docs check caught the still-stale M28 reference-member exclusion: an earlier
text replacement had not matched. The exact sentence now marks the M28
boundary and names the M29/M30 extensions. Serial validation did not trigger
the RAM guard; the audit worker and server used 2.47 GiB with 27.87 GiB
available afterward.

## M31: populated storage-root struct copies

The checked public compiler now accepts storage-to-memory declarations and
allocating rebinding for structs whose members are primitive. Copies read
each member at its actual Solidity type, then reserve and initialize one
fresh object. Exact source equations retain arbitrary unsigned, Boolean and
signed values. The populated-reservation theorem preserves older arrays,
structs, pointer words, frame cells, stack, cross-separation and allocator
ownership; its fresh-object premise concerns the actual copied payload.

The ordinary Solidity fixture changes storage before and after its first
copy, retains an old alias across allocating rebinding, changes independent
copies, creates a scoped copy, deletes a copied local and allocates another
array. Named source/target observations pin all seven objects, signed values,
unchanged storage, reserved stack/frame cells and exact twenty-cell growth.
The public input/agreement is inhabited. The actual compiler input rejects
insufficient capacity and compilation refuses a zero frame base. A prior
revert skips the copy with zero cost and inhabited input even at a zero
allocator cursor.

This clause copies storage roots only. Other storage paths, recursive
reference-bearing copies, memory-to-storage copies and runtime-length array
copies still require separate clauses. The source-copy, emitted-load/store,
populated-allocation, simulation and named witness theorems enter the
transitive audit. No dependency, heartbeat override or new trusted site was
introduced.

Validation: the full library build passed 502 jobs, the imported TestSuite
passed 182 jobs, and the frozen SolKey check passed all 377 taclets and
131 read-bearing annotations. The transitive audit passed 461 headline
theorems with only the standard axioms. The source gate checked 530 sources
and 202 inventoried sites with zero findings; both scanner tests and the
static TestSuite audit passed. All edited implementation/example files have
clean error and warning diagnostics. Reachability reports 517 modules with
the same 25 baseline Scratch orphans; prose paths retain the same 13 baseline
vendor references. `git diff --check` is clean.

The required read-only finder and skeptic found no code defect. Their final
docs check caught a broad unsupported-copy exclusion, now narrowed to copy
forms outside this clause. The load/store proof also rejected an initial
`DUP1` draft; the initializer uses `DUP2` to retain its base beneath the
current value. Serial validation did not trigger the RAM guard; the audit
worker and server used 2.47 GiB with 27.98 GiB available afterward.

## Remaining requested work

| Area | Required implementation and evidence still due |
|---|---|
| Memory compiler extension | The core path now also compiles loops (`Instr.loop`, `loop_sim`: a body that pushes, pays and shrinks nothing; divergence is the machine's fault, a fourth case of `compile_correct`). The checked public entry covers primitive-array reads/writes/deletion, compound local/array/field updates and standalone/captured bumps, lengths, local/default declarations, typed aliases, checked expressions, require/revert, primitive storage writes, allocating array declarations/rebinding, scopes and branches. M22 adds primitive struct-field reads/writes and aliases with shared ownership; M23 adds primitive-member struct defaults/constructors and allocating literal rebinding; M24 adds primitive field deletion and numeric compound/increment operations; M25 adds allocating whole-local primitive-member struct deletion; M26 adds default primitive-array declarations; M27 adds typed paths through existing reference-valued struct fields for nested primitive reads/lengths and child aliases; M28 adds direct primitive writes, deletion, compound updates and standalone bumps through those paths; M29 adds reference-valued member assignment from existing typed paths; M30 adds member deletion to fresh primitive arrays/primitive-member structs; M31 adds populated primitive-member storage-root copies and allocating rebinding. Other storage paths and copies, reference-bearing construction, other default child layouts, reference-element paths, loops and remaining mixed operations still need extension. The original `inFrag` remains the core-path predicate; the unified result carries the selected fragment's certificate and simulation requirements. |
| Loop automation | Two original `SolcLoopsOpen` timeouts remain: `multiArrayFillByPushLoops`, and `pushNoArgs2dLoop` under clean tails. `binomialFaithfulRowsSmall` proves within the default budget; `binomialRowsNine` proves with identities named by their allocations and the walk checked in chunks (`sol_prove (chunk := 128)`, about four minutes; `docs/loops.md`), through the runner too, which checks a walk past 1024 steps in chunks (it needs `--timeout-ms` past the default 300 s). Support sound invariant use/inference where missing; keep missing invariants distinct from false specifications. |
| Quantifier instantiation | Later numeric locals and anonymised invariant-loop counters are now supported by the bounded closer fallback. Ordinary ABI memory-array reads and lengths now normalize through local updates, with signed/unsigned invariant-loop regressions. Broaden remaining ground terms and larger loops only with bounded, checked instances. |
| Arithmetic | Symbolic/coefficient multiplication order and compound/difference squares are implemented with bounded checked instances. Broader operators and nonlinear decision coverage remain outside the exact verifier's characterized fragment. |
| Revert semantics | M14 adds precise computed/raw memory operands and execution certificates, with pinned raw-rethrow source checks. A self-call's callee now fails with solc's `Panic` data for overflow (`0x11`, inside or outside `checked`), division by zero (`0x12`), empty `pop()` (`0x31`) and indices (`0x32`) (`Prog.withPanics`). Exact symbolic catch relationships, literal data outside self-call frames and broader Solidity error/panic-code alignment remain required. The arbitrary-byte catch fallback is not the requested proof precision. |
| Exact verification | Expand and characterize the supported fragment, including interior quantifiers and broader arithmetic; general unbounded reachability cannot be made a total decision procedure. Unsupported cases must remain explicit. |

## Resource control during this work

A host guard monitors this chat's Lean descendants. It terminates those
processes when their combined reported RSS exceeds 16 GiB or system available
RAM falls below 8 GiB. The first broad dependency rebuild triggered the guard
at about 33 GiB summed RSS while 26 GiB remained available; checks were stopped
and resumed individually after rearming it. A later module's dependency
rebuild hit the 16 GiB process budget and was also stopped. A scratch measurement with
`LEAN_NUM_THREADS=1` reduced parallelism (four one-second checks took about six
seconds), but a later full build still reached 16.08 GiB combined RSS while
19.73 GiB remained available. The guard terminated it. Remaining modules are
requested individually with that setting and a rearmed guard. Summed RSS includes shared pages
and is a conservative process-budget measure. The guard lives in `/tmp` and
is operational protection for this session, not a permanent CI service.

