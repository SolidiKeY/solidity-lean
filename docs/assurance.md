# Assurance: trust gates, the certified memory compiler, closer extensions

The [full compiler roadmap](coverage-plan.md) requires these trust gates across
the completed source-to-executable-EVM proof closure. The compiler fragments and
premises recorded here describe existing results, not full-profile compiler
correctness. Named proof gaps cannot satisfy the roadmap's completion gate.

The work requested by the October 2026 audit: trust gates, the memory path
of the checked compiler, and bounded closer extensions.  Milestone labels
M1–M31 are cited elsewhere (e.g. M13 in `docs/semantic-gaps.md`).  The
core stays dependency-free.

## M1 · Trust gates and non-vacuity

* **Source gate**: `bash scripts/check-trust.sh` scans every Lean source
  (corpus, TestSuite, root modules, vendored LeanTeX) and rejects `sorry`,
  bare `admit`, native proof reduction and explicit axioms.  Comments and
  string text are blanked; ordinary, interpolated and literal-text views are
  combined conservatively.  It is a lint, not a Lean parser.  Tests:
  `node scripts/check-trust.test.mjs`.
* **Inventory**: `tests/trust-inventory.json` records every
  `implemented_by`, unsafe, opaque, error-recovery and kernel-option site
  by file, code and count; a changed or added site fails the gate.  It
  makes the boundary reviewable; it does not prove a compiled override
  implements its definition.  Known: the opaque cryptographic primitive is
  a model assumption, recursive thunk elaboration uses unsafe code, and
  error-recovery tactics can introduce a synthetic `sorry` while reporting
  an error.  None may reach an audited theorem.
* **Axiom gate**: `lake env lean --tstack=131072 TrustAudit.lean` follows
  the transitive axioms of the headline theorems (correctness, callbacks,
  symbolic execution, compilation, non-vacuity); anything but `propext`,
  `Classical.choice`, `Quot.sound` fails elaboration.  New public theorems
  are added to it.  CI runs both gates after the whole-library build.
* Parser assertions are `#guard` checks, not `native_decide` proofs; parser
  correctness is not proved.
* **Non-vacuity**: `Examples/Tactics/Nonvacuity.lean` proves the result of
  `uint x = 7;` and refutes `x = 8` at an actual typed initial state; the
  false specification's translation has no derivation, and the run returns
  normally, so revert and exhaustion explain neither witness.

## The memory path of the checked compiler (M2–M4, M8–M12, M15–M18, M20–M31)

`Compiler.compile` (`Evm/Compiler.lean`) is the single checked entry: the
core compiler where `Evm.inFrag` applies, otherwise the memory compiler
(`Memory.compileProg`, `Evm/MemoryCompile.lean`).  The result keeps code and
fragment certificate together; `Main.compiler_checked` restates the public
agreement theorem (core state and stack on the core path; the full
heap/pointer relation on the memory path).

**Representation invariants** (each a premise of the public input):

* An array's length cell precedes its elements; one base per heap identity
  (`Evm/MemoryHeap.lean`), so aliases share a base and distinct objects have
  disjoint intervals above the reserved local frame.  Structs are one word
  per member, no header (`StructRepr`, `StructHeapRepr`); arrays and structs
  are cross-separated.
* Every memory local is initialized (unset declarations are not admitted).
  `RefFieldsRepr` records each reference-valued struct member's child
  identity and pointer word.
* Allocation is a bump allocator (`Evm/MemoryAlloc.lean`):
  `StructAllocatorRepr` owns every live interval below the cursor, a zeroed
  free tail represents the fresh object's defaults, and capacity is a
  theorem premise (the generated code has no runtime capacity check): each
  single-allocation lemma needs `cursor + size + 1 < 2^256`
  (`Evm/MemoryAlloc.lean`), and the public input `AllocationInput`
  (`Evm/MemoryGrowResult.lean`) states `cursor + cost < 2^256` over the cost
  a run reaches (`cost = 0` needs no capacity).  Allocation needs frame
  base `0 < b` (cell zero is otherwise a local); non-allocating programs may
  use base zero.
* The frame bound is the peak context anywhere in the program
  (`frameNeedProg`), not the final one: temporaries of either branch would
  otherwise overwrite heap cells.
* Allocation cost is computed from the typed source and the reached
  execution prefix, not the erased certificate: each reached allocation
  costs its length plus a header (arrays) or `max 1 memberCount` cells
  (structs; zero would bypass the allocator requirement); unreachable
  suffixes after a revert cost nothing, and the cost skips interpretation
  when a suffix has no allocation (proved equal).

**Admitted** (each with inhabited public input/agreement witnesses, exact
source and target reversion, and its theorems in the axiom gate):

| M | What compiles |
|---|---|
| M2 | primitive-array reads and writes through typed pointer locals, source operand order |
| M3 | lengths, primitive declarations and defaults, local assignment, alias declaration and rebinding, nested reads in indices and RHS |
| M4 | checked operators and short-circuit Booleans over memory operands, primitive storage writes, `require`, `revert` |
| M8–M11 | `new T[](n)` declarations and allocating rebinding of primitive arrays |
| M12 | scoped blocks and statement-level `if` (only the selected branch costs) |
| M15 | `delete xs[i]` (a default write) and `delete xs` (rebinding to a fresh empty array) |
| M16–M18 | the five compound operators, standalone and captured `++`/`--` on elements and locals (`i = xs[i]++` uses the old index) |
| M20–M22 | primitive struct fields: reads, writes, aliases, mixed struct/array ownership |
| M23 | primitive-member struct defaults and constructors, allocating literal rebinding |
| M24–M25 | field deletion, compound updates and bumps on fields; whole-local struct deletion (allocating) |
| M26 | `T[] memory xs;` defaults |
| M27–M28 | typed paths through reference-valued struct fields: nested reads, lengths, child aliases, direct primitive writes, deletion, compound updates |
| M29 | assigning an existing reference to a struct member (RHS before the parent path; no copy) |
| M30 | deleting a reference-valued member to a fresh primitive array or primitive-member struct |
| M31 | storage-root to memory copies of primitive-member structs, declarations and allocating rebinding |

**Rules learned.**  Open the public premises with `Compilation.memory_input`
instead of normalizing the whole compiler result (that ran past the
heartbeats and once past 16 GiB RSS); mark a large computed compiler-result
constant `irreducible` in a fixture (the kernel still checks it); split a
large target-observation certificate into smaller programs rather than
raising budgets; a recursive compiler the kernel must reduce keeps its
endpoint type variable for structural recursion (M27).

## Closer extensions

* **M5 · Quantified premises at later counters** (`Calculus/CloseAll.lean`):
  bounded `allLeft` after the closer opens its binders, so a later local or
  anonymised loop counter instantiates a premise stated before it existed;
  no term enters an older scope.  Each normalization, candidate, guard and
  replay step has heartbeat recovery and rollback; `sol_close_all?` prints
  the applications.  It does not infer invariants.
* **M6 · Nonlinear bounds** (`Calculus/CloseNonlin.lean`): solkey's
  `multiply_inEq0`, `multiply_2_inEq0`, `square_nonneg`,
  `add_non_neg_square`.  Budgets: 256 declarations, 8 192 expression nodes,
  16 products examined; at most four atoms, eight factors, twelve
  comparisons, 128 facts; target products seed the search first.
  `sol_close_nonlin?` prints the proof.  Checked instances, not a decision
  procedure.
* **M7 · Quantified ABI memory scans**: `CloseScoped` rewrites memory reads
  and lengths through local pushes and counter assignments of input arrays;
  the final constructor pass visits at most 128 constructors at 1 000
  heartbeats each; arithmetic is tried before reflexivity.  Fixtures
  `tests/solc/ArrayScans.sol` (invariants supplied); the two-assert signed
  diamond proves by `sol_symex; sol_close`, while its `sol_prove` walk still
  exceeds the declaration budget.
* **M13 · Demanded memory reads in loop proofs**: the scoped reducer applies
  the memory taclets when a read, length or identity read is formed, before
  later writes duplicate it (`foldMem2`, bounded by `normalizationSize`,
  kept only if no larger; `foldMem2_eval` keeps failed writes' guards).
  `binomialFaithfulRowsSmall` (`tests/solc/OpenLoops.sol`,
  `Examples/Tactics/OpenLoops.lean`) proves in about 7 s with no invariant
  or heartbeat override.
* **M19 · Bounded rigid branch pruning** (`Calculus/Rigid.lean`):
  literal-local branch conditions substituted backward through their
  updates (`Hyps.rigid`, `Hyps.rigid_lift`); `Seq.refuteLanded_sound` uses
  the surviving sibling's derivation.  Each substitution is checked against
  a 512-node cap first (repeated `x := x + x` would expand); a refused
  projection keeps both branches.

## M14 · Computed memory revert operands

`RevPart.mem` carries a typed memory local: reason operands use the
`Error(string)` encoding, raw operands return the buffer, an empty raw
buffer the empty revert (`Semantics/RevertMemory.lean`).  Computed
`revert(reason)` and `require(c, reason)` lower to it (require captures the
condition first and evaluates the reason even on success).  The solc
importer recognizes only the whole-buffer rethrow
`revert(add(data, 32), mload(data))` on a byte buffer; a bytes local is not
accepted as a string reason.  Open: `RevPart.pat?` returns `none` for
computed operands, so catch reasoning falls back to an arbitrary-byte
allocation (`catchDataBox`), not the exact callee-memory relation.

## Remaining requested work

| Area | Still due |
|---|---|
| Memory compiler | Other storage paths and copies (memory-to-storage, runtime-length arrays, reference-bearing structs), reference-bearing construction and defaults, fixed and reference-element arrays and paths, loops on the memory path, remaining mixed operations. The core path compiles loops (`Instr.loop`, `loop_sim`). |
| Loop automation | Two `SolcLoopsOpen` functions (`docs/semantic-gaps.md`, `docs/loops.md`). Support sound invariant use where missing; keep a missing invariant distinct from a false specification. |
| Quantifier instantiation | Broaden ground terms and larger loops only with bounded, checked instances. |
| Arithmetic | Broader nonlinear coverage stays outside the exact verifier's fragment (`docs/automation.md`, M6 decisions). |
| Revert semantics | Exact symbolic catch relationships; literal data outside self-call frames; broader panic-code alignment (self-calls already fail with solc's `Panic` codes, `Prog.withPanics`). |
| Exact verification | `docs/automation.md`, M7 "What is not proved". |
