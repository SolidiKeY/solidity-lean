# G25 scalar opcode lowering: preparation lane

This lane owns only `Solidity/Backend/Scalar/` and this document. It preserves
the [approved scope](../solidity-scope.md) and existing intrinsic syntax,
semantics, refusals, observations, target predicates and proof budgets. No
other worker's files, the global coverage ledger or manifest statuses change.
The frozen component queue is complete at P2. Full G25 source-to-bytecode
preservation remains a parent integration obligation; it is not claimed here.

## Base, runtime and gap

- Repository: `/workspace/scalar-lowering`; branch
  `codex/solidity-independent5-20261029/scalar-lowering`.
- Exact base: `50658f41061b366d6e503d1e8a3a324a281e9fca`.
  The original `/workspace/solidity-lean` checkout is preserved on `work`.
- The initial compact continuation lacked the full assignment and published
  base. The full assignment was subsequently supplied; fetching origin recovered
  the exact base, and an isolated worktree was created without resetting work.
- Direct systemd and delegated-cgroup probes fail. An independent skeptic found
  the existing managed Docker route; the earlier blanket runtime blocker was
  incorrect. Docker now enforces memory.max=12884901888 and memory.swap.max=0.
  Host RAM/cgroup: 16 GiB limit, no active swap. No second 12 GiB reserve inside
  this VM is imposed. Checks hold the repository writer lock and are serial.
- Actual Lean: 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b.
  Lake: 5.0.0-src+797c613. `lake build Solidity.KeySort` passed (2 jobs),
  including a rerun using private weakLeanArgs with explicit `-j1` and
  LEAN_NUM_THREADS=1. RUNTIME_GATE_PASS applies only to this runtime probe.
- Source inspection confirms the [R10/R37 gaps](roadmap-g04-restrictions.md):
  modular values are refused by Evm.valIn, and its machine erases failure bytes.
  A nontrivial boundary control gives uint8 unchecked 255+1=0, whereas bare
  256-bit ADD gives 256. The kernel controls now pin that discrepancy and actual
  width cleanup. Source integer arithmetic rejects a zero divisor while raw
  EVM DIV returns zero. Inspection/arithmetic controls are distinct from proofs.

## Contracts and proof boundary

[Backend Opcode](../../Solidity/Backend/Opcode.lean) remains the instruction
language. Slice defines independent top-first numeric semantics over its actual
Instr and Program, using 256-bit words. Push immediates are read big-endian;
committed assembler byte-conversion lemmas are reused read-only. SUB and EXP
have their left/base operand on top; shifts have their count on top. Signed
division/remainder use truncation toward zero, SAR uses floor division/sign
fill, and SIGNEXTEND takes a byte index. Modular intermediates do not wrap.

The slice excludes gas, stack-capacity failure and unsupported instructions.
A future caller must establish enough EVM capacity/resources for every prefix.
`none` means outside this local slice or underflow, not a claimed EVM failure
observation. `run_append`, `run_comp`, `step_frame` and `run_frame` establish
composition and successful untouched-tail preservation for every admitted
instruction, including DUP. They do not establish fetched-bytecode execution.

Typed.encodeValue maps existing PrimTy.Denote values to their word bits;
ValueRel is exact word equality to that encoding. UnaryCertificate and
BinaryCertificate quantify over all existing intrinsic operands and every
stack tail, and compare run directly with the original operation's evalT.
No source semantics is defined by compilation. Boolean operation certificates
apply to already evaluated canonical operands; they do not authorize eager
source short-circuit evaluation.

Guards.guarded is an explicit component interface: a real test Program leaves
a failure flag above retained operands, then the boundary selects a real body
Program or existing Semantics.encodePanic bytes. It is not a proof that generic
branch/payload bytecode has been emitted. Modular correctness includes the
zero-modulus branch and preserves the distinction from raw EVM zero behavior.

Values.ClosedCertificate quantifies its source equation over every typed State,
so code cannot specialize state reads by evaluating source. It covers literals,
certified successful unary operations and successful binary operations whose
existing shortT declines. The short-circuit branch, reads and general Val
coverage remain open. The exact bytes are Backend.encode of the actual code.

## Work and backfill accounting

| Queue item | Status | Implemented evidence | Still required |
|---|---|---|---|
| Work 1 | done (P2 validated) | Typed literals; all accepted Boolean/equality/order/bitwise/unary constructors; typed selection coverage; full uint/int casts; all 32 cleanup widths; fixed-bytes resize/source-shift and round-trip laws | Frontend rewriting composition remains a parent integration obligation |
| Work 2 | done (P2 validated) | Native source certificates and all-width unsigned/signed add/sub/mul/div/rem math; all-width wrapping power; generic cleanup composition for shifts and every pure constructor; zero/minimum/shift exceptions | Full fetched-bytecode preservation remains a parent integration obligation |
| Work 3 | done (P2 validated) | Checked uint/int arithmetic, negation, unsigned/signed power; all-width range guards; existing truncating cast behavior retained; distinct failure data; staged composition and inhabited mixed-width controls | Generic branch/revert-byte emission remains separately owned |
| Work 4 | done (P2 validated) | Intrinsic operation/Val and ABI-word relations; closed and heterogeneous signed-power certificates; exact Backend.encode data; capacity-bearing consumers; 61 external controls | Complete source/frontend/EVM composition remains a parent integration obligation |
| Backfill A | done (P2 validated) | Unsigned checked/wrapping power at all widths; signed checked Val helper; addmod/mulmod wide intermediates and exceptional zero | None within this component queue |
| Backfill B | done (P2 validated) | Universal sequence/height/tail/prefix-capacity laws; signed/unsigned/fixed-bytes cast chains; mixed-width and signed-power inhabited capacity witnesses; boundary controls and guarded axiom pins | None within this component queue |

The widths metadata is Fin 32 (byte count minus one), not a new source type or
term IR. Existing source PrimTy is bool/uint/int; narrow widths live in frontend
metadata. Signed cleanup composition is a word-level theorem, not a claim that
source signed wrapping operations already have a selection certificate.
Fixed-point integration remains a named dependency on the separately owned
semantics/source lane, not an exclusion or full G25 completion claim.

## Feature and source anchors

Verified manifest IDs: arithmetic, unaryArithmetic, checkedArithmetic,
uncheckedArithmetic, fixedBytesTypes, explicitConversions, shifts. Their
localEvidence points to AST, Syntax/Grammar and solc-alignment; those files
were read and reused without edits. Relevant actual constructors are
BinOp.add/sub/mul/pow/div/mod/lt/gt/le/ge/eqB/neB/and/or/band/bor/bxor/shl/shr/
addW/subW/mulW/powW; UnOp.neg/not/bnot/toInt/toUint; ModOp.addmod/mulmod;
and Val.simple/binop/unop/modular. No constructor is claimed covered merely
because its opcode has a meaning in Slice.

At the exact base: AST PrimTy at line 30, ranges at 166, operators at 957,
acceptance/return at 1136; Semantics/Ops arithInt at 56 and modular evalT at 139;
Syntax/Raw narrowTy at 498 and bytesTy at 533; Syntax/Elab/Values width checks
at 1639, narrow wrapping at 1670, signedAt/casts at 1812, and bytes conversion
at 1452/1538; Semantics/Run Val.evalT at 302. Existing Evm/Signed,
Evm/SimLemmas, Evm/Exp and Semantics/NumericLowering offer read-only arithmetic
facts, but their symbolic instruction simulation is not Backend execution.

The intrinsic fixed-bytes carrier holds its payload in the low bits; widening
and narrowing preserve left-to-right byte semantics through shifts. ABI
left alignment must not be imposed blindly on every intrinsic scalar value.

## P0 validation record (historical)

This section records P0 only; the final P2 handoff below supersedes its pending
validation and implementation statuses.

The private alternate lakefile adds only Lean -j1 and is not committed.
No Lean MCP tools are exposed, so focused Lake targets provide per-file kernel
diagnostics. Passing targets so far: Slice, Typed, Widths, Comparisons,
Wrapping, Casts, Guards, Modular. Bitwise and Values now also pass their focused targets.
The pre-existing AST unused-variable warning is inherited; owned-file warnings
must be cleared. Layers pass (168 core modules, none reaches the elaborator), orphans pass
(776 reachable, zero orphaned), and trust passes (791 sources, 241 inventoried
implementation/recovery sites, zero findings). The exact-base documentation
comparison has no added or removed finding: both exit 1 with the same 46 missing
references. This inherited failure is not marked passed. The required no-new-
findings condition passes. Final full/import closure, run-lean.sh, remaining
exact-base build comparisons and external vectors remain pending.

The initial wrapping composition proof hit 200000 heartbeats. It was rewritten
to use run_comp explicitly; no heartbeat/recursion budget was raised. The fixed
wrapping/cast check passed in 2.6 seconds with 645 MiB peak summed Lean RSS,
173 MiB sampled cgroup use, and no OOM. These measurements include shared pages;
they are not comparable quantities. A later Values dependency check reached
816 MiB peak summed RSS and failed its byte-control proof, not a resource gate.
The repaired Values target passed (37 jobs), including the exact-byte control.

An independent read-only skeptic reviewed the first five modules without Lean
and found no confirmed semantic defect; it required retaining the structured-
instruction versus fetched-bytecode and frontend-width integration boundaries
above. Separate finder (Jason) and skeptic (Avicenna) reviews subsequently inspected
all ten modules and this document without Lean/server/build or writes. Neither
found a confirmed semantic defect. They specifically retained the boundary that
modularOutcome chooses Panic(0x12) for source none; this is not yet a proof
bridging Val.evalT's generic halt observation to those exact bytes. Generic
payload/branch emission, fetched-bytecode refinement, resource/capacity premises,
frontend expansion and full queue completion remain open. Final review of later
implementation changes will still be required.

Evidence directory: `/workspace/scalar-lowering-artifacts/evidence`.
The earlier handoff there describes the superseded runtime blocker and will be
replaced with the committed checkpoint handoff. No full gate is waived based
on historical SolKey mismatches or OOM. No unresolved scope question has been
used to narrow this assignment.

## Preparation checkpoint P0

All ten modules have passed focused kernel checks. Headline source constructor,
representation, slice composition and cleanup axiom outputs are now pinned with
#guard_msgs; only propext, Quot.sound and where reported Classical.choice occur.
The pinned Values import closure passed in 13.3 seconds at 664 MiB peak summed
Lean RSS (190 MiB sampled cgroup use); the pinned Modular closure passed in
3.8 seconds at 654 MiB summed RSS. No OOM or swap was observed. All checks used
the same 12 GiB/no-swap Docker cgroup and explicit Lean -j1.

This is a reviewable partial preparation checkpoint, not completion of any
numbered queue item. Full assignment validation and all remaining rows above
are still required. The absolute handoff records its actual committed head;
no self-referential commit hash is embedded in this document.


## Arithmetic checkpoint P1 (historical)

The source-native certificates now include scalarEq/scalarNe, uintNot,
intAnd/intOr/intXor, uintShl/uintShr/intShr, wrappingPow,
checkedUintAdd/Sub/Mul/Pow and checkedIntAdd/Sub/Mul. uint_div_correct,
uint_mod_correct, int_div_correct and int_mod_correct quantify over every
intrinsic operand and every untouched tail, including exceptional divisors.
int_div_body separately records its precise nonzero and minimum/-1 premises;
int_mod_body requires only a nonzero divisor. checked_negation_correct covers
the minimum integer. These are contracts for real Backend instruction slices
and the explicit guarded/guardedNext observation boundary, not a proof of
emitted control transfer or generic revert payload emission.

Signed division first chooses Panic(0x12) at zero, then Panic(0x11) at the
minimum integer divided by -1. The signed multiplication test includes the
minimum second factor/negative first factor check; division-back alone misses
that case. Signed right shift clamps negative source counts to zero rather
than passing their unsigned word readings directly to SAR.

PowerBounds holds 32×255 compiler constants. The Python generator uses only
integer arithmetic, and threshold_bounds kernel-checks both neighboring
power inequalities at every entry. powerFits_correct proves the independent
all-width range characterization, powerTest_correct proves the actual flat
opcode test, and checkedUintPow connects it to the original intrinsic pow.
Bases zero/one and exponent zero are handled separately; exponents at least
256 at bases at least two cannot fit. No root oracle is trusted. The initial
monolithic proof was stopped after 72 seconds as memory grew; its failed log
is retained. Splitting proofs by width passed in 292.1 seconds with 7721 MiB
summed Lean RSS and 8309 MiB sampled cgroup use (8713469952-byte cgroup peak),
one worker, no OOM, and the same 12 GiB/no-swap cap. No proof limit was raised.

Heights establishes step_height, run_height, run_capacity and prefix_capacity.
The executable stackBound includes temporary instruction-boundary peaks.
Tail preservation alone does not discharge it: unsignedAddTest at an initial
1023 words temporarily reaches 1025. A caller must prove the actual height
bound as well as operand availability. Source terms/values/states remain the
existing intrinsic types; no source semantics imports the compiler.

Axioms pins the actual dependencies of 51 additional headline declarations,
including all admitted primitive certificates, full guard observations,
capacity laws and threshold bounds. Its 67-job focused closure passed in
8.4 seconds with one peak Lean worker, 666 MiB summed Lean RSS and 184 MiB
sampled cgroup use. P0 guards remain in their original files. The separate
pin module avoids rebuilding the large constant table merely to guard its
message output.

Finder Dewey and skeptic Schrodinger independently inspected the stable P1
numeric/height files without Lean/LSP/build/tests or writes. They found no
semantic counterexample. Finder's missing-axiom-pin finding is addressed by
Axioms; skeptic's split-division-contract finding is addressed by the four
universal guarded theorems. Both retained the source halt-to-panic, generic
payload emission, frontend width expansion and physical capacity boundaries.
They expressly excluded the then-active power and signed-division modules.
An additional independent finder (Feynman) and skeptic (Euclid) pair inspected
those modules, SignedChecked/Mul/Guards, universal Division additions, Axioms,
the generator/checker, this document and append-only registrations without
Lean/LSP/server/build/tests or writes. Both found no confirmed semantic or
proof-boundary defect. Full assignment gates remain pending.


### P1 committed handoff section

Checkpoint status: reviewed partial arithmetic preparation; every numbered
queue item and both backfill items remained partial at P1. This
checkpoint adds sixteen owned modules (including the separate Axioms module)
to the ten P0 modules. No parent-group or full-assignment completion is claimed.

Gate commands and outcomes:

- `lake -f .scalar-lowering.toml build Solidity.Backend.Scalar.Axioms`:
  passed, 67 jobs, all owned-file diagnostics clean and 51 additional guarded
  axiom outputs accepted; only propext, Classical.choice and Quot.sound occur.
- `node scripts/check-layers.mjs`: passed, 168 core modules, zero frontend reaches.
- `node scripts/check-backend-scalar.mjs`: passed, 26 owned scalar roots,
  zero layer/source/trust/generation findings; 32×255 generated constants agree.
- `node scripts/check-orphans.mjs`: passed, 792 reachable, zero orphaned/not allowed.
- `bash scripts/check-trust.sh`: passed, 807 sources, 241 existing inventoried
  implementation/recovery sites, zero findings.
- `bash scripts/check-doc-paths.sh`: failed at both exact base and checkpoint
  with the same 46 missing references. Same-base comparison: zero additions
  and zero removals. The no-new-findings requirement passes; the whole command
  is not mislabeled green.

All focused checks used LEAN_NUM_THREADS=1, explicit Lean -j1, the writer lock
and the 12 GiB/no-swap Docker cgroup. Evidence is under the absolute directory
`/workspace/scalar-lowering-artifacts/evidence`; p1-axioms/summary.json and
p1-static-summary.json retain outcomes and measurements. The absolute
handoff.md, original.patch and SHA256SUMS in that artifact directory's parent
are refreshed after committing and record the full head, exact base and branch.
The separately saved review records identify all four read-only reviewers.

Required full/default/import/TestSuite/run-lean gates and actual encoded
sequence execution are pending; no inherited full-build failure is presumed.
The installed pinned EthereumJS Osaka runner has passed only an API bootstrap,
which is not evidence for this compiler's emitted bytes. Remaining casts,
width laws, capacity consumer and mixed-width witnesses continue next.


## Width, composition and intrinsic-helper checkpoint P2

P2 adds eleven owned modules, for 37 scalar modules total. CastChains proves
signedAt_word and signedExpansion_correct against the frontend's existing
arithmetic expansion (Values.lean signedAt at base line 1812), and proves
signed_chain and unsigned_after_signed at narrower-or-equal widths. The reverse
width-order counterexample is inhabited. FixedBytes proves bytesResize_correct,
bytesResize_range, bytesResize_roundtrip, bytesWiden_intrinsic and
bytesNarrow_intrinsic. Widening appends zero bytes on the right; narrowing drops
the rightmost bytes. A payload must fit its recorded source width for the
round-trip/range claims. No blanket ABI alignment or frontend rewriting theorem
is substituted for these contracts.

ArithmeticWidths defines widthResidue by integer Euclidean reduction modulo
2^widthBits, independently of emitted code. Its eleven unsigned/signed
add/sub/mul/div/rem and unsigned-power contracts cover all 32 widths, retaining
raw EVM zero-divisor behavior explicitly. Division/SignedGuards supply the
separate universal source-required failures. Composition proves that either
width cleanup composes with every admitted UnaryCertificate/BinaryCertificate,
with exact original intrinsic result types and untouched tails. Select dispatches
on existing BinOp/UnOp/ModOp and accepted PrimTy; binary_selection_coverage and
unary_selection_coverage establish accepted-constructor coverage. Division/rem
use their named universal observation contracts rather than being silently
accepted as total pure slices. No replacement source or opcode language is used.

WidthGuards proves unsignedWidthTest_correct, signedWidthTest_correct and their
parameterized guarded observations for every width. These implement the range
condition at the existing narrowCheck boundary (base Values.lean line 1764).
They do not turn Solidity's truncating explicit casts into checked casts.
The surrounding overflow/require mode retains control over supplied failure
data; its instrumentation/payload composition is a parent integration task.

Capacity exposes BinaryInvocation, CheckedInvocation and ClosedInvocation,
actual encoded bytes, decode_bytes and prefix safety. Their executable bounds
include temporary DUP/PUSH peaks. checkedAdditionWitness and the state-uniform
Combinations module mixedWidthCertificate/mixedWidthInvocation are inhabited: literals
255 and 2 fit uint8, their wrapping sum is 257, and signedAt at int8 returns 1.
The corresponding checked uint8 range guard rejects 257. mixedWidth_source and
mixedWidth_target independently pin the source and target observations.

SignedPowerPrefix/Post/SignedPower cover the committed heterogeneous
Val.checkedSignedPower helper (Syntax/Numeric.lean line 38;
Semantics/NumericLowering.lean checkedSignedPower_eval at base line 330).
The prepare slice computes magnitude and odd-negative result sign; the proven
unsigned power guard checks the full word range; the result test admits 2^255
only for a negative result; a final arithmetic slice applies the sign.
signedPower_correct quantifies over every int base, uint exponent and tail;
signedPower_source connects to the original typed Val helper under its exact
successful-operand evaluation boundary. No source evaluation consults code.
The source bridge preserves the original toOption/map-value statement; it is
not a new generic halt-to-panic-byte proof. SignedPowerInvocation stores all
five stage capacity checks, including the retained sign word, and
signedPowerWitness inhabits them. Positive/minimum and both signed/unsigned
magnitude-overflow source/target witnesses are kernel-checked. Its focused
65-job target passed with one worker and below 0.5 GiB sampled cgroup use.

The task-specific fixture scripts/fixtures/backend-scalar-export.lean proves
smallVectors_kernel and powerVectors_kernel and exports actual Backend.encode
bytes, including independently encoded PUSH32 inputs. Evaluation exports data
only; it is not used as a proof shortcut. The external checker
scripts/check-backend-scalar-evm.mjs uses pinned EthereumJS common/evm 10.1.3 at
Osaka. All 61 controls pass: 60 positive cases and one deliberate wrong-result
negative. It checks input immediate bytes, exact body suffixes, exceptions and
complete stacks. Signed-power preparation/result slices are included; generic
control/revert payload emission is not presented as externally validated.
Evidence is export-latest.log and external-scalar-latest.log under the absolute
evidence directory. Original smaller 44/45/55-vector runs are historical stages;
the latest successful exported set has 61 controls.

Final focused closure, static rechecks, both independent P2 reviews and
./run-lean.sh have passed as recorded below. The raw inherited documentation
path command still exits 1; its required no-new-findings comparison passes. Full source-to-bytecode preservation, source width/unchecked rewriting,
heap/read/call/control integration, exact generic failure payload emission and
separately owned fixed-point integration remain named parent obligations, not
new exclusions or claims that the full G25 roadmap group is complete.


### P2 final committed handoff section

All four assigned Work items and Backfill A/B are complete within the scalar
component boundary above. P0 and P1 are preserved reviewable commits; P2 adds
eleven modules, for 37 owned modules total. The final full SHA, original patch,
evidence and checksums are recorded in `/workspace/scalar-lowering-artifacts/handoff.md`;
the base and branch are recorded above. No source/typed semantics, shared global
interface, approved profile, manifest or other lane was edited.

The certificate premises are substantive: intrinsic accepted-operation proofs;
canonical existing typed operands; successful operand evaluation for Val helpers;
shortT decline for the closed binary Val bridge; source-width fit for fixed-byte
round trips; explicit prefix stackBound evidence for EVM's 1024-word capacity;
and separately staged guard decisions using existing failure bytes. The source
observations never depend on generated code. signedPower_source preserves the
original toOption/map-value observation, not a generic halt/payload theorem.
Headline contracts include binary_selection_coverage, unary_selection_coverage,
unsigned_addAt_correct and the other all-width arithmetic contracts,
unsignedWidthTest_correct, signedWidthTest_correct, unsigned_chain, signed_chain,
run_frame, run_capacity, prefix_capacity, mixedWidth_source/mixedWidth_target,
signedPower_correct and signedPower_source. All admitted source constructors and
headline arithmetic/guard/representation contracts have guarded axiom pins.

Final gates (same pinned toolchain; serial; LEAN_NUM_THREADS=1 and private
weakLeanArgs -j1; no heartbeat/recursion increase):

| Command | Outcome and decisive evidence |
|---|---|
| lake -f .scalar-lowering.toml build Solidity.Backend.Scalar.Axioms | Pass, 80 jobs, 119 additional guarded headline axiom pins; every owned module kernel-checked without owned-file warnings. p2-final-axioms/summary.json: 12.6s, one worker, 698 MiB aggregate Lean RSS, 185 MiB sampled cgroup use |
| lake -f .scalar-lowering.toml build Solidity.KeySort | Pass, Build completed successfully (2 jobs); final-keysort.log records actual Lean 4.24.0 / Lake 5.0.0-src+797c613 runtime probe independently of the full gate |
| ./run-lean.sh (private lake wrapper adds only -j1) | Pass exit0; default Build completed successfully (788 jobs), SolkeyTestSuite Build completed successfully (262 jobs); solkeycheck parsed 377 taclets, 131 read-bearing/table covers131 and OK against the pinned rules |
| node scripts/check-layers.mjs | Pass, 168 core modules, zero frontend reach |
| node scripts/check-orphans.mjs | Pass, 803 reachable, zero orphaned/not-allowed |
| bash scripts/check-trust.sh | Pass, 818 sources, 241 existing inventoried sites, zero findings |
| node scripts/check-backend-scalar.mjs | Pass, 37 roots, no layer/source/trust/generation findings; 8160 threshold constants agree with deterministic generation |
| bash scripts/check-doc-paths.sh, same-base comparison | Raw exit1 at both worktree and exact base: same 46 missing references; no added/removed findings. Required no-new-findings gate passes; raw command is not called passing |
| kernel fixture plus node scripts/check-backend-scalar-evm.mjs | Pass, actual encoded Osaka slices: 61 controls, 60 positive and one intentional wrong-result negative; export and external-scalar logs retain proof versus external-test boundary |

The full run took 9799.9s, peak aggregate Lean RSS10970 MiB, peak anonymous
10285 MiB, one worker, sampled/actual cgroup peak12884901888 bytes at the
enforced 12 GiB cap; swap limit0, no OOM or resource stop. Minimum sampled host
MemAvailable6228 MiB. Derived17 actually passed in154s; no historical OOM waiver
was used. The actual sort check matched, so no historical37-mismatch waiver was
used. Full-run resource evidence is full-run/summary.json and samples/modules
CSVs. Executor reattachments detached the outer stream; Docker retained the
complete output, saved as full-run-recovered.log. No competing Lean check ran.
The explicit final KeySort rerun also passed before RUNTIME_GATE_PASS was
reaffirmed. Scope questions: none.

Read-only P2 finder Beauvoir and skeptic Einstein independently reviewed all
eleven added modules, Axioms additions, fixture/checker, append-only registrations
and source anchors. Neither edited nor ran Lean, LSP, servers, builds or tests.
Neither found a confirmed semantic defect; evidence p2-reviews.md retains their
specific source/value, capacity, byte-order and external-test boundary checks.
P0/P1 reviews and confirmed P1 fixes are retained in preparation-reviews.md and
p1-reviews.md. The final update changes only status and measured gate reporting;
reviewed proof code is unchanged. No required component gate remains pending.
Parent integration obligations listed above remain explicit.

## Integration convention repair (2026-10-30)

The retained integration review identified missing explicit `have` types in
the added scalar modules, including anonymous declarations nested inside
other proofs. The repair adds 117 type annotations across 27 Lean files and
updates the power-threshold generator to reproduce the annotation in
`PowerBounds.lean`. Existing proof terms, theorem statements, semantics,
observations, target predicates, invariants and proof budgets are unchanged.

Per-file Lean MCP diagnostics completed successfully for all 27 edited Lean
files, checked serially with one document open. `PowerBounds.lean` completed
its kernel threshold checks; its axiom report remains `[propext, Quot.sound]`.
`node scripts/check-backend-scalar.mjs` passes with 37 roots, zero findings
and all 8160 generated thresholds matching. `git diff --check` also passes.
The coordinator retains responsibility for the full combined build gates.

Read-only finder and skeptic reviews independently found no remaining
untyped `have` declarations across all 37 scalar modules. Their comparison
against the integration candidate confirmed that the Lean changes contain
only type annotations and whitespace, and that the generator contains the
matching template change. Neither reviewer used the Lean server. No further
finding or scope decision remains for this repair.
