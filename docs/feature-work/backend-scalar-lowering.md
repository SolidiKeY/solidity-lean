# G25 scalar opcode lowering: preparation lane

This lane owns only `Solidity/Backend/Scalar/` and this document. It preserves
the [approved scope](../solidity-scope.md) and existing intrinsic syntax,
semantics, refusals, observations, target predicates and proof budgets. No
other worker's files, the global coverage ledger or manifest statuses change.
This checkpoint is partial; neither the frozen assignment nor full G25 is done.

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
| Work 1 | partial | Arbitrary typed literals; Boolean not/and/or/eq/ne; uint/int lt/gt/le/ge; uint AND/OR/XOR; source-exact uint/int word casts; all 32 signed/unsigned cleanup widths | Signed bitwise, numeric equality, complement, fixed-bytes conversion alignment and proof against source width/cast expansion; finish controls and checkpoint reviews/gates |
| Work 2 | partial | Source-exact uint addW/subW/mulW; all-width cleanup composition for ADD; independent DIV/SDIV/MOD/SMOD/SHL/SHR/SAR meanings and zero/saturation boundaries | Full division/remainder/shifts selection certificates and all-width source composition, signed minimum/-1 and negative-count reconciliation |
| Work 3 | partial | Operand-preserving zeroTest; distinct existing Panic(0x11)/Panic(0x12) bytes; zero-modulus failure selection and sequence laws | Checked add/sub/mul/power/negation and checked range guards, complete failure classes and inhabited mixed-width combinations |
| Work 4 | partial | Typed operator certificates, state-uniform ClosedCertificate composition, literal/not source witness, actual Backend.encode bytes | Broader Val/operation certificate coverage, representative external execution, final axiom/import/trust/validation closure |
| Backfill A | partial | addmod_correct/mulmod_correct at the guarded numeric-slice boundary, with wide-intermediate and zero controls | Exponentiation selection/guard certificates and final boundary/composition validation |
| Backfill B | partial | Universal successful tail/sequence laws; unsigned_chain; cast_code_chain; narrowing/sign/operand-order controls | Stack-height and full cast-chain/source-expansion laws, remaining negative boundaries and every constructor's axiom pins |

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

## Validation and reviews in progress

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
