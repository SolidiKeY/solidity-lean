# Calls and exceptions

Integration status (2026-10-26): included in the shared checkout. Current
combined validation is tracked in [integration.md](integration.md).
Worker handoff statuses and isolated validation results below are historical;
they neither report the current combined checks nor establish full source support.

## M1: eager operands and exact self-call panic data (2026-10-26)

Worker handoff (historical): **patch_ready_unvalidated**. This patch was produced outside the
shared checkout. Its worker ran no Lean/MCP check or build. The implementation
is now integrated, with current combined validation tracked in integration.md. The full calls/exceptions group remains
incomplete; no feature-catalog support verdict is upgraded here.

### Implementation

`RawStmt.requireWith` preserves custom-error argument evaluation for both
condition values. The elaborator keeps its cheap `require(c)` lowering only
when every omitted argument is raw-pure and its typed primitive value has
`mayHalt = false`. Raw simplicity alone does not establish totality: `p.x`
and `a.length` can fail through unset aliases or memory. Synthesis failure
in this early optimization query means "cannot omit", since later passes
may still normalize a valid selector expression. It does not reject source.
This is a frontend optimization criterion, not a new assumed theorem.

An ordinary `revert E(args)` evaluates its operands before dropping data.
A self-frame revert preserves ABI payload construction. `eagerArgsWith`
finishes one argument's hoisting and typed evaluation before starting the
next, rather than hoisting all operands before reading their residual values.
Only discarded values may omit total primitive reads. Encoded values are
captured before later effects. Reference operands are explicitly bound even
when they are names, so unset references still fail. Custom-error captures retain their declared primitive parameter types,
including exponent/shift literal expressions that are not rational-folded.
Literals retain their contextual types. A computed string reason cannot be allocated or evaluated
before a residual failing condition. Discarded event operands use the same
eager path.

Self-frame enum conversion emits literal `Panic(0x21)` bytes, and the typed
terminal branch of internal-function dispatch emits `Panic(0x51)`. These
bytes reach existing data/panic-code classification and catch rules without
an arbitrary transaction-oracle code. Outside self frames, existing ordinary
assertion/revert readings remain unchanged. Dispatch evaluates each argument
once at its formal parameter type before selecting a target; all candidate
filters, source-entry filtering and tag positions are retained.

Extra captures are local to error operands, reason conditions and indirect
calls. They can change printed fresh names and increase indirect-call proof
terms. No deep/shallow representation change or rollback of a speed-oriented
history change is involved. Measure affected examples during integration;
do not raise heartbeat limits to accommodate a regression.

### Soundness and remaining scope

No `Stmt`, `Fml`, `THalt`, taclet or frame constructor changes. Existing
soundness dispatch covers the emitted typed declarations, branches and literal
reverts. Concrete negative boxes reject the formerly vacuous proof of
`[require(false, E(failAssert()))] true` and the corresponding standalone
revert. Formulas use the existing notation.

`TRun.catchBytes_self_data` transports the callee's actual `THalt.ofData d`
for arbitrary immutable byte lists, including empty data, at a nonzero self
address. `TRun.catchData_self_data` connects those bytes with the actual typed
catch allocation, evaluated from the original caller state. Address and
decoder premises stay explicit. These ordinary execution equalities add no
axiom and make no completeness claim about callback catches. The allocation
and typed heap extension remain explicit in the conclusion.

This patch leaves conservative `allocAll` treatment of unknown memory
payloads unchanged. Callback catches, recursive memory returns with owned
writes, reference-valued function types, static-call world semantics and
external aggregate return decoding remain open. Legacy/viaIR scheduling of
the function expression itself also remains open: the existing named-value
legacy order is retained, and this milestone claims no whole-frontend
pipeline equivalence. The separate ownership-aware callback-frame milestone
must retain `withinM`; `withinW` admits a different set of shapes.

Compared `origin/master` changes loop frames to `FrameKeeps` and
`Prog.frame_within` and removes a duplicate `TRes.ofOpt_ok`. This patch uses
neither API and needs no loop proof migration. Shared source-admission edits
must still be three-way merged using the supplied exact base bytes.

### Regression evidence

`tests/solc/CallExceptions.sol` contains successful controls and deliberately
false assertions. `Examples/Tactics/CallExceptions.lean` supplies intended
kernel proofs of eager operands on true/false requires and standalone revert,
event operands, caller-side failure outside a try, 0x21/0x51 catches,
division before later overflow, condition before reason failure, value
snapshots before effects, and rollback. Negative box/diamond formulas use
concrete-state refutations. Uninitialized storage aliases appear only in
separately labelled admitted-state model tests; Solidity rejects that source.

The source's raw-catch checks inspect length, selector and code bytes.
The independent EVM runner additionally checks complete direct panic and
custom-error returndata. Its successful self-calls execute installed runtime
code at a non-precompile address in a fresh VM per vector.

The modern-provenance AST uses exact solc `0.8.38+commit.1835d247`, SHA-256
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
It does not repin frozen TestSuite fixtures. Regenerate with:

```sh
node scripts/solc-ast.mjs --compiler-file /path/to/soljson-v0.8.38+commit.1835d247.js \
  --compiler-sha256 6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390 \
  --source tests/solc/CallExceptions.sol --out tests/solc/CallExceptions.ast.json \
  --evm-version cancun --wrapper Solidity/Examples/Tactics/CallExceptions.lean
node scripts/check-call-exception-vectors.mjs COMPILER_FILE EXTERNAL_NODE_MODULES
```

Optional reference dependencies are EthereumJS vm/common/util 10.1.3 and
ethers 6.17.0, installed outside the Lean package. The runner checks compiler
hash/version and compiles legacy and viaIR with Cancun/optimizer enabled.
Patch-production checks include JavaScript syntax and modern AST generation.
Reference-vector totals and read-only review results are recorded below.
These checks do not evaluate the proposed Lean lowering or establish proofs.

### Primary integration gates

1. Three-way merge using exact base files, retaining newer source admission,
   declaration helper filtering and upstream changes. All imported fixture
   rows must remain `.elaborated`; do not weaken the regression for a gap.
2. Per-file diagnostics: Raw, Values, Arms, Stmt, RevertMemory, CallExceptions.
   Check catch-transport proof signatures and headline axiom sets.
3. Recheck FunctionTypes, RevertData, ComputedRevert, SelfCall, CallOperands,
   SourceLiteralsImport and DeclarationMetadata, inspecting changed print pins.
4. Final library/TestSuite/frozen-SolKeY/corpus gates, layer/orphan/doc-path
   checks and unchanged feature/automation audits. No raised heartbeat limit,
   new axiom, proof shortcut, unfinished proof or Lean dependency is allowed.
5. Site registration is left to the primary; this worker intentionally supplies
   no site-manifest mutation.

The primary owns compilation, kernel checking and final validation.

### Patch-production review and checks

Read-only finder and skeptic reviewed the implementation without Lean or
builds. The finder confirmed and prompted fixes for early selector synthesis
and contextual signed literal exponentiation. The patch now treats early
synthesis failure conservatively and captures self-frame custom-error values
at their declared primitive types; source cases cover both. The skeptic found
no concrete remaining defect in literal panic lowering, typed dispatch or the
exact catch-transport statements. The raw-payload test description was
corrected to distinguish selected byte checks from full EVM returndata checks.

JavaScript syntax and modern AST generation passed. Exact compiler
0.8.38+1835d247 and 0.8.34+80d5c536 each passed **70 EVM vectors**, legacy and
viaIR combined, **140 total**. The compiler hashes and versions are checked
by the runner. No Lean code, MCP, real-checkout writer lock, build or source
runner writing into the real checkout was invoked by this worker.

The artifact contains complete intended declarations/proof scripts, exact
base copies and hashes for three-way merging. Its historical
`patch_ready_unvalidated` handoff is separate from the integrated checks in
integration.md.

### Final review repair: fixed-byte custom errors

A final read-only finder found that the existing custom-error encoder used
integer ABI alignment for `bytesN`. Error operands in both require branches and standalone reverts now apply implicit
`bytesM` to `bytesN` right-padding while source widths are still visible,
before function/byte lowering and eager captures. Native external selector
projections contribute their `bytes4` width. `revertErrParts` then reads the
error declaration's width and shifts the compact byte value into the left
of its ABI word. This final step constructs an intrinsic uint value
operation directly, so the shift is 256-bit regardless of frontend width
metadata. A raw uint256(...) cast inserted after operand hoisting is not
accepted by synth and must not be used here. Integer,
signed, address and boolean error words keep their existing encoding.

Source and native regressions cover leading-zero literals, dynamic bytes,
implicit widening, returned fixed bytes, selectors, a full bytes32 word,
eager snapshots before a later effect, rollback and a false right-alignment
assertion. The external EVM runner checks complete direct error payloads
as well as the source raw catches. This repair joined the combined integration
after a `patch_ready_unvalidated` handoff; current Lean validation is tracked
in integration.md. It changes frontend encoding only, with no new semantic or
proof axiom and no new package dependency.

### Import completion: event operands

The full-build report exposed a missing source printer arm for `EmitStatement`.
Unqualified direct positional events now resolve their exact `EventDefinition`
identity, check argument counts, and emit native `emit` syntax. Its existing
lowering evaluates all operands and abstracts the log. Positional operands
keep source order in both pinned compiler pipelines. Missing/ambiguous/wrong-kind
declaration identities are refused. Qualified event names and all named event
argument lists remain explicitly unsupported. The latter need pipeline-aware
lowering: a compiler/EVM trace with `emit Seen({second: mark(1), first: mark(2)})`
records effect order 21 in legacy and 12 in viaIR for both pinned compilers;
the positional `emit Seen(mark(1), mark(2))` control records 12 in both. These
are event-specific observations, not an inference from binary or addmod order.
The source feature inventory remains partial. Parser guards pin resolved
positional overload selection, argument order and named/missing-ID refusals;
the existing source
`emitArg` kernel theorem pins actual operand panic behavior. The 176-vector
EVM source corpus is unchanged. Combined Lean checking is tracked in integration.md.

The full-build native selector regression also exposed an unhoisted raw cast
introduced by the ABI alignment repair. The final encoder now constructs the
intrinsic uint shift directly; it neither re-enters narrow-width lowering nor
asks `synth` to interpret a cast that only `hoist` handles. This restores the
resolved self body instead of falling back after a swallowed elaboration error.
The native selector and complete source raw-catch proofs stay unchanged.
