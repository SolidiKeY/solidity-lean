# Shared executable AST translator

Status: preparatory raw-reader extraction, not completion of the first checkpoint
or the assignment. Base: `b419c3cf4f642ae519b66bebc26cdf2f7cf93574`.
Branch: `codex/solidity-directruntime-20261104/shared-translator`.
Repository: `/workspace/solidity-lean`.

## Concrete executable boundary

`Frontend/ExecutableAst/Shared/Boundary.lean` defines `Reader` with these exact
fields (namespace `Solidity.Frontend.ExecutableAst.Shared`):

```lean
structure Reader where
  typeName : Json → Except String (Ty × RawTy)
  expression : Json → Except String RawExpr
  statements : Json → Except String (List RawStmt)
  params : Json → Bool → String → Except String (List (String × Ty))
  specification : Json → Except String FunSpec
```

`Translate.lean` provides the actual default `reader`, plus concrete recursive
extension steps:

```lean
typeNameStep : (Json → Except String (Ty × RawTy)) → Json → Except String (Ty × RawTy)
expressionStep : (Json → Except String RawExpr) → Json → Except String RawExpr
statementsStep : (Json → Except String RawExpr) →
  (Json → Except String (List RawStmt)) →
  (Json → Except String (Ty × RawTy)) → Json → Except String (List RawStmt)
function : Reader → Json → String → Except String (String × FunDecl)
contract : Reader → Json → Except String Contract
```

B/C modules must capture their declaration-resolution tables in callbacks,
dispatch only their owned forms, and connect all recursive callbacks through
these steps. An isolated update of `reader.expression` does not reconnect the
already-bound default `reader.statements`. `ReaderControls.lean` pins this caveat,
connected nested extensions, both conditional bodies, left-child error priority,
type recursion and retained refusals. An `Except.error` is final: never catch it
to retry another executable translator. Only the existing Raw surface syntax is
returned, as input to existing intrinsic elaboration. No new verification IR,
axiom, admitted proof or placeholder implementation is introduced.

DirectRuntime now imports Shared.Translate and calls `contract reader` and
`function reader`; the old local reader was removed. Its proof-search/export code is unchanged. The assertion builder now lives in
Shared.Intrinsic with explicit producer callbacks and a new reference guard that
preserves the already-refused default AST fragment. The extracted helpers retain all 252 original string literals
in order. Default admission remains limited: uint256/int256/bool parameters,
primitive locals, arrays/mappings as storage roots, selected expression forms,
assignment/assert/require/push/pop, while/for and compact specification parsing.
References, tuples, richer contracts/calls and do-while remain refused by this
default. The existing name-only identifier reader and String diagnostics retain
known parity gaps. Malformed boolean validation and constant-kind dispatch need
separate regression-backed fixes; this extraction does not declare them solved.

## Import closure and CR migration packet

The local source import closure of Shared.Translate has 17 modules and reaches
neither Frontend.Import nor Frontend.Testing. It uses the producer's existing
constant arithmetic/documentation helpers from SolcJson.Contract/Body. This is a
source import-cycle check, not a generated-C closure or no-kernel runtime proof.
Registration rows are proposed in the owned `registration-proposal.json`; shared
roots, maps and trust pins were not edited.

CR still owns the existing general printer/import route. CR must migrate its
producer-owned wrapper to this executable boundary while preserving every
previously supported form and diagnostic, and provide its exact reviewed commit.
No producer API was changed here. `lowerBodyLoops` currently lives in
Frontend.Import (lines 221 onward at the base); copying it into Shared would
create duplicate executable semantics. The shared intrinsic builder now reuses it through an explicit callback, alongside
the producer-owned Problem.callPre from Frontend.Problems. Producer adoption and
full source parity remain open; neither helper is copied. Importing Testing into Shared would
create a cycle and is prohibited. A new optional wrapper or this raw-reader
extraction alone does not satisfy the shared-translator requirement.

## Census and controls

Run `python3 tests/directruntime-20261104/shared-translator/inventory.py`.
The owned `coverage-inventory.json` compares all 58 emitted Solidity node kinds
against the pinned compiler ASTJsonExporter (commit
`1835d247de183f23e7b0e2bc4a50732af525b77c`, Git blob
`b855c19efcb9061c7b19b696cf7045f25e78dc74`). It inventories 16 Yul kinds,
17 RawExpr and 42 RawStmt constructors and all 212 feature catalog entries.
Every row separates source admission, Raw/elaboration input, proof closure,
semantic catalog observations, backend gaps, ownership and candidate fixtures.
It explicitly marks full per-construct positive/negative controls as pending; H30 supplies the integration-owner map below. The compiler exporter is preserved with its
GPL header as source-provenance evidence. Catalog/schema inspection is not an
AST-to-solc semantic-equivalence theorem.

ReaderFixtures.sol/ast.json are freshly generated by the pinned solc 0.8.34
compiler (compiler SHA and source SHA are in the fixture header). FixtureControls
checks supported scalar/array/loop/spec bodies beside refused memory/tuple/
do-while siblings, two distinct overloaded declaration IDs, and retained
contract-member refusal in UnsupportedContract.sol. These are raw-admission
controls; sourceId selection/reporting, formula closure and producer parity still
need their own tests.

## Validation and reviews

All heavy checks use the owned bounded.sh wrapper: Docker memory.max=12884901888,
memory.swap.max=0, one CPU; LEAN_NUM_THREADS=1 and explicit Lean -j1. The outer
cgroup/host available-memory guard monitors H1's 4 GiB reserve. Writer locking
covers commands. Actual Lean 4.24.0 (797c613), Lake 5.0.0-src+797c613 were read.
The alternate config has focused Shared defaults for MCP lean_build; tracked
run-lean.sh still requests its tracked full default targets. Native/WASM build
scripts use absolute prefix/bin/lake and need explicit bounded-config handling;
the PATH shim alone does not cover those future commands.

Evidence under `tests/directruntime-20261104/shared-translator/evidence/`:

- shared-mcp.log: focused 18-job build succeeded; both per-file diagnostics zero.
- reader-controls.log: callback/refusal controls passed (3 seconds).
- fixture-generation.log: both pinned compiler fixtures regenerated successfully.
- fixture-controls.log: all nine function rows plus unsupported contract sibling passed.
- api-signatures/1.log: exact Lean-checked callback/function/contract signatures.
- compiled-source-manifest.json: exact source/generated-C/olean hashes for Shared;
  not a runtime-closure or final exact-head gate.
- baseline-per-file/1.log: exact-base check failed due missing AnonLocalCapture.olean.
- baseline-build/1.log: fresh broad dependency build was deliberately interrupted
  before DirectRuntime; exit 137. It is pending, never counted as passing.
- reviews.md: independent read-only finder and skeptic, neither using Lean server.
  Confirmed resource/import/callback issues were fixed or explicitly retained as
  outstanding integration obligations. Counts were corrected by schema comparison.

Fresh KeySort passed after the first source commit: 377 taclets, 131 read-bearing,
table covers 131, exit 0. No RUNTIME_GATE_PASS: exact-base/head before/after timing/runtime,
compiled closure, native/WASM provenance and final full gates are still pending.
New module central registration is a proposal; no shared generated edits are
silently made to pass roots checks.

## Queue and handoff

1. Census: initial schema-complete index saved; per-form semantic/backend closure,
   all matching controls and per-form semantic/backend closure remain pending. H30 owner assignments are recorded.
2. First shared boundary: raw-reader callbacks and primitive intrinsic builder compiled/reviewed;
   full producer parity/adoption/migration and native/WASM closure remain pending.
3. Integration: no exact reviewed B memory/C control or CR migration commits have
   been received/consumed. A remains the only Shared/DirectRuntime writer.
4. Final ledger/proofs/performance/handoff: partial source packet only. Required
   full tests, proofs, reviews and serial runtime evidence remain open.

No push, merge, PR or publication. The persistent goal remains active for the
whole assignment; this preparatory packet is not final acceptance.

## Intrinsic executable API increment

Shared.Intrinsic imports Calculus.Spec; its static local closure has 104 modules
and reaches no other Frontend module. Its additional exact signatures are:

```lean
BodyLoopLowerer := List String → Nat → List RawStmt → ElabM (List RawStmt)
PlainEntryPre := (C : Contract) → (Γ : NCtx) → Fml C Γ.ctx
assertionObligation : BodyLoopLowerer → PlainEntryPre →
  (C : Contract) → String → Bool → Except String (Fml C [])
obligation : BodyLoopLowerer → PlainEntryPre →
  (C : Contract) → String → Bool → Bool → Except String (Fml C [])
```

ElabM here is Solidity's existing pure lowering computation, not Lean's environment
elaboration monad. DirectRuntime.buildObligation pins lowerBodyLoops and
`fun C Γ => Problem.callPre C Γ false [] false [] true`. No producer API changed.
The specified branch calls existing specObligation. The primitive assertion
algorithm, lowering order, source=true elaboration, entry/well-formedness premises,
scalar binders and modality are preserved.

Reference parameters remain refused. The new intrinsic guard prevents using
closeN's box reference binders for a source diamond. The producer's general wrapper
uses modality-specific binders plus refInputs; integration must preserve those
before admitting references. No arbitrary-callback source theorem is claimed.

intrinsic-mcp.log records a successful focused 114-job build and zero diagnostics.
IntrinsicControls checks the real existing lowerBodyLoops helper, both modalities,
entry-premise transport, callback failure, scalar binding, reference/return refusals
and specified/plain dispatch. These are development controls, not source or backend
correctness proofs. intrinsic-source-manifest.json binds source, generated C and
olean bytes. The broader closure warm-up was interrupted with exit 137 for this
increment and remains pending; it is not a passing before/after/runtime gate.

CR migration touchpoints remain Import.readImportedContract (base lines 565–589),
the printed-body/parser/macro-to-Raw block (793–822), loop/return lowering and source
scope checks (846–875), Problems.obligation (140–192) and the specified testing
wrappers. Changing only formula construction leaves a second AST translation path
and does not satisfy this assignment.

## H30 ownership and recovered API packet

The original executor was reattached with the branch, b2c27cb7 source commit and
uncommitted Intrinsic intact. A recovery diff/untracked archive was saved before
writes. A alone owns Shared, DirectRuntime and this lane's documentation/tests.
Shared generated roots, module maps, trust pins, Scoped and Source/ExtCall remain
untouched. B owns registered Memory modules, C ControlTuple modules and D the
registered native/browser scripts. Integration owners: CR Admission/P8 migration;
V11 MemoryOps; V09 Passes; VY5 H16 Source; V08 Lowering/V08; V16 Aggregates/Roadmap.
These ownership answers resolve DRA-OWNER-1; they grant no extra A write scope.

The API packet is API-HANDOFF.md in the owned test directory. Its exact committed
SHA/path receipt is saved in artifacts/API-RECEIPT.json after committing. Reader
signatures remain unchanged from b2c27cb7. Intrinsic is implemented and checked,
not a placeholder proof or declaration stub. First-checkpoint completion still
requires full producer parity/adoption and native/WASM closure evidence.
