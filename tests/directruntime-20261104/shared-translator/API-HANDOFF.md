# Shared executable API for DR-B, DR-C and CR

Base: b419c3cf4f642ae519b66bebc26cdf2f7cf93574.
Assigned branch: codex/solidity-directruntime-20261104/shared-translator.
The exact source commit/path/hash receipt is artifacts/API-RECEIPT.json.

Concrete implemented paths:

- Solidity/Frontend/ExecutableAst/Shared/Boundary.lean: Reader callbacks returning
  existing Raw syntax, Ty/FunSpec, with Except String failures.
- Solidity/Frontend/ExecutableAst/Shared/Translate.lean: reader, typeNameStep,
  expressionStep, statementsStep, function and contract. Default support/refusal
  behavior is the extracted executable fragment. No second reader remains in
  DirectRuntime. Exact checked signatures are in evidence/api-signatures/1.log
  and IntrinsicControls output for the additional intrinsic signatures.
- Solidity/Frontend/ExecutableAst/Shared/Intrinsic.lean: BodyLoopLowerer,
  PlainEntryPre, assertionObligation and obligation, all implemented. DirectRuntime
  pins the two callbacks to existing Frontend.lowerBodyLoops and
  fun C Γ => Problem.callPre C Γ false [] false [] true. The specified branch
  delegates existing specObligation. No helper implementation is copied.

B/C start only from the exact committed API path/SHA in the receipt. They provide
separate modules in their registered scopes; A alone wires Shared/DirectRuntime.
Extensions must reconnect recursive expression/type/statement callbacks through
step functions. Updating Reader.expression alone leaves the default statements
callback bound to its old reader. Errors are final, never fallback-as-success.
Capture resolved declaration tables in callbacks; preserve IDs, lexical scopes,
shadowing, evaluation order, overloads, unsupported siblings and diagnostics.

Reference parameters remain refused by the default AST reader and by an explicit
intrinsic guard. Before admitting them, preserve the source producer's refInputs
premise and modality-specific reference binders; closeN's box binders alone do not
implement source diamond inputs. Arbitrary lowering/premise callbacks are not
source-soundness certificates. No fabricated interface theorem is supplied.

Shared.Translate source closure:17 local modules, no Import/Testing.
Shared.Intrinsic source closure:105 local modules, including only Shared.Scope in Frontend.
These are static import results, not generated-C runtime closure proofs. Focused
MCP build/diagnostics and IntrinsicControls passed; source/C/olean manifests bind
those checked files. Full DirectRuntime/native/WASM closure remains pending.

CR owns the producer migration: preserve readImportedContract admission/settings/
provenance, migrate the actual printed-body/parser/macro-to-Raw route, retain
calldata checks, source lines, return lowering, constructors and source modality/
reference premises. Formula-wrapper changes alone leave the second AST path and
cannot satisfy acceptance. No existing producer API changes are authorized here.

H30 owners: DR-D native/browser scripts; CR Admission/P8; V11 MemoryOps;
V09 Passes; VY5 H16 Source; V08 Lowering/V08; V16 Aggregates/Roadmap.
Source/ExtCall and shared roots/maps/trust pins stay frozen. A supplies registration
proposals only. No push, merge, PR or publication.

## Metadata admission increment after the published fcdddfcc API

Reader signatures and step decoders remain unchanged. Public function/contract
now validate metadata after whole legacy root success; standalone roots can use
checkedExpression/checkedStatements. Raw Reader callbacks are not admission
certificates. Constant-folded descendants are inspected; legacy errors retain
priority; contract checks do not inspect sibling function bodies. Full CR operator
alias support remains pending because the default metadata policy refuses aliases.


## Composed runtime checkpoint after published master f77cf60d

Shared.Compose.executableReader is now the canonical runtime reader. It recursively
wires exact published B Memory.Reader and C ControlTuple.Adapter bytes; source
identity receipts are in evidence/adoption-8495/merge-resolution.json. Shared
function/contract validation still runs after decoding. Old default reader controls
are deliberately retained; composed controls are separate observations.

Shared.Scope reserves root/parameter/local/invariant names and proves numerical
freshness bounds. The plain builder now runs the existing renameStmts before the
BodyLoopLowerer callback, so that callback receives renamed syntax. Same-scope
duplicates are checked on original declarations. No source-preservation theorem
is claimed. Reference parameters/returns remain refused. Exact checked signatures
and axiom inventory are in artifacts/composed-gates/2.log and3.log.

DR-A-META: CR/D must choose required metadata retention alongside existing builtin
normalization/loop annotations, or an owner-reviewed checked compatibility adapter.
The composed fixture implements retention only in A's test scope. CR still owns
actual existing Lean import migration; no independent optional wrapper suffices.
Native/WASM ordinary closure is pending owner D evidence. At this historical checkpoint both Scope/Compose roots were local proposals;
published9584 later registers Scope. Compose remains pending; A does not edit
generated registrations.


## Published9584 adoption and canonical kind observations

Migration-packet.json binds the concrete API/current producer source hashes and
acceptance obligations. Reader-comparison.json records every same-input difference
between default and canonical readers across both57-kind suites. Existing suite:
11decoded/26refused/20no-entry for both,with four refusal-reason changes. Fresh suite:
default14decoded/23refused;canonical16decoded/21refused;both20no-entry. Only selected
DoWhileStatement/TupleExpression witnesses change to decoded. Both suites retain
37unknown-root refusals; whole witness/child failure caveats apply. Default frozen
matrices were preserved,not overwritten by capture. Frozen MCP and per-file gates
passed. Source preservation and full producer parity remain open.

Published9584 registers Scope centrally; Compose alone remains a local proposal.
No generated root or map was edited by A. CR migration/DR-A-META/native closure
remain pending; packet publication does not complete original queue item2.
