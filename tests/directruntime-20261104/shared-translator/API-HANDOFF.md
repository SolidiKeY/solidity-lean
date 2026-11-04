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
Shared.Intrinsic source closure:104 local modules, no other Frontend module.
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
