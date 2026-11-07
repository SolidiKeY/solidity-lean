# Lowering correctness: bounded prior-art study (H117)

## Open question

How do CompCert, CakeML, KEVM and Yul/EVM semantics justify loop lowering with break/continue/return, unchecked arithmetic rewriting and partial or monadic elaborators? Which mechanism can connect our actual `lowerLoops` / `uncheckStmts` to existing G19 proofs without new per-case copies (H112)? This study proposes no interface freeze, exclusion, premise or implementation change.

## Our current state

All repository references below refer to base **a0a9ca15ba35fd6e8d9a9be10e4b6b45dbf45d3e**. Source is read only; sole changed file is this report.

- Solidity/Syntax/Elab/Lower.lean:543: `lowerLoops (rs : Option (List String)) (ss : List RawStmt) : ElabM (List RawStmt)`. Both sides are raw syntax, not the resolved intrinsic Source statements or G19 target `Prog`. It projects `lowerList`'s result after initializing loop flags.
- Solidity/Syntax/Elab/Values.lean:651: `ElabM` is ReaderT over two StateT layers ending in `Except String`: scope, local context/fresh counter and call memo matter. `freshCapture` at :728 increments that counter. Success must be associated with the exact incoming scope/state and output; freshness is an obligation, not alpha equality by wish.
- Solidity/Syntax/Elab/Lower.lean:419,435,483: mutually recursive `partial def lowerList`, `lowerStmt`, `lowerLoop` hide behind the non-partial wrapper. At :448-449 out-of-loop break/continue fail; :455 rejects return without function return slots; :474 rejects jumps in try inside loops. Partiality is not just an error constructor: the proof route must also avoid assuming kernel reduction of opaque partial recursion.
- Solidity/Syntax/Elab/Lower.lean:349-385: `LoopFlags`, `LowerM`, `LoopFlags.flag`, `notAny` manage distinct loop break/continue flags and a nest-shared return flag. At :495-500 effectful while conditions are moved to iteration heads; :512-535 do-while gets a first-iteration flag, continue resets each iteration, updates are guarded by break/return, and invariants acquire flag-typing tautologies. :538 emits the outer return test. A generic simulation needs these control and scope invariants.
- Solidity/Syntax/Elab/Lower.lean:707-736: `partial def uncheckStmts : List RawStmt → Except String (List RawStmt)` recursively rewrites arithmetic, inc/dec and blocks, preserves loop specifications (:728), rejects assignment-inc/dec (:716) and nested checking blocks (:722). The transformation is for the semantics of an unchecked context; it cannot preserve the checked semantics of overflowing input.
- Call sites: Solidity/Syntax/Elab/Arms.lean:829 lowers function loops; :1522 and :1926 lower standalone loops; :2036 runs `uncheckStmts` under an unchecked reader scope before branch elaboration. Solidity/Syntax/Elab/Lower.lean:701 invokes loop lowering before return lowering in modifiers. Thus raw-output equality alone cannot establish the full resolved-source-to-model endpoint.
- docs/audits/proof-coverage.md:150 identifies F3: actual elaborator functions lack correctness linkage. Solidity/Source/Agreement/NormalStatement.lean:6-9 explicitly denies a general inhabited program pair; `NormalLocalsObligation` at :23 only constrains normal primitive locals in one direction, not errors, state, association or termination.
- Solidity/Lowering/G19/AssignmentWhileBreak.lean:12 defines a hand-written `code`; :74 `correct` assumes `ContextMap`, related source locals/target environment, Boolean reflection, Boolean slots and exact slot-map equations. It proves execution at `fuel+3`, target execution, post-local relation and unchanged target globals. It does not invoke the raw elaborator, prove arbitrary loop bodies, equate source journal with target storage, or prove physical gas.
- G19 has 18 `correct` declarations and 18 companion Controls files (36 files). This is bounded semantic evidence, not a total lowering relation. Source/Agreement contains primitive/local composition infrastructure; its normal-result contract retains the missing association explicitly.

### Construct-to-shape map

Paths in the next table are relative to Solidity/Lowering/G19/. Each anchor is the `correct` declaration. A covered shape means the listed fixed family, not its entire syntax constructor.

| Lower construct | Existing shape and anchor | Gap to actual lowering |
|---|---|---|
| while + assignment condition + break | AssignmentWhileBreak.lean:74 | raw lowering/elaboration output association |
| while + continue / reset | AssignmentWhileContinue.lean:86; AssignmentWhileReset.lean:205 | arbitrary body/iteration induction and flag scope |
| while + return | WhileReturn.lean:43 | arbitrary return values and nested control |
| do-while + break/continue/return | AssignmentDoWhileBreak.lean:74; AssignmentDoWhileContinue.lean:76; AssignmentDoWhileReturn.lean:94 | first flag and generic recursion |
| for + break/continue/return | AssignmentForBreak.lean:64; AssignmentForContinue.lean:186; AssignmentForReturn.lean:56 | generic init/update and skipped updates |
| return and suffix control | AssignmentReturnFlag.lean:69; ReturnTail.lean:140; ReturnPair.lean:90 | return-slot binding and full result agreement |
| conditionals / continuation | ConditionalStatement.lean:94; ConditionalSequence.lean:108; ConditionalReturn.lean:63; ConditionalReturnContinuation.lean:54 | compositional link to actual generated guards |
| checked/unchecked blocks | AssignmentBlocks.lean:113 | Boolean assignment blocks only; numeric panic/wrap rewrite uncovered |
| general nested loops, try jumps, arithmetic rewrite | uncovered by a general G19 correctness theorem | distinguish explicit elaborator refusals from missing proofs |



## Verified external mechanisms

These are bounded source inspections, not reruns of external proof assistants. Exact upstream revisions and file links are pinned below. Downloaded bytes and SHA256 are in the off-Git `sources.json` handoff manifest. No external compiler verification claim is inferred from an interpreter, documentation or test alone.

### CompCert: prove the successful translation, including control continuations

At revision **2685140bf72c959446981fb99b5e44a8975021bc**, [cfrontend/Cshmgen.v](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/cfrontend/Cshmgen.v#L680), `transl_statement` is a structurally recursive `res stmt` translation with explicit break/continue exit depths `nbrk,ncnt`. Its `Clight.Sloop` case (:716) translates the body with depths 1,0 and the post part with 0,S(ncnt), then constructs `Sblock (Sloop (Sseq (Sblock ts1) ts2))`. Break/continue become `Sexit`; return stays `Sreturn`. This is structured exit lowering, not our Boolean flag encoding.

[cfrontend/Cshmgenproof.v](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/cfrontend/Cshmgenproof.v#L33) defines `match_prog`; `transf_program_match` (:36) derives it from successful `transl_program`. `match_cont` (:1494) carries translation equations for loop continuations; `match_states` (:1540), `transl_step` (:1710), initial/final state lemmas and `transl_program_correct` (:2015) compose a forward simulation under `TRANSL : match_prog prog tprog` (:1117). The proof relates the *actual successful translator*, rather than an independently selected target. [common/Errors.v](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/common/Errors.v#L47) defines `res` (OK/Error), `bind` (:56) and `monadInv` (:182); inversion of success exposes each subtranslation equation. Rejecting an input is not a correctness violation of this conditional theorem and does not prove language coverage.

We also located [cfrontend/Cminorgenproof.v](https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/cfrontend/Cminorgenproof.v), but use Cshmgen's inspected mechanism for proposals. Neither C pass supplies Solidity checked-panic preservation. Difference from ours: Lower.lean:419-543 threads fresh flags through opaque partial recursion; G19/AssignmentWhileBreak.lean:74 has no translator-success equation. Reuse the success-conditioned relation and control invariant, not C's exit-depth representation or undefined-behavior assumptions.

### CakeML: functional evaluation relation plus verified compiler equations

At **58720ae1c69f86a79fec68749b0089ca6a3bb473**, [compiler/backend/proofs/source_to_flatProofScript.sml](https://github.com/CakeML/cakeml/blob/58720ae1c69f86a79fec68749b0089ca6a3bb473/compiler/backend/proofs/source_to_flatProofScript.sml#L4460), `compile_correct` (:4460) mutually relates expression, pattern-match and declaration evaluation to the output of `compile_exps` / `compile_pes` / declaration compilation. Its premises include `invariant`, environment relations and absence of source type-error abort; conclusions include `result_rel` and `s_rel`. `invariant_def` (:2828) and `invariant_dec_clock` (:2981) make the clock/state relation explicit. `compile_prog_semantics` (:6263), `compile_flat_correct` (:6372) and `compile_semantics` (:6393) lift to semantics, under `precondition_def` (:6386) and non-Fail source semantics. [compiler/backend/source_to_flatScript.sml](https://github.com/CakeML/cakeml/blob/58720ae1c69f86a79fec68749b0089ca6a3bb473/compiler/backend/source_to_flatScript.sml) supplies the executable definitions; this is a verified pass, not merely validation of sampled outputs.

[translator/ml_translatorScript.sml](https://github.com/CakeML/cakeml/blob/58720ae1c69f86a79fec68749b0089ca6a3bb473/translator/ml_translatorScript.sml#L42) separately defines `Eval_def` (:42), `AppReturns_def` (:51) and `Arrow_def` (:61): certificates relate a generated expression/function value to a HOL value/property through evaluation. This is a useful model for proof-producing elaboration; it is not a theorem about Solidity's elaborator or a generic proof that every partial program terminates.

Difference from ours: Source/Agreement/NormalComposition.lean:30 `normal_cons` composes normal-local obligations, while the missing control/error/output association remains in NormalStatement.lean:6-23. A CakeML-style clock relation does not permit us to identify source horizon with target fuel or physical gas. No direct imperative while/break lowering theorem from CakeML was verified in this bounded search; pattern/expression compilation is the evidence used.

### KEVM: operational EVM rules and reachability specifications, not a Solidity compiler proof

At **fbb2edbb8e84bb05b6ba7a255ce1f44f76051ad1**, [kevm-pyk/src/kevm_pyk/kproj/evm-semantics/evm.md](https://github.com/runtimeverification/evm-semantics/blob/fbb2edbb8e84bb05b6ba7a255ce1f44f76051ad1/kevm-pyk/src/kevm_pyk/kproj/evm-semantics/evm.md#L339) defines `#execute` and `#next`: configuration rewriting executes opcodes with stack/gas checks and exceptional exits. [media/201908-trufflecon/add-overflow-spec.k](https://github.com/runtimeverification/evm-semantics/blob/fbb2edbb8e84bb05b6ba7a255ce1f44f76051ad1/media/201908-trufflecon/add-overflow-spec.k#L3), module `ADD-OVERFLOW-SPEC`, gives a reachability-style `rule` for `#next [ ADD ]`: stack output is `chop(W0 +Int W1)`, PC advances, gas falls by `Gverylow`, under sufficient-gas/non-underflow premises. This is a historical specification example in the pinned tree, not a newly reproduced successful proof run. README.md:191 names `make test-proof` and Verified Smart Contracts.

Neither this rule nor `#execute` relates Solidity/Yul input to compiled bytecode or certifies loop/unchecked elaboration. They give a target semantics and proof language for concrete execution claims. Difference from ours: G19's hand-built execution theorems already play the bounded semantic role; replacing them with bytecode reachability would still leave Lower.lean:543,707 unconnected and add an external trust bridge. No universal negative claim about every KEVM-related project is needed.

### Yul: explicit control modes; semantics does not imply compiler correctness

At **047f63070309f436b66c61e276ab3b6d1169265a**, [EvmYul/Yul/Interpreter.lean](https://github.com/NethermindEth/EVMYulLean/blob/047f63070309f436b66c61e276ab3b6d1169265a/EvmYul/Yul/Interpreter.lean#L556), `exec` (:556) handles `.For`, `.Continue`, `.Break`, `.Leave` (:613-616); `loop` (:621) consumes explicit fuel, reports `.OutOfFuel`, evaluates the condition, consumes break, propagates leave, and executes post after continue. This supplies a runnable semantic account of the abrupt outcomes our flags must represent. No lowering correctness lemma was located in these inspected files. README.md calls the model work in progress. We do not claim a Lean/Isabelle/K cross-system proof.

At **2ec5173f2b6366832dede8b4fcd958f5c211d1a1**, [docs/yul.rst](https://github.com/ethereum/solidity/blob/2ec5173f2b6366832dede8b4fcd958f5c211d1a1/docs/yul.rst#L615) specifies evaluation `E` with global/local state and modes regular/break/continue/leave; its ForLoop clause (:664) handles post and scope restriction. This is specification prose, not a checked compiler theorem. [libyul/optimiser/ForLoopConditionIntoBody.cpp](https://github.com/ethereum/solidity/blob/2ec5173f2b6366832dede8b4fcd958f5c211d1a1/libyul/optimiser/ForLoopConditionIntoBody.cpp#L35), `ForLoopConditionIntoBody::operator()`, moves a nontrivial condition into a leading negated conditional break and sets the condition true. [libyul/optimiser/ForLoopInitRewriter.cpp](https://github.com/ethereum/solidity/blob/2ec5173f2b6366832dede8b4fcd958f5c211d1a1/libyul/optimiser/ForLoopInitRewriter.cpp), `ForLoopInitRewriter::operator()`, moves pre-statements outside the loop. These are implementation examples with no preservation theorem in the inspected files.

Difference from ours: Lower.lean:495-500 already uses condition-into-body for a particular effectful while case. Neither that similarity nor Yul's wrapping word arithmetic proves `uncheckStmts` correct for typed Solidity: widths, panics, calls and evaluation order remain obligations. Solc SMTChecker documentation was inspected as context, not cited as proof of the optimiser. **UNVERIFIED and excluded from proposals:** remembered Isabelle/K Yul lowering theorems, a general solc optimiser proof, and a direct CakeML imperative loop-lowering certificate; no exact supporting lemma was located. This is a bounded search limitation, not evidence that such work cannot exist.

## We already do this

| Verified mechanism | Existing local counterpart at pinned base | Concrete remaining difference |
|---|---|---|
| CompCert `match_states` + step simulation tied to successful `transl_statement` | G19/AssignmentWhileBreak.lean:74 proves both executions and a mapped post-state relation | G19 target is `code`, not the actual elaborator result; need output association and a compositional control relation |
| CompCert error-monad inversion | Syntax/Elab/Values.lean:651,654 `ElabM` / `ElabM.lift` expose an Except error boundary | no success equation theorem through partial lowering, fresh state and intrinsic elaboration |
| CakeML `compile_correct` using result/environment/state relations | G19/AssignmentForContinue.lean:186 explicitly carries maps, Boolean reflection and `falseValue`; Source/Agreement/NormalComposition.lean:30 `normal_cons` composes normal clauses | normal-only composition cannot carry return/break/continue, error journal or a compiler equation |
| Certificate as semantic evidence (`Eval_def`, `Arrow_def`) | Source/Agreement/NormalStatement.lean:23 names the desired semantic obligation; G19 `correct` proves bounded real executions | no certificate connecting the exact raw input, successful generated output and resolved source association |
| Yul abrupt modes and loop post handling | Syntax/Elab/Lower.lean:419,435,483 tracks `Abrupt` plus flags; G19/AssignmentWhileContinue.lean:86 and AssignmentForContinue.lean:186 distinguish continuations | need generic flag invariant, scope projection and return propagation across nests |
| Condition-into-body normalisation in solc | Syntax/Elab/Lower.lean:495-500 already rewrites an effectful while condition | similar code shape is not proof; condition effects and fresh guard variables still require association |
| KEVM gas-aware opcode specification | G19/AssignmentWhileBreak.lean:74 already proves fixed model execution, not gas | bytecode reachability cannot fill the raw elaboration gap, and would add another endpoint |

### Required bridge, independent of implementation choice

A meaningful endpoint must quantify over (1) the resolved Source statement/body and its raw-input association, (2) the actual successful raw transformation with incoming/outgoing scope, fresh counter and memo, (3) the actual successful intrinsic elaboration of that output, and (4) the semantic relation whose target is that very elaborated `Prog`. Equal-looking printed output is insufficient. Raw syntax equality may be a useful intermediate equation; it is not equality with G19's intrinsically typed `code` without the elaboration equation and context transport.

For reuse, expose one compositional association/simulation interface with sequence, conditional, block and abrupt-outcome cases; use existing G19 results as verified leaves or controls for that interface. Do not add a second `correct` theorem for each raw spelling. Existing fixed shapes alone cannot inductively prove arbitrary nested loops: generic loop/control induction is new work. Any certificate route must reject unsupported association rather than accept a supplied proof premise as evidence. Coverage/refusal accounting remains separate from soundness of accepted cases.
