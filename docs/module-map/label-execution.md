# Label execution
| Module | Purpose |
|---|---|
| `Backend/LabelExec/Step.lean`, `Backend/LabelExec/Fetch.lean`, `Backend/LabelExec/Packets.lean` | Byte-PC step over the numeric slice and JUMP/JUMPI/JUMPDEST; fetch behind a prefix; branch packets ([label execution](../feature-work/backend-label-exec.md)). |
| `Backend/LabelExec/Assembly.lean`, `Backend/LabelExec/Loops.lean`, `Backend/LabelExec/ScalarTransfer.lean` | Assembled jumps and tests; top-level loop header/backedge; `Scalar.step` lifting. |
| `Backend/LabelExec/Placement.lean`, `Backend/LabelExec/Checks.lean` | Arbitrarily placed local loop packets at whole-runtime base zero; standalone assembled-loop witness and negative controls. |
| `Backend/LabelExec/LiteralLoops.lean`, `Backend/LabelExec/LiteralChecks.lean` | Actual head/PUSH-to-test composition for literal conditions; zero/nonzero assembled entry controls, no reached-test premise. |
| `Backend/LabelExec/Boundaries.lean`, `Backend/LabelExec/LoopExit.lean`, `Backend/LabelExec/LoopExitControls.lean` | Actual indexed fetch/tag execution and six-step zero-loop exit; skipped unsupported-body and EOF controls. |
| `Backend/LabelExec/Fragment.lean`, `Backend/LabelExec/FragmentSound.lean`, `Backend/LabelExec/FragmentControls.lean` | Intrinsic stack-height/capacity refinement of existing numeric code and Block; actual one-step successor derivation and value-frame/capacity countercontrols. |
| `Backend/Transient/{State,Instructions,TypedSource,Code,Frames,Controls,SourceFrames}.lean` | P7 transient target: owner-indexed word bank, executed TLOAD/TSTORE code, selected bool Source correspondence, reset and local callback rollback; see [P7](../feature-work/p7-transient-target.md). |
| `Backend/Transient/{WordSource,WordControls}.lean` | `Val.word` Source port and signed/unsigned write/reset controls with explicit selected-slot/default premises. |
| `Backend/Transient/{Mixed,SourceCallback}.lean` | Persistent/memory/transient composition under reset, and Source environment callback execution with caller-state, static, revert and timeout controls. |

## G46.05 direct hash-query receipts (optional Bridge)
| Module (under `Bridge/SolidityBridge/`) | Purpose |
|---|---|
| `HashBridge/Queries.lean`, `HashBridge/Step.lean`, `HashBridge/Layout.lean` | Reused actual opaque digest/query and conditional storage-region interfaces. |
| `HashBridge/Prefix.lean`, `HashBridge/PrefixControls.lean` | Actual explicit-step query receipts, derived KECCAK frame, repeated-input and fuel controls; [scope](../feature-work/hash-direct-prefix.md). |
| `HashBridge/ChargedGuard.lean`, `HashBridge/Charged.lean`, `HashBridge/ChargedControls.lean` | Exact KECCAK memory/base/check order and all-fuel fetched-X-to-query receipt with full actual successor fields; logical charge/fuel/static controls. |
| `ExternalEvm/OutcomeDriver.lean` | Reused owned generic observation of pinned X checks/step/terminal dispatch; no replacement evaluator. |
| `HashBridge/Frame.lean`, `HashBridge/FrameSound.lean`, `HashBridge/FrameHash.lean`, `HashBridge/FrameControls.lean` | Recursive direct-query refinement of existing driver cuts; all-fuel existence/erasure and same-KECCAK-head continuation; error-retains-query control. |
| `HashBridge/QueryShape.lean`, `HashBridge/QueryUnique.lean`, `HashBridge/QueryControls.lean` | Fixed-state/fuel query-list uniqueness and unique existence; forbids favorable empty receipts after an executed hash. |
| `HashBridge/{QueryCut,CutSound,HashCuts,CutControls}.lean` | Checked same-run query cuts, residual execution and actual hash/error client |
| `HashBridge/CutComposition.lean`, `HashBridge/TwoHashCuts.lean` | Same-run cut grafting and conditional two-checked-hash client with derived residual receipt. |
| `HashBridge/PairControls.lean` | Concrete two-KECCAK edge producer and composed symbolic two-query/error cut. |
| `HashBridge/XiQueries.lean`, `HashBridge/XiControls.lean` | Actual public-Xi direct-query soundness/existence/uniqueness and fresh-empty-stack underflow control. |
| `HashBridge/ThetaQueries.lean`, `HashBridge/ThetaControls.lean` | Public CODE-message direct-query soundness/existence/uniqueness, exact result policy and handled-child checkpoint control. |
| `HashBridge/CallQueries.lean`, `HashBridge/CallControls.lean` | Actual call-operation CODE query receipt, reply/state installation and nonuniform low-fuel/depth control. |
| `ExternalEvm/{DriverPush,ChargedDispatch,RequireCut,RequireLocalCut,RequireLocalState,StaticcallDriver}.lean` | Reused committed owned driver closure; five exact files, one unused-simp deletion in StaticcallDriver. |
| `HashBridge/StaticQueries.lean`, `HashBridge/StaticQueryControls.lean` | Checked STATICCALL child/caller query provenance and actual fuel/check ordering controls. |
- `Yul/EvmSigned.lean`, `Yul/Checks/EvmSigned.lean`: shared-word signed readings, bounded integer encoding and universal SDIV/SMOD/SLT/SGT target-step agreement, with kernel boundary/composition/refusal controls.
- Frontend/Yul/{Grammar,DeclarationParse,ClosedParse,WordParse,OccurrenceParse,ScopedParse,Parsing}: checked source parsing composed with the core Yul certificates; declaration namespaces remain Solidity.Yul.
- Frontend/Yul/Checks/{Parsing,DeclarationParsing,ClosedSyntax,WordSyntax,Occurrences,ScopedSyntax}: parser witnesses and refusal controls separated from pure preparation controls.
- Yul/EvmArithmetic: unsigned arithmetic and two-step wrapped multiplication/division correspondence to the existing target machine. Yul/Checks/EvmArithmetic: intrinsic expression, fuel, overflow, zero and malformed-stack controls.
- Yul/EvmBitwise: comparison, bitwise, shift and EXP correspondence to actual target steps. Yul/Checks/EvmBitwise: mixed intrinsic/target execution and boundary/refusal controls.
- Yul/RawSourceVoidReturn: actual Source void-return short-circuit transport with exact raw-frame retention and explicit clean projection. Yul/Checks/RawSourceVoidReturn: dirty-frame, skipped declaration-tail, horizon and return-index controls.
- Yul/RawSourceReturnControl: void-return transport through do/while, unchecked and literal while, plus existing initializer-refusal law. Yul/Checks/RawSourceReturnControl: skipped-assignment, dirty-frame, flow and typed-tail controls.
- Yul/RawLocalDeclaration: context-indexed local snapshot and concrete Boolean declaration Source correspondence. Yul/Checks/RawLocalDeclaration: executed context growth, shifted dirty-word, timeout and full-prefix controls.
- Yul/RawLocalScope: executed Boolean declaration/scope closure, exact Source restoration and existing adapter implementation. Yul/Checks/RawLocalScope: precise horizons, dirty-frame and two-scope composition controls.
- Yul/RawDefaultDeclaration: typed constant-default lookup and Source declaration correspondence, including all integer widths. Yul/Checks/RawDefaultDeclaration: actual uint8/uint256, shifted dirty-prefix and helper-boundary controls.
- Yul/RawDefaultScope: concrete certified-default declaration/scope composition, integer Source laws and adapters. Yul/Checks/RawDefaultScope: exact scope/mixed-adapter horizons and full dirty-frame controls.
- Yul/RawLiteralInitialization: concrete Boolean literal initializer Source law and exact snapshot preservation. Yul/Checks/RawLiteralInitialization: inhabited true initializer, both-value/horizon, dirty-prefix and nondefault controls.
- Yul/RawLiteralScope: concrete Boolean initializer/scope Source composition, frame correspondence and typed adapters. Yul/Checks/RawLiteralScope: both literals, exact horizons and mixed literal/default dirty-frame controls.
- Yul/RawIntegerInitialization: all-width in-range literal conversion, typing and Source declaration execution beside raw locals. Yul/Checks/RawIntegerInitialization: signed/unsigned/wide boundaries, refusals, dirty-prefix and actual Source item composition.
- Yul/RawIntegerScope: concrete in-range integer initializer/scope Source composition, frame correspondence and typed adapters. Yul/Checks/RawIntegerScope: boundaries, precise horizons, mixed scopes and nonempty-execution controls preserving dirty locals.
- Yul/LocalBoolInitialization: actual certified Boolean expression declaration execution, typed success/failure contexts and clean Source correspondence. Yul/Checks/LocalBoolInitialization: partial-effect timeout, raw-copy refusal, short-circuit and concrete Source controls.
- Yul/LocalBoolScope: actual Boolean initializer scope closure with retained partial effects and concrete Source block correspondence. Yul/Checks/LocalBoolScope: assignment/short-circuit horizons, raw-copy and independent Source controls.
- Yul/LocalBoolBinding: concrete context-growing declaration/body composition with stage-typed failures and Source correspondence. Yul/Checks/LocalBoolBinding: new-local reads/writes, partial-state stages, raw-copy and independent Source controls.
- Yul/LocalBoolItems: intrinsic Boolean item-list certificates, reached-context partial states and concrete Source induction. Yul/Checks/LocalBoolItems: multiple bindings, cross-binding writes, staged failures, raw-copy and Source controls.
- Yul/LocalBoolItemScope: certificate-derived raw suffix restoration and concrete Source scope composition. Yul/Checks/LocalBoolItemScope: multi-declaration closure, retained partial contexts, dirty-temporary and Source controls.
- Yul/LocalBoolIf.lean and Yul/Checks/LocalBoolIf.lean: conditional scope execution and clean-input Source agreement with partial-effect controls.
- Yul/LocalBoolIfElse.lean and Yul/Checks/LocalBoolIfElse.lean: conditional selection of independently indexed item scopes with concrete clean Source agreement.
| `Yul/Adapters/AllocatedComputedFrame{,Controls}` | Actual allocation to complete canonical physical frame and whole-source unchanged writeback, with derived enlarged-heap support. |
| `Yul/Adapters/P6CalldataHash{,Controls}` | Actual calldata conversion/allocation, bounded P6 copy and target KECCAK256 composition with explicit per-input concrete hash premise. |
| `Bridge/SolidityBridge/HashBridge/QueryPrepend.lean` | Bounded revert-outcome-specs checkpoint; typed scope and retained premises are in the module. |
| `Bridge/SolidityBridge/HashBridge/StopQueries.lean` | Bounded revert-outcome-specs checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/HashBridge/XiContextControls.lean` | Bounded revert-outcome-specs checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/HashBridge/XiContextMessage.lean` | Bounded revert-outcome-specs checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/HashBridge/XiContextRun.lean` | Bounded revert-outcome-specs checkpoint; typed scope and retained obligations are stated in the module. |
| `Bridge/SolidityBridge/HashBridge/XiContextSetup.lean` | Bounded revert-outcome-specs checkpoint; typed scope and retained obligations are stated in the module. |
