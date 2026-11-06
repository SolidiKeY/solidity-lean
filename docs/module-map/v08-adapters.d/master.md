<!-- Retained V17 lane modules not yet present in the published map. -->
| `Backend/StructuredFlow/ConditionalSourceCompiler.lean` | Compile the existing V07-related conditional statement, preserving its actual Source run and reached map as well as the intrinsic compiler contract. |
| `Backend/StructuredFlow/ConditionalSourceCompilerControls.lean` | Inhabited witnesses and negative controls for the corresponding mapped lowering/compiler component. |
| `Backend/StructuredFlow/MappedBranch.lean` | Branch code over the actual V07-mapped effectful condition. |
| `Backend/StructuredFlow/MappedBranchControls.lean` | Inhabited witnesses and negative controls for the corresponding mapped lowering/compiler component. |
| `Backend/StructuredFlow/ScopedMappedSequence.lean` | Drop the mapped branch's private capture in the existing intrinsic block, then compile a continuation in the reached caller context. |
| `Backend/StructuredFlow/ScopedMappedSequenceControls.lean` | Inhabited witnesses and negative controls for the corresponding mapped lowering/compiler component. |
| `Lowering/G19/AssignmentDoWhileBreak.lean` | A mapped assignment in a do-while body followed by unconditional break. |
| `Lowering/G19/AssignmentDoWhileBreakControls.lean` | Mixed mapped clients: body writes once, arbitrary trailing condition is skipped. |
| `Lowering/G19/AssignmentDoWhileContinue.lean` | A mapped assignment followed by continue skips every remaining body item. |
| `Lowering/G19/AssignmentDoWhileContinueControls.lean` | Actual mixed mapped clients and effectful/declaration suffix rejection. |
| `Lowering/G19/AssignmentForBreak.lean` | One mapped for-loop initializer followed by an immediate break. |
| `Lowering/G19/AssignmentForBreakControls.lean` | Real mapped initializer writes and skipped optional for-loop post expressions. |
| `Lowering/G19/AssignmentReturnFlagControls.lean` | Inhabited map-guided G19 clients over V07's actual mixed Bool/integer/ memory/storage fixture. |
| `Lowering/G19/AssignmentWhileBreak.lean` | One mapped effectful while shape: a Boolean local-assignment condition and an immediate break body. |
| `Lowering/G19/AssignmentWhileBreakControls.lean` | Actual mixed V07/P12 inputs. |
| `Lowering/G19/ConditionalSequence.lean` | Actual conditional statement followed by an assignment in its caller context. |
| `Lowering/G19/ConditionalSequenceControls.lean` | Inhabited witnesses and negative controls for the corresponding mapped lowering/compiler component. |
| `Lowering/G19/ReturnTail.lean` | Consume the existing mapped return selector to suppress a real caller assignment. |
| `Lowering/G19/ReturnTailControls.lean` | Inhabited witnesses and negative controls for the corresponding mapped lowering/compiler component. |
| `Backend/StructuredFlow/ConditionalSequenceCompiler.lean` | Compiler connection for the existing V07-related conditional followed by an assignment in its reached caller context. |
| `Backend/StructuredFlow/ConditionalSequenceCompilerControls.lean` | Inhabited Source/compiler continuation witnesses, frame observations and wrong-slot controls. |
| `Lowering/G19/AssignmentWhileReset.lean` | Mapped Boolean assignment while with an actual resetting body and intrinsic loop. |
| `Lowering/G19/AssignmentWhileResetControls.lean` | Inhabited Source/compiler loop, alias and prefix-only omission controls. |
| `Lowering/G19/AssignmentWhileContinue.lean` | Mapped resetting while proves continue skips arbitrary suffixes and retests the condition. |
| `Lowering/G19/AssignmentWhileContinueControls.lean` | Inhabited continue/retest and donor-observation controls with reused compiled loop witnesses. |
| `Backend/StructuredFlow/WhileContinueCompiler.lean` | Actual emitter and compiler connection for the existing V07-related continue/retest loop. |
| `Backend/StructuredFlow/WhileContinueCompilerControls.lean` | Inhabited Source/compiler join, semantic guard mutation and corrupted-entry simulation controls. |
| `Lowering/G19/AssignmentForContinue.lean` | Actual mapped for/continue/post proof with complete scoped structural value extraction and replay. |
| `Lowering/G19/AssignmentForContinueControls.lean` | Inhabited post-after-continue and fixed-resource omitted-post Source controls. |
| `Solidity/Backend/StructuredFlow/DoWhileBreakCompiler.lean` | Mapped G19 immediate-break do-while Source certificate to existing scoped physical compiler. |
| `Solidity/Backend/StructuredFlow/DoWhileBreakCompilerControls.lean` | Inhabited pipeline/value/fuel controls and skipped-condition/omitted-body negatives. |
| `Solidity/Backend/StructuredFlow/DoWhileContinueCompiler.lean` | Mapped G19 do-while continue with skipped body suffix and literal-false exit to existing physical assignment compiler. |
| `Solidity/Backend/StructuredFlow/DoWhileContinueCompilerControls.lean` | Inhabited pipeline/value/fuel controls and skipped-suffix/omitted-body negatives. |
| `Solidity/Backend/StructuredFlow/WhileReturnCompiler.lean` | Mapped G19 while/bare-return classification to the existing captured-selector physical compiler prefix; no EVM RETURN. |
| `Solidity/Backend/StructuredFlow/WhileReturnCompilerControls.lean` | Inhabited pipeline/value/fuel controls and wrong outcome/capture/base negatives. |
| `Solidity/Backend/StructuredFlow/WhileBreakCompiler.lean` | Mapped assignment-condition/immediate-break Source certificate to the existing scoped physical compiler. |
| `Solidity/Backend/StructuredFlow/WhileBreakCompilerControls.lean` | Inhabited pipeline/value/fuel controls and visible false-condition/omitted-code/wrong-base negatives. |
| `Backend/StructuredFlow/ReturnTailCompiler.lean` | Actual compiler of mapped captured-return selection and a conditionally suppressed primitive caller assignment. |
| `Backend/StructuredFlow/ReturnTailCompilerControls.lean` | Inhabited true/false write controls, eager/omitted suffix negatives and caller-condition/private-selector alias observation. |
| `Lowering/G19/ReturnPair.lean` | V07-related captured return across two suffix assignments, rereading the second donor from reached state. |
| `Lowering/G19/ReturnPairControls.lean` | Inhabited return/fallthrough, visible second write, stale donor and omitted-second controls. |
| `Backend/StructuredFlow/ReturnPairCompiler.lean` | Actual compiler composition for mapped captured return and two reached-state suffix assignments; explicit fragment/capacity and entry premises. |
| `Backend/StructuredFlow/ReturnPairCompilerControls.lean` | Inhabited both-pipeline runs, full native snapshot and typed/native suffix mutation negatives. |
| `Lowering/G19/AssignmentDoWhileReturn.lean` | Mapped do-while body assignment then bare return; arbitrary trailing condition skipped, true fresh flag independent of assigned value. |
| `Lowering/G19/AssignmentDoWhileReturnControls.lean` | Both-pipeline/checked-mode true and false body runs, same-slot, wrong flag, skipped-effect and return classification controls. |
| `Backend/StructuredFlow/DoWhileReturnCompiler.lean` | Actual compiler composition for mapped do-while assignment/bare-return; explicit entry, fragment and capacity. |
| `Backend/StructuredFlow/DoWhileReturnCompilerControls.lean` | Both-pipeline/checked-mode native snapshots, independent true capture, wrong flag and leaked trailing-write native mutations. |
| `Lowering/G19/ConditionalReturn.lean` | V07-related conditional assignments then unconditional bare return, scoped branch temps and independent true return flag. |
| `Lowering/G19/ConditionalReturnControls.lean` | Both-pipeline/checked-mode branch writes, reached-state donor, wrong donor/flag and Source return classification controls. |
| `Backend/StructuredFlow/ConditionalReturnCompiler.lean` | Actual compiler composition for V07-related conditional assignments followed by captured bare return. |
| `Backend/StructuredFlow/ConditionalReturnCompilerControls.lean` | Both-pipeline native full-cell/stack observations and compiled donor/flag mutation refusals. |
| `Lowering/G19/ConditionalReturnContinuation.lean` | V07-related conditional return suppresses arbitrary unreachable Source and intrinsic target continuations. |
| `Lowering/G19/ConditionalReturnContinuationControls.lean` | Both-pipeline/checked-mode return continuation controls and eager caller-write rejection for both guards. |
| `Backend/StructuredFlow/ConditionalContinuationCompiler.lean` | Actual compiler of V07-related captured-return continuation guard with whole-tail fragment check. |
| `Backend/StructuredFlow/ConditionalContinuationCompilerControls.lean` | Full native cell/stack guard observations and separately compiled eager caller-write rejection. |
| `Lowering/G19/AssignmentBlocks.lean` | Arbitrary finite ordered Boolean-copy blocks with actual Source/typed runs and full V07 context-map transport. |
| `Lowering/G19/AssignmentBlocksControls.lean` | Heterogeneous unsigned/Boolean frame, reached-read ordering, reversal, repetition and same-slot controls. |
| `Backend/StructuredFlow/AssignmentBlocksCompiler.lean` | Actual ordered Boolean-block compiler with mapped entry, full fragment/capacity premises; extraction provenance remains NONPASS. |
| `Backend/StructuredFlow/AssignmentBlocksCompilerControls.lean` | Full native cell/stack order, repetition and same-slot controls with factored exact execution. |
| `Lowering/G19/AssignmentForReturn.lean`, `Lowering/G19/AssignmentForReturnControls.lean` | G19 map-guided for-loop immediate return with arbitrary skipped post, actual Source runs, captured target flag and mixed-state controls ([scope](../feature-work/roadmap-g19-for-return.md)). |
| `Backend/StructuredFlow/ForContinueCompiler.lean`, `Backend/StructuredFlow/ForContinueCompilerControls.lean` | Actual mapped for/continue/post to existing loop-compiler join with physical observations and negative controls ([scope](../feature-work/roadmap-g36-for-continue-compiler.md)). |
| `Backend/StructuredFlow/ForReturnCompiler.lean`, `Backend/StructuredFlow/ForReturnCompilerControls.lean` | Actual for-loop Source outcome/captured-flag compiler connection, full physical snapshots and capture/base/outcome negatives ([scope](../feature-work/roadmap-g36-for-return-compiler.md)). |
| `Backend/StructuredFlow/ForBreakCompiler.lean`, `Backend/StructuredFlow/ForBreakCompilerControls.lean` | Actual mapped for-initializer/break to scoped-prefix compilation, exact exit fragment, full snapshots and initializer/base/post negatives ([scope](../feature-work/roadmap-g36-for-break-compiler.md)). |
