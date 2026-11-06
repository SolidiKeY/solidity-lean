# Source agreement producers

| `Source/Agreement/NormalBoolBindings.lean` | Actual boolean literal initializer normal-step producer and two-initializer composition, retaining primitive locals only. |
| `Source/Agreement/NormalBoolControls.lean` | Concrete two-literal importing client, actual Source horizon controls and false-versus-true initializer countercontrol. |
| `Source/Agreement/NormalStep.lean` | Explicit per-statement normal-result producer premise over existing Source and model evaluators. |
| `Source/Agreement/NormalCuts.lean` | Actual Source sequence/journal decomposition; normal-tail inversion without chosen intermediate state. |
| `Source/Agreement/NormalComposition.lean` | Conditional nil/cons/two-statement proof of the existing normal-locals agreement obligation. |
| `Source/Agreement/NormalControls.lean` | Concrete no-op producer/importer and timeout, early-return and incompatible-association controls. |
| `Source/Agreement/NormalDefaults.lean` | Concrete bool/uint256/int256 default-declaration step producers and actual two-step composition. |
| `Source/Agreement/NormalDefaultControls.lean` | Both evaluator histories, ordered local-tail/state preservation, horizon and wrong-default controls. |
| `Source/Agreement/NormalStatement.lean` | One-way normal-locals target; conditional sequence proofs are separate, and general Source/model agreement remains open. |
| `Source/Agreement/NormalBoolAssign.lean` | Concrete head-local boolean assignment and initializer-overwrite normal-step producers; actual local tail retained. |
| `Source/Agreement/NormalBoolAssignControls.lean` | Both interpreter histories, total initial-locals client, Source horizon failures and wrong-value countercontrol. |
| `Source/Agreement/BoolSlot.lean` | Existing intrinsic indices at an arbitrary typed primitive prefix and actual local-set correspondence. |
| `Source/Agreement/BoolSlotAssign.lean` | Arbitrary-position boolean assignment producer, internally instantiated normal client and short-horizon control. |
| `Source/Agreement/BoolSlotControls.lean` | Actual middle-slot Source/model preservation and a wrong-slot countercontrol. |
| `Source/Agreement/BoolSlotRead.lean` | Actual arbitrary-slot get correspondence, local-read initialization and later original-slot write producers. |
| `Source/Agreement/BoolSlotReadControls.lean` | Concrete read-copy/write histories and importing client; horizon and primitive-copy-versus-alias controls. |
| `Source/Agreement/BoolSlotNot.lean` | Actual local-read boolean negation initializer producer with internally derived operand and factored checked monad runs. |
| `Source/Agreement/BoolSlotNotControls.lean` | Total-initial-locals client, Source horizon and both negation polarity controls. |
| `Source/Agreement/BoolSlotConditional.lean` | Actual local-conditioned boolean literal initializer, with internally derived guard and preserved primitive locals. |
| `Source/Agreement/BoolSlotConditionalControls.lean` | Concrete conditional client, branch/horizon controls and separately scoped Source selected/unselected-write traces. |
| `Source/Agreement/BoolSlotAnd.lean` | Actual short-circuit conjunction initializer with corresponding local left operand and literal right operand. |
| `Source/Agreement/BoolSlotAndControls.lean` | Internally instantiated conjunction client, Source selected/skipped right-hand effects and fuel, and operator-distinction controls. |
| `Source/Agreement/BoolSlotOr.lean` | Actual short-circuit disjunction initializer with corresponding local left operand and literal right operand. |
| `Source/Agreement/BoolSlotOrControls.lean` | Internally instantiated disjunction client, reversed selected/skipped right-hand effects/fuel and operator-distinction controls. |
| `Source/Agreement/BoolSlotToggle.lean` | Actual computed-RHS boolean read-modify-write expression/statement producer, returning the new value and retaining exact local/state history. |
| `Source/Agreement/BoolSlotToggleControls.lean` | Internally instantiated computed-assignment client, low fuel/new-result controls and actual Source/model two-head-update restoration. |
| `Source/Agreement/BoolSlotReadWrite.lean` | Actual paired-index get/set, last-write and read-after-write restoration laws over existing locals/environments. |
| `Source/Agreement/BoolSlotRepeated.lean` | Both actual two-computed-update executions at arbitrary slots, with internally derived intermediate reads and normal composition. |
| `Source/Agreement/BoolSlotRepeatedControls.lean` | Both-run importing client, insufficient-horizon refusal and different-slot countercontrol. |
| `Source/Agreement/BoolSlotSaved.lean` | Fixed-code saved old copy followed by computed inverse update of the shifted original slot, through actual Source/model runs. |
| `Source/Agreement/BoolSlotSavedControls.lean` | Internally instantiated saved-copy client, horizon and polarity/liveness controls. |
| `Source/Agreement/PrimitiveSlot.lean` | Actual arbitrary-slot primitive read/write transport and normal initialization agreement, retaining signed/unsigned range evidence. |
| `Source/Agreement/PrimitiveSlotControls.lean` | Internally instantiated copy client, actual integer runs, insufficient horizon and wrong-value refusal. |
| `Source/Agreement/PrimitiveSlotAssign.lean` | Actual primitive old-head-to-deeper-slot assignment, concrete normal producer/client and exact insufficient-horizon control. |
| `Source/Agreement/PrimitiveSlotAssignControls.lean` | Mixed-type neighbor preservation, actual signed/unsigned writes and reversed-copy controls. |
| `Source/Agreement/PrimitiveSavedAssign.lean` | Actual primitive save-and-shifted-copy sequence, composed normal agreement/client and exact horizon-four timeout. |
| `Source/Agreement/PrimitiveSavedAssignControls.lean` | Saved/original head liveness, mixed neighbors and overwritten-target refusal controls. |
| `Source/Agreement/PrimitiveSlotReverse.lean` | Actual deeper-slot-to-head primitive assignment with internally derived operand, normal client and timeout. |
| `Source/Agreement/PrimitiveSlotReverseControls.lean` | Retained source/tail/neighbors and real opposite-direction controls. |
| `Source/Agreement/PrimitiveCopySequence.lean` | Both orders of concrete primitive copies, actual intermediate reads, normal agreements/clients and horizon-four timeouts. |
| `Source/Agreement/PrimitiveCopySequenceControls.lean` | Original-value survival by copy order, same-input model noncommutation and swap refusal controls. |
