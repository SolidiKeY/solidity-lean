import Lean
import Solidity.Source.Agreement.BoolSlot
import Solidity.Source.Agreement.BoolSlotAnd
import Solidity.Source.Agreement.BoolSlotAndControls
import Solidity.Source.Agreement.BoolSlotAssign
import Solidity.Source.Agreement.BoolSlotConditional
import Solidity.Source.Agreement.BoolSlotConditionalControls
import Solidity.Source.Agreement.BoolSlotControls
import Solidity.Source.Agreement.BoolSlotNot
import Solidity.Source.Agreement.BoolSlotNotControls
import Solidity.Source.Agreement.BoolSlotOr
import Solidity.Source.Agreement.BoolSlotOrControls
import Solidity.Source.Agreement.BoolSlotRead
import Solidity.Source.Agreement.BoolSlotReadControls
import Solidity.Source.Agreement.BoolSlotReadWrite
import Solidity.Source.Agreement.BoolSlotRepeated
import Solidity.Source.Agreement.BoolSlotRepeatedControls
import Solidity.Source.Agreement.BoolSlotSaved
import Solidity.Source.Agreement.BoolSlotSavedControls
import Solidity.Source.Agreement.BoolSlotToggle
import Solidity.Source.Agreement.BoolSlotToggleControls
import Solidity.Source.Agreement.Locals
import Solidity.Source.Agreement.NormalBoolAssign
import Solidity.Source.Agreement.NormalBoolAssignControls
import Solidity.Source.Agreement.NormalBoolBindings
import Solidity.Source.Agreement.NormalBoolControls
import Solidity.Source.Agreement.NormalComposition
import Solidity.Source.Agreement.NormalControls
import Solidity.Source.Agreement.NormalCuts
import Solidity.Source.Agreement.NormalDefaultControls
import Solidity.Source.Agreement.NormalDefaults
import Solidity.Source.Agreement.NormalStatement
import Solidity.Source.Agreement.NormalStep
import Solidity.Source.Agreement.Primitive
import Solidity.Source.Agreement.PrimitiveCopySequence
import Solidity.Source.Agreement.PrimitiveCopySequenceControls
import Solidity.Source.Agreement.PrimitiveSavedAssign
import Solidity.Source.Agreement.PrimitiveSavedAssignControls
import Solidity.Source.Agreement.PrimitiveSlot
import Solidity.Source.Agreement.PrimitiveSlotAssign
import Solidity.Source.Agreement.PrimitiveSlotAssignControls
import Solidity.Source.Agreement.PrimitiveSlotControls
import Solidity.Source.Agreement.PrimitiveSlotReverse
import Solidity.Source.Agreement.PrimitiveSlotReverseControls
import Solidity.Source.Agreement.PrimitiveTypes
import Solidity.Source.Calldata
import Solidity.Source.CalldataExamples
import Solidity.Source.Const
import Solidity.Source.ConstCheck
import Solidity.Source.Ctor
import Solidity.Source.Decls
import Solidity.Source.Decode
import Solidity.Source.DecodeExamples
import Solidity.Source.Elaborate
import Solidity.Source.ElaborateExamples
import Solidity.Source.Elaborated
import Solidity.Source.Eval
import Solidity.Source.Examples
import Solidity.Source.ExprProgress
import Solidity.Source.FailureCursor
import Solidity.Source.FailureResources
import Solidity.Source.Hoare
import Solidity.Source.Horizon
import Solidity.Source.HorizonDeploy
import Solidity.Source.Infer
import Solidity.Source.Inheritance
import Solidity.Source.InlineExamples
import Solidity.Source.Ledger
import Solidity.Source.Machine
import Solidity.Source.Observe
import Solidity.Source.Overloads
import Solidity.Source.Preservation.AllocatingControls
import Solidity.Source.Preservation.AllocatingFragment
import Solidity.Source.Preservation.AllocationBodyControls
import Solidity.Source.Preservation.AllocationControls
import Solidity.Source.Preservation.AllocationSites
import Solidity.Source.Preservation.ArrayLiteralControls
import Solidity.Source.Preservation.ArrayLiterals
import Solidity.Source.Preservation.CallFrames
import Solidity.Source.Preservation.CallerReferenceControls
import Solidity.Source.Preservation.Combinators
import Solidity.Source.Preservation.Controls
import Solidity.Source.Preservation.Encoding
import Solidity.Source.Preservation.EncodingArguments
import Solidity.Source.Preservation.EncodingVariantControls
import Solidity.Source.Preservation.EncodingVariants
import Solidity.Source.Preservation.Expressions
import Solidity.Source.Preservation.Fragment
import Solidity.Source.Preservation.FragmentControls
import Solidity.Source.Preservation.FrameControls
import Solidity.Source.Preservation.Frames
import Solidity.Source.Preservation.LocalFrames
import Solidity.Source.Preservation.MemberPacking
import Solidity.Source.Preservation.MemoryBodies
import Solidity.Source.Preservation.MemoryBodyCalls
import Solidity.Source.Preservation.MemoryBodyControls
import Solidity.Source.Preservation.MemoryBranchControls
import Solidity.Source.Preservation.MemoryExpressions
import Solidity.Source.Preservation.MemoryProgram
import Solidity.Source.Preservation.MemoryProgramControls
import Solidity.Source.Preservation.NewArrayFragment
import Solidity.Source.Preservation.NewArrayFragmentControls
import Solidity.Source.Preservation.Reads
import Solidity.Source.Preservation.ReferenceArguments
import Solidity.Source.Preservation.ReferenceReturnControls
import Solidity.Source.Preservation.ReferenceReturns
import Solidity.Source.Preservation.ResultValidity
import Solidity.Source.Preservation.StatementFrames
import Solidity.Source.Preservation.Statements
import Solidity.Source.Preservation.StorageCopyControls
import Solidity.Source.Preservation.ValueConversions
import Solidity.Source.Progress.AggregateDefaultControls
import Solidity.Source.Progress.AggregateDefaults
import Solidity.Source.Progress.AggregateReturnControls
import Solidity.Source.Progress.AllocationBodyCallControls
import Solidity.Source.Progress.AllocationBodyCalls
import Solidity.Source.Progress.AllocationReturns
import Solidity.Source.Progress.ArithmeticBuiltins
import Solidity.Source.Progress.BoundCatalogue
import Solidity.Source.Progress.BoundCatalogueControls
import Solidity.Source.Progress.BoundCataloguePanicControls
import Solidity.Source.Progress.BoundCatalogueParentControls
import Solidity.Source.Progress.BoundParentControls
import Solidity.Source.Progress.BoundParentPanicControls
import Solidity.Source.Progress.BoundParents
import Solidity.Source.Progress.BuiltinAdmission
import Solidity.Source.Progress.BuiltinControls
import Solidity.Source.Progress.BuiltinStatements
import Solidity.Source.Progress.CallComposition
import Solidity.Source.Progress.CallCompositionControls
import Solidity.Source.Progress.CheckedPrograms
import Solidity.Source.Progress.Controls
import Solidity.Source.Progress.EffectBodies
import Solidity.Source.Progress.EffectCatalogue
import Solidity.Source.Progress.EffectCatalogueControls
import Solidity.Source.Progress.EmitBuiltins
import Solidity.Source.Progress.ForwardingChain
import Solidity.Source.Progress.ForwardingChainControls
import Solidity.Source.Progress.ForwardingControls
import Solidity.Source.Progress.ForwardingReturns
import Solidity.Source.Progress.InitializedCalls
import Solidity.Source.Progress.InitializedChain
import Solidity.Source.Progress.InitializedChainControls
import Solidity.Source.Progress.InitializedControls
import Solidity.Source.Progress.InitializedLocals
import Solidity.Source.Progress.InitializedPrefixes
import Solidity.Source.Progress.InlineArrayParentControls
import Solidity.Source.Progress.InlineArrayParents
import Solidity.Source.Progress.LiteralBuiltinControls
import Solidity.Source.Progress.LiteralBuiltins
import Solidity.Source.Progress.NewArray
import Solidity.Source.Progress.NewArrayControls
import Solidity.Source.Progress.ParentArgumentControls
import Solidity.Source.Progress.ParentArgumentFlowControls
import Solidity.Source.Progress.ParentArguments
import Solidity.Source.Progress.ReadyArguments
import Solidity.Source.Progress.ReadyBodies
import Solidity.Source.Progress.ReadyBodyCalls
import Solidity.Source.Progress.ReadyBodyControls
import Solidity.Source.Progress.ReadyCatalogue
import Solidity.Source.Progress.ReadyCatalogueControls
import Solidity.Source.Progress.ReadyDefaults
import Solidity.Source.Progress.ReadyDispatchControls
import Solidity.Source.Progress.ReadyExpressionControls
import Solidity.Source.Progress.ReadyExpressions
import Solidity.Source.Progress.ReadyProgram
import Solidity.Source.Progress.ReadyProgramControls
import Solidity.Source.Progress.ReadyRebinding
import Solidity.Source.Progress.ReadyRebindingControls
import Solidity.Source.Progress.ReadyReturnControls
import Solidity.Source.Progress.ReadyReturns
import Solidity.Source.Progress.ReadyScopeControls
import Solidity.Source.Progress.RecoveryBuiltin
import Solidity.Source.Progress.ScalarBuiltinControls
import Solidity.Source.Progress.StructParentControls
import Solidity.Source.Progress.StructParents
import Solidity.Source.Resolve
import Solidity.Source.Resolved
import Solidity.Source.Semantics
import Solidity.Source.SemanticsExamples
import Solidity.Source.Session
import Solidity.Source.SessionExamples
import Solidity.Source.SoundnessExamples
import Solidity.Source.State
import Solidity.Source.StateExamples
import Solidity.Source.StmtProgress
import Solidity.Source.Syntax
import Solidity.Source.TryExamples
import Solidity.Source.Types
import Solidity.Source.Typing
import Solidity.Source.TypingExamples
import Solidity.Source.Unique
import Solidity.Source.Units
import Solidity.Source.Upstream
import Solidity.Source.UserOps
import Solidity.Source.Value
import Solidity.Source.ValueProgress
import Solidity.Source.WellFormed
import Solidity.Source.WellTyped
import Solidity.Source.World

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let some output ← liftIO (IO.getEnv "H62_API_OUTPUT")
    | throwError "H62_API_OUTPUT is required"
  let constants := env.constants.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let rows := constants.filterMap fun (n, ci) => do
    let idx ← env.getModuleIdxFor? n
    let mod := env.header.moduleNames[idx.toNat]!
    if !mod.toString.startsWith "Solidity.Source." then none else
      let kind := match ci with
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quotient"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
      some <| Json.mkObj [("module", toJson mod.toString), ("name", toJson n.toString),
        ("kind", toJson kind), ("universes", toJson (ci.levelParams.map Name.toString)),
        ("type_repr", toJson (reprStr ci.type))]
  let requested : List String := ["Solidity.Source.Agreement.BoolSlot", "Solidity.Source.Agreement.BoolSlotAnd", "Solidity.Source.Agreement.BoolSlotAndControls", "Solidity.Source.Agreement.BoolSlotAssign", "Solidity.Source.Agreement.BoolSlotConditional", "Solidity.Source.Agreement.BoolSlotConditionalControls", "Solidity.Source.Agreement.BoolSlotControls", "Solidity.Source.Agreement.BoolSlotNot", "Solidity.Source.Agreement.BoolSlotNotControls", "Solidity.Source.Agreement.BoolSlotOr", "Solidity.Source.Agreement.BoolSlotOrControls", "Solidity.Source.Agreement.BoolSlotRead", "Solidity.Source.Agreement.BoolSlotReadControls", "Solidity.Source.Agreement.BoolSlotReadWrite", "Solidity.Source.Agreement.BoolSlotRepeated", "Solidity.Source.Agreement.BoolSlotRepeatedControls", "Solidity.Source.Agreement.BoolSlotSaved", "Solidity.Source.Agreement.BoolSlotSavedControls", "Solidity.Source.Agreement.BoolSlotToggle", "Solidity.Source.Agreement.BoolSlotToggleControls", "Solidity.Source.Agreement.Locals", "Solidity.Source.Agreement.NormalBoolAssign", "Solidity.Source.Agreement.NormalBoolAssignControls", "Solidity.Source.Agreement.NormalBoolBindings", "Solidity.Source.Agreement.NormalBoolControls", "Solidity.Source.Agreement.NormalComposition", "Solidity.Source.Agreement.NormalControls", "Solidity.Source.Agreement.NormalCuts", "Solidity.Source.Agreement.NormalDefaultControls", "Solidity.Source.Agreement.NormalDefaults", "Solidity.Source.Agreement.NormalStatement", "Solidity.Source.Agreement.NormalStep", "Solidity.Source.Agreement.Primitive", "Solidity.Source.Agreement.PrimitiveCopySequence", "Solidity.Source.Agreement.PrimitiveCopySequenceControls", "Solidity.Source.Agreement.PrimitiveSavedAssign", "Solidity.Source.Agreement.PrimitiveSavedAssignControls", "Solidity.Source.Agreement.PrimitiveSlot", "Solidity.Source.Agreement.PrimitiveSlotAssign", "Solidity.Source.Agreement.PrimitiveSlotAssignControls", "Solidity.Source.Agreement.PrimitiveSlotControls", "Solidity.Source.Agreement.PrimitiveSlotReverse", "Solidity.Source.Agreement.PrimitiveSlotReverseControls", "Solidity.Source.Agreement.PrimitiveTypes", "Solidity.Source.Calldata", "Solidity.Source.CalldataExamples", "Solidity.Source.Const", "Solidity.Source.ConstCheck", "Solidity.Source.Ctor", "Solidity.Source.Decls", "Solidity.Source.Decode", "Solidity.Source.DecodeExamples", "Solidity.Source.Elaborate", "Solidity.Source.ElaborateExamples", "Solidity.Source.Elaborated", "Solidity.Source.Eval", "Solidity.Source.Examples", "Solidity.Source.ExprProgress", "Solidity.Source.FailureCursor", "Solidity.Source.FailureResources", "Solidity.Source.Hoare", "Solidity.Source.Horizon", "Solidity.Source.HorizonDeploy", "Solidity.Source.Infer", "Solidity.Source.Inheritance", "Solidity.Source.InlineExamples", "Solidity.Source.Ledger", "Solidity.Source.Machine", "Solidity.Source.Observe", "Solidity.Source.Overloads", "Solidity.Source.Preservation.AllocatingControls", "Solidity.Source.Preservation.AllocatingFragment", "Solidity.Source.Preservation.AllocationBodyControls", "Solidity.Source.Preservation.AllocationControls", "Solidity.Source.Preservation.AllocationSites", "Solidity.Source.Preservation.ArrayLiteralControls", "Solidity.Source.Preservation.ArrayLiterals", "Solidity.Source.Preservation.CallFrames", "Solidity.Source.Preservation.CallerReferenceControls", "Solidity.Source.Preservation.Combinators", "Solidity.Source.Preservation.Controls", "Solidity.Source.Preservation.Encoding", "Solidity.Source.Preservation.EncodingArguments", "Solidity.Source.Preservation.EncodingVariantControls", "Solidity.Source.Preservation.EncodingVariants", "Solidity.Source.Preservation.Expressions", "Solidity.Source.Preservation.Fragment", "Solidity.Source.Preservation.FragmentControls", "Solidity.Source.Preservation.FrameControls", "Solidity.Source.Preservation.Frames", "Solidity.Source.Preservation.LocalFrames", "Solidity.Source.Preservation.MemberPacking", "Solidity.Source.Preservation.MemoryBodies", "Solidity.Source.Preservation.MemoryBodyCalls", "Solidity.Source.Preservation.MemoryBodyControls", "Solidity.Source.Preservation.MemoryBranchControls", "Solidity.Source.Preservation.MemoryExpressions", "Solidity.Source.Preservation.MemoryProgram", "Solidity.Source.Preservation.MemoryProgramControls", "Solidity.Source.Preservation.NewArrayFragment", "Solidity.Source.Preservation.NewArrayFragmentControls", "Solidity.Source.Preservation.Reads", "Solidity.Source.Preservation.ReferenceArguments", "Solidity.Source.Preservation.ReferenceReturnControls", "Solidity.Source.Preservation.ReferenceReturns", "Solidity.Source.Preservation.ResultValidity", "Solidity.Source.Preservation.StatementFrames", "Solidity.Source.Preservation.Statements", "Solidity.Source.Preservation.StorageCopyControls", "Solidity.Source.Preservation.ValueConversions", "Solidity.Source.Progress.AggregateDefaultControls", "Solidity.Source.Progress.AggregateDefaults", "Solidity.Source.Progress.AggregateReturnControls", "Solidity.Source.Progress.AllocationBodyCallControls", "Solidity.Source.Progress.AllocationBodyCalls", "Solidity.Source.Progress.AllocationReturns", "Solidity.Source.Progress.ArithmeticBuiltins", "Solidity.Source.Progress.BoundCatalogue", "Solidity.Source.Progress.BoundCatalogueControls", "Solidity.Source.Progress.BoundCataloguePanicControls", "Solidity.Source.Progress.BoundCatalogueParentControls", "Solidity.Source.Progress.BoundParentControls", "Solidity.Source.Progress.BoundParentPanicControls", "Solidity.Source.Progress.BoundParents", "Solidity.Source.Progress.BuiltinAdmission", "Solidity.Source.Progress.BuiltinControls", "Solidity.Source.Progress.BuiltinStatements", "Solidity.Source.Progress.CallComposition", "Solidity.Source.Progress.CallCompositionControls", "Solidity.Source.Progress.CheckedPrograms", "Solidity.Source.Progress.Controls", "Solidity.Source.Progress.EffectBodies", "Solidity.Source.Progress.EffectCatalogue", "Solidity.Source.Progress.EffectCatalogueControls", "Solidity.Source.Progress.EmitBuiltins", "Solidity.Source.Progress.ForwardingChain", "Solidity.Source.Progress.ForwardingChainControls", "Solidity.Source.Progress.ForwardingControls", "Solidity.Source.Progress.ForwardingReturns", "Solidity.Source.Progress.InitializedCalls", "Solidity.Source.Progress.InitializedChain", "Solidity.Source.Progress.InitializedChainControls", "Solidity.Source.Progress.InitializedControls", "Solidity.Source.Progress.InitializedLocals", "Solidity.Source.Progress.InitializedPrefixes", "Solidity.Source.Progress.InlineArrayParentControls", "Solidity.Source.Progress.InlineArrayParents", "Solidity.Source.Progress.LiteralBuiltinControls", "Solidity.Source.Progress.LiteralBuiltins", "Solidity.Source.Progress.NewArray", "Solidity.Source.Progress.NewArrayControls", "Solidity.Source.Progress.ParentArgumentControls", "Solidity.Source.Progress.ParentArgumentFlowControls", "Solidity.Source.Progress.ParentArguments", "Solidity.Source.Progress.ReadyArguments", "Solidity.Source.Progress.ReadyBodies", "Solidity.Source.Progress.ReadyBodyCalls", "Solidity.Source.Progress.ReadyBodyControls", "Solidity.Source.Progress.ReadyCatalogue", "Solidity.Source.Progress.ReadyCatalogueControls", "Solidity.Source.Progress.ReadyDefaults", "Solidity.Source.Progress.ReadyDispatchControls", "Solidity.Source.Progress.ReadyExpressionControls", "Solidity.Source.Progress.ReadyExpressions", "Solidity.Source.Progress.ReadyProgram", "Solidity.Source.Progress.ReadyProgramControls", "Solidity.Source.Progress.ReadyRebinding", "Solidity.Source.Progress.ReadyRebindingControls", "Solidity.Source.Progress.ReadyReturnControls", "Solidity.Source.Progress.ReadyReturns", "Solidity.Source.Progress.ReadyScopeControls", "Solidity.Source.Progress.RecoveryBuiltin", "Solidity.Source.Progress.ScalarBuiltinControls", "Solidity.Source.Progress.StructParentControls", "Solidity.Source.Progress.StructParents", "Solidity.Source.Resolve", "Solidity.Source.Resolved", "Solidity.Source.Semantics", "Solidity.Source.SemanticsExamples", "Solidity.Source.Session", "Solidity.Source.SessionExamples", "Solidity.Source.SoundnessExamples", "Solidity.Source.State", "Solidity.Source.StateExamples", "Solidity.Source.StmtProgress", "Solidity.Source.Syntax", "Solidity.Source.TryExamples", "Solidity.Source.Types", "Solidity.Source.Typing", "Solidity.Source.TypingExamples", "Solidity.Source.Unique", "Solidity.Source.Units", "Solidity.Source.Upstream", "Solidity.Source.UserOps", "Solidity.Source.Value", "Solidity.Source.ValueProgress", "Solidity.Source.WellFormed", "Solidity.Source.WellTyped", "Solidity.Source.World"]
  let ledger := Json.mkObj [("schema", toJson (1 : Nat)), ("complete", Json.bool true),
    ("assigned_module_count", toJson (199 : Nat)), ("requested_modules", toJson requested),
    ("rows", Json.arr rows), ("boundary", Json.str "Compiler-format observation; not semantic API equivalence")]
  liftIO <| IO.FS.writeFile output ledger.compress
  logInfo m!"H62 Source constant/type ledger: {rows.size} entries"
