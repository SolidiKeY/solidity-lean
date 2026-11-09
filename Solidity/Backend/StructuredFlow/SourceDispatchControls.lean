import Solidity.Backend.StructuredFlow.SourceDispatchCorrect
import Solidity.Backend.StructuredFlow.AssignmentBlocksCompilerControls
import Solidity.Backend.StructuredFlow.ConditionalReturnCompilerControls
import Solidity.Backend.StructuredFlow.SourceDispatchCoverage

/-!
# Regression controls for actual Source dispatch

Guards reject-all dispatch, accepting an unsupported Source constructor from
its outer tag, and treating a literal loop condition as a mapped local-copy
condition. The positive control invokes the actual compiler entry; it is not
an implication from an assumed compiler certificate.
-/
namespace Solidity.Backend.StructuredFlow.SourceDispatch
open Solidity.Lowering.V07 Solidity.Lowering.G19

/-- Arbitrary environments/contracts still admit the empty finite-copy block. -/
theorem empty_block_accepts {E : Source.Env} {C : Contract}
    {R : List Source.STy} {M : Bool} {k : Source.SCtx} (base : Nat) :
    ∃ compiled, dispatch (C := C)
      (AssignmentBlocks.statement (E := E) (R := R) (M := M) (k := k) (Γ := []) [])
      ContextMap.empty base (Evm.Frag.init []) = .ok compiled := by
  exact ⟨_,rfl⟩

/-- A valid Source statement outside the sixteen-template union is refused. -/
theorem skip_refused {E : Source.Env} {C : Contract}
    {R : List Source.STy} {M : Bool} {k : Source.SCtx} {srcΓ : Source.RCtx} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (base : Nat) (frame : Evm.Frag Γ) :
    dispatch (C := C) (Source.RStmt.skip (E := E) (R := R) (M := M) (k := k)) m base frame =
      .error .unsupportedSource := rfl

/-- Matching a while tag and break body does not admit a different condition. -/
theorem literal_condition_refused {E : Source.Env} {C : Contract}
    {R : List Source.STy} {M l u : Bool} {srcΓ : Source.RCtx} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (base : Nat) (frame : Evm.Frag Γ) :
    dispatch (C := C) (Source.RStmt.whileLoop (E := E) (R := R) (M := M) (l := l) (u := u)
      (.bool true) .brk) m base frame = .error .unsupportedSource := rfl

/-- Reuse the existing nonempty ordered-write fixture through the actual entry. -/
theorem ordered_block_accepts {E : Source.Env} {C : Contract} :
    ∃ compiled, dispatch (C := C)
      (AssignmentBlocks.statement (E := E) (R := []) (M := false) (k := ⟨false,false⟩)
        AssignmentBlocksCompiler.Controls.steps)
      ConditionalSourceCompiler.Controls.mapping 0
      (Evm.Frag.init ConditionalSourceCompiler.Controls.TargetCtx) = .ok compiled ∧
      compiled.result.code = AssignmentBlocksCompiler.Controls.emitted := by
  exact ⟨_,rfl,rfl⟩

/-- A Boolean source slot mapped to uint is not silently cast to a Boolean. -/
theorem incompatible_mapping_refused {E : Source.Env} {C : Contract} (base : Nat) :
    dispatch (C := C)
      (AssignmentBlocks.statement (E := E) (R := []) (M := false) (k := ⟨false,false⟩)
        [(.here,.here)])
      (ContextMap.cons ContextMap.empty .bool (.val .uint)) base
      (Evm.Frag.init [.val .uint]) = .error .incompatibleMapping := rfl

/-- The existing wrong-return-flag mutation remains observably different
from the actual artifact returned by Source dispatch, on the false branch. -/
theorem captured_flag_control {E : Source.Env} :
    ∃ compiled, dispatch (C := MappedCondition.Controls.C)
      (ConditionalReturn.statement (E := E) (M := false) (k := ⟨false,false⟩)
        ConditionalSourceCompiler.Controls.sci ConditionalSourceCompiler.Controls.sca
        .here ConditionalSourceCompiler.Controls.sci ConditionalSourceCompiler.Controls.sca .here)
      ConditionalSourceCompiler.Controls.mapping 0
      (Evm.Frag.init ConditionalSourceCompiler.Controls.TargetCtx) = .ok compiled ∧
      ConditionalReturnCompiler.Controls.snapshot
        (Evm.run (Evm.compileProg 0 ConditionalReturn.Controls.wrongFlag) (ReturnTailCompiler.Controls.machine false)) ≠
      ConditionalReturnCompiler.Controls.snapshot
        (Evm.run compiled.result.code (ReturnTailCompiler.Controls.machine false)) := by
  let plan := Plan.returning (E := E) (M := false) (k := ⟨false,false⟩)
    ConditionalSourceCompiler.Controls.sci ConditionalSourceCompiler.Controls.sca
    .here ConditionalSourceCompiler.Controls.sci ConditionalSourceCompiler.Controls.sca .here
  let mapped : Mapping ConditionalSourceCompiler.Controls.mapping plan := {
    condition := ⟨⟨ConditionalSourceCompiler.Controls.tci,rfl⟩,⟨ConditionalSourceCompiler.Controls.tca,rfl⟩⟩
    left := ⟨.bool,⟨.here,rfl⟩,⟨ConditionalSourceCompiler.Controls.tci,rfl⟩⟩
    rightDest := ⟨ConditionalSourceCompiler.Controls.tca,rfl⟩
    rightDonor := ⟨.here,rfl⟩ }
  obtain ⟨compiled,accepted,code⟩ := dispatch_checked (C := MappedCondition.Controls.C)
    ConditionalSourceCompiler.Controls.mapping 0 (Evm.Frag.init ConditionalSourceCompiler.Controls.TargetCtx)
    plan mapped (Evm.Frag.init (.val .bool :: ConditionalSourceCompiler.Controls.TargetCtx))
    (recognize_returning_exact _ _ _ _ _ _) (mapping_exact _ plan mapped) rfl
  refine ⟨compiled,accepted,?_⟩
  rw [code]
  exact ConditionalReturnCompiler.Controls.wrong_flag_refused

end Solidity.Backend.StructuredFlow.SourceDispatch
