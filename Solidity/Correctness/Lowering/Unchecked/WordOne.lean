import Solidity.Correctness.Lowering.Unchecked.WordProgram
import Solidity.Correctness.Lowering.Unchecked.IntegerOne

/-!
# Exact destination/old-value association for word increments

Guards certifying `z = a +% b` as an increment of `z`. The total refinement
requires the arithmetic's left operand to be that same destination slot and
its right operand to be the literal one. Certificates contain only typed AST
facts. Raw/Source name binding, checkedness association, full state/failure
correspondence and the production endpoint remain separate obligations.
-/
namespace Solidity.Correctness.Lowering.Unchecked
open Solidity.Lowering.V07

/-- Static refinement of the supplied program to a same-slot update by one. -/
structure WordOneAssociation {C : Contract} {Γ : Ctx}
    (inc : Bool) (program : Prog C Γ Γ) where
  target : WordProgramAssociation (if inc then .add else .sub) program
  old : target.arithmetic.left = .simple (.local target.slot)
  one : target.arithmetic.right = .simple (.lit 1 (by decide))

/-- Total checking of destination, old-value slot and exact literal operand.
This uint256/local prototype is not a final exclusion of wider syntax. -/
def checkWordOne {C : Contract} {Γ : Ctx}
    (inc : Bool) (program : Prog C Γ Γ) : Option (WordOneAssociation inc program) := do
  let target ← checkWordProgram (if inc then .add else .sub) program
  match hOld : target.arithmetic.left, hOne : target.arithmetic.right with
  | .simple (.local slot), .simple (.lit n _) =>
    if same : slot = target.slot then
      if number : n = 1 then
        some ⟨target, by rw [hOld, same], by subst n; exact hOne⟩
      else none
    else none
  | _, _ => none

/-- The actual supplied program's arithmetic operands follow from static
association and one initial local observation. No operand-evaluation equation
or whole-program correctness certificate is an input. This remains a model
update/Source arithmetic leaf, not the complete Source statement bridge. -/
theorem wordOne_run {D : Source.Layout} {C : Contract} {Γ : Ctx}
    (target : State C Γ) (inc : Bool) (program : Prog C Γ Γ)
    (certificate : WordOneAssociation inc program) (x : Int)
    (range : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (read : TEnv.get certificate.target.slot target.env = integerValue Source.IntTy.u256 x range) :
    ∃ (sourceResult : Source.Val D (.int Source.IntTy.u256)) (modelResult : PrimTy.uint.Denote),
      Source.binVal false (if inc then .add else .sub)
        (.int x range) (.int 1 (integerOne_range Source.IntTy.u256)) = .ok sourceResult ∧
      IntValueRel Source.IntTy.u256 sourceResult modelResult ∧
      program.run target = .ok (⟨target.setLocal certificate.target.slot modelResult,
        List.prefix_refl _⟩ : Out C target.H Γ) := by
  apply wordProgramAssociation_run target (if inc then .add else .sub) program certificate.target
    x 1 range (integerOne_range Source.IntTy.u256)
  · rw [certificate.old]
    change Except.ok (TEnv.get certificate.target.slot target.env) = _
    rw [read]
  · rw [certificate.one]
    rfl

#print axioms wordOne_run

end Solidity.Correctness.Lowering.Unchecked
