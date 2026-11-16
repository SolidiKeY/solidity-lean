import Solidity.Correctness.Lowering.Unchecked.WordAssociation

/-!
# Supplied wrapping word-update programs

Guards replacing the supplied output program by an independently chosen
assignment. The total recognizer checks its actual single-statement spine,
local target and arithmetic value, and returns only static equalities.
This initial word/local boundary is not the all-arm raw/Source/program
validator. Raw bindings, Source state correspondence, operand failures,
other widths, captures, calls and the prescribed pass endpoint remain.
-/
namespace Solidity.Correctness.Lowering.Unchecked
open Solidity.Lowering.V07

/-- A static association to the actual supplied program and target slot. -/
structure WordProgramAssociation {C : Contract} {Γ : Ctx}
    (op : Source.BinOp) (program : Prog C Γ Γ) where
  slot : Idx Γ (.val .uint)
  value : Val C Γ .uint
  arithmetic : WordAssociation op value
  output : program = .cons (.assignLocal slot value) .nil

/-- Total supplied-program inspection. Declarations, captures and additional
statements are rejected explicitly here, not silently replaced or ignored. -/
def checkWordProgram {C : Contract} {Γ : Ctx}
    (op : Source.BinOp) (program : Prog C Γ Γ) : Option (WordProgramAssociation op program) :=
  match program with
  | .cons (.assignLocal (p := .uint) slot value) .nil =>
    (checkWordValue op value).map fun arithmetic => ⟨slot, value, arithmetic, rfl⟩
  | _ => none

/-- The actual supplied program writes the model result related to actual
Source arithmetic. Static certificate fields contain no execution theorem;
semantic validity is derived from the existing arithmetic proof and run.
Operand observations remain local preconditions to be established by the
full checker; this is not complete Source statement/pass correctness. -/
theorem wordProgramAssociation_run {D : Source.Layout} {C : Contract} {Γ : Ctx}
    (target : State C Γ) (op : Source.BinOp) (program : Prog C Γ Γ)
    (certificate : WordProgramAssociation op program) (x y : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (hy : Source.IntTy.u256.lo ≤ y ∧ y ≤ Source.IntTy.u256.hi)
    (left : certificate.arithmetic.left.evalT target = .ok (integerValue Source.IntTy.u256 x hx))
    (right : certificate.arithmetic.right.evalT target = .ok (integerValue Source.IntTy.u256 y hy)) :
    ∃ (sourceResult : Source.Val D (.int Source.IntTy.u256)) (modelResult : PrimTy.uint.Denote),
      Source.binVal false op (.int x hx) (.int y hy) = .ok sourceResult ∧
      IntValueRel Source.IntTy.u256 sourceResult modelResult ∧
      program.run target = .ok (⟨target.setLocal certificate.slot modelResult,
        List.prefix_refl _⟩ : Out C target.H Γ) := by
  obtain ⟨sourceResult, modelResult, source, valueRun, related⟩ :=
    wordAssociation_sound (D := D) target op certificate.value certificate.arithmetic x y hx hy left right
  refine ⟨sourceResult, modelResult, source, related, ?_⟩
  have assigned : (Stmt.assignLocal certificate.slot certificate.value).run target =
      .ok (⟨target.setLocal certificate.slot modelResult, List.prefix_refl _⟩ : Out C target.H Γ) := by
    change (do
      let value ← certificate.value.evalT target
      pure (⟨target.setLocal certificate.slot value, List.prefix_refl _⟩ : Out C target.H Γ)) = _
    rw [valueRun]
    rfl
  apply Eq.trans (congrArg (fun output : Prog C Γ Γ => output.run target) certificate.output)
  dsimp only
  rw [Prog.run_cons_ok assigned, Prog.run_nil]
  rfl

#print axioms wordProgramAssociation_run

end Solidity.Correctness.Lowering.Unchecked
