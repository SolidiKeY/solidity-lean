import Solidity.Calculus.Surface
import Solidity.Calculus.SurfaceRevert

/-!
# Revert data read in formulas (S6.2)

`dl!{ φ ↯ ψ }` (`Calculus/SurfaceRevert.lean`) reads the data a revert
returns: `[ P ] φ ↯ ψ` asks `φ` of a normal end and `ψ` of a revert's data.
These examples pin the notation, its printer, and both readings of a reason
the elaborator gives (`docs/semantic-gaps.md`, "Revert data"): a literal
reason written as bytes (`hex"…"`, the solc import's form) keeps its
`Error(string)` data in every frame; a string reason outside a self-call's
callee is a data-free `revert`.
-/

namespace Solidity.Examples.Tactics.RevertFormulas

local instance : InContract := ⟨StandardExample⟩
open scoped Solidity.Scoped

/-! ## The printer reads back -/

/--
info: dl{ [ revert(hex"626f6f6d"); ] true ↯ Error("boom") } : RFml StandardExample []
-/
#guard_msgs in #check dl!{ [ revert(hex"626f6f6d"); ] true ↯ Error("boom") }

/--
info: dl{ ⟨ revert(); ⟩ false ↯ [] ∨ ¬Panic(1) ∧ selector [8, 195, 121, 160] } : RFml StandardExample []
-/
#guard_msgs in #check dl!{ ⟨ revert(); ⟩ false ↯ [] ∨ ¬ Panic(1) ∧ selector [8, 195, 121, 160] }

/-! ## Valid formulas -/

/-- `revert(hex"626f6f6d")` reverts with `Error("boom")`. -/
theorem hexReason : RFml.Valid dl!{ [ revert(hex"626f6f6d"); ] true ↯ Error("boom") } := by
  intro σ
  exact (revModal_revertBytes σ _ _ _ _ _ _).2 rfl

/-- …and it does revert: the diamond with a false postcondition holds. -/
theorem hexReason_reverts : RFml.Valid dl!{ ⟨ revert(hex"626f6f6d"); ⟩ false ↯ Error(_) } := by
  intro σ
  exact (revModal_revertBytes σ _ _ _ _ _ _).2 rfl

/-- `revert("boom")` outside a self-call's callee reverts with no data in
the model: it satisfies `[]`, not `Error("boom")`. -/
theorem stringReason_empty : RFml.Valid dl!{ ⟨ revert("boom"); ⟩ false ↯ [] } := by
  intro σ
  exact (revModal_revert σ _ _ _ _ _).2 rfl

/-- A reason reached through a branch: `x = 5` passes the test, so the run
reverts with `Error("big")`. -/
theorem branchReason :
    RFml.Valid dl!{ ⟨ uint x = 5; if (x > 3) { revert(hex"626967"); }; ⟩ false ↯ Error("big") } := by
  intro σ
  exact (revModal_of_revert (d := Semantics.encodeError [98, 105, 103]) .diamond _ _ rfl).2 rfl

/-- The modality is conservative: accepting any data, the box is the box. -/
theorem box_any (σ : State StandardExample []) :
    RFml.holds σ dl!{ [ alice.age = 1; ] alice.age == 1 ↯ _ } ↔
      σ ⊧ dl!{ [ alice.age = 1; ] alice.age == 1 } :=
  revModal_box_any σ _ _ _

/-! ## Negative controls -/

/-- The data is read: `Error("boom")` is not `Error("bam")`. -/
theorem hexReason_not_other (σ : State StandardExample []) :
    ¬ RFml.holds σ dl!{ [ revert(hex"626f6f6d"); ] true ↯ Error("bam") } := fun h =>
  absurd ((revModal_revertBytes σ _ _ _ _ _ _).1 h) (by decide)

/-- The model drops a string reason at top level (recorded deviation). -/
theorem stringReason_not_error (σ : State StandardExample []) :
    ¬ RFml.holds σ dl!{ [ revert("boom"); ] true ↯ Error("boom") } := fun h =>
  absurd ((revModal_revert σ _ _ _ _ _).1 h) (by decide)

/-- A normal end reads no data: `⟨ ⟩ false ↯ _` fails. -/
theorem skip_not_reverts (σ : State StandardExample []) :
    ¬ RFml.holds σ dl!{ ⟨ ⟩ false ↯ _ } := fun h =>
  (revModal_of_ok (τ := σ) .diamond _ _ rfl).1 h trivial

/-- A branch not taken reverts with nothing: `x = 2` fails the test. -/
theorem branch_not_taken (σ : State StandardExample []) :
    ¬ RFml.holds σ dl!{ ⟨ uint x = 2; if (x > 3) { revert(hex"626967"); }; ⟩ false ↯ _ } := by
  intro h
  exact (revModal_of_ok (τ := _) .diamond _ _ rfl).1 h trivial

/-- A top-level `assert` panics: no data predicate reads it (solc reverts with
`Panic(1)`; recorded in `docs/solc-alignment.md`). -/
theorem assert_not_panic (σ : State StandardExample []) :
    ¬ RFml.holds σ dl!{ ⟨ assert(false); ⟩ false ↯ Panic(1) } :=
  revModal_not_panic _ _ _ rfl

/-- `↯ none` is stronger than the box: `revert()` satisfies `[ revert(); ] true`
but not `[ revert(); ] true ↯ none`. -/
theorem box_none_stronger (σ : State StandardExample []) :
    σ ⊧ dl!{ [ revert(); ] true } ∧ ¬ RFml.holds σ dl!{ [ revert(); ] true ↯ none } :=
  ⟨(revModal_box_any σ _ _ _).1 ((revModal_revert σ _ _ _ _ _).2 rfl),
    fun h => absurd ((revModal_revert σ _ _ _ _ _).1 h) (by decide)⟩

/-- `↯ _` is weaker than the diamond: `revert()` satisfies
`⟨ revert(); ⟩ false ↯ _` but not `⟨ revert(); ⟩ false`. -/
theorem diamond_any_weaker (σ : State StandardExample []) :
    RFml.holds σ dl!{ ⟨ revert(); ⟩ false ↯ _ } ∧ ¬ σ ⊧ dl!{ ⟨ revert(); ⟩ false } :=
  ⟨(revModal_revert σ _ _ _ _ _).2 rfl, fun h =>
    absurd ((revModal_revert σ _ _ _ _ _).1 ((revModal_diamond_none σ _ _ _).2 h)) (by decide)⟩

/-! `↯` needs a modality: a formula without one is refused, not read with
`ψ` ignored. -/

/--
error: `↯` reads the revert data of a modality: write `[ P ] φ ↯ ψ` or `⟨ P ⟩ φ ↯ ψ`
-/
#guard_msgs in #check dl!{ true ↯ Error("x") }

/-- The printed form reads back to the same formula. -/
example : dl{ [ revert(hex"626f6f6d"); ] true ↯ Error("boom") } =
    dl!{ [ revert(hex"626f6f6d"); ] true ↯ Error("boom") } := rfl

/-! ## Axiom guards -/

/-- info: 'Solidity.revModal_box_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms revModal_box_any

end Solidity.Examples.Tactics.RevertFormulas
