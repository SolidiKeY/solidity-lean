import Solidity.Correctness.Sim.Lang

/-! Checked boundary examples for the simulation framework. -/
namespace Solidity.Correctness.Sim.Examples
open Solidity.Roadmap Solidity.Roadmap.G49Final

/-- A deterministic constant observation family with no hidden guard. -/
def constant (result : Option Outcome) : Behaviour where
  Env := Unit
  Res := Unit
  resLE := ⟨fun _ _ => True⟩
  Allowed := fun _ => True
  Admissible := fun _ => True
  Forward := fun _ _ => True
  Guard := fun _ _ => True
  observe := fun _ _ => ⟨[], result⟩
  consistent := fun _ _ _ _ => Prefix.Le.refl _

/-- Deterministic small-step presentations for these families. -/
def machine (result : Option Outcome) : Machine where
  State := Unit
  initial := ()
  step := Eq
  observe := fun _ => ⟨[], result⟩

theorem deterministic (result : Option Outcome) (s t u : Unit)
    (ht : (machine result).step s t) (hu : (machine result).step s u) : t = u :=
  ht.symm.trans hu

/-- A forward diagram may match an unfinished source with a completed target. -/
def forwardOnly : Diagram (machine none) (machine (some (.success []))) where
  matchState := fun _ _ => True
  initial := trivial
  step := fun _ _ t _ _ => ⟨t, .refl t, trivial⟩
  events := fun _ _ _ => List.prefix_refl _
  final := by intros s t o _ impossible; cases impossible

/-- Both deterministic families have full run coverage, yet a forward diagram
alone cannot establish the backward clause: the source never completes. -/
theorem no_backward_certificate :
    PassCorrect (constant none) (constant (some (.success []))) → False := by
  intro certificate
  obtain ⟨r, _, _, le⟩ := certificate.back () () trivial trivial trivial
  have eq := le.final_eq (o := .success []) rfl
  have finals := congrArg Prefix.final eq
  change (none : Option Outcome) = some (.success []) at finals
  cases finals

theorem constant_coverage (result : Option Outcome) :
    Covers (constant result) (fun _ => machine result) (fun _ _ => True) := by
  intro e r _ _
  exact ⟨(), .refl (), rfl⟩

/-- Silent countdown reaches a final pair without requiring a target step. -/
example (n : Nat) : ∃ m, Star (fun s t : Nat => s = t + 1) n m ∧
    ((True ∧ m = 0 ∧ True) ∨ ∃ _ : Unit, Plus (fun _ _ : Unit => False) () () ∧ True) := by
  apply wellFounded_final_or_progress (fun _ (_ : Unit) => True)
    (fun m => m = 0) (fun _ => True) Nat.lt Nat.lt_wfRel.wf
    (source := fun s t => s = t + 1) (target := fun _ _ : Unit => False)
    (progress := ?_) n () trivial
  intro s t _
  cases s with
  | zero => exact .inl ⟨rfl, trivial⟩
  | succ k => exact .inr (.inr ⟨k, rfl, Nat.lt_succ_self k, trivial⟩)

/-- An executable-language boundary instance exercising the full constructor. -/
def constantLang (result : Option Outcome) : Lang Event Outcome where
  Prog := Unit
  Env := Unit
  Res := Unit
  resLE := ⟨fun _ _ => True⟩
  Allowed := fun _ => True
  Admissible := fun _ => True
  sem := fun _ _ _ => ⟨[], result⟩
  consistent := fun _ _ _ _ _ => Prefix.Le.refl _

def identityDiagram (result : Option Outcome) : Diagram (machine result) (machine result) where
  matchState := fun _ _ => True
  initial := trivial
  step := fun _ _ t _ _ => ⟨t, .refl t, trivial⟩
  events := fun _ _ _ => List.prefix_refl _
  final := fun _ _ _ _ _ => rfl

def identityCertificate (result : Option Outcome) :
    PassCorrect (Behaviour.ofLang (constantLang result) ())
      (Behaviour.ofLang (constantLang result) ()) := by
  apply lang_passCorrect (constantLang result) (constantLang result) () ()
    (fun _ => machine result) (fun _ => machine result) id
    (fun _ h => h) (fun e h => ⟨e, h, rfl⟩)
    (fun _ => identityDiagram result) (fun _ => identityDiagram result)
  · exact { need := fun _ r => r
            coverage := fun _ _ _ _ => ⟨(), .refl (), rfl⟩
            ready := fun _ _ _ h => h
            bound := fun _ _ _ _ _ _ _ _ _ _ => Prefix.Le.refl _ }
  · exact { coverage := fun _ _ _ _ => ⟨(), .refl (), rfl⟩
            bound := fun _ _ _ _ _ _ _ _ _ _ _ => ⟨(), trivial, trivial, Prefix.Le.refl _⟩ }

/-- A concrete completed revert is covered in both certificate directions. -/
example : ∃ r, (Behaviour.ofLang (constantLang (some (.revert []))) ()).Admissible r ∧
    (Behaviour.ofLang (constantLang (some (.revert []))) ()).Guard () r ∧
    (Behaviour.ofLang (constantLang (some (.revert []))) ()).observe () r = ⟨[], some (.revert [])⟩ :=
  completed_backward (identityCertificate (some (.revert []))) (e := ()) (r := ()) trivial trivial trivial rfl

end Solidity.Correctness.Sim.Examples
