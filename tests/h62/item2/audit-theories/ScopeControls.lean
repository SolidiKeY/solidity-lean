import Solidity.Theory.Progress.Program
import Solidity.Source.SemanticsExamples
import Solidity.Theory.Reachable.Mode

/-! Further exact-input witnesses and global-versus-per-input controls.
None of these installs a new premise on a frozen interface. -/
namespace H62.AuditTheories
open Solidity Solidity.Source Solidity.Source.Progress Solidity.Theory.Progress
open Solidity.Source.SemanticsExamples

/-- All inputs and hypotheses of expr_progress, on a supported bool literal. -/
theorem expr_progress_joint_witness :
    ∃ (E : Env) (X : StmtExt E) (A : Source.Decl → Prop) (G : Glob E) (c : String)
      (F : Fr) (_n : Nat) (Γ : RCtx) (τ : STy) (e : RExpr E Γ τ)
      (_x : Locals E.layout Γ × St E),
      CallsOKX X A G c ∧ X.Sound G A (· = c) ∧ F.contract = c ∧
      RExpr.ValFragC A e ∧ e.OpsOK := by
  exact ⟨E0, StmtExt.none E0, (fun _ => False), G0 .legacy, F0.contract,
    F0, 10, [], .bool, .bool true, (.nil, s0), callsOKX_none _ _ _,
    StmtExt.none_sound _ _ _, rfl, trivial, trivial⟩

/-- All inputs and hypotheses of items_progress, on an empty body block. -/
theorem items_progress_joint_witness :
    ∃ (E : Env) (X : StmtExt E) (A : Source.Decl → Prop) (G : Glob E) (c : String)
      (F : Fr) (_n nps : Nat) (_ph : Option (Ph E)) (R : List STy) (M : Bool)
      (k : SCtx) (Γ Γ' : RCtx) (b : RItems E R M k Γ Γ')
      (_l : Locals E.layout Γ) (_x : Locals E.layout [] × St E),
      CallsOKX X A G c ∧ X.Sound G A (· = c) ∧ F.contract = c ∧
      IFrag X A b ∧ b.OpsOK ∧ BodyFrame nps R Γ := by
  exact ⟨E0, StmtExt.none E0, (fun _ => False), G0 .legacy, F0.contract,
    F0, 10, 0, none, [], false, .body, [], [], .nil, .nil, (.nil, s0),
    callsOKX_none _ _ _, StmtExt.none_sound _ _ _, rfl, .nil, trivial, ⟨[], [], rfl, rfl⟩⟩

/-- The supported `function f() { }` source body used by body_progress. -/
def emptyBody : RBody E0 where
  ps := []
  rs := []
  inModifier := false
  locals := []
  out := []
  items := .nil

/-- All inputs and hypotheses of body_progress, including an actual body frame. -/
theorem body_progress_joint_witness :
    ∃ (E : Env) (X : StmtExt E) (A : Source.Decl → Prop) (G : Glob E) (c : String)
      (F : Fr) (_n : Nat) (b : RBody E) (_l : Locals E.layout b.locals)
      (_x : Locals E.layout [] × St E),
      CallsOKX X A G c ∧ X.Sound G A (· = c) ∧ F.contract = c ∧
      IFrag X A b.items ∧ b.items.OpsOK ∧ BodyFrame b.ps.length b.rs b.locals := by
  exact ⟨E0, StmtExt.none E0, (fun _ => False), G0 .legacy, F0.contract,
    F0, 10, emptyBody, .nil, (.nil, s0), callsOKX_none _ _ _,
    StmtExt.none_sound _ _ _, rfl, .nil, trivial, ⟨[], [], rfl, rfl⟩⟩

/-- A witness for every input of callsOKX_none itself. -/
theorem callsOKX_none_joint_witness :
    ∃ (E : Env) (X : StmtExt E) (G : Glob E) (c : String),
      CallsOKX X (fun _ => False) G c :=
  ⟨E0, StmtExt.none E0, G0 .legacy, F0.contract, callsOKX_none _ _ _⟩

/-- A call-free global premise exists, but it supplies no admitted declaration.
Thus it cannot be substituted for the simultaneous hypotheses of call_progress. -/
theorem call_free_global_does_not_supply_call :
    CallsOKX (StmtExt.none E0) (fun _ => False) (G0 .legacy) F0.contract ∧
      ¬ ∃ d : Source.Decl, (fun _ : Source.Decl => False) d := by
  refine ⟨callsOKX_none _ _ _, ?_⟩
  rintro ⟨d, hd⟩
  exact hd

/-- A global lifetime-system structure is inhabited even when its action and
constructor input types have no members. -/
def emptySystem (C : Contract) : Lifetime.System C Empty Empty where
  deploy := fun d => nomatch d
  call := fun a => nomatch a

/-- Inhabiting the global system is insufficient for per-input feasibility:
there is no actual entry state in the system above, for any contract. -/
theorem empty_system_has_no_entry (C : Contract) :
    Nonempty (Lifetime.System C Empty Empty) ∧
      ∀ σ : State C [], ¬ Reachable.EntryState (emptySystem C) σ := by
  refine ⟨⟨emptySystem C⟩, ?_⟩
  intro σ h
  obtain ⟨s, tx, a, _⟩ := h
  exact nomatch a

#print axioms expr_progress_joint_witness
#print axioms items_progress_joint_witness
#print axioms body_progress_joint_witness
#print axioms callsOKX_none_joint_witness
#print axioms call_free_global_does_not_supply_call
#print axioms empty_system_has_no_entry
end H62.AuditTheories
