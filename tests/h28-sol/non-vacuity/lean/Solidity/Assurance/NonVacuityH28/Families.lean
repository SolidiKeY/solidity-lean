import Solidity.Theorems

/-!
# H28 inhabited families

These witnesses quantify over every existing contract and every fresh world's
balances and self address. The program has one executable require statement;
it is not the empty program. Source and target computations are separate.
-/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics

variable (C : Contract)

def requireProgram (v : Bool) : Prog C [] [] :=
  .cons (.require (.simple (.bool v))) .nil

theorem rule_family (k : Nat) (m : Modality) {Γ Γ' : Ctx}
    (s : Stmt C Γ Γ') (σ : State C Γ) :
    Rule C k m s (s.step k m) ∧ Premise.Sound m s (s.step k m) σ :=
  ⟨Main.rule_exists k m s, Main.rule_sound (Main.rule_exists k m s) σ⟩

theorem unique_family (k : Nat) (m : Modality) {Γ Γ' : Ctx}
    (s : Stmt C Γ Γ') (p : Premise C Γ Γ') (h : Rule C k m s p) :
    p = s.step k m :=
  Main.rule_unique h (Main.rule_exists k m s)

theorem fragment_family (v : Bool) :
    Evm.inFragP (Evm.Frag.init []) (requireProgram C v) = some (Evm.Frag.init []) := rfl

theorem simulation_family (balance : Nat) (hb : balance < Evm.W)
    (bal : Fin Evm.W → Nat) (self : Fin Evm.W) (heq : balance = bal self) :
    Evm.Sim C 1 0 (Evm.Frag.init []) (Evm.freshT C balance hb self)
      (Evm.Machine.init bal self) :=
  Evm.Sim.init C balance hb bal self heq

theorem checked_family (v : Bool) (balance : Nat) (hb : balance < Evm.W)
    (bal : Fin Evm.W → Nat) (self : Fin Evm.W) (heq : balance = bal self)
    (frame : Nat) (base : Nat → Fin Evm.W) :
    (Evm.Compiler.Compilation.core (b := 0) _ (fragment_family C v)).Agrees
      1 frame base (Evm.freshT C balance hb self) (Evm.Machine.init bal self) := by
  apply Main.compiler_checked
  exact ⟨simulation_family C balance hb bal self heq, by change 1 ≤ Evm.Lmax; decide⟩

theorem impossible_resource {Γ : Ctx} {F : Evm.Frag Γ}
    {σ : State C Γ} {mc : Evm.Machine} {b : Nat} :
    ¬ Evm.Sim C (Evm.Lmax + 1) b F σ mc := by
  intro h
  have hbound : Evm.Lmax + 1 ≤ Evm.Lmax := h.bound
  omega

theorem source_true (σ : State C []) :
    Prog.run σ (requireProgram C true) = .ok ⟨σ, List.prefix_refl _⟩ := rfl

theorem source_false (σ : State C []) :
    Prog.run σ (requireProgram C false) = .error .revert := rfl

theorem target_true (b : Nat) (mc : Evm.Machine) :
    Evm.run (Evm.compileProg b (requireProgram C true)) mc = .ok mc 0 := rfl

theorem target_false (b : Nat) (mc : Evm.Machine) :
    Evm.run (Evm.compileProg b (requireProgram C false)) mc = .revert := rfl

theorem nonempty_program (v : Bool) : requireProgram C v ≠ .nil := by
  intro h
  cases h

theorem nonempty_code (b : Nat) (v : Bool) :
    Evm.compileProg b (requireProgram C v) ≠ [] := by
  intro h
  cases h

theorem always_revert_rejected (b : Nat) (mc : Evm.Machine) :
    Evm.run (Evm.compileProg b (requireProgram C true)) mc ≠ Evm.run [.revert] mc := by
  rw [target_true]
  intro h
  cases h

theorem correct_success (balance : Nat) (hb : balance < Evm.W)
    (bal : Fin Evm.W → Nat) (self : Fin Evm.W) (heq : balance = bal self) :
    ∃ o mc',
      Prog.run (Evm.freshT C balance hb self) (requireProgram C true) = .ok o ∧
      Evm.run (Evm.compileProg 0 (requireProgram C true)) (Evm.Machine.init bal self) =
        .ok mc' 0 ∧
      Evm.Sim C (1 + Evm.Prog.pushes (requireProgram C true)) 0 (Evm.Frag.init []) o.st mc' := by
  rcases Main.compiler_correct (fragment_family C true)
    (simulation_family C balance hb bal self heq) (by change 1 ≤ Evm.Lmax; decide) with
    h | ⟨hsrc, _⟩ | ⟨hp, _⟩ | ⟨hsrc, _⟩
  · exact h
  · rcases hsrc with hr | ⟨_, hp⟩
    · rw [source_true] at hr
      cases hr
    · rw [source_true] at hp
      cases hp
  · cases hp
  · rw [source_true] at hsrc
    cases hsrc

theorem net_success (balance : Nat) (hb : balance < Evm.W)
    (bal : Fin Evm.W → Nat) (self : Fin Evm.W) (heq : balance = bal self) :
    ∃ o, Prog.run (Evm.freshT C balance hb self) (requireProgram C true) = .ok o ∧
      (∀ a : Fin Evm.W, a ≠ (Evm.Machine.init bal self).self →
        Evm.netAt o.st.net a.1 = ((Evm.Machine.init bal self).bal₀ a : Int) -
          (Evm.Machine.init bal self).bal a) ∧
      Evm.netAt o.st.net (Evm.Machine.init bal self).self = 0 :=
  Main.compiler_net (fragment_family C true)
    (simulation_family C balance hb bal self heq) (by change 1 ≤ Evm.Lmax; decide) (target_true C 0 _)

/-- The same typed fresh state and a fully built machine can disagree on funds. -/
theorem mismatched_funds (self : Fin Evm.W) :
    ¬ Evm.Sim C 1 0 (Evm.Frag.init []) (Evm.freshT C 0 (by decide) self)
      { Evm.Machine.init (fun _ => 0) self with bal := fun _ => 1 } := by
  intro h
  have hfunds : (0 : Int) = 1 := h.funds
  omega

/-- No False premise is required to initialize all simulation fields. -/
theorem closed_simulation :
    Evm.Sim C 1 0 (Evm.Frag.init []) (Evm.freshT C 0 (by decide) ⟨0, by decide⟩)
      (Evm.Machine.init (fun _ => 0) ⟨0, by decide⟩) :=
  simulation_family C 0 (by decide) (fun _ => 0) ⟨0, by decide⟩ rfl

def emptyContract : Contract := { vars := [] }

theorem closed_joint_witness :
    ∃ (σ : State emptyContract []) (mc : Evm.Machine),
      Evm.Sim emptyContract 1 0 (Evm.Frag.init []) σ mc ∧
      Prog.run σ (requireProgram emptyContract true) = .ok ⟨σ, List.prefix_refl _⟩ ∧
      Evm.run (Evm.compileProg 0 (requireProgram emptyContract true)) mc = .ok mc 0 :=
  ⟨_, _, closed_simulation emptyContract, source_true emptyContract _,
    target_true emptyContract 0 _⟩

theorem inhabited_fragment : ∃ P : Prog C [] [], P ≠ .nil ∧
    Evm.inFragP (Evm.Frag.init []) P = some (Evm.Frag.init []) :=
  ⟨requireProgram C true, nonempty_program C true, fragment_family C true⟩

theorem rule_step_family (k : Nat) (m : Modality) {Γ Γ' : Ctx}
    (s : Stmt C Γ Γ') : s.step k m = s.step k m :=
  Main.rule_is_step (Main.rule_exists k m s)

theorem rule_from_step_family (k : Nat) (m : Modality) {Γ Γ' : Ctx}
    (s : Stmt C Γ Γ') : Rule C k m s (s.step k m) :=
  Main.rule_of_step rfl

theorem mismatched_oracle (self : Fin Evm.W) :
    ¬ Evm.Sim C 1 0 (Evm.Frag.init []) (Evm.freshT C 0 (by decide) self)
      { Evm.Machine.init (fun _ => 0) self with accepts := fun _ _ => false } := by
  intro h
  have horacle : true = false := h.oracle ⟨0, rfl⟩ ⟨0, rfl⟩
    ⟨0, by decide⟩ ⟨0, by decide⟩ rfl rfl
  cases horacle

theorem correct_revert (balance : Nat) (hb : balance < Evm.W)
    (bal : Fin Evm.W → Nat) (self : Fin Evm.W) (heq : balance = bal self) :
    Evm.run (Evm.compileProg 0 (requireProgram C false)) (Evm.Machine.init bal self) = .revert := by
  rcases Main.compiler_correct (fragment_family C false)
    (simulation_family C balance hb bal self heq) (by change 1 ≤ Evm.Lmax; decide) with
    ⟨_, _, ho, _⟩ | ⟨_, hr⟩ | ⟨hp, _⟩ | ⟨hd, _⟩
  · simp only [Main.Runs, source_false, reduceCtorEq] at ho
  · exact hr
  · cases hp
  · rw [source_false] at hd
    cases hd

/-- Every local type has an intrinsic value over the empty heap. -/
def defaultLocal : (t : LTy) → t.TDenote C []
  | .val p => PrimTy.dflt p
  | .alias _ => none
  | .mem _ => none
  | .old => Storage.init C
  | .oldNet => []
  | .kint => 0

def defaultEnv : (Γ : Ctx) → TEnv C [] Γ
  | [] => ()
  | t :: Γ => (defaultLocal C t, defaultEnv Γ)

def contextState (Γ : Ctx) : State C Γ :=
  { storage := Storage.init C, H := [], heap := Heap.empty, env := defaultEnv C Γ }

/-- A constructive state and rule premise for every statement constructor,
including contexts with aliases, memory locals and snapshots. This does not
assert that every statement succeeds. -/
theorem every_rule_inhabited (k : Nat) (m : Modality) {Γ Γ' : Ctx}
    (s : Stmt C Γ Γ') :
    ∃ (σ : State C Γ) (p : Premise C Γ Γ'),
      Rule C k m s p ∧ Premise.Sound m s p σ ∧ s.step k m = p :=
  ⟨contextState C Γ, s.step k m, Main.rule_exists k m s,
    Main.rule_sound (Main.rule_exists k m s) _, Main.rule_is_step (Main.rule_exists k m s)⟩

theorem mismatched_self_ledger :
    ¬ Evm.Sim C 1 0 (Evm.Frag.init [])
      { Evm.freshT C 0 (by decide) ⟨0, by decide⟩ with net := [(⟨0, rfl⟩, 1)] }
      (Evm.Machine.init (fun _ => 0) ⟨0, by decide⟩) := by
  intro h
  have hnet : (1 : Int) = 0 := h.netSelf
  omega

theorem mismatched_external_ledger :
    ¬ Evm.Sim C 1 0 (Evm.Frag.init [])
      { Evm.freshT C 0 (by decide) ⟨0, by decide⟩ with net := [(⟨9, rfl⟩, -5)] }
      (Evm.Machine.init (fun _ => 0) ⟨0, by decide⟩) := by
  intro h
  have hnet : (-5 : Int) = 0 := h.net ⟨9, by decide⟩ (by decide)
  omega

end Solidity.Assurance.NonVacuityH28
