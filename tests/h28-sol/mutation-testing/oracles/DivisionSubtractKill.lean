import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.DivisionSubtractKill
open Solidity

def C : Contract := { vars := [] }
def Γ : Ctx := [.val .int]
def initial (b : Bool) : PrimTy.int.Denote :=
  if b then ⟨-Semantics.intBound, by decide +kernel⟩ else ⟨1, by decide +kernel⟩
def divisor (b : Bool) : PrimTy.int.Denote :=
  if b then ⟨-1, by decide +kernel⟩ else ⟨0, by decide +kernel⟩
def σ (b : Bool) : State C Γ := (State.init C).push (t := .val .int) (initial b)
def statement (b : Bool) : Stmt C Γ Γ :=
  .opAssign .div rfl rfl (.local .here) (.simple (.lit (divisor b).1 (divisor b).2))
def update (b : Bool) : Upd C Γ Γ := .snoc .nil (.local .here (.val
  (.app2 (.binop .sub rfl) (.pvV .here) (.app0 (.lit (divisor b))))))
def premise (b : Bool) : Premise C Γ Γ := .update (update b)

theorem source_link : ∀ b : Bool, Taclet C 0 .diamond (statement b) (premise b) := fun _b => .localOpAssign
theorem input_inhabited : ∀ _b : Bool, Nonempty (State C Γ) := fun b => ⟨σ b⟩
theorem rejecting_run : ∀ b : Bool, (statement b).runR (σ b) = .error .revert := by
  intro b
  cases b <;> rfl

def answer (b : Bool) : PrimTy.int.Denote :=
  if b then ⟨-Semantics.intBound + 1, by decide +kernel⟩ else ⟨1, by decide +kernel⟩
def after (b : Bool) : State C Γ := (σ b).setLocal .here (answer b)

theorem update_returns : ∀ b : Bool, (update b).globT (σ b) = some (σ b).globG := by
  intro b
  cases b <;> rfl

theorem typed_landing : ∀ b : Bool, (update b).Lands (σ b) (σ b).globG (after b) := by
  intro b
  apply Upd.lands_iff_applyV.mpr
  refine ⟨(σ b).locV.set .here (answer b), ?_, ?_, ?_⟩
  · cases b <;> rfl
  · rfl
  · intro t i
    cases i with
    | here => rfl
    | there i => nomatch i

theorem premise_accepts_true : ∀ b : Bool, holds (σ b) ((premise b).fml .diamond .nil .nil .tt) := by
  intro b
  change (update b).afterT .diamond (σ b) (fun _ => True)
  apply Upd.afterT_intro
  · intro h
    rw [update_returns b] at h
    cases h
  · intro g τ h
    trivial

theorem execution_rejects_true : ∀ b : Bool,
    ¬ holds (σ b) (.modal .diamond (.cons (statement b) .nil) .nil .tt) := by
  intro b
  cases b <;> (change ¬ (THalt.revert = THalt.exhausted ∧ _); intro h; cases h.1)

theorem checked_kill : ¬ Premise.Sound .diamond (statement true) (premise true) (σ true) := by
  intro h
  exact execution_rejects_true true (h .nil .nil .tt (premise_accepts_true true))

theorem checked_zero_kill : ¬ Premise.Sound .diamond (statement false) (premise false) (σ false) := by
  intro h
  exact execution_rejects_true false (h .nil .nil .tt (premise_accepts_true false))

#print axioms source_link
#print axioms input_inhabited
#print axioms rejecting_run
#print axioms update_returns
#print axioms typed_landing
#print axioms premise_accepts_true
#print axioms execution_rejects_true
#print axioms checked_kill
#print axioms checked_zero_kill
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @rejecting_run
#check @update_returns
#check @typed_landing
#check @premise_accepts_true
#check @execution_rejects_true
#check @checked_kill
#check @checked_zero_kill
end H28.DivisionSubtractKill
