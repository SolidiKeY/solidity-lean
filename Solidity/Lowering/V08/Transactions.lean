import Solidity.Semantics.TransientWorld

/-!
# Snapshot and observation laws for existing intrinsic transactions

Every execution hypothesis names the actual supplied frame at its actual input.
Nested frames share the transaction region; only the outer boundary resets it.
These laws do not supply source execution or environment admission certificates.
-/
namespace Solidity.Lowering.V08
open Solidity.ContractWorld
variable {K : Type} {contracts : K → Contract}

/-- Normalization is idempotent as a complete world, including bookkeeping. -/
theorem resetTransient_idem (w : World contracts) :
    w.resetTransient.resetTransient = w.resetTransient := by
  have accounts : w.resetTransient.resetTransient.accounts = w.resetTransient.accounts :=
    funext (World.resetTransient_accounts_idem w)
  cases w
  exact congrArg (fun accounts => World.mk accounts _ _ _) accounts

/-- Exact frame equality at the actual reset input transports all observations. -/
theorem transact_congr {α : Type} (w : World contracts)
    (left right : World contracts → TRes (World contracts × α))
    (same : left w.resetTransient = right w.resetTransient) :
    w.transact left = w.transact right := by
  unfold World.transact
  rw [same]

/-- Result extension preserves the committed snapshot and exact failure. -/
theorem transact_observe {α β : Type} (w : World contracts)
    (frame : World contracts → TRes (World contracts × α)) (observe : α → β) :
    w.transact (fun input => (frame input).map (fun pair => (pair.1, observe pair.2))) =
      ((w.transact frame).1, (w.transact frame).2.map observe) := by
  unfold World.transact
  dsimp only
  cases frame w.resetTransient <;> rfl

/-- A descendant success followed by an ancestor failure restores the outer
snapshot, retaining the exact halt rather than the descendant snapshot. -/
theorem transact_descendant_failure {α β : Type} (w middle : World contracts)
    (first : World contracts → TRes (World contracts × α))
    (later : World contracts → α → TRes (World contracts × β))
    (value : α) (halt : THalt)
    (success : first w.resetTransient = .ok (middle, value))
    (failed : later middle value = .error halt) :
    w.transact (fun input => do
      let (next, result) ← first input
      later next result) = (w.resetTransient, .error halt) := by
  apply World.transact_failure
  simp only [success, bind, Except.bind, failed]

/-- Two transactions reset between calls; the second frame receives the first
committed world's reset, not its dirty intermediate state. -/
theorem transact_repeat {α β : Type} (w middle final : World contracts)
    (first : World contracts → TRes (World contracts × α))
    (second : World contracts → TRes (World contracts × β)) (a : α) (b : β)
    (one : first w.resetTransient = .ok (middle, a))
    (two : second middle.resetTransient = .ok (final, b)) :
    (w.transact first).1.transact second = (final.resetTransient, .ok b) := by
  rw [World.transact_commit w middle first a one]
  apply World.transact_commit
  rw [resetTransient_idem]
  exact two

/-- The same rollback snapshot with a different halt is distinguishable. -/
theorem transact_wrong_halt {α : Type} (w : World contracts)
    (frame : World contracts → TRes (World contracts × α)) (actual wrong : THalt)
    (failed : frame w.resetTransient = .error actual) (different : actual ≠ wrong) :
    w.transact frame ≠ (w.resetTransient, .error wrong) := by
  rw [World.transact_failure w frame actual failed]
  intro same
  exact different (Except.error.inj (congrArg Prod.snd same))

/-- An atomic descendant status resumes at its own entry snapshot; successful
outer work is retained. The supplied tail receives any THalt. This API law
makes no Solidity-catchability claim, including for exhaustion or divergence. -/
theorem transact_atomic_descendant {α β γ : Type} (w middle final : World contracts)
    (outer : World contracts → TRes (World contracts × α))
    (inner : World contracts → α → TRes (World contracts × β))
    (tail : World contracts → TRes β → TRes (World contracts × γ))
    (a : α) (c : γ) (halt : THalt)
    (entered : outer w.resetTransient = .ok (middle, a))
    (failed : inner middle a = .error halt)
    (continued : tail middle (.error halt) = .ok (final, c)) :
    w.transact (fun input => do
      let (snapshot, value) ← outer input
      let (after, status) := atomic snapshot (inner snapshot value)
      tail after status) = (final.resetTransient, .ok c) := by
  apply World.transact_commit
  simp only [entered, bind, Except.bind, failed, atomic_failure, continued]

/-- Any observation of a nested outer rollback reads exactly the entry
snapshot, rather than any successful descendant's state. -/
theorem rollback_observation {α β : Type} (w : World contracts)
    (frame : World contracts → TRes (World contracts × α)) (halt : THalt)
    (observe : World contracts → β) (failed : frame w.resetTransient = .error halt) :
    observe (w.transact frame).1 = observe w.resetTransient := by
  rw [World.transact_failure w frame halt failed]

end Solidity.Lowering.V08
