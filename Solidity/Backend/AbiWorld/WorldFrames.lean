import Solidity.Source.World

/-!
# Independent frame and observation transport over published typed worlds

Only proofs and structural observations are added. No source-world execution,
callee model or intrinsic/EVM preservation premise is introduced here.
-/
namespace Solidity.Backend.AbiWorld
open Source Roadmap

variable {D : Source.Layout} {L T : Address → SPath → STy}

/-- The owner address already carried by an intrinsic source operation. -/
def operationOwner : Source.Op D L T → Address
  | .account a _ => a
  | .transient a _ => a

/-- Arbitrary operations on other accounts preserve both typed observations.
The address separation is explicit; the update functions are unrestricted. -/
theorem unrelated_world_frame (s : ExecState D L T) (os : List (Source.Op D L T))
    (a : Address) (separated : ∀ o ∈ os, operationOwner o ≠ a) :
    ((s.run os).world.accounts a, (s.run os).transient.cells a) =
      (s.world.accounts a, s.transient.cells a) := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih =>
    have ho : operationOwner o ≠ a := separated o (List.mem_cons_self)
    have ht : ∀ x ∈ os, operationOwner x ≠ a :=
      fun x hx => separated x (List.mem_cons_of_mem o hx)
    change (((s.apply o).run os).world.accounts a, ((s.apply o).run os).transient.cells a) = _
    rw [ih (s.apply o) ht]
    cases o with
    | account b f =>
      change b ≠ a at ho
      change ((s.world.set b (f (s.world.accounts b))).accounts a, s.transient.cells a) = _
      rw [World.set_other s.world (Ne.symm ho)]
    | transient b f =>
      change b ≠ a at ho
      change (s.world.accounts a, (s.transient.set b (f (s.transient.cells b))).cells a) = _
      simp only [Transient.set, dif_neg (Ne.symm ho)]

/-- Callback rollback permits entirely different outer/inner frame metadata.
All actual world, transient and journal changes are restored by the published law. -/
theorem heterogeneous_callback_rollback (s : ExecState D L T)
    (before callback : List (Source.Op D L T)) (outer inner : CallFrame)
    (ho : outer.mark = s.journal.length)
    (hi : inner.mark = (s.run before).journal.length) :
    inner.rollback ((s.run before).run callback) = s.run before ∧
      outer.rollback (inner.rollback ((s.run before).run callback)) = s := by
  have hr : inner.rollback ((s.run before).run callback) = s.run before := by
    simp only [CallFrame.rollback, hi, ExecState.journal_run]
    simp only [Nat.add_sub_cancel_left]
    exact ExecState.undoN_run _ _
  refine ⟨hr, ?_⟩
  rw [hr]
  simp only [CallFrame.rollback, ho, ExecState.journal_run]
  rw [show s.journal.length + before.length - s.journal.length = before.length by omega]
  exact ExecState.undoN_run _ _

/-- Prefix adapter for observations already emitted by a caller. -/
def prependEvents {E O : Type} (events : List E) (p : Prefix E O) : Prefix E O :=
  ⟨events ++ p.events, p.final⟩

/-- Observation concatenation respects the published completed-prefix order. -/
theorem prependEvents_monotone {E O : Type} (events : List E) {p q : Prefix E O}
    (h : p.Le q) : (prependEvents events p).Le (prependEvents events q) := by
  refine ⟨(List.prefix_append_right_inj events).2 h.1, ?_⟩
  rcases h.2 with hf | he
  · exact Or.inl hf
  · subst q
    exact Or.inr rfl

/-- Appending observations in two frames has exactly the same event ordering. -/
theorem prependEvents_assoc {E O : Type} (xs ys : List E) (p : Prefix E O) :
    prependEvents xs (prependEvents ys p) = prependEvents (xs ++ ys) p := by
  cases p
  simp only [prependEvents, List.append_assoc]

/-- info: 'Solidity.Backend.AbiWorld.unrelated_world_frame' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms unrelated_world_frame
/-- info: 'Solidity.Backend.AbiWorld.heterogeneous_callback_rollback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms heterogeneous_callback_rollback
/-- info: 'Solidity.Backend.AbiWorld.prependEvents_monotone' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms prependEvents_monotone
end Solidity.Backend.AbiWorld
