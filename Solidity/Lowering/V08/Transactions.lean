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

/-- Two distinct atomic snapshots. The inner completed failure resumes at
`middle`; the later middle failure resumes at `outer`. Both status consumers
are arbitrary THalt consumers, not Solidity catch handlers. Only transact resets. -/
theorem transact_two_boundaries {α β γ δ ε : Type}
    (w outer middle final : World contracts)
    (enterOuter : World contracts → TRes (World contracts × α))
    (enterMiddle : World contracts → α → TRes (World contracts × β))
    (inner : World contracts → β → TRes (World contracts × γ))
    (middleTail : World contracts → TRes γ → TRes (World contracts × δ))
    (outerTail : World contracts → TRes δ → TRes (World contracts × ε))
    (a : α) (b : β) (result : ε) (innerHalt middleHalt : THalt)
    (outerReached : enterOuter w.resetTransient = .ok (outer, a))
    (middleReached : enterMiddle outer a = .ok (middle, b))
    (innerFailed : inner middle b = .error innerHalt)
    (middleFailed : middleTail middle (.error innerHalt) = .error middleHalt)
    (outerContinued : outerTail outer (.error middleHalt) = .ok (final, result)) :
    w.transact (fun input => do
      let (outerSnapshot, a) ← enterOuter input
      let (afterMiddle, middleStatus) := atomic outerSnapshot (do
        let (middleSnapshot, b) ← enterMiddle outerSnapshot a
        let (afterInner, innerStatus) := atomic middleSnapshot (inner middleSnapshot b)
        middleTail afterInner innerStatus)
      outerTail afterMiddle middleStatus) = (final.resetTransient, .ok result) := by
  apply World.transact_commit
  simp only [outerReached, bind, Except.bind, middleReached, innerFailed,
    atomic_failure, middleFailed, outerContinued]

/-- Complete observations include both the reset world and exact result/status;
this is congruence of a proved transaction, not a preservation premise. -/
theorem transact_complete_observation {α β : Type} (w final : World contracts)
    (frame : World contracts → TRes (World contracts × α)) (result : α)
    (ran : frame w.resetTransient = .ok (final, result))
    (observe : World contracts × TRes α → β) :
    observe (w.transact frame) = observe (final.resetTransient, .ok result) := by
  rw [World.transact_commit w final frame result ran]

#print axioms transact_two_boundaries
#print axioms transact_complete_observation

/-- A failed repeated transaction rolls back to the committed first world's
reset, never the original transaction's entry or its dirty final state. -/
theorem transact_repeat_failure {α β : Type} (w middle : World contracts)
    (first : World contracts → TRes (World contracts × α))
    (second : World contracts → TRes (World contracts × β)) (value : α) (halt : THalt)
    (one : first w.resetTransient = .ok (middle, value))
    (two : second middle.resetTransient = .error halt) :
    (w.transact first).1.transact second = (middle.resetTransient, .error halt) := by
  rw [World.transact_commit w middle first value one]
  have failed : second middle.resetTransient.resetTransient = .error halt := by
    rw [resetTransient_idem]
    exact two
  rw [World.transact_failure middle.resetTransient second halt failed, resetTransient_idem]

#print axioms transact_repeat_failure

/-- A failed transaction followed by success retains BOTH exact statuses.
The second frame runs at the same reset entry, not at a dirty handler prefix. -/
theorem transact_failure_then_commit {α β : Type} (w next : World contracts)
    (first : World contracts → TRes (World contracts × α))
    (second : World contracts → TRes (World contracts × β)) (halt : THalt) (value : β)
    (failed : first w.resetTransient = .error halt)
    (succeeded : second w.resetTransient = .ok (next, value)) :
    ((w.transact first).2, (w.transact first).1.transact second) =
      (.error halt, (next.resetTransient, .ok value)) := by
  rw [World.transact_failure w first halt failed]
  have ran : second w.resetTransient.resetTransient = .ok (next, value) := by
    rw [resetTransient_idem]
    exact succeeded
  rw [World.transact_commit w.resetTransient next second value ran]

#print axioms transact_failure_then_commit

end Solidity.Lowering.V08
