import Solidity.Source.FailurePrimitives

/-! Structural no-cut invariants of the actual typed cursor. These are not
full evaluator coherence, NoFail execution, balance installation or P8 facts. -/
namespace Solidity.Source.FailureExecution
open EM

def Cursor.CutFree (c : Cursor) : Prop :=
  c.pending = none ∧ (∀ b, c.request = some b → b.cut = none) ∧
    ∀ b, b ∈ c.frames → b.cut = none

theorem Cursor.cutFree_empty : Cursor.empty.CutFree := by
  refine ⟨rfl, ?_, ?_⟩
  · intro b impossible
    cases impossible
  · intro b impossible
    cases impossible

private theorem search_none {n : Nat} (frames : List (FrameBudget n))
    (clear : ∀ b, b ∈ frames → b.cut = none) :
    (frames.find? (fun b => cutReached b.cut b.emitted)) = none := by
  simp only [List.find?_eq_none]
  intro b member
  simp only [clear b member, cutReached, Bool.false_eq_true, not_false_eq_true]

theorem Cursor.cutFree_stop (c : Cursor) (clear : c.CutFree) : c.stop? = none := by
  have search := search_none c.frames.reverse
    (fun b member => clear.2.2 b (List.mem_reverse.mp member))
  simp only [Cursor.stop?, clear.1, Option.orElse]
  cases request : c.request with
  | none => simp only [search, Option.map_none]
  | some b =>
    have cut := clear.2.1 b request
    have reached : cutReached b.cut b.emitted = false := by
      rw [cut]
      rfl
    simp only [reached, Bool.false_eq_true, if_false, search, Option.map_none]

theorem Cursor.cutFree_enterFrame (points : Roadmap.Evm.FailurePoints)
    (noFail : FailureResources.NoFail points) (c : Cursor) (clear : c.CutFree) :
    (c.enterFrame points).CutFree := by
  refine ⟨?_, ?_, ?_⟩
  · change c.pending.map Stop.growFrame = none
    rw [clear.1]
    rfl
  · intro b member
    exact clear.2.1 b member
  · intro b member
    change b ∈ (⟨Fin.last c.nextFrame,points.frame c.nextFrame,0⟩ ::
      c.frames.map FrameBudget.grow) at member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact noFail.2 c.nextFrame
    · rcases List.mem_map.mp member with ⟨old,old_member,rfl⟩
      exact clear.2.2 old old_member

theorem Cursor.cutFree_enterRequest (points : Roadmap.Evm.FailurePoints)
    (noFail : FailureResources.NoFail points) (c : Cursor) (clear : c.CutFree)
    (quiescent : c.quiescent = true) : (c.enterRequest points quiescent).2.CutFree := by
  obtain ⟨balance,fate⟩ := noFail.1 c.nextRequest
  simp only [Cursor.enterRequest, fate]
  refine ⟨?_, ?_, ?_⟩
  · change c.pending.map Stop.growRequest = none
    rw [clear.1]
    rfl
  · intro b member
    have same := Option.some.inj member
    cases same
    rfl
  · intro b member
    exact clear.2.2 b member

theorem Cursor.cutFree_leaveFrame (c : Cursor) (clear : c.CutFree) :
    c.leaveFrame.CutFree := by
  refine ⟨?_, ?_, ?_⟩
  · cases frames : c.frames <;> simp only [Cursor.leaveFrame, clear.1, frames]
  · exact clear.2.1
  · intro b member
    exact clear.2.2 b (List.mem_of_mem_tail member)

theorem Cursor.cutFree_leaveRequest (c : Cursor) (clear : c.CutFree) :
    c.leaveRequest.CutFree := by
  refine ⟨?_, ?_, ?_⟩
  · cases request : c.request <;> simp only [Cursor.leaveRequest, clear.1, request]
  · intro b impossible
    cases impossible
  · exact clear.2.2

theorem Cursor.cutFree_advanceEvent (c : Cursor) (clear : c.CutFree) :
    c.advanceEvent.CutFree := by
  let advanced : Cursor := { c with
    request := c.request.map (fun b => { b with emitted := b.emitted+1 })
    frames := c.frames.map (fun b => { b with emitted := b.emitted+1 }) }
  have nextClear : advanced.CutFree := by
    refine ⟨clear.1, ?_, ?_⟩
    · intro b member
      change c.request.map (fun b => { b with emitted := b.emitted+1 }) = some b at member
      cases request : c.request with
      | none => rw [request] at member; cases member
      | some old =>
        rw [request] at member
        have same := Option.some.inj member
        cases same
        exact clear.2.1 old request
    · intro b member
      change b ∈ c.frames.map (fun b => { b with emitted := b.emitted+1 }) at member
      rcases List.mem_map.mp member with ⟨old,old_member,rfl⟩
      exact clear.2.2 old old_member
  unfold Cursor.advanceEvent
  rw [Cursor.cutFree_stop _ clear]
  change Cursor.CutFree { advanced with pending := advanced.stop? }
  rw [Cursor.cutFree_stop _ nextClear]
  exact ⟨rfl, nextClear.2.1, nextClear.2.2⟩

/-- Exact full-state identity for a real check on a structurally clear cursor.
NoFail of the input plan alone does not establish this cursor premise. -/
theorem check_cutFree {E : Env} {Γ : RCtx} (plan : RuntimePlan)
    (locals : Locals E.layout Γ) (state : St E) (clear : state.resource.CutFree) :
    (check plan : EM E Γ Unit).run (locals,state) = (.ok (),(locals,state)) := by
  cases plan with
  | none => rfl
  | some points =>
    dsimp only [check, EM.st, bind, pure, ExceptT.bind, ExceptT.bindCont,
      ExceptT.pure, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure,
      StateT.get, get, getThe, MonadStateOf.get, liftM, monadLift,
      MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map]
    rw [Cursor.cutFree_stop _ clear]
    rfl

end Solidity.Source.FailureExecution

/-- info: 'Solidity.Source.FailureExecution.Cursor.CutFree' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Cursor.CutFree

/-- info: 'Solidity.Source.FailureExecution.Cursor.cutFree_empty' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Cursor.cutFree_empty

/-- info: 'Solidity.Source.FailureExecution.Cursor.cutFree_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Cursor.cutFree_stop

/-- info: 'Solidity.Source.FailureExecution.Cursor.cutFree_enterFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Cursor.cutFree_enterFrame

/-- info: 'Solidity.Source.FailureExecution.Cursor.cutFree_enterRequest' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Cursor.cutFree_enterRequest

/-- info: 'Solidity.Source.FailureExecution.Cursor.cutFree_leaveFrame' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Cursor.cutFree_leaveFrame

/-- info: 'Solidity.Source.FailureExecution.Cursor.cutFree_leaveRequest' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Cursor.cutFree_leaveRequest

/-- info: 'Solidity.Source.FailureExecution.Cursor.cutFree_advanceEvent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.Cursor.cutFree_advanceEvent

/-- info: 'Solidity.Source.FailureExecution.check_cutFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.check_cutFree
