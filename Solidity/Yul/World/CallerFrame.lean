import Solidity.Yul.World.PhysicalEnvironmentAnswer
import Solidity.Source.Horizon

/-! Caller-local transport uses the actual Source.EM.sub implementation.
It does not assert heap or function-local preservation for arbitrary Invoke. -/
namespace Solidity.Yul.World.CallerFrame
open Solidity.Source
open Solidity.Roadmap (Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion

/-- Exact source external-local boundary, including the callee's returned
empty-context locals in the raw Source result. -/
def sourceBoundary {E Γ} (caller : EMState E Γ) (child : EMState E []) (status : Except Halt Outcome) :=
  (Source.EM.sub (L0 E) (ExceptT.mk (fun _ : EMState E [] => (status,child)))).run caller

theorem sourceBoundary_exact {E Γ} (caller : EMState E Γ) (child : EMState E []) (status : Except Halt Outcome) :
    sourceBoundary caller child status =
      (status.map (fun out=>(out,child.1)),(caller.1,child.2)) := by
  cases status <;> rfl

/-- A full-carrier producer with its real Source external-local boundary.
Source state/physical journals/ordered suffix are all retained. -/
def liftInvoke {E Γ} (invoke : Invoke E []) : Invoke E Γ :=
  fun o frame kind target gas input c =>
    (invoke o frame kind target gas input ⟨⟨⟨L0 E,c.1.1.2⟩,c.1.2⟩,c.2⟩).map (fun answer =>
      let run := sourceBoundary c.1.1 answer.1.2.1.1 answer.1.1
      ((run.1.map Prod.fst,⟨⟨run.2,answer.1.2.1.2⟩,answer.1.2.2⟩),answer.2))

theorem liftInvoke_exact {E Γ} (invoke : Invoke E []) o frame kind target gas input
    (c : Carrier E Γ) (status : Except Halt Outcome) (after : Carrier E []) (suffix : List Observation)
    (ran : invoke o frame kind target gas input ⟨⟨⟨L0 E,c.1.1.2⟩,c.1.2⟩,c.2⟩ = some ((status,after),suffix)) :
    liftInvoke invoke o frame kind target gas input c =
      some ((status,⟨⟨⟨c.1.1.1,after.1.1.2⟩,after.1.2⟩,after.2⟩),suffix) := by
  simp only [liftInvoke,ran,Option.map_some,sourceBoundary_exact]
  cases status <;> rfl

/-- The retained Source St is exactly the real callee St. Heap/fnLocals
restoration must therefore be proved from the actual producer, not assumed. -/
theorem liftInvoke_state {E Γ} (invoke : Invoke E []) o f k target gas input
    (c : Carrier E Γ) status (after : Carrier E []) suffix
    (ran : invoke o f k target gas input ⟨⟨⟨L0 E,c.1.1.2⟩,c.1.2⟩,c.2⟩ = some ((status,after),suffix)) :
    (liftInvoke invoke o f k target gas input c).map (fun result =>
      (result.1.2.1.1.1,result.1.2.1.1.2,result.1.2.1.2,result.1.2.2,result.2)) =
      some (c.1.1.1,after.1.1.2,after.1.2,after.2,suffix) := by
  rw [liftInvoke_exact _ _ _ _ _ _ _ _ _ _ _ ran]
  rfl

/-- Actual enterInstance restores its recorded caller heap after every
completed dispatch attempt, including stuck/timeout. Fuel0 is excluded. -/
theorem enterInstance_heap {E} (G : Glob E) (s : EMState E []) (n : Nat)
    a sender value input static contract depth (mark : Nat × Nat × Source.Heap E.layout) :
    ((Source.enterInstance G (n+1) a sender value input static contract depth mark).run s).2.2.heap=mark.2.2 := by
  let F : Fr := {this:=a,sender:=sender,value:=value,static:=static,contract:=contract,checked:=true,depth:=depth,cd:=input}
  let resume : Except Halt Solidity.Roadmap.Bytes → EM E [] Outcome := fun result => do
    Source.EM.modSt (fun state=>{state with heap:=mark.2.2})
    match result with
    | .ok data => pure (.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (.revert data)
    | .error h => Source.EM.halt h
  change ((do
    Source.EM.modSt (fun state=>{state with heap:=Source.Heap.empty})
    let result ← Source.EM.attempt (Source.dispatch G F n input)
    resume result).run s).2.2.heap=mark.2.2
  rw [Source.Hoare.run_bind]
  change ((do let result ← Source.EM.attempt (Source.dispatch G F n input); resume result).run
    (s.1,{s.2 with heap:=Source.Heap.empty})).2.2.heap=mark.2.2
  rw [Source.Hoare.run_bind]
  change (match (Source.dispatch G F n input).run (s.1,{s.2 with heap:=Source.Heap.empty}) with
    | (result,child)=>(resume result).run child).2.2.heap=mark.2.2
  cases run : (Source.dispatch G F n input).run (s.1,{s.2 with heap:=Source.Heap.empty}) with
  | mk status child =>
    cases status with
    | ok data => rfl
    | error h => cases h <;> rfl

/-- Actual external instance runner with the caller's Source mark and Source
local boundary. This does not supply a full-topic trace adapter for all code. -/
def runInstance {E Γ} (G : Glob E) (caller : EMState E Γ) (n : Nat)
    a sender value input static contract depth :=
  (Source.EM.sub (L0 E) (Source.enterInstance G (n+1) a sender value input static contract depth
    (caller.2.ex.journal.length,caller.2.logs.length,caller.2.heap))).run caller

theorem runInstance_frame {E Γ} (G : Glob E) (caller : EMState E Γ) (n : Nat)
    a sender value input static contract depth :
    (runInstance G caller n a sender value input static contract depth).2.1=caller.1 ∧
    (runInstance G caller n a sender value input static contract depth).2.2.heap=caller.2.heap := by
  rcases caller with ⟨locals,state⟩
  have heap := enterInstance_heap G (⟨L0 E,state⟩ : EMState E []) n
    a sender value input static contract depth (state.ex.journal.length,state.logs.length,state.heap)
  unfold runInstance
  rw [Source.run_sub]
  cases run : (Source.enterInstance G (n+1) a sender value input static contract depth
      (state.ex.journal.length,state.logs.length,state.heap)).run (L0 E,state) with
  | mk status after =>
    rw [run] at heap
    rcases after with ⟨childLocals,childState⟩
    cases status <;> exact ⟨rfl,heap⟩

end Solidity.Yul.World.CallerFrame
