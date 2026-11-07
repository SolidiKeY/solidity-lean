import Solidity.Yul.Composition.ScopeCatchPhysical

/-! Actual captured allocated typed LOCAL → existing resolved canonical rethrow.
A consumer router, not general Source try selection. EM.sub restores locals but
never rolls back Source/world effects. Raw caller is an unchanged companion. -/
namespace Solidity.Yul.Composition.RethrowPhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls LocalPhysicalControls

/-- Execute the real resolved statement using the ACTUAL supplied scoped locals.
The evaluator itself has an empty local context, restored by actual EM.sub. -/
def scopedRethrow {E Γ Δ} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (index : Source.Idx Δ (.bytes .memory)) (inside : Source.Locals E.layout Δ) :
    Source.EM E Γ (List UInt8) := do
  let _ ← Source.EM.sub .nil (Source.execS G F fuel 0 none
    (.rethrow index : Source.RStmt E [] false ⟨false,false⟩ _ _) inside)
  pure []

theorem exec_rethrow_succ {E Γ} (G : Source.Glob E) (F : Source.Fr) (fuel address : Nat)
    (bytes : List UInt8) (inside : Source.Locals E.layout Γ) (index : Source.Idx Γ (.bytes .memory))
    (state : Source.St E) (reference : inside.get index = .memRef rfl address)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execS G F (fuel+1) 0 none
      (.rethrow index : Source.RStmt E [] false ⟨false,false⟩ _ _) inside).run (.nil,state) =
      (Except.error (.revert bytes),(.nil,state)) := by
  rw [Source.execS,reference]
  change (do let data ← Source.heapBytes address; Source.EM.halt (.revert data) : Source.EM E [] _).run (.nil,state) = _
  rw [Source.Hoare.run_bind]
  have read : (Source.heapBytes address : Source.EM E [] _).run (.nil,state) = (Except.ok bytes,(.nil,state)) :=
    HeapCatchPhysical.bytesOf_ref_run F address bytes .nil state found
  rw [read]
  rfl

theorem scope_succ {E Γ Δ} (G : Source.Glob E) (F : Source.Fr) (fuel address : Nat)
    (bytes : List UInt8) (inside : Source.Locals E.layout Δ) (index : Source.Idx Δ (.bytes .memory))
    (outer : Source.Locals E.layout Γ) (state : Source.St E)
    (reference : inside.get index = .memRef rfl address)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (scopedRethrow G F (fuel+1) index inside).run (outer,state) =
      (Except.error (.revert bytes),(outer,state)) := by
  unfold scopedRethrow
  rw [Source.Hoare.run_bind,ScopeCatchPhysical.sub_run,exec_rethrow_succ G F fuel address bytes inside index state reference found]

theorem scope_zero {E Γ Δ} (G : Source.Glob E) (F : Source.Fr)
    (inside : Source.Locals E.layout Δ) (index : Source.Idx Δ (.bytes .memory))
    (outer : Source.Locals E.layout Γ) (state : Source.St E) :
    (scopedRethrow G F 0 index inside).run (outer,state) =
      (Except.error .timeout,(outer,state)) := rfl

/-- Consumer route only: success bypasses rethrow, every other halt propagates.
For caught bytes use the actual returned inner locals, not a rebuilt reference. -/
def route (G : Source.Glob originEnv) (fuel : Nat)
    (result : Except Source.Halt (Except Source.Halt ((List UInt8) ⊕
      (Source.Val originEnv.layout (.bytes .memory) × (List UInt8 × Source.Locals originEnv.layout ScopeCatchPhysical.Inner))))) :
    Source.EM originEnv ScopeCatchPhysical.Outer (List UInt8) :=
  match result with
  | .error halt | .ok (.error halt) => Source.EM.halt halt
  | .ok (.ok (.inl bytes)) => pure bytes
  | .ok (.ok (.inr (_,(_,inside)))) => scopedRethrow G packedStepFrame fuel .here inside

def run (G : Source.Glob originEnv) (outcome : Except Source.Halt (List UInt8)) (fuel : Nat) :=
  let execution :=  (ScopeCatchPhysical.run outcome).2
  (execution,AttemptPhysical.companion (route G fuel execution.1.1) execution.1.2.1 execution.2)

theorem captured_rethrow (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (run G (.error (.revert bytes)) (fuel+1)).2 =
      ((.ok (.error (.revert bytes)),(ScopeCatchPhysical.outer,(HeapCatchPhysical.allocated bytes).2.2)),
        (HeapCatchPhysical.allocated bytes).2) := by
  unfold run
  dsimp only
  rw [ScopeCatchPhysical.bound_capture_result,ScopeCatchPhysical.caller_scope_restored,ScopeCatchPhysical.raw_and_frame_retained]
  unfold route AttemptPhysical.companion
  have object : (HeapCatchPhysical.allocated bytes).2.2.heap.get 1 = some ⟨.bytes .memory,.bytes bytes⟩ := by
    simpa only [ScopeCatchPhysical.input_next] using HeapCatchPhysical.object_contents bytes
  rw [AttemptPhysical.attempt_run,scope_succ G packedStepFrame fuel 1 bytes
    _ .here ScopeCatchPhysical.outer _ rfl object]

theorem captured_zero (G : Source.Glob originEnv) (bytes : List UInt8) :
    (run G (.error (.revert bytes)) 0).2 =
      ((.ok (.error .timeout),(ScopeCatchPhysical.outer,(HeapCatchPhysical.allocated bytes).2.2)),
        (HeapCatchPhysical.allocated bytes).2) := by
  unfold run
  dsimp only
  rw [ScopeCatchPhysical.bound_capture_result,ScopeCatchPhysical.caller_scope_restored,ScopeCatchPhysical.raw_and_frame_retained]
  rfl

theorem success (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (run G (.ok bytes) fuel).2.1.1 = .ok (.ok bytes) := rfl

theorem timeout (G : Source.Glob originEnv) (fuel : Nat) :
    (run G (.error .timeout) fuel).2.1.1 = .ok (.error .timeout) := rfl

theorem stuck (G : Source.Glob originEnv) (why : String) (fuel : Nat) :
    (run G (.error (.stuck why)) fuel).2.1.1 = .ok (.error (.stuck why)) := rfl

/-- Wrong same-type index rethrows OLD AABB, not caught DEAD of equal length. -/
theorem wrong_index (G : Source.Glob originEnv) (fuel : Nat) :
    (scopedRethrow G packedStepFrame (fuel+1) (.there .here) ScopeCatchPhysical.inner).run
      (ScopeCatchPhysical.outer,(HeapCatchPhysical.allocated [0xde,0xad]).2.2) =
      (Except.error (.revert [0xaa,0xbb]),(ScopeCatchPhysical.outer,(HeapCatchPhysical.allocated [0xde,0xad]).2.2)) :=
  scope_succ G packedStepFrame fuel 0 _ _ _ _ _ rfl rfl

def danglingInner : Source.Locals originEnv.layout ScopeCatchPhysical.Inner :=
  .cons (.memRef rfl 2) ScopeCatchPhysical.outer

theorem dangling (G : Source.Glob originEnv) (fuel : Nat) :
    (scopedRethrow G packedStepFrame (fuel+1) .here danglingInner).run
      (ScopeCatchPhysical.outer,(HeapCatchPhysical.allocated [0xde,0xad]).2.2) =
      (Except.error (.stuck "dangling memory reference"),(ScopeCatchPhysical.outer,(HeapCatchPhysical.allocated [0xde,0xad]).2.2)) := by
  unfold scopedRethrow
  rw [Source.Hoare.run_bind,ScopeCatchPhysical.sub_run,Source.execS]
  rfl

/-- The generic law covers ALL positive horizons, without stability assumptions. -/
theorem positive_unique (G : Source.Glob originEnv) (bytes : List UInt8) (first second : Nat) :
    (run G (.error (.revert bytes)) (first+1)).2 = (run G (.error (.revert bytes)) (second+1)).2 := by
  rw [captured_rethrow,captured_rethrow]

theorem raw_retained (G : Source.Glob originEnv) (outcome : Except Source.Halt (List UInt8)) (fuel : Nat) :
    (run G outcome fuel).2.2.1 = (ScopeCatchPhysical.run outcome).2.2.1 := rfl

theorem restored (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (run G (.error (.revert bytes)) (fuel+1)).2.1.2.1 = ScopeCatchPhysical.outer := by
  rw [captured_rethrow]

theorem full_post (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (run G (.error (.revert bytes)) (fuel+1)).2.2 = (HeapCatchPhysical.allocated bytes).2 := by
  rw [captured_rethrow]

theorem nonword_retained (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (run G (.error (.revert bytes)) (fuel+1)).2.2.1.get memoryRef.index =
      (LocalValues.ofClean locals).get memoryRef.index := by
  rw [full_post]
  exact CatchFunctionPhysical.nonword_retained

theorem raw_not_clean (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    LocalState.clean? (run G (.error (.revert bytes)) (fuel+1)).2.2 = none := by
  rw [full_post]
  change (LocalValues.clean? ctx.tys CatchFunctionPhysical.completed.state.1).map _ = none
  cases clean : LocalValues.clean? ctx.tys CatchFunctionPhysical.completed.state.1 with
  | none => rfl
  | some values =>
      have bad := CatchFunctionPhysical.raw_not_clean
      unfold LocalState.clean? at bad
      rw [clean] at bad
      cases bad

theorem no_clean_resume (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat)
    (action : Source.EM originEnv ctx.tys Unit) :
    LocalState.runClean action (run G (.error (.revert bytes)) (fuel+1)).2.2 = none :=
  LocalState.runClean_refuses action _ (raw_not_clean G bytes fuel)

/-- Full actual composed payload controls, not a numerical length surrogate. -/
theorem dead (G : Source.Glob originEnv) :
    (run G (.error (.revert [0xde,0xad])) 32).2.1.1 = .ok (.error (.revert [0xde,0xad])) := by
  rw [show 32=31+1 from rfl,captured_rethrow]

theorem empty (G : Source.Glob originEnv) :
    (run G (.error (.revert [])) 1).2.1.1 = .ok (.error (.revert [])) := by
  rw [show 1=0+1 from rfl,captured_rethrow]

theorem panic (G : Source.Glob originEnv) :
    (run G (Source.panic .assert) 32).2.1.1 = .ok (.error (.revert (Source.panicData .assert))) := by
  change (run G (.error (.revert (Source.panicData .assert))) (31+1)).2.1.1 = _
  rw [captured_rethrow]

#print axioms captured_rethrow
#print axioms scope_succ
#print axioms dangling
end Solidity.Yul.Composition.RethrowPhysical
