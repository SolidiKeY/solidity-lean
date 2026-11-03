import Solidity.Yul.World.ReturningCall

/-! Actual custom-error body and an honest smaller-horizon assert control.
Both use existing Source APIs; no supplied revert outcome or new codec. -/
namespace Solidity.Yul.World.ReturningCall
open Solidity.Source
open Solidity.Roadmap (Bytes Outcome)

def assertBody : RBody env := ⟨[],[uint],false,[uint],[uint],
  .stmt (.expr (.builtin .assert (.cons (.bool false) .nil) rfl)) .nil,[]⟩
def failureBody : RBody env := ⟨[],[uint],false,[uint],[uint],
  .stmt (.revertError errorDecl rfl (.cons (.const (Q.ofInt value)) (by decide) .nil)) .nil,[]⟩
def errorData (G : Glob env) : Bytes := (glob G).selector (sigOf env.layout "Denied" [uint])++output
def failingGlob (G : Glob env) : Glob env :=
  {glob G with prog:={(glob G).prog with body:=fun d=>if d.name="answer" then some failureBody else none}}

theorem failure_resolved (G : Glob env) : (failingGlob G).dispatchFn "Finite" answerDecl=answerDecl := rfl

theorem failure_picked (G : Glob env) : (failingGlob G).pickFn child (input G)=some answerDecl := by
  rw [Glob.pickFn]
  change ([answerDecl].find? (fun d=>((failingGlob G).prog.body ((failingGlob G).dispatchFn "Finite" d)).isSome &&
    match d.fnSig env with
    | some (ps,_) => (failingGlob G).selector (sigOf env.layout d.name ps)==(input G).take 4
    | none => false))=_
  simp only [List.find?_cons,failure_resolved,signature]
  rw [List.take_of_length_le (by rw [input_length]; exact Nat.le_refl _)]
  have found : (failingGlob G).prog.body answerDecl=some failureBody := rfl
  have selector : (failingGlob G).selector (sigOf env.layout answerDecl.name [])=input G := rfl
  simp only [found,Option.isSome_some,Bool.true_and,selector,BEq.rfl]

theorem failure_internal (G : Glob env) (s : Source.EMState env []) :
    (Source.callInternal (failingGlob G) child 7 answerDecl .nil [uint]).run s=
      (.error (.revert (errorData G)),s) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem failure_dispatch (G : Glob env) (s : Source.EMState env []) :
    (Source.dispatch (failingGlob G) child 8 (input G)).run s=(.error (.revert (errorData G)),s) := by
  rw [Source.dispatch,failure_picked,input_nonempty]
  simp only [signature,input_length]
  change ((do
    let (r,_) ← Source.EM.sub (Source.L0 env) (Source.callInternal (failingGlob G) child 7 answerDecl .nil [uint])
    Source.encodeVals child 7 false (← Source.EM.lift (Source.unRet [uint] r))).run s)=_
  rw [Source.Hoare.run_bind,Source.run_sub,failure_internal]

theorem failure_enter (G : Glob env) (s : Source.EMState env [])
    (mark : Nat × Nat × Source.Heap env.layout) :
    (Source.enterInstance (failingGlob G) 9 CallerFrameChecks.receiver CallerFrameChecks.owner 7 (input G) false "Finite" 1 mark).run s=
      (.ok (.revert (errorData G)),((Source.rollbackTo mark).run (s.1,{s.2 with heap:=mark.2.2})).2) := by
  let cleared : Source.EMState env [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have caught : (Source.EM.attempt (Source.dispatch (failingGlob G) child 8 (input G))).run cleared=
      (.ok (.error (.revert (errorData G))),cleared) := by
    change (match (Source.dispatch (failingGlob G) child 8 (input G)).run cleared with
      | (r,t)=>((Except.ok r : Except Halt (Except Halt Bytes)),t))=_
    rw [failure_dispatch]
  rw [Source.enterInstance,Source.Hoare.run_bind]
  change ((do
    let r ← Source.EM.attempt (Source.dispatch (failingGlob G) child 8 (input G))
    Source.EM.modSt (fun t=>{t with heap:=mark.2.2})
    match r with
    | .ok data => pure (Outcome.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (Outcome.revert data)
    | .error halt => Source.EM.halt halt).run cleared)=_
  rw [Source.Hoare.run_bind,caught]
  rfl

theorem failure_selected (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution) :
    (Source.instanceAt (failingGlob G) CallerFrameChecks.receiver).run s=(.ok (some "Finite"),s) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  rfl

theorem failure_source (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution) :
    (Source.callAddr (failingGlob G) parentFrame 10 CallerFrameChecks.receiver 7 (input G) false).run s=
      (.ok (.revert (errorData G)),s) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  simp only [Source.callAddr,parentFrame,show ¬(0 ≥ 1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,run_pure,
    failure_selected G (l,⟨entryExecution,h,events,logs,fn⟩) rfl,run_mark,run_st,
    show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,
    transfer_actual,run_modSt,Bool.not_true,Bool.false_or]
  rw [failure_enter]
  change ((Except.ok (Outcome.revert (errorData G)) : Except Halt Outcome),
    ((l,⟨moved.undoN 2,h,events,logs.drop (logs.length-logs.length),fn⟩) : Source.EMState env []))=_
  simp only [moved,Source.ExecState.undoN,Source.ExecState.undo_apply,Nat.sub_self,List.drop_zero]

/-- The attempted assert body does not reach its assertion at this unchanged
horizon. The earlier desired Panic proof remains a retained failed attempt. -/
theorem assert_timeout (G : Glob env) (s : Source.EMState env []) :
    (Source.callInternal {glob G with prog:={(glob G).prog with body:=fun d=>if d.name="answer" then some assertBody else none}}
      child 7 answerDecl .nil [uint]).run s=(.error .timeout,s) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

end Solidity.Yul.World.ReturningCall
