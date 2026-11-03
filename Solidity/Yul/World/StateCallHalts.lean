import Solidity.Yul.World.StateCallStatic

/-! Actual pre-write source timeout for the state-changing body. A timeout
is pending, not EVM revert; no source/physical journal effect is fabricated. -/
namespace Solidity.Yul.World.StateCall
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.ReturningCall (answerDecl uint child)

theorem internal_timeout (failed : Bool) (G : Glob env) (s : Source.EMState env []) (cd : Bytes := []) :
    (Source.callInternal (glob failed G) (child cd) 3 answerDecl .nil [uint]).run s=(.error .timeout,s) := by
  cases failed <;> cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem dispatch_timeout (failed : Bool) (G : Glob env) (s : Source.EMState env []) (cd : Bytes := []) :
    (Source.dispatch (glob failed G) (child cd) 4 (input G)).run s=(.error .timeout,s) := by
  rw [Source.dispatch,StateCall.picked failed G cd,input_nonempty]
  simp only [signature,input_length]
  change ((do
    let (r,_) ← Source.EM.sub (Source.L0 env) (Source.callInternal (glob failed G) (child cd) 3 answerDecl .nil [uint])
    Source.encodeVals (child cd) 3 false (← Source.EM.lift (Source.unRet [uint] r))).run s)=_
  rw [Source.Hoare.run_bind,Source.run_sub,internal_timeout failed G _ cd]

theorem enter_timeout (failed : Bool) (G : Glob env) (s : Source.EMState env [])
    (mark : Nat × Nat × Source.Heap env.layout) :
    (Source.enterInstance (glob failed G) 5 CallerFrameChecks.receiver CallerFrameChecks.owner 7 (input G) false "Finite" 1 mark).run s=
      (.error .timeout,(s.1,{s.2 with heap:=mark.2.2})) := by
  let cleared : Source.EMState env [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have caught : (Source.EM.attempt (Source.dispatch (glob failed G) (child (input G)) 4 (input G))).run cleared=
      (.ok (.error .timeout),cleared) := by
    change (match (Source.dispatch (glob failed G) (child (input G)) 4 (input G)).run cleared with
      | (r,t)=>((Except.ok r : Except Halt (Except Halt Bytes)),t))=_
    rw [dispatch_timeout failed G cleared (input G)]
  rw [Source.enterInstance,Source.Hoare.run_bind]
  change ((do
    let r ← Source.EM.attempt (Source.dispatch (glob failed G) (child (input G)) 4 (input G))
    Source.EM.modSt (fun t=>{t with heap:=mark.2.2})
    match r with
    | .ok data => pure (Outcome.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (Outcome.revert data)
    | .error halt => Source.EM.halt halt).run cleared)=_
  rw [Source.Hoare.run_bind,caught]
  rfl



theorem source_timeout (failed : Bool) (G : Glob env) (s : EMState env [])
    (next : ExecState env.layout env.lay env.lay)
    (code : (s.2.ex.world.accounts CallerFrameChecks.receiver).code=some 0)
    (transfer : s.2.ex.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some next) :
    (Source.callAddr (glob failed G) ReturningCall.parentFrame 6 CallerFrameChecks.receiver 7 (input G) false).run s=
      (.error .timeout,transferred s next) := by
  simp only [Source.callAddr,ReturningCall.parentFrame,show ¬(0 ≥ 1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,ReturningCall.run_pure,
    StateCall.selected failed G s code,ReturningCall.run_mark,ReturningCall.run_st,
    show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,transfer,
    ReturningCall.run_modSt,Bool.not_true,Bool.false_or,transferred]
  rw [enter_timeout]

theorem empty_dispatch (failed : Bool) (G : Glob env) (s : EMState env []) :
    (Source.dispatch (glob failed G) child 8 []).run s=(.error (.revert []),s) := by
  rw [Source.dispatch]
  cases h : (glob failed G).pickFn child [] <;> rfl

end Solidity.Yul.World.StateCall
