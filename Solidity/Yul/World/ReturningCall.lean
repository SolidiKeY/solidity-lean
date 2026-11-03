import Solidity.Yul.World.KnownSequence

/-! Actual selected typed function return through Source's existing encoder.
Selectors use the supplied Fixed hash, not an assumed calldata certificate. -/
namespace Solidity.Yul.World.ReturningCall
open Solidity.Source
open Solidity.Roadmap (Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion

def uint : STy := .int IntTy.u256
def answerDecl : Decl := ⟨.function,"answer",some "Finite",false,
  .function (.ident "answer") .nil (some .external) (some .payable) .nil false none
    (.cons (.param (.elem (.int false 256 (by decide))) none none) .nil) (.some (.block .nil))⟩
def errorDecl : Decl := ⟨.error,"Denied",some "Finite",false,
  .error "Denied" (.cons (.errorParam (.elem (.int false 256 (by decide))) none) .nil)⟩
def env : Env := ⟨answerDecl::errorDecl::CallbackSuccess.env.decls⟩
def value : Nat := 0x11223344 * 2^224 + 0x55
def body : RBody env := ⟨[],[uint],false,[uint],[uint],
  .stmt (.retVal rfl (.const (Q.ofInt value)) (by decide)) .nil,[]⟩
def glob (G : Glob env) : Glob env :=
  {G with prog:={G.prog with contracts:=["Finite"],body:=fun d=>if d.name="answer" then some body else none}}
def input (G : Glob env) : Bytes := (glob G).selector (sigOf env.layout "answer" [])
def output : Bytes := wordBytes (toWord value)
def child : Fr := ⟨CallerFrameChecks.receiver,CallerFrameChecks.owner,7,false,"Finite",true,1⟩

theorem input_length (G : Glob env) : (input G).length=4 := by
  simp only [input,Glob.selector,List.length_take,wordBytes_length]
  rfl

theorem input_nonempty (G : Glob env) : (input G).isEmpty=false := by
  apply List.isEmpty_eq_false_iff.mpr
  intro nil
  have impossible : (4 : Nat)=0 := (input_length G).symm.trans (congrArg List.length nil)
  exact (by decide : (4 : Nat)≠0) impossible

theorem exposed : env.exposed "Finite"=[answerDecl] := rfl

theorem resolved (G : Glob env) : (glob G).dispatchFn "Finite" answerDecl=answerDecl := rfl

theorem signature : answerDecl.fnSig env=some ([],[uint]) := rfl

theorem found (G : Glob env) : (glob G).prog.body answerDecl=some body := rfl

theorem picked (G : Glob env) : (glob G).pickFn child (input G)=some answerDecl := by
  rw [Glob.pickFn]
  change ([answerDecl].find? (fun d=>((glob G).prog.body ((glob G).dispatchFn "Finite" d)).isSome &&
    match d.fnSig env with
    | some (ps,_) => (glob G).selector (sigOf env.layout d.name ps)==(input G).take 4
    | none => false))=_
  simp only [List.find?_cons,resolved,found,Option.isSome_some,signature,Bool.true_and]
  rw [List.take_of_length_le (by rw [input_length]; exact Nat.le_refl _)]
  simp only [input,answerDecl,BEq.rfl]

theorem internal_run (G : Glob env) (s : Source.EMState env []) :
    (Source.callInternal (glob G) child 7 answerDecl .nil [uint]).run s=
      (.ok (.val (.int (value : Int) (by decide))),s) := by
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem dispatch_run (G : Glob env) (s : Source.EMState env []) :
    (Source.dispatch (glob G) child 8 (input G)).run s=(.ok output,s) := by
  rw [Source.dispatch,picked,input_nonempty]
  simp only [signature,input_length]
  change ((do
    let (r,_) ← Source.EM.sub (Source.L0 env) (Source.callInternal (glob G) child 7 answerDecl .nil [uint])
    Source.encodeVals child 7 false (← Source.EM.lift (Source.unRet [uint] r))).run s)=_
  rw [Source.Hoare.run_bind,Source.run_sub,internal_run]
  rfl

theorem enter_run (G : Glob env) (s : Source.EMState env [])
    (mark : Nat × Nat × Source.Heap env.layout) :
    (Source.enterInstance (glob G) 9 CallerFrameChecks.receiver CallerFrameChecks.owner 7 (input G) false "Finite" 1 mark).run s=
      (.ok (.success output),(s.1,{s.2 with heap:=mark.2.2})) := by
  let cleared : Source.EMState env [] := ⟨s.1,{s.2 with heap:=Source.Heap.empty}⟩
  have caught : (Source.EM.attempt (Source.dispatch (glob G) child 8 (input G))).run cleared=
      (.ok (.ok output),cleared) := by
    change (match (Source.dispatch (glob G) child 8 (input G)).run cleared with | (r,t)=>((Except.ok r : Except Halt (Except Halt Bytes)),t))=_
    rw [dispatch_run]
  rw [Source.enterInstance,Source.Hoare.run_bind]
  change ((do
    let r ← Source.EM.attempt (Source.dispatch (glob G) child 8 (input G))
    Source.EM.modSt (fun t=>{t with heap:=mark.2.2})
    match r with
    | .ok data => pure (Outcome.success data)
    | .error (.revert data) => do Source.rollbackTo mark; pure (Outcome.revert data)
    | .error halt => Source.EM.halt halt).run cleared)=_
  rw [Source.Hoare.run_bind,caught]
  rfl

def initial : Source.ExecState env.layout env.lay env.lay := ⟨⟨fun _=>Source.Account.empty _⟩,.empty,[]⟩
def entryExecution := ((initial.apply (.account CallerFrameChecks.owner (fun a=>{a with balance:=11,nonce:=1,code:=some 0}))).apply
  (.account CallerFrameChecks.receiver (fun a=>{a with balance:=23,nonce:=2,code:=some 0}))).apply (.account CallerFrameChecks.owner id)
def moved := (entryExecution.apply (.account CallerFrameChecks.owner (fun a=>a.withBalance 4))).apply
  (.account CallerFrameChecks.receiver (fun a=>a.withBalance 30))
def parentFrame : Fr := ⟨CallerFrameChecks.owner,CallerFrameChecks.sender,0,false,"Finite",true,0⟩
def after {Γ} (s : Source.EMState env Γ) : Source.EMState env Γ := ⟨s.1,{s.2 with ex:=moved}⟩

theorem run_pure {E Γ α} (v : α) (s : Source.EMState E Γ) :
    (pure v : Source.EM E Γ α).run s=(.ok v,s) := rfl

theorem run_st {E Γ} (s : Source.EMState E Γ) : Source.EM.st.run s=(.ok s.2,s) := rfl

theorem run_modSt {E Γ} (f : Source.St E→Source.St E) (s : Source.EMState E Γ) :
    (Source.EM.modSt f).run s=(.ok (), (s.1,f s.2)) := rfl

theorem run_mark {E Γ} (s : Source.EMState E Γ) :
    Source.mark.run s=(.ok (s.2.ex.journal.length,s.2.logs.length,s.2.heap),s) := rfl

theorem selected (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution) :
    (Source.instanceAt (glob G) CallerFrameChecks.receiver).run s=(.ok (some "Finite"),s) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  rfl

theorem transfer_actual : entryExecution.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some moved := rfl

theorem source_run (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution) :
    (Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 7 (input G) false).run s=
      (.ok (.success output),after s) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  simp only [Source.callAddr,parentFrame,show ¬(0 ≥ 1024) from by decide,if_false,
    Bool.false_and,Bool.false_eq_true,Source.Hoare.run_bind,run_pure,selected G (l,⟨entryExecution,h,events,logs,fn⟩) rfl,
    run_mark,run_st,show CallerFrameChecks.receiver≠CallerFrameChecks.owner from by decide,
    transfer_actual,run_modSt,Bool.not_true,Bool.false_or,after]
  rw [enter_run]

theorem output_exact : output=[0x11,0x22,0x33,0x44]++List.replicate 27 0++[0x55] := rfl

end Solidity.Yul.World.ReturningCall
