import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveStep

/-! Native scalar-return and turn equations for the real recursive family.
Child execution premises are discharged by the all-horizon induction. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarRecursiveSource
open Evm Evm.Memory RecursiveSource

def entered {C : Contract} {R : RefTy} (σ : State C (Frame R)) (n : Nat) (bound : n<W) (ref : HRef σ.H R) :=
 (σ.withEnv (Δ:=Parameters R) (countValue n bound,(some ref,()))).push (t:=.val .uint) (PrimTy.dflt .uint)

theorem zero_return {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true) (depth : Nat)
 (σ : State C (Frame R)) (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue 0 W_pos) :
 (body R hm (depth+1)).run σ=.ok ⟨finished σ 0 W_pos,List.prefix_refl _⟩ := by
 rw [successor_run hm depth σ]
 have guarded := guard_eval σ 0 (congrArg (fun x : PrimTy.uint.Denote => x.val) counter)
 simp only [TRun.seq,TRun.ite,guarded,show decide (0<(0:Nat))=false from rfl,
   boolT,TRun.nil,ok_bind,Except.map]
 rfl

theorem call_result {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true) (depth : Nat)
 (σ : State C (Frame R)) (n : Nat) (bound : n+1<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue (n+1) bound)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref)
 (nested : (body R hm depth).run (entered σ n (by omega) ref)=
   if n<depth then .ok ⟨finished (entered σ n (by omega) ref) n (by omega),List.prefix_refl _⟩ else .error .exhausted) :
 TRun.call (next R hm) (result R) (body (C:=C) R hm depth).ext (body R hm depth).runR σ=
 if n<depth then .ok ⟨finished σ n (by omega),List.prefix_refl _⟩ else .error .exhausted := by
 have args := next_eval hm σ n bound ref counter alias
 have scope : (body (C:=C) R hm depth).ext=Ext.refl := Subsingleton.elim _ _
 unfold TRun.call
 simp only [args,ok_bind,result,CallRet.enterT,scope]
 change (do
   let out ← (body R hm depth).run (entered σ n (by omega) ref)
   pure (⟨out.st.withEnv
     ((result R).leaveT (TEnv.wk ((List.prefix_refl σ.H).trans out.ext) (Frame R) σ.env)
       (TEnv.take [.val .uint] out.st.env)),(List.prefix_refl σ.H).trans out.ext⟩ : Solidity.Out C σ.H (Frame R)))=_
 rw [nested]
 by_cases enough : n<depth
 · simp only [if_pos enough,ok_bind,result,CallRet.leaveT,TEnv.wk_self]
   rfl
 · simp only [if_neg enough,error_bind]

theorem arm_result {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true) (depth : Nat)
 (σ : State C (Frame R)) (n : Nat) (bound : n+1<W)
 (recursive : TRun.call (next R hm) (result R) (body (C:=C) R hm depth).ext (body R hm depth).runR σ=
   if n<depth then .ok ⟨finished σ n (by omega),List.prefix_refl _⟩ else .error .exhausted) :
 (arm R hm depth (fun _ => body R hm depth)).run σ=
 if n<depth then .ok ⟨finished σ (n+1) bound,List.prefix_refl _⟩ else .error .exhausted := by
 have called : (.callRec "scalarCountdown" depth (next R hm) (result R) (fun _ => body R hm depth) :
     Stmt C (Frame R) (Frame R)).run σ=
     if n<depth then .ok ⟨finished σ n (by omega),List.prefix_refl _⟩ else .error .exhausted := recursive
 by_cases enough : n<depth
 · rw [if_pos enough] at called ⊢
   have advanced := increment_run (finished σ n (by omega)) n bound rfl
   rw [arm,Prog.run_cons_ok called,Prog.run_cons_ok advanced,Prog.run_nil]
   rfl
 · rw [if_neg enough] at called ⊢
   change TRun.seq (.callRec "scalarCountdown" depth (next R hm) (result R) (fun _ => body R hm depth) :
     Stmt C (Frame R) (Frame R)).runR (TRun.seq increment.runR TRun.nil) σ=_
   change (.callRec "scalarCountdown" depth (next R hm) (result R) (fun _ => body R hm depth) :
     Stmt C (Frame R) (Frame R)).runR σ=.error .exhausted at called
   simp only [TRun.seq,called]

theorem turn_result {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true) (depth : Nat)
 (σ : State C (Frame R)) (n : Nat) (bound : n+1<W)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue (n+1) bound)
 (recursive : TRun.call (next R hm) (result R) (body (C:=C) R hm depth).ext (body R hm depth).runR σ=
   if n<depth then .ok ⟨finished σ n (by omega),List.prefix_refl _⟩ else .error .exhausted) :
 (body R hm (depth+1)).run σ=
 if n<depth then .ok ⟨finished σ (n+1) bound,List.prefix_refl _⟩ else .error .exhausted := by
 rw [successor_run hm depth σ]
 have guarded := guard_eval σ (n+1) (congrArg (fun x : PrimTy.uint.Denote => x.val) counter)
 have actual := arm_result hm depth σ n bound recursive
 change (arm R hm depth (fun _ => body R hm depth)).runR σ=_ at actual
 by_cases enough : n<depth
 · simp only [TRun.seq,TRun.ite,guarded,show decide (0<n+1)=true from decide_eq_true (by omega),
     boolT,actual,if_pos enough,TRun.nil,Except.map,ok_bind]
   rfl
 · simp only [TRun.seq,TRun.ite,guarded,show decide (0<n+1)=true from decide_eq_true (by omega),
     boolT,actual,if_neg enough,ok_bind,Except.map]
   rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarRecursiveSource
