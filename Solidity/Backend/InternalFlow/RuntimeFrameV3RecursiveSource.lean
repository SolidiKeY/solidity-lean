import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV1
import Solidity.Semantics.RunWk

/-! A genuine recursive source family over existing intrinsic typed syntax.
Arguments retain a real memory reference while the uint counter decreases.
No source evaluator, target simulation or admission cutoff is defined here. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource
open Evm Evm.Memory
abbrev Parameters (R : RefTy) : Ctx := [.val .uint,.mem R]
def countValue (n : Nat) (bound : n<W) : PrimTy.uint.Denote := indexValue ⟨n,bound⟩

def nonzero {C : Contract} {R : RefTy} : Val C (Parameters R) .bool :=
 .binop .gt rfl rfl (.simple (.local .here)) (.simple (.lit 0 rfl))
def nextArgs {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) : Args C (Parameters R) (Parameters R) :=
 .snoc (.snocMemory .nil R (.user "alias") (.var (.there .here) hm)) .uint (.user "count")
 (.binop .sub rfl rfl (.simple (.local .here)) (.simple (.lit 1 rfl)))

def step {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (d : Nat)
 (back : Unit → Prog C (Parameters R) (Parameters R)) : Prog C (Parameters R) (Parameters R) :=
 .cons (.ite nonzero (.cons (.callRec "countdown" d (nextArgs R hm) .none back) .nil) .nil) .nil

def body {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (n : Nat) : Prog C (Parameters R) (Parameters R) :=
 recUnroll Prog.recBase (step R hm) n

set_option backward.isDefEq.respectTransparency false in
theorem guard_eval {C : Contract} {R : RefTy} (σ : State C (Parameters R)) (n : Nat)
 (h : (TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env).val=(n:Int)) :
 (nonzero (C:=C) (R:=R)).evalT σ=.ok (decide (0<n)) := by
 change Except.ok (decide ((0:Int)<(TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env).val))=_
 rw [h]
 simp only [show ((0:Int)<(n:Int)) ↔ 0<n from by omega]

set_option backward.isDefEq.respectTransparency false in
theorem next_eval {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (σ : State C (Parameters R)) (n : Nat) (bound : n+1<W)
 (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue (n+1) bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref) :
 (nextArgs R hm).evalT σ=.ok (countValue n (by omega),(some ref,())) := by
 have range : PrimTy.uint.inRange (n:Int)=true := by
   change decide (0≤(n:Int) ∧ (n:Int)<(W:Int))=true
   exact decide_eq_true ⟨Int.natCast_nonneg n,Int.ofNat_lt.mpr (by omega)⟩
 have subtract : ((n+1:Nat):Int)-1=(n:Int) := by omega
 simp only [nextArgs,Args.evalT,MPath.mvalT,alias,Val.evalT,Simple.evalT,counter,
   PrimTy.ofLit,BinOp.shortT,BinOp.evalT,BinOp.evalNum,BinOp.arithInt,countValue,indexValue,
   subtract,Option.bind_some,PrimTy.ofInt?,range,dite_eq_left,TRes.ofOpt,ok_bind]
 rfl
/-- Exact execution at EVERY intrinsic unrolling horizon. Exhaustion stays
exhaustion; successful recursion restores the complete caller state, including
its memory reference, rather than returning a fabricated failed State. -/
theorem all_horizons {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (depth : Nat) (σ : State C (Parameters R)) (count : Nat) (bound : count<W)
 (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref) :
 (body R hm depth).run σ =
 if count<depth then .ok ⟨σ,List.prefix_refl _⟩ else .error .exhausted := by
 induction depth generalizing σ count with
 | zero =>
   change (.error .exhausted : TRes (Solidity.Out C σ.H (Parameters R))) = _
   simp only [Nat.not_lt_zero,ite_false]
 | succ depth ih =>
   have evaluated := guard_eval σ count (congrArg (fun v : PrimTy.uint.Denote => v.val) counter)
   change TRun.seq
     (TRun.ite nonzero .refl
       (TRun.seq (TRun.call (nextArgs R hm) .none .refl (body R hm depth).runR) TRun.nil)
       .refl TRun.nil) TRun.nil σ = _
   cases count with
   | zero =>
     simp only [TRun.seq,TRun.ite,evaluated,show decide (0<(0:Nat))=false from rfl,
       boolT,TRun.nil,Except.map,Nat.zero_lt_succ,ite_true]
     rfl
   | succ count =>
     have args := next_eval hm σ count bound ref counter alias
     let child : State C (Parameters R) := σ.withEnv (countValue count (by omega),(some ref,()))
     have nested := ih child count (by omega) ref rfl rfl
     have weakened := TEnv.wk_self (List.prefix_refl σ.H) (Parameters R) σ.env
     have recursive : TRun.call (nextArgs R hm) .none .refl (body R hm depth).runR σ =
       if count<depth then .ok ⟨σ,List.prefix_refl _⟩ else .error .exhausted := by
       unfold TRun.call
       simp only [args,CallRet.enterT]
       change (do
         let out ← (body R hm depth).run child
         pure (⟨out.st.withEnv (TEnv.wk ((List.prefix_refl σ.H).trans out.ext) (Parameters R) σ.env),
           (List.prefix_refl σ.H).trans out.ext⟩ : Solidity.Out C σ.H (Parameters R))) = _
       rw [nested]
       by_cases enough : count<depth
       · simp only [ite_eq_left enough,ok_bind]
         change (Except.ok (⟨child.withEnv (TEnv.wk (List.prefix_refl σ.H) (Parameters R) σ.env),List.prefix_refl _⟩ : Solidity.Out C σ.H (Parameters R)) : TRes (Solidity.Out C σ.H (Parameters R))) = _
         rw [weakened]
         rfl
       · simp only [ite_eq_right enough,error_bind]
     have enough : count+1<depth+1 ↔ count<depth := by omega
     simp only [TRun.seq,TRun.ite,evaluated,show decide (0<count+1)=true from decide_eq_true (by omega),
       boolT,recursive,enough]
     by_cases done : count<depth
     · simp only [ite_eq_left done,TRun.nil,Except.map]
       rfl
     · simp only [ite_eq_right done]
       rfl

/-- Ordinary source entry arguments use existing typed caller destinations.
The recursive body's arguments are nextArgs; only the initial entry is here. -/
def entryArgs {C : Contract} {Γ : Ctx} (R : RefTy) (hm : (Ty.ref R).mapFree=true)
 (reference : Idx Γ (.mem R)) (counter : Idx Γ (.val .uint)) : Args C Γ (Parameters R) :=
 .snoc (.snocMemory .nil R (.user "alias") (.var reference hm)) .uint (.user "count") (.simple (.local counter))

theorem call_all_horizons {C : Contract} {Γ : Ctx} {R : RefTy}
 (hm : (Ty.ref R).mapFree=true) (f : Name) (args : Args C Γ (Parameters R))
 (depth : Nat) (caller : State C Γ) (count : Nat) (bound : count<W) (ref : HRef caller.H R)
 (evaluated : args.evalT caller=.ok (countValue count bound,(some ref,()))) :
 (InterfaceV1.recursiveSource f args .none (step R hm) depth).run caller =
 if count<depth then .ok ⟨caller,List.prefix_refl _⟩ else .error .exhausted := by
 let child : State C (Parameters R) := caller.withEnv (countValue count bound,(some ref,()))
 have inner := all_horizons hm depth child count bound ref rfl rfl
 change TRun.call args .none .refl (body R hm depth).runR caller = _
 unfold TRun.call
 simp only [evaluated,CallRet.enterT]
 change (do
   let out ← (body R hm depth).run child
   pure (⟨out.st.withEnv (TEnv.wk ((List.prefix_refl caller.H).trans out.ext) Γ caller.env),
     (List.prefix_refl caller.H).trans out.ext⟩ : Solidity.Out C caller.H Γ)) = _
 rw [inner]
 by_cases enough : count<depth
 · simp only [ite_eq_left enough,ok_bind]
   change (Except.ok (⟨child.withEnv (TEnv.wk (List.prefix_refl caller.H) Γ caller.env),List.prefix_refl _⟩ : Solidity.Out C caller.H Γ) : TRes (Solidity.Out C caller.H Γ)) = _
   rw [TEnv.wk_self]
   rfl
 · simp only [ite_eq_right enough,error_bind]

/-- The actual source-coherence duty for this effect-free countdown family.
No successful source output or desired coherence equation is assumed. -/
theorem source_coherence {C : Contract} {Γ : Ctx} {R : RefTy}
 (hm : (Ty.ref R).mapFree=true) (f : Name)
 (reference : Idx Γ (.mem R)) (counter : Idx Γ (.val .uint)) :
 InterfaceV1.RecursiveReturnCoherence (C:=C) f (entryArgs R hm reference counter) .none (step R hm) := by
 intro caller n k left right leftRun rightRun
 cases hasRef : TEnv.get reference caller.env with
 | none =>
   have failed : (entryArgs R hm reference counter).evalT caller=.error .revert := by
     simp only [entryArgs,Args.evalT,MPath.mvalT,hasRef,error_bind]
     rfl
   change TRun.call (entryArgs R hm reference counter) .none .refl (body R hm n).runR caller=_ at leftRun
   simp only [TRun.call,failed,error_bind] at leftRun
   cases leftRun
 | some ref =>
   let value := TEnv.get counter caller.env
   have numeric : value=countValue value.word.val value.word.isLt :=
     Subtype.ext (Evm.word_val value).symm
   have args : (entryArgs R hm reference counter).evalT caller=
       .ok (countValue value.word.val value.word.isLt,(some ref,())) := by
     simp only [entryArgs,Args.evalT,MPath.mvalT,hasRef,Val.evalT,Simple.evalT,ok_bind]
     exact congrArg (fun v => Except.ok (v,(some ref,()))) numeric
   have first := call_all_horizons hm f (entryArgs R hm reference counter) n caller value.word.val value.word.isLt ref args
   have second := call_all_horizons hm f (entryArgs R hm reference counter) k caller value.word.val value.word.isLt ref args
   rw [first] at leftRun
   rw [second] at rightRun
   split at leftRun
   · split at rightRun
     · exact (Except.ok.inj leftRun).symm.trans (Except.ok.inj rightRun)
     · cases rightRun
   · cases leftRun

end Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource
