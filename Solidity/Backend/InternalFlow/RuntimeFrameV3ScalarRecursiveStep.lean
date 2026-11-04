import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveSource
import Solidity.Semantics.RunAccel

/-! Genuine scalar-result recursion over the existing intrinsic call relation.
The private result is initialized, returned through CallRet.val, then consumed
by checked uint addition. No target compiler or profile claim is supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarRecursiveSource
open Evm Evm.Memory RecursiveSource
abbrev Frame (R : RefTy) : Ctx := .val .uint :: Parameters R

def guard {C : Contract} {R : RefTy} : Val C (Frame R) .bool :=
 .binop .gt rfl rfl (.simple (.local (.there .here))) (.simple (.lit 0 rfl))
def next {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) : Args C (Frame R) (Parameters R) :=
 .snoc (.snocMemory .nil R (.user "alias") (.var (.there (.there .here)) hm)) .uint (.user "count")
 (.binop .sub rfl rfl (.simple (.local (.there .here))) (.simple (.lit 1 rfl)))
def result (R : RefTy) : CallRet (Frame R) [.val .uint] (Frame R) := .val .uint (.user "result") (some .here)
def zero {C : Contract} {R : RefTy} : Stmt C (Frame R) (Frame R) := .assignLocal .here (.simple (.lit 0 rfl))
def increment {C : Contract} {R : RefTy} : Stmt C (Frame R) (Frame R) :=
 .assignLocal .here (.binop .add rfl rfl (.simple (.local .here)) (.simple (.lit 1 rfl)))
def arm {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (d : Nat)
 (back : Unit → Prog C (Frame R) (Frame R)) : Prog C (Frame R) (Frame R) :=
 .cons (.callRec "scalarCountdown" d (next R hm) (result R) back) (.cons increment .nil)
def step {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (d : Nat)
 (back : Unit → Prog C (Frame R) (Frame R)) : Prog C (Frame R) (Frame R) :=
 .cons (.ite guard (arm R hm d back) (.cons zero .nil)) .nil
def body {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (depth : Nat) : Prog C (Frame R) (Frame R) :=
 recUnroll Prog.recBase (step R hm) depth

def finished {C : Contract} {R : RefTy} (σ : State C (Frame R)) (n : Nat) (fit : n<W) :=
 σ.setLocal (.here : Idx (Frame R) (.val .uint)) (countValue n fit)

theorem guard_eval {C : Contract} {R : RefTy} (σ : State C (Frame R)) (n : Nat)
 (counter : (TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env).val=(n:Int)) :
 guard.evalT σ=.ok (decide (0<n)) := by
 change Except.ok (decide ((0:Int)<(TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env).val))=_
 rw [counter]
 have positive : ((0:Int)<(n:Int)) ↔ 0<n := by omega
 simp only [positive]

theorem next_eval {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (σ : State C (Frame R)) (n : Nat) (bound : n+1<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue (n+1) bound)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref) :
 (next R hm).evalT σ=.ok (countValue n (by omega),(some ref,())) := by
 have range : PrimTy.uint.inRange (n:Int)=true := by
   change decide (0≤(n:Int) ∧ (n:Int)<(W:Int))=true
   exact decide_eq_true ⟨Int.natCast_nonneg n,Int.ofNat_lt.mpr (by omega)⟩
 have subtract : ((n+1:Nat):Int)-1=(n:Int) := by omega
 simp only [next,Args.evalT,MPath.mvalT,alias,Val.evalT,Simple.evalT,counter,
   PrimTy.ofLit,BinOp.shortT,BinOp.evalT,BinOp.evalNum,BinOp.arithInt,countValue,indexValue,
   subtract,Option.bind_some,PrimTy.ofInt?,range,dif_pos,TRes.ofOpt,ok_bind]
 rfl

theorem successor_ofInt (n : Nat) (bound : n+1<W) :
 PrimTy.ofInt? .uint ((n:Int)+1)=some (countValue (n+1) bound) := by
 have range : PrimTy.uint.inRange ((n+1:Nat):Int)=true := PrimTy.inRange_uint_of_lt bound
 rw [show (n:Int)+1=((n+1:Nat):Int) from by omega]
 simp only [PrimTy.ofInt?,range,dif_pos]
 rfl

theorem increment_run {C : Contract} {R : RefTy} (σ : State C (Frame R)) (n : Nat) (bound : n+1<W)
 (value : TEnv.get (.here : Idx (Frame R) (.val .uint)) σ.env=countValue n (by omega)) :
 increment.run σ=.ok ⟨finished σ (n+1) bound,List.prefix_refl _⟩ := by
 have numeric : (TEnv.get (.here : Idx (Frame R) (.val .uint)) σ.env).val=(n:Int) :=
   congrArg (fun x : PrimTy.uint.Denote => x.val) value
 have law := (Stmt.bumps_assign (C:=C) (.here : Idx (Frame R) (.val .uint)) 1 rfl rfl rfl).2 σ
 have checked := (congrArg (fun x : Int => PrimTy.ofInt? .uint (x+1)) numeric).trans (successor_ofInt n bound)
 simp only [show Int.toNat (1:Int)=1 from rfl,Int.natCast_one] at law
 rw [checked] at law
 exact law


/-- Checked equation through the published runR/runC correspondence, retaining
actual private-scope metadata for the scalar return. -/
theorem successor_run {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (depth : Nat) (σ : State C (Frame R)) :
 (body R hm (depth+1)).run σ=
 TRun.seq (TRun.ite guard .refl (arm R hm depth (fun _ => body R hm depth)).runR
   .refl (TRun.seq zero.runR TRun.nil)) TRun.nil σ := by
 change (body R hm (depth+1)).runR σ=_
 rw [Prog.runR_eq (body R hm (depth+1)),Prog.runR_eq (arm R hm depth (fun _ => body (C:=C) R hm depth)),
   Stmt.runR_eq (zero (C:=C) (R:=R))]
 rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarRecursiveSource
