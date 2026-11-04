import Solidity.Backend.PrimitivePackets.SignedDiv.Origin
import Solidity.Backend.Passes.StatefulDivision

/-! Public compiler selection for int256 local division. Unchecked overflow is
lowered with an intrinsic conditional around the checked division, not a changed
operator or default. The original zero-divisor revert remains in both modes. -/
namespace Solidity.Backend.PrimitivePackets.SignedDiv
open Evm Evm.Memory

def minimum {C : Contract} {Γ : Ctx} : Val C Γ .int :=
 .simple (.lit (-((2^255:Nat):Int)) (by decide))
def minusOne {C : Contract} {Γ : Ctx} : Val C Γ .int := .simple (.lit (-1) (by decide))
def raw {C : Contract} {Γ : Ctx} (i j : Idx Γ (.val .int)) : Val C Γ .int :=
 .binop .div rfl rfl (.simple (.local i)) (.simple (.local j))
def overflow {C : Contract} {Γ : Ctx} (i j : Idx Γ (.val .int)) : Val C Γ .bool :=
 .binop .and rfl rfl
  (.binop .eqB rfl rfl (.simple (.local i)) minimum)
  (.binop .eqB rfl rfl (.simple (.local j)) minusOne)
def expression {C : Contract} {Γ : Ctx} (checked : Bool) (i j : Idx Γ (.val .int)) : Val C Γ .int :=
 if checked then raw i j else .ternary (overflow i j) minimum (raw i j)

theorem selectable {C : Contract} {Γ : Ctx} (b : Nat) (F : Frag Γ)
 (checked : Bool) (i j : Idx Γ (.val .int)) :
 (Memory.compileVal b F (expression (C:=C) checked i j)).isSome=true := by
 cases checked <;> rfl

def selected {C : Contract} {Γ : Ctx} (b : Nat) (F : Frag Γ)
 (checked : Bool) (i j : Idx Γ (.val .int)) : CompiledVal b F (expression (C:=C) checked i j) :=
 (Memory.compileVal b F (expression checked i j)).get (selectable b F checked i j)

theorem public_selection {C : Contract} {Γ : Ctx} (b : Nat) (F : Frag Γ)
 (checked : Bool) (i j : Idx Γ (.val .int)) :
 Memory.compileVal b F (expression (C:=C) checked i j)=some (selected b F checked i j) := by
 first | (solve | simp only [selected,Option.some_get]) | (solve | rfl) | (solve | decide) | (solve | omega)

theorem raw_run {C : Contract} {Γ : Ctx} (σ : State C Γ) (i j : Idx Γ (.val .int))
 (a b : PrimTy.int.Denote) (left : TEnv.get i σ.env=a) (right : TEnv.get j σ.env=b) :
 (raw i j).evalT σ=TRes.ofOpt (BinOp.div.evalT rfl a b) := by
 simp only [raw,Val.evalT,Simple.evalT,left,right,BinOp.shortT,bind,Except.bind]

theorem overflow_run {C : Contract} {Γ : Ctx} (σ : State C Γ) (i j : Idx Γ (.val .int))
 (a b : PrimTy.int.Denote) (left : TEnv.get i σ.env=a) (right : TEnv.get j σ.env=b) :
 (overflow i j).evalT σ=.ok (decide (a.val=-((2^255:Nat):Int) ∧ b.val = -1)) := by
 by_cases ha : a.val=-((2^255:Nat):Int) <;> by_cases hb : b.val = -1 <;>
  simp only [overflow,minimum,minusOne,Val.evalT,Simple.evalT,left,right,
   BinOp.evalT,BinOp.evalNum,BinOp.evalBool,BinOp.shortT,BinOp.ret,BinOp.isArith,PrimTy.ofLit,boolT,
   bind,Except.bind,TRes.ofOpt,ha,hb,decide_true,decide_false,
   pure,Except.pure,and_true,and_false]

 all_goals rfl

theorem expression_run {C : Contract} {Γ : Ctx} (σ : State C Γ) (checked : Bool)
 (i j : Idx Γ (.val .int)) (a b : PrimTy.int.Denote)
 (left : TEnv.get i σ.env=a) (right : TEnv.get j σ.env=b) :
 (expression checked i j).evalT σ=
 if checked then TRes.ofOpt (BinOp.div.evalT rfl a b)
 else if a.val=-((2^255:Nat):Int) ∧ b.val = -1 then .ok Backend.Scalar.minimumInt
 else TRes.ofOpt (BinOp.div.evalT rfl a b) := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 cases checked
 · simp only [expression,Bool.false_eq_true,if_false,Val.evalT,
    overflow_run σ i j a b left right]
   split <;> simp_all only [decide_eq_true_eq,if_true,if_false,
    and_self,minimum,Val.evalT,Simple.evalT,boolT,raw_run σ i j a b left right,bind,Except.bind]
   all_goals rfl
 · exact raw_run σ i j a b left right

theorem runtime {C : Contract} {Γ : Ctx} (σ : State C Γ) (checked : Bool)
 (i j : Idx Γ (.val .int)) (a b : PrimTy.int.Denote)
 (left : TEnv.get i σ.env=a) (right : TEnv.get j σ.env=b)
 {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {m : Machine}
 (input : StateRepr L offset frame F σ base m) (tail : List Word) :
 ValOutT .int
  (if checked then TRes.ofOpt (BinOp.div.evalT rfl a b)
   else if a.val=-((2^255:Nat):Int) ∧ b.val = -1 then .ok Backend.Scalar.minimumInt
   else TRes.ofOpt (BinOp.div.evalT rfl a b))
  (run (selected (C:=C) offset F checked i j).code {m with stack:=tail}) {m with stack:=tail} := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 have correct := (selected (C:=C) offset F checked i j).cert.correct (input.stack tail)
 rw [expression_run σ checked i j a b left right] at correct
 exact correct
end Solidity.Backend.PrimitivePackets.SignedDiv
