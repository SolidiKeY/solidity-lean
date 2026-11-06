import Solidity.Backend.PrimitivePackets.SignedDiv.Selected

/-! Same typed local operands connect independent actual Source execution and
publicly selected intrinsic execution. Source Panic(0x11)/Panic(0x12) remain
exact; native failure is the published coarse revert, not payload emission. -/
namespace Solidity.Backend.PrimitivePackets.SignedDiv
open Evm Evm.Memory Solidity.Backend.Passes

theorem intrinsic_ordinary (a b : PrimTy.int.Denote) (nonzero : b.val≠0)
 (ordinary : ¬ (a.val=-((2^255:Nat):Int) ∧ b.val = -1)) :
 BinOp.div.evalT rfl a b=some (quotient a b nonzero ordinary) := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 have hr := Solidity.Lowering.V07.integer_range T _ (quotient_range a b nonzero ordinary)
 change PrimTy.int.inRange (a.val.tdiv b.val)=true at hr
 simp only [BinOp.evalT,BinOp.evalNum,BinOp.arithInt,nonzero,if_false,Option.bind_some,
  PrimTy.ofInt?,dif_pos hr]
 rfl

theorem intrinsic_zero {C : Contract} {Γ : Ctx} (σ : State C Γ) (checked : Bool)
 (i j : Idx Γ (.val .int)) (a b : PrimTy.int.Denote)
 (left : TEnv.get i σ.env=a) (right : TEnv.get j σ.env=b) (zero : b.val=0) :
 (expression checked i j).evalT σ=.error .revert := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 rw [expression_run σ checked i j a b left right]
 cases checked <;> simp only [Bool.false_eq_true,if_false,if_true,
  BinOp.evalT,BinOp.evalNum,BinOp.arithInt,zero,if_true,Option.bind_none,TRes.ofOpt,
  show ¬ ((0:Int) = -1) from by decide,and_false]

theorem intrinsic_overflow {C : Contract} {Γ : Ctx} (σ : State C Γ)
 (i j : Idx Γ (.val .int)) (a b : PrimTy.int.Denote)
 (left : TEnv.get i σ.env=a) (right : TEnv.get j σ.env=b)
 (minimum : a.val=-((2^255:Nat):Int)) (minusOne : b.val = -1) :
 (expression true i j).evalT σ=.error .revert ∧
 (expression false i j).evalT σ=.ok Backend.Scalar.minimumInt := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 simp only [expression_run σ true i j a b left right,expression_run σ false i j a b left right,
  if_true,Bool.false_eq_true,if_false,minimum,minusOne,and_self,
  Backend.Scalar.int_div_exception a b minimum minusOne,TRes.ofOpt]

theorem ordinary_execution {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
 (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ)
 (target : State C Γ) (si sj : Source.Idx srcΓ (.int T)) (i j : Idx Γ (.val .int))
 (a b : PrimTy.int.Denote) (sl : source.1.get si=sourceValue a) (sr : source.1.get sj=sourceValue b)
 (tl : TEnv.get i target.env=a) (tr : TEnv.get j target.env=b)
 (nonzero : b.val≠0) (ordinary : ¬ (a.val=-((2^255:Nat):Int) ∧ b.val = -1))
 {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {m : Machine}
 (input : StateRepr L offset frame F target base m) (tail : List Word) :
 (Source.evalE G SF (fuel+3) (.binary .div (.local si) (.local sj))).run source=
 (.ok (.val (sourceValue (quotient a b nonzero ordinary))),source) ∧
 ∃ word, ReprV .int (quotient a b nonzero ordinary) word ∧
 run (selected (C:=C) offset F SF.checked i j).code {m with stack:=tail}=
 .ok ({m with stack:=tail}.push word) 0 := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 refine ⟨?_,?_⟩
 · rw [locals_origin G SF fuel source si sj a b sl sr,source_ordinary SF.checked a b nonzero ordinary]
   rfl
 · apply value_success_tail _ input
   rw [expression_run target SF.checked i j a b tl tr,intrinsic_ordinary a b nonzero ordinary]
   cases SF.checked <;> simp only [Bool.false_eq_true,if_false,if_true,ordinary,TRes.ofOpt]

theorem zero_execution {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
 (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ)
 (target : State C Γ) (si sj : Source.Idx srcΓ (.int T)) (i j : Idx Γ (.val .int))
 (a b : PrimTy.int.Denote) (sl : source.1.get si=sourceValue a) (sr : source.1.get sj=sourceValue b)
 (tl : TEnv.get i target.env=a) (tr : TEnv.get j target.env=b) (zero : b.val=0)
 {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {m : Machine}
 (input : StateRepr L offset frame F target base m) (tail : List Word) :
 (Source.evalE G SF (fuel+3) (.binary .div (.local si) (.local sj))).run source=
 (.error (.revert (Source.panicData .divZero)),source) ∧
 run (selected (C:=C) offset F SF.checked i j).code {m with stack:=tail}=.revert := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 refine ⟨?_,?_⟩
 · rw [locals_origin G SF fuel source si sj a b sl sr,source_zero SF.checked a b zero]
   rfl
 · exact (value_revert_iff _ input tail).mpr (intrinsic_zero target SF.checked i j a b tl tr zero)

theorem overflow_execution {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
 (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ)
 (target : State C Γ) (si sj : Source.Idx srcΓ (.int T)) (i j : Idx Γ (.val .int))
 (a b : PrimTy.int.Denote) (sl : source.1.get si=sourceValue a) (sr : source.1.get sj=sourceValue b)
 (tl : TEnv.get i target.env=a) (tr : TEnv.get j target.env=b)
 (minimum : a.val=-((2^255:Nat):Int)) (minusOne : b.val = -1)
 {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {m : Machine}
 (input : StateRepr L offset frame F target base m) (tail : List Word) :
 (Source.evalE G {SF with checked:=true} (fuel+3) (.binary .div (.local si) (.local sj))).run source=
 (.error (.revert (Source.panicData .arithmetic)),source) ∧
 run (selected (C:=C) offset F true i j).code {m with stack:=tail}=.revert ∧
 (Source.evalE G {SF with checked:=false} (fuel+3) (.binary .div (.local si) (.local sj))).run source=
 (.ok (.val (sourceValue Backend.Scalar.minimumInt)),source) ∧
 ∃ word, ReprV .int Backend.Scalar.minimumInt word ∧
 run (selected (C:=C) offset F false i j).code {m with stack:=tail}=.ok ({m with stack:=tail}.push word) 0 := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 have native := intrinsic_overflow target i j a b tl tr minimum minusOne
 refine ⟨?_,(value_revert_iff _ input tail).mpr native.1,?_,value_success_tail _ input native.2 tail⟩
 · rw [locals_origin G {SF with checked:=true} fuel source si sj a b sl sr,source_overflow a b minimum minusOne]
   rfl
 · rw [locals_origin G {SF with checked:=false} fuel source si sj a b sl sr,source_unchecked_overflow a b minimum minusOne]
   rfl
end Solidity.Backend.PrimitivePackets.SignedDiv
