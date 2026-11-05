import Solidity.Lowering.V07.UnsignedNarrowing

/-! Unsigned explicit casts of actual Source locals. The operand is read from
arbitrary initial state; neither an execution nor a desired result is assumed. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedCast
open Solidity.Lowering.V07
open Solidity.Lowering.V07.UnsignedNarrowing

abbrev Legal (bits : Nat) := bits % 8 = 0 ∧ 8 ≤ bits ∧ bits < 256

def targetTy (bits : Nat) (legal : Legal bits) : Source.IntTy :=
  ty bits ⟨legal.1, legal.2.1, Nat.le_of_lt legal.2.2⟩

def expression {E : Source.Env} {Γ : Source.RCtx} (bits : Nat) (legal : Legal bits)
    (i : Source.Idx Γ (.int Source.IntTy.u256)) : Source.RExpr E Γ (.int (targetTy bits legal)) :=
  .convExplicit (.local i) (by
    change (_ || (true || _)) = true
    simp only [Bool.true_or, Bool.or_true])

theorem source_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (bits : Nat) (legal : Legal bits) (i : Source.Idx Γ (.int Source.IntTy.u256))
    (n : Int) (range : Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi)
    (read : source.1.get i = .int n range) :
    (Source.evalE G F (fuel+2) (expression bits legal i)).run source =
      (.ok (.val (Source.intWrap (targetTy bits legal) n)), source) := by
  unfold expression
  rw [Source.evalE, Source.Hoare.run_bind]
  have localRun : (Source.evalE G F (fuel+1) (.local i)).run source =
      (.ok (.val (.int n range)),source) := by
    change (Except.ok (Source.RVal.val (source.1.get i)),source) = _
    rw [read]
  rw [localRun]
  rfl

/-- Every intrinsically typed uint256 local supplies the numeric witness;
no integer/read premise is needed to obtain a completing Source cast. -/
theorem source_total {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (bits : Nat) (legal : Legal bits) (i : Source.Idx Γ (.int Source.IntTy.u256)) :
    ∃ n range, source.1.get i = .int n range ∧
      (Source.evalE G F (fuel+2) (expression bits legal i)).run source =
        (.ok (.val (Source.intWrap (targetTy bits legal) n)),source) := by
  cases read : source.1.get i with
  | int n range => exact ⟨n,range,rfl,source_run G F fuel source bits legal i n range read⟩
  | memRef invalid _ => cases invalid
  | storRef invalid _ => cases invalid
  | cdRef invalid _ _ => cases invalid

theorem wrapped (bits : Nat) (legal : Legal bits) (n : Int) :
    (targetTy bits legal).wrap n = n % ((2 ^ bits : Nat) : Int) :=
  wrap_eq bits _ n

/-- The existing intrinsic operator, not a new intermediate language. -/
def value {C : Contract} {Γ : Ctx} (bits : Nat) (legal : Legal bits)
    (j : Idx Γ (.val .uint)) : Val C Γ .uint :=
  .binop .mod rfl rfl (.simple (.local j))
    (.simple (.lit ((2 ^ bits : Nat) : Int) (modulus_range bits legal.2.2)))

theorem value_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (legal : Legal bits) (j : Idx Γ (.val .uint))
    (n : Int) (range : Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi)
    (read : TEnv.get j target.env = integerValue Source.IntTy.u256 n range) :
    (value bits legal j).evalT target =
      .ok (integerValue (targetTy bits legal) ((targetTy bits legal).wrap n)
        ((targetTy bits legal).wrap_mem n)) := by
  have same : Source.IntTy.u256.wrap n = n := wrap_of_range 256 (by decide) n range
  unfold value
  rw [Val.evalT]
  change TRes.ofOpt (BinOp.evalT .mod rfl (TEnv.get j target.env)
    (⟨((2 ^ bits : Nat) : Int),modulus_range bits legal.2.2⟩ : PrimTy.uint.Denote)) = _
  rw [read]
  have operation := mod_word_eval bits ⟨legal.1,legal.2.1,Nat.le_of_lt legal.2.2⟩ legal.2.2 n
  have input_eq : integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap n)
      (Source.IntTy.u256.wrap_mem n) = integerValue Source.IntTy.u256 n range :=
    Subtype.ext same
  rw [input_eq] at operation
  rw [operation]
  rfl

end Solidity.Backend.PrimitivePackets.UnsignedCast
