import Solidity.Lowering.V07.UnsignedWidthCasts
import Solidity.Lowering.V07.SignedWordSubtraction

/-! Actual signed integer casts at every approved source/destination width,
using the existing typed conditional, word truncation/subtraction and signed
readback. Caller locals retain their source type; no admission or production
compiler is supplied. -/
namespace Solidity.Lowering.V07.SignedWidthCasts

def ty (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) : Source.IntTy :=
  ⟨true,bits,valid⟩

theorem word_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi) :
    WordCasts.signed.lo ≤ x ∧ x ≤ WordCasts.signed.hi := by
  apply implicit_integer_range (ty bits valid) WordCasts.signed _ x hx
  change (decide (bits ≤ 256) || false) = true
  simp only [Bool.or_false,decide_eq_true_eq]
  exact valid.2.2

theorem allowed (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256)
    (E : Source.Env) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (Source.STy.int (ty fromBits fromValid)).explicit E.isBase E.mapFree (.int (ty bits valid)) = true := by
  simp only [Source.STy.explicit,ty,BEq.beq,decide_true,Bool.true_or,Bool.or_true]

theorem wrap_eq (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x : Int) :
    (ty bits valid).wrap x =
      if x % ((2^bits : Nat) : Int) < ((2^(bits-1) : Nat) : Int)
      then x % ((2^bits : Nat) : Int) else x % ((2^bits : Nat) : Int) - ((2^bits : Nat) : Int) := by
  have hc : ((2^(bits-1)-1 : Nat) : Int) = ((2^(bits-1) : Nat) : Int)-1 := by
    have hp := Source.two_pow_pos (bits-1)
    omega
  simp only [ty,Source.IntTy.wrap,Source.wrapBits,Source.bitsHi,true_and,if_true]
  rw [hc]
  split <;> split <;> omega

def castValue {C : Contract} {Γ : Ctx} (bits : Nat) (v : Val C Γ .int) : Val C Γ .int :=
  if h : bits < 256 then
    let low := UnsignedCasts.castValue bits (.unop .toUint rfl rfl v)
    .ternary (.binop .lt rfl rfl low (.simple (.lit ((2^(bits-1) : Nat) : Int)
      (UnsignedNarrowing.modulus_range (bits-1) (by omega)))))
      (.unop .toInt rfl rfl low)
      (.unop .toInt rfl rfl (.binop .subW rfl rfl low (.simple (.lit ((2^bits : Nat) : Int)
        (UnsignedNarrowing.modulus_range bits h)))))
  else v

theorem value_run (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256)
    {C : Contract} {Γ : Ctx} (target : State C Γ) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (v : Val C Γ .int)
    (x : Int) (hx : (ty fromBits fromValid).lo ≤ x ∧ x ≤ (ty fromBits fromValid).hi)
    (read : v.evalT target = .ok (integerValue (ty fromBits fromValid) x hx)) :
    (castValue bits v).evalT target =
      .ok (integerValue (ty bits valid) ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x)) := by
  have input := WordCasts.to_uint_run target v x (word_range fromBits fromValid x hx) read
  have low := UnsignedCasts.value_run target bits valid (.unop .toUint rfl rfl v)
    (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x) input
  let q := x % ((2^bits : Nat) : Int)
  have hq := (UnsignedNarrowing.ty bits valid).wrap_mem x
  rw [UnsignedNarrowing.wrap_eq] at hq
  have lowrun : (UnsignedCasts.castValue bits (.unop .toUint rfl rfl v)).evalT target =
      .ok (integerValue (UnsignedNarrowing.ty bits valid) q hq) := by
    have word : Source.IntTy.u256.wrap x % ((2^bits : Nat) : Int) = q :=
      UnsignedNarrowing.word_then_narrow bits valid.2.2 x
    simpa only [UnsignedNarrowing.wrap_eq,word] using low
  have hw := wrap_eq bits valid x
  change (ty bits valid).wrap x =
    (if q < ((2^(bits-1) : Nat) : Int) then q else q-((2^bits : Nat) : Int)) at hw
  have dst := word_range bits valid ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x)
  unfold castValue
  split
  · rename_i hbits
    have cond : (Val.binop .lt rfl rfl
        (UnsignedCasts.castValue bits (.unop .toUint rfl rfl v))
        (.simple (.lit ((2^(bits-1) : Nat) : Int)
          (UnsignedNarrowing.modulus_range (bits-1) (by omega))))).evalT target =
        .ok (decide (q < ((2^(bits-1) : Nat) : Int))) := by
      rw [Val.evalT,lowrun]
      rfl
    rw [Val.evalT,cond]
    simp only [Bind.bind,Except.bind]
    by_cases sign : q < ((2^(bits-1) : Nat) : Int)
    · simp only [sign,decide_true,boolT,if_true]
      have eq : (ty bits valid).wrap x = q := by simpa only [sign,if_true] using hw
      rw [eq] at dst
      have result := WordCasts.to_int_run target _ q
        (UnsignedWidthCasts.word_range bits valid q hq) lowrun
      simpa only [SignedWordSubtraction.wrap_of_range q dst,eq] using result
    · simp only [sign,decide_false,boolT]
      have eq : (ty bits valid).wrap x = q-((2^bits : Nat) : Int) := by
        simpa only [sign,if_false] using hw
      rw [eq] at dst
      have subrun : (Val.binop .subW rfl rfl
          (UnsignedCasts.castValue bits (.unop .toUint rfl rfl v))
          (.simple (.lit ((2^bits : Nat) : Int) (UnsignedNarrowing.modulus_range bits hbits)))).evalT target =
          .ok (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap (q-((2^bits : Nat) : Int)))
            (Source.IntTy.u256.wrap_mem (q-((2^bits : Nat) : Int)))) := by
        rw [Val.evalT,lowrun]
        change TRes.ofOpt (BinOp.evalT .subW rfl (integerValue (UnsignedNarrowing.ty bits valid) q hq)
          (⟨((2^bits : Nat) : Int),UnsignedNarrowing.modulus_range bits hbits⟩ : PrimTy.uint.Denote)) = _
        rw [UnsignedNarrowing.word_sub_eval]
        rfl
      have result := WordCasts.to_int_run target _ _ (Source.IntTy.u256.wrap_mem _) subrun
      simpa only [SignedWordSubtraction.wrap_word,
        SignedWordSubtraction.wrap_of_range (q-((2^bits : Nat) : Int)) dst,eq] using result
  · have hb : bits = 256 := by omega
    subst bits
    have hw := SignedWordSubtraction.wrap_of_range x (word_range fromBits fromValid x hx)
    change v.evalT target = .ok (integerValue WordCasts.signed
      (WordCasts.signed.wrap x) (WordCasts.signed.wrap_mem x))
    simpa only [hw] using read

theorem source_of_run (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256) {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source mid : Source.EMState E Γ)
    (e : Source.RExpr E Γ (.int (ty fromBits fromValid))) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x : Int) (hx : (ty fromBits fromValid).lo ≤ x ∧ x ≤ (ty fromBits fromValid).hi)
    (read : (Source.evalE G F fuel e).run source = (.ok (.val (.int x hx)),mid)) :
    (Source.evalE G F (fuel+1)
      (.convExplicit (τ := .int (ty bits valid)) e (allowed fromBits fromValid E bits valid))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) x)),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  rfl

theorem source_local_run (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256) {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (i : Source.Idx Γ (.int (ty fromBits fromValid))) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x : Int) (hx : (ty fromBits fromValid).lo ≤ x ∧ x ≤ (ty fromBits fromValid).hi)
    (read : source.1.get i = .int x hx) :
    (Source.evalE G F (fuel+2) (.convExplicit (τ := .int (ty bits valid))
      (.local i) (allowed fromBits fromValid E bits valid))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) x)),source) := by
  apply source_of_run fromBits fromValid G F (fuel+1) source source (.local i) bits valid x hx
  change (Except.ok (Source.RVal.val (source.1.get i)),source) = _
  rw [read]

def assignedOperand {C : Contract} {Γ : Ctx} (bits : Nat) (i a : Idx Γ (.val .int)) :
    DeferredSource.Operand C Γ (.prim .int) :=
  ⟨_,(assignLocalOperand i a).code,.val (castValue bits (.simple (.local .here)))⟩

theorem assigned_run (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256) {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (i a : Idx Γ (.val .int)) (x : Int)
    (hx : (ty fromBits fromValid).lo ≤ x ∧ x ≤ (ty fromBits fromValid).hi)
    (read : TEnv.get a target.env = integerValue (ty fromBits fromValid) x hx) :
    (assignedOperand bits i a).run target =
      .ok (⟨target.setLocal i (integerValue (ty fromBits fromValid) x hx),List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x))) := by
  unfold assignedOperand DeferredSource.Operand.run assignLocalOperand
  change (do
    let x' ← (Except.ok (TEnv.get a target.env) : TRes PrimTy.int.Denote)
    let y ← (Except.ok (TEnv.get i (TEnv.set i x' target.env)) : TRes PrimTy.int.Denote)
    let z ← (Src.val (castValue bits (.simple (.local .here))) :
      Src C (.val .int :: Γ) (.prim .int)).valueT ((target.setLocal i x').push y)
    pure ((⟨target.setLocal i x',List.prefix_refl _⟩ : Out C target.H Γ),z)) = _
  rw [read]
  simp only [Bind.bind,Except.bind,TEnv.get_set]
  rw [Src.valueT,value_run fromBits fromValid
    ((target.setLocal i (integerValue (ty fromBits fromValid) x hx)).push
      (integerValue (ty fromBits fromValid) x hx)) bits valid (.simple (.local .here)) x hx rfl]
  rfl

/-- Initial-family transport for an actual effectful cast. The scalar family
continues at its original type; only the returned captured value changes width. -/
theorem assignment_transport (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256) {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} {ι : Type}
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int (ty fromBits fromValid))) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily (ty fromBits fromValid) si ti source.1 target.env)
    (i a : ι) (x : Int) (hx : (ty fromBits fromValid).lo ≤ x ∧ x ≤ (ty fromBits fromValid).hi)
    (readA : source.1.get (si a) = .int x hx) :
    (Source.evalE G F (fuel+3)
      (.convExplicit (τ := .int (ty bits valid))
        (.assign (.local (si i)) (.local (si a))) (allowed fromBits fromValid E bits valid))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) x)),(source.1.set (si i) (.int x hx),source.2)) ∧
    (assignedOperand bits (ti i) (ti a)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue (ty fromBits fromValid) x hx),List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x))) ∧
    IntValueRel (ty bits valid) (Source.intWrap (ty bits valid) x : Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x)) ∧
    IntegerLocalFamily (ty fromBits fromValid) si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue (ty fromBits fromValid) x hx) target.env) := by
  refine ⟨source_of_run fromBits fromValid G F (fuel+2) source _ _ bits valid x hx
    (source_assign_local_run G F fuel source (si i) (si a) _ readA),
    assigned_run fromBits fromValid target bits valid (ti i) (ti a) x hx (family.read a x hx readA),
    integer_related _ _ _,?_⟩
  have post := family.write i a
  rw [readA,family.read a x hx readA] at post
  exact post

theorem assignment_extension (fromBits : Nat) (fromValid : fromBits % 8 = 0 ∧ 8 ≤ fromBits ∧ fromBits ≤ 256) {C : Contract} {Γ Δ : Ctx}
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (target : State C Γ) (i a : Idx Γ (.val .int))
    (x : Int) (hx : (ty fromBits fromValid).lo ≤ x ∧ x ≤ (ty fromBits fromValid).hi)
    (read : TEnv.get a target.env = integerValue (ty fromBits fromValid) x hx)
    (thin : Thin Γ Δ) (extra : TEnv C target.H Δ) :
    ((assignedOperand bits i a).wk thin).run (target.lift thin extra) =
      liftedT₂ thin extra (.ok ((⟨target.setLocal i (integerValue (ty fromBits fromValid) x hx),List.prefix_refl _⟩ : Out C target.H Γ),
        SVal.prim (integerValue (ty bits valid) ((ty bits valid).wrap x) ((ty bits valid).wrap_mem x)))) := by
  rw [DeferredSource.Operand.run_wk,assigned_run fromBits fromValid target bits valid i a x hx read]
  rfl

end Solidity.Lowering.V07.SignedWidthCasts
