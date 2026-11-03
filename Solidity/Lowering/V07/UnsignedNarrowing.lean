import Solidity.Lowering.V07.DoubleAssignment
import Solidity.Lowering.V07.SourceReads

/-! G16 unchecked unsigned subtraction over existing typed Source/Val carriers.
This uses published intrinsic word operators, not Backend.Scalar opcode code. -/
namespace Solidity.Lowering.V07.UnsignedNarrowing

/-- An existing Source integer type; no new width or value representation. -/
def ty (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) : Source.IntTy :=
  ⟨false,bits,valid⟩

theorem wrap_eq (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (n : Int) :
    (ty bits valid).wrap n = n % ((2 ^ bits : Nat) : Int) := by
  simp only [ty,Source.IntTy.wrap,Source.wrapBits,Bool.false_eq_true,false_and,if_false]

theorem word_then_narrow (bits : Nat) (bound : bits ≤ 256) (n : Int) :
    (n % Semantics.uintBound) % ((2 ^ bits : Nat) : Int) = n % ((2 ^ bits : Nat) : Int) := by
  obtain ⟨k,hk⟩ := Nat.pow_dvd_pow 2 bound
  apply Int.emod_emod_of_dvd
  refine ⟨(k : Int),?_⟩
  change ((2 ^ 256 : Nat) : Int) = ((2 ^ bits : Nat) : Int) * (k : Int)
  rw [hk,Int.natCast_mul]

theorem modulus_range (bits : Nat) (narrow : bits < 256) :
    PrimTy.uint.inRange ((2 ^ bits : Nat) : Int) = true := by
  have h := Nat.pow_lt_pow_right (by decide : 1 < 2) narrow
  exact PrimTy.inRange_uint_of_lt h

theorem wrap_of_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (n : Int) (h : (ty bits valid).lo ≤ n ∧ n ≤ (ty bits valid).hi) :
    (ty bits valid).wrap n = n := by
  rw [wrap_eq]
  have hp := Source.two_pow_pos bits
  simp only [ty,Source.IntTy.lo,Source.IntTy.hi,Bool.false_eq_true,if_false] at h
  apply Int.emod_eq_of_lt h.1
  omega

def subValue {C : Contract} {Γ : Ctx} (bits : Nat)
    (a b : Val C Γ .uint) : Val C Γ .uint :=
  let raw := Val.binop .subW rfl rfl a b
  if h : bits < 256 then
    .binop .mod rfl rfl raw (.simple (.lit ((2 ^ bits : Nat) : Int) (modulus_range bits h)))
  else raw

theorem source_sub_unchecked {D : Source.Layout} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) :
    Source.binVal false .sub (.int x hx : Source.Val D (.int (ty bits valid))) (.int y hy) =
      .ok (Source.intWrap (ty bits valid) (x-y)) := by
  simp only [Source.binVal,Source.intBin,Source.intRes]
  split
  · rename_i h
    have hw := wrap_of_range bits valid (x-y) h
    simp only [Source.intWrap,hw]
    rfl
  · rfl

theorem word_sub_eval (x y : PrimTy.uint.Denote) :
    BinOp.evalT .subW rfl x y =
      some (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap (x.val-y.val))
        (Source.IntTy.u256.wrap_mem (x.val-y.val))) := by
  have hr := integer_range Source.IntTy.u256 (Source.IntTy.u256.wrap (x.val-y.val))
    (Source.IntTy.u256.wrap_mem (x.val-y.val))
  change PrimTy.uint.inRange ((x.val-y.val) % Semantics.uintBound) = true at hr
  change (BinOp.arithInt .subW x.val y.val).bind PrimTy.uint.ofInt? =
    some ⟨(x.val-y.val) % Semantics.uintBound,hr⟩
  simp only [BinOp.arithInt,Option.bind_some,PrimTy.ofInt?,dif_pos hr]

theorem mod_word_eval (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (narrow : bits < 256) (n : Int) :
    BinOp.evalT .mod rfl
      (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap n) (Source.IntTy.u256.wrap_mem n))
      (⟨((2 ^ bits : Nat) : Int),modulus_range bits narrow⟩ : PrimTy.uint.Denote) =
      some (integerValue (ty bits valid) ((ty bits valid).wrap n) ((ty bits valid).wrap_mem n)) := by
  have hr := integer_range (ty bits valid) ((ty bits valid).wrap n) ((ty bits valid).wrap_mem n)
  change PrimTy.uint.inRange (n % ((2 ^ bits : Nat) : Int)) = true at hr
  have hnonneg : 0 ≤ n % Semantics.uintBound := Int.emod_nonneg n (by unfold Semantics.uintBound; decide)
  have hpos : (0 : Int) < ((2 ^ bits : Nat) : Int) := Int.ofNat_lt.mpr (Source.two_pow_pos bits)
  change (BinOp.arithInt .mod (n % Semantics.uintBound) ((2 ^ bits : Nat) : Int)).bind
    PrimTy.uint.ofInt? = some ⟨n % ((2 ^ bits : Nat) : Int),hr⟩
  simp only [BinOp.arithInt,if_neg (Int.ne_of_gt hpos),Int.tmod_eq_emod_of_nonneg hnonneg,
    word_then_narrow bits valid.2.2,Option.bind_some,PrimTy.ofInt?,dif_pos hr]

theorem sub_value_run {C : Contract} {Γ : Ctx} (target : State C Γ) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (a b : Val C Γ .uint)
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (left : a.evalT target = .ok (integerValue (ty bits valid) x hx))
    (right : b.evalT target = .ok (integerValue (ty bits valid) y hy)) :
    (subValue bits a b).evalT target =
      .ok (integerValue (ty bits valid) ((ty bits valid).wrap (x-y)) ((ty bits valid).wrap_mem (x-y))) := by
  have raw : (Val.binop .subW rfl rfl a b).evalT target =
      .ok (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap (x-y))
        (Source.IntTy.u256.wrap_mem (x-y))) := by
    rw [Val.evalT,left]
    change (do
      let y' ← b.evalT target
      TRes.ofOpt (BinOp.evalT .subW rfl (integerValue (ty bits valid) x hx) y')) = _
    rw [right]
    change TRes.ofOpt (BinOp.evalT .subW rfl
      (integerValue (ty bits valid) x hx) (integerValue (ty bits valid) y hy)) = _
    rw [word_sub_eval]
    rfl
  unfold subValue
  split
  · rename_i hbits
    rw [Val.evalT,raw]
    change TRes.ofOpt (BinOp.evalT .mod rfl
      (integerValue Source.IntTy.u256 (Source.IntTy.u256.wrap (x-y)) (Source.IntTy.u256.wrap_mem (x-y)))
      (⟨((2 ^ bits : Nat) : Int),modulus_range bits hbits⟩ : PrimTy.uint.Denote)) = _
    rw [mod_word_eval bits valid hbits (x-y)]
    rfl
  · rename_i hbits
    have hb : bits = 256 := by omega
    subst bits
    exact raw

/-- Composition helper; concrete clauses below discharge the pair with actual
Source operations. The unchecked frame is explicit, not a changed default. -/
theorem source_from_pair {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source mid : Source.EMState E Γ) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (a b : Source.RExpr E Γ (.int (ty bits valid))) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (pair : (Source.evalPair G {F with checked := false} fuel a b).run source =
      (.ok (.val (.int x hx),.val (.int y hy)),mid)) :
    (Source.evalE G {F with checked := false} (fuel+1) (.binary .sub a b)).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (x-y))),mid) := by
  rw [Source.evalE]
  simp only [reduceCtorEq,decide_false,Bool.false_or,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,pair]
  change (do
    let v ← Source.EM.lift (Source.binVal false .sub
      (.int x hx : Source.Val E.layout (.int (ty bits valid))) (.int y hy))
    pure (Source.RVal.val v)).run mid = _
  rw [source_sub_unchecked]
  rfl

theorem source_locals_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (a b : Source.Idx Γ (.int (ty bits valid))) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get a = .int x hx) (readB : source.1.get b = .int y hy) :
    (Source.evalE G {F with checked := false} (fuel+3)
      (.binary .sub (.local a) (.local b))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (x-y))),source) :=
  source_from_pair G F (fuel+2) source source bits valid _ _ x y hx hy
    (source_local_pair G {F with checked := false} fuel source (ty bits valid) a b x y hx hy readA readB)

theorem locals_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (a b : ι) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy) :
    (Source.evalE G {F with checked := false} (fuel+3)
      (.binary .sub (.local (si a)) (.local (si b)))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (x-y))),source) ∧
    (subValue bits (.simple (.local (ti a))) (.simple (.local (ti b)))).evalT target =
      .ok (integerValue (ty bits valid) ((ty bits valid).wrap (x-y)) ((ty bits valid).wrap_mem (x-y))) ∧
    IntValueRel (ty bits valid) (Source.intWrap (ty bits valid) (x-y) : Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) ((ty bits valid).wrap (x-y)) ((ty bits valid).wrap_mem (x-y))) := by
  refine ⟨source_locals_run G F fuel source bits valid (si a) (si b) x y hx hy readA readB,
    sub_value_run target bits valid _ _ x y hx hy ?_ ?_,integer_related _ _ _⟩
  · change Except.ok (TEnv.get (ti a) target.env) = _
    rw [family.read a x hx readA]
  · change Except.ok (TEnv.get (ti b) target.env) = _
    rw [family.read b y hy readB]

/-- Actual effectful assignment/read expression; result bounds come from
Source wrapping, never a desired-result range premise. -/
theorem source_assign_read_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (i a : Source.Idx Γ (.int (ty bits valid))) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get a = .int x hx) (readI : source.1.get i = .int y hy) :
    (Source.evalE G {F with checked := false} (fuel+4)
      (.binary .sub (.assign (.local i) (.local a)) (.local i))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (x-(if G.pipeline = .legacy then y else x)))),
        (source.1.set i (.int x hx),source.2)) := by
  have pair := source_assign_read_pair G {F with checked := false} fuel source i a
    (.int x hx) (.int y hy) readA readI
  by_cases order : G.pipeline = .legacy
  · simp only [order,if_true] at pair ⊢
    exact source_from_pair G F (fuel+3) source _ bits valid _ _ x y hx hy pair
  · simp only [order,if_false] at pair ⊢
    exact source_from_pair G F (fuel+3) source _ bits valid _ _ x x hx hx pair

def assignReadOperand {C : Contract} {Γ : Ctx} (pipeline : Roadmap.Pipeline)
    (bits : Nat) (i a : Idx Γ (.val .uint)) : DeferredSource.Operand C Γ (.prim .uint) :=
  ⟨.val .uint :: .val .uint :: Γ,assignReadPrefix pipeline i a,
    match pipeline with
    | .legacy => .val (subValue bits (.simple (.local .here)) (.simple (.local (.there .here))))
    | .viaIR => .val (subValue bits (.simple (.local (.there .here))) (.simple (.local .here)))⟩

theorem assign_read_operand_run {C : Contract} {Γ : Ctx} (pipeline : Roadmap.Pipeline)
    (target : State C Γ) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (i a : Idx Γ (.val .uint)) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : TEnv.get a target.env = integerValue (ty bits valid) x hx)
    (readI : TEnv.get i target.env = integerValue (ty bits valid) y hy) :
    (assignReadOperand pipeline bits i a).run target =
      .ok (⟨target.setLocal i (integerValue (ty bits valid) x hx),List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap (x-(if pipeline = .legacy then y else x)))
          ((ty bits valid).wrap_mem (x-(if pipeline = .legacy then y else x))))) := by
  cases pipeline
  · let reached : State C (.val .uint :: .val .uint :: Γ) :=
      ((target.setLocal i (integerValue (ty bits valid) x hx)).push (integerValue (ty bits valid) y hy)).push
        (integerValue (ty bits valid) x hx)
    have value := sub_value_run reached bits valid (.simple (.local .here))
      (.simple (.local (.there .here))) x y hx hy rfl rfl
    unfold assignReadOperand DeferredSource.Operand.run
    rw [assign_read_prefix_run .legacy target i a _ _ readA readI]
    change (do
      let v ← (Src.val (subValue bits (.simple (.local .here)) (.simple (.local (.there .here)))) :
        Src C (.val .uint :: .val .uint :: Γ) (.prim .uint)).valueT reached
      pure ((⟨target.setLocal i (integerValue (ty bits valid) x hx),List.prefix_refl _⟩ : Out C target.H Γ),v)) = _
    simp only [Src.valueT,value]
    rfl
  · let reached : State C (.val .uint :: .val .uint :: Γ) :=
      ((target.setLocal i (integerValue (ty bits valid) x hx)).push (integerValue (ty bits valid) x hx)).push
        (integerValue (ty bits valid) x hx)
    have value := sub_value_run reached bits valid (.simple (.local (.there .here)))
      (.simple (.local .here)) x x hx hx rfl rfl
    unfold assignReadOperand DeferredSource.Operand.run
    rw [assign_read_prefix_run .viaIR target i a _ _ readA readI]
    change (do
      let v ← (Src.val (subValue bits (.simple (.local (.there .here))) (.simple (.local .here))) :
        Src C (.val .uint :: .val .uint :: Γ) (.prim .uint)).valueT reached
      pure ((⟨target.setLocal i (integerValue (ty bits valid) x hx),List.prefix_refl _⟩ : Out C target.H Γ),v)) = _
    simp only [Src.valueT,value]
    rfl

/-- Initial alignment supplies target reads and every selected postbinding.
No output-range or desired-run relation is a premise. -/
theorem assignment_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (i a : ι) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get (si a) = .int x hx) (readI : source.1.get (si i) = .int y hy) :
    (Source.evalE G {F with checked := false} (fuel+4)
      (.binary .sub (.assign (.local (si i)) (.local (si a))) (.local (si i)))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (x-(if G.pipeline = .legacy then y else x)))),
        (source.1.set (si i) (.int x hx),source.2)) ∧
    (assignReadOperand G.pipeline bits (ti i) (ti a)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue (ty bits valid) x hx),List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap (x-(if G.pipeline = .legacy then y else x)))
          ((ty bits valid).wrap_mem (x-(if G.pipeline = .legacy then y else x))))) ∧
    IntValueRel (ty bits valid)
      (Source.intWrap (ty bits valid) (x-(if G.pipeline = .legacy then y else x)) :
        Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) ((ty bits valid).wrap (x-(if G.pipeline = .legacy then y else x)))
        ((ty bits valid).wrap_mem (x-(if G.pipeline = .legacy then y else x)))) ∧
    IntegerLocalFamily (ty bits valid) si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue (ty bits valid) x hx) target.env) := by
  refine ⟨source_assign_read_run G F fuel source bits valid (si i) (si a) x y hx hy readA readI,
    assign_read_operand_run G.pipeline target bits valid (ti i) (ti a) x y hx hy
      (family.read a x hx readA) (family.read i y hy readI),integer_related _ _ _,?_⟩
  have post := family.write i a
  rw [readA,family.read a x hx readA] at post
  exact post

theorem assignment_extension {C : Contract} {Γ Δ : Ctx}
    (pipeline : Roadmap.Pipeline) (target : State C Γ) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (i a : Idx Γ (.val .uint))
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : TEnv.get a target.env = integerValue (ty bits valid) x hx)
    (readI : TEnv.get i target.env = integerValue (ty bits valid) y hy)
    (thin : Thin Γ Δ) (extra : TEnv C target.H Δ) :
    ((assignReadOperand pipeline bits i a).wk thin).run (target.lift thin extra) =
      liftedT₂ thin extra (.ok ((⟨target.setLocal i (integerValue (ty bits valid) x hx),List.prefix_refl _⟩ : Out C target.H Γ),
        SVal.prim (integerValue (ty bits valid) ((ty bits valid).wrap (x-(if pipeline = .legacy then y else x)))
          ((ty bits valid).wrap_mem (x-(if pipeline = .legacy then y else x)))))) := by
  rw [DeferredSource.Operand.run_wk,assign_read_operand_run pipeline target bits valid i a x y hx hy readA readI]
  rfl

end Solidity.Lowering.V07.UnsignedNarrowing
