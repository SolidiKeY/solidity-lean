import Solidity.Source.PowerV2Correct
import Solidity.Lowering.V07.IntegerConstants
import Solidity.Lowering.G16.PanicGuard
import Solidity.Syntax.CheckedExact
import Solidity.Lowering.V07.UnsignedAddition
import Solidity.Lowering.V07.UnsignedMultiplication
import Solidity.Lowering.V07.SignedNarrowAddition
import Solidity.Lowering.V07.SignedNarrowSubtraction
import Solidity.Lowering.V07.SignedNarrowMultiplication

/-! V07 ring programs and signed quotient/remainder guards. Whole-family composition remains separate; no frontend selection or admission claim. -/
namespace Solidity.Lowering.G16.Arithmetic
open Solidity.Lowering.V07

inductive RingOp where
  | add | sub | mul
  deriving DecidableEq, Repr

def RingOp.source : RingOp → Source.BinOp
  | .add => .add | .sub => .sub | .mul => .mul

def RingOp.calculate : RingOp → Int → Int → Int
  | .add => (· + ·) | .sub => (· - ·) | .mul => (· * ·)

/-- Reuse V07 word arithmetic and width restoration. -/
def wrappingValue {C : Contract} {Γ : Ctx} (t : Source.IntTy) (op : RingOp) :
    Val C Γ (integerPrim t) → Val C Γ (integerPrim t) → Val C Γ (integerPrim t) :=
  match t with
  | ⟨false,bits,_⟩ => match op with
    | .add => UnsignedAddition.addValue bits
    | .sub => UnsignedNarrowing.subValue bits
    | .mul => UnsignedMultiplication.mulValue bits
  | ⟨true,bits,_⟩ => match op with
    | .add => SignedNarrowAddition.addValue bits
    | .sub => SignedNarrowSubtraction.subValue bits
    | .mul => SignedNarrowMultiplication.mulValue bits

/-- All three ring operations, widths and signs in an explicit unchecked Source frame. Premises observe initial locals, never desired runs. -/
theorem wrapping_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (t : Source.IntTy) (op : RingOp)
    (si : ι → Source.Idx srcΓ (.int t)) (ti : ι → Idx Γ (.val (integerPrim t)))
    (family : IntegerLocalFamily t si ti source.1 target.env)
    (a b : ι) (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy) :
    (Source.evalE G {F with checked := false} (fuel+3)
      (.binary op.source (.local (si a)) (.local (si b)))).run source =
      (.ok (.val (Source.intWrap t (op.calculate x y))),source) ∧
    (wrappingValue t op (.simple (.local (ti a))) (.simple (.local (ti b)))).evalT target =
      .ok (integerValue t (t.wrap (op.calculate x y)) (t.wrap_mem (op.calculate x y))) ∧
    IntValueRel t (Source.intWrap t (op.calculate x y) : Source.Val E.layout (.int t))
      (integerValue t (t.wrap (op.calculate x y)) (t.wrap_mem (op.calculate x y))) := by
  obtain ⟨sign,bits,valid⟩ := t
  cases sign with
  | false =>
    cases op with
    | add => exact UnsignedAddition.locals_transport G F fuel source target bits valid si ti family a b x y hx hy readA readB
    | sub => exact UnsignedNarrowing.locals_transport G F fuel source target bits valid si ti family a b x y hx hy readA readB
    | mul => exact UnsignedMultiplication.locals_transport G F fuel source target bits valid si ti family a b x y hx hy readA readB
  | true =>
    cases op with
    | add => exact SignedNarrowAddition.locals_transport bits valid G F fuel source target si ti family a b x y hx hy readA readB
    | sub => exact SignedNarrowSubtraction.locals_transport bits valid G F fuel source target si ti family a b x y hx hy readA readB
    | mul => exact SignedNarrowMultiplication.locals_transport bits valid G F fuel source target si ti family a b x y hx hy readA readB


/-- Reuse V07's assignment/read operand, capture prefix and pipeline order. -/
def wrappingAssignmentOperand {C : Contract} {Γ : Ctx} (t : Source.IntTy)
    (op : RingOp) (pipeline : Roadmap.Pipeline) :
    Idx Γ (.val (integerPrim t)) → Idx Γ (.val (integerPrim t)) →
      DeferredSource.Operand C Γ (.prim (integerPrim t)) :=
  match t with
  | ⟨false,bits,_⟩ => match op with
    | .add => UnsignedAddition.assignReadOperand pipeline bits
    | .sub => UnsignedNarrowing.assignReadOperand pipeline bits
    | .mul => UnsignedMultiplication.assignReadOperand pipeline bits
  | ⟨true,bits,_⟩ => match op with
    | .add => SignedNarrowAddition.assignReadOperand bits pipeline
    | .sub => SignedNarrowSubtraction.assignReadOperand bits pipeline
    | .mul => SignedNarrowMultiplication.assignReadOperand bits pipeline

/-- Pipeline-sensitive assignment/read at all widths/signs, with derived caller update. Only initial alignment/reads are assumed; no frontend selection or held validator association. -/
theorem wrapping_assignment_transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (t : Source.IntTy) (op : RingOp)
    (si : ι → Source.Idx srcΓ (.int t)) (ti : ι → Idx Γ (.val (integerPrim t)))
    (family : IntegerLocalFamily t si ti source.1 target.env)
    (i a : ι) (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : source.1.get (si a) = .int x hx) (readI : source.1.get (si i) = .int y hy) :
    (Source.evalE G {F with checked := false} (fuel+4)
      (.binary op.source (.assign (.local (si i)) (.local (si a))) (.local (si i)))).run source =
      (.ok (.val (Source.intWrap t (op.calculate x (if G.pipeline = .legacy then y else x)))),
        (source.1.set (si i) (.int x hx),source.2)) ∧
    (wrappingAssignmentOperand t op G.pipeline (ti i) (ti a)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue t x hx),List.prefix_refl _⟩,
        .prim (integerValue t (t.wrap (op.calculate x (if G.pipeline = .legacy then y else x)))
          (t.wrap_mem (op.calculate x (if G.pipeline = .legacy then y else x))))) ∧
    IntValueRel t
      (Source.intWrap t (op.calculate x (if G.pipeline = .legacy then y else x)) : Source.Val E.layout (.int t))
      (integerValue t (t.wrap (op.calculate x (if G.pipeline = .legacy then y else x)))
        (t.wrap_mem (op.calculate x (if G.pipeline = .legacy then y else x)))) ∧
    IntegerLocalFamily t si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue t x hx) target.env) := by
  obtain ⟨sign,bits,valid⟩ := t
  cases sign with
  | false =>
    cases op with
    | add => exact UnsignedAddition.assignment_transport G F fuel source target bits valid si ti family i a x y hx hy readA readI
    | sub => exact UnsignedNarrowing.assignment_transport G F fuel source target bits valid si ti family i a x y hx hy readA readI
    | mul => exact UnsignedMultiplication.assignment_transport G F fuel source target bits valid si ti family i a x y hx hy readA readI
  | true =>
    cases op with
    | add => exact SignedNarrowAddition.assignment_transport bits valid G F fuel source target si ti family i a x y hx hy readA readI
    | sub => exact SignedNarrowSubtraction.assignment_transport bits valid G F fuel source target si ti family i a x y hx hy readA readI
    | mul => exact SignedNarrowMultiplication.assignment_transport bits valid G F fuel source target si ti family i a x y hx hy readA readI

namespace CheckedUnsigned
open UnsignedNarrowing (ty)

/-- Guard the V07 modular result at its width; multiplication tests zero before division. -/
def condition {C : Contract} {Γ : Ctx} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (op : RingOp)
    (a b : Val C Γ .uint) : Val C Γ .bool :=
  match op with
  | .add => .binop .le rfl rfl a (wrappingValue (ty bits valid) .add a b)
  | .sub => .binop .le rfl rfl b a
  | .mul => .ternary (.binop .eqB rfl rfl a (Checked.litU 0 (by decide)))
      (.simple (.bool true))
      (.binop .eqB rfl rfl
        (UnsignedQuotRem.value false (wrappingValue (ty bits valid) .mul a b) a) b)

private theorem value_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (op : RingOp)
    (a b : Val C Γ .uint) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (left : a.evalT target = .ok (integerValue (ty bits valid) x hx))
    (right : b.evalT target = .ok (integerValue (ty bits valid) y hy)) :
    (wrappingValue (ty bits valid) op a b).evalT target =
      .ok (integerValue (ty bits valid) ((ty bits valid).wrap (op.calculate x y))
        ((ty bits valid).wrap_mem (op.calculate x y))) := by
  cases op with
  | add => exact UnsignedAddition.add_value_run target bits valid a b x y hx hy left right
  | sub => exact UnsignedNarrowing.sub_value_run target bits valid a b x y hx hy left right
  | mul => exact UnsignedMultiplication.mul_value_run target bits valid a b x y hx hy left right

private theorem condition_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (op : RingOp)
    (a b : Val C Γ .uint) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (left : a.evalT target = .ok (integerValue (ty bits valid) x hx))
    (right : b.evalT target = .ok (integerValue (ty bits valid) y hy)) :
    (condition bits valid op a b).evalT target =
      .ok (decide ((ty bits valid).lo ≤ op.calculate x y ∧
        op.calculate x y ≤ (ty bits valid).hi)) := by
  have hp : (0 : Int) < ((2 ^ bits : Nat) : Int) := by
    exact_mod_cast Source.two_pow_pos bits
  have hx' : 0 ≤ x ∧ x < ((2 ^ bits : Nat) : Int) := by
    have h := hx
    simp only [ty,Source.IntTy.lo,Source.IntTy.hi,Bool.false_eq_true,if_false] at h
    omega
  have hy' : 0 ≤ y ∧ y < ((2 ^ bits : Nat) : Int) := by
    have h := hy
    simp only [ty,Source.IntTy.lo,Source.IntTy.hi,Bool.false_eq_true,if_false] at h
    omega
  cases op with
  | add =>
    have raw := value_run target bits valid .add a b x y hx hy left right
    have exactGuard := Checked.add_uint_exact hx'.1 hx'.2 hy'.1 hy'.2
    have bounds : (x ≤ (ty bits valid).wrap (x+y)) ↔
        ((ty bits valid).lo ≤ x+y ∧ x+y ≤ (ty bits valid).hi) := by
      rw [UnsignedNarrowing.wrap_eq,exactGuard]
      simp only [ty,Source.IntTy.lo,Source.IntTy.hi,Bool.false_eq_true,if_false]
      have positive := Source.two_pow_pos bits
      omega
    unfold condition
    rw [Val.evalT,left,raw]
    change Except.ok (decide (x ≤ (ty bits valid).wrap (x+y))) = _
    simp only [bounds,RingOp.calculate]
  | sub =>
    have bounds : y ≤ x ↔
        ((ty bits valid).lo ≤ x-y ∧ x-y ≤ (ty bits valid).hi) := by
      change y ≤ x ↔ (0 ≤ x-y ∧ x-y ≤ _)
      have upper := hx.2
      omega
    unfold condition
    rw [Val.evalT,right,left]
    change Except.ok (decide (y ≤ x)) = _
    simp only [bounds,RingOp.calculate]
  | mul =>
    have raw := value_run target bits valid .mul a b x y hx hy left right
    have exactGuard := Checked.mul_uint_exact hx'.1 hx'.2 hy'.1 hy'.2
    have bounds : (x = 0 ∨ ((ty bits valid).wrap (x*y)).tdiv x = y) ↔
        ((ty bits valid).lo ≤ x*y ∧ x*y ≤ (ty bits valid).hi) := by
      rw [UnsignedNarrowing.wrap_eq,exactGuard]
      have nonneg := Int.mul_nonneg hx'.1 hy'.1
      simp only [ty,Source.IntTy.lo,Source.IntTy.hi,Bool.false_eq_true,if_false]
      have positive := Source.two_pow_pos bits
      omega
    have zeroTest : (Val.binop .eqB rfl rfl a (Checked.litU 0 (by decide))).evalT target =
        .ok (decide (x = 0)) := by
      rw [Val.evalT,left]
      rfl
    change (Val.ternary _ _ _).evalT target = _
    rw [Val.evalT,zeroTest]
    by_cases zero : x = 0
    · have inRange := bounds.mp (Or.inl zero)
      simp only [zero,decide_true,ok_bind,if_true]
      have fits : (ty bits valid).lo ≤ 0*y ∧ 0*y ≤ (ty bits valid).hi := by simpa only [zero] using inRange
      simp only [RingOp.calculate,zero,fits,decide_true]
      rfl
    · have quotient := UnsignedQuotRem.value_run bits valid target false
        (wrappingValue (ty bits valid) .mul a b) a ((ty bits valid).wrap (x*y)) x
        ((ty bits valid).wrap_mem (x*y)) hx zero raw left
      simp only [zero,decide_false,ok_bind,Bool.false_eq_true,if_false]
      rw [Val.evalT,quotient,right]
      change Except.ok (decide (((ty bits valid).wrap (x*y)).tdiv x = y)) = _
      have reduced : (((ty bits valid).wrap (x*y)).tdiv x = y) ↔
          ((ty bits valid).lo ≤ x*y ∧ x*y ≤ (ty bits valid).hi) := by
        simpa only [zero,false_or] using bounds
      simp only [reduced,RingOp.calculate]

/-- Guard the existing unsigned ring program toward `Solidity.Goals.lowerLoopsCorrect`. No replacement of the held validator/scalar endpoint or frontend producer is asserted. -/
def operand {C : Contract} {Γ : Ctx} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (op : RingOp)
    (checked : Bool) (a b : Idx Γ (.val .uint)) :
    DeferredSource.Operand C Γ (.prim .uint) :=
  let x : Val C Γ .uint := .simple (.local a)
  let y : Val C Γ .uint := .simple (.local b)
  ⟨Γ,(if checked then .cons (PanicGuard.code .arithmetic (condition bits valid op x y)) .nil else .nil),
    .val (wrappingValue (ty bits valid) op x y)⟩

private theorem source_value {D : Source.Layout}
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (op : RingOp) (checked : Bool) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) :
    Source.binVal checked op.source
      (.int x hx : Source.Val D (.int (ty bits valid))) (.int y hy) =
      if checked = true ∧ ¬ ((ty bits valid).lo ≤ op.calculate x y ∧
          op.calculate x y ≤ (ty bits valid).hi) then
        .error (.revert (Source.panicData .arithmetic))
      else .ok (Source.intWrap (ty bits valid) (op.calculate x y)) := by
  have reduces : Source.binVal checked op.source
      (.int x hx : Source.Val D (.int (ty bits valid))) (.int y hy) =
        Source.intRes (ty bits valid) checked (op.calculate x y) := by
    cases op <;> rfl
  rw [reduces]
  by_cases fits : (ty bits valid).lo ≤ op.calculate x y ∧ op.calculate x y ≤ (ty bits valid).hi
  · have wrapped := UnsignedNarrowing.wrap_of_range bits valid (op.calculate x y) fits
    rw [Source.intRes,dif_pos fits]
    simp only [show ¬ (checked = true ∧ ¬ ((ty bits valid).lo ≤ op.calculate x y ∧ op.calculate x y ≤ (ty bits valid).hi)) from by intro h; exact h.2 fits,if_false,Source.intWrap,wrapped]
    rfl
  · rw [Source.intRes,dif_neg fits]
    cases checked <;> simp only [fits,not_false_eq_true,and_true,Bool.false_eq_true,if_false,if_true,Source.panic]
    all_goals rfl

private theorem operand_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (op : RingOp)
    (checked : Bool) (a b : Idx Γ (.val .uint)) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : TEnv.get a target.env = integerValue (ty bits valid) x hx)
    (readB : TEnv.get b target.env = integerValue (ty bits valid) y hy) :
    (operand bits valid op checked a b).run target =
      if checked = true ∧ ¬ ((ty bits valid).lo ≤ op.calculate x y ∧
          op.calculate x y ≤ (ty bits valid).hi) then
        .error (THalt.ofData (Source.panicData .arithmetic))
      else .ok (⟨target,List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap (op.calculate x y))
          ((ty bits valid).wrap_mem (op.calculate x y)))) := by
  have left : (Val.simple (.local a) : Val C Γ .uint).evalT target =
      .ok (integerValue (ty bits valid) x hx) := congrArg Except.ok readA
  have right : (Val.simple (.local b) : Val C Γ .uint).evalT target =
      .ok (integerValue (ty bits valid) y hy) := congrArg Except.ok readB
  have test := condition_run target bits valid op _ _ x y hx hy left right
  have value := value_run target bits valid op _ _ x y hx hy left right
  let gateCode : Prog C Γ Γ := if checked then
    .cons (PanicGuard.code .arithmetic (condition bits valid op (.simple (.local a)) (.simple (.local b)))) .nil
    else .nil
  have prefixRun : gateCode.run target =
      if checked = true ∧ ¬ ((ty bits valid).lo ≤ op.calculate x y ∧ op.calculate x y ≤ (ty bits valid).hi) then
        .error (THalt.ofData (Source.panicData .arithmetic))
      else .ok (⟨target,List.prefix_refl _⟩ : Out C target.H Γ) := by
    cases checked with
    | false => simp only [gateCode,Bool.false_eq_true,if_false,false_and,Prog.run_nil]
    | true =>
      by_cases fits : (ty bits valid).lo ≤ op.calculate x y ∧ op.calculate x y ≤ (ty bits valid).hi
      · have passed := PanicGuard.run target .arithmetic _ true (by simpa only [fits,decide_true] using test)
        simp only [if_true] at passed
        change (Prog.cons _ Prog.nil).run target = _
        rw [Prog.run_cons_ok passed,Prog.run_nil]
        simp only [true_and,if_neg (show ¬ ¬ ((ty bits valid).lo ≤ op.calculate x y ∧ op.calculate x y ≤ (ty bits valid).hi) from by intro h; exact h fits)]
        rfl
      · have failed := PanicGuard.run target .arithmetic _ false (by simpa only [fits,decide_false] using test)
        simp only [Bool.false_eq_true,if_false] at failed
        change TRun.seq (PanicGuard.code .arithmetic _).runR _ target = _
        simp only [TRun.seq,show (PanicGuard.code .arithmetic _).runR target =
          .error (THalt.ofData (Source.panicData .arithmetic)) from failed,true_and,if_pos fits]
  change (DeferredSource.Operand.run ⟨Γ,gateCode,.val (wrappingValue (ty bits valid) op
    (.simple (.local a)) (.simple (.local b)))⟩ target) = _
  unfold DeferredSource.Operand.run
  rw [prefixRun]
  by_cases failed : checked = true ∧ ¬ ((ty bits valid).lo ≤ op.calculate x y ∧ op.calculate x y ≤ (ty bits valid).hi)
  · simp only [if_pos failed]
    rfl
  · simp only [if_neg failed]
    rw [Ext.eq_of_depth gateCode.ext Ext.refl]
    simp only [bind,Except.bind,Src.valueT]
    rw [value]
    rfl

/-- All unsigned widths, three operators and both modes: success or arithmetic panic. Premises observe initial aligned locals, with no overflow exclusion or desired run. The final wrapped-value law does not assert observed success on failure. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (op : RingOp)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (a b : ι) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy) :
    let failed := F.checked = true ∧ ¬ ((ty bits valid).lo ≤ op.calculate x y ∧
      op.calculate x y ≤ (ty bits valid).hi)
    (Source.evalE G F (fuel+3)
      (.binary op.source (.local (si a)) (.local (si b)))).run source =
      (if failed then (.error (.revert (Source.panicData .arithmetic)),source)
        else (.ok (.val (Source.intWrap (ty bits valid) (op.calculate x y))),source)) ∧
    (operand bits valid op F.checked (ti a) (ti b)).run target =
      (if failed then .error (THalt.ofData (Source.panicData .arithmetic))
        else .ok (⟨target,List.prefix_refl _⟩,
          .prim (integerValue (ty bits valid) ((ty bits valid).wrap (op.calculate x y))
            ((ty bits valid).wrap_mem (op.calculate x y))))) ∧
    IntValueRel (ty bits valid)
      (Source.intWrap (ty bits valid) (op.calculate x y) : Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) ((ty bits valid).wrap (op.calculate x y))
        ((ty bits valid).wrap_mem (op.calculate x y))) := by
  have left := family.read a x hx readA
  have right := family.read b y hy readB
  refine ⟨?_,operand_run target bits valid op F.checked (ti a) (ti b) x y hx hy left right,?_⟩
  · have pair := source_local_pair G F fuel source (ty bits valid) (si a) (si b) x y hx hy readA readB
    rw [Source.evalE,Source.withLibraryCalldata_known]
    have nonspecial : (decide (op.source = .and) || decide (op.source = .or)) = false := by cases op <;> rfl
    simp only [nonspecial,Bool.false_eq_true,if_false]
    rw [Source.Hoare.run_bind,pair]
    change (do
      let value ← Source.EM.lift (Source.binVal F.checked op.source
        (.int x hx : Source.Val E.layout (.int (ty bits valid))) (.int y hy))
      pure (Source.RVal.val value)).run source = _
    rw [source_value]
    split <;> rfl
  · exact integer_related _ _ _

end CheckedUnsigned

namespace CheckedSigned
open SignedWidthCasts (ty)

private theorem hi_eq (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (ty bits valid).hi = -(ty bits valid).lo - 1 := by
  have positive := Source.two_pow_pos (bits-1)
  change (((2 ^ (bits-1)-1 : Nat) : Int)) = -(-((2 ^ (bits-1) : Nat) : Int)) - 1
  omega

private theorem min_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (ty bits valid).lo ≤ (ty bits valid).lo ∧ (ty bits valid).lo ≤ (ty bits valid).hi :=
  ⟨Int.le_refl _,Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2⟩

private theorem max_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (ty bits valid).lo ≤ (ty bits valid).hi ∧ (ty bits valid).hi ≤ (ty bits valid).hi :=
  ⟨Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2,Int.le_refl _⟩

private theorem value_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (op : RingOp)
    (a b : Val C Γ .int) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (left : a.evalT target = .ok (integerValue (ty bits valid) x hx))
    (right : b.evalT target = .ok (integerValue (ty bits valid) y hy)) :
    (wrappingValue (ty bits valid) op a b).evalT target =
      .ok (integerValue (ty bits valid) ((ty bits valid).wrap (op.calculate x y))
        ((ty bits valid).wrap_mem (op.calculate x y))) := by
  cases op with
  | add => exact SignedNarrowAddition.add_value_run bits valid target a b x y hx hy left right
  | sub => exact SignedNarrowSubtraction.sub_value_run bits valid target a b x y hx hy left right
  | mul => exact SignedNarrowMultiplication.mul_value_run bits valid target a b x y hx hy left right

private theorem le_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (a b : Val C Γ .int) (x y : PrimTy.int.Denote)
    (left : a.evalT target = .ok x) (right : b.evalT target = .ok y) :
    (Val.binop .le rfl rfl a b).evalT target = .ok (decide (x.val ≤ y.val)) := by
  rw [Val.evalT,left,right]
  rfl

private theorem ge_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (a b : Val C Γ .int) (x y : PrimTy.int.Denote)
    (left : a.evalT target = .ok x) (right : b.evalT target = .ok y) :
    (Val.binop .ge rfl rfl a b).evalT target = .ok (decide (y.val ≤ x.val)) := by
  rw [Val.evalT,left,right]
  rfl

private theorem gt_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (a b : Val C Γ .int) (x y : PrimTy.int.Denote)
    (left : a.evalT target = .ok x) (right : b.evalT target = .ok y) :
    (Val.binop .gt rfl rfl a b).evalT target = .ok (decide (y.val < x.val)) := by
  rw [Val.evalT,left,right]
  rfl

private theorem eq_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (a b : Val C Γ .int) (x y : PrimTy.int.Denote)
    (left : a.evalT target = .ok x) (right : b.evalT target = .ok y) :
    (Val.binop .eqB rfl rfl a b).evalT target = .ok (decide (x.val = y.val)) := by
  rw [Val.evalT,left,right]
  rfl

private theorem ternary_true {C : Contract} {Γ : Ctx} {p : PrimTy}
    (target : State C Γ) (c : Val C Γ .bool) (a b : Val C Γ p)
    (test : c.evalT target = .ok true) :
    (Val.ternary c a b).evalT target = a.evalT target := by
  rw [Val.evalT,test]
  rfl

private theorem ternary_false {C : Contract} {Γ : Ctx} {p : PrimTy}
    (target : State C Γ) (c : Val C Γ .bool) (a b : Val C Γ p)
    (test : c.evalT target = .ok false) :
    (Val.ternary c a b).evalT target = b.evalT target := by
  rw [Val.evalT,test]
  rfl

private theorem div_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi) (positive : 0 < y) :
    (ty bits valid).lo ≤ x.tdiv y ∧ x.tdiv y ≤ (ty bits valid).hi := by
  have zero := integer_zero_range (ty bits valid)
  by_cases nonneg : 0 ≤ x
  · have lower := Int.tdiv_nonneg nonneg (Int.le_of_lt positive)
    have upper := Int.tdiv_le_self y nonneg
    omega
  · have lower := Int.tdiv_nonneg (show 0 ≤ -x by omega) (Int.le_of_lt positive)
    have upper := Int.tdiv_le_self y (show 0 ≤ -x by omega)
    have negation : x.tdiv y = -((-x).tdiv y) := by rw [←Int.neg_tdiv,Int.neg_neg]
    rw [negation]
    omega

private theorem div_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (a b : Val C Γ .int) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (positive : 0 < y)
    (left : a.evalT target = .ok (integerValue (ty bits valid) x hx))
    (right : b.evalT target = .ok (integerValue (ty bits valid) y hy)) :
    (Val.binop .div rfl rfl a b).evalT target =
      .ok (integerValue (ty bits valid) (x.tdiv y) (div_range bits valid x y hx positive)) := by
  have range := integer_range (ty bits valid) (x.tdiv y) (div_range bits valid x y hx positive)
  change PrimTy.int.inRange (x.tdiv y) = true at range
  rw [Val.evalT,left]
  change (do
    let v ← b.evalT target
    TRes.ofOpt (BinOp.evalT .div rfl (integerValue (ty bits valid) x hx) v)) = _
  rw [right]
  change TRes.ofOpt ((if y = 0 then none else some (x.tdiv y)).bind PrimTy.int.ofInt?) = _
  simp only [if_neg (by omega : y ≠ 0),Option.bind_some,PrimTy.ofInt?,dif_pos range]
  rfl

private def predicate (lo hi : Int) (op : RingOp) (x y : Int) : Prop :=
  match op with
  | .add => if 0 ≤ y then x ≤ hi-y else lo-y ≤ x
  | .sub => if 0 ≤ y then lo+y ≤ x else x ≤ hi+y
  | .mul => x = 0 ∨ y = 0 ∨
      (if 0 < x then (if 0 < y then x ≤ hi.tdiv y else lo.tdiv x ≤ y)
       else (if 0 < y then lo.tdiv y ≤ x
         else (x ≠ lo ∧ y ≠ lo ∧ -x ≤ hi.tdiv (-y))))

private instance predicate_decidable (lo hi : Int) (op : RingOp) (x y : Int) :
    Decidable (predicate lo hi op x y) := by
  cases op <;> unfold predicate <;> infer_instance

private theorem predicate_exact (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (op : RingOp) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) :
    predicate (ty bits valid).lo (ty bits valid).hi op x y ↔
      ((ty bits valid).lo ≤ op.calculate x y ∧ op.calculate x y ≤ (ty bits valid).hi) := by
  let M : Int := ((2 ^ (bits-1) : Nat) : Int)
  have positive : 0 < M := Int.ofNat_lt.mpr (Source.two_pow_pos (bits-1))
  have lo : (ty bits valid).lo = -M := rfl
  have hi : (ty bits valid).hi = M-1 := by rw [hi_eq,lo]; omega
  have hxM : -M ≤ x ∧ x < M := by rw [lo,hi] at hx; omega
  have hyM : -M ≤ y ∧ y < M := by rw [lo,hi] at hy; omega
  cases op with
  | add => simpa only [predicate,RingOp.calculate,lo,hi] using Checked.add_int_exact hxM (b := y)
  | sub => simpa only [predicate,RingOp.calculate,lo,hi] using Checked.sub_int_exact hxM (b := y)
  | mul => simpa only [predicate,RingOp.calculate,lo,hi,Int.zero_sub] using Checked.mul_int_exact positive hxM hyM

/-- Width-specific signed guards mirror the existing checked formulas; zero/minimum branches stay lazy. -/
def condition {C : Contract} {Γ : Ctx} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (op : RingOp)
    (a b : Val C Γ .int) : Val C Γ .bool :=
  let zero : Val C Γ .int := IntegerConstants.value (ty bits valid) 0 (integer_zero_range _)
  let min : Val C Γ .int := IntegerConstants.value (ty bits valid) (ty bits valid).lo (min_range bits valid)
  let max : Val C Γ .int := IntegerConstants.value (ty bits valid) (ty bits valid).hi (max_range bits valid)
  let eq (x y : Val C Γ .int) := Val.binop .eqB rfl rfl x y
  let pos (x : Val C Γ .int) := Val.binop .gt rfl rfl x zero
  let neg (x : Val C Γ .int) := SignedNarrowSubtraction.subValue bits zero x
  match op with
  | .add => .ternary (.binop .ge rfl rfl b zero)
      (.binop .le rfl rfl a (SignedNarrowSubtraction.subValue bits max b))
      (.binop .ge rfl rfl a (SignedNarrowSubtraction.subValue bits min b))
  | .sub => .ternary (.binop .ge rfl rfl b zero)
      (.binop .ge rfl rfl a (SignedNarrowAddition.addValue bits min b))
      (.binop .le rfl rfl a (SignedNarrowAddition.addValue bits max b))
  | .mul => .ternary (eq a zero) (.simple (.bool true))
      (.ternary (eq b zero) (.simple (.bool true))
        (.ternary (pos a)
          (.ternary (pos b) (.binop .le rfl rfl a (.binop .div rfl rfl max b))
            (.binop .ge rfl rfl b (.binop .div rfl rfl min a)))
          (.ternary (pos b) (.binop .ge rfl rfl a (.binop .div rfl rfl min b))
            (.ternary (eq a min) (.simple (.bool false))
              (.ternary (eq b min) (.simple (.bool false))
                (.binop .le rfl rfl (neg a) (.binop .div rfl rfl max (neg b))))))))

private theorem exact_value_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (op : RingOp)
    (a b : Val C Γ .int) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (result : (ty bits valid).lo ≤ op.calculate x y ∧ op.calculate x y ≤ (ty bits valid).hi)
    (left : a.evalT target = .ok (integerValue (ty bits valid) x hx))
    (right : b.evalT target = .ok (integerValue (ty bits valid) y hy)) :
    (wrappingValue (ty bits valid) op a b).evalT target =
      .ok (integerValue (ty bits valid) (op.calculate x y) result) := by
  have wrapped := SignedNarrowing.wrap_of_range bits valid (op.calculate x y) result
  simpa only [wrapped] using value_run target bits valid op a b x y hx hy left right

private theorem predicate_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (op : RingOp)
    (a b : Val C Γ .int) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (left : a.evalT target = .ok (integerValue (ty bits valid) x hx))
    (right : b.evalT target = .ok (integerValue (ty bits valid) y hy)) :
    (condition bits valid op a b).evalT target =
      .ok (decide (predicate (ty bits valid).lo (ty bits valid).hi op x y)) := by
  let zero : Val C Γ .int := IntegerConstants.value (ty bits valid) 0 (integer_zero_range (ty bits valid))
  let min : Val C Γ .int := IntegerConstants.value (ty bits valid) (ty bits valid).lo (min_range bits valid)
  let max : Val C Γ .int := IntegerConstants.value (ty bits valid) (ty bits valid).hi (max_range bits valid)
  have zeroEval := IntegerConstants.value_run (C := C) (Γ := Γ) target (ty bits valid) 0 (integer_zero_range (ty bits valid))
  have minEval := IntegerConstants.value_run (C := C) (Γ := Γ) target (ty bits valid) (ty bits valid).lo (min_range bits valid)
  have maxEval := IntegerConstants.value_run (C := C) (Γ := Γ) target (ty bits valid) (ty bits valid).hi (max_range bits valid)
  have zeroRange := integer_zero_range (ty bits valid)
  have symmetric : (ty bits valid).hi = -(ty bits valid).lo-1 := hi_eq bits valid
  have nonnegY : (Val.binop .ge rfl rfl b zero).evalT target = .ok (decide (0 ≤ y)) :=
    ge_run target b zero _ _ right zeroEval
  cases op with
  | add =>
    unfold condition
    by_cases nonneg : 0 ≤ y
    · rw [ternary_true target _ _ _ (by simpa only [nonneg,decide_true] using nonnegY)]
      have fits : (ty bits valid).lo ≤ (ty bits valid).hi-y ∧ (ty bits valid).hi-y ≤ (ty bits valid).hi := by omega
      have threshold := exact_value_run target bits valid .sub max b (ty bits valid).hi y
        (max_range bits valid) hy fits maxEval right
      have result := le_run target a (SignedNarrowSubtraction.subValue bits max b) _ _ left threshold
      simpa only [predicate,if_pos nonneg] using result
    · rw [ternary_false target _ _ _ (by simpa only [nonneg,decide_false] using nonnegY)]
      have fits : (ty bits valid).lo ≤ (ty bits valid).lo-y ∧ (ty bits valid).lo-y ≤ (ty bits valid).hi := by omega
      have threshold := exact_value_run target bits valid .sub min b (ty bits valid).lo y
        (min_range bits valid) hy fits minEval right
      have result := ge_run target a (SignedNarrowSubtraction.subValue bits min b) _ _ left threshold
      simpa only [predicate,if_neg nonneg] using result
  | sub =>
    unfold condition
    by_cases nonneg : 0 ≤ y
    · rw [ternary_true target _ _ _ (by simpa only [nonneg,decide_true] using nonnegY)]
      have fits : (ty bits valid).lo ≤ (ty bits valid).lo+y ∧ (ty bits valid).lo+y ≤ (ty bits valid).hi := by omega
      have threshold := exact_value_run target bits valid .add min b (ty bits valid).lo y
        (min_range bits valid) hy fits minEval right
      have result := ge_run target a (SignedNarrowAddition.addValue bits min b) _ _ left threshold
      simpa only [predicate,if_pos nonneg] using result
    · rw [ternary_false target _ _ _ (by simpa only [nonneg,decide_false] using nonnegY)]
      have fits : (ty bits valid).lo ≤ (ty bits valid).hi+y ∧ (ty bits valid).hi+y ≤ (ty bits valid).hi := by omega
      have threshold := exact_value_run target bits valid .add max b (ty bits valid).hi y
        (max_range bits valid) hy fits maxEval right
      have result := le_run target a (SignedNarrowAddition.addValue bits max b) _ _ left threshold
      simpa only [predicate,if_neg nonneg] using result
  | mul =>
    have eqZeroA : (Val.binop .eqB rfl rfl a zero).evalT target = .ok (decide (x = 0)) :=
      eq_run target a zero _ _ left zeroEval
    have eqZeroB : (Val.binop .eqB rfl rfl b zero).evalT target = .ok (decide (y = 0)) :=
      eq_run target b zero _ _ right zeroEval
    have posA : (Val.binop .gt rfl rfl a zero).evalT target = .ok (decide (0 < x)) :=
      gt_run target a zero _ _ left zeroEval
    have posB : (Val.binop .gt rfl rfl b zero).evalT target = .ok (decide (0 < y)) :=
      gt_run target b zero _ _ right zeroEval
    unfold condition
    by_cases xa : x = 0
    · rw [ternary_true target _ _ _ (by simpa only [xa,decide_true] using eqZeroA)]
      simp only [predicate,xa,true_or,decide_true]
      rfl
    · rw [ternary_false target _ _ _ (by simpa only [xa,decide_false] using eqZeroA)]
      by_cases yb : y = 0
      · rw [ternary_true target _ _ _ (by simpa only [yb,decide_true] using eqZeroB)]
        simp only [predicate,xa,yb,false_or,true_or,decide_true]
        rfl
      · rw [ternary_false target _ _ _ (by simpa only [yb,decide_false] using eqZeroB)]
        by_cases xp : 0 < x
        · rw [ternary_true target _ _ _ (by simpa only [xp,decide_true] using posA)]
          by_cases yp : 0 < y
          · rw [ternary_true target _ _ _ (by simpa only [yp,decide_true] using posB)]
            have quotient := div_run target bits valid max b (ty bits valid).hi y (max_range bits valid) hy yp maxEval right
            have result := le_run target a (.binop .div rfl rfl max b) _ _ left quotient
            simpa only [predicate,xa,yb,false_or,if_pos xp,if_pos yp] using result
          · rw [ternary_false target _ _ _ (by simpa only [yp,decide_false] using posB)]
            have quotient := div_run target bits valid min a (ty bits valid).lo x (min_range bits valid) hx xp minEval left
            have result := ge_run target b (.binop .div rfl rfl min a) _ _ right quotient
            simpa only [predicate,xa,yb,false_or,if_pos xp,if_neg yp] using result
        · rw [ternary_false target _ _ _ (by simpa only [xp,decide_false] using posA)]
          by_cases yp : 0 < y
          · rw [ternary_true target _ _ _ (by simpa only [yp,decide_true] using posB)]
            have quotient := div_run target bits valid min b (ty bits valid).lo y (min_range bits valid) hy yp minEval right
            have result := ge_run target a (.binop .div rfl rfl min b) _ _ left quotient
            simpa only [predicate,xa,yb,false_or,if_neg xp,if_pos yp] using result
          · rw [ternary_false target _ _ _ (by simpa only [yp,decide_false] using posB)]
            have eqMinA : (Val.binop .eqB rfl rfl a min).evalT target = .ok (decide (x = (ty bits valid).lo)) :=
              eq_run target a min _ _ left minEval
            have eqMinB : (Val.binop .eqB rfl rfl b min).evalT target = .ok (decide (y = (ty bits valid).lo)) :=
              eq_run target b min _ _ right minEval
            by_cases xmin : x = (ty bits valid).lo
            · rw [ternary_true target _ _ _ (by simpa only [xmin,decide_true] using eqMinA)]
              simp only [predicate,xa,yb,false_or,if_neg xp,if_neg yp]
              simp only [xmin,ne_eq,not_true_eq_false,false_and,decide_false]
              rfl
            · rw [ternary_false target _ _ _ (by simpa only [xmin,decide_false] using eqMinA)]
              by_cases ymin : y = (ty bits valid).lo
              · rw [ternary_true target _ _ _ (by simpa only [ymin,decide_true] using eqMinB)]
                simp only [predicate,xa,yb,false_or,if_neg xp,if_neg yp]
                simp only [ymin,ne_eq,not_true_eq_false,and_false,false_and,decide_false]
                rfl
              · rw [ternary_false target _ _ _ (by simpa only [ymin,decide_false] using eqMinB)]
                have negX : (ty bits valid).lo ≤ -x ∧ -x ≤ (ty bits valid).hi := by omega
                have negY : (ty bits valid).lo ≤ -y ∧ -y ≤ (ty bits valid).hi := by omega
                have ax : (SignedNarrowSubtraction.subValue bits zero a).evalT target =
                    .ok (integerValue (ty bits valid) (-x) negX) := by
                  simpa only [RingOp.calculate,Int.zero_sub] using
                    exact_value_run target bits valid .sub zero a 0 x zeroRange hx
                      (by simpa only [RingOp.calculate,Int.zero_sub] using negX) zeroEval left
                have by' : (SignedNarrowSubtraction.subValue bits zero b).evalT target =
                    .ok (integerValue (ty bits valid) (-y) negY) := by
                  simpa only [RingOp.calculate,Int.zero_sub] using
                    exact_value_run target bits valid .sub zero b 0 y zeroRange hy
                      (by simpa only [RingOp.calculate,Int.zero_sub] using negY) zeroEval right
                have quotient := div_run target bits valid max (SignedNarrowSubtraction.subValue bits zero b)
                  (ty bits valid).hi (-y) (max_range bits valid) negY (by omega) maxEval by'
                have result := le_run target (SignedNarrowSubtraction.subValue bits zero a)
                  (.binop .div rfl rfl max (SignedNarrowSubtraction.subValue bits zero b)) _ _ ax quotient
                simpa only [predicate,xa,yb,false_or,if_neg xp,if_neg yp,xmin,ymin,ne_eq,not_false_eq_true,true_and,
                  RingOp.calculate,Int.zero_sub] using result

private theorem condition_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (op : RingOp)
    (a b : Val C Γ .int) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (left : a.evalT target = .ok (integerValue (ty bits valid) x hx))
    (right : b.evalT target = .ok (integerValue (ty bits valid) y hy)) :
    (condition bits valid op a b).evalT target =
      .ok (decide ((ty bits valid).lo ≤ op.calculate x y ∧ op.calculate x y ≤ (ty bits valid).hi)) := by
  simpa only [predicate_exact bits valid op x y hx hy] using
    predicate_run target bits valid op a b x y hx hy left right

/-- Existing V07 value programs behind a width-specific guard; no frontend or validator association is asserted. -/
def operand {C : Contract} {Γ : Ctx} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (op : RingOp)
    (checked : Bool) (a b : Idx Γ (.val .int)) : DeferredSource.Operand C Γ (.prim .int) :=
  let x : Val C Γ .int := .simple (.local a)
  let y : Val C Γ .int := .simple (.local b)
  let value : Val C Γ .int := match op with
    | .add => SignedNarrowAddition.addValue bits x y
    | .sub => SignedNarrowSubtraction.subValue bits x y
    | .mul => SignedNarrowMultiplication.mulValue bits x y
  PanicGuard.checkedOperand .arithmetic checked (condition bits valid op x y) value

private theorem wrap_self (t : Source.IntTy) (z : Int) (fits : t.lo ≤ z ∧ z ≤ t.hi) : t.wrap z = z := by
  obtain ⟨sign,bits,valid⟩ := t
  cases sign with
  | false => exact UnsignedNarrowing.wrap_of_range bits valid z fits
  | true => exact SignedNarrowing.wrap_of_range bits valid z fits

private theorem source_value {D : Source.Layout} (t : Source.IntTy)
    (op : RingOp) (checked : Bool) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi) :
    Source.binVal checked op.source (.int x hx : Source.Val D (.int t)) (.int y hy) =
      if checked = true ∧ ¬ (t.lo ≤ op.calculate x y ∧ op.calculate x y ≤ t.hi) then
        .error (.revert (Source.panicData .arithmetic))
      else .ok (Source.intWrap t (op.calculate x y)) := by
  have reduces : Source.binVal checked op.source (.int x hx : Source.Val D (.int t)) (.int y hy) =
      Source.intRes t checked (op.calculate x y) := by cases op <;> rfl
  rw [reduces]
  by_cases fits : t.lo ≤ op.calculate x y ∧ op.calculate x y ≤ t.hi
  · have wrapped := wrap_self t (op.calculate x y) fits
    rw [Source.intRes,dif_pos fits]
    simp only [show ¬ (checked = true ∧ ¬ (t.lo ≤ op.calculate x y ∧ op.calculate x y ≤ t.hi)) from
      by intro h; exact h.2 fits,if_false,Source.intWrap,wrapped]
    rfl
  · rw [Source.intRes,dif_neg fits]
    cases checked <;> simp only [fits,not_false_eq_true,and_true,Bool.false_eq_true,if_false,if_true,Source.panic]
    all_goals rfl

private theorem source_run {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ)
    (t : Source.IntTy) (op : RingOp) (a b : Source.Idx srcΓ (.int t)) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : source.1.get a = .int x hx) (readB : source.1.get b = .int y hy) :
    (Source.evalE G F (fuel+3) (.binary op.source (.local a) (.local b))).run source =
      if F.checked = true ∧ ¬ (t.lo ≤ op.calculate x y ∧ op.calculate x y ≤ t.hi) then
        (.error (.revert (Source.panicData .arithmetic)),source)
      else (.ok (.val (Source.intWrap t (op.calculate x y))),source) := by
  have pair := source_local_pair G F fuel source t a b x y hx hy readA readB
  rw [Source.evalE,Source.withLibraryCalldata_known]
  have nonspecial : (decide (op.source = .and) || decide (op.source = .or)) = false := by cases op <;> rfl
  simp only [nonspecial,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,pair]
  change (do
    let value ← Source.EM.lift (Source.binVal F.checked op.source
      (.int x hx : Source.Val E.layout (.int t)) (.int y hy))
    pure (Source.RVal.val value)).run source = _
  rw [source_value]
  split <;> rfl

private theorem operand_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (op : RingOp)
    (checked : Bool) (a b : Idx Γ (.val .int)) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : TEnv.get a target.env = integerValue (ty bits valid) x hx)
    (readB : TEnv.get b target.env = integerValue (ty bits valid) y hy) :
    (operand bits valid op checked a b).run target =
      if checked = true ∧ ¬ ((ty bits valid).lo ≤ op.calculate x y ∧ op.calculate x y ≤ (ty bits valid).hi) then
        .error (THalt.ofData (Source.panicData .arithmetic))
      else .ok (⟨target,List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap (op.calculate x y))
          ((ty bits valid).wrap_mem (op.calculate x y)))) := by
  have left : (Val.simple (.local a) : Val C Γ .int).evalT target =
      .ok (integerValue (ty bits valid) x hx) := congrArg Except.ok readA
  have right : (Val.simple (.local b) : Val C Γ .int).evalT target =
      .ok (integerValue (ty bits valid) y hy) := congrArg Except.ok readB
  have test := condition_run target bits valid op _ _ x y hx hy left right
  have computed := value_run target bits valid op _ _ x y hx hy left right
  have joined := PanicGuard.checkedOperand_run target .arithmetic checked
    (condition bits valid op (.simple (.local a)) (.simple (.local b)))
    (wrappingValue (ty bits valid) op (.simple (.local a)) (.simple (.local b))) _ _ test computed
  cases op <;> simpa only [operand,wrappingValue,ty,decide_eq_false_iff_not] using joined

/-- Signed local ring arithmetic at every width and in both modes toward `Solidity.Goals.lowerLoopsCorrect`. Initial reads/alignment suffice; overflow, zero and minimum inputs are not excluded. No producer association is asserted. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (op : RingOp)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (a b : ι) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy) :
    let failed := F.checked = true ∧ ¬ ((ty bits valid).lo ≤ op.calculate x y ∧ op.calculate x y ≤ (ty bits valid).hi)
    if failed then
      (Source.evalE G F (fuel+3) (.binary op.source (.local (si a)) (.local (si b)))).run source =
        (.error (.revert (Source.panicData .arithmetic)),source) ∧
      (operand bits valid op F.checked (ti a) (ti b)).run target =
        .error (THalt.ofData (Source.panicData .arithmetic))
    else
      (Source.evalE G F (fuel+3) (.binary op.source (.local (si a)) (.local (si b)))).run source =
        (.ok (.val (Source.intWrap (ty bits valid) (op.calculate x y))),source) ∧
      (operand bits valid op F.checked (ti a) (ti b)).run target =
        .ok (⟨target,List.prefix_refl _⟩,
          .prim (integerValue (ty bits valid) ((ty bits valid).wrap (op.calculate x y))
            ((ty bits valid).wrap_mem (op.calculate x y)))) ∧
      IntValueRel (ty bits valid)
        (Source.intWrap (ty bits valid) (op.calculate x y) : Source.Val E.layout (.int (ty bits valid)))
        (integerValue (ty bits valid) ((ty bits valid).wrap (op.calculate x y))
          ((ty bits valid).wrap_mem (op.calculate x y))) := by
  have sr := source_run G F fuel source (ty bits valid) op (si a) (si b) x y hx hy readA readB
  have nr := operand_run target bits valid op F.checked (ti a) (ti b) x y hx hy
    (family.read a x hx readA) (family.read b y hy readB)
  by_cases failed : F.checked = true ∧ ¬ ((ty bits valid).lo ≤ op.calculate x y ∧ op.calculate x y ≤ (ty bits valid).hi)
  · simp only [if_pos failed] at sr nr ⊢
    exact ⟨sr,nr⟩
  · simp only [if_neg failed] at sr nr ⊢
    exact ⟨sr,nr,integer_related _ _ _⟩

end CheckedSigned

namespace SignedQuotRem
open SignedWidthCasts (ty)

abbrev calculate := Solidity.Lowering.V07.UnsignedQuotRem.calculate

abbrev sourceOp := Solidity.Lowering.V07.UnsignedQuotRem.sourceOp

private theorem remainder_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x y : Int) (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (nonzero : y ≠ 0) :
    (ty bits valid).lo ≤ x.tmod y ∧ x.tmod y ≤ (ty bits valid).hi := by
  have positive := Source.two_pow_pos (bits-1)
  have hi := CheckedSigned.hi_eq bits valid
  have small : (x.tmod y).natAbs < y.natAbs := by
    rw [Int.natAbs_tmod]
    exact Nat.mod_lt _ (by omega)
  change -((2^(bits-1) : Nat) : Int) ≤ y ∧ y ≤ _ at hy
  change -((2^(bits-1) : Nat) : Int) ≤ x.tmod y ∧ x.tmod y ≤ _
  change (ty bits valid).hi = -(-((2^(bits-1) : Nat) : Int)) - 1 at hi
  omega

private theorem quotient_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi) (nonzero : y ≠ 0)
    (safe : ¬ (x = (ty bits valid).lo ∧ y = -1)) :
    (ty bits valid).lo ≤ x.tdiv y ∧ x.tdiv y ≤ (ty bits valid).hi := by
  have positive := Source.two_pow_pos (bits-1)
  have hi := CheckedSigned.hi_eq bits valid
  change (ty bits valid).hi = -(-((2^(bits-1) : Nat) : Int)) - 1 at hi
  change -((2^(bits-1) : Nat) : Int) ≤ x ∧ x ≤ (ty bits valid).hi at hx
  have exactness := Checked.div_int_exact (M := ((2^(bits-1) : Nat) : Int)) (by omega)
    (a := x) (b := y) (by change -((2^(bits-1) : Nat) : Int) ≤ x ∧ x < _; omega) nonzero
  change ¬ (x = -((2^(bits-1) : Nat) : Int) ∧ y = -1) at safe
  change -((2^(bits-1) : Nat) : Int) ≤ x.tdiv y ∧ x.tdiv y ≤ _
  have bounds := exactness.mp safe
  change (ty bits valid).hi = -(-((2^(bits-1) : Nat) : Int)) - 1 at hi
  omega

private theorem wrap_minimum_quotient (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (ty bits valid).wrap (-(ty bits valid).lo) = (ty bits valid).lo := by
  have positive := Source.two_pow_pos (bits-1)
  have double := Source.two_pow_succ_pred (b := bits) (by omega : 1 ≤ bits)
  have hi := CheckedSigned.hi_eq bits valid
  have modulus : ((2^bits : Nat) : Int) = 2 * ((2^(bits-1) : Nat) : Int) := by
    exact_mod_cast double
  rw [SignedWidthCasts.wrap_eq]
  have small : 0 ≤ -(ty bits valid).lo ∧ -(ty bits valid).lo < ((2^bits : Nat) : Int) := by
    change 0 ≤ -(-((2^(bits-1) : Nat) : Int)) ∧ -(-((2^(bits-1) : Nat) : Int)) < _
    omega
  rw [Int.emod_eq_of_lt small.1 small.2]
  change (if -(-((2^(bits-1) : Nat) : Int)) < ((2^(bits-1) : Nat) : Int) then _ else _) = _
  simp only [Int.neg_neg,Int.lt_irrefl,if_false]
  change -(-((2^(bits-1) : Nat) : Int)) - ((2^bits : Nat) : Int) = -((2^(bits-1) : Nat) : Int)
  omega

private theorem result_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (rem : Bool) (x y : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (nonzero : y ≠ 0)
    (safe : rem = false → ¬ (x = (ty bits valid).lo ∧ y = -1)) :
    (ty bits valid).lo ≤ calculate rem x y ∧ calculate rem x y ≤ (ty bits valid).hi := by
  cases rem
  · exact quotient_range bits valid x y hx nonzero (safe rfl)
  · exact remainder_range bits valid x y hy nonzero

private theorem minus_one_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (ty bits valid).lo ≤ -1 ∧ -1 ≤ (ty bits valid).hi := by
  have positive := Source.two_pow_pos (bits-1)
  have zero := integer_zero_range (ty bits valid)
  change -((2^(bits-1) : Nat) : Int) ≤ -1 ∧ -1 ≤ _
  omega

private def minimum {C : Contract} {Γ : Ctx} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) : Val C Γ .int :=
  IntegerConstants.value (ty bits valid) (ty bits valid).lo (CheckedSigned.min_range bits valid)

private def minusOne {C : Contract} {Γ : Ctx} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) : Val C Γ .int :=
  IntegerConstants.value (ty bits valid) (-1) (minus_one_range bits valid)

private def exceptional {C : Contract} {Γ : Ctx} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (a b : Val C Γ .int) : Val C Γ .bool :=
  .ternary (.binop .eqB rfl rfl a (minimum bits valid))
    (.binop .eqB rfl rfl b (minusOne bits valid)) (.simple (.bool false))

/-- The exceptional quotient uses the minimum constant before intrinsic division can overflow. -/
def value {C : Contract} {Γ : Ctx} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (rem : Bool)
    (a b : Val C Γ .int) : Val C Γ .int :=
  if rem then .binop .mod rfl rfl a b else
    .ternary (exceptional bits valid a b) (minimum bits valid) (.binop .div rfl rfl a b)

private theorem exceptional_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (a b : Val C Γ .int) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (left : a.evalT target = .ok (integerValue (ty bits valid) x hx))
    (right : b.evalT target = .ok (integerValue (ty bits valid) y hy)) :
    (exceptional bits valid a b).evalT target = .ok (decide (x = (ty bits valid).lo ∧ y = -1)) := by
  have first := CheckedSigned.eq_run target a (minimum bits valid) _ _ left
    (IntegerConstants.value_run target _ _ _)
  have second := CheckedSigned.eq_run target b (minusOne bits valid) _ _ right
    (IntegerConstants.value_run target _ _ _)
  change (Val.binop .eqB rfl rfl a (minimum bits valid)).evalT target = .ok (decide (x = (ty bits valid).lo)) at first
  change (Val.binop .eqB rfl rfl b (minusOne bits valid)).evalT target = .ok (decide (y = -1)) at second
  change (Val.ternary _ _ _).evalT target = _
  by_cases low : x = (ty bits valid).lo
  · have test : (Val.binop .eqB rfl rfl a (minimum bits valid)).evalT target = .ok true := by
      simpa only [low,decide_true] using first
    rw [CheckedSigned.ternary_true target _ _ _ test]
    simpa only [low,true_and] using second
  · have test : (Val.binop .eqB rfl rfl a (minimum bits valid)).evalT target = .ok false := by
      simpa only [low,decide_false] using first
    rw [CheckedSigned.ternary_false target _ _ _ test]
    simp only [low,false_and,decide_false]
    rfl

private theorem raw_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (rem : Bool)
    (a b : Val C Γ .int) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (nonzero : y ≠ 0)
    (safe : rem = false → ¬ (x = (ty bits valid).lo ∧ y = -1))
    (left : a.evalT target = .ok (integerValue (ty bits valid) x hx))
    (right : b.evalT target = .ok (integerValue (ty bits valid) y hy)) :
    (if rem then Val.binop .mod rfl rfl a b else Val.binop .div rfl rfl a b).evalT target =
      .ok (integerValue (ty bits valid) (calculate rem x y) (result_range bits valid rem x y hx hy nonzero safe)) := by
  have range := integer_range (ty bits valid) (calculate rem x y) (result_range bits valid rem x y hx hy nonzero safe)
  cases rem
  · change PrimTy.int.inRange (x.tdiv y) = true at range
    change (Val.binop .div rfl rfl a b).evalT target = _
    rw [Val.evalT,left]
    change (do let v ← b.evalT target; TRes.ofOpt (BinOp.evalT .div rfl (integerValue (ty bits valid) x hx) v)) = _
    rw [right]
    change TRes.ofOpt ((if y = 0 then none else some (x.tdiv y)).bind PrimTy.int.ofInt?) = _
    simp only [if_neg nonzero,Option.bind_some,PrimTy.ofInt?,dif_pos range]
    rfl
  · change PrimTy.int.inRange (x.tmod y) = true at range
    change (Val.binop .mod rfl rfl a b).evalT target = _
    rw [Val.evalT,left]
    change (do let v ← b.evalT target; TRes.ofOpt (BinOp.evalT .mod rfl (integerValue (ty bits valid) x hx) v)) = _
    rw [right]
    change TRes.ofOpt ((if y = 0 then none else some (x.tmod y)).bind PrimTy.int.ofInt?) = _
    simp only [if_neg nonzero,Option.bind_some,PrimTy.ofInt?,dif_pos range]
    rfl

private theorem value_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (rem : Bool)
    (a b : Val C Γ .int) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) (nonzero : y ≠ 0)
    (left : a.evalT target = .ok (integerValue (ty bits valid) x hx))
    (right : b.evalT target = .ok (integerValue (ty bits valid) y hy)) :
    (value bits valid rem a b).evalT target =
      .ok (integerValue (ty bits valid) ((ty bits valid).wrap (calculate rem x y))
        ((ty bits valid).wrap_mem (calculate rem x y))) := by
  cases rem
  · by_cases bad : x = (ty bits valid).lo ∧ y = -1
    · have test := exceptional_run target bits valid a b x y hx hy left right
      simp only [bad.1,bad.2,true_and,decide_true] at test
      simp only [value,Bool.false_eq_true,if_false]
      rw [CheckedSigned.ternary_true target _ _ _ test]
      have computed := IntegerConstants.value_run target (ty bits valid) (ty bits valid).lo (CheckedSigned.min_range bits valid)
      simpa only [calculate,Solidity.Lowering.V07.UnsignedQuotRem.calculate,Bool.false_eq_true,if_false,bad.1,bad.2,Int.tdiv_neg,Int.tdiv_one,wrap_minimum_quotient] using computed
    · have test := exceptional_run target bits valid a b x y hx hy left right
      simp only [bad,decide_false] at test
      simp only [value,Bool.false_eq_true,if_false]
      rw [CheckedSigned.ternary_false target _ _ _ test]
      have result := raw_run target bits valid false a b x y hx hy nonzero (fun _ => bad) left right
      simpa only [Bool.false_eq_true,if_false,SignedNarrowing.wrap_of_range bits valid _ (result_range bits valid false x y hx hy nonzero (fun _ => bad))] using result
  · have safe : true = false → ¬ (x = (ty bits valid).lo ∧ y = -1) := by intro h; cases h
    have result := raw_run target bits valid true a b x y hx hy nonzero safe left right
    simpa only [value,if_true,SignedNarrowing.wrap_of_range bits valid _ (result_range bits valid true x y hx hy nonzero safe)] using result

private def nonzeroCondition {C : Contract} {Γ : Ctx} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (b : Val C Γ .int) : Val C Γ .bool :=
  .ternary (.binop .eqB rfl rfl b (IntegerConstants.value (ty bits valid) 0 (integer_zero_range _)))
    (.simple (.bool false)) (.simple (.bool true))

private def safeCondition {C : Contract} {Γ : Ctx} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (a b : Val C Γ .int) : Val C Γ .bool :=
  .ternary (exceptional bits valid a b) (.simple (.bool false)) (.simple (.bool true))

/-- Zero is always guarded; only checked quotient guards the minimum divided by minus one. -/
def operand {C : Contract} {Γ : Ctx} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (rem checked : Bool)
    (a b : Idx Γ (.val .int)) : DeferredSource.Operand C Γ (.prim .int) :=
  let x : Val C Γ .int := .simple (.local a)
  let y : Val C Γ .int := .simple (.local b)
  let inner := PanicGuard.checkedOperand .arithmetic (checked && !rem)
    (safeCondition bits valid x y) (value bits valid rem x y)
  ⟨Γ,.cons (PanicGuard.code .divZero (nonzeroCondition bits valid y)) inner.code,inner.value⟩

private theorem tests_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (a b : Val C Γ .int) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (left : a.evalT target = .ok (integerValue (ty bits valid) x hx))
    (right : b.evalT target = .ok (integerValue (ty bits valid) y hy)) :
    (nonzeroCondition bits valid b).evalT target = .ok (decide (y ≠ 0)) ∧
    (safeCondition bits valid a b).evalT target = .ok (decide (¬ (x = (ty bits valid).lo ∧ y = -1))) := by
  have zero := CheckedSigned.eq_run target b (IntegerConstants.value (ty bits valid) 0 (integer_zero_range _)) _ _ right
    (IntegerConstants.value_run target _ _ _)
  change (Val.binop .eqB rfl rfl b (IntegerConstants.value (ty bits valid) 0 (integer_zero_range _))).evalT target = .ok (decide (y = 0)) at zero
  have bad := exceptional_run target bits valid a b x y hx hy left right
  constructor
  · unfold nonzeroCondition
    by_cases iszero : y = 0
    · simp only [iszero,decide_true] at zero
      rw [CheckedSigned.ternary_true target _ _ _ zero]
      simp only [iszero,ne_eq,not_true_eq_false,decide_false]
      rfl
    · simp only [iszero,decide_false] at zero
      rw [CheckedSigned.ternary_false target _ _ _ zero]
      simp only [iszero,ne_eq,not_false_eq_true,decide_true]
      rfl
  · unfold safeCondition
    by_cases special : x = (ty bits valid).lo ∧ y = -1
    · simp only [special.1,special.2,true_and,decide_true] at bad
      rw [CheckedSigned.ternary_true target _ _ _ bad]
      simp only [special,not_true_eq_false,decide_false]
      rfl
    · simp only [special,decide_false] at bad
      rw [CheckedSigned.ternary_false target _ _ _ bad]
      simp only [special,not_false_eq_true,decide_true]
      rfl

private theorem operand_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (rem checked : Bool)
    (a b : Idx Γ (.val .int)) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : TEnv.get a target.env = integerValue (ty bits valid) x hx)
    (readB : TEnv.get b target.env = integerValue (ty bits valid) y hy) :
    (operand bits valid rem checked a b).run target =
      if y = 0 then .error (THalt.ofData (Source.panicData .divZero)) else
      if checked = true ∧ rem = false ∧ x = (ty bits valid).lo ∧ y = -1 then
        .error (THalt.ofData (Source.panicData .arithmetic)) else
        .ok (⟨target,List.prefix_refl _⟩,
          .prim (integerValue (ty bits valid) ((ty bits valid).wrap (calculate rem x y))
            ((ty bits valid).wrap_mem (calculate rem x y)))) := by
  have left : (Val.simple (.local a) : Val C Γ .int).evalT target = .ok (integerValue (ty bits valid) x hx) := congrArg Except.ok readA
  have right : (Val.simple (.local b) : Val C Γ .int).evalT target = .ok (integerValue (ty bits valid) y hy) := congrArg Except.ok readB
  have tests := tests_run target bits valid _ _ x y hx hy left right
  by_cases iszero : y = 0
  · have test : (nonzeroCondition bits valid (.simple (.local b)) : Val C Γ .bool).evalT target = .ok false := by
      simpa only [iszero,ne_eq,not_true_eq_false,decide_false] using tests.1
    have stopped := PanicGuard.run target .divZero _ false test
    simp only [Bool.false_eq_true,if_false] at stopped
    unfold operand DeferredSource.Operand.run
    change (do let out ← (Prog.cons _ _).run target; _) = _
    change (do let out ← TRun.seq (PanicGuard.code .divZero _).runR _ target; _) = _
    simp only [TRun.seq,show (PanicGuard.code .divZero (nonzeroCondition bits valid (.simple (.local b)))).runR target =
      .error (THalt.ofData (Source.panicData .divZero)) from stopped,iszero,if_true]
    rfl
  · have test : (nonzeroCondition bits valid (.simple (.local b)) : Val C Γ .bool).evalT target = .ok true := by
      simpa only [iszero,ne_eq,not_false_eq_true,decide_true] using tests.1
    have passed := PanicGuard.run target .divZero _ true test
    simp only [if_true] at passed
    have computed := value_run target bits valid rem _ _ x y hx hy iszero left right
    have joined := PanicGuard.checkedOperand_run target .arithmetic (checked && !rem)
      (safeCondition bits valid (.simple (.local a)) (.simple (.local b)))
      (value bits valid rem (.simple (.local a)) (.simple (.local b))) _ _ tests.2 computed
    let inner : DeferredSource.Operand C Γ (.prim .int) := PanicGuard.checkedOperand .arithmetic (checked && !rem)
      (safeCondition bits valid (.simple (.local a)) (.simple (.local b)))
      (value bits valid rem (.simple (.local a)) (.simple (.local b)))
    let guard : Stmt C Γ Γ := PanicGuard.code .divZero (nonzeroCondition bits valid (.simple (.local b)))
    have prefixRun : (Prog.cons guard inner.code).run target = inner.code.run target := by
      rw [Prog.run_cons_ok passed]
      generalize inner.code.run target = result
      cases result <;> rfl
    have normalized : (operand bits valid rem checked a b).run target = inner.run target := by
      unfold operand DeferredSource.Operand.run
      change (do let out ← (Prog.cons guard inner.code).run target
                 let v ← inner.value.valueT out.st
                 pure ((⟨out.st.drop (Prog.cons guard inner.code).ext,out.ext⟩ : Out C target.H Γ),v)) = _
      rw [prefixRun,Ext.eq_of_depth (Prog.cons guard inner.code).ext inner.code.ext]
    rw [normalized,joined]
    have failure : ((checked && !rem) = true ∧ decide (¬ (x = (ty bits valid).lo ∧ y = -1)) = false) ↔
        (checked = true ∧ rem = false ∧ x = (ty bits valid).lo ∧ y = -1) := by
      cases checked <;> cases rem <;> simp only [Bool.and_true,Bool.and_false,Bool.not_true,Bool.not_false,
        Bool.false_eq_true,Bool.true_eq_false,false_and,true_and,decide_eq_false_iff_not,Classical.not_not,and_false]
    simp only [failure,iszero,if_false]

private theorem source_value {D : Source.Layout} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (rem checked : Bool) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi) :
    Source.binVal checked (sourceOp rem) (.int x hx : Source.Val D (.int (ty bits valid))) (.int y hy) =
      if y = 0 then .error (.revert (Source.panicData .divZero)) else
      if checked = true ∧ rem = false ∧ x = (ty bits valid).lo ∧ y = -1 then
        .error (.revert (Source.panicData .arithmetic)) else
        .ok (Source.intWrap (ty bits valid) (calculate rem x y)) := by
  have reduces : Source.binVal checked (sourceOp rem) (.int x hx : Source.Val D (.int (ty bits valid))) (.int y hy) =
      if y = 0 then Source.panic .divZero else Source.intRes (ty bits valid) checked (calculate rem x y) := by cases rem <;> rfl
  rw [reduces]
  by_cases iszero : y = 0
  · simp only [iszero,if_true,Source.panic]
  · simp only [iszero,if_false]
    by_cases special : rem = false ∧ x = (ty bits valid).lo ∧ y = -1
    · obtain ⟨rfl,low,rfl⟩ := special
      have hi := CheckedSigned.hi_eq bits valid
      have positive := Source.two_pow_pos (bits-1)
      have overflow : ¬ ((ty bits valid).lo ≤ calculate false x (-1) ∧ calculate false x (-1) ≤ (ty bits valid).hi) := by
        simp only [calculate,Solidity.Lowering.V07.UnsignedQuotRem.calculate,Bool.false_eq_true,if_false,Int.tdiv_neg,Int.tdiv_one,low]
        change ¬ (-((2^(bits-1) : Nat) : Int) ≤ -(-((2^(bits-1) : Nat) : Int)) ∧ -(-((2^(bits-1) : Nat) : Int)) ≤ (ty bits valid).hi)
        change (ty bits valid).hi = -(-((2^(bits-1) : Nat) : Int)) - 1 at hi
        omega
      rw [Source.intRes,dif_neg overflow]
      cases checked <;> simp only [Bool.false_eq_true,if_false,if_true,low,true_and,and_self,false_and]
      all_goals rfl
    · have safe : rem = false → ¬ (x = (ty bits valid).lo ∧ y = -1) := by intro hr hb; exact special ⟨hr,hb⟩
      have bounds := result_range bits valid rem x y hx hy iszero safe
      have wrapped := SignedNarrowing.wrap_of_range bits valid _ bounds
      simp only [Source.intRes,dif_pos bounds,show ¬ (checked = true ∧ rem = false ∧ x = (ty bits valid).lo ∧ y = -1) from by intro h; exact special h.2,if_false,Source.intWrap,wrapped]
      rfl

private theorem source_run {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (rem : Bool)
    (a b : Source.Idx srcΓ (.int (ty bits valid))) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get a = .int x hx) (readB : source.1.get b = .int y hy) :
    (Source.evalE G F (fuel+3) (.binary (sourceOp rem) (.local a) (.local b))).run source =
      if y = 0 then (.error (.revert (Source.panicData .divZero)),source) else
      if F.checked = true ∧ rem = false ∧ x = (ty bits valid).lo ∧ y = -1 then
        (.error (.revert (Source.panicData .arithmetic)),source) else
        (.ok (.val (Source.intWrap (ty bits valid) (calculate rem x y))),source) := by
  have pair := source_local_pair G F fuel source (ty bits valid) a b x y hx hy readA readB
  rw [Source.evalE,Source.withLibraryCalldata_known]
  have nonspecial : (decide (sourceOp rem = .and) || decide (sourceOp rem = .or)) = false := by cases rem <;> rfl
  simp only [nonspecial,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,pair]
  change (do let result ← Source.EM.lift (Source.binVal F.checked (sourceOp rem)
              (.int x hx : Source.Val E.layout (.int (ty bits valid))) (.int y hy))
             pure (Source.RVal.val result)).run source = _
  rw [source_value]
  split
  · rfl
  · split <;> rfl

/-- Both signed operators/modes at every width toward `Solidity.Goals.lowerLoopsCorrect`.
Only initial aligned reads are assumed; zero and minimum divided by -1 are retained. No producer association is asserted. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (rem : Bool)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (a b : ι) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy) :
    if y = 0 then
      (Source.evalE G F (fuel+3) (.binary (sourceOp rem) (.local (si a)) (.local (si b)))).run source =
        (.error (.revert (Source.panicData .divZero)),source) ∧
      (operand bits valid rem F.checked (ti a) (ti b)).run target =
        .error (THalt.ofData (Source.panicData .divZero))
    else if F.checked = true ∧ rem = false ∧ x = (ty bits valid).lo ∧ y = -1 then
      (Source.evalE G F (fuel+3) (.binary (sourceOp rem) (.local (si a)) (.local (si b)))).run source =
        (.error (.revert (Source.panicData .arithmetic)),source) ∧
      (operand bits valid rem F.checked (ti a) (ti b)).run target =
        .error (THalt.ofData (Source.panicData .arithmetic))
    else
      (Source.evalE G F (fuel+3) (.binary (sourceOp rem) (.local (si a)) (.local (si b)))).run source =
        (.ok (.val (Source.intWrap (ty bits valid) (calculate rem x y))),source) ∧
      (operand bits valid rem F.checked (ti a) (ti b)).run target =
        .ok (⟨target,List.prefix_refl _⟩,
          .prim (integerValue (ty bits valid) ((ty bits valid).wrap (calculate rem x y))
            ((ty bits valid).wrap_mem (calculate rem x y)))) ∧
      IntValueRel (ty bits valid)
        (Source.intWrap (ty bits valid) (calculate rem x y) : Source.Val E.layout (.int (ty bits valid)))
        (integerValue (ty bits valid) ((ty bits valid).wrap (calculate rem x y))
          ((ty bits valid).wrap_mem (calculate rem x y))) := by
  have sr := source_run G F fuel source bits valid rem (si a) (si b) x y hx hy readA readB
  have nr := operand_run target bits valid rem F.checked (ti a) (ti b) x y hx hy
    (family.read a x hx readA) (family.read b y hy readB)
  by_cases iszero : y = 0
  · simp only [iszero,if_true] at sr nr ⊢
    exact ⟨sr,nr⟩
  · simp only [iszero,if_false] at sr nr ⊢
    by_cases failed : F.checked = true ∧ rem = false ∧ x = (ty bits valid).lo ∧ y = -1
    · simp only [if_pos failed] at sr nr ⊢
      exact ⟨sr,nr⟩
    · simp only [if_neg failed] at sr nr ⊢
      exact ⟨sr,nr,integer_related _ _ _⟩

private theorem prefix_operand_run {C : Contract} {Γ Δ : Ctx} {T : Ty}
    (target : State C Γ) (steps : Prog C Γ Δ) (reached : State C Δ)
    (heap : List.IsPrefix target.H reached.H)
    (prefixRun : steps.run target = .ok ⟨reached,heap⟩)
    (next : DeferredSource.Operand C Δ T) :
    (⟨next.tailCtx,steps.join next.code,next.value⟩ : DeferredSource.Operand C Γ T).run target =
      (next.run reached).map (fun (out,value) =>
        ((⟨out.st.drop steps.ext,List.IsPrefix.trans heap out.ext⟩ : Out C target.H Γ),value)) := by
  unfold DeferredSource.Operand.run
  rw [DeferredSource.join_run]
  simp only [TRun.seq,show steps.runR target = .ok ⟨reached,heap⟩ from prefixRun]
  rw [Ext.eq_of_depth (steps.join next.code).ext (Ext.trans steps.ext next.code.ext)]
  simp only [Prog.run]
  generalize next.code.runR reached = result
  cases result with
  | error failure => rfl
  | ok out =>
    dsimp only [Except.map,bind,Except.bind]
    generalize next.value.valueT out.st = value
    cases value with
    | error failure => rfl
    | ok value => simp only [State.drop,TEnv.drop_trans]; rfl

/-- Capture assignment/read operands in V07 order before the existing signed guards. -/
def assignmentOperand {C : Contract} {Γ : Ctx} (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (rem checked : Bool)
    (pipeline : Roadmap.Pipeline) (i a : Idx Γ (.val .int)) :
    DeferredSource.Operand C Γ (.prim .int) :=
  let next := operand bits valid rem checked (Γ := .val .int :: .val .int :: Γ) .here (.there .here)
  ⟨next.tailCtx,(assignReadPrefix pipeline i a).join next.code,next.value⟩

private theorem assignment_target_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (rem checked : Bool)
    (pipeline : Roadmap.Pipeline) (i a : Idx Γ (.val .int)) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : TEnv.get a target.env = integerValue (ty bits valid) x hx)
    (readI : TEnv.get i target.env = integerValue (ty bits valid) y hy) :
    (assignmentOperand bits valid rem checked pipeline i a).run target =
      if (if pipeline = .legacy then y else x) = 0 then
        .error (THalt.ofData (Source.panicData .divZero)) else
      if checked = true ∧ rem = false ∧ x = (ty bits valid).lo ∧
          (if pipeline = .legacy then y else x) = -1 then
        .error (THalt.ofData (Source.panicData .arithmetic)) else
        .ok (⟨target.setLocal i (integerValue (ty bits valid) x hx),List.prefix_refl _⟩,
          .prim (integerValue (ty bits valid)
            ((ty bits valid).wrap (calculate rem x (if pipeline = .legacy then y else x)))
            ((ty bits valid).wrap_mem (calculate rem x (if pipeline = .legacy then y else x))))) := by
  let z := if pipeline = .legacy then y else x
  have hz : (ty bits valid).lo ≤ z ∧ z ≤ (ty bits valid).hi := by dsimp only [z]; split <;> assumption
  let caller : State C Γ := target.setLocal i (integerValue (ty bits valid) x hx)
  let reached : State C (.val .int :: .val .int :: Γ) := (caller.push (integerValue (ty bits valid) z hz)).push (integerValue (ty bits valid) x hx)
  have pref : (assignReadPrefix pipeline i a).run target = .ok ⟨reached,List.prefix_refl _⟩ := by
    have actual := assign_read_prefix_run pipeline target i a _ _ readA readI
    cases pipeline <;> simpa only [reached,caller,z,if_true,reduceCtorEq,if_false] using actual
  have tail := operand_run reached bits valid rem checked .here (.there .here) x z hx hz rfl rfl
  have joined := prefix_operand_run target (assignReadPrefix pipeline i a) reached (List.prefix_refl _) pref
    (operand bits valid rem checked .here (.there .here))
  unfold assignmentOperand
  rw [joined,tail]
  change _ = (if z = 0 then .error (THalt.ofData (Source.panicData .divZero)) else
    if checked = true ∧ rem = false ∧ x = (ty bits valid).lo ∧ z = -1 then
      .error (THalt.ofData (Source.panicData .arithmetic)) else
      .ok (⟨caller,List.prefix_refl _⟩,
        .prim (integerValue (ty bits valid) ((ty bits valid).wrap (calculate rem x z))
          ((ty bits valid).wrap_mem (calculate rem x z)))) : TRes (Out C target.H Γ × SVal (.prim .int)))
  by_cases zero : z = 0
  · simp only [if_pos zero]
    rfl
  · simp only [if_neg zero]
    by_cases failed : checked = true ∧ rem = false ∧ x = (ty bits valid).lo ∧ z = -1
    · simp only [if_pos failed]
      rfl
    · simp only [if_neg failed]
      cases pipeline <;> rfl

private theorem assignment_source_run {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (rem : Bool)
    (i a : Source.Idx srcΓ (.int (ty bits valid))) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get a = .int x hx) (readI : source.1.get i = .int y hy) :
    (Source.evalE G F (fuel+4)
      (.binary (sourceOp rem) (.assign (.local i) (.local a)) (.local i))).run source =
      (if (if G.pipeline = .legacy then y else x) = 0 then
        .error (.revert (Source.panicData .divZero)) else
      if F.checked = true ∧ rem = false ∧ x = (ty bits valid).lo ∧
          (if G.pipeline = .legacy then y else x) = -1 then
        .error (.revert (Source.panicData .arithmetic)) else
        .ok (.val (Source.intWrap (ty bits valid) (calculate rem x (if G.pipeline = .legacy then y else x)))),
        (source.1.set i (.int x hx),source.2)) := by
  have pair := source_assign_read_pair G F fuel source i a (.int x hx) (.int y hy) readA readI
  rw [Source.evalE,Source.withLibraryCalldata_known]
  have nonspecial : (decide (sourceOp rem = .and) || decide (sourceOp rem = .or)) = false := by cases rem <;> rfl
  simp only [nonspecial,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,pair]
  by_cases order : G.pipeline = .legacy
  · simp only [if_pos order]
    change (do let result ← Source.EM.lift (Source.binVal F.checked (sourceOp rem)
                (.int x hx : Source.Val E.layout (.int (ty bits valid))) (.int y hy))
               pure (Source.RVal.val result)).run (source.1.set i (.int x hx),source.2) = _
    rw [source_value]
    split
    · rfl
    · split <;> rfl
  · simp only [if_neg order]
    change (do let result ← Source.EM.lift (Source.binVal F.checked (sourceOp rem)
                (.int x hx : Source.Val E.layout (.int (ty bits valid))) (.int x hx))
               pure (Source.RVal.val result)).run (source.1.set i (.int x hx),source.2) = _
    rw [source_value]
    split
    · rfl
    · split <;> rfl

/-- Both signed operators, modes, pipelines and widths with actual operand capture and exact panics;
caller alignment follows operand writes, including Source writes before panic. No rollback or producer association. -/
theorem assignment_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (rem : Bool)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (i a : ι) (x y : Int)
    (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (hy : (ty bits valid).lo ≤ y ∧ y ≤ (ty bits valid).hi)
    (readA : source.1.get (si a) = .int x hx) (readI : source.1.get (si i) = .int y hy) :
    let z := if G.pipeline = .legacy then y else x
    let result := calculate rem x z
    let zero := z = 0
    let overflow := F.checked = true ∧ rem = false ∧ x = (ty bits valid).lo ∧ z = -1
    (Source.evalE G F (fuel+4)
      (.binary (sourceOp rem) (.assign (.local (si i)) (.local (si a))) (.local (si i)))).run source =
      (if zero then .error (.revert (Source.panicData .divZero)) else
        if overflow then .error (.revert (Source.panicData .arithmetic)) else
        .ok (.val (Source.intWrap (ty bits valid) result)),(source.1.set (si i) (.int x hx),source.2)) ∧
    (assignmentOperand bits valid rem F.checked G.pipeline (ti i) (ti a)).run target =
      (if zero then .error (THalt.ofData (Source.panicData .divZero)) else
        if overflow then .error (THalt.ofData (Source.panicData .arithmetic)) else
        .ok (⟨target.setLocal (ti i) (integerValue (ty bits valid) x hx),List.prefix_refl _⟩,
          .prim (integerValue (ty bits valid) ((ty bits valid).wrap result) ((ty bits valid).wrap_mem result)))) ∧
    (¬ zero → ¬ overflow → IntValueRel (ty bits valid)
      (Source.intWrap (ty bits valid) result : Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) ((ty bits valid).wrap result) ((ty bits valid).wrap_mem result))) ∧
    IntegerLocalFamily (ty bits valid) si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue (ty bits valid) x hx) target.env) := by
  have updated := family.write i a
  rw [readA,family.read a x hx readA] at updated
  exact ⟨assignment_source_run G F fuel source bits valid rem (si i) (si a) x y hx hy readA readI,
    assignment_target_run target bits valid rem F.checked G.pipeline (ti i) (ti a) x y hx hy
      (family.read a x hx readA) (family.read i y hy readI),fun _ _ => integer_related _ _ _,updated⟩

end SignedQuotRem

namespace CheckedAssignment

def condition {C : Contract} {Γ : Ctx} (t : Source.IntTy) (op : RingOp)
    (a b : Val C Γ (integerPrim t)) : Val C Γ .bool :=
  match t with
  | ⟨false,bits,valid⟩ => CheckedUnsigned.condition bits valid op a b
  | ⟨true,bits,valid⟩ => CheckedSigned.condition bits valid op a b

private theorem computations {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (op : RingOp) (a b : Val C Γ (integerPrim t)) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (left : a.evalT target = .ok (integerValue t x hx))
    (right : b.evalT target = .ok (integerValue t y hy)) :
    (condition t op a b).evalT target = .ok (decide (t.lo ≤ op.calculate x y ∧ op.calculate x y ≤ t.hi)) ∧
    (wrappingValue t op a b).evalT target =
      .ok (integerValue t (t.wrap (op.calculate x y)) (t.wrap_mem (op.calculate x y))) := by
  obtain ⟨sign,bits,valid⟩ := t
  cases sign with
  | false => exact ⟨CheckedUnsigned.condition_run target bits valid op a b x y hx hy left right,
      CheckedUnsigned.value_run target bits valid op a b x y hx hy left right⟩
  | true => exact ⟨CheckedSigned.condition_run target bits valid op a b x y hx hy left right,
      CheckedSigned.value_run target bits valid op a b x y hx hy left right⟩

/-- The V07 capture prefix followed by the width/sign-specific ring guard and value. -/
def operand {C : Contract} {Γ : Ctx} (t : Source.IntTy) (op : RingOp) (checked : Bool)
    (pipeline : Roadmap.Pipeline) (i a : Idx Γ (.val (integerPrim t))) :
    DeferredSource.Operand C Γ (.prim (integerPrim t)) :=
  PanicGuard.afterPrefix (assignReadPrefix pipeline i a) .arithmetic checked
    (condition t op (.simple (.local .here)) (.simple (.local (.there .here))))
    (wrappingValue t op (.simple (.local .here)) (.simple (.local (.there .here))))

private theorem target_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (op : RingOp) (checked : Bool) (pipeline : Roadmap.Pipeline)
    (i a : Idx Γ (.val (integerPrim t))) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : TEnv.get a target.env = integerValue t x hx)
    (readI : TEnv.get i target.env = integerValue t y hy) :
    (operand t op checked pipeline i a).run target =
      if checked = true ∧ ¬ (t.lo ≤ op.calculate x (if pipeline = .legacy then y else x) ∧
          op.calculate x (if pipeline = .legacy then y else x) ≤ t.hi) then
        .error (THalt.ofData (Source.panicData .arithmetic)) else
        .ok (⟨target.setLocal i (integerValue t x hx),List.prefix_refl _⟩,
          .prim (integerValue t (t.wrap (op.calculate x (if pipeline = .legacy then y else x)))
            (t.wrap_mem (op.calculate x (if pipeline = .legacy then y else x))))) := by
  let z := if pipeline = .legacy then y else x
  have hz : t.lo ≤ z ∧ z ≤ t.hi := by dsimp only [z]; split <;> assumption
  let caller : State C Γ := target.setLocal i (integerValue t x hx)
  let reached : State C (.val (integerPrim t) :: .val (integerPrim t) :: Γ) :=
    (caller.push (integerValue t z hz)).push (integerValue t x hx)
  have pref : (assignReadPrefix pipeline i a).run target = .ok ⟨reached,List.prefix_refl _⟩ := by
    have actual := assign_read_prefix_run pipeline target i a _ _ readA readI
    cases pipeline <;> simpa only [reached,caller,z,if_true,reduceCtorEq,if_false] using actual
  have ready := computations reached t op (.simple (.local .here)) (.simple (.local (.there .here)))
    x z hx hz rfl rfl
  have joined := PanicGuard.afterPrefix_run target (assignReadPrefix pipeline i a) reached
    (List.prefix_refl _) pref .arithmetic checked _ _ _ _ ready.1 ready.2
  unfold operand
  cases pipeline <;> simpa only [z,reached,caller,decide_eq_false_iff_not,
    assignReadPrefix,Prog.ext,Stmt.ext,Ext.trans,State.drop,if_true,reduceCtorEq,if_false] using joined

private theorem source_run {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ)
    (t : Source.IntTy) (op : RingOp) (i a : Source.Idx srcΓ (.int t)) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : source.1.get a = .int x hx) (readI : source.1.get i = .int y hy) :
    (Source.evalE G F (fuel+4) (.binary op.source (.assign (.local i) (.local a)) (.local i))).run source =
      (if F.checked = true ∧ ¬ (t.lo ≤ op.calculate x (if G.pipeline = .legacy then y else x) ∧
          op.calculate x (if G.pipeline = .legacy then y else x) ≤ t.hi) then
        .error (.revert (Source.panicData .arithmetic)) else
        .ok (.val (Source.intWrap t (op.calculate x (if G.pipeline = .legacy then y else x)))),
        (source.1.set i (.int x hx),source.2)) := by
  have pair := source_assign_read_pair G F fuel source i a (.int x hx) (.int y hy) readA readI
  rw [Source.evalE,Source.withLibraryCalldata_known]
  have nonspecial : (decide (op.source = .and) || decide (op.source = .or)) = false := by cases op <;> rfl
  simp only [nonspecial,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,pair]
  by_cases order : G.pipeline = .legacy
  · simp only [if_pos order]
    change (do let result ← Source.EM.lift (Source.binVal F.checked op.source
                (.int x hx : Source.Val E.layout (.int t)) (.int y hy))
               pure (Source.RVal.val result)).run (source.1.set i (.int x hx),source.2) = _
    rw [CheckedSigned.source_value]
    split <;> rfl
  · simp only [if_neg order]
    change (do let result ← Source.EM.lift (Source.binVal F.checked op.source
                (.int x hx : Source.Val E.layout (.int t)) (.int x hx))
               pure (Source.RVal.val result)).run (source.1.set i (.int x hx),source.2) = _
    rw [CheckedSigned.source_value]
    split <;> rfl

/-- Checked/wrapping assignment-read ring arithmetic at every width/sign toward `Solidity.Goals.lowerLoopsCorrect`.
Initial alignment/reads derive capture order, exact panic and the caller relation after operands; no rollback or producer association. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (t : Source.IntTy) (op : RingOp)
    (si : ι → Source.Idx srcΓ (.int t)) (ti : ι → Idx Γ (.val (integerPrim t)))
    (family : IntegerLocalFamily t si ti source.1 target.env) (i a : ι) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (readA : source.1.get (si a) = .int x hx) (readI : source.1.get (si i) = .int y hy) :
    let result := op.calculate x (if G.pipeline = .legacy then y else x)
    let failed := F.checked = true ∧ ¬ (t.lo ≤ result ∧ result ≤ t.hi)
    (Source.evalE G F (fuel+4)
      (.binary op.source (.assign (.local (si i)) (.local (si a))) (.local (si i)))).run source =
      (if failed then .error (.revert (Source.panicData .arithmetic))
        else .ok (.val (Source.intWrap t result)),(source.1.set (si i) (.int x hx),source.2)) ∧
    (operand t op F.checked G.pipeline (ti i) (ti a)).run target =
      (if failed then .error (THalt.ofData (Source.panicData .arithmetic)) else
        .ok (⟨target.setLocal (ti i) (integerValue t x hx),List.prefix_refl _⟩,
          .prim (integerValue t (t.wrap result) (t.wrap_mem result)))) ∧
    (¬ failed → IntValueRel t (Source.intWrap t result : Source.Val E.layout (.int t))
      (integerValue t (t.wrap result) (t.wrap_mem result))) ∧
    IntegerLocalFamily t si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue t x hx) target.env) := by
  have updated := family.write i a
  rw [readA,family.read a x hx readA] at updated
  exact ⟨source_run G F fuel source t op (si i) (si a) x y hx hy readA readI,
    target_run target t op F.checked G.pipeline (ti i) (ti a) x y hx hy
      (family.read a x hx readA) (family.read i y hy readI),fun _ => integer_related _ _ _,updated⟩

end CheckedAssignment

namespace TypedPower

private theorem wrap_congr (t : Source.IntTy) (x y : Int)
    (residue : x % ((2^t.bits : Nat) : Int) = y % ((2^t.bits : Nat) : Int)) :
    t.wrap x = t.wrap y := by
  simp only [Source.IntTy.wrap,Source.wrapBits]
  rw [residue]

private theorem word_then_wrap (t : Source.IntTy) (x : Int) :
    t.wrap (Source.IntTy.u256.wrap x) = t.wrap x := by
  apply wrap_congr
  exact UnsignedNarrowing.word_then_narrow t.bits t.valid.2.2 x

private theorem power_mod (x modulus : Int) (n : Nat) :
    (x % modulus)^n % modulus = x^n % modulus := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((x%modulus)^n * (x%modulus)) % modulus = (x^n*x) % modulus
    rw [Int.mul_emod ((x%modulus)^n) (x%modulus) modulus,
      Int.mul_emod (x^n) x modulus,ih,Int.emod_emod]

private theorem minus_one_power (n : Nat) :
    (-1 : Int)^n = if n%2 = 0 then 1 else -1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases even : n%2 = 0
    · have odd : ¬ (n+1)%2 = 0 := by omega
      simp only [Int.pow_succ,ih,if_pos even,if_neg odd]
      rfl
    · have next : (n+1)%2 = 0 := by omega
      simp only [Int.pow_succ,ih,if_neg even,if_pos next]
      rfl

private theorem unchecked_result {D : Source.Layout} (t : Source.IntTy) (x : Int) :
    Source.intRes (D := D) t false x = .ok (Source.intWrap t x) := by
  unfold Source.intRes
  split
  · rename_i fits
    simp only [Source.intWrap,CheckedSigned.wrap_self t x fits]
    rfl
  · rfl

private theorem source_power {D : Source.Layout} (t : Source.IntTy) (x : Int) (n : Nat)
    (bound : n < 2^300) :
    Source.intPow (D := D) t false x n = .ok (Source.intWrap t (x^n)) := by
  unfold Source.intPow
  split
  · exact unchecked_result t _
  · split
    · rename_i minus
      rw [unchecked_result,minus,minus_one_power]
    · change Except.ok (Source.intWrap t (Source.powMod x n (2^t.bits))) = _
      have residue := (Source.PowerV2.powMod_agrees_v1 x n (2^t.bits) bound).symm.trans
        (Source.PowerV2.powMod_residue x n (2^t.bits))
      have wrapped := wrap_congr t _ _ residue
      simp only [Source.intWrap,wrapped]

private theorem amount_bound (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (y : Int) (hy : (UnsignedNarrowing.ty bits valid).lo ≤ y ∧ y ≤ (UnsignedNarrowing.ty bits valid).hi) :
    y.toNat < 2^300 := by
  have wide := UnsignedWidthCasts.word_range bits valid y hy
  change 0 ≤ y ∧ y ≤ ((2^256-1 : Nat) : Int) at wide
  have positive := Source.two_pow_pos 256
  have bounded : y.toNat < 2^256 := by omega
  exact Nat.lt_trans bounded (Nat.pow_lt_pow_right (by decide) (by decide : 256 < 300))

private def baseWord {C : Contract} {Γ : Ctx} (t : Source.IntTy) :
    Val C Γ (integerPrim t) → Val C Γ .uint :=
  match t with
  | ⟨false,_,_⟩ => fun a => a
  | ⟨true,_,_⟩ => fun a => .unop .toUint rfl rfl a

private theorem base_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (a : Val C Γ (integerPrim t)) (x : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (read : a.evalT target = .ok (integerValue t x hx)) :
    (baseWord t a).evalT target = .ok (integerValue .u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x)) := by
  obtain ⟨sign,bits,valid⟩ := t
  cases sign with
  | false =>
    have wide := UnsignedWidthCasts.word_range bits valid x hx
    have wrapped : Source.IntTy.u256.wrap x = x := UnsignedNarrowing.wrap_of_range 256 (by decide) x wide
    change a.evalT target = _
    rw [read]
    apply congrArg Except.ok
    apply Subtype.ext
    exact wrapped.symm
  | true => exact WordCasts.to_uint_run target a x (SignedWidthCasts.word_range bits valid x hx) read

private def restore {C : Contract} {Γ : Ctx} (t : Source.IntTy) (a : Val C Γ .uint) : Val C Γ (integerPrim t) :=
  match t with
  | ⟨false,bits,_⟩ => UnsignedCasts.castValue bits a
  | ⟨true,bits,_⟩ => SignedWidthCasts.castValue bits (.unop .toInt rfl rfl a)

private theorem restore_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (a : Val C Γ .uint) (x : Int)
    (read : a.evalT target = .ok (integerValue .u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x))) :
    (restore t a).evalT target = .ok (integerValue t (t.wrap x) (t.wrap_mem x)) := by
  obtain ⟨sign,bits,valid⟩ := t
  cases sign with
  | false =>
    have narrowed := UnsignedCasts.value_run target bits valid a _ (Source.IntTy.u256.wrap_mem x) read
    simpa only [restore,word_then_wrap] using narrowed
  | true =>
    have signed := WordCasts.to_int_run target a _ (Source.IntTy.u256.wrap_mem x) read
    have narrowed := SignedWidthCasts.value_run 256 (by decide) target bits valid _ _
      (WordCasts.signed.wrap_mem (Source.IntTy.u256.wrap x)) signed
    simpa only [restore,SignedNarrowing.wrap_word,word_then_wrap] using narrowed

private theorem word_eval (x y : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (hy : Source.IntTy.u256.lo ≤ y ∧ y ≤ Source.IntTy.u256.hi) :
    BinOp.evalT .powW rfl (integerValue .u256 x hx) (integerValue .u256 y hy) =
      some (integerValue .u256 (Source.IntTy.u256.wrap (x^y.toNat)) (Source.IntTy.u256.wrap_mem (x^y.toNat))) := by
  have hr := integer_range Source.IntTy.u256 (Source.IntTy.u256.wrap (x^y.toNat)) (Source.IntTy.u256.wrap_mem (x^y.toNat))
  change PrimTy.uint.inRange (x^y.toNat % Semantics.uintBound) = true at hr
  change (BinOp.arithInt .powW x y).bind PrimTy.uint.ofInt? = some ⟨x^y.toNat % Semantics.uintBound,hr⟩
  have nonnegative : ¬ y < 0 := by change 0 ≤ y ∧ y ≤ _ at hy; omega
  simp only [BinOp.arithInt,if_neg nonnegative,Option.bind_some,PrimTy.ofInt?,dif_pos hr]

/-- V07 width/sign restoration after native word power; exponent has its own unsigned type. -/
def value {C : Contract} {Γ : Ctx} (t : Source.IntTy)
    (a : Val C Γ (integerPrim t)) (b : Val C Γ .uint) : Val C Γ (integerPrim t) :=
  restore t (.binop .powW rfl rfl (baseWord t a) b)

private theorem value_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (a : Val C Γ (integerPrim t)) (b : Val C Γ .uint) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (hy : (UnsignedNarrowing.ty bits valid).lo ≤ y ∧ y ≤ (UnsignedNarrowing.ty bits valid).hi)
    (left : a.evalT target = .ok (integerValue t x hx))
    (right : b.evalT target = .ok (integerValue (UnsignedNarrowing.ty bits valid) y hy)) :
    (value t a b).evalT target =
      .ok (integerValue t (t.wrap (x^y.toNat)) (t.wrap_mem (x^y.toNat))) := by
  have wide := UnsignedWidthCasts.word_range bits valid y hy
  have casted := base_run target t a x hx left
  have raw : (Val.binop .powW rfl rfl (baseWord t a) b).evalT target =
      .ok (integerValue .u256 (Source.IntTy.u256.wrap ((Source.IntTy.u256.wrap x)^y.toNat))
        (Source.IntTy.u256.wrap_mem ((Source.IntTy.u256.wrap x)^y.toNat))) := by
    rw [Val.evalT,casted]
    change (do let z ← b.evalT target
               TRes.ofOpt (BinOp.evalT .powW rfl (integerValue .u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x)) z)) = _
    rw [right]
    change TRes.ofOpt (BinOp.evalT .powW rfl (integerValue .u256 (Source.IntTy.u256.wrap x) (Source.IntTy.u256.wrap_mem x))
      (integerValue .u256 y wide)) = _
    rw [word_eval]
    rfl
  have canonical : Source.IntTy.u256.wrap ((Source.IntTy.u256.wrap x)^y.toNat) = Source.IntTy.u256.wrap (x^y.toNat) :=
    power_mod x Semantics.uintBound y.toNat
  have normalized : (Val.binop .powW rfl rfl (baseWord t a) b).evalT target =
      .ok (integerValue .u256 (Source.IntTy.u256.wrap (x^y.toNat)) (Source.IntTy.u256.wrap_mem (x^y.toNat))) := by
    simpa only [canonical] using raw
  exact restore_run target t _ _ normalized

private theorem source_run {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ)
    (t : Source.IntTy) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (a : Source.Idx srcΓ (.int t)) (b : Source.Idx srcΓ (.int (UnsignedNarrowing.ty bits valid)))
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (hy : (UnsignedNarrowing.ty bits valid).lo ≤ y ∧ y ≤ (UnsignedNarrowing.ty bits valid).hi)
    (left : source.1.get a = .int x hx) (right : source.1.get b = .int y hy) :
    (Source.evalE G {F with checked := false} (fuel+3)
      (.shiftLike .exp (.local a) (.local b) rfl)).run source =
      (.ok (.val (Source.intWrap t (x^y.toNat))),source) := by
  have leftRun : (Source.evalE G {F with checked := false} (fuel+1) (.local a)).run source =
      (.ok (.val (.int x hx)),source) := by
    change (Except.ok (Source.RVal.val (source.1.get a)),source) = _
    rw [left]
  have rightRun : (Source.evalE G {F with checked := false} (fuel+1) (.local b)).run source =
      (.ok (.val (.int y hy)),source) := by
    change (Except.ok (Source.RVal.val (source.1.get b)),source) = _
    rw [right]
  have pair := source_pure_pair G {F with checked := false} (fuel+1) source (.local a) (.local b)
    (.val (.int x hx)) (.val (.int y hy)) leftRun rightRun
  rw [Source.evalE,Source.Hoare.run_bind,pair]
  change (do let result ← Source.EM.lift (Source.intPow t false x y.toNat)
             pure (Source.RVal.val result)).run source = _
  rw [source_power t x y.toNat (amount_bound bits valid y hy)]
  rfl

/-- Every base width/sign and typed unsigned exponent width, using V1 evaluation and V07 casts.
The cutoff bound is derived; checked power, constants, effects and producer association remain separate. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (t : Source.IntTy) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (a : Source.Idx srcΓ (.int t)) (b : Source.Idx srcΓ (.int (UnsignedNarrowing.ty bits valid)))
    (c : Idx Γ (.val (integerPrim t))) (d : Idx Γ (.val .uint))
    (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (hy : (UnsignedNarrowing.ty bits valid).lo ≤ y ∧ y ≤ (UnsignedNarrowing.ty bits valid).hi)
    (readA : source.1.get a = .int x hx) (readB : source.1.get b = .int y hy)
    (nativeA : TEnv.get c target.env = integerValue t x hx)
    (nativeB : TEnv.get d target.env = integerValue (UnsignedNarrowing.ty bits valid) y hy) :
    (Source.evalE G {F with checked := false} (fuel+3)
      (.shiftLike .exp (.local a) (.local b) rfl)).run source =
      (.ok (.val (Source.intWrap t (x^y.toNat))),source) ∧
    (value t (.simple (.local c)) (.simple (.local d))).evalT target =
      .ok (integerValue t (t.wrap (x^y.toNat)) (t.wrap_mem (x^y.toNat))) ∧
    IntValueRel t (Source.intWrap t (x^y.toNat) : Source.Val E.layout (.int t))
      (integerValue t (t.wrap (x^y.toNat)) (t.wrap_mem (x^y.toNat))) := by
  exact ⟨source_run G F fuel source t bits valid a b x y hx hy readA readB,
    value_run target t bits valid _ _ x y hx hy (congrArg Except.ok nativeA) (congrArg Except.ok nativeB),
    integer_related _ _ _⟩

end TypedPower

end Solidity.Lowering.G16.Arithmetic

/-- info: 'Solidity.Lowering.G16.Arithmetic.wrapping_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Arithmetic.wrapping_transport

/-- info: 'Solidity.Lowering.G16.Arithmetic.wrapping_assignment_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Arithmetic.wrapping_assignment_transport

/-- info: 'Solidity.Lowering.G16.Arithmetic.CheckedUnsigned.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Arithmetic.CheckedUnsigned.transport

/-- info: 'Solidity.Lowering.G16.Arithmetic.CheckedSigned.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Arithmetic.CheckedSigned.transport

/-- info: 'Solidity.Lowering.G16.Arithmetic.SignedQuotRem.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Arithmetic.SignedQuotRem.transport

/-- info: 'Solidity.Lowering.G16.Arithmetic.CheckedAssignment.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Arithmetic.CheckedAssignment.transport

/-- info: 'Solidity.Lowering.G16.Arithmetic.SignedQuotRem.assignment_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Arithmetic.SignedQuotRem.assignment_transport

/-- info: 'Solidity.Lowering.G16.Arithmetic.TypedPower.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Arithmetic.TypedPower.transport

namespace Solidity.Lowering.G16.Arithmetic.Modular
open Solidity.Lowering.V07
private theorem source_range (x : PrimTy.uint.Denote) :
    Source.IntTy.u256.lo ≤ x.val ∧ x.val ≤ Source.IntTy.u256.hi := by
  have h := of_decide_eq_true x.property
  change 0 ≤ x.val ∧ x.val < ((2^256 : Nat) : Int) at h
  change 0 ≤ x.val ∧ x.val ≤ (((2^256 : Nat) : Int)-1)
  omega
def sourceValue {D : Source.Layout} (x : PrimTy.uint.Denote) : Source.Val D (.int Source.IntTy.u256) :=
  .int x.val (source_range x)
private def sourceOp : ModOp → Source.Builtin
  | .addmod => .addmod | .mulmod => .mulmod
def sourceExpr {E : Source.Env} {Γ : Source.RCtx} (op : ModOp)
    (i j k : Source.Idx Γ (.int Source.IntTy.u256)) : Source.RExpr E Γ (.int Source.IntTy.u256) :=
  .builtin (sourceOp op) (.cons (.local i) (.cons (.local j) (.cons (.local k) .nil)))
    (by cases op <;> rfl)

private theorem args_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (s : Source.EMState E Γ)
    (i j k : Source.Idx Γ (.int Source.IntTy.u256)) (x y m : PrimTy.uint.Denote)
    (hx : s.1.get i = sourceValue x)
    (hy : s.1.get j = sourceValue y)
    (hm : s.1.get k = sourceValue m) :
    let args : Source.RArgs E Γ [.int Source.IntTy.u256,.int Source.IntTy.u256,.int Source.IntTy.u256] :=
      .cons (.local i) (.cons (.local j) (.cons (.local k) .nil))
    let vals : Source.RVals E.layout [.int Source.IntTy.u256,.int Source.IntTy.u256,.int Source.IntTy.u256] :=
      .cons (.val (sourceValue x))
        (.cons (.val (sourceValue y)) (.cons (.val (sourceValue m)) .nil))
    (Source.evalArgs G F (fuel+4) args).run s = (.ok vals,s) ∧
    (Source.evalArgsRev G F (fuel+4) args).run s = (.ok vals,s) := by
  have hi (n : Nat) : (Source.evalE G F (n+1) (.local i)).run s =
      (.ok (.val (sourceValue x)),s) := by
    change (Except.ok (Source.RVal.val (s.1.get i)),s) = _
    rw [hx]
  have hj (n : Nat) : (Source.evalE G F (n+1) (.local j)).run s =
      (.ok (.val (sourceValue y)),s) := by
    change (Except.ok (Source.RVal.val (s.1.get j)),s) = _
    rw [hy]
  have hk (n : Nat) : (Source.evalE G F (n+1) (.local k)).run s =
      (.ok (.val (sourceValue m)),s) := by
    change (Except.ok (Source.RVal.val (s.1.get k)),s) = _
    rw [hm]
  have hpure {α : Type} (a : α) : (pure a : Source.EM E Γ α).run s = (.ok a,s) := rfl
  constructor
  · simp only [Source.evalArgs,Source.Hoare.run_bind,hpure,hi,hj,hk]
  · simp only [Source.evalArgsRev,Source.Hoare.run_bind,hpure,hi,hj,hk]

private theorem source_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (s : Source.EMState E Γ)
    (op : ModOp) (i j k : Source.Idx Γ (.int Source.IntTy.u256))
    (x y m : PrimTy.uint.Denote)
    (hx : s.1.get i = sourceValue x)
    (hy : s.1.get j = sourceValue y)
    (hm : s.1.get k = sourceValue m) :
    (Source.evalE G F (fuel+6) (sourceExpr op i j k)).run s =
      (if m.val = 0 then .error (.revert (Source.panicData .divZero))
       else .ok (.val (Source.intWrap Source.IntTy.u256 (op.wide x.val y.val % m.val))),s) := by
  have args := args_run G F fuel s i j k x y m hx hy hm
  cases op <;> cases hp : G.pipeline
  all_goals
    unfold sourceExpr
    rw [Source.evalE,Source.evalBuiltin]
    simp only [sourceOp,hp,Bool.true_or,Bool.false_or,Bool.and_true,
      Bool.and_false,reduceCtorEq,decide_true,decide_false,Bool.false_eq_true,if_true,if_false]
    rw [Source.Hoare.run_bind]
    first | rw [args.1] | rw [args.2]
    dsimp only
    change ((if m.val = 0 then Source.EM.lift (Source.panic .divZero)
      else pure (.val (Source.intWrap Source.IntTy.u256 (_ % m.val)))) :
        Source.EM E Γ (Source.RVal E.layout (.int Source.IntTy.u256))).run s = _
    by_cases zero : m.val = 0
    · simp only [if_pos zero]
      rfl
    · simp only [if_neg zero]
      rfl

private def value {C : Contract} {Γ : Ctx} (op : ModOp) (i j k : Idx Γ (.val .uint)) : Val C Γ .uint :=
  .modular op (.simple (.local i)) (.simple (.local j)) (.simple (.local k))
private def condition {C : Contract} {Γ : Ctx} (k : Idx Γ (.val .uint)) : Val C Γ .bool :=
  .binop .neB rfl rfl (.simple (.local k)) (Checked.litU 0 (by decide))
def result (op : ModOp) (x y m : PrimTy.uint.Denote) : PrimTy.uint.Denote :=
  integerValue Source.IntTy.u256
    (Source.IntTy.u256.wrap (op.wide x.val y.val % m.val))
    (Source.IntTy.u256.wrap_mem _)
private theorem remainder_range (op : ModOp) (x y m : PrimTy.uint.Denote) (hn : m.val ≠ 0) :
    Source.IntTy.u256.lo ≤ op.wide x.val y.val % m.val ∧
      op.wide x.val y.val % m.val ≤ Source.IntTy.u256.hi := by
  have hm := source_range m
  have lowm : 0 ≤ m.val := hm.1
  have positive : 0 < m.val := by omega
  have low := Int.emod_nonneg (op.wide x.val y.val) hn
  have high := Int.emod_lt_of_pos (op.wide x.val y.val) positive
  exact ⟨low,by omega⟩
private theorem value_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (op : ModOp) (i j k : Idx Γ (.val .uint)) (x y m : PrimTy.uint.Denote)
    (hx : TEnv.get i target.env = x) (hy : TEnv.get j target.env = y)
    (hm : TEnv.get k target.env = m) (hn : m.val ≠ 0) :
    (value op i j k).evalT target = .ok (result op x y m) := by
  have hr := integer_range Source.IntTy.u256 (op.wide x.val y.val % m.val) (remainder_range op x y m hn)
  change PrimTy.uint.inRange (op.wide x.val y.val % m.val) = true at hr
  have wrapped := UnsignedNarrowing.wrap_of_range 256 (by decide)
    (op.wide x.val y.val % m.val) (remainder_range op x y m hn)
  change Source.IntTy.u256.wrap (op.wide x.val y.val % m.val) = _ at wrapped
  change (do
    let a ← (Except.ok (TEnv.get i target.env) : TRes PrimTy.uint.Denote)
    let b ← (Except.ok (TEnv.get j target.env) : TRes PrimTy.uint.Denote)
    let c ← (Except.ok (TEnv.get k target.env) : TRes PrimTy.uint.Denote)
    TRes.ofOpt (op.evalT a b c)) = _
  rw [hx,hy,hm]
  simp only [ok_bind,ModOp.evalT,if_neg hn,PrimTy.ofInt?,dif_pos hr,TRes.ofOpt]
  apply congrArg Except.ok
  apply Subtype.ext
  exact wrapped.symm
private theorem condition_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (k : Idx Γ (.val .uint)) (m : PrimTy.uint.Denote) (hm : TEnv.get k target.env = m) :
    (condition k).evalT target = .ok (!decide (m.val = 0)) := by
  change (TRes.ofOpt (BinOp.evalT .neB rfl (TEnv.get k target.env)
    (⟨0,by decide⟩ : PrimTy.uint.Denote))) = _
  rw [hm]
  rfl

def operand {C : Contract} {Γ : Ctx} (op : ModOp) (i j k : Idx Γ (.val .uint)) :
    DeferredSource.Operand C Γ (.prim .uint) :=
  PanicGuard.checkedOperand .divZero true (condition k) (value op i j k)
private theorem operand_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (op : ModOp) (i j k : Idx Γ (.val .uint)) (x y m : PrimTy.uint.Denote)
    (hx : TEnv.get i target.env = x) (hy : TEnv.get j target.env = y)
    (hm : TEnv.get k target.env = m) :
    (operand op i j k).run target =
      if m.val = 0 then .error (THalt.ofData (Source.panicData .divZero))
      else .ok (⟨target,List.prefix_refl _⟩,.prim (result op x y m)) := by
  have test := condition_run target k m hm
  by_cases zero : m.val = 0
  · rw [if_pos zero]
    have tested : (condition k).evalT target = .ok false := by
      simpa only [zero,decide_true,Bool.not_true] using test
    have failed := PanicGuard.run target .divZero (condition k) false tested
    simp only [Bool.false_eq_true,if_false] at failed
    have stopped : (Prog.cons (PanicGuard.code .divZero (condition k)) .nil).run target =
        .error (THalt.ofData (Source.panicData .divZero)) := by
      change TRun.seq (PanicGuard.code .divZero (condition k)).runR _ target = _
      simp only [TRun.seq,show (PanicGuard.code .divZero (condition k)).runR target =
        .error (THalt.ofData (Source.panicData .divZero)) from failed]
    unfold operand PanicGuard.checkedOperand DeferredSource.Operand.run
    simp only [if_true]
    rw [stopped]
    rfl
  · rw [if_neg zero]
    have tested : (condition k).evalT target = .ok true := by
      simpa only [show decide (m.val = 0) = false from decide_eq_false zero,Bool.not_false] using test
    have computed := value_run target op i j k x y m hx hy hm zero
    have ran := PanicGuard.checkedOperand_run target .divZero true (condition k) (value op i j k)
      true (result op x y m) tested computed
    simpa only [Bool.true_eq_false,and_false,if_false] using ran

/-- Both modular builtins on uint256 locals: unbounded intermediates and exact zero-modulus panic in either mode/pipeline. Successful callers are unchanged; no frontend or effectful-operand association. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ)
    (target : State C Γ) (op : ModOp)
    (i j k : Source.Idx srcΓ (.int Source.IntTy.u256)) (a b c : Idx Γ (.val .uint))
    (x y m : PrimTy.uint.Denote)
    (readX : source.1.get i = sourceValue x) (readY : source.1.get j = sourceValue y)
    (readM : source.1.get k = sourceValue m)
    (nativeX : TEnv.get a target.env = x) (nativeY : TEnv.get b target.env = y)
    (nativeM : TEnv.get c target.env = m) :
    (Source.evalE G F (fuel+6) (sourceExpr op i j k)).run source =
      (if m.val = 0 then .error (.revert (Source.panicData .divZero))
       else .ok (.val (Source.intWrap Source.IntTy.u256 (op.wide x.val y.val % m.val))),source) ∧
    (operand op a b c).run target =
      if m.val = 0 then .error (THalt.ofData (Source.panicData .divZero))
      else .ok (⟨target,List.prefix_refl _⟩,.prim (result op x y m)) := by
  exact ⟨source_run G F fuel source op i j k x y m readX readY readM,
    operand_run target op a b c x y m nativeX nativeY nativeM⟩
end Solidity.Lowering.G16.Arithmetic.Modular

/-- info: 'Solidity.Lowering.G16.Arithmetic.Modular.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Arithmetic.Modular.transport
