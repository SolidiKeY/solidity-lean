import Solidity.Lowering.V07.IntegerConstants
import Solidity.Lowering.G16.PanicGuard
import Solidity.Syntax.CheckedExact
import Solidity.Lowering.V07.UnsignedAddition
import Solidity.Lowering.V07.UnsignedMultiplication
import Solidity.Lowering.V07.SignedNarrowAddition
import Solidity.Lowering.V07.SignedNarrowSubtraction
import Solidity.Lowering.V07.SignedNarrowMultiplication

/-! V07 ring clauses: checked/wrapping +, -, * at all widths/signs.
Quotient/remainder and whole-family composition remain separate obligations; no frontend selection or admission claim. -/
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

/-- All three ring operations, widths and signs in an explicit unchecked Source frame.
Premises observe initial locals, never desired runs. -/
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

/-- Pipeline-sensitive assignment/read at all widths/signs, with derived caller update.
Only initial alignment/reads are assumed; no frontend selection or held validator association. -/
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

/-- Guard the existing unsigned ring program toward `Solidity.Goals.lowerLoopsCorrect`.
No replacement of the held validator/scalar endpoint or frontend producer is asserted. -/
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

/-- All unsigned widths, three operators and both modes: success or arithmetic panic.
Premises observe initial aligned locals, with no overflow exclusion or desired run.
The final wrapped-value law does not assert observed success on failure. -/
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

/-- Signed local ring arithmetic at every width and in both modes toward `Solidity.Goals.lowerLoopsCorrect`.
Initial reads/alignment suffice; overflow, zero and minimum inputs are not excluded. No producer association is asserted. -/
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
