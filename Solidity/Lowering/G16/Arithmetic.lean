import Solidity.Lowering.V07.UnsignedAddition
import Solidity.Lowering.V07.UnsignedMultiplication
import Solidity.Lowering.V07.SignedNarrowAddition
import Solidity.Lowering.V07.SignedNarrowSubtraction
import Solidity.Lowering.V07.SignedNarrowMultiplication

/-! Scalar arithmetic families built from the published V07 operational leaves.
This module starts with wrapping addition, subtraction and multiplication at
all valid widths and signs. Checked arithmetic and quotient/remainder remain
separate obligations; no frontend selection or admission theorem is asserted. -/
namespace Solidity.Lowering.G16.Arithmetic
open Solidity.Lowering.V07

inductive RingOp where
  | add | sub | mul
  deriving DecidableEq, Repr

def RingOp.source : RingOp → Source.BinOp
  | .add => .add | .sub => .sub | .mul => .mul

def RingOp.calculate : RingOp → Int → Int → Int
  | .add => (· + ·) | .sub => (· - ·) | .mul => (· * ·)

/-- Reuse V07's actual word arithmetic and width-restoring value programs. -/
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

/-- One statement covers all three ring operations, every valid width, and
both signs. The premises are initial local observations, never desired runs.
The source is explicitly evaluated in an unchecked frame. -/
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


/-- Select the published V07 assignment/read operand without rebuilding its
capture prefix or changing its pipeline order. -/
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

/-- A single ring-family clause includes the actual pipeline-sensitive
assignment/read pair, all valid widths/signs, and the derived caller update.
Only initial alignment and reads are premises. This operational leaf does not
supply frontend selection or the held validator association. -/
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

end Solidity.Lowering.G16.Arithmetic

/-- info: 'Solidity.Lowering.G16.Arithmetic.wrapping_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Arithmetic.wrapping_transport

/-- info: 'Solidity.Lowering.G16.Arithmetic.wrapping_assignment_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Arithmetic.wrapping_assignment_transport
