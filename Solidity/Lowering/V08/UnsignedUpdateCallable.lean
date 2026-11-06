import Solidity.Lowering.V08.IntegerCallable
import Solidity.Lowering.V07.UnsignedLocalUpdate

/-! Unsigned local updates as actual selected Source call arguments. Prefix
returns the new value; postfix returns the captured old value. Both retain the
updated caller local and the entire Source machine. The independently derived
intrinsic argument operand is not a compiled callee or runtime-frame theorem. -/
namespace Solidity.Lowering.V08.UnsignedUpdateCallable
open Solidity Source
open Solidity.Lowering.V07
open UnsignedLocalUpdate
open UnsignedNarrowing (ty)
variable {E : Source.Env} {Γ : Source.RCtx}

def arguments (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (inc pre : Bool) (i : Source.Idx Γ (.int (UnsignedNarrowing.ty bits valid))) :
    Source.RConvArgs E Γ [.int (UnsignedNarrowing.ty bits valid)] :=
  .cons (.incDec inc pre (.local i))
    (IntegerCallable.implicit_identity _) .nil

theorem argument_actual (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (g : Source.Glob E) (f : Source.Fr) (extra : Nat) (source : Source.EMState E Γ)
    (inc pre : Bool) (i : Source.Idx Γ (.int (UnsignedNarrowing.ty bits valid)))
    (x : Int) (hx : (UnsignedNarrowing.ty bits valid).lo ≤ x ∧ x ≤ (UnsignedNarrowing.ty bits valid).hi)
    (read : source.1.get i = .int x hx) :
    (Source.evalConvArgs g {f with checked := false} (extra+16)
      (arguments bits valid inc pre i)).run source =
      (.ok (.cons (if pre then Source.intWrap (UnsignedNarrowing.ty bits valid) (changed inc x)
        else .int x hx) .nil),
       (source.1.set i (Source.intWrap (UnsignedNarrowing.ty bits valid) (changed inc x)),source.2)) := by
  first
  | simp only [arguments,Source.evalConvArgs,IntegerCallable.conversion_identity,
      Source.Hoare.run_bind,UnsignedLocalUpdate.source_run bits valid g f (extra+13)
        source inc pre i x hx read]; rfl
  | decide
  | omega
  | rfl

/-- No execution/preservation premise: selected body syntax and initial reads
produce the actual argument, local subframe execution and restored caller locals. -/
theorem source_expression (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (g : Source.Glob E) (f : Source.Fr) (decl : Source.Decl)
    (selected : IntegerCallable.Inputs g {f with checked := false} decl (UnsignedNarrowing.ty bits valid))
    (extra : Nat) (source : Source.EMState E Γ) (inc pre : Bool)
    (i : Source.Idx Γ (.int (UnsignedNarrowing.ty bits valid)))
    (x : Int) (hx : (UnsignedNarrowing.ty bits valid).lo ≤ x ∧ x ≤ (UnsignedNarrowing.ty bits valid).hi)
    (read : source.1.get i = .int x hx) :
    (Source.evalE g {f with checked := false} (extra+17)
      (.call decl selected.signature (arguments bits valid inc pre i))).run source =
      (.ok (.val (if pre then Source.intWrap (UnsignedNarrowing.ty bits valid) (changed inc x)
        else .int x hx)),
       (source.1.set i (Source.intWrap (UnsignedNarrowing.ty bits valid) (changed inc x)),source.2)) := by
  cases pre
  · exact SourceCallable.expression_complete g {f with checked := false} (extra+16)
      decl selected.signature (arguments bits valid inc false i) source.1
      (source.1.set i (Source.intWrap (UnsignedNarrowing.ty bits valid) (changed inc x)))
      (.cons (.int x hx) .nil) (.val (.int x hx)) source.2 source.2 source.2
      (argument_actual bits valid g f extra source inc false i x hx read)
      (IntegerCallable.source_call g {f with checked := false} decl _ selected (extra+4) source.2 x hx)
  · exact SourceCallable.expression_complete g {f with checked := false} (extra+16)
      decl selected.signature (arguments bits valid inc true i) source.1
      (source.1.set i (Source.intWrap (UnsignedNarrowing.ty bits valid) (changed inc x)))
      (.cons (Source.intWrap (UnsignedNarrowing.ty bits valid) (changed inc x)) .nil)
      (.val (Source.intWrap (UnsignedNarrowing.ty bits valid) (changed inc x))) source.2 source.2 source.2
      (argument_actual bits valid g f extra source inc true i x hx read)
      (IntegerCallable.source_call g {f with checked := false} decl _ selected (extra+4)
        source.2 _ ((UnsignedNarrowing.ty bits valid).wrap_mem (changed inc x)))

theorem transport_context (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (decl : Source.Decl)
    (selected : IntegerCallable.Inputs G {F with checked := false} decl (ty bits valid)) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (inc pre : Bool)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (i : ι) (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : source.1.get (si i) = .int x hx) :
    (Source.evalE G {F with checked := false} (fuel+17) (.call decl selected.signature (arguments bits valid inc pre (si i)))).run source =
      (.ok (.val (if pre then Source.intWrap (ty bits valid) (changed inc x) else .int x hx)),
        (source.1.set (si i) (Source.intWrap (ty bits valid) (changed inc x)),source.2)) ∧
    (operand bits inc pre (ti i)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue (ty bits valid) ((ty bits valid).wrap (changed inc x))
        ((ty bits valid).wrap_mem (changed inc x))),List.prefix_refl _⟩,
        .prim (if pre then integerValue (ty bits valid) ((ty bits valid).wrap (changed inc x))
          ((ty bits valid).wrap_mem (changed inc x)) else integerValue (ty bits valid) x hx)) ∧
    IntValueRel (ty bits valid)
      ((if pre then Source.intWrap (ty bits valid) (changed inc x) else .int x hx) : Source.Val E.layout (.int (ty bits valid)))
      (if pre then integerValue (ty bits valid) ((ty bits valid).wrap (changed inc x))
        ((ty bits valid).wrap_mem (changed inc x)) else integerValue (ty bits valid) x hx) ∧
    IntegerLocalFamily (ty bits valid) si ti
      (source.1.set (si i) (Source.intWrap (ty bits valid) (changed inc x)))
      (TEnv.set (ti i) (integerValue (ty bits valid) ((ty bits valid).wrap (changed inc x))
        ((ty bits valid).wrap_mem (changed inc x))) target.env) := by
  have argument := UnsignedLocalUpdate.transport bits valid G F fuel source target inc pre si ti family i x hx read
  exact ⟨source_expression bits valid G F decl selected fuel source inc pre (si i) x hx read,argument.2⟩

end Solidity.Lowering.V08.UnsignedUpdateCallable

/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.arguments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.arguments
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.argument_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.argument_actual
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.source_expression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.source_expression
/-- info: 'Solidity.Lowering.V08.UnsignedUpdateCallable.transport_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.UnsignedUpdateCallable.transport_context
