import Solidity.Lowering.V08.IntegerCallable
import Solidity.Lowering.V07.FixedBytesAssignment

/-! Kernel-checked argument-phase component: actual fixed-bytes converted argument execution
and reached caller-local alignment. No selected callee execution, compiler
selection, ABI encoding, Source admission or runtime-frame adequacy is claimed.
The source argument uses the published evaluator and assignment, not a supplied
execution/preservation equality. Exact observed standard axiom footprints are guarded below. -/
namespace Solidity.Lowering.V08.FixedBytesCallableArgument
open Solidity Source
open Solidity.Lowering.V07
open FixedBytesAssignment (Rel value)
variable {E : Source.Env} {srcΓ : Source.RCtx}

def arguments (n : Nat) (width : 1 ≤ n ∧ n ≤ 32)
    (i r : Source.Idx srcΓ (.fixedBytes n width)) :
    Source.RConvArgs E srcΓ [.fixedBytes n width] :=
  .cons (.assign (.local i) (.local r))
    (by change decide (n ≤ n) = true; exact decide_eq_true (Nat.le_refl n)) .nil

theorem argument_actual (G : Source.Glob E) (F : Source.Fr) (extra : Nat)
    (source : Source.EMState E srcΓ) (n : Nat) (width : 1 ≤ n ∧ n ≤ 32)
    (i r : Source.Idx srcΓ (.fixedBytes n width)) (bs : List UInt8)
    (length : bs.length = n) (read : source.1.get r = .fixedBytes bs length) :
    (Source.evalConvArgs G F (extra+4) (arguments n width i r)).run source =
      (.ok (.cons (.fixedBytes bs length) .nil),
       (source.1.set i (.fixedBytes bs length),source.2)) := by
  first
  | simp only [arguments,Source.evalConvArgs,IntegerCallable.conversion_identity,
      Source.Hoare.run_bind,source_assign_local_run G F (extra+1) source i r
        (.fixedBytes bs length) read]; rfl
  | decide
  | omega
  | rfl

theorem transport_argument {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (n : Nat) (width : 1 ≤ n ∧ n ≤ 32) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (reflect : ∀ (v : Source.Val E.layout (.fixedBytes n width)) (x : PrimTy.uint.Denote),
      R (.fixedBytes n width) (.val .uint) v x → Rel n width v x)
    (i r : Source.Idx srcΓ (.fixedBytes n width)) (j k : Idx Γ (.val .uint))
    (writeMap : m.slot i = ⟨.val .uint,j⟩) (readMap : m.slot r = ⟨.val .uint,k⟩)
    (bs : List UInt8) (length : bs.length = n) (read : source.1.get r = .fixedBytes bs length) :
    (Source.evalConvArgs G F (fuel+4) (arguments n width i r)).run source =
      (.ok (.cons (.fixedBytes bs length) .nil),(source.1.set i (.fixedBytes bs length),source.2)) ∧
    (assignLocalOperand j k).run target =
      .ok (⟨target.setLocal j (value n width bs length),List.prefix_refl _⟩,.prim (value n width bs length)) ∧
    Rel n width (.fixedBytes bs length : Source.Val E.layout (.fixedBytes n width)) (value n width bs length) ∧
    m.Related R (source.1.set i (.fixedBytes bs length)) (TEnv.set j (value n width bs length) target.env) := by
  have actual := FixedBytesAssignment.transport G F (fuel+1) source target n width
    m R aligned reflect i r j k writeMap readMap bs length read
  exact ⟨argument_actual G F fuel source n width i r bs length read,actual.2⟩

end Solidity.Lowering.V08.FixedBytesCallableArgument

/-- info: 'Solidity.Lowering.V08.FixedBytesCallableArgument.arguments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.FixedBytesCallableArgument.arguments
/-- info: 'Solidity.Lowering.V08.FixedBytesCallableArgument.argument_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.FixedBytesCallableArgument.argument_actual
/-- info: 'Solidity.Lowering.V08.FixedBytesCallableArgument.transport_argument' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.V08.FixedBytesCallableArgument.transport_argument
