import Solidity.Backend.PrimitivePackets.SignedCheckedAdd.Target

/-! Selected checked int256 addition from arbitrary Source locals.
Initial local correspondence and the existing full StateRepr are real premises;
no compiled value, desired run or desired poststate is a caller argument. -/
namespace Solidity.Backend.PrimitivePackets.SignedCheckedAdd
open Evm Evm.Memory Solidity.Lowering.V07

variable {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}

/-- The Source state stays exact; every target field below the result word is
unchanged, including an arbitrary saved stack and populated caller frame. -/
theorem success (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int U)) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily U si ti source.1 target.env) (a b : ι)
    (x y : Int) (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy)
    (fits : U.lo ≤ x+y ∧ x+y ≤ U.hi)
    {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L offset frame F target base machine) (tail : List Word) :
    Memory.compileVal offset F (value (C:=C) (ti a) (ti b)) = some (selected offset F (ti a) (ti b)) ∧
    (Source.evalE G {SF with checked := true} (fuel+3)
      (.binary .add (.local (si a)) (.local (si b)))).run source =
      (.ok (.val (.int (x+y) fits)),source) ∧
    ∃ word, ReprV .int (integerValue U (x+y) fits) word ∧
      run (selected (C:=C) offset F (ti a) (ti b)).code {machine with stack := tail} =
        .ok ({machine with stack := tail}.push word) 0 := by
  exact ⟨public_selection offset F (ti a) (ti b),
    source_success G SF fuel source (si a) (si b) x y hx hy readA readB fits,
    target_success target (ti a) (ti b) x y hx hy
      (family.read a x hx readA) (family.read b y hy readB) fits represented tail⟩

/-- The source exposes exact panic bytes; the target exposes only coarse revert.
In particular this theorem asserts neither target panic bytes nor an invented
reverted machine state. -/
theorem overflow (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int U)) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily U si ti source.1 target.env) (a b : ι)
    (x y : Int) (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy)
    (outside : ¬ (U.lo ≤ x+y ∧ x+y ≤ U.hi))
    {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L offset frame F target base machine) (tail : List Word) :
    Memory.compileVal offset F (value (C:=C) (ti a) (ti b)) = some (selected offset F (ti a) (ti b)) ∧
    (Source.evalE G {SF with checked := true} (fuel+3)
      (.binary .add (.local (si a)) (.local (si b)))).run source =
      (.error (.revert (Source.panicData .arithmetic)),source) ∧
    run (selected (C:=C) offset F (ti a) (ti b)).code {machine with stack := tail} = .revert := by
  exact ⟨public_selection offset F (ti a) (ti b),
    source_overflow G SF fuel source (si a) (si b) x y hx hy readA readB outside,
    target_overflow target (ti a) (ti b) x y hx hy
      (family.read a x hx readA) (family.read b y hy readB) outside represented tail⟩
end Solidity.Backend.PrimitivePackets.SignedCheckedAdd
