import Solidity.Backend.PrimitivePackets.CheckedSub.Target

/-! Selected checked uint256 subtraction from arbitrary Source locals.
Initial local correspondence and the existing full StateRepr are real premises;
no compiled value, desired run or desired poststate is a caller argument. -/
namespace Solidity.Backend.PrimitivePackets.CheckedSub
open Evm Evm.Memory Solidity.Lowering.V07

theorem underflow_iff (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi) :
    ¬ (U.lo ≤ x-y ∧ x-y ≤ U.hi) ↔ x < y := by
  have zero : U.lo = 0 := rfl
  rw [zero] at hx hy ⊢
  omega

theorem success_iff (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi) :
    (U.lo ≤ x-y ∧ x-y ≤ U.hi) ↔ y ≤ x := by
  have zero : U.lo = 0 := rfl
  rw [zero] at hx hy ⊢
  omega

variable {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}

/-- The Source state stays exact; every target field below the result word is
unchanged, including an arbitrary saved stack and populated caller frame. -/
theorem success (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int U)) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily U si ti source.1 target.env) (a b : ι)
    (x y : Int) (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy)
    (fits : U.lo ≤ x-y ∧ x-y ≤ U.hi)
    {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L offset frame F target base machine) (tail : List Word) :
    Memory.compileVal offset F (value (C:=C) (ti a) (ti b)) = some (selected offset F (ti a) (ti b)) ∧
    (Source.evalE G {SF with checked := true} (fuel+3)
      (.binary .sub (.local (si a)) (.local (si b)))).run source =
      (.ok (.val (.int (x-y) fits)),source) ∧
    ∃ word, ReprV .uint (integerValue U (x-y) fits) word ∧
      run (selected (C:=C) offset F (ti a) (ti b)).code {machine with stack := tail} =
        .ok ({machine with stack := tail}.push word) 0 := by
  exact ⟨public_selection offset F (ti a) (ti b),
    source_success G SF fuel source (si a) (si b) x y hx hy readA readB fits,
    target_success target (ti a) (ti b) x y hx hy
      (family.read a x hx readA) (family.read b y hy readB) fits represented tail⟩

/-- The source exposes exact panic bytes; the target exposes only coarse revert.
In particular this theorem asserts neither target panic bytes nor an invented
reverted machine state. -/
theorem underflow (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int U)) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily U si ti source.1 target.env) (a b : ι)
    (x y : Int) (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy)
    (outside : ¬ (U.lo ≤ x-y ∧ x-y ≤ U.hi))
    {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L offset frame F target base machine) (tail : List Word) :
    Memory.compileVal offset F (value (C:=C) (ti a) (ti b)) = some (selected offset F (ti a) (ti b)) ∧
    (Source.evalE G {SF with checked := true} (fuel+3)
      (.binary .sub (.local (si a)) (.local (si b)))).run source =
      (.error (.revert (Source.panicData .arithmetic)),source) ∧
    run (selected (C:=C) offset F (ti a) (ti b)).code {machine with stack := tail} = .revert := by
  exact ⟨public_selection offset F (ti a) (ti b),
    source_underflow G SF fuel source (si a) (si b) x y hx hy readA readB outside,
    target_underflow target (ti a) (ti b) x y hx hy
      (family.read a x hx readA) (family.read b y hy readB) outside represented tail⟩
/-- Total classification for all in-range runtime-local operands. The caller
supplies neither an outcome nor a range premise for the difference. Success
retains the entire represented machine below the pushed word; underflow has
only the existing coarse target revert observation. -/
theorem classification (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int U)) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily U si ti source.1 target.env) (a b : ι)
    (x y : Int) (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy)
    {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L offset frame F target base machine) (tail : List Word) :
    Memory.compileVal offset F (value (C:=C) (ti a) (ti b)) = some (selected offset F (ti a) (ti b)) ∧
    if h : y ≤ x then
      (Source.evalE G {SF with checked := true} (fuel+3)
        (.binary .sub (.local (si a)) (.local (si b)))).run source =
        (.ok (.val (.int (x-y) ((success_iff x y hx hy).mpr h))),source) ∧
      ∃ word, ReprV .uint (integerValue U (x-y) ((success_iff x y hx hy).mpr h)) word ∧
        run (selected (C:=C) offset F (ti a) (ti b)).code {machine with stack := tail} =
          .ok ({machine with stack := tail}.push word) 0 ∧
        StateRepr L offset frame F target base ({machine with stack := tail}.push word)
    else
      (Source.evalE G {SF with checked := true} (fuel+3)
        (.binary .sub (.local (si a)) (.local (si b)))).run source =
        (.error (.revert (Source.panicData .arithmetic)),source) ∧
      run (selected (C:=C) offset F (ti a) (ti b)).code {machine with stack := tail} = .revert := by
  refine ⟨public_selection offset F (ti a) (ti b),?_⟩
  split
  · rename_i h
    obtain ⟨_,hs,word,repr,ran⟩ := success G SF fuel source target si ti family a b x y hx hy readA readB
      ((success_iff x y hx hy).mpr h) represented tail
    exact ⟨hs,word,repr,ran,represented.stack (word::tail)⟩
  · rename_i h
    have outside : ¬ (U.lo ≤ x-y ∧ x-y ≤ U.hi) := by
      intro fits
      exact h ((success_iff x y hx hy).mp fits)
    exact (underflow G SF fuel source target si ti family a b x y hx hy readA readB outside represented tail).2

/-- The selected physical run reverts exactly on unsigned underflow. -/
theorem target_underflow_iff (target : State C Γ) (a b : Idx Γ (.val .uint))
    (x y : Int) (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (ha : TEnv.get a target.env = integerValue U x hx)
    (hb : TEnv.get b target.env = integerValue U y hy)
    {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L offset frame F target base machine) (tail : List Word) :
    run (selected (C:=C) offset F a b).code {machine with stack := tail} = .revert ↔ x < y := by
  by_cases h : x < y
  · exact ⟨fun _ => h,fun _ => target_underflow target a b x y hx hy ha hb
      ((underflow_iff x y hx hy).mpr h) represented tail⟩
  · have fits : U.lo ≤ x-y ∧ x-y ≤ U.hi := (success_iff x y hx hy).mpr (by omega)
    obtain ⟨word,_,ran⟩ := target_success target a b x y hx hy ha hb fits represented tail
    constructor
    · intro failed
      rw [ran] at failed
      cases failed
    · exact fun lt => False.elim (h lt)

end Solidity.Backend.PrimitivePackets.CheckedSub
