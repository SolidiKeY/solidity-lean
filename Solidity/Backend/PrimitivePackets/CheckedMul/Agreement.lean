import Solidity.Backend.PrimitivePackets.CheckedMul.Target

/-! Selected checked uint256 multiplication from arbitrary Source locals.
Initial local correspondence and the existing full StateRepr are real premises;
no compiled value, desired run or desired poststate is a caller argument. -/
namespace Solidity.Backend.PrimitivePackets.CheckedMul
open Evm Evm.Memory Solidity.Lowering.V07

theorem overflow_iff (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi) :
    ¬ (U.lo ≤ x*y ∧ x*y ≤ U.hi) ↔ U.hi < x*y := by
  have zero : U.lo = 0 := rfl
  rw [zero] at hx hy ⊢
  have nonnegative : 0 ≤ x*y := Int.mul_nonneg hx.1 hy.1
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
    (fits : U.lo ≤ x*y ∧ x*y ≤ U.hi)
    {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L offset frame F target base machine) (tail : List Word) :
    Memory.compileVal offset F (value (C:=C) (ti a) (ti b)) = some (selected offset F (ti a) (ti b)) ∧
    (Source.evalE G {SF with checked := true} (fuel+3)
      (.binary .mul (.local (si a)) (.local (si b)))).run source =
      (.ok (.val (.int (x*y) fits)),source) ∧
    ∃ word, ReprV .uint (integerValue U (x*y) fits) word ∧
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
    (si : ι → Source.Idx srcΓ (.int U)) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily U si ti source.1 target.env) (a b : ι)
    (x y : Int) (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy)
    (outside : ¬ (U.lo ≤ x*y ∧ x*y ≤ U.hi))
    {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L offset frame F target base machine) (tail : List Word) :
    Memory.compileVal offset F (value (C:=C) (ti a) (ti b)) = some (selected offset F (ti a) (ti b)) ∧
    (Source.evalE G {SF with checked := true} (fuel+3)
      (.binary .mul (.local (si a)) (.local (si b)))).run source =
      (.error (.revert (Source.panicData .arithmetic)),source) ∧
    run (selected (C:=C) offset F (ti a) (ti b)).code {machine with stack := tail} = .revert := by
  exact ⟨public_selection offset F (ti a) (ti b),
    source_overflow G SF fuel source (si a) (si b) x y hx hy readA readB outside,
    target_overflow target (ti a) (ti b) x y hx hy
      (family.read a x hx readA) (family.read b y hy readB) outside represented tail⟩

/-- Exact failure classification for the actual selected instructions. -/
theorem target_overflow_exact {C : Contract} {Γ : Ctx} {offset L frame : Nat} {F : Frag Γ}
    (s : State C Γ) (a b : Idx Γ (.val .uint)) (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (ha : TEnv.get a s.env = integerValue U x hx)
    (hb : TEnv.get b s.env = integerValue U y hy)
    {base : Nat → Fin W} {m : Machine} (represented : StateRepr L offset frame F s base m)
    (tail : List Word) :
    run (selected (C:=C) offset F a b).code {m with stack:=tail} = .revert ↔ U.hi < x*y := by
  constructor
  · intro observed
    apply Classical.byContradiction
    intro outside
    have nonnegative : U.lo ≤ x*y := Int.mul_nonneg hx.1 hy.1
    have fits : U.lo ≤ x*y ∧ x*y ≤ U.hi := ⟨nonnegative,by omega⟩
    obtain ⟨word,repr,ran⟩ := target_success s a b x y hx hy ha hb fits represented tail
    rw [observed] at ran
    cases ran
  · intro outside
    exact target_overflow s a b x y hx hy ha hb ((overflow_iff x y hx hy).mpr outside) represented tail

/-- Source classification retains the exact arithmetic panic bytes and state. -/
theorem source_overflow_exact {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (s : Source.EMState E Γ)
    (a b : Source.Idx Γ (.int U)) (x y : Int)
    (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi)
    (ha : s.1.get a = .int x hx) (hb : s.1.get b = .int y hy) :
    (Source.evalE G {F with checked:=true} (fuel+3)
      (.binary .mul (.local a) (.local b))).run s =
      (.error (.revert (Source.panicData .arithmetic)),s) ↔ U.hi < x*y := by
  constructor
  · intro observed
    apply Classical.byContradiction
    intro outside
    have nonnegative : U.lo ≤ x*y := Int.mul_nonneg hx.1 hy.1
    have fits : U.lo ≤ x*y ∧ x*y ≤ U.hi := ⟨nonnegative,by omega⟩
    rw [source_success G F fuel s a b x y hx hy ha hb fits] at observed
    cases observed
  · intro outside
    exact source_overflow G F fuel s a b x y hx hy ha hb ((overflow_iff x y hx hy).mpr outside)

#print axioms target_overflow_exact
#print axioms source_overflow_exact

#print axioms overflow_iff
#print axioms success
#print axioms overflow
end Solidity.Backend.PrimitivePackets.CheckedMul
