import Solidity.Backend.PrimitivePackets.BitNot.Target

/-! Source-to-public-selected-code complement for all valid unsigned widths.
Only the initial local family and full StateRepr are premises. The compiler
result, masked value and exact preserved source/target states are derived. -/
namespace Solidity.Backend.PrimitivePackets.BitNot
open Evm Evm.Memory Solidity.Lowering.V07
open UnsignedNarrowing (ty)

variable {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}

theorem success (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int (ty bits valid))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits valid) si ti source.1 target.env)
    (k : ι) (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : source.1.get (si k) = .int x hx)
    {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L offset frame F target base machine) (tail : List Word) :
    Memory.compileVal offset F (value (C:=C) bits (ti k)) = some (selected bits offset F (ti k)) ∧
    (Source.evalE G SF (fuel+2) (.unary .bitNot (.local (si k)))).run source =
      (.ok (.val (Source.intWrap (ty bits valid) (-x-1))),source) ∧
    IntValueRel (ty bits valid)
      (Source.intWrap (ty bits valid) (-x-1) : Source.Val E.layout (.int (ty bits valid)))
      (integerValue (ty bits valid) ((ty bits valid).wrap (-x-1)) ((ty bits valid).wrap_mem (-x-1))) ∧
    ∃ word, ReprV .uint (integerValue (ty bits valid) ((ty bits valid).wrap (-x-1))
        ((ty bits valid).wrap_mem (-x-1))) word ∧
      run (selected (C:=C) bits offset F (ti k)).code {machine with stack := tail} =
        .ok ({machine with stack := tail}.push word) 0 := by
  exact ⟨public_selection bits offset F (ti k),
    source_success bits valid G SF fuel source (si k) x hx read,
    integer_related _ _ _,
    target_success target bits valid (ti k) x hx (family.read k x hx read) represented tail⟩
end Solidity.Backend.PrimitivePackets.BitNot

/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.success
