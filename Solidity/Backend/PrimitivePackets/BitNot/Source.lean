import Solidity.Lowering.V07.UnsignedComplement

/-! Actual Source unsigned complement at every admitted byte width. Both
checked modes use the original wrapping/masking semantics and preserve the
complete input state. No target execution or desired run is a premise. -/
namespace Solidity.Backend.PrimitivePackets.BitNot
open Solidity.Lowering.V07
open UnsignedNarrowing (ty)

theorem masked_value (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi) :
    (ty bits valid).wrap (-x-1) = ((2^bits : Nat) : Int)-1-x := by
  have positive := Source.two_pow_pos bits
  have bounds : 0 ≤ x ∧ x < ((2^bits : Nat) : Int) := by
    simp only [ty,Source.IntTy.lo,Source.IntTy.hi,Bool.false_eq_true,if_false] at hx
    omega
  rw [UnsignedNarrowing.wrap_eq,←Int.add_emod_left ((2^bits : Nat) : Int) (-x-1)]
  rw [show ((2^bits : Nat) : Int)+(-x-1) = ((2^bits : Nat) : Int)-1-x by omega]
  apply Int.emod_eq_of_lt <;> omega

theorem source_success (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (s : Source.EMState E Γ) (i : Source.Idx Γ (.int (ty bits valid)))
    (x : Int) (hx : (ty bits valid).lo ≤ x ∧ x ≤ (ty bits valid).hi)
    (read : s.1.get i = .int x hx) :
    (Source.evalE G F (fuel+2) (.unary .bitNot (.local i))).run s =
      (.ok (.val (Source.intWrap (ty bits valid) (-x-1))),s) := by
  apply UnsignedComplement.source_of_run bits valid G F (fuel+1) s s (.local i) x hx
  change (Except.ok (Source.RVal.val (s.1.get i)),s) = _
  rw [read]
end Solidity.Backend.PrimitivePackets.BitNot

/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.masked_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.masked_value
/-- info: 'Solidity.Backend.PrimitivePackets.BitNot.source_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.PrimitivePackets.BitNot.source_success
