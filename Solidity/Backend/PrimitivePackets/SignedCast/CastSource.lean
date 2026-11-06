import Solidity.Lowering.V07.SignedWidthCasts

/-! Actual Source signed local casts; both width directions use the existing
explicit conversion, including its wrapping rather than checked arithmetic. -/
namespace Solidity.Backend.PrimitivePackets.SignedCast
open Solidity.Lowering.V07
abbrev Valid (bits : Nat) := bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256
abbrev ty := SignedWidthCasts.ty

theorem source_success (fromBits bits : Nat) (hf : Valid fromBits) (ht : Valid bits)
    {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (s : Source.EMState E Γ) (i : Source.Idx Γ (.int (ty fromBits hf)))
    (x : Int) (hx : (ty fromBits hf).lo ≤ x ∧ x ≤ (ty fromBits hf).hi)
    (read : s.1.get i = .int x hx) :
    (Source.evalE G F (fuel+2) (.convExplicit (τ := .int (ty bits ht))
      (.local i) (SignedWidthCasts.allowed fromBits hf E bits ht))).run s =
      (.ok (.val (Source.intWrap (ty bits ht) x)),s) := by
  first | rfl | omega | exact SignedWidthCasts.source_local_run fromBits hf G F fuel s i bits ht x hx read
end Solidity.Backend.PrimitivePackets.SignedCast
