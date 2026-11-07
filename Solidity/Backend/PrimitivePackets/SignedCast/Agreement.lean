import Solidity.Backend.PrimitivePackets.SignedCast.Target

/-! Local Source origin, actual public selection and target execution for every
approved intN to intM conversion. Initial family and physical StateRepr are
explicit; no desired execution, selected certificate or poststate is assumed. -/
namespace Solidity.Backend.PrimitivePackets.SignedCast
open Evm Evm.Memory Solidity.Lowering.V07

theorem success (fromBits bits : Nat) (hf : Valid fromBits) (ht : Valid bits)
    {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int (ty fromBits hf))) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily (ty fromBits hf) si ti source.1 target.env) (a : ι)
    (x : Int) (hx : (ty fromBits hf).lo ≤ x ∧ x ≤ (ty fromBits hf).hi)
    (read : source.1.get (si a) = .int x hx)
    {offset L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {m : Machine}
    (represented : StateRepr L offset frame F target base m) (tail : List Word) :
    Memory.compileVal offset F (value (C:=C) bits (ti a)) =
        some (selected (C:=C) bits ht offset F (ti a)) ∧
    (Source.evalE G SF (fuel+2) (.convExplicit (τ := .int (ty bits ht))
      (.local (si a)) (SignedWidthCasts.allowed fromBits hf E bits ht))).run source =
        (.ok (.val (Source.intWrap (ty bits ht) x)),source) ∧
    ∃ word, ReprV .int (integerValue (ty bits ht) ((ty bits ht).wrap x)
        ((ty bits ht).wrap_mem x)) word ∧
      run (selected (C:=C) bits ht offset F (ti a)).code {m with stack := tail} =
        .ok ({m with stack := tail}.push word) 0 := by
  exact ⟨public_selection bits ht offset F (ti a),
    source_success fromBits bits hf ht G SF fuel source (si a) x hx read,
    target_success fromBits bits hf ht target (ti a) x hx
      (family.read a x hx read) represented tail⟩

#print axioms success
#print axioms signextend
end Solidity.Backend.PrimitivePackets.SignedCast
