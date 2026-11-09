import Solidity.Lowering.V07.UnsignedComplement
import Solidity.Lowering.V07.SignedComplement

/-! Integer complement at all widths and signs, through the published V07
programs. This is a local-expression leaf, not a frontend selection theorem. -/
namespace Solidity.Lowering.G16.Complement
open Solidity.Lowering.V07

def value {C : Contract} {Γ : Ctx} (t : Source.IntTy) :
    Val C Γ (integerPrim t) → Val C Γ (integerPrim t) :=
  match t with
  | ⟨false,bits,_⟩ => UnsignedComplement.complementValue bits
  | ⟨true,bits,_⟩ => SignedComplement.complementValue bits

/-- One integer-complement statement includes all valid signs and widths in
both checked and unchecked frames. Initial aligned locals supply the inputs. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (t : Source.IntTy)
    (si : ι → Source.Idx srcΓ (.int t)) (ti : ι → Idx Γ (.val (integerPrim t)))
    (family : IntegerLocalFamily t si ti source.1 target.env)
    (k : ι) (x : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (read : source.1.get (si k) = .int x hx) :
    (Source.evalE G F (fuel+2) (.unary .bitNot (.local (si k)))).run source =
      (.ok (.val (Source.intWrap t (-x-1))),source) ∧
    (value t (.simple (.local (ti k)))).evalT target =
      .ok (integerValue t (t.wrap (-x-1)) (t.wrap_mem (-x-1))) ∧
    IntValueRel t (Source.intWrap t (-x-1) : Source.Val E.layout (.int t))
      (integerValue t (t.wrap (-x-1)) (t.wrap_mem (-x-1))) := by
  obtain ⟨sign,bits,valid⟩ := t
  cases sign with
  | false => exact UnsignedComplement.local_transport bits valid G F fuel source target si ti family k x hx read
  | true => exact SignedComplement.local_transport bits valid G F fuel source target si ti family k x hx read

end Solidity.Lowering.G16.Complement

/-- info: 'Solidity.Lowering.G16.Complement.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Complement.transport
