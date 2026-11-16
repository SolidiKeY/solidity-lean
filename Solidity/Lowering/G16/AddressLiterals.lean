import Solidity.Lowering.V07.AddressConversions
import Solidity.Lowering.V07.IntegerConstants

/-! Address literal evaluation and fresh native capture, reusing V07's
160-bit address relation and integer-constant program. Length/checksum
admission is not inferred from a resolved Source literal. -/
namespace Solidity.Lowering.G16.AddressLiterals
open Solidity.Lowering.V07

/-- The value of the actual resolved Source literal, including its 160-bit
reduction. This is not a new admission predicate. -/
def address (digits : List (Fin 16)) : Roadmap.Address :=
  ⟨digits.foldl (fun acc d => acc * 16 + d.val) 0 % 2 ^ 160,
    Nat.mod_lt _ (by decide)⟩

def operand {C : Contract} {Γ : Ctx} (digits : List (Fin 16)) :
    DeferredSource.Operand C Γ (.prim .uint) :=
  IntegerConstants.operand AddressConversions.ty (address digits).val
    (AddressConversions.address_range (address digits))

/-- One family statement over all resolved address literals. The Source
execution, actual capture program, and 160-bit value relation are independent
conclusions; no successful execution is assumed. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (digits : List (Fin 16)) :
    (Source.evalE G F (fuel+1) (.addressLit digits)).run source =
      (.ok (.val (.address (address digits))),source) ∧
    (operand digits).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim (AddressConversions.addressValue (address digits))) ∧
    AddressConversions.AddressRel false
      (.address (address digits) : Source.Val E.layout (.address false))
      (AddressConversions.addressValue (address digits)) := by
  exact ⟨rfl,IntegerConstants.operand_run target AddressConversions.ty _ _,
    AddressConversions.address_related false (address digits)⟩

end Solidity.Lowering.G16.AddressLiterals

/-- info: 'Solidity.Lowering.G16.AddressLiterals.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.AddressLiterals.transport
