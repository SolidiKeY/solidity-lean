import Lean
import Solidity.Lowering.Readonly.PrimitiveReads

/-! Guard private helper identities being silently dropped or replaced by public
surrogates. These macros resolve the exact original private kernel names; the
resulting applications are ordinary kernel-checked proof terms. All equality
and typing premises are supplied together at actual true/default Bool values.
This is premise satisfiability, not Source execution or compiler adequacy. The
SDK elaborator import is confined to this test module, never the core roots. -/
namespace Solidity.H62.ReadonlyAudit.PrivateTransportWitnesses
open Solidity.Source
open Solidity.Lowering.Readonly

macro "original_cast_injective" : term =>
  return Lean.mkIdent (Lean.mkPrivateNameCore `Solidity.Lowering.Readonly.PrimitiveFields
    `Solidity.Lowering.Readonly.PrimitiveFields.cast_injective)
macro "original_cast_back" : term =>
  return Lean.mkIdent (Lean.mkPrivateNameCore `Solidity.Lowering.Readonly.PrimitiveFields
    `Solidity.Lowering.Readonly.PrimitiveFields.cast_back)
macro "original_default_transport" : term =>
  return Lean.mkIdent (Lean.mkPrivateNameCore `Solidity.Lowering.Readonly.PrimitiveFields
    `Solidity.Lowering.Readonly.PrimitiveFields.default_transport)
macro "original_cancel" : term =>
  return Lean.mkIdent (Lean.mkPrivateNameCore `Solidity.Lowering.Readonly.PrimitiveReads
    `Solidity.Lowering.Readonly.PrimitiveReads.cancel)

def environment : Env := ⟨[]⟩
def yes : Solidity.Source.Val environment.layout .bool := .bool true

theorem injective_joint : (STy.bool = STy.bool) ∧
    ((rfl : STy.bool = STy.bool).symm ▸ yes = (rfl : STy.bool = STy.bool).symm ▸ yes) ∧ yes = yes :=
  ⟨rfl, rfl, original_cast_injective (rfl : STy.bool = STy.bool) yes yes rfl⟩

theorem back_joint : (STy.bool = STy.bool) ∧
    (rfl : STy.bool = STy.bool).symm ▸ ((rfl : STy.bool = STy.bool) ▸ yes) = yes :=
  ⟨rfl, original_cast_back (rfl : STy.bool = STy.bool) yes⟩

theorem default_joint : (STy.bool = PrimitiveValues.sourceTy .bool) ∧
    Solidity.Source.Val.default environment.layout .bool =
      some ((rfl : STy.bool = PrimitiveValues.sourceTy .bool).symm ▸
        PrimitiveValues.toSource environment.layout .bool (Solidity.PrimTy.dflt .bool)) :=
  ⟨rfl, original_default_transport environment.layout .bool .bool rfl⟩

theorem cancel_joint : (STy.bool = STy.bool) ∧
    (rfl : STy.bool = STy.bool) ▸ ((rfl : STy.bool = STy.bool).symm ▸ yes) = yes :=
  ⟨rfl, original_cancel (rfl : STy.bool = STy.bool) yes⟩

/-- A transported true value is distinguishable from the false default. -/
theorem true_not_default : some yes ≠ Solidity.Source.Val.default environment.layout .bool := by
  intro same
  cases same

end Solidity.H62.ReadonlyAudit.PrivateTransportWitnesses
