import Solidity.Lowering.Readonly.PrimitiveLocals

/-! Guard empty contexts and binder permutation hiding vacuous primitive transport.
An inhabited mixed uint/int/bool context supplies the SAME concrete inputs to all
four original local-map statements. Primitive values/default/injectivity inputs
are inhabited too. These are original statement inputs and exact applications,
not ABI decoding, compiler success, or Source/callee/native-frame adequacy. -/
namespace Solidity.H62.ReadonlyAudit.PrimitiveTransportWitnesses
open Solidity Solidity.Source
open Solidity.Lowering.Readonly

def contract : Solidity.Contract := { vars := [] }
def environment : Env := ⟨[]⟩
def kinds : List PrimTy := [.bool,.uint,.int,.bool]
def unsigned : PrimTy.Denote .uint := ⟨9, by decide⟩
def signed : PrimTy.Denote .int := ⟨-3, by decide⟩
def target : TEnv contract [] (PrimitiveLocals.targetCtx kinds) :=
  (true,unsigned,signed,false,())
def source : Locals environment.layout (kinds.map PrimitiveValues.sourceTy) :=
  .cons (.bool true) (.cons (PrimitiveValues.toSource environment.layout .uint unsigned)
    (.cons (PrimitiveValues.toSource environment.layout .int signed) (.cons (.bool false) .nil)))
def last : Solidity.Idx (PrimitiveLocals.targetCtx kinds) (.val .bool) :=
  .there (.there (.there .here))

theorem values_from_to_joint :
    PrimitiveValues.fromSource environment.layout .uint
      (PrimitiveValues.toSource environment.layout .uint unsigned) = unsigned :=
  PrimitiveValues.from_to environment.layout .uint unsigned

theorem values_to_from_joint :
    PrimitiveValues.toSource environment.layout .int
      (PrimitiveValues.fromSource environment.layout .int
        (PrimitiveValues.toSource environment.layout .int signed)) =
      PrimitiveValues.toSource environment.layout .int signed :=
  PrimitiveValues.to_from environment.layout .int _

theorem faithful_joint :
    (PrimitiveValues.toSource environment.layout .bool true =
      PrimitiveValues.toSource environment.layout .bool true) ∧
    (true : Bool) = true :=
  ⟨rfl, PrimitiveValues.faithful environment.layout .bool (a₁ := true) (a₂ := true) rfl⟩

theorem default_joint :
    Solidity.Source.Val.default environment.layout (PrimitiveValues.sourceTy .bool) =
      some (PrimitiveValues.toSource environment.layout .bool (PrimTy.dflt .bool)) :=
  PrimitiveValues.default_value environment.layout .bool

theorem locals_from_to_joint :
    PrimitiveLocals.fromLocals environment.layout kinds
      (PrimitiveLocals.toLocals environment.layout kinds target) = target :=
  PrimitiveLocals.from_to kinds target

theorem locals_to_from_joint :
    PrimitiveLocals.toLocals (C := contract) (H := []) environment.layout kinds
      (PrimitiveLocals.fromLocals environment.layout kinds source) = source :=
  PrimitiveLocals.to_from kinds source

theorem get_to_joint :
    (PrimitiveLocals.toLocals environment.layout kinds target).get
      (PrimitiveLocals.sourceIndex last) =
      PrimitiveValues.toSource environment.layout .bool (TEnv.get last target) :=
  PrimitiveLocals.get_toLocals kinds target last

theorem get_from_joint :
    PrimitiveValues.fromSource environment.layout .bool
      (source.get (PrimitiveLocals.sourceIndex last)) =
      TEnv.get last (PrimitiveLocals.fromLocals (C := contract) (H := [])
        environment.layout kinds source) :=
  PrimitiveLocals.get_fromLocals kinds source last

/-- Nonempty mixed contexts keep both order and distinct Bool endpoints. -/
theorem context_observed :
    PrimitiveLocals.toLocals environment.layout kinds target = source ∧
    source.get (PrimitiveLocals.sourceIndex last) = .bool false ∧
    source.get (Solidity.Source.Idx.here) = .bool true := ⟨rfl,rfl,rfl⟩

/-- The two numeric positions transport actual nondefault, different-sign inputs. -/
theorem numbers_observed : unsigned.val = 9 ∧ signed.val = -3 := ⟨rfl,rfl⟩

/-- A constant translator loses the distinct endpoint values and fails injectivity. -/
theorem constant_refused :
    ¬ Function.Injective (fun (_ : Bool) => PrimitiveValues.toSource environment.layout .bool true) := by
  intro h
  have clash : (true : Bool) = false := @h true false rfl
  cases clash

end Solidity.H62.ReadonlyAudit.PrimitiveTransportWitnesses
