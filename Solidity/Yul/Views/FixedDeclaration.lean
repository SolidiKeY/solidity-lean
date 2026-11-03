import Solidity.Yul.Views.NestedDeclarationFinal

/-! Finite layout certificates indexed by ACTUAL source types/declarations.
This is not another source AST/state: no untyped shape is accepted, no desired
slots/inverses/safety laws are fields, and no depth/fuel limit is introduced.
A finite certificate does not assert arbitrary cyclic declarations supported. -/
namespace Solidity.Yul.Views

mutual
inductive FixedDeclaration (E : Source.Env) : Source.STy → Type where
  | scalar (τ : Source.STy) (supported : (declarationScalar? E.layout τ).isSome) : FixedDeclaration E τ
  | array {τ : Source.STy} (count : Nat) (positive : 0 < count) (element : FixedDeclaration E τ) :
      FixedDeclaration E (.array .storage τ (some count))
  | strct (name : Source.DeclName) (fields : List (String × Source.STy))
      (found : E.structFields name .storage = some fields)
      (members : FixedDeclarationFields E (fields.map Prod.snd)) : FixedDeclaration E (.struct .storage name)
inductive FixedDeclarationFields (E : Source.Env) : List Source.STy → Type where
  | nil : FixedDeclarationFields E []
  | cons {τ τs} (head : FixedDeclaration E τ) (tail : FixedDeclarationFields E τs) : FixedDeclarationFields E (τ::τs)
end

end Solidity.Yul.Views
