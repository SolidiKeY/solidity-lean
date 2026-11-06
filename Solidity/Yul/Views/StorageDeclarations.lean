import Solidity.Yul.Views.StorageDeclarationHead

namespace Solidity.Yul.Views

/-- Existing typed declaration certificates, indexed by the selected root names
and declared types. Actual rootTy agreement is CHECKED by pack below. -/
inductive StorageDeclarations (E : Source.Env) : List (Source.DeclName × Source.STy) → Type where
  | nil : StorageDeclarations E []
  | cons {root τ rest} (head : StorageDeclaration E τ) (tail : StorageDeclarations E rest) :
      StorageDeclarations E ((root,τ)::rest)


def StorageDeclarations.pack {E ds} (d : StorageDeclarations E ds) : RootPackFn E :=
  StorageDeclarations.casesOn (motive := fun _ _ => RootPackFn E) d
    (fun _ cursor => .ok ([],cursor))
    (fun {root τ _} head tail a cursor =>
      if E.rootTy root = some τ then
        (head.pack ⟨root,[]⟩ a cursor).bind fun first =>
          (tail.pack a first.2).map fun rest => (first.1++rest.1,rest.2)
      else .error .missingRoot)

/-- Constructor equation keeps simplification local instead of unfolding a
symbolic recursive tail under its eliminator. -/
theorem StorageDeclarations.pack_cons {E root τ rest} (head : StorageDeclaration E τ) (tail : StorageDeclarations E rest)
    (a : Roadmap.Address) (cursor : Nat) :
    (StorageDeclarations.cons (root := root) head tail).pack a cursor =
      if E.rootTy root = some τ then
        (head.pack ⟨root,[]⟩ a cursor).bind (fun first =>
          (tail.pack a first.2).map (fun result => (first.1++result.1,result.2)))
      else .error .missingRoot := rfl

def StorageDeclarations.paths {E ds} (d : StorageDeclarations E ds) : List Source.SPath :=
  StorageDeclarations.casesOn (motive := fun _ _ => List Source.SPath) d []
    (fun {root _ _} head tail => head.paths ⟨root,[]⟩ ++ tail.paths)

def StorageDeclarations.endByte {E ds} (d : StorageDeclarations E ds) : Nat → Nat :=
  StorageDeclarations.casesOn (motive := fun _ _ => Nat → Nat) d id
    (fun head tail cursor => tail.endByte (head.endByte cursor))

end Solidity.Yul.Views
