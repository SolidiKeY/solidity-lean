import Solidity.Yul.Views.FixedDeclaration

namespace Solidity.Yul.Views

abbrev FixedPackFn (E : Source.Env) := (path : Source.SPath) → (a : Roadmap.Address) → Nat →
  Except DeclarationPackingError (List (ScalarPath E.layout (E.lay a)) × Nat)

def packFixedRow {E : Source.Env} (step : Nat → Source.Step) (head : FixedPackFn E) (tail : Nat → FixedPackFn E)
    (index : Nat) (path : Source.SPath) (a : Roadmap.Address) (cursor : Nat) :=
  (head (path.go (step index)) a cursor).bind (fun first =>
    (tail (index+1) path a first.2).map (fun rest => (first.1++rest.1,rest.2)))

/-- Fold over the ACTUAL declared array count. The child function is the
intrinsic certificate recursor result, not an untyped intermediate AST. -/
def packFixedElements {E : Source.Env} (child : FixedPackFn E) (path : Source.SPath) (a : Roadmap.Address)
    (index count cursor : Nat) : Except DeclarationPackingError (List (ScalarPath E.layout (E.lay a)) × Nat) :=
  match count with
  | 0 => .ok ([],cursor)
  | n+1 => packFixedRow Source.Step.index child (fun i path a cursor => packFixedElements child path a i n cursor) index path a cursor

def packFixedField {E : Source.Env} (head : FixedPackFn E) (tail : Nat → FixedPackFn E)
    (index : Nat) (path : Source.SPath) (a : Roadmap.Address) (cursor : Nat) :=
  packFixedRow Source.Step.field head tail index path a cursor

def alignFixedPack {E : Source.Env} (body : FixedPackFn E) : FixedPackFn E :=
  fun path a cursor => (body path a (roundSlot cursor)).map (fun out => (out.1,roundSlot out.2))

mutual
/-- Uses casesOn on the intrinsically indexed finite certificate; owner source
values/state are unchanged. All scalar arithmetic remains in the ONE existing
packDeclarationPaths implementation. Aggregate entry AND exit align to slots. -/
def FixedDeclaration.pack {E : Source.Env} {τ : Source.STy} (d : FixedDeclaration E τ) : FixedPackFn E :=
  FixedDeclaration.casesOn (motive_1 := fun _ _ => FixedPackFn E) d
    (fun τ _ => fun path a cursor => packDeclarationPaths E (fun _ => path) a 0 [("",τ)] cursor)
    (fun count _ element => alignFixedPack (fun path a cursor => packFixedElements element.pack path a 0 count cursor))
    (fun _ _ _ members => alignFixedPack (members.pack 0))

def FixedDeclarationFields.pack {E : Source.Env} {τs : List Source.STy} (d : FixedDeclarationFields E τs) : Nat → FixedPackFn E :=
  FixedDeclarationFields.casesOn (motive_2 := fun _ _ => Nat → FixedPackFn E) d
    (fun _ _ _ cursor => .ok ([],cursor))
    (fun head tail => packFixedField head.pack tail.pack)

end

/-- Root binding is checked against the ACTUAL declared source type. Input
base is explicit; arbitrary global root assignment is still an owner agreement. -/
def prepareFixedDeclaration {E : Source.Env} {τ : Source.STy} (d : FixedDeclaration E τ)
    (root : Source.DeclName) (a : Roadmap.Address) (base : Roadmap.Word) :
    Except DeclarationPackingError (List (ScalarPath E.layout (E.lay a)) × Nat) :=
  if E.rootTy root = some τ then d.pack ⟨root,[]⟩ a (base.val*32) else .error .missingRoot

end Solidity.Yul.Views
