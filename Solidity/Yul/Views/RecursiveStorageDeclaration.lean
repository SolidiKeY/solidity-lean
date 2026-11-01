import Solidity.Yul.Views.MemberStorageCompatibility

namespace Solidity.Yul.Views

/-! Finite intrinsic certificate, not another Source state/AST. The Bool index
records actual primitive dynamic occurrence; all-fixed subtrees retain existing
FixedDeclaration leaves. No recursion-depth or runtime length cap is introduced. -/
mutual
inductive RecursiveStorageDeclaration (E : Source.Env) : Source.STy → Bool → Type where
  | leaf {τ} (old : StorageDeclaration E τ) : RecursiveStorageDeclaration E τ old.primitiveDynamic
  | strct (name : Source.DeclName) (fields : List (String × Source.STy))
      (found : E.structFields name .storage = some fields)
      (members : RecursiveStorageFields E (fields.map Prod.snd) true) :
      RecursiveStorageDeclaration E (.struct .storage name) true
inductive RecursiveStorageFields (E : Source.Env) : List Source.STy → Bool → Type where
  | nil : RecursiveStorageFields E [] false
  | cons {τ τs hb tb} (head : RecursiveStorageDeclaration E τ hb) (tail : RecursiveStorageFields E τs tb) :
      RecursiveStorageFields E (τ::τs) (hb || tb)
end

mutual
/-- Constant motives generalize BOTH intrinsic indices (source type and dynamic
presence). Child checks preserve the old field guard and actual full path. -/
def RecursiveStorageDeclaration.pack {E τ b} (d : RecursiveStorageDeclaration E τ b) : FixedPackFn E :=
  RecursiveStorageDeclaration.casesOn (motive_1 := fun _ _ _ => FixedPackFn E) d
    (fun old => old.pack) (fun _ _ _ members => alignFixedPack (members.pack 0))
def RecursiveStorageFields.pack {E τs b} (d : RecursiveStorageFields E τs b) : Nat → FixedPackFn E :=
  RecursiveStorageFields.casesOn (motive_2 := fun _ _ _ => Nat → FixedPackFn E) d
    (fun _ _ _ cursor => .ok ([],cursor))
    (fun {τ _ _ _} head tail => packFixedField
      (fun p a cursor => if E.pathTy p = some τ then head.pack p a cursor else .error .cellMismatch) tail.pack)
end

mutual
def RecursiveStorageDeclaration.endByte {E τ b} (d : RecursiveStorageDeclaration E τ b) : Nat → Nat :=
  RecursiveStorageDeclaration.casesOn (motive_1 := fun _ _ _ => Nat → Nat) d
    (fun old => old.endByte) (fun _ _ _ members cursor => roundSlot (members.endByte (roundSlot cursor)))
def RecursiveStorageFields.endByte {E τs b} (d : RecursiveStorageFields E τs b) : Nat → Nat :=
  RecursiveStorageFields.casesOn (motive_2 := fun _ _ _ => Nat → Nat) d id
    (fun head tail cursor => tail.endByte (head.endByte cursor))
end

mutual
def RecursiveStorageDeclaration.paths {E τ b} (d : RecursiveStorageDeclaration E τ b) : Source.SPath → List Source.SPath :=
  RecursiveStorageDeclaration.casesOn (motive_1 := fun _ _ _ => Source.SPath → List Source.SPath) d
    (fun old => old.paths) (fun _ _ _ members => members.paths 0)
def RecursiveStorageFields.paths {E τs b} (d : RecursiveStorageFields E τs b) : Nat → Source.SPath → List Source.SPath :=
  RecursiveStorageFields.casesOn (motive_2 := fun _ _ _ => Nat → Source.SPath → List Source.SPath) d
    (fun _ _ => []) (fun head tail i p => head.paths (p.go (.field i)) ++ tail.paths (i+1) p)
end

mutual
def RecursiveStorageDeclaration.headers {E τ b} (d : RecursiveStorageDeclaration E τ b) : Source.SPath → Nat → List PathHeaderEntry :=
  RecursiveStorageDeclaration.casesOn (motive_1 := fun _ _ _ => Source.SPath → Nat → List PathHeaderEntry) d
    (fun old => old.pathHeaders) (fun _ _ _ members p cursor => members.headers 0 p (roundSlot cursor))
def RecursiveStorageFields.headers {E τs b} (d : RecursiveStorageFields E τs b) : Nat → Source.SPath → Nat → List PathHeaderEntry :=
  RecursiveStorageFields.casesOn (motive_2 := fun _ _ _ => Nat → Source.SPath → Nat → List PathHeaderEntry) d
    (fun _ _ _ => []) (fun head tail i p cursor => head.headers (p.go (.field i)) cursor ++ tail.headers (i+1) p (head.endByte cursor))
end

end Solidity.Yul.Views
