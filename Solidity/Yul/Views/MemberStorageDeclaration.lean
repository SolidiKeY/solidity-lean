import Solidity.Yul.Views.PrimitiveDynamicCoverage

namespace Solidity.Yul.Views

/-- Actual declared struct field types, in the owner structFields order. Heads
reuse EXISTING StorageDeclaration; references are never relabelled inline Data. -/
inductive MemberStorageDeclarations (E : Source.Env) : List Source.STy → Type where
  | nil : MemberStorageDeclarations E []
  | cons {τ τs} (head : StorageDeclaration E τ) (tail : MemberStorageDeclarations E τs) : MemberStorageDeclarations E (τ::τs)

def checkedMemberPack {E τ} (d : StorageDeclaration E τ) : FixedPackFn E :=
  fun p a cursor => if E.pathTy p = some τ then d.pack p a cursor else .error .cellMismatch

def MemberStorageDeclarations.pack {E τs} (d : MemberStorageDeclarations E τs) : Nat → FixedPackFn E :=
  MemberStorageDeclarations.casesOn (motive := fun _ _ => Nat → FixedPackFn E) d
    (fun _ _ _ cursor => .ok ([],cursor))
    (fun head tail => packFixedField (checkedMemberPack head) tail.pack)

def MemberStorageDeclarations.endByte {E τs} (d : MemberStorageDeclarations E τs) : Nat → Nat :=
  MemberStorageDeclarations.casesOn (motive := fun _ _ => Nat → Nat) d id
    (fun head tail cursor => tail.endByte (head.endByte cursor))

def MemberStorageDeclarations.hasDynamic {E τs} (d : MemberStorageDeclarations E τs) : Bool :=
  MemberStorageDeclarations.casesOn (motive := fun _ _ => Bool) d false
    (fun head tail => head.primitiveDynamic || tail.hasDynamic)

/-- All-fixed structs retain the old leaf profile. The new certificate is for
actual primitive dynamic members, not a competing arbitrary struct layout. -/
inductive RootStorageDeclaration (E : Source.Env) : Source.STy → Type where
  | leaf {τ} (old : StorageDeclaration E τ) : RootStorageDeclaration E τ
  | strct (name : Source.DeclName) (fields : List (String × Source.STy))
      (found : E.structFields name .storage = some fields)
      (members : MemberStorageDeclarations E (fields.map Prod.snd))
      (dynamic : members.hasDynamic = true) : RootStorageDeclaration E (.struct .storage name)

def RootStorageDeclaration.pack {E τ} (d : RootStorageDeclaration E τ) : FixedPackFn E :=
  RootStorageDeclaration.casesOn (motive := fun _ _ => FixedPackFn E) d
    (fun old => old.pack) (fun _ _ _ members _ => alignFixedPack (members.pack 0))

def RootStorageDeclaration.endByte {E τ} (d : RootStorageDeclaration E τ) : Nat → Nat :=
  RootStorageDeclaration.casesOn (motive := fun _ _ => Nat → Nat) d
    (fun old => old.endByte) (fun _ _ _ members _ cursor => roundSlot (members.endByte (roundSlot cursor)))

theorem checkedMemberPack_success {E τ} (d : StorageDeclaration E τ) (p a cursor cs stop)
    (success : checkedMemberPack d p a cursor = .ok (cs,stop)) :
    E.pathTy p = some τ ∧ d.pack p a cursor = .ok (cs,stop) := by
  unfold checkedMemberPack at success
  split at success
  · exact ⟨by assumption,success⟩
  · cases success

theorem checkedMemberPack_good {E τ} (d : StorageDeclaration E τ) : FixedPackGood (checkedMemberPack d) := by
  intro p a cursor cs stop success
  exact d.pack_good _ _ _ _ _ (checkedMemberPack_success d p a cursor cs stop success).2

theorem MemberStorageDeclarations.pack_good {E τs} (d : MemberStorageDeclarations E τs) :
    FixedFieldsGood τs.length d.pack := by
  induction d with
  | nil => exact fixedRowsNil_good Source.Step.field
  | @cons τ τs head tail ih =>
    exact packFixedRow_good Source.Step.field (fun _ _ h => Source.Step.field.inj h) τs.length
      (checkedMemberPack head) tail.pack (checkedMemberPack_good head) ih

theorem RootStorageDeclaration.pack_good {E τ} (d : RootStorageDeclaration E τ) : FixedPackGood d.pack := by
  cases d with
  | leaf old => exact old.pack_good
  | strct name fields found members dynamic =>
    exact alignFixedPack_good _ (fixedRows_body_good Source.Step.field _ _ members.pack_good)

theorem FixedDeclaration.no_dynamic_array {E τ} (d : FixedDeclaration E (.array .storage τ none)) : False := by
  cases d with
  | scalar _ supported => cases supported

end Solidity.Yul.Views
