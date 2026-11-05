import Solidity.Yul.Views.RecursiveStorageTrace

namespace Solidity.Yul.Views

def MemberStorageDeclarations.toRecursive {E τs} (d : MemberStorageDeclarations E τs) : RecursiveStorageFields E τs d.hasDynamic :=
  MemberStorageDeclarations.casesOn (motive := fun τs d => RecursiveStorageFields E τs d.hasDynamic) d
    .nil (fun head tail => .cons (.leaf head) tail.toRecursive)

def RootStorageDeclaration.dynamicFlag {E τ} (d : RootStorageDeclaration E τ) : Bool :=
  RootStorageDeclaration.casesOn (motive := fun _ _ => Bool) d (fun old => old.primitiveDynamic) (fun _ _ _ _ _ => true)

def RootStorageDeclaration.toRecursive {E τ} (d : RootStorageDeclaration E τ) : RecursiveStorageDeclaration E τ d.dynamicFlag :=
  RootStorageDeclaration.casesOn (motive := fun τ d => RecursiveStorageDeclaration E τ d.dynamicFlag) d
    (fun old => .leaf old) (fun name fields found members dynamic => .strct name fields found (dynamic ▸ members.toRecursive))

theorem RecursiveStorageFields.cast_pack {E τs b c} (d : RecursiveStorageFields E τs b) (h : b = c) : (h ▸ d).pack = d.pack := by cases h; rfl
theorem RecursiveStorageFields.cast_paths {E τs b c} (d : RecursiveStorageFields E τs b) (h : b = c) : (h ▸ d).paths = d.paths := by cases h; rfl
theorem RecursiveStorageFields.cast_end {E τs b c} (d : RecursiveStorageFields E τs b) (h : b = c) : (h ▸ d).endByte = d.endByte := by cases h; rfl
theorem RecursiveStorageFields.cast_headers {E τs b c} (d : RecursiveStorageFields E τs b) (h : b = c) : (h ▸ d).headers = d.headers := by cases h; rfl

theorem MemberStorageDeclarations.toRecursive_pack {E τs} (d : MemberStorageDeclarations E τs) : d.toRecursive.pack = d.pack := by
  induction d with
  | nil => rfl
  | cons head tail ih =>
    funext i p a cursor
    change packFixedField (checkedMemberPack head) tail.toRecursive.pack i p a cursor = _
    rw [ih]
    rfl

theorem MemberStorageDeclarations.toRecursive_paths {E τs} (d : MemberStorageDeclarations E τs) : d.toRecursive.paths = d.paths := by
  induction d with
  | nil => rfl
  | cons head tail ih =>
    funext i p
    change head.paths (p.go (.field i)) ++ tail.toRecursive.paths (i+1) p = _
    rw [ih]
    rfl

theorem MemberStorageDeclarations.toRecursive_end {E τs} (d : MemberStorageDeclarations E τs) : d.toRecursive.endByte = d.endByte := by
  induction d with
  | nil => rfl
  | cons head tail ih =>
    funext cursor
    change tail.toRecursive.endByte (head.endByte cursor) = _
    rw [ih]
    rfl

theorem MemberStorageDeclarations.toRecursive_headers {E τs} (d : MemberStorageDeclarations E τs) : d.toRecursive.headers = d.headers := by
  induction d with
  | nil => rfl
  | cons head tail ih =>
    funext i p cursor
    change head.pathHeaders (p.go (.field i)) cursor ++ tail.toRecursive.headers (i+1) p (head.endByte cursor) = _
    rw [ih]
    rfl

theorem RootStorageDeclaration.toRecursive_pack {E τ} (d : RootStorageDeclaration E τ) : d.toRecursive.pack = d.pack := by
  cases d with
  | leaf old => rfl
  | strct name fields found members dynamic =>
    change alignFixedPack ((dynamic ▸ members.toRecursive).pack 0) = alignFixedPack (members.pack 0)
    rw [RecursiveStorageFields.cast_pack,members.toRecursive_pack]

theorem RootStorageDeclaration.toRecursive_paths {E τ} (d : RootStorageDeclaration E τ) : d.toRecursive.paths = d.paths := by
  cases d with
  | leaf old => rfl
  | strct name fields found members dynamic =>
    change (dynamic ▸ members.toRecursive).paths 0 = members.paths 0
    rw [RecursiveStorageFields.cast_paths,members.toRecursive_paths]

theorem RootStorageDeclaration.toRecursive_end {E τ} (d : RootStorageDeclaration E τ) : d.toRecursive.endByte = d.endByte := by
  cases d with
  | leaf old => rfl
  | strct name fields found members dynamic =>
    exact congrArg (fun f : Nat → Nat => fun cursor => roundSlot (f (roundSlot cursor)))
      ((RecursiveStorageFields.cast_end members.toRecursive dynamic).trans members.toRecursive_end)

theorem RootStorageDeclaration.toRecursive_headers {E τ} (d : RootStorageDeclaration E τ) : d.toRecursive.headers = d.headers := by
  cases d with
  | leaf old => rfl
  | strct name fields found members dynamic =>
    funext p cursor
    change (dynamic ▸ members.toRecursive).headers 0 p (roundSlot cursor) = members.headers 0 p (roundSlot cursor)
    rw [RecursiveStorageFields.cast_headers,members.toRecursive_headers]

end Solidity.Yul.Views
