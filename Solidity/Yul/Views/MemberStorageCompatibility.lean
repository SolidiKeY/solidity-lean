import Solidity.Yul.Views.MemberStoragePaths

namespace Solidity.Yul.Views

/-- Embed the ENTIRE existing primitive/fixed root certificate. Every original
root remains a leaf; no selector or existing guard/profile is changed. -/
def StorageDeclarations.memberRoots {E ds} (d : StorageDeclarations E ds) : RootMemberDeclarations E ds :=
  StorageDeclarations.casesOn (motive := fun ds _ => RootMemberDeclarations E ds) d
    .nil (fun head tail => .cons (.leaf head) tail.memberRoots)

theorem StorageDeclarations.memberRoots_pack {E ds} (d : StorageDeclarations E ds) : d.memberRoots.pack = d.pack := by
  induction d with
  | nil => rfl
  | @cons root τ rest head tail ih =>
    funext a cursor
    change (if E.rootTy root = some τ then (head.pack ⟨root,[]⟩ a cursor).bind
      (fun first => (tail.memberRoots.pack a first.2).map (fun out => (first.1++out.1,out.2))) else .error .missingRoot) = _
    rw [ih]
    rfl

theorem StorageDeclarations.memberRoots_paths {E ds} (d : StorageDeclarations E ds) : d.memberRoots.paths = d.paths := by
  induction d with
  | nil => rfl
  | @cons root τ rest head tail ih =>
    change head.paths ⟨root,[]⟩ ++ tail.memberRoots.paths = head.paths ⟨root,[]⟩ ++ tail.paths
    rw [ih]

def ComputedStorage.toMembers {E ds d active a} (r : @ComputedStorage E ds d active a) : MemberComputedStorage d.memberRoots active a :=
  ⟨r.origin,r.ordered,r.sourceDistinct,r.distinct,r.registrations,r.endByte,
    by rw [StorageDeclarations.memberRoots_pack]; exact r.packed⟩

theorem ComputedStorage.toMembers_registrations {E ds d active a} (r : @ComputedStorage E ds d active a) :
    r.toMembers.registrations = r.registrations := rfl

end Solidity.Yul.Views
