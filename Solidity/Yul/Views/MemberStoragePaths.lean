import Solidity.Yul.Views.RootMemberTrace

namespace Solidity.Yul.Views

def MemberStorageDeclarations.paths {E τs} (d : MemberStorageDeclarations E τs) : Nat → Source.SPath → List Source.SPath :=
  MemberStorageDeclarations.casesOn (motive := fun _ _ => Nat → Source.SPath → List Source.SPath) d
    (fun _ _ => []) (fun head tail index p => head.paths (p.go (.field index)) ++ tail.paths (index+1) p)

theorem checkedMemberPack_paths {E τ} (d : StorageDeclaration E τ) : FixedPackPaths (checkedMemberPack d) d.paths := by
  intro p a cursor cs stop success
  exact d.pack_paths _ _ _ _ _ (checkedMemberPack_success d p a cursor cs stop success).2

theorem MemberStorageDeclarations.pack_paths {E τs} (d : MemberStorageDeclarations E τs) (i : Nat) :
    FixedPackPaths (d.pack i) (d.paths i) := by
  induction d generalizing i with
  | nil => intro p a cursor cs stop success; cases success; rfl
  | cons head tail ih =>
    exact packFixedRow_paths Source.Step.field (checkedMemberPack head) tail.pack head.paths tail.paths (checkedMemberPack_paths head) ih i

def RootStorageDeclaration.paths {E τ} (d : RootStorageDeclaration E τ) : Source.SPath → List Source.SPath :=
  RootStorageDeclaration.casesOn (motive := fun _ _ => Source.SPath → List Source.SPath) d
    (fun old => old.paths) (fun _ _ _ members _ => members.paths 0)

theorem RootStorageDeclaration.pack_paths {E τ} (d : RootStorageDeclaration E τ) : FixedPackPaths d.pack d.paths := by
  cases d with
  | leaf old => exact old.pack_paths
  | strct name fields found members dynamic => exact alignFixedPack_paths _ _ (members.pack_paths 0)

def RootMemberDeclarations.paths {E ds} (d : RootMemberDeclarations E ds) : List Source.SPath :=
  RootMemberDeclarations.casesOn (motive := fun _ _ => List Source.SPath) d []
    (fun {root _ _} head tail => head.paths ⟨root,[]⟩ ++ tail.paths)

theorem RootMemberDeclarations.pack_paths {E ds} (d : RootMemberDeclarations E ds) (a : Roadmap.Address)
    (cursor cs stop) (success : d.pack a cursor = .ok (cs,stop)) : cs.map ScalarPath.path = d.paths := by
  induction d generalizing cursor cs stop with
  | nil => cases success; rfl
  | @cons root τ rest head tail ih =>
    simp only [RootMemberDeclarations.pack_cons] at success
    split at success
    · cases first : head.pack ⟨root,[]⟩ a cursor with
      | error reason => simp only [first,Except.bind] at success; cases success
      | ok result =>
        rcases result with ⟨left,middle⟩
        cases second : tail.pack a middle with
        | error reason => simp only [first,second,Except.bind,Except.map] at success; cases success
        | ok result =>
          rcases result with ⟨right,last⟩
          simp only [first,second,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
          obtain ⟨rfl,rfl⟩ := success
          rw [List.map_append,head.pack_paths _ _ _ _ _ first,ih _ _ _ second]
          rfl
    · cases success

theorem RootMemberDeclarations.pack_end {E ds} (d : RootMemberDeclarations E ds) (a : Roadmap.Address)
    (cursor cs stop) (success : d.pack a cursor = .ok (cs,stop)) : stop = d.endByte cursor := by
  induction d generalizing cursor cs stop with
  | nil => cases success; rfl
  | @cons root τ rest head tail ih =>
    simp only [RootMemberDeclarations.pack_cons] at success
    split at success
    · cases first : head.pack ⟨root,[]⟩ a cursor with
      | error reason => simp only [first,Except.bind] at success; cases success
      | ok result =>
        rcases result with ⟨left,middle⟩
        cases second : tail.pack a middle with
        | error reason => simp only [first,second,Except.bind,Except.map] at success; cases success
        | ok result =>
          rcases result with ⟨right,last⟩
          simp only [first,second,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
          obtain ⟨rfl,rfl⟩ := success
          change last = tail.endByte (head.endByte cursor)
          rw [ih _ _ _ second,head.pack_end _ _ _ _ _ first]
    · cases success

end Solidity.Yul.Views

namespace Solidity.Yul.Views

theorem MemberComputedStorage.coverage {E ds d active a} (r : @MemberComputedStorage E ds d active a) :
    r.registrations.map ScalarPath.path = d.paths := d.pack_paths a _ _ _ r.packed

theorem MemberComputedStorage.paths_unique {E ds d active a} (r : @MemberComputedStorage E ds d active a) :
    d.paths.Nodup := by
  rw [← r.coverage]
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp (fun separated => separated.1) r.separated

theorem MemberComputedStorage.end_exact {E ds d active a} (r : @MemberComputedStorage E ds d active a) :
    r.endByte = d.endByte (r.origin.persistent.val*32) := d.pack_end a _ _ _ r.packed

end Solidity.Yul.Views
