import Solidity.Yul.Views.RecursiveStorageDeclaration

namespace Solidity.Yul.Views

def checkedRecursivePack {E τ b} (d : RecursiveStorageDeclaration E τ b) : FixedPackFn E :=
  fun p a cursor => if E.pathTy p = some τ then d.pack p a cursor else .error .cellMismatch

theorem checkedRecursivePack_success {E τ b} (d : RecursiveStorageDeclaration E τ b) (p a cursor cs stop)
    (success : checkedRecursivePack d p a cursor = .ok (cs,stop)) :
    E.pathTy p = some τ ∧ d.pack p a cursor = .ok (cs,stop) := by
  unfold checkedRecursivePack at success
  split at success
  · exact ⟨by assumption,success⟩
  · cases success

mutual
theorem RecursiveStorageDeclaration.pack_good {E τ b} (d : RecursiveStorageDeclaration E τ b) : FixedPackGood d.pack := by
  cases d with
  | leaf old => exact old.pack_good
  | strct name fields found members =>
    exact alignFixedPack_good _ (fixedRows_body_good Source.Step.field _ _ members.pack_good)
theorem RecursiveStorageFields.pack_good {E τs b} (d : RecursiveStorageFields E τs b) : FixedFieldsGood τs.length d.pack := by
  cases d with
  | nil => exact fixedRowsNil_good Source.Step.field
  | @cons τ τs hb tb head tail =>
    have good : FixedPackGood (checkedRecursivePack head) := by
      intro p a cursor cs stop success
      exact head.pack_good _ _ _ _ _ (checkedRecursivePack_success head _ _ _ _ _ success).2
    exact packFixedRow_good Source.Step.field (fun _ _ h => Source.Step.field.inj h) τs.length
      (checkedRecursivePack head) tail.pack good tail.pack_good
end

mutual
theorem RecursiveStorageDeclaration.pack_paths {E τ b} (d : RecursiveStorageDeclaration E τ b) : FixedPackPaths d.pack d.paths := by
  cases d with
  | leaf old => exact old.pack_paths
  | strct name fields found members => exact alignFixedPack_paths _ _ (members.pack_paths 0)
theorem RecursiveStorageFields.pack_paths {E τs b} (d : RecursiveStorageFields E τs b) (i : Nat) : FixedPackPaths (d.pack i) (d.paths i) := by
  cases d with
  | nil => intro p a cursor cs stop success; cases success; rfl
  | cons head tail =>
    have good : FixedPackPaths (checkedRecursivePack head) head.paths := by
      intro p a cursor cs stop success
      exact head.pack_paths _ _ _ _ _ (checkedRecursivePack_success head _ _ _ _ _ success).2
    exact packFixedRow_paths Source.Step.field (checkedRecursivePack head) tail.pack head.paths tail.paths good tail.pack_paths i
end

end Solidity.Yul.Views
