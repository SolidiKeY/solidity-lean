import Solidity.Yul.Views.SlotTranslation

namespace Solidity.Yul.Views

/-! Additive finite certificates indexed by ACTUAL source types. The Bool marks
aggregate-array occurrence, not primitive dynamic occurrence. Ordinary leaves
retain their exact old checks. No runtime count/depth bound is introduced.
This static packing owns headers; it does not inline referenced array contents. -/
mutual
inductive AggregateStorageDeclaration (E : Source.Env) : Source.STy → Bool → Type where
  | ordinary {τ b} (old : RecursiveStorageDeclaration E τ b) : AggregateStorageDeclaration E τ false
  | strct (name : Source.DeclName) (fields : List (String × Source.STy))
      (found : E.structFields name .storage = some fields)
      (members : AggregateStorageFields E (fields.map Prod.snd) true) :
      AggregateStorageDeclaration E (.struct .storage name) true
  | array {τ b} (child : AggregateStorageDeclaration E τ b) (aggregate : τ.isValue = false) :
      AggregateStorageDeclaration E (.array .storage τ none) true
inductive AggregateStorageFields (E : Source.Env) : List Source.STy → Bool → Type where
  | nil : AggregateStorageFields E [] false
  | cons {τ τs hb tb} (head : AggregateStorageDeclaration E τ hb) (tail : AggregateStorageFields E τs tb) :
      AggregateStorageFields E (τ::τs) (hb || tb)
end

mutual
def AggregateStorageDeclaration.pack {E τ b} (d : AggregateStorageDeclaration E τ b) : FixedPackFn E :=
  AggregateStorageDeclaration.casesOn (motive_1 := fun _ _ _ => FixedPackFn E) d
    (fun old => old.pack) (fun _ _ _ members => alignFixedPack (members.pack 0))
    (fun _ _ => alignFixedPack (uintHeaderCell E).pack)
def AggregateStorageFields.pack {E τs b} (d : AggregateStorageFields E τs b) : Nat → FixedPackFn E :=
  AggregateStorageFields.casesOn (motive_2 := fun _ _ _ => Nat → FixedPackFn E) d
    (fun _ _ _ cursor => .ok ([],cursor))
    (fun {τ _ _ _} head tail => packFixedField
      (fun p a cursor => if E.pathTy p = some τ then head.pack p a cursor else .error .cellMismatch) tail.pack)
end

mutual
def AggregateStorageDeclaration.endByte {E τ b} (d : AggregateStorageDeclaration E τ b) : Nat → Nat :=
  AggregateStorageDeclaration.casesOn (motive_1 := fun _ _ _ => Nat → Nat) d
    (fun old => old.endByte) (fun _ _ _ members cursor => roundSlot (members.endByte (roundSlot cursor)))
    (fun _ _ => (StorageDeclaration.uintArray (E := E)).endByte)
def AggregateStorageFields.endByte {E τs b} (d : AggregateStorageFields E τs b) : Nat → Nat :=
  AggregateStorageFields.casesOn (motive_2 := fun _ _ _ => Nat → Nat) d id
    (fun head tail cursor => tail.endByte (head.endByte cursor))
end

mutual
def AggregateStorageDeclaration.paths {E τ b} (d : AggregateStorageDeclaration E τ b) : Source.SPath → List Source.SPath :=
  AggregateStorageDeclaration.casesOn (motive_1 := fun _ _ _ => Source.SPath → List Source.SPath) d
    (fun old => old.paths) (fun _ _ _ members => members.paths 0) (fun _ _ p => [p])
def AggregateStorageFields.paths {E τs b} (d : AggregateStorageFields E τs b) : Nat → Source.SPath → List Source.SPath :=
  AggregateStorageFields.casesOn (motive_2 := fun _ _ _ => Nat → Source.SPath → List Source.SPath) d
    (fun _ _ => []) (fun head tail i p => head.paths (p.go (.field i)) ++ tail.paths (i+1) p)
end

def checkedAggregatePack {E τ b} (d : AggregateStorageDeclaration E τ b) : FixedPackFn E :=
  fun p a cursor => if E.pathTy p = some τ then d.pack p a cursor else .error .cellMismatch

theorem checkedAggregatePack_success {E τ b} (d : AggregateStorageDeclaration E τ b) (p a cursor cs stop)
    (success : checkedAggregatePack d p a cursor = .ok (cs,stop)) :
    E.pathTy p = some τ ∧ d.pack p a cursor = .ok (cs,stop) := by
  unfold checkedAggregatePack at success
  split at success
  · exact ⟨by assumption,success⟩
  · cases success

mutual
theorem AggregateStorageDeclaration.pack_good {E τ b} (d : AggregateStorageDeclaration E τ b) : FixedPackGood d.pack := by
  cases d with
  | ordinary old => exact old.pack_good
  | strct name fields found members =>
    exact alignFixedPack_good _ (fixedRows_body_good Source.Step.field _ _ members.pack_good)
  | array child aggregate => exact (StorageDeclaration.uintArray (E := E)).pack_good
theorem AggregateStorageFields.pack_good {E τs b} (d : AggregateStorageFields E τs b) : FixedFieldsGood τs.length d.pack := by
  cases d with
  | nil => exact fixedRowsNil_good Source.Step.field
  | @cons τ τs hb tb head tail =>
    have good : FixedPackGood (checkedAggregatePack head) := by
      intro p a cursor cs stop success
      exact head.pack_good _ _ _ _ _ (checkedAggregatePack_success head _ _ _ _ _ success).2
    exact packFixedRow_good Source.Step.field (fun _ _ h => Source.Step.field.inj h) τs.length
      (checkedAggregatePack head) tail.pack good tail.pack_good
end

mutual
theorem AggregateStorageDeclaration.pack_paths {E τ b} (d : AggregateStorageDeclaration E τ b) : FixedPackPaths d.pack d.paths := by
  cases d with
  | ordinary old => exact old.pack_paths
  | strct name fields found members => exact alignFixedPack_paths _ _ (members.pack_paths 0)
  | array child aggregate => exact (StorageDeclaration.uintArray (E := E)).pack_paths
theorem AggregateStorageFields.pack_paths {E τs b} (d : AggregateStorageFields E τs b) (i : Nat) : FixedPackPaths (d.pack i) (d.paths i) := by
  cases d with
  | nil => intro p a cursor cs stop success; cases success; rfl
  | cons head tail =>
    have good : FixedPackPaths (checkedAggregatePack head) head.paths := by
      intro p a cursor cs stop success
      exact head.pack_paths _ _ _ _ _ (checkedAggregatePack_success head _ _ _ _ _ success).2
    exact packFixedRow_paths Source.Step.field (checkedAggregatePack head) tail.pack head.paths tail.paths good tail.pack_paths i
end

end Solidity.Yul.Views
