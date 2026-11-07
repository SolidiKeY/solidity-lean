import Solidity.Source.CalldataCopyAccess

/-! G18.05 consumers of actual Source local memory conversion/deletion.
No heap-copy/delete implementation, semantics or fuel policy is replaced. -/
namespace Solidity.Source
open EM
variable {E : Env} {Γ : RCtx}

/-- The actual identity conversion preserves the reference, complete caller
state and original allocation history, even at fuel zero. -/
theorem convRV_same_run (F : Fr) (budget : Nat) {τ : STy}
    (value : RVal E.layout τ) (before : EMState E Γ) :
    (convRV F budget τ value).run before = (.ok value,before) := by
  simp only [convRV]
  rfl

/-- Total existing local deletion: the two exhausted budgets retain the
original state; the sufficient branch installs a fresh EMPTY array and
changes only the selected local, retaining every alias to the old object. -/
theorem deleteLocal_array_run (F : Fr) (budget : Nat) (σ : STy)
    (index : Idx Γ (.array .memory σ none)) (before : EMState E Γ) :
    (deleteLoc F budget (.local index)).run before =
      match budget with
      | 0 | 1 => (.error .timeout,before)
      | _+2 => (.ok (),
        (before.1.set index (.memRef rfl before.2.heap.next),
          {before.2 with heap := (before.2.heap.alloc
            ⟨.array .memory σ none,Data.array 0 (fun _ h => nomatch h) Fin.elim0⟩).1})) := by
  cases budget with
  | zero => rfl
  | succ budget => cases budget <;> rfl

/-- Byte-reference deletion follows the same real budget/fresh-identity rule.
Deleting the local does not mutate the old bytes through another alias. -/
theorem deleteLocal_bytes_run (F : Fr) (budget : Nat)
    (index : Idx Γ (.bytes .memory)) (before : EMState E Γ) :
    (deleteLoc F budget (.local index)).run before =
      match budget with
      | 0 | 1 => (.error .timeout,before)
      | _+2 => (.ok (),
        (before.1.set index (.memRef rfl before.2.heap.next),
          {before.2 with heap := (before.2.heap.alloc ⟨.bytes .memory,Data.bytes []⟩).1})) := by
  cases budget with
  | zero => rfl
  | succ budget => cases budget <;> rfl

end Solidity.Source
