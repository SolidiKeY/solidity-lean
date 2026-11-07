import Solidity.Lowering.Readonly.StaticJournal

/-! Guard vacuous journal witnesses built only from empty storage or self/zero
transfers. A funded amount-three transfer between distinct accounts changes both
balances while preserving an actual persistent Bool cell. Credit is observed
through its actual Source EM run. History remains an algebraic certificate;
these witnesses do not establish arbitrary call execution or physical frames. -/
namespace Solidity.H62.ReadonlyAudit.JournalWitnesses
open Solidity.Source
open Solidity.Lowering.Readonly.StaticJournal

def flag : Decl := ⟨.stateVar, "flag", none, false,
  .stateVar (.elem .bool) none none none false "flag" .none⟩
def environment : Env := ⟨[flag]⟩
def sender : Solidity.Roadmap.Address := ⟨0, by decide⟩
def receiver : Solidity.Roadmap.Address := ⟨1, by decide⟩
def amount : Solidity.Roadmap.Word := ⟨3, by decide⟩
def state : St environment :=
  { ex := { world := ⟨fun a =>
        { (Account.empty (D := environment.layout) (environment.lay a)).withBalance
            (if a = sender then 9 else 1) with
          storage := (Storage.empty : Storage environment.layout (environment.lay a)).write flag.path (.bool true) }⟩
            transient := ⟨fun _ => Storage.empty⟩, journal := [] }
    heap := Heap.empty, events := [], logs := [], fnLocals := ⟨[], .nil⟩ }
def final : ExecState environment.layout environment.lay environment.lay :=
  (state.ex.apply (.account sender (fun account => account.withBalance 6))).apply
    (.account receiver (fun account => account.withBalance 4))
def credited : St environment :=
  { state with ex := state.ex.apply (.account receiver (fun account => account.withBalance 4)) }

theorem transfer_joint : state.ex.transfer sender receiver amount = some final ∧
    History state.ex true final :=
  ⟨rfl, transfer_history state.ex final sender receiver amount true rfl⟩

theorem storage_joint : History state.ex true final ∧ (true = true) ∧ SameStorage final state.ex :=
  ⟨transfer_joint.2, rfl, History.storage transfer_joint.2 rfl⟩

theorem credit_joint : History state.ex true
    ((credit receiver amount : EM environment [.bool] Unit).run (.cons (.bool false) .nil, state)).2.2.ex :=
  credit_history receiver amount (.cons (.bool false) .nil) state true

theorem credit_observed :
    (credit receiver amount : EM environment [.bool] Unit).run (.cons (.bool false) .nil, state) =
      (.ok (), (.cons (.bool false) .nil, credited)) := rfl

theorem transfer_balances :
    (final.world.accounts sender).balance = 6 ∧ (final.world.accounts receiver).balance = 4 :=
  ⟨rfl, rfl⟩

theorem preserved_flag :
    (final.world.accounts sender).storage.read flag.path = some (.bool true) := by
  rw [storage_joint.2.2 sender]
  rfl

/-- A balance-changing transfer is not whole-world equality. -/
theorem unchanged_world_refused : final ≠ state.ex := by
  intro same
  have observed := congrArg (fun s : ExecState environment.layout environment.lay environment.lay =>
    (s.world.accounts sender).balance) same
  have different : (final.world.accounts sender).balance ≠ (state.ex.world.accounts sender).balance := by decide
  exact different observed

/-- Preserving an actual typed cell excludes replacement by its false default. -/
theorem erased_flag_refused :
    (final.world.accounts sender).storage.read flag.path ≠ some (.bool false) := by
  rw [preserved_flag]
  intro same
  cases same

end Solidity.H62.ReadonlyAudit.JournalWitnesses
