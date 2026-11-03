import Solidity.Yul.Views.Controls

/-! Controls through the actual typed source world, not a shadow state. -/
namespace Solidity.Yul.Views.Controls

def allBool : Source.SPath → Source.STy := fun _ => .bool
def perAccount : Roadmap.Address → Source.SPath → Source.STy := fun _ => allBool
def root : Source.SPath := ⟨⟨some "Assembly", "flag"⟩, []⟩
def account : Roadmap.Address := ⟨1, by decide⟩
def initial : Source.ExecState layout perAccount perAccount :=
  ⟨⟨fun _ => Source.Account.empty allBool⟩, Source.Transient.empty, []⟩
def persistentWrite : Source.Op layout perAccount perAccount :=
  .account account fun a => {a with storage := a.storage.write root (.bool true)}
def transientWrite : Source.Op layout perAccount perAccount :=
  .transient account fun s => s.write root (.bool true)
def writes := [persistentWrite, transientWrite]

theorem source_write_effects :
    ((initial.run writes).world.accounts account).storage.read root = some (.bool true) ∧
    ((initial.run writes).transient.cells account).read root = some (.bool true) := by
  constructor <;> rfl

theorem source_reset_effects :
    (((initial.run writes).endTx.world.accounts account).storage.read root = some (.bool true)) ∧
    (((initial.run writes).endTx.transient.cells account).read root = some (.bool false)) := by
  constructor <;> rfl

theorem source_rollback_effects :
    (initial.enter account account 0 [] false).rollback (initial.run writes) = initial :=
  Source.rollback_run initial writes account account 0 [] false

theorem residual_slot_readback :
    saveSlot (fun _ => 9) 999 42 999 = 42 ∧ saveSlot (fun _ => 9) 999 42 998 = 9 := by decide

#print axioms source_write_effects
#print axioms source_reset_effects
#print axioms source_rollback_effects

end Solidity.Yul.Views.Controls
