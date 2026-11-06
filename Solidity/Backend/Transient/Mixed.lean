import Solidity.Backend.Transient.WordControls

/-! Actual ordinary target writes between transient writes. This is an existing
Evm.exec regression; Source memory/layout and G42 call composition remain open. -/
namespace Solidity.Backend.Transient.Mixed
open Solidity.Backend.Transient

def code : List Evm.Instr :=
  [.push (.val ⟨0x5566,by decide⟩),.push (.slot (.root 7)),.sstore,
   .push (.val ⟨0xa1ff,by decide⟩),.mstore 3]
def afterMachine (m : Evm.Machine) : Evm.Machine :=
  { m with
    store := Evm.WordStore.write m.store (.root 7) 0x5566
    mem := Evm.upd m.mem 3 (.val ⟨0xa1ff,by decide⟩) }

theorem ordinary_run (s : State) : ordinary code s=.ok (afterMachine s.machine) 0 := rfl

def execute (s : State) : Option State :=
  resumeOrdinary s (ordinary code s)

theorem execute_exact (s : State) :
    execute s=some ⟨afterMachine s.machine,s.bank,s.journal⟩ := rfl

def before : State := write
  {Controls.target with machine := frameMachine Controls.frame Controls.target.machine}
  Controls.owner Controls.slot.key ⟨0xde,by decide⟩
def after : State := ⟨afterMachine before.machine,before.bank,before.journal⟩

theorem mixed_snapshot :
    execute before=some after ∧
    after.machine.store (.root 7)=0x5566 ∧ after.machine.mem 3=.val ⟨0xa1ff,by decide⟩ ∧
    after.bank Controls.owner Controls.slot.key=⟨0xde,by decide⟩ ∧
    after.bank Controls.other Controls.slot.key=⟨0xcc,by decide⟩ ∧
    after.journal.length=2 := by
  refine ⟨rfl,?_,?_,?_,?_,rfl⟩
  · exact Evm.WordStore.write_same _ _ _
  · change Evm.upd before.machine.mem 3 (Evm.Word.val ⟨0xa1ff,by decide⟩) 3=_
    exact Evm.upd_same before.machine.mem 3 (Evm.Word.val ⟨0xa1ff,by decide⟩)
  · change put Controls.target.bank Controls.owner Controls.slot.key ⟨0xde,by decide⟩ Controls.owner Controls.slot.key=_
    exact put_same Controls.target.bank Controls.owner Controls.slot.key ⟨0xde,by decide⟩
  · change put Controls.target.bank Controls.owner Controls.slot.key ⟨0xde,by decide⟩ Controls.other Controls.slot.key=_
    rw [put_other Controls.target.bank Controls.owner Controls.other Controls.slot.key Controls.slot.key ⟨0xde,by decide⟩ (Or.inl (by decide))]
    exact put_same Controls.base.bank Controls.other Controls.slot.key ⟨0xcc,by decide⟩

theorem reset_keeps_ordinary :
    (endTx after).machine.store (.root 7)=0x5566 ∧
    (endTx after).machine.mem 3=.val ⟨0xa1ff,by decide⟩ ∧
    (endTx after).bank Controls.owner Controls.slot.key=⟨0,by decide⟩ ∧
    (endTx after).journal=[] :=
  ⟨mixed_snapshot.2.1,mixed_snapshot.2.2.1,rfl,rfl⟩
end Solidity.Backend.Transient.Mixed
