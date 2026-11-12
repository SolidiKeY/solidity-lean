import Solidity.Yul.World.TransientTargetRollback
import Solidity.Yul.World.TransientTargetControls
namespace Solidity.Yul.World.TransientTarget.RollbackControls
open Views Solidity.Backend
open Views.Controls Views.TransientSlotControls
open Solidity.Yul.World.TransientTarget.Controls

def decorated : Source.EMState rootEnv [.bool] :=
  ⟨.cons (.bool true) .nil,
    {caller.1.2.2 with
      heap := (Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [0xa1,0,0xff]⟩).1
      events := [.call account 0 [0x12,0x34] false]
      logs := [(account,[0xa5,0x5a])]
      fnLocals := ⟨[.bool],.cons (.bool false) .nil⟩}⟩
def first := (transientSlotStore? (ps:=ps) (ts:=ts) frame 0 rawB decorated caller.2).get (by decide)
def second := (transientSlotStore? (ps:=ps) (ts:=ts) frame 99 rawMax first.1.2 first.2).get (by decide)

theorem nonempty_entry : decorated.2.heap.next = 1 ∧ decorated.2.ex.journal.length = 2 ∧
    caller.2.journal.length = 2 ∧ target.journal.length = 1 ∧
    decorated.1 = .cons (.bool true) .nil ∧
    decorated.2.fnLocals = ⟨[.bool],.cons (.bool false) .nil⟩ := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem actual_two_stores : store (ps:=ps) (ts:=ts) frame 0 rawB decorated caller.2 target =
    some (first,.ok (Transient.write target account 0 rawB)) ∧
    store (ps:=ps) (ts:=ts) frame 99 rawMax first.1.2 first.2
      (Transient.write target account 0 rawB) =
    some (second,.ok (Transient.write (Transient.write target account 0 rawB) account 99 rawMax)) := by
  exact ⟨rfl,rfl⟩

theorem actual_changed_journals : second.1.2.2.ex.journal.length = 4 ∧ second.2.journal.length = 4 ∧
    transientSlotLoad ts ⟨second.1.2.2.ex,second.2⟩ account 0 = some rawB ∧
    transientSlotLoad ts ⟨second.1.2.2.ex,second.2⟩ account 99 = some rawMax := by
  decide

theorem full_enclosing_rollback : (let entry : ResidualCompanion rootEnv.layout rootEnv.lay rootEnv.lay complementCarrierOwnership :=
       ⟨decorated.2.ex,caller.2⟩
     let restored := companionRollback (companionEnter entry frame.this frame.sender frame.value frame.cd frame.static)
       ⟨second.1.2.2.ex,second.2⟩
     ((second.1.2.1,{second.1.2.2 with ex := restored.source}),restored.residual,
       Transient.rollback target.journal.length
         (Transient.write (Transient.write target account 0 rawB) account 99 rawMax)) =
       (decorated,caller.2,target)) := by
  exact (store_two_outer_rollback frame 0 rawB decorated caller.2 target first
      (by simp only [first, Option.some_get]; rfl) 99 rawMax second (by simp only [second, Option.some_get]) rfl).2.2

theorem wrong_mark_keeps_mutation : (Transient.rollback (target.journal.length + 2)
    (Transient.write (Transient.write target account 0 rawB) account 99 rawMax)).bank account 0 ≠
      target.bank account 0 := by
  decide
end Solidity.Yul.World.TransientTarget.RollbackControls
