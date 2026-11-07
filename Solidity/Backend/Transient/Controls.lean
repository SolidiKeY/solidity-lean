import Solidity.Backend.Transient.Frames

/-! Inhabited G39 target and typed Source controls, with distinct owner/code
identities and nonempty caller storage, heap, local and journal prefixes. -/
namespace Solidity.Backend.Transient.Controls
open Solidity.Backend.Transient

def declaration (name : String) (transient : Bool) : Source.Decl :=
  {kind:=.stateVar,name:=name,scope:=some "P7",top:=false,
   node:=.stateVar (.elem .bool) none none none transient name .none}
def env : Source.Env := ⟨[declaration "saved" false,declaration "scratch" true]⟩
def path : Source.SPath := ⟨⟨some "P7","scratch"⟩,[]⟩
def saved : Source.SPath := ⟨⟨some "P7","saved"⟩,[]⟩
def slot : BoolSlot env := ⟨path,rfl,rfl,⟨7,by decide⟩⟩
def owner : Roadmap.Address := ⟨0x20,by decide⟩
def other : Roadmap.Address := ⟨0x30,by decide⟩
def frame : Source.Fr :=
  { this := owner, sender := other, value := ⟨9,by decide⟩, static := false, contract := "P7" }
def source : Source.EMState env [.bool] :=
  ⟨.cons (.bool true) .nil,
   ⟨⟨⟨fun _ => Source.Account.empty _⟩,Source.Transient.empty,[]⟩,
    (Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [0xa1,0,0xff]⟩).1,
    [.call other ⟨3,by decide⟩ [0x12] false],[(owner,[0x99,0x42])],⟨[.bool],.cons (.bool false) .nil⟩,Source.FailureExecution.Cursor.empty⟩⟩
def prefixedSource : Source.EMState env [.bool] :=
  ⟨source.1,{ source.2 with ex := source.2.ex.run [
    .account owner (fun a => { a with
      balance := 93
      nonce := 4
      code := some 0
      storage := a.storage.write saved (.bool true) }),
    .transient other (fun cells => cells.write path (.bool true))] }⟩
def base : State :=
  ⟨{ Evm.Machine.init with
      stack := [.val ⟨0xa5,by decide⟩]
      store := Evm.WordStore.write Evm.WordStore.zero (.root 7) 0x1234
      mem := fun _ => .val ⟨0x42,by decide⟩ },empty,[]⟩
def target : State := write base other slot.key ⟨0xcc,by decide⟩

theorem initial_relation : Represents slot owner prefixedSource target := ⟨false,rfl,rfl⟩
theorem actual_write :
    (Source.writeAt frame slot.path (.bool true)).run prefixedSource=
      (.ok (),(prefixedSource.1,sourceWrite slot owner true prefixedSource.2)) ∧
    run owner false (storeCode slot.key (boolWord true)) target=
      .ok (write target owner slot.key (boolWord true)) ∧
    Represents slot owner (prefixedSource.1,sourceWrite slot owner true prefixedSource.2)
      (write target owner slot.key (boolWord true)) :=
  compiled_write slot frame rfl true prefixedSource target

theorem nontrivial_prefix :
    prefixedSource.2.ex.journal.length=2 ∧ target.journal.length=1 ∧
    prefixedSource.2.heap.next=1 ∧ (prefixedSource.2.ex.world.accounts owner).balance=93 ∧
    prefixedSource.2.fnLocals=⟨[.bool],.cons (.bool false) .nil⟩ ∧
    target.bank other slot.key=⟨0xcc,by decide⟩ := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem callback_success : callback owner false (storeCode slot.key (boolWord true)) target=
    .ok (write target owner slot.key (boolWord true)) := callback_store owner _ _ target

theorem callback_revert : callback owner false (storeCode slot.key (boolWord true)++emptyRevert) target=
    .error .reverted target := callback_store_revert owner _ _ target

theorem reset_second_transaction :
    (endTx (write target owner slot.key (boolWord true))).bank owner slot.key=boolWord false ∧
    (endTx (write target owner slot.key (boolWord true))).bank other slot.key=boolWord false ∧
    Represents slot owner (prefixedSource.1,{prefixedSource.2 with ex:=prefixedSource.2.ex.endTx})
      (endTx (write target owner slot.key (boolWord true))) :=
  ⟨rfl,rfl,end_represents slot owner prefixedSource _⟩

theorem wrong_owner : target.bank other slot.key≠target.bank owner slot.key := by decide

theorem static_source :
    (Source.writeAt {frame with static:=true} slot.path (.bool true)).run prefixedSource=
      (.error (.revert []),prefixedSource) := write_static slot _ rfl true prefixedSource

theorem nonempty_revert_refused :
    step owner false (.op .REVERT)
      {target with machine:={target.machine with stack:=[.val ⟨0,by decide⟩,.val ⟨1,by decide⟩]}}=
      .error .unsupported {target with machine:={target.machine with stack:=[.val ⟨0,by decide⟩,.val ⟨1,by decide⟩]}} := rfl


theorem unsupported_after_write :
    callback owner false (storeCode slot.key (boolWord true)++[.op .ADD]) target=
      .error .unsupported {write target owner slot.key (boolWord true) with
        machine := {target.machine with stack := []}} := by
  simp only [callback,run_append,store_code,run,step,finish,write]

end Solidity.Backend.Transient.Controls
