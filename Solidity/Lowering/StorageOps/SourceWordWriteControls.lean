import Solidity.Lowering.StorageOps.SourceWordWrite

/-! Actual Source writes and value-free target code with populated contexts.
Static/type/budget/region/operand controls do not claim world rollback. -/
namespace Solidity.Lowering.StorageOps.SourceWordWriteControls
open Solidity.Backend.StorageOps

def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))
def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
 (.cons (.stateVar uintSyntax none none none false "left" .none)
  (.cons (.stateVar uintSyntax none none none false "right" .none)
   (.cons (.stateVar uintSyntax none none none true "scratch" .none) .nil)))) .nil)
def env : Source.Env := unit.env
def left : Source.SPath := ⟨⟨some "C","left"⟩,[]⟩
def right : Source.SPath := ⟨⟨some "C","right"⟩,[]⟩
def scratch : Source.SPath := ⟨⟨some "C","scratch"⟩,[]⟩
def missing : Source.SPath := ⟨⟨some "C","missing"⟩,[]⟩
def address : Roadmap.Address := ⟨7,by decide⟩
def storage : Source.Storage env.layout env.cellTy :=
 ((Source.Storage.empty : Source.Storage env.layout env.cellTy).write left (.int 11 (by decide))).write right (.int 17 (by decide))
def transient : Source.Storage env.layout env.cellTy :=
 (Source.Storage.empty : Source.Storage env.layout env.cellTy).write scratch (.int 41 (by decide))
def state : Source.St env :=
  { ex :=
      { world := ⟨fun a => if a = address then
          { balance := 19, nonce := 3, code := some 0, storage := storage }
          else Source.Account.empty _⟩
        transient := Source.Transient.empty.set address transient
        journal := [] }
    heap := Source.Heap.empty
    events := []
    logs := []
    fnLocals := ⟨[],.nil⟩ }
def initial : Source.Locals env.layout [] × Source.St env := (.nil,state)
def frame : Source.Fr :=
 {this := address,sender := ⟨13,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "C"}
def value : Source.Val env.layout (env.cellTy left) := .int 53 (by decide)
def sourceRun := (Source.storeVal (E:=env) (Γ:=[]) frame 1 (env.cellTy left) left value).run initial
def staticRun := (Source.storeVal (E:=env) (Γ:=[]) {frame with static:=true} 1 (env.cellTy left) left value).run initial
def zeroRun := (Source.storeVal (E:=env) (Γ:=[]) frame 0 (env.cellTy left) left value).run initial
def typeRun := (Source.writeAt (E:=env) (Γ:=[]) frame left (.bool true)).run initial
def scratchValue : Source.Val env.layout (env.cellTy scratch) := .int 53 (by decide)
def scratchRun := (Source.storeVal (E:=env) (Γ:=[]) frame 1 (env.cellTy scratch) scratch scratchValue).run initial
def sourceView (s : Source.St env) :=
 ([SourceArrayDeleteTarget.wordAt frame s.ex left,SourceArrayDeleteTarget.wordAt frame s.ex right,
   (((s.ex.transient.cells frame.this).read scratch).bind Source.Val.word).map Fin.val,
   SourceArrayDeleteTarget.wordAt frame s.ex missing],
 s.ex.journal.length,(s.ex.world.accounts address).balance,
 (s.ex.world.accounts address).nonce,(s.ex.world.accounts address).code,s.events.length,s.logs.length)
def machine : Evm.Machine :=
 { Evm.Machine.init (fun _=>37) (Evm.wmod 43) with
   stack := [.val (Evm.wmod 23),.slot (.root 9)],
   store := .ofFn (fun s => if s=.root 0 then 11 else if s=.root 1 then 17 else if s=.root 9 then 99 else 0),
   mem := fun _=>.val (Evm.wmod 31),bal₀ := fun _=>41,caller := Evm.wmod 47,
   callvalue := Evm.wmod 0,timestamp := Evm.wmod 53,accepts := fun _ _=>false }
def targetAfter (n : Nat) : Evm.Machine := {machine with store := Evm.WordStore.write machine.store (.root 0) n}
def targetRun := Evm.run (StackWordWrite.code (.root 0)) {machine with stack := .val (Evm.wmod 53)::machine.stack}
def wrongOperand := Evm.run (StackWordWrite.code (.root 0)) {machine with stack := .val (Evm.wmod 59)::machine.stack}
def malformedOperand := Evm.run (StackWordWrite.code (.root 0)) {machine with stack := .slot (.root 5)::machine.stack}
def targetView (m : Evm.Machine) :=
 ([m.store (.root 0),m.store (.root 1),m.store (.root 9),m.store (.root 3)],m.stack,m.mem 0,
 m.bal (Evm.wmod 0),m.bal₀ (Evm.wmod 0),m.self,m.caller,m.callvalue,m.timestamp,m.accepts (Evm.wmod 0) (Evm.wmod 0))

def sourceRead := (Source.readAt (E:=env) (Γ:=[]) frame left (env.cellTy left)).run sourceRun.2
def targetRead := Evm.run (TargetOperations.readCode (.root 0)) (targetAfter 53)


theorem certificate :
 sourceRun=(.ok (),(.nil,SourceWordWrite.after frame left value state)) ∧
 targetRun=.ok (targetAfter 53) 0 ∧
 ((sourceRun.2.2.ex.world.accounts frame.this).storage.read left).bind Source.Val.word=some (Evm.wmod 53) ∧
 (targetAfter 53).store.cells (.root 0)=Evm.wmod 53 := by
  exact SourceWordWrite.complete env [] frame left value .nil state rfl rfl 0 (Evm.wmod 53) rfl machine (.root 0)

theorem source_ordered :
 (sourceView state,sourceView sourceRun.2.2,sourceView scratchRun.2.2) =
 (([some 11,some 17,some 41,none],0,19,3,some 0,0,0),([some 53,some 17,some 41,none],1,19,3,some 0,0,0),([some 11,some 17,some 53,none],1,19,3,some 0,0,0)) := by
  rfl

theorem failure_outcomes :
 (staticRun,zeroRun,typeRun) =
 ((.error (.revert []),initial),(.error .timeout,initial),(.error (.stuck "storage cell type"),initial)) := by
  rfl

theorem target_ordered :
 (targetRun,wrongOperand,malformedOperand,targetView machine,targetView (targetAfter 53),targetView (targetAfter 59)) =
 (.ok (targetAfter 53) 0,.ok (targetAfter 59) 0,.fault,([11,17,99,0],[.val (Evm.wmod 23),.slot (.root 9)],.val (Evm.wmod 31),37,41,Evm.wmod 43,Evm.wmod 47,Evm.wmod 0,Evm.wmod 53,false),([53,17,99,0],[.val (Evm.wmod 23),.slot (.root 9)],.val (Evm.wmod 31),37,41,Evm.wmod 43,Evm.wmod 47,Evm.wmod 0,Evm.wmod 53,false),([59,17,99,0],[.val (Evm.wmod 23),.slot (.root 9)],.val (Evm.wmod 31),37,41,Evm.wmod 43,Evm.wmod 47,Evm.wmod 0,Evm.wmod 53,false)) := by
  rfl

theorem readbacks :
 (sourceRead,targetRead) =
 ((.ok value,(.nil,SourceWordWrite.after frame left value state)),
 .ok {targetAfter 53 with stack:=.val (Evm.wmod 53)::machine.stack} 0) := by
  rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceWordWriteControls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceWordWriteControls.source_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_ordered
/-- info: 'Solidity.Lowering.StorageOps.SourceWordWriteControls.failure_outcomes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failure_outcomes
/-- info: 'Solidity.Lowering.StorageOps.SourceWordWriteControls.target_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_ordered
/-- info: 'Solidity.Lowering.StorageOps.SourceWordWriteControls.readbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readbacks
end Solidity.Lowering.StorageOps.SourceWordWriteControls
