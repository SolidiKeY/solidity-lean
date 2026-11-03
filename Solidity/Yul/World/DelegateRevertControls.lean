import Solidity.Yul.World.DelegateRevertHeap
namespace Solidity.Yul.World.DelegateRevertControls
open Solidity.Source
open Solidity.Roadmap (Word Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StateCall
open Solidity.Yul.World.StateCallPhysical (registry flag)
open Solidity.Yul.World.DelegatePhysical
open Solidity.Yul.World.DelegatePort
open Solidity.Yul.World.DelegateRevertPort

def extraLog : Log := ⟨CallerFrameChecks.target,1,⟨#[0x556677],rfl⟩,[0xc1,0xd2]⟩
def tracePrefix := GeneralReturningChecks.tracePrefix++[.event (.credit CallerFrameChecks.target 5),.log extraLog]
def locals : Locals env.layout [ReturningCall.uint,.bytes .memory,.bytes .memory] :=
  .cons (.int 0x99 (by decide)) (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil))
def functionLocals : Locals env.layout [.bytes .memory,.bytes .memory] := .cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil)
def entry := (StateCallChecks.entry.apply (.account CallerFrameChecks.target (fun a=>{a with nonce:=91}))).apply
  (.account CallerFrameChecks.target id)
def source (G : Glob env) : EMState env [ReturningCall.uint,.bytes .memory,.bytes .memory] :=
  ⟨locals,⟨entry,StateCallChecks.heap G,interactionEvents tracePrefix,
    [(CallerFrameChecks.target,[0x81,0x82]),(CallerFrameChecks.owner,[0x70])],⟨[.bytes .memory,.bytes .memory],functionLocals⟩⟩⟩
def observer : ObservedEffects env.layout env.lay env.lay := ⟨⟨entry,committedLogs tracePrefix,[0xe1,0xe2,0xe3]⟩,tracePrefix,rfl⟩
def residue := residualWrite StateCallChecks.residual (complementKey true CallerFrameChecks.target 13,0x1234)
def encoding := boolEncodingWrite before (ownedByteKey true CallerFrameChecks.target flag,⟨⟨3,by decide⟩,by decide⟩)
def prepare := prepareRepresentedSlot (E:=env) registry registry request encoding
theorem ready : prepare.isSome := by decide
def plan : RepresentedSlotPlan (E:=env) registry registry request encoding := prepare.get ready

def run (G : Glob env) (src size : Word) := DelegateRevertPort.run G 0 (by decide) (source G)
  DelegateChecks.sender DelegateChecks.target DelegateChecks.value 10000 (by decide) rfl residue rfl encoding plan
  (Option.some_get ready).symm observer rfl (StateCallChecks.memory G) 160 4 (StateCallChecks.loaded G)
  (StateCallChecks.placement G) (StateCallChecks.byteEntry G) 1 src size

def expected (G : Glob env) (bytes : Bytes) := HeapOutputTransport.image
  (completed G (source G) residue encoding observer) (StateCallChecks.heap G) (heap_eq G (source G) residue encoding observer)
  (StateCallChecks.placement G) (StateCallChecks.byteEntry G) (StateCallChecks.memory G) 1 bytes

theorem argument (G : Glob env) : run G 4 2=some (.ok (.revert (errorData G)),expected G [0x11,0x22]) := by
  apply argument_copy
  · simp only [StateCallChecks.byteEntry,input_length]
    decide
  · exact (DelegateOutput.reads G).1
  · exact (DelegateOutput.reads G).2

theorem exact_end (G : Glob env) : run G 36 0=some (.ok (.revert (errorData G)),expected G []) := by
  apply exact_end_zero
  · simp only [StateCallChecks.byteEntry,input_length]
    decide
  · exact (DelegateOutput.reads G).1
  · exact (DelegateOutput.reads G).2

theorem invalid_zero (G : Glob env) :
    run G 37 0=some (.ok (.revert (errorData G)),(completed G (source G) residue encoding observer,none)) :=
  out_of_source_zero G 0 (by decide) (source G) DelegateChecks.sender DelegateChecks.target DelegateChecks.value 10000
    (by decide) rfl residue rfl encoding plan (Option.some_get ready).symm observer rfl
    (StateCallChecks.memory G) 160 4 (StateCallChecks.loaded G) (StateCallChecks.placement G) (StateCallChecks.byteEntry G) 1

theorem dirty_prefixes : entry.journal.length=6 ∧ residue.journal.length=2 ∧ encoding.journal.length=2 := ⟨rfl,rfl,rfl⟩

theorem mutation_then_rollback (G : Glob env) :
    ((source G).2.ex.world.accounts account).storage.read flagPath=some (.bool false) ∧
    ((changed (source G) account).2.ex.world.accounts account).storage.read flagPath=some (.bool true) := ⟨rfl,rfl⟩

theorem not_old_caller (G : Glob env) : (source G).2.ex≠(StateCallChecks.caller G).2.ex := by
  intro same
  have impossible:=congrArg (fun x=>x.journal.length) same
  change (6 : Nat)=4 at impossible
  omega

theorem false_caller_observer (G : Glob env) : observer.effects.execution≠(StateCallChecks.caller G).2.ex := not_old_caller G

theorem stale_buffer : returnWindow observer.effects.returndata 4 2=none := rfl
end Solidity.Yul.World.DelegateRevertControls
