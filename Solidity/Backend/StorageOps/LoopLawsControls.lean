import Solidity.Backend.StorageOps.LoopLaws
import Solidity.Backend.StorageOps.TargetArrayClear

/-! Populated intrinsic-machine controls for the shared loop adapters.
No Source execution, bytecode/gas or world rollback claim. -/
namespace Solidity.Backend.StorageOps.LoopLawsControls

def initial : Evm.Machine :=
 { Evm.Machine.init (fun _ => 37) (Evm.wmod 43) with
   stack := [.val (Evm.wmod 23),.slot (.root 9)],
   store := .ofFn (fun s => if s=.root 0 then 11 else 0),
   mem := fun _ => .val (Evm.wmod 17), bal₀ := fun _ => 41,
   accepts := fun _ _ => false, caller := Evm.wmod 47,
   callvalue := Evm.wmod 0, timestamp := Evm.wmod 53 }
def after : Evm.Machine := { initial with stack := .val (Evm.wmod 99)::initial.stack }
def yes : List Evm.Instr := [.push (.val (Evm.wmod 1))]
def no : List Evm.Instr := [.push (.val (Evm.wmod 0))]
def body : List Evm.Instr := [.push (.val (Evm.wmod 99))]
def pending : List Evm.Instr := [.jump 1]
def malformed : List Evm.Instr := [.push (.slot (.root 5))]
def view (m : Evm.Machine) :=
 (m.stack,m.store (.root 0),m.mem 0,m.bal (Evm.wmod 0),m.bal₀ (Evm.wmod 0),
  m.self,m.accepts (Evm.wmod 0) (Evm.wmod 0),m.caller,m.callvalue,m.timestamp)


theorem ordered_cases :
 (Evm.loopTurn (Evm.run yes) (Evm.run body) initial,
 Evm.loopTurn (Evm.run no) (Evm.run pending) initial,
 Evm.loopTurn (Evm.run yes) (Evm.run pending) initial,
 Evm.loopTurn (Evm.run malformed) (Evm.run body) initial,
 Solidity.Backend.StorageOps.TargetArrayClear.condition,view initial,view after) =
 (.inl after,.inr (.ok initial 0),.inr .fault,.inr .fault,
 [.dup 2,.dup 2,.lt],([.val (Evm.wmod 23),.slot (.root 9)],11,.val (Evm.wmod 17),37,41,Evm.wmod 43,false,Evm.wmod 47,Evm.wmod 0,Evm.wmod 53),([.val (Evm.wmod 99),.val (Evm.wmod 23),.slot (.root 9)],11,.val (Evm.wmod 17),37,41,Evm.wmod 43,false,Evm.wmod 47,Evm.wmod 0,Evm.wmod 53)) := by
  rfl

theorem single_loop_actual :
 Evm.run [.loop no pending] initial = .ok initial 0 := by
  exact LoopLaws.run_single_loop _ _ _ _ (Evm.loopRun_of_iterN (n:=1) rfl)

/-- info: 'Solidity.Backend.StorageOps.LoopLawsControls.ordered_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ordered_cases
/-- info: 'Solidity.Backend.StorageOps.LoopLawsControls.single_loop_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms single_loop_actual
end Solidity.Backend.StorageOps.LoopLawsControls
