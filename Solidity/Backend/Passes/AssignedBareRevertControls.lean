import Solidity.Backend.Passes.AssignedBareRevert

/-! Actual typed assignment before the published callee-OOB bare-revert
producer. Every old alias/object, cursor and saved stack is observed before
failure; no failed final machine or restored-world state is invented. -/
namespace Solidity.Backend.Passes.AssignedBareRevert.Controls
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.InternalFlow.RuntimeFrame

abbrev C := V3BareRevertProducer.Checks.P.C
abbrev Γ := V3BareRevertProducer.Checks.P.Γ
abbrev F := V3BareRevertProducer.Checks.F
def dst : Idx Γ (.val .uint) := .here
def before := V3BareRevertProducer.Checks.caller.setLocal dst (V3BareRevertProducer.Checks.P.uint 0 (by decide))
def machine := writeMachine V3BareRevertProducer.Checks.machine 3 w[0]
def operand : Val C Γ .uint := .simple (.lit 9 rfl)
def valueCode : CompiledVal 0 F operand := ⟨Evm.compileVal 0 operand,.core _ rfl⟩
def prefixCode := assignmentStage dst operand valueCode
def code := prefixCode.code ++ (V3BareRevertProducer.plan V3BareRevertProducer.Checks.callSelected 8 8).code
def cells : List Nat := [3,2,1,0,8,9,16,17,18,20,21]
def initialWords : List Word := [w[0],w[16],w[16],w[20],w[10],w[0],w[2],w[7],w[9],w[1],w[4]]
def reachedWords : List Word := [w[9],w[16],w[16],w[20],w[10],w[0],w[2],w[7],w[9],w[1],w[4]]
def target (tail : List Word) := writeMachine {machine with stack := tail} 3 w[9]

theorem initial_repr : StateRepr 1 0 16 F before V3BareRevertProducer.Checks.P.base machine :=
  V3BareRevertProducer.Checks.initial.setVal dst (V3BareRevertProducer.Checks.P.uint 0 (by decide)) w[0] (ReprV.uint_of rfl)
theorem evaluated : operand.evalT before = .ok (V3BareRevertProducer.Checks.P.uint 9 (by decide)) := rfl
theorem source_revert :
    V3BareRevertProducer.Checks.call.run (before.setLocal dst (V3BareRevertProducer.Checks.P.uint 9 (by decide))) = .error .revert :=
  V3BareRevertProducer.Checks.call_source

def instantiated : type_of% (AssignedBareRevert.reached dst operand valueCode initial_repr
    (V3BareRevertProducer.Checks.P.uint 9 (by decide)) evaluated V3BareRevertProducer.Checks.call V3BareRevertProducer.Checks.callSelected 8 8 10
    (by decide) (by decide) (by simpa only [Nat.zero_add] using V3BareRevertProducer.Checks.metadata.2.1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl (.inl (V3BareRevertProducer.Checks.callSelected.checked.zeroCost V3BareRevertProducer.Checks.metadata.2.2.2 _)) source_revert) :=
  AssignedBareRevert.reached dst operand valueCode initial_repr
    (V3BareRevertProducer.Checks.P.uint 9 (by decide)) evaluated V3BareRevertProducer.Checks.call V3BareRevertProducer.Checks.callSelected 8 8 10
    (by decide) (by decide) (by simpa only [Nat.zero_add] using V3BareRevertProducer.Checks.metadata.2.1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl (.inl (V3BareRevertProducer.Checks.callSelected.checked.zeroCost V3BareRevertProducer.Checks.metadata.2.2.2 _)) source_revert

theorem joined_source :
    (Prog.cons (.assignLocal dst operand) (.cons V3BareRevertProducer.Checks.call .nil)).run before = .error .revert :=
  instantiated.1

/-- Canonical actual written word is fixed before every saved tail. -/
theorem physical (tail : List Word) :
    prefixCode.Input 1 16 V3BareRevertProducer.Checks.P.base before {machine with stack := tail} ∧
    run prefixCode.code {machine with stack := tail} = .ok (target tail) 0 ∧
    MappedOutput prefixCode 1 16 V3BareRevertProducer.Checks.P.base before {machine with stack := tail}
      V3BareRevertProducer.Checks.caller (target tail) V3BareRevertProducer.Checks.P.base ∧
    V3BareRevertProducer.admitted V3BareRevertProducer.Checks.callSelected 8 8 1 16 V3BareRevertProducer.Checks.caller V3BareRevertProducer.Checks.P.base (target tail) 10 ∧
    run (V3BareRevertProducer.plan V3BareRevertProducer.Checks.callSelected 8 8).code (target tail) = .revert ∧
    run code {machine with stack := tail} = .revert := by
  obtain ⟨word,repr,runs⟩ := instantiated.2
  have fixed : word = w[9] := Restored.value_unique repr (ReprV.uint_of rfl)
  subst word
  exact runs tail

theorem initial_observations : cells.map machine.mem = initialWords := rfl

theorem reached_observations (tail : List Word) :
    (cells.map (target tail).mem,(target tail).stack) = (reachedWords,tail) := rfl

theorem prefix_instructions : prefixCode.code = [.push w[9],.mstore 3] := by
  first | rfl | decide +kernel

/-- Skipping the real assignment cannot satisfy the actual right-hand Input
at the reached caller whose primitive local is nine. -/
theorem skipped_assignment :
    ¬ V3BareRevertProducer.admitted V3BareRevertProducer.Checks.callSelected 8 8 1 16 V3BareRevertProducer.Checks.caller V3BareRevertProducer.Checks.P.base machine 10 := by
  intro missing
  have observed := missing.represented.core.vals (.here : Idx Γ (.val .uint))
  have bad : (w[0] : Word) = w[9] :=
    Restored.value_unique observed (ReprV.uint_of rfl)
  exact (by decide : (w[0] : Word) ≠ w[9]) bad

theorem wrong_cursor (tail : List Word) :
    ¬ V3BareRevertProducer.admitted V3BareRevertProducer.Checks.callSelected 8 8 1 16 V3BareRevertProducer.Checks.caller V3BareRevertProducer.Checks.P.base (target tail) 11 := by
  intro bad
  have same : (w[10] : Word) = w[11] := bad.cursor
  exact (by decide : (w[10] : Word) ≠ w[11]) same

theorem insufficient_frame (tail : List Word) :
    ¬ V3BareRevertProducer.admitted V3BareRevertProducer.Checks.callSelected 8 8 1 14 V3BareRevertProducer.Checks.caller V3BareRevertProducer.Checks.P.base (target tail) 10 := by
  intro bad
  have room : 10 + 5 ≤ 14 := bad.reserve
  omega

/-- A later callee failure does not erase the successful assignment prefix. -/
theorem prefix_not_revert (tail : List Word) :
    run prefixCode.code {machine with stack := tail} ≠ .revert := by
  rw [(physical tail).2.1]
  intro impossible
  cases impossible

/-- Existing producer source evidence also records its inner valid write37
before the later out-of-bounds failure. It supplies no failed target machine or world rollback. -/
theorem inner_source_write :
    V3BareRevertProducer.Checks.firstWrite.run V3BareRevertProducer.Checks.caller = .ok ⟨V3BareRevertProducer.Checks.changed,List.prefix_refl _⟩ :=
  V3BareRevertProducer.Checks.prefix_source

end Solidity.Backend.Passes.AssignedBareRevert.Controls
