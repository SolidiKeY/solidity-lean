import Solidity.Backend.InternalFlow.RuntimeFrameV3ArgumentEntry
import Solidity.Backend.Executable.ConstructorArgumentControls

/-! Constructor argument preparation consumes the published checked declaration
compiler and reached caller frame. No new instruction selector, frame semantics,
Source admission, constructor-body or executable-byte theorem is introduced. -/
namespace Solidity.Backend.Executable.ConstructorFrameSelection
open Solidity Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
namespace Prior
abbrev A := ArgumentEntry.Checks.A
abbrev Γ := ArgumentEntry.Checks.Γ
abbrev checked := ArgumentEntry.Checks.checked
abbrev caller := ArgumentEntry.Checks.caller
end Prior
abbrev C := CountdownWitness.P.C
abbrev Γ := RecursiveSource.Parameters Prior.A ++ Prior.Γ
abbrev F := Prior.checked.frag
def caller : State C Γ := Prior.caller.withEnv
  (TEnv.append (RecursiveSource.Parameters Prior.A) MemoryArgument.child.env Prior.caller.env)
def args : Args C Γ [.val .uint,.val .uint] :=
  ConstructorLocalArguments.targetArgs Source.IntTy.u8 Source.IntTy.u8
    (.here : Idx Γ (.val .uint)) (.there (.there .here))
def program : Prog C Γ ([.val .uint,.val .uint] ++ Γ) := args.declsThen .nil

def values : TEnv C caller.H [.val .uint,.val .uint] :=
  (PrimTy.ofLit .uint 9 rfl,(PrimTy.ofLit .uint 1 rfl,()))

theorem arguments : args.evalT caller = .ok values := by rfl

def checked : Calls.Program 1 F program :=
  (Calls.compile 1 F program).get (by decide +kernel)

theorem public_selection : Calls.compile 1 F program = some checked :=
  (Option.some_get _).symm

theorem code_eq : checked.code = [.mload 5,.mstore 6,.mload 3,.mstore 7] := by rfl

theorem need_eq : checked.need = 7 := by decide +kernel

theorem room : 1 + checked.need ≤ 16 := by decide +kernel

theorem insufficient_room : ¬ 1 + checked.need ≤ 7 := by decide +kernel

theorem cost_zero : checked.cost caller = 0 :=
  checked.zeroCost (by decide +kernel) caller

theorem capacity : AllocationInput 1 16 (checked.cost caller) caller
    ArgumentEntry.Checks.addresses ArgumentEntry.Checks.target := .inl cost_zero

def declared := caller.withEnv (TEnv.append [.val .uint,.val .uint] values caller.env)

theorem declared_run : program.run caller = .ok ⟨declared,List.prefix_refl _⟩ :=
  ArgumentEntry.source args caller values arguments

theorem caller_restored : declared.drop (Ext.append Γ [.val .uint,.val .uint]) = caller :=
  ArgumentEntry.retained caller values

def target := writeMachine (writeMachine ArgumentEntry.Checks.target 6 w[1]) 7 w[9]

theorem target_run : run checked.code ArgumentEntry.Checks.target = .ok target 0 := by
  rw [code_eq]
  rfl

/-- Both the complete declaration frame and the restricted caller frame are
reached on the same physical output. Capacity is derived from selection. -/
theorem endpoint : ∃ addresses,
    StateRepr 1 1 16 checked.frag declared addresses target ∧
    StateRepr 1 1 16 (checked.frag.restrict Γ) caller addresses target ∧
    target.stack = ArgumentEntry.Checks.target.stack ∧
    BaseExtends caller.H ArgumentEntry.Checks.addresses addresses ∧
    GrowsAllocator 1 16 (checked.cost caller) caller ArgumentEntry.Checks.addresses
      ArgumentEntry.Checks.target declared addresses target := by
  obtain ⟨m,addresses,executed,full,retained,stack,extended,growth⟩ :=
    ArgumentEntry.endpoint args checked caller values arguments
      ArgumentEntry.Checks.addresses ArgumentEntry.Checks.target
      ArgumentEntry.Checks.specification.1 room capacity
  have same : m = target := (Evm.Out.ok.inj (executed.symm.trans target_run)).1
  subst m
  exact ⟨addresses,full,retained,stack,extended,growth⟩

/-- Distinct arguments and a populated protected caller stack. -/
theorem observations : target.mem 6 = w[1] ∧ target.mem 7 = w[9] ∧
    target.stack = [w[77]] := by decide +kernel

theorem wrong_order : ¬ (target.mem 6 = w[9] ∧ target.mem 7 = w[1]) := by
  decide +kernel

/-- Includes the old caller locals, both old arrays and their contents. -/
theorem preserved_contents :
    [target.mem 1,target.mem 2,target.mem 3,target.mem 4,target.mem 5,
      target.mem 16,target.mem 17,target.mem 18,target.mem 20,target.mem 21] =
    [w[20],w[16],w[9],w[20],w[1],w[2],w[7],w[9],w[1],w[4]] := by
  decide +kernel

end Solidity.Backend.Executable.ConstructorFrameSelection
