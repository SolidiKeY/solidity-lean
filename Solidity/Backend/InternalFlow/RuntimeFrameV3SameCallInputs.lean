import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveScopeClient

/-! A successful checked empty-array rebinding preparation produces a second
represented input for the SAME recursive call and argument expression.
These are pre-failure states, not states returned by a failed execution. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.SameCallInputs
noncomputable section
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client (Γ F reference)
abbrev C := CountdownWitness.P.C
abbrev A := CountdownWitness.A
abbrev origin := ScalarContinuation.final
abbrev initialBase := ScalarContinuation.finalBase
abbrev before := ScalarContinuation.target

def length : Simple C Γ .uint := .lit 0 rfl
def preparation : Stmt C Γ Γ := .rebindMem reference (.newArr length rfl)
def compiled : CompiledStmt 1 F preparation := (Memory.compileStmt 1 F preparation).get (by rfl)
def checked : Calls.Statement 1 F preparation := Calls.plainStmt compiled

theorem root : Memory.compileStmt 1 F preparation=some compiled := rfl
theorem code : checked.code=rebindNewCode 1 reference length := rfl

def size : Fin W := ⟨0,by decide⟩
def fresh := (origin.alloc (defaultArray .uint size)).2
def caller := (origin.alloc (defaultArray .uint size)).1.setLocal reference (some fresh)
def addresses := upd initialBase origin.H.length (⟨26,by decide⟩ : Fin W)
def machine := writeMachine (allocateMachine before (⟨26,by decide⟩ : Fin W) size)
 (cellOf 1 reference) w[26]
def output : Solidity.Out C origin.H Γ := ⟨caller,List.prefix_append _ _⟩

theorem reached : preparation.run origin=.ok output ∧
 run checked.code before=.ok machine 0 ∧ StateRepr 1 1 16 F caller addresses machine ∧
 StructAllocatorRepr caller.heap addresses 16 (⟨27,by decide⟩ : Fin W) machine ∧
 machine.stack=before.stack ∧ Footprint.Words 8 16 before machine := by
 exact Footprint.rebind ScalarContinuation.endpoint.2.2.1 ScalarContinuation.allocation_facts.2.2.1
   (by decide) .uint reference length rfl size rfl (by decide) (lo:=8) (by decide)

theorem exact_cost : checked.cost origin=1 := rfl

theorem capacity : AllocationInput 1 16 (checked.cost origin) origin initialBase before :=
 .inr ⟨by decide,⟨26,by decide⟩,ScalarContinuation.allocation_facts.2.2.1,by decide⟩

theorem checked_execution : GrowingResult 1 1 16 (checked.cost origin) checked.frag origin initialBase before
 (preparation.run origin) (run checked.code before) :=
 checked.sound ScalarContinuation.endpoint.2.2.1 (by decide) capacity

theorem bases_preserved : BaseExtends origin.H initialBase addresses :=
 fun ref => allocationBase_old initialBase (⟨26,by decide⟩ : Fin W) ref

theorem growth : GrowsAllocator 1 16 1 origin initialBase before caller addresses machine := by
 intro cursor positive owner space
 have same : cursor=(⟨26,by decide⟩ : Fin W) :=
   Word.val.inj (owner.arrays.free.cell.symm.trans ScalarContinuation.allocation_facts.2.2.1.arrays.free.cell)
 subst cursor
 exact reached.2.2.2.1

theorem count_fails : ScalarReentry.count.evalT caller=.error .revert := by
 with_unfolding_all rfl

theorem cursor : machine.mem 9=w[10] :=
 (reached.2.2.2.2.2 9 (by decide) (by decide)).trans ScalarReentry.prefix_cursor

end
end Solidity.Backend.InternalFlow.RuntimeFrame.SameCallInputs
