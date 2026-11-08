import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarPairedTransport
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDescentControls

/-! The generic frozen-contract consumer has a concrete checked producer and
populated allocator, caller alias and scalar-return client. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPairedTransport.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

theorem inhabited : ∃ last,
 run (image guardCompiled 8 7) ScalarAllocatingDescent.Controls.input=.ok last 0 ∧
 last.stack=[w[77]] ∧ last.mem 0=w[30] ∧ last.mem 8=w[10] ∧ last.mem 2=w[16] ∧
 last.mem 4=w[2] ∧ last.mem 8≠w[16] := by
 have repr : StateRepr 1 2 16 F ScalarAllocatingDescent.Controls.σ CountdownWitness.P.base
     ScalarAllocatingDescent.Controls.input :=
   reserved_write AllocatingScalarTarget.represented 7 (by decide) (by decide) w[10]
 have owned : StructAllocatorRepr ScalarAllocatingDescent.Controls.σ.heap CountdownWitness.P.base 16
     (⟨22,by decide⟩ : Fin W) ScalarAllocatingDescent.Controls.input :=
   AllocatingScalarTarget.ownership.localWrite 7 (by decide) (by decide) w[10]
 obtain ⟨τ,e,down,last,addresses,selected,actual,running,done,lastRepr,size,kept,extended,growth,lastOwner,stack,pointer,reference⟩ :=
   complete guardCompiled producer 2 ScalarAllocatingDescent.Controls.σ (by decide) CountdownWitness.P.r0
     rfl rfl rfl CountdownWitness.P.base ScalarAllocatingDescent.Controls.input repr
     (⟨22,by decide⟩ : Fin W) owned (by decide) 8 8 7 10
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) rfl (by decide) (by decide) (by decide) rfl
 have cursor : last.mem 0=w[30] := lastOwner.arrays.free.cell
 have result := lastRepr.core.vals (.here : Idx (Frame A) (.val .uint))
 have resultWord : last.mem 4=w[2] := Restore.uint_unique result (ReprV.uint_of rfl)
 refine ⟨last,actual,stack,cursor,pointer,reference,resultWord,?_⟩
 rw [pointer];decide

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPairedTransport.Controls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPairedTransport.Controls.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPairedTransport.Controls.inhabited
