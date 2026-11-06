import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingOuterFamily

/-! Populated zero- and one-allocation members of the same outer-call image.
These witness the family premises, not general compiler/profile closure. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent
abbrev σ := OuterAllocatingCall.σ
abbrev input := OuterAllocatingCall.input

theorem one (depth : Nat) (enough : 1<depth) :
 ∃ (out : Solidity.Out C σ.H (Frame A)) (last : Machine) (addresses : Nat → Fin W),
 (source depth).run σ=.ok out ∧ run image input=.ok last 0 ∧ StateRepr 1 2 16 F out.st addresses last ∧
 (last.stack,[last.mem 0,last.mem 2,last.mem 3,last.mem 4,last.mem 8])=
 ([w[77]],[w[26],w[16],w[2],w[1],w[10]]) ∧ last.mem 4≠w[2] ∧ run image input≠.revert := by
 have repr : StateRepr 1 2 16 F σ CountdownWitness.P.base input :=
   reserved_write AllocatingScalarTarget.represented 7 (by decide) (by decide) w[10]
 have owned : StructAllocatorRepr σ.heap CountdownWitness.P.base 16 (⟨22,by decide⟩ : Fin W) input :=
   AllocatingScalarTarget.ownership.localWrite 7 (by decide) (by decide) w[10]
 obtain ⟨out,last,addresses,native,actual,represented,stack,position,refWord,countWord,resultWord,owner⟩ :=
   endpoint depth 1 σ (by decide) CountdownWitness.P.r0 rfl rfl CountdownWitness.P.base input repr
     (⟨22,by decide⟩ : Fin W) owned (by decide) (by decide) (by decide) rfl enough
 refine ⟨out,last,addresses,native,actual,represented,?_,?_,?_⟩
 · rw [stack,owner.arrays.free.cell,refWord,countWord,resultWord,position];rfl
 · rw [resultWord];decide
 · rw [actual];intro bad;cases bad

def zeroCaller := σ.setLocal (.there .here) (countValue 1 (by decide))
def zeroInput := writeMachine input 3 w[1]

theorem zero (depth : Nat) (enough : 0<depth) :
 ∃ (out : Solidity.Out C zeroCaller.H (Frame A)) (last : Machine) (addresses : Nat → Fin W),
 (source depth).run zeroCaller=.ok out ∧ run image zeroInput=.ok last 0 ∧
 StateRepr 1 2 16 F out.st addresses last ∧
 (last.stack,[last.mem 0,last.mem 2,last.mem 3,last.mem 4,last.mem 8])=
 ([w[77]],[w[22],w[16],w[1],w[0],w[10]]) := by
 have original : StateRepr 1 2 16 F σ CountdownWitness.P.base input :=
   reserved_write AllocatingScalarTarget.represented 7 (by decide) (by decide) w[10]
 have repr : StateRepr 1 2 16 F zeroCaller CountdownWitness.P.base zeroInput :=
   original.setVal (.there .here) (countValue 1 (by decide)) w[1] (ReprV.uint_of rfl)
 have owned : StructAllocatorRepr zeroCaller.heap CountdownWitness.P.base 16 (⟨22,by decide⟩ : Fin W) zeroInput :=
   (AllocatingScalarTarget.ownership.localWrite 7 (by decide) (by decide) w[10]).localWrite 3 (by decide) (by decide) w[1]
 obtain ⟨out,last,addresses,native,actual,represented,stack,position,refWord,countWord,resultWord,owner⟩ :=
   endpoint depth 0 zeroCaller (by decide) CountdownWitness.P.r0 rfl rfl CountdownWitness.P.base zeroInput repr
     (⟨22,by decide⟩ : Fin W) owned (by decide) (by decide) (by decide) rfl enough
 refine ⟨out,last,addresses,native,actual,represented,?_⟩
 rw [stack,owner.arrays.free.cell,refWord,countWord,resultWord,position];rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls.one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls.one
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls.zero
