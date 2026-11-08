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

/-- An old caller result is saved but must not overwrite the live return. -/
def callerWithResult := σ.setLocal .here (countValue 7 (by decide))
def inputWithResult := writeMachine input 4 w[7]

theorem older_frame (depth : Nat) (enough : 1<depth) :
 ∃ (out : Solidity.Out C callerWithResult.H (Frame A)) (last : Machine) (addresses : Nat → Fin W),
 (source depth).run callerWithResult=.ok out ∧ run image inputWithResult=.ok last 0 ∧
 StateRepr 1 2 16 F out.st addresses last ∧ BaseExtends callerWithResult.H CountdownWitness.P.base addresses ∧
 GrowsAllocator 2 16 4 callerWithResult CountdownWitness.P.base inputWithResult out.st addresses last ∧
 Footprint.Words 8 10 inputWithResult last ∧ last.mem 9=w[99] ∧ last.mem 9≠w[98] ∧
 last.mem 4=w[1] ∧ last.mem 4≠w[7] := by
 have original : StateRepr 1 2 16 F σ CountdownWitness.P.base input :=
   reserved_write AllocatingScalarTarget.represented 7 (by decide) (by decide) w[10]
 have repr : StateRepr 1 2 16 F callerWithResult CountdownWitness.P.base inputWithResult :=
   original.setVal .here (countValue 7 (by decide)) w[7] (ReprV.uint_of rfl)
 have owned : StructAllocatorRepr callerWithResult.heap CountdownWitness.P.base 16 (⟨22,by decide⟩ : Fin W) inputWithResult :=
   (AllocatingScalarTarget.ownership.localWrite 7 (by decide) (by decide) w[10]).localWrite 4 (by decide) (by decide) w[7]
 obtain ⟨out,last,addresses,native,actual,represented,stack,position,reference,countWord,resultWord,owner,extended,growth,olderWords⟩ :=
   framed_endpoint depth 1 callerWithResult (by decide) CountdownWitness.P.r0 rfl rfl CountdownWitness.P.base inputWithResult repr
     (⟨22,by decide⟩ : Fin W) owned (by decide) (by decide) (by decide) rfl enough
 have sentinel : last.mem 9=w[99] := olderWords 9 (by decide) (by decide)
 refine ⟨out,last,addresses,native,actual,represented,extended,growth,olderWords,sentinel,?_,resultWord,?_⟩
 · rw [sentinel];decide
 · rw [resultWord];decide

def startEleven := writeMachine (writeMachine zeroInput 8 w[11]) 10 w[123]

theorem dynamic_zero (depth : Nat) (enough : 0<depth) :
 ∃ (out : Solidity.Out C zeroCaller.H (Frame A)) (last : Machine) (addresses : Nat → Fin W),
 (source depth).run zeroCaller=.ok out ∧ run image startEleven=.ok last 0 ∧
 StateRepr 1 2 16 F out.st addresses last ∧ Footprint.Words 8 11 startEleven last ∧
 (last.stack,[last.mem 0,last.mem 2,last.mem 3,last.mem 4,last.mem 8,last.mem 9,last.mem 10])=
 ([w[77]],[w[22],w[16],w[1],w[0],w[11],w[99],w[123]]) ∧ last.mem 8≠w[10] := by
 have original : StateRepr 1 2 16 F σ CountdownWitness.P.base input :=
   reserved_write AllocatingScalarTarget.represented 7 (by decide) (by decide) w[10]
 have zeroRepr : StateRepr 1 2 16 F zeroCaller CountdownWitness.P.base zeroInput :=
   original.setVal (.there .here) (countValue 1 (by decide)) w[1] (ReprV.uint_of rfl)
 have repr : StateRepr 1 2 16 F zeroCaller CountdownWitness.P.base startEleven :=
   reserved_write (reserved_write zeroRepr 8 (by decide) (by decide) w[11]) 10 (by decide) (by decide) w[123]
 have owned : StructAllocatorRepr zeroCaller.heap CountdownWitness.P.base 16 (⟨22,by decide⟩ : Fin W) startEleven :=
   (((AllocatingScalarTarget.ownership.localWrite 7 (by decide) (by decide) w[10]).localWrite 3
     (by decide) (by decide) w[1]).localWrite 8 (by decide) (by decide) w[11]).localWrite 10 (by decide) (by decide) w[123]
 obtain ⟨out,last,addresses,native,actual,represented,stack,position,reference,countWord,resultWord,owner,extended,growth,olderWords⟩ :=
   dynamic_endpoint depth 0 11 zeroCaller (by decide) CountdownWitness.P.r0 rfl rfl CountdownWitness.P.base startEleven repr
     (⟨22,by decide⟩ : Fin W) owned (by decide) (by decide) (by decide) (by decide) rfl enough
 refine ⟨out,last,addresses,native,actual,represented,olderWords,?_,?_⟩
 · rw [stack,owner.arrays.free.cell,reference,countWord,resultWord,position,olderWords 9 (by decide) (by decide),olderWords 10 (by decide) (by decide)];rfl
 · rw [position];decide

def startNine := writeMachine input 8 w[9]

theorem dynamic_one (depth : Nat) (enough : 1<depth) :
 ∃ (out : Solidity.Out C σ.H (Frame A)) (last : Machine) (addresses : Nat → Fin W),
 (source depth).run σ=.ok out ∧ run image startNine=.ok last 0 ∧
 StateRepr 1 2 16 F out.st addresses last ∧ Footprint.Words 8 9 startNine last ∧
 (last.stack,[last.mem 0,last.mem 2,last.mem 3,last.mem 4,last.mem 8])=
 ([w[77]],[w[26],w[16],w[2],w[1],w[9]]) ∧ last.mem 8≠w[10] := by
 have original : StateRepr 1 2 16 F σ CountdownWitness.P.base input :=
   reserved_write AllocatingScalarTarget.represented 7 (by decide) (by decide) w[10]
 have repr : StateRepr 1 2 16 F σ CountdownWitness.P.base startNine :=
   reserved_write original 8 (by decide) (by decide) w[9]
 have owned : StructAllocatorRepr σ.heap CountdownWitness.P.base 16 (⟨22,by decide⟩ : Fin W) startNine :=
   (AllocatingScalarTarget.ownership.localWrite 7 (by decide) (by decide) w[10]).localWrite 8 (by decide) (by decide) w[9]
 obtain ⟨out,last,addresses,native,actual,represented,stack,position,reference,countWord,resultWord,owner,extended,growth,olderWords⟩ :=
   dynamic_endpoint depth 1 9 σ (by decide) CountdownWitness.P.r0 rfl rfl CountdownWitness.P.base startNine repr
     (⟨22,by decide⟩ : Fin W) owned (by decide) (by decide) (by decide) (by decide) rfl enough
 refine ⟨out,last,addresses,native,actual,represented,olderWords,?_,?_⟩
 · rw [stack,owner.arrays.free.cell,reference,countWord,resultWord,position];rfl
 · rw [position];decide

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls.one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls.one
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls.zero

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls.older_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls.older_frame

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls.dynamic_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls.dynamic_zero
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls.dynamic_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingOuterFamily.Controls.dynamic_one
