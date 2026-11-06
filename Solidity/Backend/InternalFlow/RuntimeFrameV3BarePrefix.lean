import Solidity.Backend.InternalFlow.RuntimeFrameV3BareRevertProducer

/-! Successful checked prefixes followed by the published bare-revert frame
producer. Reached representation/capacity are derived, not supplied. This
component says nothing about a failed State, rollback or payload bytes. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.BarePrefix
open Evm Evm.Memory

theorem after_prefix {C : Contract} {Γ Δ Ξ : Ctx} {b L frame : Nat} {F : Frag Γ}
 {P : Prog C Γ Δ} {statement : Stmt C Δ Ξ}
 (before : Composition.Program b F P)
 (failure : Composition.Program b before.checked.frag (.cons statement .nil))
 (σ : State C Γ) (base : Nat → Fin W) (machine : Machine)
 (represented : StateRepr L b frame F σ base machine)
 (out : Solidity.Out C σ.H Δ) (source : P.run σ=.ok out)
 (failed : statement.run out.st=.error .revert)
 (lo pointer start : Nat) (prefixRoom : b+before.checked.need≤lo)
 (callerRoom : b+Δ.length≤lo) (resultRoom : b+Ξ.length≤lo)
 (bodyRoom : b+failure.checked.need≤lo)
 (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame)
 (payloadAbove : lo≤start) (reserve : start+(Δ.length+1)≤frame)
 (separate : pointer<start ∨ start+(Δ.length+1)≤pointer)
 (fits : start+(Δ.length+1)<W) (cursor : machine.mem pointer=.val (wmod start))
 (capacity : AllocationInput b frame (before.checked.cost σ+failure.checked.cost out.st) σ base machine) :
 ∃ reached addresses,
 run before.checked.code machine=.ok reached 0 ∧
 StateRepr L b frame before.checked.frag out.st addresses reached ∧
 InterfaceV1.Entry (V3BareRevertProducer.plan failure lo pointer) L b frame before.checked.frag out.st addresses reached start ∧
 run (V3BareRevertProducer.plan failure lo pointer).code reached=.revert ∧
 run (before.checked.code++(V3BareRevertProducer.plan failure lo pointer).code) machine=.revert := by
 have input := capacity.of_le (show before.checked.cost σ≤before.checked.cost σ+failure.checked.cost out.st by omega)
 obtain ⟨reached,addresses,executed,repr,stack,extended,growth,words⟩ :=
   Composition.endpoint before represented prefixRoom (by omega) input out source
 have next := growth.nextInput capacity
 have nextCursor : reached.mem pointer=.val (wmod start) :=
   (words pointer pointerAbove pointerBelow).trans cursor
 have admitted : V3BareRevertProducer.admitted failure lo pointer L frame out.st addresses reached start :=
   ⟨repr,callerRoom,resultRoom,bodyRoom,pointerAbove,pointerBelow,payloadAbove,reserve,separate,fits,nextCursor,next⟩
 have entry := V3BareRevertProducer.coverage failure lo pointer L frame out.st addresses reached start admitted
 have reverted := V3BareRevertProducer.bare_revert failure lo pointer L frame out.st addresses reached start entry failed
 exact ⟨reached,addresses,executed,repr,entry,reverted,(Evm.run_append_ok executed).trans reverted⟩

namespace Checks
namespace B
abbrev C := V3BareRevertProducer.Checks.P.C
abbrev Γ := V3BareRevertProducer.Checks.P.Γ
abbrev F := V3BareRevertProducer.Checks.F
abbrev base := V3BareRevertProducer.Checks.P.base
abbrev caller := V3BareRevertProducer.Checks.caller
abbrev machine := V3BareRevertProducer.Checks.machine
abbrev call := V3BareRevertProducer.Checks.call
abbrev selected := V3BareRevertProducer.Checks.callSelected
end B

def successful : Prog B.C B.Γ B.Γ := .cons (.assignLocal .here (.simple (.lit 2 rfl))) .nil
def selected : Composition.Program 0 B.F successful :=
 Composition.cons (Composition.assign B.F .here (.simple (.lit 2 rfl)) ⟨_,.core _ rfl⟩) (Composition.nil 0 B.F)
def caller := B.caller.setLocal (.here : Idx B.Γ (.val .uint)) (V3BareRevertProducer.Checks.P.uint 2 (by decide))

theorem public_prefix_selection : Mutation.compileProgram 0 B.F successful=some selected := by rfl

theorem prefix_source : successful.run B.caller=.ok ⟨caller,List.prefix_refl _⟩ := by rfl

theorem failure_source : B.call.run caller=.error .revert := by with_unfolding_all rfl

theorem capacity : AllocationInput 0 16 (selected.checked.cost B.caller+B.selected.checked.cost caller) B.caller B.base B.machine := by
 apply Or.inl
 have noalloc := B.selected.checked.zeroCost V3BareRevertProducer.Checks.metadata.2.2.2 caller
 change 0+B.selected.checked.cost caller=0
 exact noalloc

theorem endpoint : ∃ reached addresses,
 run selected.checked.code B.machine=.ok reached 0 ∧
 StateRepr 1 0 16 selected.checked.frag caller addresses reached ∧
 InterfaceV1.Entry (V3BareRevertProducer.plan B.selected 8 8) 1 0 16 selected.checked.frag caller addresses reached 10 ∧
 run (V3BareRevertProducer.plan B.selected 8 8).code reached=.revert ∧
 run (selected.checked.code++(V3BareRevertProducer.plan B.selected 8 8).code) B.machine=.revert := by
 apply after_prefix selected B.selected B.caller B.base B.machine V3BareRevertProducer.Checks.initial
   ⟨caller,List.prefix_refl _⟩ prefix_source failure_source 8 8 10
   (by decide) (by decide) (by decide) (by simpa only [Nat.zero_add] using V3BareRevertProducer.Checks.metadata.2.1)
   (by decide) (by decide) (by decide) (by decide) (.inl (by decide)) (by decide) rfl capacity

def reached := writeMachine B.machine 3 w[2]

theorem prefix_target : run selected.checked.code B.machine=.ok reached 0 := by rfl

theorem reached_entry : ∃ addresses,
 StateRepr 1 0 16 selected.checked.frag caller addresses reached ∧
 InterfaceV1.Entry (V3BareRevertProducer.plan B.selected 8 8) 1 0 16 selected.checked.frag caller addresses reached 10 ∧
 run (V3BareRevertProducer.plan B.selected 8 8).code reached=.revert := by
 obtain ⟨actual,addresses,prefixRun,repr,entry,bodyRun,whole⟩ := endpoint
 have same : actual=reached := (Evm.Out.ok.inj (prefixRun.symm.trans prefix_target)).1
 subst actual
 exact ⟨addresses,repr,entry,bodyRun⟩

theorem combined_revert : run (selected.checked.code++(V3BareRevertProducer.plan B.selected 8 8).code) B.machine=.revert :=
 endpoint.choose_spec.choose_spec.2.2.2.2

theorem ordered_prefix_words :
 (reached.stack,[reached.mem 0,reached.mem 1,reached.mem 2,reached.mem 3,reached.mem 8,
 reached.mem 16,reached.mem 17,reached.mem 18,reached.mem 20,reached.mem 21])=
 ([w[77]],[w[20],w[16],w[16],w[2],w[10],w[2],w[7],w[9],w[1],w[4]]) := by decide +kernel

theorem source_sequence : (.cons (.assignLocal .here (.simple (.lit 2 rfl))) (.cons B.call .nil) : Prog B.C B.Γ B.Γ).run B.caller=.error .revert := by
 with_unfolding_all rfl

theorem wrong_scalar : reached.mem 3≠w[9] := by decide +kernel

theorem other_halt (halt : THalt) (different : halt≠.revert) : B.call.run caller≠.error halt := by
 intro other
 exact different (Except.error.inj (failure_source.symm.trans other)).symm

theorem not_fault : run (selected.checked.code++(V3BareRevertProducer.plan B.selected 8 8).code) B.machine≠.fault := by
 rw [combined_revert]
 intro impossible;cases impossible

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.BarePrefix

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.BarePrefix.after_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Backend.InternalFlow.RuntimeFrame.BarePrefix.after_prefix
