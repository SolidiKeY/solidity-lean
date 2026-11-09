import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingQuotations

/-! Internal caller transport for failure after actual argument entry and
allocation. The same represented prefix supplies reached capacity; the
existing callee failure image is consumed. No failed state or rollback is
reconstructed, and no general failure-path compiler is introduced. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ArgumentCalleeFailure
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes
abbrev A : RefTy := CountdownWitness.A

set_option backward.isDefEq.respectTransparency false in
theorem after_arguments {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
 (name : Name) (args : Args C Γ (Parameters A))
 (checked : Calls.Program b F (args.declsThen .nil)) (σ : State C Γ)
 (n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (evaluated : args.evalT σ=.ok (countValue (n+1) fit,(some ref,())))
 (failed : ArrayProbe.value.evalT (σ.withEnv (Δ:=Parameters A) (countValue (n+1) fit,(some ref,())))=.error .revert)
 (base : Nat → Fin W) (before : Machine) (initial : StateRepr L b frame F σ base before)
 (prefixRoom : b+checked.need≤frame) (bodyRoom : b+Γ.length+3≤frame)
 (capacity : AllocationInput b frame (checked.cost σ+4) σ base before) (pointer bottom : Nat) :
 ∃ (mid : Machine) (addresses : Nat → Fin W),
 run checked.code before=.ok mid 0 ∧
 StateRepr L (b+Γ.length) frame (Frag.init (Parameters A))
   (σ.withEnv (Δ:=Parameters A) (countValue (n+1) fit,(some ref,()))) addresses mid ∧
 StateRepr L b frame (checked.frag.restrict Γ) σ addresses mid ∧ mid.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧
 AllocationInput (b+Γ.length) frame 4 (σ.withEnv (Δ:=Parameters A) (countValue (n+1) fit,(some ref,()))) addresses mid ∧
 (∀ depth,(InterfaceV1.recursiveSource name args .none AllocatingActivation.step (depth+1)).run σ=.error .revert) ∧
 (∀ suffix, run (checked.code++(AllocatingReturn.image (C:=C) (b+Γ.length) (Frag.init (Parameters A)) pointer bottom++suffix)) before=.revert) := by
 obtain ⟨mid,addresses,executed,full,caller,stack,extended,growth⟩ :=
   ArgumentEntry.endpoint args checked σ _ evaluated base before initial prefixRoom (AllocatingArguments.prefix_input capacity)
 have parameters := parameter_projection (tail:=Γ) full
 change StateRepr L (b+Γ.length) frame (Frag.init (Parameters A))
   (σ.withEnv (TEnv.take (Parameters A) (TEnv.append (Parameters A) (countValue (n+1) fit,(some ref,())) σ.env))) addresses mid at parameters
 rw [AllocatingZero.take_parameters] at parameters
 have reached := growth.nextInput capacity
 have bodyCapacity : AllocationInput (b+Γ.length) frame 4
     (σ.withEnv (Δ:=Parameters A) (countValue (n+1) fit,(some ref,()))) addresses mid := by
   rcases reached with zero | ⟨positive,cursor,owner,room⟩
   · cases zero
   · exact .inr ⟨by omega,cursor,owner,room⟩
 have callee : run (AllocatingReturn.image (C:=C) (b+Γ.length) (Frag.init (Parameters A)) pointer bottom) mid=.revert := by
   rcases bodyCapacity with zero | ⟨positive,cursor,owner,room⟩
   · cases zero
   · exact AllocatingFailure.target_image _ n fit ref rfl rfl failed addresses mid parameters cursor owner positive room bodyRoom pointer bottom
 refine ⟨mid,addresses,executed,parameters,caller,stack,extended,bodyCapacity,?_,?_⟩
 · intro depth
   exact AllocatingFailure.call_failure name args σ depth n fit ref evaluated failed
 · intro suffix
   exact (run_append_ok executed).trans (run_append_revert callee)

namespace Checks
open CountdownWitness
abbrev Γ := MemoryArgument.Γ
abbrev F := MemoryArgument.F
abbrev caller := MemoryArgument.caller
abbrev input := MemoryArgument.input

def args : Args P.C Γ (Parameters A) :=
 .snoc (.snocMemory .nil A (.user "alias") (.var (.there (.there .here)) rfl)) .uint (.user "count") (.simple (.lit 3 rfl))
def child := caller.withEnv (Δ:=Parameters A) (countValue 3 (by decide),(some Evm.Memory.CompileExamples.r1,()))

theorem args_succeed : args.evalT caller=.ok child.env := rfl

theorem read_fails : ArrayProbe.value.evalT child=.error .revert := by
 apply (HeapDomain.failure_iff child 2 (by decide) Evm.Memory.CompileExamples.r1 rfl rfl).2
 change CountdownWitness.callee.heap.len Evm.Memory.CompileExamples.r1 .dyn≤2
 rw [HeapDomain.Checks.length_one]
 decide

def program : Prog P.C Γ (Parameters A++Γ) := args.declsThen .nil
def checked : Calls.Program 1 F program := (Calls.compile 1 F program).get (by decide +kernel)
theorem public_selection : Calls.compile 1 F program=some checked := (Option.some_get _).symm
theorem code_eq : checked.code=[.mload 1,.mstore 4,.push w[3],.mstore 5] := rfl
theorem need_eq : checked.need=5 := by decide +kernel
theorem cost_zero : checked.cost caller=0 := checked.zeroCost (by decide +kernel) caller

theorem total_capacity : AllocationInput 1 16 (checked.cost caller+4) caller P.base input :=
 .inr ⟨by decide,⟨22,by decide⟩,MemoryArgument.ownership,by rw [cost_zero];decide⟩

def entry := writeMachine (writeMachine input 4 w[20]) 5 w[3]
theorem entry_run : run checked.code input=.ok entry 0 := by rw [code_eq];rfl

theorem available : ∃ (mid : Machine) (addresses : Nat → Fin W),
 run checked.code input=.ok mid 0 ∧ StateRepr 1 4 16 CountdownWitness.F child addresses mid ∧
 StateRepr 1 1 16 (checked.frag.restrict Γ) caller addresses mid ∧ mid.stack=input.stack ∧
 BaseExtends caller.H P.base addresses ∧ AllocationInput 4 16 4 child addresses mid ∧
 (∀ depth,(InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step (depth+1)).run caller=.error .revert) ∧
 (∀ suffix,run (checked.code++(AllocatingReturn.image (C:=P.C) 4 CountdownWitness.F 8 7++suffix)) input=.revert) :=
 after_arguments "allocatingCountdown" args checked caller 2 (by decide) Evm.Memory.CompileExamples.r1 args_succeed read_fails
   P.base input MemoryArgument.initial (by rw [need_eq];decide) (by decide) total_capacity 8 7

noncomputable def midpoint := available.choose
noncomputable def addresses := available.choose_spec.choose

theorem specification :
 run checked.code input=.ok midpoint 0 ∧ StateRepr 1 4 16 CountdownWitness.F child addresses midpoint ∧
 StateRepr 1 1 16 (checked.frag.restrict Γ) caller addresses midpoint ∧ midpoint.stack=input.stack ∧
 BaseExtends caller.H P.base addresses ∧ AllocationInput 4 16 4 child addresses midpoint ∧
 (∀ depth,(InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step (depth+1)).run caller=.error .revert) ∧
 (∀ suffix,run (checked.code++(AllocatingReturn.image (C:=P.C) 4 CountdownWitness.F 8 7++suffix)) input=.revert) :=
 available.choose_spec.choose_spec

theorem same_midpoint : midpoint=entry := (Evm.Out.ok.inj (specification.1.symm.trans entry_run)).1

theorem represented : StateRepr 1 4 16 CountdownWitness.F child addresses entry := by
 rw [←same_midpoint]
 exact specification.2.1

theorem owned : StructAllocatorRepr child.heap addresses 16 (⟨22,by decide⟩ : Fin W) entry := by
 have capacity := specification.2.2.2.2.2.1
 rw [same_midpoint] at capacity
 rcases capacity with zero | ⟨positive,cursor,owner,room⟩
 · cases zero
 · have same : cursor=(⟨22,by decide⟩ : Fin W) := by
     have word := owner.arrays.free.cell
     change w[22]=.val cursor at word
     exact (Word.val.inj word).symm
   subst cursor
   exact owner

def allocated := AllocatingActivation.allocated child
noncomputable def allocatedAddresses := upd addresses child.H.length (⟨22,by decide⟩ : Fin W)
def reached := writeMachine (allocateMachine entry (⟨22,by decide⟩ : Fin W) AllocatingActivation.size) 6 w[22]

/-- A successful source/target intermediate before the failure, not an Out
reconstructed from revert. The private allocation binder is then dropped. -/
theorem allocation :
 (DomainTransport.scopedNew .bool AllocatingActivation.lengthExpr).run child=.ok ⟨allocated,AllocatingActivation.extension child⟩ ∧
 run (declareNewCode 4 (AllocatingActivation.lengthExpr (C:=P.C))) entry=.ok reached 0 ∧
 StateRepr 1 4 16 CountdownWitness.F allocated allocatedAddresses reached ∧
 StructAllocatorRepr allocated.heap allocatedAddresses 16 (⟨26,by decide⟩ : Fin W) reached ∧ reached.stack=entry.stack := by
 obtain ⟨source,target,repr,owner,stack,words⟩ := Footprint.declare represented owned (by decide)
   .bool AllocatingActivation.lengthExpr rfl AllocatingActivation.size rfl (by decide) (lo:=8) (by decide) (by decide)
 exact ⟨DomainTransport.scoped_source child .bool AllocatingActivation.lengthExpr AllocatingActivation.size rfl,
   target,repr.drop (.push .refl),owner,stack⟩

/-- The observed allocation machine is reached after the SAME real argument
code, rather than paired with a separate initial-machine execution. -/
theorem before_failure_target :
 run (checked.code++declareNewCode 4 (AllocatingActivation.lengthExpr (C:=P.C))) input=.ok reached 0 :=
 (run_append_ok entry_run).trans allocation.2.1

theorem allocation_observations :
 (reached.stack,[reached.mem 0,reached.mem 1,reached.mem 2,reached.mem 3,reached.mem 4,reached.mem 5,reached.mem 6,
 reached.mem 7,reached.mem 8,reached.mem 9,reached.mem 16,reached.mem 17,reached.mem 18,reached.mem 20,reached.mem 21,
 reached.mem 22,reached.mem 23,reached.mem 24,reached.mem 25])=
 ([w[77]],[w[26],w[20],w[16],w[9],w[20],w[3],w[22],w[10],w[10],w[99],w[2],w[7],w[9],w[1],w[4],w[3],w[0],w[0],w[0]]) := rfl

theorem reached_read_fails : ArrayProbe.value.evalT allocated=.error .revert :=
 AllocatingFailure.allocated_failure child 2 (by decide) Evm.Memory.CompileExamples.r1 rfl rfl read_fails

def call (depth : Nat) : Stmt P.C Γ Γ := InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step depth
def code := checked.code++AllocatingReturn.image (C:=P.C) 4 CountdownWitness.F 8 7

theorem source_failure (depth : Nat) : (call (depth+1)).run caller=.error .revert := specification.2.2.2.2.2.2.1 depth

theorem target_failure : run code input=.revert := by
 simpa only [code,List.append_nil] using specification.2.2.2.2.2.2.2 []

theorem suffix_absorbed (suffix : List Instr) : run (code++suffix) input=.revert := run_append_revert target_failure

theorem source_zero : (call 0).run caller=.error .exhausted := by
 change TRun.call args .none .refl (AllocatingActivation.body 0).runR caller=_
 simp only [TRun.call,args_succeed,CallRet.enterT]
 change (do
   let out ← (AllocatingActivation.body 0).run child
   pure (exported (ps:=Parameters A) (CallRet.none : CallRet Γ [] Γ) Ext.refl caller child.env out))=_
 rw [AllocatingActivation.base_exhausts]
 rfl

theorem not_fault : run code input≠.fault := by rw [target_failure];intro wrong;cases wrong

theorem wrong_alias : reached.mem 4≠w[16] := by decide

theorem omitted_allocation : reached.mem 0≠w[22] := by decide

/-- Matched positive baseline uses the existing valid index/client unchanged. -/
theorem successful_control : ArgumentCall.call.run caller=.ok ArgumentCall.output ∧ run ArgumentCall.code input=.ok ArgumentCall.last 0 :=
 ⟨ArgumentCall.source,ArgumentCall.target⟩

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.ArgumentCalleeFailure
