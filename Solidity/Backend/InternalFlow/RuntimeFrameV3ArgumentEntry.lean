import Solidity.Backend.InternalFlow.RuntimeFrameV3MemoryArgument
import Solidity.Calculus.SoundCalls
/-! Exact argument-declaration output and checked target entry frames.
The existing ordered evaluation law is consumed, not reimplemented. Full
caller and parameter frames are reached by actual admitted compiler clients. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ArgumentEntry
open Evm Evm.Memory

theorem source {C : Contract} {Γ ps : Ctx} (args : Args C Γ ps) (σ : State C Γ)
 (a : TEnv C σ.H ps) (evaluated : args.evalT σ=.ok a) :
 (args.declsThen .nil).run σ=.ok ⟨σ.withEnv (TEnv.append ps a σ.env),List.prefix_refl _⟩ := by
 have projected := Args.runSt_declsThen σ args (.nil : Prog C (ps++Γ) (ps++Γ))
 rw [evaluated] at projected
 simp only [Prog.runSt_nil] at projected
 change ((args.declsThen .nil).run σ).map (fun out => out.st)=.ok (σ.withEnv (TEnv.append ps a σ.env)) at projected
 cases actual : (args.declsThen .nil).run σ with
 | error halt => rw [actual] at projected;cases projected
 | ok out =>
   rw [actual] at projected
   have same : out.st=σ.withEnv (TEnv.append ps a σ.env) := Except.ok.inj projected
   rcases out with ⟨st,e⟩
   cases same
   rfl

/-- Preserve the exact intrinsic halt, not merely its byte projection. -/
theorem source_failure {C : Contract} {Γ ps : Ctx} (args : Args C Γ ps) (σ : State C Γ)
 (halt : THalt) (evaluated : args.evalT σ=.error halt) :
 (args.declsThen .nil).run σ=.error halt := by
 have projected := Args.runSt_declsThen σ args (.nil : Prog C (ps++Γ) (ps++Γ))
 rw [evaluated] at projected
 change ((args.declsThen .nil).run σ).map (fun out => out.st)=.error halt at projected
 cases actual : (args.declsThen .nil).run σ with
 | error other =>
   rw [actual] at projected
   have same : other=halt := Except.error.inj projected
   cases same
   rfl
 | ok out => rw [actual] at projected;cases projected

theorem retained {C : Contract} {Γ ps : Ctx} (σ : State C Γ) (a : TEnv C σ.H ps) :
 (σ.withEnv (TEnv.append ps a σ.env)).drop (Ext.append Γ ps)=σ := by
 change σ.withEnv (Δ:=Γ) (TEnv.drop (Ext.append Γ ps) (TEnv.append ps a σ.env))=σ
 rw [TEnv.drop_append]
 rfl

/-- The actual checked argument-declaration program supplies the target state,
capacity cost and complete caller/parameter representation. -/
theorem endpoint {C : Contract} {Γ ps : Ctx} {L b frame : Nat} {F : Frag Γ}
 (args : Args C Γ ps) (checked : Calls.Program b F (args.declsThen .nil))
 (σ : State C Γ) (a : TEnv C σ.H ps) (evaluated : args.evalT σ=.ok a)
 (base : Nat → Fin W) (before : Machine) (initial : StateRepr L b frame F σ base before)
 (room : b+checked.need≤frame) (capacity : AllocationInput b frame (checked.cost σ) σ base before) :
 ∃ target addresses,
 run checked.code before=.ok target 0 ∧
 StateRepr L b frame checked.frag (σ.withEnv (TEnv.append ps a σ.env)) addresses target ∧
 StateRepr L b frame (checked.frag.restrict Γ) σ addresses target ∧
 target.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (checked.cost σ) σ base before (σ.withEnv (TEnv.append ps a σ.env)) addresses target := by
 rcases checked.sound initial room capacity with ⟨out,target,addresses,actual,executed,repr,stack,extended,growth⟩ | ⟨actual,failed⟩
 · have same : out=⟨σ.withEnv (TEnv.append ps a σ.env),List.prefix_refl _⟩ :=
     Except.ok.inj (actual.symm.trans (source args σ a evaluated))
   subst out
   have caller := repr.drop (Ext.append Γ ps)
   rw [retained] at caller
   exact ⟨target,addresses,executed,repr,caller,stack,extended,growth⟩
 · rw [source args σ a evaluated] at actual
   cases actual

/-- Bare revert is the checked producer's exact supported failure alternative.
Other THalt classes are not silently mapped to it. -/
theorem target_revert {C : Contract} {Γ ps : Ctx} {L b frame : Nat} {F : Frag Γ}
 (args : Args C Γ ps) (checked : Calls.Program b F (args.declsThen .nil))
 (σ : State C Γ) (evaluated : args.evalT σ=.error .revert)
 (base : Nat → Fin W) (before : Machine) (initial : StateRepr L b frame F σ base before)
 (room : b+checked.need≤frame) (capacity : AllocationInput b frame (checked.cost σ) σ base before) :
 run checked.code before=.revert := by
 rcases checked.sound initial room capacity with ⟨out,target,addresses,actual,rest⟩ | ⟨actual,failed⟩
 · rw [source_failure args σ .revert evaluated] at actual
   cases actual
 · exact failed

namespace Checks
open CountdownWitness RecursiveSource
abbrev A : RefTy := CountdownWitness.A
abbrev Γ := MemoryArgument.Γ
abbrev F := MemoryArgument.F
abbrev caller := MemoryArgument.caller
abbrev input := MemoryArgument.input
abbrev args := MemoryArgument.args

def program : Prog P.C Γ (Parameters A++Γ) := args.declsThen .nil

def checked : Calls.Program 1 F program := (Calls.compile 1 F program).get (by decide +kernel)

theorem public_selection : Calls.compile 1 F program=some checked := (Option.some_get _).symm

theorem code_eq : checked.code=[.mload 1,.mstore 4,.push w[1],.mstore 5] := by rfl

theorem need_eq : checked.need=5 := by decide +kernel

theorem raw_run (m : Machine) : run checked.code m=.ok (writeMachine (writeMachine m 4 (m.mem 1)) 5 w[1]) 0 := by
 rw [code_eq]
 rfl

/-- The public selected certificate also has a derived scratch-frame law;
it is not supplied as a safety or simulation field. -/
theorem safe : Composition.ProgramSafe checked := by
 intro L frame lo σ base m target repr room boundary capacity actual
 have same : target=writeMachine (writeMachine m 4 (m.mem 1)) 5 w[1] :=
   (Evm.Out.ok.inj (actual.symm.trans (raw_run m))).1
 subst target
 rw [need_eq] at room
 intro x above below
 exact (upd_other _ w[1] (by omega)).trans (upd_other _ (m.mem 1) (by omega))

def prepared : Composition.Program 1 F program := ⟨checked,safe⟩

theorem cost_zero : checked.cost caller=0 := checked.zeroCost (by decide +kernel) caller

theorem room : 1+checked.need≤16 := by decide +kernel

theorem capacity : AllocationInput 1 16 (checked.cost caller) caller P.base input := .inl cost_zero

def target := writeMachine (writeMachine input 4 w[20]) 5 w[1]

theorem target_run : run checked.code input=.ok target 0 := by
 rw [code_eq]
 rfl

theorem available : ∃ addresses,
 StateRepr 1 1 16 checked.frag (caller.withEnv (TEnv.append (Parameters A) MemoryArgument.child.env caller.env)) addresses target ∧
 StateRepr 1 1 16 (checked.frag.restrict Γ) caller addresses target ∧
 target.stack=input.stack ∧ BaseExtends caller.H P.base addresses ∧
 GrowsAllocator 1 16 (checked.cost caller) caller P.base input
   (caller.withEnv (TEnv.append (Parameters A) MemoryArgument.child.env caller.env)) addresses target := by
 obtain ⟨m,addresses,executed,repr,retained,stack,extended,growth⟩ :=
   endpoint args checked caller MemoryArgument.child.env MemoryArgument.arguments P.base input MemoryArgument.initial room capacity
 have same : m=target := (Evm.Out.ok.inj (executed.symm.trans target_run)).1
 subst m
 exact ⟨addresses,repr,retained,stack,extended,growth⟩

noncomputable def addresses : Nat → Fin W := available.choose

theorem specification :
 StateRepr 1 1 16 checked.frag (caller.withEnv (TEnv.append (Parameters A) MemoryArgument.child.env caller.env)) addresses target ∧
 StateRepr 1 1 16 (checked.frag.restrict Γ) caller addresses target ∧
 target.stack=input.stack ∧ BaseExtends caller.H P.base addresses ∧
 GrowsAllocator 1 16 (checked.cost caller) caller P.base input
   (caller.withEnv (TEnv.append (Parameters A) MemoryArgument.child.env caller.env)) addresses target := available.choose_spec

theorem retained_ownership : StructAllocatorRepr caller.heap addresses 16 (⟨22,by decide⟩ : Fin W) target := by
 have owner := specification.2.2.2.2 ⟨22,by decide⟩ (by decide) MemoryArgument.ownership (by rw [cost_zero];decide)
 simpa only [cost_zero,Nat.add_zero,State.withEnv] using owner

theorem actual_source : program.run caller=.ok ⟨caller.withEnv (TEnv.append (Parameters A) MemoryArgument.child.env caller.env),List.prefix_refl _⟩ :=
 source args caller MemoryArgument.child.env MemoryArgument.arguments

theorem parameter_frame : StateRepr 1 4 16 CountdownWitness.F MemoryArgument.child addresses target :=
 RecursiveActivation.parameter_projection (tail:=Γ) specification.1

theorem observations :
 (target.stack,[target.mem 0,target.mem 1,target.mem 2,target.mem 3,target.mem 4,target.mem 5,
 target.mem 7,target.mem 8,target.mem 9,target.mem 16,target.mem 17,target.mem 18,target.mem 20,target.mem 21])=
 ([w[77]],[w[22],w[20],w[16],w[9],w[20],w[1],w[10],w[10],w[99],w[2],w[7],w[9],w[1],w[4]]) := by rfl

theorem wrong_parameter_identity : target.mem 4≠w[16] := by decide

theorem lost_caller_scalar : target.mem 3≠w[1] := by decide

theorem wrong_parameter_scalar : target.mem 5≠w[9] := by decide

def badArgs : Args P.C Γ (Parameters A) :=
 .snoc (.snocMemory .nil A (.user "alias") (.var (.there (.there .here)) rfl)) .uint (.user "count")
   (.readMem (.index .dyn (.var (.there (.there .here)) rfl) (.simple (.lit 1 rfl))))

def badProgram : Prog P.C Γ (Parameters A++Γ) := badArgs.declsThen .nil

def badChecked : Calls.Program 1 F badProgram := (Calls.compile 1 F badProgram).get (by decide +kernel)

theorem bad_selection : Calls.compile 1 F badProgram=some badChecked := (Option.some_get _).symm

theorem bad_evaluated : badArgs.evalT caller=.error .revert := by with_unfolding_all rfl

theorem bad_source : badProgram.run caller=.error .revert := source_failure badArgs caller .revert bad_evaluated

theorem bad_capacity : AllocationInput 1 16 (badChecked.cost caller) caller P.base input :=
 .inl (badChecked.zeroCost (by decide +kernel) caller)

theorem bad_target : run badChecked.code input=.revert :=
 target_revert badArgs badChecked caller bad_evaluated P.base input MemoryArgument.initial (by decide +kernel) bad_capacity

theorem bad_suffix (suffix : List Instr) : run (badChecked.code++suffix) input=.revert := run_append_revert bad_target

theorem bad_not_fault : run badChecked.code input≠.fault := by
 rw [bad_target]
 intro wrong
 cases wrong

theorem bad_not_exhausted : badProgram.run caller≠.error .exhausted := by
 rw [bad_source]
 intro wrong
 cases wrong

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.ArgumentEntry
