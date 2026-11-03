import Solidity.Backend.InternalFlow.RuntimeFrameV3ArgumentCall

/-! The zero-counter allocating image executes no allocation or unwind step.
Its exact identity is derived from existing guards and loop laws, without an
allocator-owner premise. Positive allocation admission is not weakened. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingZero
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes
abbrev A : RefTy := CountdownWitness.A

/-- Both real guards stop, so the same image is the identity on every field. -/
theorem image {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (base : Nat → Fin W) (before : Machine)
 (repr : StateRepr L b frame F σ base before)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue 0 W_pos)
 (pointer bottom start : Nat) (current : before.mem pointer=.val (wmod start))
 (bottomValue : before.mem bottom=.val (wmod start)) :
 run (AllocatingReturn.image (C:=C) b F pointer bottom) before=.ok before 0 := by
 have guard := guard_run σ 0 W_pos counter base before repr
 have checked : run (guardCompiled (C:=C) b F).code before=.ok (before.push w[0]) 0 := by
   simpa only [bword] using guard
 have empty := empty_turn (run (guardCompiled (C:=C) b F).code) (run (AllocatingActivation.code (C:=C) b F pointer)) before checked
 have observed : loopIterN (run (guardCompiled (C:=C) b F).code) (run (AllocatingActivation.code (C:=C) b F pointer)) 1 before=.inr (.ok before 0) := by
   simp only [loopIterN,empty]
 have descent := successful_loop _ _ before before 1 observed
 have stopped := ParentStop.stop_after_running (b:=b) (R:=A) (before:=before) (last:=before) (horizon:=0)
   (by rfl) current bottomValue
 have restored := PairedUnwind.run_of_stopped stopped
 exact (run_append_ok descent).trans restored

theorem source_all {C : Contract} (σ : State C (Parameters A))
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue 0 W_pos)
 (depth : Nat) (positive : 0<depth) :
 (AllocatingActivation.body depth).run σ=.ok ⟨σ,List.prefix_refl _⟩ := by
 cases depth with
 | zero => omega
 | succ depth => exact AllocatingActivation.source_zero σ depth counter

/-- Cost zero preserves every supplied owner, but does not assert one exists. -/
theorem growth {C : Contract} {Γ : Ctx} (b frame : Nat) (σ : State C Γ) (base : Nat → Fin W) (before : Machine) :
 GrowsAllocator b frame 0 σ base before σ base before := by
 intro cursor positive owned space
 simpa only [Nat.add_zero] using owned

theorem endpoint {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (base : Nat → Fin W) (before : Machine)
 (repr : StateRepr L b frame F σ base before)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue 0 W_pos)
 (pointer bottom start : Nat) (current : before.mem pointer=.val (wmod start))
 (bottomValue : before.mem bottom=.val (wmod start)) :
 GrowingResult L b frame 0 F σ base before ((AllocatingActivation.body 1).run σ)
   (run (AllocatingReturn.image (C:=C) b F pointer bottom) before) :=
 .inl ⟨⟨σ,List.prefix_refl _⟩,before,base,source_all σ counter 1 (by decide),
   image σ base before repr counter pointer bottom start current bottomValue,repr,rfl,BaseExtends.refl _,growth b frame σ base before⟩

/-- Native export restores every caller local at zero, for arbitrary Γ. -/
theorem native_call {C : Contract} {Γ : Ctx} (name : Name) (args : Args C Γ (Parameters A))
 (σ : State C Γ) (a : TEnv C σ.H (Parameters A)) (evaluated : args.evalT σ=.ok a)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) a=countValue 0 W_pos)
 (depth : Nat) (positive : 0<depth) :
 (InterfaceV1.recursiveSource name args .none AllocatingActivation.step depth).run σ=.ok ⟨σ,List.prefix_refl _⟩ := by
 have body := source_all (σ.withEnv a) counter depth positive
 have called := call_return args .none .refl (AllocatingActivation.body depth).runR σ a evaluated ⟨σ.withEnv a,List.prefix_refl _⟩ body
 have restored : exported (ps:=Parameters A) (CallRet.none : CallRet Γ [] Γ) Ext.refl σ a
     (⟨σ.withEnv a,List.prefix_refl _⟩ : Solidity.Out C σ.H (Parameters A))=⟨σ,List.prefix_refl _⟩ := by
   change (⟨(σ.withEnv a).withEnv (Δ:=Γ) (TEnv.wk (List.prefix_refl σ.H) Γ σ.env),List.prefix_refl _⟩ : Solidity.Out C σ.H Γ)=_
   rw [TEnv.wk_self]
   rfl
 exact called.trans (congrArg Except.ok restored)

theorem take_parameters {C : Contract} {H : HTy} {Γ : Ctx}
 (a : TEnv C H (Parameters A)) (env : TEnv C H Γ) :
 TEnv.take (Parameters A) (TEnv.append (Parameters A) a env)=a := by
 rcases a with ⟨count,reference,tailUnit⟩
 cases tailUnit
 rfl

/-- General zero-counter call composition over arbitrary caller contexts.
The real prefix certificate and its scratch law produce the reached frame;
there is no positive allocator-owner premise for the skipped body. -/
theorem after_arguments {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
 (name : Name) (args : Args C Γ (Parameters A))
 (compiled : Composition.Program b F (args.declsThen .nil))
 (σ : State C Γ) (a : TEnv C σ.H (Parameters A)) (evaluated : args.evalT σ=.ok a)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) a=countValue 0 W_pos)
 (depth : Nat) (positive : 0<depth)
 (base : Nat → Fin W) (before : Machine) (initial : StateRepr L b frame F σ base before)
 (lo pointer bottom start : Nat) (room : b+compiled.checked.need≤lo) (boundary : lo≤frame)
 (pointerAbove : lo≤pointer) (pointerBelow : pointer<frame) (bottomAbove : lo≤bottom) (bottomBelow : bottom<frame)
 (current : before.mem pointer=.val (wmod start)) (bottomValue : before.mem bottom=.val (wmod start))
 (capacity : AllocationInput b frame (compiled.checked.cost σ) σ base before) :
 ∃ target addresses,
 (InterfaceV1.recursiveSource name args .none AllocatingActivation.step depth).run σ=.ok ⟨σ,List.prefix_refl _⟩ ∧
 run (compiled.checked.code++AllocatingReturn.image (C:=C) (b+Γ.length) (Frag.init (Parameters A)) pointer bottom) before=.ok target 0 ∧
 StateRepr L b frame (compiled.checked.frag.restrict Γ) σ addresses target ∧ target.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧ GrowsAllocator b frame (compiled.checked.cost σ) σ base before σ addresses target := by
 obtain ⟨target,addresses,executed,full,caller,stack,extended,growth⟩ :=
   ArgumentEntry.endpoint args compiled.checked σ a evaluated base before initial (by omega) capacity
 have parameters := parameter_projection (tail:=Γ) full
 change StateRepr L (b+Γ.length) frame (Frag.init (Parameters A))
   (σ.withEnv (TEnv.take (Parameters A) (TEnv.append (Parameters A) a σ.env))) addresses target at parameters
 rw [take_parameters] at parameters
 have scratch := compiled.safe initial room boundary capacity executed
 have body := image (σ.withEnv a) addresses target parameters counter pointer bottom start
   ((scratch pointer pointerAbove pointerBelow).trans current) ((scratch bottom bottomAbove bottomBelow).trans bottomValue)
 exact ⟨target,addresses,native_call name args σ a evaluated counter depth positive,(run_append_ok executed).trans body,
   caller,stack,extended,growth⟩

namespace Checks
open CountdownWitness
abbrev Γ := MemoryArgument.Γ
abbrev F := MemoryArgument.F
abbrev caller := MemoryArgument.caller
def input := writeMachine MemoryArgument.input 0 w[0]

theorem initial : StateRepr 1 1 16 F caller P.base input := by
 apply Restored.memory_transport MemoryArgument.initial input.mem
 · intro t i observed
   exact upd_other _ w[0] (by have h := le_lvl 1 i;change 1≤cellOf 1 i at h;omega)
 · intro x above
   exact upd_other _ w[0] (by omega)

/-- This model cannot supply any actual allocation owner. It is used only
on a genuinely zero-cost path, not admitted for positive allocation. -/
theorem no_owner (cursor : Fin W) : ¬StructAllocatorRepr caller.heap P.base 16 cursor input := by
 intro owner
 have word := owner.arrays.free.cell
 change w[0]=.val cursor at word
 have zero : (0:Nat)=cursor.val := congrArg Fin.val (Word.val.inj word)
 have above := owner.arrays.free.above
 omega

theorem no_positive_input : ¬AllocationInput 1 16 4 caller P.base input := by
 rintro (zero | ⟨positive,cursor,owner,room⟩)
 · omega
 · exact no_owner cursor owner

def args : Args P.C Γ (Parameters A) :=
 .snoc (.snocMemory .nil A (.user "alias") (.var (.there (.there .here)) rfl)) .uint (.user "count") (.simple (.lit 0 rfl))
def child := caller.withEnv (Δ:=Parameters A) (countValue 0 W_pos,(some Evm.Memory.CompileExamples.r1,()))
def program : Prog P.C Γ (Parameters A++Γ) := args.declsThen .nil

def checked : Calls.Program 1 F program := (Calls.compile 1 F program).get (by decide +kernel)

theorem public_selection : Calls.compile 1 F program=some checked := (Option.some_get _).symm

theorem arguments : args.evalT caller=.ok child.env := by rfl

theorem code_eq : checked.code=[.mload 1,.mstore 4,.push w[0],.mstore 5] := by rfl

theorem need_eq : checked.need=5 := by decide +kernel

theorem raw_run (m : Machine) : run checked.code m=.ok (writeMachine (writeMachine m 4 (m.mem 1)) 5 w[0]) 0 := by
 rw [code_eq]
 rfl

theorem safe : Composition.ProgramSafe checked := by
 intro L frame lo σ base m target repr room boundary capacity actual
 have same : target=writeMachine (writeMachine m 4 (m.mem 1)) 5 w[0] := (Evm.Out.ok.inj (actual.symm.trans (raw_run m))).1
 subst target
 rw [need_eq] at room
 intro x above below
 exact (upd_other _ w[0] (by omega)).trans (upd_other _ (m.mem 1) (by omega))

def prepared : Composition.Program 1 F program := ⟨checked,safe⟩

theorem cost_zero : checked.cost caller=0 := checked.zeroCost (by decide +kernel) caller

theorem capacity : AllocationInput 1 16 (checked.cost caller) caller P.base input := .inl cost_zero

def target := writeMachine (writeMachine input 4 w[20]) 5 w[0]

theorem target_prefix : run checked.code input=.ok target 0 := by rw [code_eq];rfl

theorem available : ∃ addresses,
 StateRepr 1 1 16 checked.frag (caller.withEnv (TEnv.append (Parameters A) child.env caller.env)) addresses target ∧
 StateRepr 1 1 16 (checked.frag.restrict Γ) caller addresses target := by
 obtain ⟨m,addresses,executed,repr,retained,rest⟩ :=
   ArgumentEntry.endpoint args checked caller child.env arguments P.base input initial (by decide +kernel) capacity
 have same : m=target := (Evm.Out.ok.inj (executed.symm.trans target_prefix)).1
 subst m
 exact ⟨addresses,repr,retained⟩

noncomputable def addresses : Nat → Fin W := available.choose

theorem specification :
 StateRepr 1 1 16 checked.frag (caller.withEnv (TEnv.append (Parameters A) child.env caller.env)) addresses target ∧
 StateRepr 1 1 16 (checked.frag.restrict Γ) caller addresses target := available.choose_spec

theorem parameter_frame : StateRepr 1 4 16 CountdownWitness.F child addresses target :=
 parameter_projection (tail:=Γ) specification.1

noncomputable def output : Solidity.Out P.C caller.H Γ :=
 exported (ps:=Parameters A) (CallRet.none : CallRet Γ [] Γ) Ext.refl caller child.env ⟨child,List.prefix_refl _⟩
def call : Stmt P.C Γ Γ := InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step 1
def code : List Instr := checked.code ++ AllocatingReturn.image (C:=P.C) 4 CountdownWitness.F 8 7

theorem source : call.run caller=.ok output :=
 call_return args .none .refl (AllocatingActivation.body 1).runR caller child.env arguments ⟨child,List.prefix_refl _⟩
   (source_all child rfl 1 (by decide))

theorem target_run : run code input=.ok target 0 :=
 (run_append_ok target_prefix).trans (image child addresses target parameter_frame rfl 8 7 10 rfl rfl)

theorem caller_fragment : checked.frag.restrict Γ=F := by rfl

theorem represented : StateRepr 1 1 16 F output.st addresses target := by
 have retained := specification.2
 rw [caller_fragment] at retained
 exact CallerReframe.reframe caller child (List.prefix_refl _) addresses addresses target target retained parameter_frame
   (BaseExtends.refl _) (by intro t i;rfl)
   (by intro R i;cases i with | there i => cases i with | there i => cases i with | there i => cases i)

theorem completed : call.run caller=.ok output ∧ run code input=.ok target 0 ∧ StateRepr 1 1 16 F output.st addresses target :=
 ⟨source,target_run,represented⟩

theorem general_client : ∃ m addresses,
 (InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step 1).run caller=.ok ⟨caller,List.prefix_refl _⟩ ∧
 run code input=.ok m 0 ∧ StateRepr 1 1 16 (checked.frag.restrict Γ) caller addresses m ∧ m.stack=input.stack ∧
 BaseExtends caller.H P.base addresses ∧ GrowsAllocator 1 16 (checked.cost caller) caller P.base input caller addresses m :=
 after_arguments "allocatingCountdown" args prepared caller child.env arguments rfl 1 (by decide) P.base input initial
   6 8 7 10 (by change 1+checked.need≤6;rw [need_eq];decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl capacity

theorem output_identity : output=⟨caller,List.prefix_refl _⟩ :=
 Except.ok.inj (source.symm.trans (native_call "allocatingCountdown" args caller child.env arguments rfl 1 (by decide)))

theorem observations :
 (target.stack,[target.mem 0,target.mem 1,target.mem 2,target.mem 3,target.mem 4,target.mem 5,target.mem 6,
 target.mem 7,target.mem 8,target.mem 9,target.mem 10,target.mem 11,target.mem 16,target.mem 17,target.mem 18,target.mem 20,target.mem 21])=
 ([w[77]],[w[0],w[20],w[16],w[9],w[20],w[0],w[0],w[10],w[10],w[99],w[0],w[0],w[2],w[7],w[9],w[1],w[4]]) := by rfl

theorem no_output_owner (cursor : Fin W) : ¬StructAllocatorRepr output.st.heap addresses 16 cursor target := by
 intro owner
 have word := owner.arrays.free.cell
 change w[0]=.val cursor at word
 have zero : (0:Nat)=cursor.val := congrArg Fin.val (Word.val.inj word)
 have above := owner.arrays.free.above
 omega

theorem zero_quote : (InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step 0).run caller=.error .exhausted :=
 AllocatingSource.call_exhaustion "allocatingCountdown" args 0 caller 0 W_pos Evm.Memory.CompileExamples.r1 arguments (by omega) (by decide)

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingZero
