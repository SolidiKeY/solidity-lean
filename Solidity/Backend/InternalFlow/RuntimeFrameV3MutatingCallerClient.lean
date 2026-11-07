import Solidity.Backend.InternalFlow.RuntimeFrameV3MutatingCaller

/-! Inhabited caller-context transport through an actual old-object mutation
and private iteration allocation. Source and target are derived independently;
no general recursive compiler or original profile is supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.MutatingCaller
noncomputable section
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes CountdownWitness
namespace Client
open CountdownWitness
abbrev Γ := MemoryArgument.Γ
abbrev F := MemoryArgument.F
abbrev caller := MemoryArgument.caller
abbrev input := MemoryArgument.input
abbrev args := MemoryArgument.args
abbrev child := MemoryArgument.child
abbrev checked := ArgumentEntry.Checks.checked
def call : Stmt P.C Γ Γ := InterfaceV1.recursiveSource "mutatingCountdown" args .none MutatingActivation.step 2
def code := checked.code++MutatingCompletion.image (C:=P.C) 4 (Frag.init (Parameters A)) 8 7

theorem available :
 ∃ (out : Solidity.Out P.C caller.H Γ) (target : Machine) (addresses : Nat → Fin W) (mid : Machine),
 run checked.code input=.ok mid 0 ∧ call.run caller=.ok out ∧ run code input=.ok target 0 ∧
 StateRepr 1 1 16 (checked.frag.restrict Γ) out.st addresses target ∧ target.stack=input.stack ∧
 BaseExtends caller.H P.base addresses ∧ GrowsAllocator 1 16 (checked.cost caller+4*1) caller P.base input out.st addresses target ∧
 (∀ {t : LTy} (i : Idx Γ t),target.mem (cellOf 1 i)=mid.mem (cellOf 1 i)) ∧ target.mem 8=w[10] ∧
 (∀ j,j<1 → target.mem (10+2*j)=.val (P.base Evm.Memory.CompileExamples.r1.id) ∧ target.mem (10+2*j+1)=.val (wmod (1-j))) :=
 after_arguments "mutatingCountdown" args ArgumentEntry.Checks.prepared caller child.env MemoryArgument.arguments
   1 (by decide) (by decide) Evm.Memory.CompileExamples.r1 rfl rfl MemoryArgument.read_bound
   P.base input MemoryArgument.initial 7 8 7 10
   (by change 1+checked.need≤7;rw [ArgumentEntry.Checks.need_eq];decide) (by decide)
   (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
   (by decide) (by decide) (by decide) (by decide) rfl (by decide) ArgumentCall.total_capacity
   (by intro R i;cases i with | there i => cases i with | there i => cases i with | there i => cases i)

noncomputable def output := available.choose
noncomputable def target := available.choose_spec.choose
noncomputable def addresses := available.choose_spec.choose_spec.choose
noncomputable def midpoint := available.choose_spec.choose_spec.choose_spec.choose

theorem specification :
 run checked.code input=.ok midpoint 0 ∧ call.run caller=.ok output ∧ run code input=.ok target 0 ∧
 StateRepr 1 1 16 (checked.frag.restrict Γ) output.st addresses target ∧ target.stack=input.stack ∧
 BaseExtends caller.H P.base addresses ∧ GrowsAllocator 1 16 (checked.cost caller+4*1) caller P.base input output.st addresses target ∧
 (∀ {t : LTy} (i : Idx Γ t),target.mem (cellOf 1 i)=midpoint.mem (cellOf 1 i)) ∧ target.mem 8=w[10] ∧
 (∀ j,j<1 → target.mem (10+2*j)=.val (P.base Evm.Memory.CompileExamples.r1.id) ∧ target.mem (10+2*j+1)=.val (wmod (1-j))) :=
 available.choose_spec.choose_spec.choose_spec.choose_spec


/-- Source identity is computed from the actual one-turn call, independently
of the existential target endpoint. Caller locals are restored after mutation. -/
def changed := caller.withHeap (caller.heap.set Evm.Memory.CompileExamples.r1
 (MObj.setElem .dyn (caller.heap.get Evm.Memory.CompileExamples.r1) 0 (countValue 1 (by decide))))
def expected := (changed.alloc (defaultArray .bool AllocatingActivation.size)).1

theorem source_exact : call.run caller=.ok (⟨expected,List.prefix_append _ _⟩ : Solidity.Out P.C caller.H Γ) := by
 let mutated := MutatingActivation.changed child Evm.Memory.CompileExamples.r1 0
 let parent := AllocatingActivation.allocated mutated
 let extension := AllocatingActivation.extension mutated
 let inherited := Evm.Memory.CompileExamples.r1.wk extension
 let zeroChild : State P.C (Parameters A) := parent.withEnv (countValue 0 W_pos,(some inherited,()))
 have parameters := AllocatingActivation.allocated_parameters mutated 0 (by decide)
   Evm.Memory.CompileExamples.r1 (show mutated.env.1=countValue 1 (by decide) from rfl) rfl
 have argsZero := next_eval rfl parent 0 (by decide) inherited parameters.1 parameters.2
 have zero := MutatingActivation.source_zero zeroChild 0 rfl
 let childOut : Solidity.Out P.C parent.H (Parameters A) := ⟨zeroChild,List.prefix_refl _⟩
 have nested := call_return (nextArgs A rfl) .none .refl (MutatingActivation.body 1).runR
   parent zeroChild.env argsZero childOut zero
 let returned := exported (ps:=Parameters A) (CallRet.none : CallRet (Parameters A) [] (Parameters A))
   Ext.refl parent zeroChild.env childOut
 let bodyOut : Solidity.Out P.C child.H (Parameters A) := ⟨returned.st,extension.trans returned.ext⟩
 have entered := MutatingActivation.source_positive child 1 0 (by decide)
   Evm.Memory.CompileExamples.r1 rfl rfl (Nat.lt_of_lt_of_le (by decide : 0<1) MemoryArgument.read_bound)
 have nested' : (.call "mutatingCountdown" (nextArgs A rfl) .none (MutatingActivation.body 1) :
     Stmt P.C (Parameters A) (Parameters A)).run parent=.ok returned := nested
 rw [nested'] at entered
 have bodyRun : (MutatingActivation.body 2).run child=.ok bodyOut := entered.trans rfl
 have native := call_return args .none .refl (MutatingActivation.body 2).runR
   caller child.env MemoryArgument.arguments bodyOut bodyRun
 exact native.trans (by rfl)

theorem output_exact : output=(⟨expected,List.prefix_append _ _⟩ : Solidity.Out P.C caller.H Γ) :=
 Except.ok.inj (specification.2.1.symm.trans source_exact)

theorem output_identity : output.st=expected := congrArg (fun out : Solidity.Out P.C caller.H Γ => out.st) output_exact

theorem mutation : output.st.heap.get (Evm.Memory.CompileExamples.r1.wk output.ext)=
 MObj.setElem .dyn (caller.heap.get Evm.Memory.CompileExamples.r1) 0 (countValue 1 (by decide)) := by
 rw [output_exact]
 with_unfolding_all rfl

theorem not_keeps : ¬Heap.Keeps output.ext caller.heap output.st.heap := by
 intro kept
 have object := kept Evm.Memory.CompileExamples.r1
 rw [mutation] at object
 have values := congrArg (fun object : MObj output.st.H A => object.val.map (fun value => value.val)) object
 with_unfolding_all change ([1] : List Int)=[4] at values
 have unequal : ([1] : List Int)≠[4] := by decide
 exact unequal values

theorem represented : StateRepr 1 1 16 F output.st addresses target := by
 have actual := specification.2.2.2.1
 rw [ArgumentCall.caller_fragment] at actual
 exact actual

theorem returned_owner : StructAllocatorRepr output.st.heap addresses 16 (⟨26,by decide⟩ : Fin W) target := by
 have grown := specification.2.2.2.2.2.2.1
 have owned := grown ⟨22,by decide⟩ (by decide) MemoryArgument.ownership
   (by rw [ArgumentEntry.Checks.cost_zero];decide)
 simpa only [ArgumentEntry.Checks.cost_zero,Nat.zero_add] using owned

theorem protected_observations :
 target.stack=[w[77]] ∧ [target.mem 1,target.mem 2,target.mem 3]=[w[20],w[16],w[9]] ∧
 target.mem 0=w[26] ∧ target.mem 8=w[10] := by
 rcases specification with ⟨prefixRun,source,execution,repr,stack,extended,growth,words,cursor,saved⟩
 have same : midpoint=ArgumentEntry.Checks.target :=
   (Evm.Out.ok.inj (prefixRun.symm.trans ArgumentEntry.Checks.target_run)).1
 have first := words (.there (.there .here) : Idx Γ (.mem A))
 have second := words (.there .here : Idx Γ (.mem A))
 have third := words (.here : Idx Γ (.val .uint))
 rw [same] at first second third
 change target.mem 1=w[20] at first
 change target.mem 2=w[16] at second
 change target.mem 3=w[9] at third
 exact ⟨stack,by rw [first,second,third],returned_owner.arrays.free.cell,cursor⟩

/-- The changed old element is observed in the SAME returned target state. -/
theorem mutation_target : target.mem 21=w[1] := by
 let reference := Evm.Memory.CompileExamples.r1.wk output.ext
 have element : (MObj.elems .dyn (output.st.heap.get reference))[0]?=some (countValue 1 (by decide)) := by
   change (MObj.elems .dyn (output.st.heap.get (Evm.Memory.CompileExamples.r1.wk output.ext)))[0]?=_
   rw [mutation]
   with_unfolding_all rfl
 have encoded := (represented.heap.arrays reference).elements 0 _ element
 have base := specification.2.2.2.2.2.1 Evm.Memory.CompileExamples.r1
 change addresses Evm.Memory.CompileExamples.r1.id=P.base Evm.Memory.CompileExamples.r1.id at base
 change ReprV .uint (countValue 1 (by decide))
   (target.mem ((addresses Evm.Memory.CompileExamples.r1.id).val+1+0)) at encoded
 rw [base] at encoded
 change ReprV .uint (countValue 1 (by decide)) (target.mem 21) at encoded
 obtain ⟨word,cell,value⟩ := encoded
 have one : word.val=1 := by
   change (1:Int)=(word.val:Int) at value
   omega
 have same : word=(⟨1,by decide⟩ : Fin W) := Fin.ext one
 exact cell.trans (congrArg Word.val same)

theorem wrong_old_contents : target.mem 21≠w[4] := by
 rw [mutation_target]
 decide

end Client

end
end Solidity.Backend.InternalFlow.RuntimeFrame.MutatingCaller
