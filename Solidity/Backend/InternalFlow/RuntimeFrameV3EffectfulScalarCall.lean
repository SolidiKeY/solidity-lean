import Solidity.Backend.InternalFlow.RuntimeFrameV3EffectfulScalarSource
import Solidity.Backend.InternalFlow.RuntimeFrameV3DisjointScalarControls

/-! A real callee write before recursive scalar return. The client has literal
scalar/reference arguments: the checked target write precedes marshalling,
while the native theorem proves the actual callee-prefix outcomes separately.
No argument-effect commutation oracle, general selector or profile is supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulScalarCall
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn
open DisjointScalarReturn.Client (Γ F caller before reference count value)

def changed := caller.withHeap (caller.heap.set CountdownWitness.P.r0 (MObj.setElem .dyn (caller.heap.get CountdownWitness.P.r0) 0 EffectfulScalarSource.replacement))
def written := writeMachine before 17 w[37]
def index : Val CountdownWitness.P.C Γ .uint := .simple (.lit 0 rfl)
def rhs : Val CountdownWitness.P.C Γ .uint := .simple (.lit 37 rfl)
def writeCode : List Instr := writeLocalValueCode 1 reference [.push w[0]] [.push w[37]]

theorem write_facts :
 run writeCode before=.ok written 0 ∧ StateRepr 1 1 16 F changed CountdownWitness.P.base written := by
 obtain ⟨word,encoded,source,executed,represented,words⟩ := Footprint.write_local
   DisjointScalarReturn.Client.initial reference CountdownWitness.P.r0 rfl index rhs
   ⟨_,.core _ rfl⟩ ⟨_,.core _ rfl⟩ (⟨0,by decide⟩ : Fin W) rfl
   EffectfulScalarSource.replacement rfl (by with_unfolding_all decide) 8
 have same : word=w[37] := Restored.value_unique encoded (ReprV.uint_of rfl)
 simpa only [same] using And.intro executed represented

theorem write_addr : caller.heap.writeAddr (.index CountdownWitness.P.r0 .dyn (countValue 0 W_pos))
 EffectfulScalarSource.replacement=some changed.heap := by
 with_unfolding_all rfl

theorem initial : StateRepr 1 1 16 F changed CountdownWitness.P.base written := write_facts.2

theorem available : ∃ (after : Machine) (addresses : Nat → Fin W),
 run (code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8) written=.ok after 0 ∧
 (∀ f depth,(call rfl reference count (.here : Idx Γ (.val .uint)) f depth).run changed=
   if 3<depth then .ok ⟨changed.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr 1 1 16 F (changed.setLocal .here (countValue 3 (by decide))) addresses after ∧
 after.stack=[w[77]] ∧ BaseExtends changed.H CountdownWitness.P.base addresses ∧
 after.mem 4=w[3] ∧ after.mem 7=w[3] ∧ after.mem 6=w[3] ∧ after.mem 5=w[16] ∧
 after.mem 9=w[10] ∧ after.mem 8=w[10] ∧
 GrowsAllocator 1 16 0 changed CountdownWitness.P.base written (changed.setLocal .here (countValue 3 (by decide))) addresses after ∧
 (∀ x,x≠4 → x≠9 → x≠8 → x≠5 → x≠6 → x≠7 → (x<10 ∨ 16≤x) → after.mem x=written.mem x) ∧
 (∀ j,j<3 → after.mem (10+2*j)=w[16] ∧ after.mem (10+2*j+1)=.val (wmod (3-j))) :=
 endpoint rfl changed reference count value .here 3 (by decide) rfl CountdownWitness.P.base written initial
   8 9 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl

noncomputable def machine : Machine := available.choose
noncomputable def addresses : Nat → Fin W := available.choose_spec.choose

theorem specification :
 run (code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8) written=.ok machine 0 ∧
 (∀ f depth,(call rfl reference count (.here : Idx Γ (.val .uint)) f depth).run changed=
   if 3<depth then .ok ⟨changed.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr 1 1 16 F (changed.setLocal .here (countValue 3 (by decide))) addresses machine ∧
 machine.stack=[w[77]] ∧ BaseExtends changed.H CountdownWitness.P.base addresses ∧
 machine.mem 4=w[3] ∧ machine.mem 7=w[3] ∧ machine.mem 6=w[3] ∧ machine.mem 5=w[16] ∧
 machine.mem 9=w[10] ∧ machine.mem 8=w[10] ∧
 GrowsAllocator 1 16 0 changed CountdownWitness.P.base written (changed.setLocal .here (countValue 3 (by decide))) addresses machine ∧
 (∀ x,x≠4 → x≠9 → x≠8 → x≠5 → x≠6 → x≠7 → (x<10 ∨ 16≤x) → machine.mem x=written.mem x) ∧
 (∀ j,j<3 → machine.mem (10+2*j)=w[16] ∧ machine.mem (10+2*j+1)=.val (wmod (3-j))) :=
 available.choose_spec.choose_spec

theorem initial_owner : StructAllocatorRepr changed.heap CountdownWitness.P.base 16 ⟨22,by decide⟩ written :=
 DisjointScalarReturn.Client.initial_owner.setArray CountdownWitness.P.r0 0 (by with_unfolding_all decide)
   EffectfulScalarSource.replacement w[37] (ReprV.uint_of rfl)

theorem entry_contrast : ∃ middle,
 run (DisjointScalarEntry.code 1 5 reference value) written=.ok middle 0 ∧
 middle.mem 7=w[0] ∧ middle.mem 4=w[77] ∧ middle.stack=[w[77]] := by
 obtain ⟨ref,middle,args,executed,callee,old,stack,referenceWord,outside,growth⟩ :=
   DisjointScalarEntry.entered (c:=5) rfl changed reference count value 3 (by decide) rfl CountdownWitness.P.base written initial (by decide) (by decide)
 have privateZero : middle.mem 7=w[0] := Restored.value_unique (callee.core.vals .here) (ReprV.dflt_zero .uint)
 have oldResult : middle.mem 4=w[77] := Restored.value_unique (old.core.vals .here) (ReprV.uint_of rfl)
 exact ⟨middle,executed,privateZero,oldResult,stack⟩

theorem old_caller_words : (machine.mem 1,machine.mem 2,machine.mem 3)=(w[16],w[16],w[2]) := by
 rcases specification with ⟨_,_,_,_,_,_,_,_,_,_,_,_,outside,_⟩
 rw [outside 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   outside 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   outside 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))]
 rfl

theorem owner : StructAllocatorRepr changed.heap addresses 16 ⟨22,by decide⟩ machine := by
 rcases specification with ⟨_,_,_,_,_,_,_,_,_,_,_,growth,_⟩
 exact growth ⟨22,by decide⟩ (by decide) initial_owner (by decide)

theorem snapshot :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,
 machine.mem 5,machine.mem 6,machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,
 machine.mem 11,machine.mem 12,machine.mem 13,machine.mem 14,machine.mem 15,machine.mem 16,
 machine.mem 17,machine.mem 18,machine.mem 19,machine.mem 20,machine.mem 21])=
 ([w[77]],[w[22],w[16],w[16],w[2],w[3],w[16],w[3],w[3],w[10],w[10],w[16],w[3],
 w[16],w[2],w[16],w[1],w[2],w[37],w[9],w[0],w[1],w[4]]) := by
 rcases specification with ⟨executed,source,reached,stack,extended,destination,result,counter,alias,cursor,bottomWord,growth,outside,saved⟩
 have one : machine.mem 1=w[16] := congrArg (fun xs : Word×Word×Word => xs.1) old_caller_words
 have two : machine.mem 2=w[16] := congrArg (fun xs : Word×Word×Word => xs.2.1) old_caller_words
 have three : machine.mem 3=w[2] := congrArg (fun xs : Word×Word×Word => xs.2.2) old_caller_words
 rw [stack,owner.arrays.free.cell,one,two,three,destination,result,counter,alias,cursor,bottomWord,
   (saved 0 (by decide)).1,(saved 0 (by decide)).2,
   (saved 1 (by decide)).1,(saved 1 (by decide)).2,
   (saved 2 (by decide)).1,(saved 2 (by decide)).2,
   outside 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))]
 rfl


def invoke (depth : Nat) := EffectfulScalarSource.invoke "effectfulScalar"
 (DisjointScalarEntry.args rfl reference count) (.here : Idx Γ (.val .uint)) depth
def image := writeCode++code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8

theorem native (depth : Nat) : (invoke depth).run caller=
 if 3<depth then .ok ⟨changed.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ else .error .exhausted :=
 EffectfulScalarSource.all_horizons "effectfulScalar" (DisjointScalarEntry.args rfl reference count)
 .here depth caller 3 (by decide) CountdownWitness.P.r0 rfl changed.heap write_addr

theorem target : run image before=.ok machine 0 :=
 (run_append_ok write_facts.1).trans specification.1

theorem native_and_target (depth : Nat) (enough : 3<depth) :
 (invoke depth).run caller=.ok ⟨changed.setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ ∧
 run image before=.ok machine 0 ∧
 StateRepr 1 1 16 F (changed.setLocal .here (countValue 3 (by decide))) addresses machine :=
 ⟨(native depth).trans (if_pos enough),target,specification.2.2.1⟩

theorem whole_growth : GrowsAllocator 1 16 0 caller CountdownWitness.P.base before
 (changed.setLocal (.here : Idx Γ (.val .uint)) (countValue 3 (by decide))) addresses machine := by
 intro cursor positive owned room
 have modified := owned.setArray CountdownWitness.P.r0 0 (by with_unfolding_all decide)
   EffectfulScalarSource.replacement w[37] (ReprV.uint_of rfl)
 rcases specification with ⟨_,_,_,_,_,_,_,_,_,_,_,growth,_,_⟩
 exact growth cursor positive modified room

theorem old_cell : machine.mem 17=w[37] := by
 rcases specification with ⟨_,_,_,_,_,_,_,_,_,_,_,_,outside,_⟩
 exact outside 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))

theorem wrong_old_contents : machine.mem 17≠w[7] := by
 rw [old_cell]
 decide

theorem changed_destination : before.mem 4=w[77] ∧ machine.mem 4=w[3] :=
 ⟨rfl,specification.2.2.2.2.2.1⟩

theorem not_keeps : ¬Heap.Keeps (List.prefix_refl caller.H) caller.heap
 (changed.setLocal (.here : Idx Γ (.val .uint)) (countValue 3 (by decide))).heap := by
 intro kept
 have object := kept CountdownWitness.P.r0
 have values := congrArg (fun object : MObj caller.H CountdownWitness.A => object.val.map (fun value => value.val)) object
 with_unfolding_all change ([37,9] : List Int)=[7,9] at values
 have unequal : ([37,9] : List Int)≠[7,9] := by decide
 exact unequal values

theorem exhaustion_boundary : (invoke 0).run caller=.error .exhausted ∧ run image before=.ok machine 0 :=
 ⟨(native 0).trans (if_neg (by decide)),target⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulScalarCall
