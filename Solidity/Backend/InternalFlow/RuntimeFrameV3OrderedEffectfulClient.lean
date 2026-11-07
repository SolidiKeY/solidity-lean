import Solidity.Backend.InternalFlow.RuntimeFrameV3OrderedEffectfulScalar
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarReentryEndpoint

/-! A heap read supplies count3 BEFORE the callee replaces that same cell by37.
The actual private frame, scalar unwind and caller export retain captured3.
The earlier private array remains represented. General selection/profile and
full failure/termination correspondence remain separate obligations. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulScalar.Client
noncomputable section
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
open DisjointScalarReturn.Client (Γ F reference)
abbrev C := CountdownWitness.P.C
def caller := ScalarContinuation.final.setLocal (.here : Idx Γ (.val .uint)) (countValue 77 (by decide))
def before := writeMachine ScalarContinuation.target 4 w[77]
noncomputable abbrev base := ScalarContinuation.finalBase
def ref : HRef caller.H A := CountdownWitness.P.r0.wk ScalarContinuation.extension
abbrev count := ScalarReentry.count
abbrev value := ScalarReentry.emitted.value

theorem initial : StateRepr 1 1 16 F caller base before :=
 ScalarContinuation.endpoint.2.2.1.setVal .here (countValue 77 (by decide)) w[77] (ReprV.uint_of rfl)

theorem evaluated : count.evalT caller=.ok (countValue 3 (by decide)) := by
 change ScalarReentry.count.evalT ScalarContinuation.final=_
 exact ScalarReentry.actual_count

theorem binding : TEnv.get reference caller.env=some ref := by with_unfolding_all rfl

theorem live : 0<caller.heap.len ref .dyn := by with_unfolding_all decide

theorem ref_base : base ref.id=(⟨16,by decide⟩ : Fin W) :=
 ScalarContinuation.bases_preserved CountdownWitness.P.r0

theorem current : before.mem 9=w[10] :=
 (upd_other ScalarContinuation.target.mem w[77] (by decide : (9:Nat)≠4)).trans ScalarReentry.prefix_cursor

theorem available : ∃ (after : Machine) (addresses : Nat → Fin W),
 run (code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8) before=.ok after 0 ∧
 (∀ f depth,(call reference count (.here : Idx Γ (.val .uint)) f depth).run caller=
   if 3<depth then .ok ⟨(changed caller ref).setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr 1 1 16 F ((changed caller ref).setLocal .here (countValue 3 (by decide))) addresses after ∧
 after.stack=before.stack ∧ BaseExtends caller.H base addresses ∧
 after.mem 4=w[3] ∧ after.mem 7=w[3] ∧ after.mem 6=w[3] ∧ after.mem 5=before.mem 2 ∧
 after.mem 9=w[10] ∧ after.mem 8=w[10] ∧
 GrowsAllocator 1 16 0 caller base before ((changed caller ref).setLocal .here (countValue 3 (by decide))) addresses after ∧
 (∀ x,x≠4 → x≠9 → x≠8 → x≠5 → x≠6 → x≠7 → (x<10 ∨ 16≤x) →
   after.mem x=(writeMachine before 17 w[37]).mem x) ∧
 (∀ j,j<3 → after.mem (10+2*j)=before.mem 2 ∧ after.mem (10+2*j+1)=.val (wmod (3-j))) := by
 have facts := endpoint (c:=5) caller reference ref binding live count value .here 3 (by decide) evaluated base before initial
   8 9 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) current
     (by intro R i;cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => cases i)
 rw [ref_base] at facts
 exact facts

noncomputable def machine : Machine := available.choose
noncomputable def addresses : Nat → Fin W := available.choose_spec.choose

theorem specification :
 run (code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8) before=.ok machine 0 ∧
 (∀ f depth,(call reference count (.here : Idx Γ (.val .uint)) f depth).run caller=
   if 3<depth then .ok ⟨(changed caller ref).setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr 1 1 16 F ((changed caller ref).setLocal .here (countValue 3 (by decide))) addresses machine ∧
 machine.stack=before.stack ∧ BaseExtends caller.H base addresses ∧
 machine.mem 4=w[3] ∧ machine.mem 7=w[3] ∧ machine.mem 6=w[3] ∧ machine.mem 5=before.mem 2 ∧
 machine.mem 9=w[10] ∧ machine.mem 8=w[10] ∧
 GrowsAllocator 1 16 0 caller base before ((changed caller ref).setLocal .here (countValue 3 (by decide))) addresses machine ∧
 (∀ x,x≠4 → x≠9 → x≠8 → x≠5 → x≠6 → x≠7 → (x<10 ∨ 16≤x) →
   machine.mem x=(writeMachine before 17 w[37]).mem x) ∧
 (∀ j,j<3 → machine.mem (10+2*j)=before.mem 2 ∧ machine.mem (10+2*j+1)=.val (wmod (3-j))) :=
 available.choose_spec.choose_spec

theorem initial_owner : StructAllocatorRepr caller.heap base 16 (⟨26,by decide⟩ : Fin W) before :=
 ScalarContinuation.allocation_facts.2.2.1.localWrite 4 (by decide) (by decide) w[77]

theorem owner : StructAllocatorRepr (changed caller ref).heap addresses 16 (⟨26,by decide⟩ : Fin W) machine := by
 rcases specification with ⟨_,_,_,_,_,_,_,_,_,_,_,growth,_,_⟩
 exact growth ⟨26,by decide⟩ (by decide) initial_owner (by decide)

theorem changed_count : count.evalT (changed caller ref)=.ok (countValue 37 (by decide)) := by
 with_unfolding_all rfl

theorem native_and_target (depth : Nat) (enough : 3<depth) :
 (call reference count (.here : Idx Γ (.val .uint)) "orderedScalar" depth).run caller=
   .ok ⟨(changed caller ref).setLocal .here (countValue 3 (by decide)),List.prefix_refl _⟩ ∧
 run (code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8) before=.ok machine 0 ∧
 StateRepr 1 1 16 F ((changed caller ref).setLocal .here (countValue 3 (by decide))) addresses machine :=
 ⟨(specification.2.1 "orderedScalar" depth).trans (if_pos enough),specification.1,specification.2.2.1⟩

theorem private_base : addresses 2=(⟨22,by decide⟩ : Fin W) :=
 specification.2.2.2.2.1 ((ScalarContinuation.changed.alloc (defaultArray .uint ScalarContinuation.size)).2)

theorem input_stack : before.stack=[w[77]] :=
 congrArg (fun observed : List Word × List Word => observed.1) ScalarContinuation.Controls.complete_observations

theorem snapshot :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,
 machine.mem 5,machine.mem 6,machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,
 machine.mem 11,machine.mem 12,machine.mem 13,machine.mem 14,machine.mem 15,machine.mem 16,
 machine.mem 17,machine.mem 18,machine.mem 19,machine.mem 20,machine.mem 21,machine.mem 22,
 machine.mem 23,machine.mem 24,machine.mem 25])=
 ([w[77]],[w[26],w[16],w[16],w[2],w[3],w[16],w[3],w[3],w[10],w[10],w[16],w[3],
 w[16],w[2],w[16],w[1],w[2],w[37],w[9],w[0],w[1],w[4],w[3],w[0],w[0],w[0]]) := by
 rcases specification with ⟨executed,source,reached,stack,extended,destination,result,counter,alias,cursor,bottomWord,growth,outside,saved⟩
 have old1 : ScalarContinuation.target.mem 1=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[1]?) ScalarContinuation.Controls.complete_observations)
 have old2 : ScalarContinuation.target.mem 2=w[16] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[2]?) ScalarContinuation.Controls.complete_observations)
 have old3 : ScalarContinuation.target.mem 3=w[2] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[3]?) ScalarContinuation.Controls.complete_observations)
 have old16 : ScalarContinuation.target.mem 16=w[2] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[16]?) ScalarContinuation.Controls.complete_observations)
 have old18 : ScalarContinuation.target.mem 18=w[9] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[18]?) ScalarContinuation.Controls.complete_observations)
 have old19 : ScalarContinuation.target.mem 19=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[19]?) ScalarContinuation.Controls.complete_observations)
 have old20 : ScalarContinuation.target.mem 20=w[1] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[20]?) ScalarContinuation.Controls.complete_observations)
 have old21 : ScalarContinuation.target.mem 21=w[4] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[21]?) ScalarContinuation.Controls.complete_observations)
 have old22 : ScalarContinuation.target.mem 22=w[3] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[22]?) ScalarContinuation.Controls.complete_observations)
 have old23 : ScalarContinuation.target.mem 23=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[23]?) ScalarContinuation.Controls.complete_observations)
 have old24 : ScalarContinuation.target.mem 24=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[24]?) ScalarContinuation.Controls.complete_observations)
 have old25 : ScalarContinuation.target.mem 25=w[0] := Option.some.inj (congrArg (fun observed : List Word × List Word => observed.2[25]?) ScalarContinuation.Controls.complete_observations)
 rw [stack,input_stack,owner.arrays.free.cell,destination,result,counter,alias,cursor,bottomWord,
   (saved 0 (by decide)).1,(saved 0 (by decide)).2,
   (saved 1 (by decide)).1,(saved 1 (by decide)).2,
   (saved 2 (by decide)).1,(saved 2 (by decide)).2,
   outside 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   outside 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   outside 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   outside 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide)),
   outside 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))]
 simp only [before,writeMachine,upd,if_true,old1,old2,old3,old16,old18,old19,old20,old21,old22,old23,old24,old25]
 rfl

theorem result_not_late : machine.mem 4≠w[37] := by
 have result := specification.2.2.2.2.2.1
 rw [result]
 decide

theorem late_argument_does_not_fit :
 count.evalT (changed caller ref)=.ok (countValue 37 (by decide)) ∧ ¬10+2*37≤(16:Nat) :=
 ⟨changed_count,by decide⟩

theorem not_keeps : ¬Heap.Keeps (List.prefix_refl caller.H) caller.heap
 ((changed caller ref).setLocal (.here : Idx Γ (.val .uint)) (countValue 3 (by decide))).heap := by
 intro kept
 have object := kept ref
 have values := congrArg (fun object : MObj caller.H A => object.val.map (fun value => value.val)) object
 with_unfolding_all change ([37,9] : List Int)=[3,9] at values
 have unequal : ([37,9] : List Int)≠[3,9] := by decide
 exact unequal values

theorem shallow_boundary :
 (call reference count (.here : Idx Γ (.val .uint)) "orderedScalar" 0).run caller=.error .exhausted ∧
 run (code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8) before=.ok machine 0 :=
 ⟨(specification.2.1 "orderedScalar" 0).trans (if_neg (by decide)),specification.1⟩

end
end Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulScalar.Client
