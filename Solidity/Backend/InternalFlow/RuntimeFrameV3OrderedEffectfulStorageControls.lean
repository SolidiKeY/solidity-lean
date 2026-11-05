import Solidity.Backend.InternalFlow.RuntimeFrameV3OrderedEffectfulStorage
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallerStorageFrameControls

/-! Heap-reading recursion with a protected fragile storage alias. The old
heap cell is mutated after capture; full return observations are retained. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls
noncomputable section
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource OrderedEffectfulScalar
namespace P
abbrev C := CallerStorageFrame.Controls.C
abbrev post := CallerStorageFrame.Controls.post
abbrev ref := CallerStorageFrame.Controls.ref
abbrev alias := CallerStorageFrame.Controls.alias
abbrev slot := CallerStorageFrame.Controls.slot
abbrev old := CallerStorageFrame.Controls.after
abbrev base := CallerStorageFrame.Controls.addresses
end P
abbrev C := P.C
abbrev Γ : Ctx := [.val .uint,.mem A,.alias A]
def F : Frag Γ := ((Frag.init []).push (.alias A) .fragile).push (.mem A) .ok |>.push (.val .uint) .ok

def caller := P.post.withEnv (Δ:=Γ) (countValue 99 (by decide),(some P.ref,(some P.alias,())))
def before := writeMachine (writeMachine (writeMachine (writeMachine P.old 2 w[32]) 3 w[99]) 8 w[99]) 9 w[10]
abbrev base := P.base
abbrev ref := P.ref
def reference : Idx Γ (.mem A) := .there .here

theorem no_struct {s : Name} (r : HRef caller.H (.struct s)) : False := by
 change HRef [A] (.struct s) at r
 rcases r with ⟨i,hi⟩
 cases i with | zero => cases hi | succ i => cases hi

theorem initial : StateRepr 1 1 32 F caller base before := by
 have heap : HeapRepr caller.heap base 16 before :=
   (((CallerStorageFrame.Controls.reached.heap.localWrite 2 (by decide) w[32]).localWrite 3 (by decide) w[99]).localWrite 8 (by decide) w[99]).localWrite 9 (by decide) w[10]
 have old := CallerStorageFrame.Controls.reached.core
 refine ⟨?_,⟨heap.arrays,?_,heap.separated⟩,?_,by decide,
   ⟨fun r => (no_struct r).elim,fun r => (no_struct r).elim,fun r => (no_struct r).elim⟩,
   CallerStorageFrame.Controls.reached.separated,RefFieldsRepr.withoutStructs _ _ _ (fun r => no_struct r)⟩
 · refine ⟨old.store,?_,?_,old.net,old.netSelf,old.bound,?_,old.env,old.funds,old.oracle⟩
   · intro p i;cases i with
     | here => exact ReprV.uint_of rfl
     | there i => cases i with | there i => cases i with | there i => cases i
   · intro R i flag;cases i with
     | there i => cases i with
       | there i => cases i with | here => cases flag | there i => cases i
   · intro R i flag;cases i with
     | there i => cases i with
       | there i => cases i with
         | here => exact ⟨P.alias,P.slot,rfl,rfl,CallerStorageFrame.Controls.path,_,CallerStorageFrame.Controls.live⟩
         | there i => cases i
 · intro p r
   change HRef [A] (.array (.prim p)) at r
   rcases r with ⟨i,hi⟩
   cases i with
   | zero => cases hi;change (32:Nat)≤32;decide
   | succ i => cases hi
 · intro R i;cases i with
   | there i => cases i with
     | here => exact ⟨ref,rfl,rfl⟩
     | there i => cases i with | there i => cases i

def count : Val C Γ .uint := .readMem (.index .dyn (.var reference rfl) (.simple (.lit 0 rfl)))
def value : CompiledVal 1 F count := (Memory.compileVal 1 F count).get (by rfl)
theorem public_root : Memory.compileVal 1 F count=some value := by rfl

theorem evaluated : count.evalT caller=.ok (countValue 7 (by decide)) := by with_unfolding_all rfl

theorem binding : TEnv.get reference caller.env=some ref := by rfl

theorem live : 0<caller.heap.len ref .dyn := by with_unfolding_all decide

theorem ref_base : base ref.id=(⟨32,by decide⟩ : Fin W) := by rfl

theorem current : before.mem 9=w[10] := by rfl

theorem available : ∃ (after : Machine) (addresses : Nat → Fin W),
 run (code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8) before=.ok after 0 ∧
 (∀ f depth,(call reference count (.here : Idx Γ (.val .uint)) f depth).run caller=
   if 7<depth then .ok ⟨(changed caller ref).setLocal .here (countValue 7 (by decide)),List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr 1 1 32 F ((changed caller ref).setLocal .here (countValue 7 (by decide))) addresses after ∧
 after.stack=before.stack ∧ BaseExtends caller.H base addresses ∧
 after.mem 3=w[7] ∧ after.mem 7=w[7] ∧ after.mem 6=w[7] ∧ after.mem 5=before.mem 2 ∧
 after.mem 9=w[10] ∧ after.mem 8=w[10] ∧
 GrowsAllocator 1 32 0 caller base before ((changed caller ref).setLocal .here (countValue 7 (by decide))) addresses after ∧
 (∀ x,x≠3 → x≠9 → x≠8 → x≠5 → x≠6 → x≠7 → (x<10 ∨ 24≤x) →
   after.mem x=(writeMachine before 33 w[37]).mem x) ∧
 (∀ j,j<7 → after.mem (10+2*j)=before.mem 2 ∧ after.mem (10+2*j+1)=.val (wmod (7-j))) := by
 have facts := endpoint (c:=5) caller reference ref binding live count value .here 7 (by decide) evaluated base before initial
   8 9 8 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) current

 rw [ref_base] at facts
 exact facts

noncomputable def machine : Machine := available.choose
noncomputable def addresses : Nat → Fin W := available.choose_spec.choose

theorem specification :
 run (code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8) before=.ok machine 0 ∧
 (∀ f depth,(call reference count (.here : Idx Γ (.val .uint)) f depth).run caller=
   if 7<depth then .ok ⟨(changed caller ref).setLocal .here (countValue 7 (by decide)),List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr 1 1 32 F ((changed caller ref).setLocal .here (countValue 7 (by decide))) addresses machine ∧
 machine.stack=before.stack ∧ BaseExtends caller.H base addresses ∧
 machine.mem 3=w[7] ∧ machine.mem 7=w[7] ∧ machine.mem 6=w[7] ∧ machine.mem 5=before.mem 2 ∧
 machine.mem 9=w[10] ∧ machine.mem 8=w[10] ∧
 GrowsAllocator 1 32 0 caller base before ((changed caller ref).setLocal .here (countValue 7 (by decide))) addresses machine ∧
 (∀ x,x≠3 → x≠9 → x≠8 → x≠5 → x≠6 → x≠7 → (x<10 ∨ 24≤x) →
   machine.mem x=(writeMachine before 33 w[37]).mem x) ∧
 (∀ j,j<7 → machine.mem (10+2*j)=before.mem 2 ∧ machine.mem (10+2*j+1)=.val (wmod (7-j))) :=
 available.choose_spec.choose_spec


theorem outside_old_condition : ¬(∀ {R : RefTy} (i : Idx Γ (.alias R)),F.get i≠.fragile) := by
 intro condition
 exact condition (.there (.there .here)) rfl

theorem fragile_observed :
 ∃ r s,Look.ofTEnv ((changed caller ref).setLocal (.here : Idx Γ (.val .uint)) (countValue 7 (by decide))).env
   (.there (.there .here) : Idx Γ (.alias A))=some r ∧ machine.mem 1=.slot s ∧
 PathSlot C false r s ∧ ∃ v,((changed caller ref).setLocal (.here : Idx Γ (.val .uint)) (countValue 7 (by decide))).storage.findLive r=some v :=
 specification.2.2.1.core.fragile (.there (.there .here)) rfl



theorem before_observations :
 (before.stack,(List.range 34).map (fun i => before.mem i))=
 ([w[77]],[w[34],.slot P.slot,w[32],w[99],w[0],w[32],w[0],w[0],w[99],w[10],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[1],w[7]]) := by rfl

theorem complete_observations :
 (machine.stack,(List.range 34).map (fun i => machine.mem i))=
 ([w[77]],[w[34],.slot P.slot,w[32],w[7],w[0],w[32],w[7],w[7],w[10],w[10],w[32],w[7],w[32],w[6],w[32],w[5],w[32],w[4],w[32],w[3],w[32],w[2],w[32],w[1],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[0],w[1],w[37]]) := by
 rcases specification with ⟨executed,source,reached,stack,extended,destination,result,counter,alias,cursor,bottomWord,growth,outside,saved⟩
 have input_stack : before.stack=[w[77]] := congrArg Prod.fst before_observations
 have old0 : before.mem 0=w[34] := Option.some.inj (congrArg (fun obs : List Word × List Word => obs.2[0]?) before_observations)
 have old1 : before.mem 1=.slot P.slot := Option.some.inj (congrArg (fun obs : List Word × List Word => obs.2[1]?) before_observations)
 have old2 : before.mem 2=w[32] := Option.some.inj (congrArg (fun obs : List Word × List Word => obs.2[2]?) before_observations)
 have old4 : before.mem 4=w[0] := Option.some.inj (congrArg (fun obs : List Word × List Word => obs.2[4]?) before_observations)
 have old24 : before.mem 24=w[0] := Option.some.inj (congrArg (fun obs : List Word × List Word => obs.2[24]?) before_observations)
 have old25 : before.mem 25=w[0] := Option.some.inj (congrArg (fun obs : List Word × List Word => obs.2[25]?) before_observations)
 have old26 : before.mem 26=w[0] := Option.some.inj (congrArg (fun obs : List Word × List Word => obs.2[26]?) before_observations)
 have old27 : before.mem 27=w[0] := Option.some.inj (congrArg (fun obs : List Word × List Word => obs.2[27]?) before_observations)
 have old28 : before.mem 28=w[0] := Option.some.inj (congrArg (fun obs : List Word × List Word => obs.2[28]?) before_observations)
 have old29 : before.mem 29=w[0] := Option.some.inj (congrArg (fun obs : List Word × List Word => obs.2[29]?) before_observations)
 have old30 : before.mem 30=w[0] := Option.some.inj (congrArg (fun obs : List Word × List Word => obs.2[30]?) before_observations)
 have old31 : before.mem 31=w[0] := Option.some.inj (congrArg (fun obs : List Word × List Word => obs.2[31]?) before_observations)
 have old32 : before.mem 32=w[1] := Option.some.inj (congrArg (fun obs : List Word × List Word => obs.2[32]?) before_observations)
 have cell0 : machine.mem 0=before.mem 0 := (outside 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))).trans (upd_other before.mem (x:=33) (y:=0) w[37] (by decide))
 have cell1 : machine.mem 1=before.mem 1 := (outside 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))).trans (upd_other before.mem (x:=33) (y:=1) w[37] (by decide))
 have cell2 : machine.mem 2=before.mem 2 := (outside 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))).trans (upd_other before.mem (x:=33) (y:=2) w[37] (by decide))
 have cell4 : machine.mem 4=before.mem 4 := (outside 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))).trans (upd_other before.mem (x:=33) (y:=4) w[37] (by decide))
 have cell24 : machine.mem 24=before.mem 24 := (outside 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))).trans (upd_other before.mem (x:=33) (y:=24) w[37] (by decide))
 have cell25 : machine.mem 25=before.mem 25 := (outside 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))).trans (upd_other before.mem (x:=33) (y:=25) w[37] (by decide))
 have cell26 : machine.mem 26=before.mem 26 := (outside 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))).trans (upd_other before.mem (x:=33) (y:=26) w[37] (by decide))
 have cell27 : machine.mem 27=before.mem 27 := (outside 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))).trans (upd_other before.mem (x:=33) (y:=27) w[37] (by decide))
 have cell28 : machine.mem 28=before.mem 28 := (outside 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))).trans (upd_other before.mem (x:=33) (y:=28) w[37] (by decide))
 have cell29 : machine.mem 29=before.mem 29 := (outside 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))).trans (upd_other before.mem (x:=33) (y:=29) w[37] (by decide))
 have cell30 : machine.mem 30=before.mem 30 := (outside 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))).trans (upd_other before.mem (x:=33) (y:=30) w[37] (by decide))
 have cell31 : machine.mem 31=before.mem 31 := (outside 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))).trans (upd_other before.mem (x:=33) (y:=31) w[37] (by decide))
 have cell32 : machine.mem 32=before.mem 32 := (outside 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))).trans (upd_other before.mem (x:=33) (y:=32) w[37] (by decide))
 have cell33 : machine.mem 33=w[37] := (outside 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by decide))).trans (upd_same before.mem 33 w[37])
 change (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 4,machine.mem 5,machine.mem 6,machine.mem 7,machine.mem 8,machine.mem 9,machine.mem 10,machine.mem 11,machine.mem 12,machine.mem 13,machine.mem 14,machine.mem 15,machine.mem 16,machine.mem 17,machine.mem 18,machine.mem 19,machine.mem 20,machine.mem 21,machine.mem 22,machine.mem 23,machine.mem 24,machine.mem 25,machine.mem 26,machine.mem 27,machine.mem 28,machine.mem 29,machine.mem 30,machine.mem 31,machine.mem 32,machine.mem 33])=_
 rw [stack,input_stack,destination,result,counter,alias,cursor,bottomWord,(saved 0 (by decide)).1,(saved 0 (by decide)).2,(saved 1 (by decide)).1,(saved 1 (by decide)).2,(saved 2 (by decide)).1,(saved 2 (by decide)).2,(saved 3 (by decide)).1,(saved 3 (by decide)).2,(saved 4 (by decide)).1,(saved 4 (by decide)).2,(saved 5 (by decide)).1,(saved 5 (by decide)).2,(saved 6 (by decide)).1,(saved 6 (by decide)).2,cell0,cell1,cell2,cell4,cell24,cell25,cell26,cell27,cell28,cell29,cell30,cell31,cell32,cell33,old0,old1,old2,old4,old24,old25,old26,old27,old28,old29,old30,old31,old32]
 rfl

theorem changed_count : count.evalT (changed caller ref)=.ok (countValue 37 (by decide)) := by with_unfolding_all rfl

theorem not_keeps : ¬Heap.Keeps (List.prefix_refl caller.H) caller.heap
 ((changed caller ref).setLocal (.here : Idx Γ (.val .uint)) (countValue 7 (by decide))).heap := by
 intro kept
 have object := kept ref
 have values := congrArg (fun object : MObj caller.H A => object.val.map (fun value => value.val)) object
 with_unfolding_all change ([37] : List Int)=[7] at values
 have unequal : ([37] : List Int)≠[7] := by decide
 exact unequal values

theorem shallow_boundary :
 (call reference count (.here : Idx Γ (.val .uint)) "orderedFragile" 0).run caller=.error .exhausted ∧
 run (code 1 5 reference value (.here : Idx Γ (.val .uint)) 9 8) before=.ok machine 0 :=
 ⟨(specification.2.1 "orderedFragile" 0).trans (if_neg (by decide)),specification.1⟩

end
end Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.no_struct' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.no_struct

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.initial

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.public_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.public_root

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.evaluated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.evaluated

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.binding' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.binding

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.live' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.live

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.ref_base' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.ref_base

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.current' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.current

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.available' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.available

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.specification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.specification

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.outside_old_condition' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.outside_old_condition

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.fragile_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.fragile_observed

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.before_observations' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.before_observations

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.complete_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.complete_observations

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.changed_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.changed_count

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.not_keeps' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.not_keeps

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.shallow_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.OrderedEffectfulStorage.Controls.shallow_boundary
