import Solidity.Backend.MemoryOps.MixedCalldataScheduleControls

/-! Per-destination INITIAL footprints, sharper than joint heap restoration.
An old Boolean child may be restored while uint remains changed. No final child
relation, stagewise preservation or physical/Source execution is a premise. -/
namespace Solidity.Backend.MemoryOps
section
variable {D : Source.Layout} {H : HTy} {R Q : RefTy}
variable (c : Source.Calldata D) (off : Nat) (cu : Source.Calldata D) (uo : Nat)
variable (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
variable (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
variable (bs us : List SnapshotArgs) (out : Heap H)
variable (ho : checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us=some out)

private theorem childObject_ext {T : RefTy} {E : Ty} (z : ArrTy T E) (x y : MObj H T)
    (h : MObj.elems z x=MObj.elems z y) : x=y := by
  cases z <;> apply Subtype.ext <;> simpa only [MObj.elems_dyn,MObj.elems_fixed] using h

include ho in
theorem checkedMixedCaptures_bool_restore : out.get r=hp.get r ↔
    ∃ pb, calldataBools c off=some pb ∧ ∀ k,
      (replaceSlice (MObj.elems a (hp.get r)) d ((pb.drop s).take (t-s)))[captureOrigin bs k]?=(MObj.elems a (hp.get r))[k]? := by
  obtain ⟨pb,pu,hpb,hpu,hr,hu⟩ := checkedMixedCaptures_read c off cu uo hp r a s t d q b u v f bs us out ho
  constructor
  · intro he
    exact ⟨pb,hpb,fun k => (hr k).symm.trans (congrArg (fun o => (MObj.elems a o)[k]?) he)⟩
  · rintro ⟨pb',hpb',ha⟩
    have he : pb=pb' := Option.some.inj (hpb.symm.trans hpb')
    subst pb'
    have hv : MObj.elems a (out.get r)=MObj.elems a (hp.get r) := List.ext_getElem? (fun k => (hr k).trans (ha k))
    exact childObject_ext a _ _ hv

include ho in
theorem checkedMixedCaptures_uint_restore : out.get q=hp.get q ↔
    ∃ pu, calldataUints cu uo=some pu ∧ ∀ k,
      (replaceSlice (MObj.elems b (hp.get q)) f ((pu.drop u).take (v-u)))[captureOrigin us k]?=(MObj.elems b (hp.get q))[k]? := by
  obtain ⟨pb,pu,hpb,hpu,hr,hu⟩ := checkedMixedCaptures_read c off cu uo hp r a s t d q b u v f bs us out ho
  constructor
  · intro he
    exact ⟨pu,hpu,fun k => (hu k).symm.trans (congrArg (fun o => (MObj.elems b o)[k]?) he)⟩
  · rintro ⟨pu',hpu',ha⟩
    have he : pu=pu' := Option.some.inj (hpu.symm.trans hpu')
    subst pu'
    have hv : MObj.elems b (out.get q)=MObj.elems b (hp.get q) := List.ext_getElem? (fun k => (hu k).trans (ha k))
    exact childObject_ext b _ _ hv
end

theorem BoolChildRepr.mixed_schedule_iff {D : Source.Layout} {H : HTy} {Q : RefTy}
    {old c cu : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hi : BoolChildRepr old address hp sv r) (off uo s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (bs us : List SnapshotArgs) (out : Heap H)
    (ho : checkedMixedCaptures c off cu uo hp r .dyn s t d q b u v f bs us=some out) :
    BoolChildRepr old address out sv r ↔ ∃ pb, calldataBools c off=some pb ∧ ∀ k,
      (replaceSlice (MObj.elems .dyn (hp.get r)) d ((pb.drop s).take (t-s)))[captureOrigin bs k]?=(MObj.elems .dyn (hp.get r))[k]? := by
  rw [hi.at_heap_iff out]
  exact checkedMixedCaptures_bool_restore c off cu uo hp r .dyn s t d q b u v f bs us out ho

namespace MixedChildControls
open SequenceFixtures
open MixedScheduleControls (input input_bool input_uint)
open UintScheduleControls (repairs)
private abbrev B := BoolChildRef
private abbrev V : RefTy := .array (.prim .uint)
private abbrev P : RefTy := .fixed (.ref B) 2
private abbrev H : HTy := [B,V,P]
private def r : HRef H B := ⟨0,rfl⟩
private def q : HRef H V := ⟨1,rfl⟩
private def parent : HRef H P := ⟨2,rfl⟩
private def eight : U := ⟨8,by decide⟩
private def nine : U := ⟨9,by decide⟩
private def old (n : Nat) := [true,false,false]++List.replicate n false
private def hp (n : Nat) (hn : n+3<2^256) : Heap H :=
  (⟨old n,by simp only [old,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,
    ⟨[seven,eight,eight]++List.replicate n maximum,by simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,
    ⟨[r,r],rfl⟩,())
private def sv : Source.Data D BoolChildTy := .val (.cdRef rfl 7)
private theorem initial (n : Nat) (hn : n+3<2^256) : BoolChildRepr (bools (old n)) (fun _ => 7) (hp n hn) sv r := by
  refine ⟨rfl,?_⟩; simp only [MObj.elems_dyn]; rfl
private theorem lookup : calldataBools input 7=some [true] := by rw [calldataBools_lookup input_bool]; rfl
private theorem uint_lookup : calldataUints input 9=some [nine] := by rfl
private theorem uint_values : List.ofFn (fun i : Fin 1 => calldataUint
    (Source.Data.val (sourceUint (D:=D) ([nine][i]))))=[nine] := by
  simpa only [List.ofFn_succ,List.ofFn_zero] using congrArg (fun word : U => [word]) (calldataUint_sourceUint (D:=D) nine)

/-- The OLD represented child is repaired, but the other destination remains
materially changed. A joint whole-heap premise would unnecessarily miss it. -/
theorem repaired_child_changed_uint (n copies : Nat) (hn : n+3<2^256) :
    ∃ out, checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 (repairs copies) []=some out ∧
      BoolChildRepr (bools (old n)) (fun _ => 7) out sv r ∧
      MObj.elems .dyn (out.get r)=old n ∧
      MObj.elems .dyn (out.get q)=[seven,nine,eight]++List.replicate n maximum ∧
      (MObj.elems .fixed (out.get parent)).map HRef.id=[0,0] ∧ out ≠ hp n hn ∧
      ¬ (∃ pu, calldataUints input 9=some pu ∧ ∀ k,
        (replaceSlice (MObj.elems .dyn ((hp n hn).get q)) 1 ((pu.drop 0).take (1-0)))[captureOrigin [] k]?=(MObj.elems .dyn ((hp n hn).get q))[k]?) := by
  have hfull := MixedScheduleControls.fixture_restore (hp n hn) r .dyn q .dyn
    (List.replicate n false) (List.replicate n maximum)
    (by simp only [MObj.elems_dyn]; rfl) (by simp only [MObj.elems_dyn]; rfl) copies 0
  obtain ⟨bm,ini,out,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp hfull
  have ho : checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 (repairs copies) []=some out :=
    (checkedMixedCaptures_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr ⟨bm,ini,out,hb,hu,hs,rfl⟩
  have hchild := (BoolChildRepr.mixed_schedule_iff (initial n hn) 7 9 0 1 1 q .dyn 0 1 1 _ _ out ho).mpr
    ⟨[true],lookup,by simp only [MObj.elems_dyn]; exact MixedScheduleControls.initial_bool_agreement (List.replicate n false) copies⟩
  have hbvalue : MObj.elems .dyn (out.get r)=old n := by
    rw [(initial n hn).at_heap_iff out |>.mp hchild]; simp only [MObj.elems_dyn]; rfl
  have hi := (checkedBoolUintSequence_some_iff input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 ini).mpr ⟨bm,hb,hu⟩
  have huvalue : MObj.elems .dyn (out.get q)=[seven,nine,eight]++List.replicate n maximum := by
    obtain ⟨pb,pu,hpb,hpu,hr,hur⟩ := checkedMixedCaptures_read _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho
    have eu : pu=[nine] := Option.some.inj (hpu.symm.trans uint_lookup)
    subst pu
    apply List.ext_getElem?
    intro k
    rw [hur k]; simp only [MObj.elems_dyn]; rfl
  have hneq : out.get q ≠ (hp n hn).get q := by
    intro he
    have hv := congrArg (fun o : MObj H V => (MObj.elems .dyn o)[1]?) he
    dsimp only at hv
    rw [huvalue] at hv
    simp only [MObj.elems_dyn] at hv
    change (some nine : Option U)=some eight at hv
    have hnine := congrArg (fun word : U => word.val) (Option.some.inj hv)
    change (9 : Int)=8 at hnine
    contradiction
  refine ⟨out,ho,hchild,hbvalue,huvalue,?_,?_,?_⟩
  · rw [checkedMixedCaptures_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho parent (by decide) (by decide)]
    simp only [MObj.elems_fixed]; rfl
  · intro he
    exact hneq (congrArg (fun h : Heap H => h.get q) he)
  · intro ha
    exact hneq ((checkedMixedCaptures_uint_restore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho).mpr ha)

/-- Same actual decoded inputs and changed uint, but omitting Boolean repair
invalidates the old child relation; unchanged parent IDs do not repair contents. -/
theorem unrepaired_child (n : Nat) (hn : n+3<2^256) :
    ∃ out, checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 [] []=some out ∧
      ¬ BoolChildRepr (bools (old n)) (fun _ => 7) out sv r ∧
      MObj.elems .dyn (out.get r)=[true,true,false]++List.replicate n false ∧
      MObj.elems .dyn (out.get q)=[seven,nine,eight]++List.replicate n maximum ∧
      (MObj.elems .fixed (out.get parent)).map HRef.id=[0,0] := by
  have hfull := MixedScheduleControls.fixture_restore (hp n hn) r .dyn q .dyn
    (List.replicate n false) (List.replicate n maximum)
    (by simp only [MObj.elems_dyn]; rfl) (by simp only [MObj.elems_dyn]; rfl) 0 0
  obtain ⟨bm,ini,mid,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp hfull
  have ho : checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 [] []=some ini :=
    (checkedMixedCaptures_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr ⟨bm,ini,ini,hb,hu,rfl,rfl⟩
  have hi := (checkedBoolUintSequence_some_iff input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 ini).mpr ⟨bm,hb,hu⟩
  have hv := checkedBoolUintSequence_elems input_bool input_uint _ _ _ _ _ _ _ _ _ _ _ ini hi
  refine ⟨ini,ho,?_,?_,?_,?_⟩
  · intro hc
    obtain ⟨pb,hpb,ha⟩ := (BoolChildRepr.mixed_schedule_iff (initial n hn) 7 9 0 1 1 q .dyn 0 1 1 [] [] ini ho).mp hc
    have he : pb=[true] := Option.some.inj (hpb.symm.trans lookup)
    subst pb
    have hbad := ha 1
    simp only [MObj.elems_dyn] at hbad
    change (some true : Option Bool)=some false at hbad
    cases hbad
  · rw [hv.1]
    change replaceSlice (MObj.elems .dyn ((hp n hn).get r)) 1 (([true].drop 0).take (1-0))=[true,true,false]++List.replicate n false
    simp only [MObj.elems_dyn]; rfl
  · obtain ⟨pb,pu,hpb,hpu,hr,hur⟩ := checkedMixedCaptures_read _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho
    have eu : pu=[nine] := Option.some.inj (hpu.symm.trans uint_lookup)
    subst pu
    apply List.ext_getElem?
    intro k
    rw [hur k]; simp only [MObj.elems_dyn]; rfl
  · rw [checkedMixedCaptures_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho parent (by decide) (by decide)]
    simp only [MObj.elems_fixed]; rfl
end MixedChildControls
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_bool_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_bool_restore
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_uint_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_uint_restore
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.mixed_schedule_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.mixed_schedule_iff
/-- info: 'Solidity.Backend.MemoryOps.MixedChildControls.repaired_child_changed_uint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms MixedChildControls.repaired_child_changed_uint
/-- info: 'Solidity.Backend.MemoryOps.MixedChildControls.unrepaired_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms MixedChildControls.unrepaired_child
end Solidity.Backend.MemoryOps
