import Solidity.Backend.MemoryOps.CalldataScheduleGrowth
import Solidity.Backend.MemoryOps.CalldataUintScheduleGrowth

/-! Only Option composition of the actual mixed decoded initialization and two
existing finite reached-heap schedules. Typed Bool/uint identity separation is
derived, not a physical disjointness or Source admission premise. -/
namespace Solidity.Backend.MemoryOps
section
variable {D : Source.Layout} {H : HTy} {R Q : RefTy}
variable (c : Source.Calldata D) (off : Nat) (cu : Source.Calldata D) (uo : Nat)
variable (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
variable (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)

def checkedMixedCaptures (bs us : List SnapshotArgs) : Option (Heap H) :=
  (checkedBoolUintSequence c off cu uo hp r a s t d q b u v f).bind fun ini =>
    (runCaptures ini r a bs).bind fun mid => runCaptures mid q b us

theorem checkedMixedCaptures_some (bs us : List SnapshotArgs) (out : Heap H) :
    checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us = some out ↔
      ∃ bm ini mid, checkedCalldataBools c off hp r a s t d = some bm ∧
        checkedCalldataUints cu uo bm q b u v f = some ini ∧
        runCaptures ini r a bs = some mid ∧ runCaptures mid q b us = some out := by
  constructor
  · intro ho
    obtain ⟨ini,hi,ht⟩ := Option.bind_eq_some_iff.mp ho
    obtain ⟨bm,hb,hu⟩ := (checkedBoolUintSequence_some_iff c off cu uo hp r a s t d q b u v f ini).mp hi
    obtain ⟨mid,hs,hsu⟩ := Option.bind_eq_some_iff.mp ht
    exact ⟨bm,ini,mid,hb,hu,hs,hsu⟩
  · rintro ⟨bm,ini,mid,hb,hu,hs,hsu⟩
    exact Option.bind_eq_some_iff.mpr ⟨ini,
      (checkedBoolUintSequence_some_iff c off cu uo hp r a s t d q b u v f ini).mpr ⟨bm,hb,hu⟩,
      Option.bind_eq_some_iff.mpr ⟨mid,hs,hsu⟩⟩

theorem mixedInitialization_all_len {T : RefTy} {E : Ty} (ini : Heap H)
    (hi : checkedBoolUintSequence c off cu uo hp r a s t d q b u v f = some ini)
    (k : HRef H T) (z : ArrTy T E) : ini.len k z = hp.len k z := by
  obtain ⟨bm,hb,hu⟩ := (checkedBoolUintSequence_some_iff c off cu uo hp r a s t d q b u v f ini).mp hi
  exact (uintTransfer_all_len cu uo bm q b u v f ini hu k z).trans
    (boolTransfer_all_len c off hp r a s t d bm hb k z)

theorem checkedMixedCaptures_all_len {T : RefTy} {E : Ty} (bs us : List SnapshotArgs) (out : Heap H)
    (ho : checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us = some out)
    (k : HRef H T) (z : ArrTy T E) : out.len k z = hp.len k z := by
  obtain ⟨bm,ini,mid,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some c off cu uo hp r a s t d q b u v f bs us out).mp ho
  exact (runCaptures_all_len mid out q b us hsu k z).trans
    ((runCaptures_all_len ini mid r a bs hs k z).trans
      ((uintTransfer_all_len cu uo bm q b u v f ini hu k z).trans
        (boolTransfer_all_len c off hp r a s t d bm hb k z)))

theorem checkedMixedCaptures_success (bs us : List SnapshotArgs) :
    (∃ out, checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us = some out) ↔
      (∃ ini, checkedBoolUintSequence c off cu uo hp r a s t d q b u v f = some ini) ∧
        CapturesValid (hp.len r a) bs ∧ CapturesValid (hp.len q b) us := by
  constructor
  · rintro ⟨out,ho⟩
    obtain ⟨bm,ini,mid,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some c off cu uo hp r a s t d q b u v f bs us out).mp ho
    have hi := (checkedBoolUintSequence_some_iff c off cu uo hp r a s t d q b u v f ini).mpr ⟨bm,hb,hu⟩
    have hvb := (runCaptures_success_iff ini r a bs).mp ⟨mid,hs⟩
    have hvu := (runCaptures_success_iff mid q b us).mp ⟨out,hsu⟩
    rw [mixedInitialization_all_len c off cu uo hp r a s t d q b u v f ini hi r a] at hvb
    rw [runCaptures_all_len ini mid r a bs hs q b,
      mixedInitialization_all_len c off cu uo hp r a s t d q b u v f ini hi q b] at hvu
    exact ⟨⟨ini,hi⟩,hvb,hvu⟩
  · rintro ⟨⟨ini,hi⟩,hvb,hvu⟩
    rw [← mixedInitialization_all_len c off cu uo hp r a s t d q b u v f ini hi r a] at hvb
    obtain ⟨mid,hs⟩ := (runCaptures_success_iff ini r a bs).mpr hvb
    rw [← mixedInitialization_all_len c off cu uo hp r a s t d q b u v f ini hi q b,
      ← runCaptures_all_len ini mid r a bs hs q b] at hvu
    obtain ⟨out,hsu⟩ := (runCaptures_success_iff mid q b us).mpr hvu
    exact ⟨out,Option.bind_eq_some_iff.mpr ⟨ini,hi,Option.bind_eq_some_iff.mpr ⟨mid,hs,hsu⟩⟩⟩

theorem checkedMixedCaptures_success_lookup (bs us : List SnapshotArgs) :
    (∃ out, checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us = some out) ↔
      ∃ pb pu, calldataBools c off = some pb ∧ calldataUints cu uo = some pu ∧
        SliceBounds pb.length s t ∧ d+(t-s) ≤ hp.len r a ∧
        SliceBounds pu.length u v ∧ f+(v-u) ≤ hp.len q b ∧
        CapturesValid (hp.len r a) bs ∧ CapturesValid (hp.len q b) us := by
  rw [checkedMixedCaptures_success]
  constructor
  · rintro ⟨⟨ini,hi⟩,hvb,hvu⟩
    obtain ⟨bm,hb,hu⟩ := (checkedBoolUintSequence_some_iff c off cu uo hp r a s t d q b u v f ini).mp hi
    obtain ⟨pb,hpb,hbs,hbd,heB⟩ := boolTransfer_result_lookup c off hp r a s t d bm hb
    obtain ⟨pu,hpu,hus,hud,heU⟩ := uintTransfer_result_lookup cu uo bm q b u v f ini hu
    refine ⟨pb,pu,hpb,hpu,hbs,?_,hus,?_,hvb,hvu⟩
    · simpa only [hbs.length] using hbd
    · rw [boolTransfer_all_len c off hp r a s t d bm hb q b] at hud
      simpa only [hus.length] using hud
  · rintro ⟨pb,pu,hpb,hpu,hbs,hbd,hus,hud,hvb,hvu⟩
    have hfirst : ∃ bm, checkedCalldataBools c off hp r a s t d = some bm := by
      unfold checkedCalldataBools
      rw [hpb]
      simp only [Bind.bind,Option.bind,dif_pos (show s ≤ t ∧ t ≤ pb.length from ⟨hbs.ordered,hbs.bounded⟩),dif_pos hbd]
      exact ⟨_,rfl⟩
    obtain ⟨bm,hb⟩ := hfirst
    have hud' : f+(v-u) ≤ bm.len q b := by rw [boolTransfer_all_len c off hp r a s t d bm hb q b]; exact hud
    have hsecond : ∃ ini, checkedCalldataUints cu uo bm q b u v f = some ini := by
      unfold checkedCalldataUints
      rw [hpu]
      simp only [Bind.bind,Option.bind,dif_pos (show u ≤ v ∧ v ≤ pu.length from ⟨hus.ordered,hus.bounded⟩),dif_pos hud']
      exact ⟨_,rfl⟩
    obtain ⟨ini,hu⟩ := hsecond
    exact ⟨⟨ini,(checkedBoolUintSequence_some_iff c off cu uo hp r a s t d q b u v f ini).mpr ⟨bm,hb,hu⟩⟩,hvb,hvu⟩

theorem checkedMixedCaptures_none_ordered (bs us : List SnapshotArgs) :
    checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us = none ↔
      checkedBoolUintSequence c off cu uo hp r a s t d q b u v f = none ∨
      ∃ ini, checkedBoolUintSequence c off cu uo hp r a s t d q b u v f = some ini ∧
        (runCaptures ini r a bs = none ∨ ∃ mid, runCaptures ini r a bs = some mid ∧ runCaptures mid q b us = none) := by
  unfold checkedMixedCaptures
  cases hi : checkedBoolUintSequence c off cu uo hp r a s t d q b u v f with
  | none => simp only [Option.bind_none,true_or]
  | some ini =>
    simp only [Option.bind_some,Option.some_ne_none,false_or,Option.some.injEq,exists_eq_left']
    cases hs : runCaptures ini r a bs with
    | none => simp only [Option.bind_none,true_or]
    | some mid => simp only [Option.bind_some,Option.some_ne_none,false_or,Option.some.injEq,exists_eq_left']

theorem checkedMixedCaptures_none_first (bs us : List SnapshotArgs) :
    checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us = none ↔
      (checkedCalldataBools c off hp r a s t d = none ∨
        ∃ bm, checkedCalldataBools c off hp r a s t d = some bm ∧ checkedCalldataUints cu uo bm q b u v f = none) ∨
      ∃ ini, checkedBoolUintSequence c off cu uo hp r a s t d q b u v f = some ini ∧
        ((∃ pre x post reached, bs=pre++x::post ∧ runCaptures ini r a pre=some reached ∧
          checkedCaptureOverwrite reached r a r a x.1 x.2.1 x.2.2=none) ∨
          ∃ mid, runCaptures ini r a bs=some mid ∧
            ∃ pre x post reached, us=pre++x::post ∧ runCaptures mid q b pre=some reached ∧
              checkedCaptureOverwrite reached q b q b x.1 x.2.1 x.2.2=none) := by
  simp only [checkedMixedCaptures_none_ordered,checkedBoolUintSequence_none_ordered,runCaptures_none_first]

private theorem boolWrite_frame {T : RefTy} (out : Heap H)
    (ho : checkedCalldataBools c off hp r a s t d = some out) (k : HRef H T) (hne : r.id ≠ k.id) : out.get k=hp.get k := by
  obtain ⟨pb,hpb,hbs,hbd,rfl⟩ := boolTransfer_result_lookup c off hp r a s t d out ho
  exact overwriteSlice_frame hp r k a d _ hbd hne

private theorem uintWrite_frame {T : RefTy} (out : Heap H)
    (ho : checkedCalldataUints cu uo hp q b u v f = some out) (k : HRef H T) (hne : q.id ≠ k.id) : out.get k=hp.get k := by
  obtain ⟨pu,hpu,hus,hud,rfl⟩ := uintTransfer_result_lookup cu uo hp q b u v f out ho
  exact overwriteSlice_frame hp q k b f _ hud hne

theorem checkedMixedCaptures_frame {T : RefTy} (bs us : List SnapshotArgs) (out : Heap H)
    (ho : checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us=some out)
    (k : HRef H T) (hr : r.id ≠ k.id) (hq : q.id ≠ k.id) : out.get k=hp.get k := by
  obtain ⟨bm,ini,mid,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some c off cu uo hp r a s t d q b u v f bs us out).mp ho
  exact (runCaptures_frame mid out q b us hsu k hq).trans
    ((runCaptures_frame ini mid r a bs hs k hr).trans
      ((uintWrite_frame cu uo bm q b u v f ini hu k hq).trans (boolWrite_frame c off hp r a s t d bm hb k hr)))

theorem checkedMixedCaptures_read (bs us : List SnapshotArgs) (out : Heap H)
    (ho : checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us=some out) :
    ∃ pb pu, calldataBools c off=some pb ∧ calldataUints cu uo=some pu ∧
      (∀ k, (MObj.elems a (out.get r))[k]? = (replaceSlice (MObj.elems a (hp.get r)) d ((pb.drop s).take (t-s)))[captureOrigin bs k]?) ∧
      (∀ k, (MObj.elems b (out.get q))[k]? = (replaceSlice (MObj.elems b (hp.get q)) f ((pu.drop u).take (v-u)))[captureOrigin us k]?) := by
  obtain ⟨bm,ini,mid,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some c off cu uo hp r a s t d q b u v f bs us out).mp ho
  obtain ⟨pb,hpb,hbs,hbd,heB⟩ := boolTransfer_result_lookup c off hp r a s t d bm hb
  obtain ⟨pu,hpu,hus,hud,heU⟩ := uintTransfer_result_lookup cu uo bm q b u v f ini hu
  have hne := bool_uint_transfer_ne r a q b
  have hbini : MObj.elems a (ini.get r) = replaceSlice (MObj.elems a (hp.get r)) d ((pb.drop s).take (t-s)) := by
    rw [uintWrite_frame cu uo bm q b u v f ini hu r hne.symm,heB,overwriteSlice_elems]
  have huini : MObj.elems b (ini.get q) = replaceSlice (MObj.elems b (hp.get q)) f ((pu.drop u).take (v-u)) := by
    rw [heU,overwriteSlice_elems,boolWrite_frame c off hp r a s t d bm hb q hne]
  refine ⟨pb,pu,hpb,hpu,?_,?_⟩
  · intro k
    rw [runCaptures_frame mid out q b us hsu r hne.symm,runCaptures_read ini mid r a bs hs k,hbini]
  · intro k
    rw [runCaptures_read mid out q b us hsu k,runCaptures_frame ini mid r a bs hs q hne,huini]

private theorem arrayContents_ext {T : RefTy} {E : Ty} (z : ArrTy T E) (x y : MObj H T)
    (h : MObj.elems z x=MObj.elems z y) : x=y := by
  cases z <;> apply Subtype.ext <;> simpa only [MObj.elems_dyn,MObj.elems_fixed] using h

theorem checkedMixedCaptures_restore (bs us : List SnapshotArgs) (out : Heap H)
    (ho : checkedMixedCaptures c off cu uo hp r a s t d q b u v f bs us=some out) :
    out=hp ↔ ∃ pb pu, calldataBools c off=some pb ∧ calldataUints cu uo=some pu ∧
      (∀ k, (replaceSlice (MObj.elems a (hp.get r)) d ((pb.drop s).take (t-s)))[captureOrigin bs k]? = (MObj.elems a (hp.get r))[k]?) ∧
      (∀ k, (replaceSlice (MObj.elems b (hp.get q)) f ((pu.drop u).take (v-u)))[captureOrigin us k]? = (MObj.elems b (hp.get q))[k]?) := by
  obtain ⟨pb,pu,hpb,hpu,hr,hu⟩ := checkedMixedCaptures_read c off cu uo hp r a s t d q b u v f bs us out ho
  constructor
  · intro he
    subst out
    exact ⟨pb,pu,hpb,hpu,fun k => (hr k).symm,fun k => (hu k).symm⟩
  · rintro ⟨pb',pu',hpb',hpu',hbAgree,huAgree⟩
    have eb : pb=pb' := Option.some.inj (hpb.symm.trans hpb')
    have eu : pu=pu' := Option.some.inj (hpu.symm.trans hpu')
    subst pb'; subst pu'
    have rb : out.get r=hp.get r := arrayContents_ext a _ _ (List.ext_getElem? (fun k => (hr k).trans (hbAgree k)))
    have ru : out.get q=hp.get q := arrayContents_ext b _ _ (List.ext_getElem? (fun k => (hu k).trans (huAgree k)))
    apply memoryOps_heap_ext
    intro T k
    by_cases er : r.id=k.id
    · obtain ⟨rfl,hk⟩ := HRef.heq_of_id r k er
      cases hk
      exact rb
    · by_cases eq : q.id=k.id
      · obtain ⟨rfl,hk⟩ := HRef.heq_of_id q k eq
        cases hk
        exact ru
      · exact checkedMixedCaptures_frame c off cu uo hp r a s t d q b u v f bs us out ho k er eq
end
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_some
/-- info: 'Solidity.Backend.MemoryOps.mixedInitialization_all_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mixedInitialization_all_len
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_all_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_all_len
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_success
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_success_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_success_lookup
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_none_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_none_ordered
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_none_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_none_first
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_frame
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_read
/-- info: 'Solidity.Backend.MemoryOps.checkedMixedCaptures_restore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedMixedCaptures_restore
end Solidity.Backend.MemoryOps
