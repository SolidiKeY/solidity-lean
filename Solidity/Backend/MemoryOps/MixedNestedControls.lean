import Solidity.Backend.MemoryOps.MixedNestedFootprint

namespace Solidity.Backend.MemoryOps.MixedNestedControls
open SequenceFixtures
open MixedScheduleControls (input input_bool input_uint)
open UintScheduleControls (repairs)
private abbrev B := BoolChildRef
private abbrev V : RefTy := .array (.prim .uint)
private abbrev C := RefChildRef
private abbrev H : HTy := [B,B,V,C,C]
private def r : HRef H B := ⟨0,rfl⟩
private def other : HRef H B := ⟨1,rfl⟩
private def q : HRef H V := ⟨2,rfl⟩
private def root : HRef H C := ⟨3,rfl⟩
private def separate : HRef H C := ⟨4,rfl⟩
private def address (i : Nat) := 7+i
private def eight : U := ⟨8,by decide⟩
private def nine : U := ⟨9,by decide⟩
private def two : U := ⟨2,by decide⟩
private def bold (n : Nat) := [true,false,false]++List.replicate n false
private def uold (n : Nat) := [seven,eight,eight]++List.replicate n maximum
private def aliases (n : Nat) : List (HRef H B) := [r,other,r]++List.replicate n other
private def untouched (n : Nat) : List (HRef H B) := [other,other]++List.replicate n other
private def hp (n : Nat) (hn : n+3<2^256) : Heap H :=
  (⟨bold n,by simp only [bold,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,
    ⟨[false,true],by decide⟩,
    ⟨uold n,by simp only [uold,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,
    ⟨aliases n,by simp only [aliases,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,
    ⟨untouched n,by simp only [untouched,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,())
private def tables (n : Nat) : Source.Calldata D := ⟨[],fun off =>
  if off=7 then some ⟨BoolChildTy,decodedBools (bold n)⟩ else
  if off=8 then some ⟨BoolChildTy,decodedBools [false,true]⟩ else
  if off=10 then some ⟨RefChildTy,decodedChildRefs address (aliases n)⟩ else
  if off=11 then some ⟨RefChildTy,decodedChildRefs address (untouched n)⟩ else none⟩
private def sv : Source.Data D RefChildTy := .val (.cdRef rfl (address root.id))
private def ssep : Source.Data D RefChildTy := .val (.cdRef rfl (address separate.id))
private theorem leaf_cases (n : Nat) (leaf : HRef H B) (hm : leaf ∈ aliases n) : leaf=r ∨ leaf=other := by
  rcases List.mem_append.mp hm with h | h
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact Or.inr (List.mem_replicate.mp h).2
private theorem separate_leaf (n : Nat) (leaf : HRef H B) (hm : leaf ∈ untouched n) : leaf=other := by
  rcases List.mem_append.mp hm with h | h
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h | h <;> exact h
  · exact (List.mem_replicate.mp h).2
private theorem first_repr (n : Nat) (hn : n+3<2^256) :
    BoolChildRepr (tables n) address (hp n hn) (.val (.cdRef rfl (address r.id))) r := by
  refine ⟨rfl,?_⟩; simp only [MObj.elems_dyn]; rfl
private theorem other_repr (n : Nat) (hn : n+3<2^256) :
    BoolChildRepr (tables n) address (hp n hn) (.val (.cdRef rfl (address other.id))) other := by
  refine ⟨rfl,?_⟩; simp only [MObj.elems_dyn]; rfl

/-- Independently inhabited INITIAL old tables contain repeated selected aliases
AND a separate unaffected child. No output relation or address injection premise. -/
theorem initial (n : Nat) (hn : n+3<2^256) :
    RefChildRepr (tables n) address (hp n hn) sv root ∧
    RefChildRepr (tables n) address (hp n hn) ssep separate := by
  constructor
  · refine ⟨rfl,?_,?_⟩
    · simp only [MObj.elems_dyn]; rfl
    · intro leaf hl
      have hm : leaf ∈ aliases n := by simpa only [MObj.elems_dyn] using hl
      rcases leaf_cases n leaf hm with rfl | rfl
      · exact first_repr n hn
      · exact other_repr n hn
  · refine ⟨rfl,?_,?_⟩
    · simp only [MObj.elems_dyn]; rfl
    · intro leaf hl
      have hm : leaf ∈ untouched n := by simpa only [MObj.elems_dyn] using hl
      have he := separate_leaf n leaf hm
      subst leaf
      exact other_repr n hn
private theorem lookupB : calldataBools input 7=some [true] := by rw [calldataBools_lookup input_bool]; rfl
private theorem lookupU : calldataUints input 9=some [nine] := by rfl
private theorem bool_agrees (n copies : Nat) (hn : n+3<2^256) :
    ∃ pb, calldataBools input 7=some pb ∧ ∀ k,
      (replaceSlice (MObj.elems .dyn ((hp n hn).get r)) 1 ((pb.drop 0).take (1-0)))[captureOrigin (repairs copies) k]?=(MObj.elems .dyn ((hp n hn).get r))[k]? := by
  refine ⟨[true],lookupB,?_⟩
  simp only [MObj.elems_dyn]
  exact MixedScheduleControls.initial_bool_agreement (List.replicate n false) copies
private theorem hfull (n copies : Nat) (hn : n+3<2^256) :
    checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 (repairs copies) (repairs 0)=some (hp n hn) :=
  MixedScheduleControls.fixture_restore _ r .dyn q .dyn _ _
    (by simp only [MObj.elems_dyn]; rfl) (by simp only [MObj.elems_dyn]; rfl) copies 0

/-- The ACTUAL mixed run repairs every selected Boolean alias while uint
remains changed; the alias criterion is discharged from INITIAL values only. -/
theorem repaired (n copies : Nat) (hn : n+3<2^256) :
    ∃ bm ini out, checkedCalldataBools input 7 (hp n hn) r .dyn 0 1 1=some bm ∧
      checkedCalldataUints input 9 bm q .dyn 0 1 1=some ini ∧
      runCaptures ini r .dyn (repairs copies)=some out ∧
      checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 (repairs copies) []=some out ∧
      RefChildRepr (tables n) address out sv root ∧
      MObj.elems .dyn (out.get r)=bold n ∧
      MObj.elems .dyn (out.get q)=[seven,nine,eight]++List.replicate n maximum ∧
      MObj.elems .dyn (out.get other)=[false,true] ∧
      (MObj.elems .dyn (out.get root)).map HRef.id=[0,1,0]++List.replicate n 1 := by
  obtain ⟨bm,ini,out,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp (hfull n copies hn)
  have ho : checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 (repairs copies) []=some out :=
    (checkedMixedCaptures_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr ⟨bm,ini,out,hb,hu,hs,rfl⟩
  have hpost := ((initial n hn).1.mixed_schedule_iff input 7 input 9 r .dyn 0 1 1 q .dyn 0 1 1 _ _ out ho).mpr
    (fun leaf hmem he => bool_agrees n copies hn)
  have hr : out.get r=(hp n hn).get r := (checkedMixedCaptures_bool_restore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho).mpr (bool_agrees n copies hn)
  have huval : MObj.elems .dyn (out.get q)=[seven,nine,eight]++List.replicate n maximum := by
    obtain ⟨pb,pu,hpb,hpu,hbr,hur⟩ := checkedMixedCaptures_read _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho
    have he : pu=[nine] := Option.some.inj (hpu.symm.trans lookupU)
    subst pu
    apply List.ext_getElem?
    intro k
    rw [hur k]; simp only [MObj.elems_dyn]; rfl
  refine ⟨bm,ini,out,hb,hu,hs,ho,hpost,?_,huval,?_,?_⟩
  · rw [hr]; simp only [MObj.elems_dyn]; rfl
  · rw [checkedMixedCaptures_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho other (by decide) (by decide)]
    simp only [MObj.elems_dyn]; rfl
  · rw [checkedMixedCaptures_ref_root_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho root]
    simp only [MObj.elems_dyn]
    change (aliases n).map HRef.id=[0,1,0]++List.replicate n 1
    simp only [aliases,List.map_append,List.map_cons,List.map_nil,List.map_replicate]
    rfl
private theorem selected (n : Nat) (hn : n+3<2^256) : r ∈ MObj.elems .dyn ((hp n hn).get root) := by
  simp only [MObj.elems_dyn]
  change r ∈ aliases n
  exact List.mem_append_left _ List.mem_cons_self

private theorem no_repair_false (n : Nat) (hn : n+3<2^256) (out : Heap H)
    (ho : checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 [] []=some out) :
    ¬ RefChildRepr (tables n) address out sv root := by
  intro hr
  obtain ⟨pb,hpb,ha⟩ := ((initial n hn).1.mixed_schedule_iff input 7 input 9 r .dyn 0 1 1 q .dyn 0 1 1 [] [] out ho).mp hr r (selected n hn) rfl
  have he : pb=[true] := Option.some.inj (hpb.symm.trans lookupB)
  subst pb
  have hbad := ha 1
  simp only [MObj.elems_dyn] at hbad
  change (some true : Option Bool)=some false at hbad
  cases hbad

private theorem initialized_values (n : Nat) (hn : n+3<2^256) (out : Heap H)
    (ho : checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 [] []=some out) :
    MObj.elems .dyn (out.get r)=[true,true,false]++List.replicate n false ∧
    MObj.elems .dyn (out.get q)=[seven,nine,eight]++List.replicate n maximum := by
  obtain ⟨pb,pu,hpb,hpu,hr,hu⟩ := checkedMixedCaptures_read _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho
  have eb : pb=[true] := Option.some.inj (hpb.symm.trans lookupB)
  have eu : pu=[nine] := Option.some.inj (hpu.symm.trans lookupU)
  subst pb; subst pu
  constructor
  · apply List.ext_getElem?
    intro k
    rw [hr k]; simp only [MObj.elems_dyn]; rfl
  · apply List.ext_getElem?
    intro k
    rw [hu k]; simp only [MObj.elems_dyn]; rfl

private theorem observations (n : Nat) (hn : n+3<2^256) (out : Heap H)
    (ho : out.get other=(hp n hn).get other) (hr : out.get root=(hp n hn).get root)
    (hs : out.get separate=(hp n hn).get separate) :
    MObj.elems .dyn (out.get other)=[false,true] ∧
    (MObj.elems .dyn (out.get root)).map HRef.id=[0,1,0]++List.replicate n 1 ∧
    (MObj.elems .dyn (out.get separate)).map HRef.id=[1,1]++List.replicate n 1 := by
  rw [ho,hr,hs]
  simp only [MObj.elems_dyn]
  refine ⟨rfl,?_,?_⟩
  · change (aliases n).map HRef.id=_
    simp only [aliases,List.map_append,List.map_cons,List.map_nil,List.map_replicate]; rfl
  · change (untouched n).map HRef.id=_
    simp only [untouched,List.map_append,List.map_cons,List.map_nil,List.map_replicate]; rfl

/-- FULL old/decoded/repaired/final vectors and every-stage reference identities.
The actual both-decoded intermediate BREAKS the old nested relation. -/
theorem stages (n copies : Nat) (hn : n+3<2^256) :
    ∃ bm ini out, checkedCalldataBools input 7 (hp n hn) r .dyn 0 1 1=some bm ∧
      checkedCalldataUints input 9 bm q .dyn 0 1 1=some ini ∧ runCaptures ini r .dyn (repairs copies)=some out ∧
      checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 (repairs copies) []=some out ∧
      RefChildRepr (tables n) address (hp n hn) sv root ∧
      ¬ RefChildRepr (tables n) address ini sv root ∧ RefChildRepr (tables n) address out sv root ∧
      [MObj.elems .dyn ((hp n hn).get r),MObj.elems .dyn (bm.get r),MObj.elems .dyn (ini.get r),MObj.elems .dyn (out.get r),MObj.elems .dyn (out.get r)] =
        [bold n,[true,true,false]++List.replicate n false,[true,true,false]++List.replicate n false,bold n,bold n] ∧
      [MObj.elems .dyn ((hp n hn).get q),MObj.elems .dyn (bm.get q),MObj.elems .dyn (ini.get q),MObj.elems .dyn (out.get q),MObj.elems .dyn (out.get q)] =
        [uold n,uold n,[seven,nine,eight]++List.replicate n maximum,[seven,nine,eight]++List.replicate n maximum,[seven,nine,eight]++List.replicate n maximum] ∧
      ∀ h ∈ [hp n hn,bm,ini,out,out], MObj.elems .dyn (h.get other)=[false,true] ∧
        (MObj.elems .dyn (h.get root)).map HRef.id=[0,1,0]++List.replicate n 1 ∧
        (MObj.elems .dyn (h.get separate)).map HRef.id=[1,1]++List.replicate n 1 := by
  obtain ⟨bm,ini,out,hb,hu,hs,ho,hr,hbval,huval,hother,hroot⟩ := repaired n copies hn
  have hi : checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 [] []=some ini :=
    (checkedMixedCaptures_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr ⟨bm,ini,ini,hb,hu,rfl,rfl⟩
  have hini := initialized_values n hn ini hi
  have hbvalues : MObj.elems .dyn (bm.get r)=[true,true,false]++List.replicate n false := by
    obtain ⟨pb,hpb,hbs,hbd,he⟩ := boolTransfer_result_lookup input 7 (hp n hn) r .dyn 0 1 1 bm hb
    have ep : pb=[true] := Option.some.inj (hpb.symm.trans lookupB)
    subst pb
    rw [he,overwriteSlice_elems]; simp only [MObj.elems_dyn]; rfl
  have huvalues : MObj.elems .dyn (bm.get q)=uold n := by
    rw [checkedCalldataBools_frame input_bool _ _ _ _ _ _ _ hb q (by decide)]
    simp only [MObj.elems_dyn]; rfl
  refine ⟨bm,ini,out,hb,hu,hs,ho,(initial n hn).1,no_repair_false n hn ini hi,hr,?_,?_,?_⟩
  · rw [hbvalues,hini.1,hbval]; simp only [MObj.elems_dyn]; rfl
  · rw [huvalues,hini.2,huval]; simp only [MObj.elems_dyn]; rfl
  · have obm := observations n hn bm
        (checkedCalldataBools_frame input_bool _ _ _ _ _ _ _ hb other (by decide))
        (checkedCalldataBools_frame input_bool _ _ _ _ _ _ _ hb root (by decide))
        (checkedCalldataBools_frame input_bool _ _ _ _ _ _ _ hb separate (by decide))
    have oini := observations n hn ini
        (checkedMixedCaptures_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi other (by decide) (by decide))
        (checkedMixedCaptures_ref_root_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi root)
        (checkedMixedCaptures_ref_root_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi separate)
    have oout := observations n hn out
        (checkedMixedCaptures_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho other (by decide) (by decide))
        (checkedMixedCaptures_ref_root_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho root)
        (checkedMixedCaptures_ref_root_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho separate)
    intro h hh
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl
    · exact observations n hn _ rfl rfl rfl
    · exact obm
    · exact oini
    · exact oout
    · exact oout

/-- SAME old table and SAME successful un-repaired run: the aliased root fails,
but the nonempty disjoint root still corresponds. Wrong inner false-read is
concrete despite identical reference fields. -/
theorem skipped_and_disjoint (n : Nat) (hn : n+3<2^256) :
    ∃ out, checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 [] []=some out ∧
      ¬ RefChildRepr (tables n) address out sv root ∧ RefChildRepr (tables n) address out ssep separate ∧
      MObj.elems .dyn (out.get r)=[true,true,false]++List.replicate n false ∧
      MObj.elems .dyn (out.get q)=[seven,nine,eight]++List.replicate n maximum ∧
      MObj.elems .dyn (out.get other)=[false,true] ∧
      (MObj.elems .dyn (out.get root)).map HRef.id=[0,1,0]++List.replicate n 1 ∧
      (MObj.elems .dyn (out.get separate)).map HRef.id=[1,1]++List.replicate n 1 ∧
      out.index root .dyn zero=some r ∧ out.index r .dyn one=some true ∧
      DecodedBoolRead (tables n) (address r.id) 1 false ∧ out.index r .dyn one ≠ some false := by
  obtain ⟨bm,ini,mid,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp (hfull n 0 hn)
  have ho : checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 [] []=some ini :=
    (checkedMixedCaptures_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr ⟨bm,ini,ini,hb,hu,rfl,rfl⟩
  have hv := initialized_values n hn ini ho
  have hr := checkedMixedCaptures_ref_root_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho root
  have hsep := ((initial n hn).2.mixed_schedule_iff input 7 input 9 r .dyn 0 1 1 q .dyn 0 1 1 [] [] ini ho).mpr (by
    intro leaf hmem he
    have hm : leaf ∈ untouched n := by simpa only [MObj.elems_dyn] using hmem
    have hleaf := separate_leaf n leaf hm
    subst leaf
    exact False.elim ((by decide : r.id ≠ other.id) he))
  have obs := observations n hn ini
    (checkedMixedCaptures_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho other (by decide) (by decide)) hr
    (checkedMixedCaptures_ref_root_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho separate)
  have hidx : ini.index r .dyn one=some true := by
    change (MObj.elems .dyn (ini.get r))[1]?=some true
    rw [hv.1]; rfl
  refine ⟨ini,ho,no_repair_false n hn ini ho,hsep,hv.1,hv.2,obs.1,obs.2.1,obs.2.2,?_,hidx,?_,?_⟩
  · change (MObj.elems .dyn (ini.get root))[0]?=some r
    rw [hr]; simp only [MObj.elems_dyn]; rfl
  · exact ((first_repr n hn).read_iff 1 false).mpr (by simp only [MObj.elems_dyn]; rfl)
  · rw [hidx]; decide

/-- Actual outer+inner indices and OLD decoded reads, including two repeated
aliases and the separate child; invokes the NEW composed index_bool adapter. -/
theorem two_level_reads (n copies : Nat) (hn : n+3<2^256) :
    ∃ out, checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 (repairs copies) []=some out ∧
      out.index root .dyn zero=some r ∧ out.index root .dyn one=some other ∧ out.index root .dyn two=some r ∧
      out.index r .dyn one=some false ∧ out.index other .dyn one=some true ∧
      DecodedArrayRead (tables n) (address root.id) BoolChildTy none 0 (.val (.cdRef rfl (address r.id))) ∧
      DecodedArrayRead (tables n) (address root.id) BoolChildTy none 1 (.val (.cdRef rfl (address other.id))) ∧
      DecodedBoolRead (tables n) (address r.id) 1 false ∧ DecodedBoolRead (tables n) (address other.id) 1 true := by
  obtain ⟨bm,ini,out,hb,hu,hs,ho,hpost,hbval,huval,hother,hroot⟩ := repaired n copies hn
  have hf := checkedMixedCaptures_ref_root_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho root
  have idx0 : out.index root .dyn zero=some r := by
    change (MObj.elems .dyn (out.get root))[0]?=some r
    rw [hf]; simp only [MObj.elems_dyn]; rfl
  have idx1 : out.index root .dyn one=some other := by
    change (MObj.elems .dyn (out.get root))[1]?=some other
    rw [hf]; simp only [MObj.elems_dyn]; rfl
  have idx2 : out.index root .dyn two=some r := by
    change (MObj.elems .dyn (out.get root))[2]?=some r
    rw [hf]; simp only [MObj.elems_dyn]; rfl
  have bit0 : out.index r .dyn one=some false := by
    change (MObj.elems .dyn (out.get r))[1]?=some false
    rw [hbval]; rfl
  have bit1 : out.index other .dyn one=some true := by
    change (MObj.elems .dyn (out.get other))[1]?=some true
    rw [hother]; rfl
  have bound0 : zero.val.toNat < (hp n hn).len root .dyn := by
    simp only [Heap.len,MObj.elems_dyn]
    change 0 < (aliases n).length
    simp only [aliases,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
  obtain ⟨leaf,hidx,hcd,hbool⟩ := (initial n hn).1.mixed_schedule_index_bool input 7 input 9
    r .dyn 0 1 1 q .dyn 0 1 1 _ _ out ho (fun leaf hm he => bool_agrees n copies hn) zero bound0 one false
  have he : leaf=r := Option.some.inj (hidx.symm.trans idx0)
  subst leaf
  have bound1 : one.val.toNat < out.len root .dyn := by
    rw [checkedMixedCaptures_all_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho root .dyn]
    simp only [Heap.len,MObj.elems_dyn]
    change 1 < (aliases n).length
    simp only [aliases,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
  obtain ⟨leaf,hidx1,hcd1,hbool1⟩ := hpost.index_bool one bound1 one true
  have he1 : leaf=other := Option.some.inj (hidx1.symm.trans idx1)
  subst leaf
  exact ⟨out,ho,idx0,idx1,idx2,bit0,bit1,hcd,hcd1,hbool.mpr bit0,hbool1.mpr bit1⟩

/-- Endpoint rejection is a typed Option/decoded-read observation, not a Source
halt or rollback. Both outer and selected-child endpoints are exercised. -/
theorem endpoint_rejection (n copies : Nat) (hn : n+3<2^256) :
    ∃ out, checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 (repairs copies) []=some out ∧
      out.index root .dyn (uintOfNat (n+3))=none ∧
      ¬ DecodedArrayRead (tables n) (address root.id) BoolChildTy none (n+3) (.val (.cdRef rfl (address r.id))) ∧
      out.index r .dyn (uintOfNat (n+3))=none ∧ ¬ DecodedBoolRead (tables n) (address r.id) (n+3) false := by
  obtain ⟨bm,ini,out,hb,hu,hs,ho,hpost,hbval,huval,hother,hroot⟩ := repaired n copies hn
  have hlen : out.len root .dyn=n+3 := by
    rw [checkedMixedCaptures_all_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho root .dyn]
    simp only [Heap.len,MObj.elems_dyn]
    change (aliases n).length=n+3
    simp only [aliases,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
  have hend : out.len root .dyn ≤ (uintOfNat (n+3)).val.toNat := by
    rw [hlen,uintOfNat_val hn,Int.toNat_natCast]
    exact Nat.le_refl _
  have hob := hpost.index_bounds (uintOfNat (n+3)) hend (.val (.cdRef rfl (address r.id)))
  rw [uintOfNat_val hn,Int.toNat_natCast] at hob
  refine ⟨out,ho,hob.1,hob.2,?_,?_⟩
  · change (MObj.elems .dyn (out.get r))[(uintOfNat (n+3)).val.toNat]?=none
    rw [uintOfNat_val hn,Int.toNat_natCast,hbval]
    apply List.getElem?_eq_none_iff.mpr
    simp only [bold,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
  · apply decodedBoolRead_overrun (first_repr n hn).2
    simp only [MObj.elems_dyn]
    change (bold n).length ≤ n+3
    simp only [bold,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega

/-- Element32 selects the unaffected child from a nonempty runtime tail; this
is not a physical byte-word encoding or a public payload bound. -/
theorem boundary33 :
    ∃ out, checkedMixedCaptures input 7 input 9 (hp 33 (by decide)) r .dyn 0 1 1 q .dyn 0 1 1 (repairs 4) []=some out ∧
      RefChildRepr (tables 33) address out sv root ∧
      out.index root .dyn (uintOfNat 32)=some other ∧ out.index other .dyn one=some true ∧
      DecodedBoolRead (tables 33) (address other.id) 1 true := by
  obtain ⟨bm,ini,out,hb,hu,hs,ho,hpost,hbval,huval,hother,hroot⟩ := repaired 33 4 (by decide)
  have idx : out.index root .dyn (uintOfNat 32)=some other := by
    change (MObj.elems .dyn (out.get root))[(uintOfNat 32).val.toNat]?=some other
    rw [uintOfNat_val (by decide : 32<2^256),Int.toNat_natCast,
      checkedMixedCaptures_ref_root_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho root]
    simp only [MObj.elems_dyn]; rfl
  have bit : out.index other .dyn one=some true := by
    change (MObj.elems .dyn (out.get other))[1]?=some true
    rw [hother]; rfl
  have bnd : (uintOfNat 32).val.toNat < out.len root .dyn := by
    rw [uintOfNat_val (by decide : 32<2^256),Int.toNat_natCast,
      checkedMixedCaptures_all_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho root .dyn]
    simp only [Heap.len,MObj.elems_dyn]; decide
  obtain ⟨leaf,hl,hcd,hbool⟩ := hpost.index_bool (uintOfNat 32) bnd one true
  have he : leaf=other := Option.some.inj (hl.symm.trans idx)
  subst leaf
  exact ⟨out,ho,hpost,idx,bit,hbool.mpr bit⟩

/-- info: 'Solidity.Backend.MemoryOps.MixedNestedControls.initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms initial
/-- info: 'Solidity.Backend.MemoryOps.MixedNestedControls.repaired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms repaired
/-- info: 'Solidity.Backend.MemoryOps.MixedNestedControls.stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stages
/-- info: 'Solidity.Backend.MemoryOps.MixedNestedControls.skipped_and_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms skipped_and_disjoint
/-- info: 'Solidity.Backend.MemoryOps.MixedNestedControls.two_level_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms two_level_reads
/-- info: 'Solidity.Backend.MemoryOps.MixedNestedControls.endpoint_rejection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms endpoint_rejection
/-- info: 'Solidity.Backend.MemoryOps.MixedNestedControls.boundary33' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boundary33
end Solidity.Backend.MemoryOps.MixedNestedControls
