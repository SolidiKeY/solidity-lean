import Solidity.Backend.MemoryOps.DisjointSnapshotSchedules
import Solidity.Backend.MemoryOps.SnapshotScheduleControls

/-! DRAFT / UNVALIDATED. Runtime parent lengths and arbitrary valid schedules,
nonprimitive parents sharing BOTH old children, meaningful changes to BOTH
parents, primitive arrays, actual late rejection, and a same-parent negative.
These are intrinsic observations only, not physical bytes or Source execution.
-/
namespace Solidity.Backend.MemoryOps

private theorem schedule_capture_elems {H : HTy} {R : RefTy} {E : Ty}
    (hp out : Heap H) (r : HRef H R) (a : ArrTy R E) (x : SnapshotArgs)
    (h : checkedCaptureOverwrite hp r a r a x.1 x.2.1 x.2.2=some out) :
    MObj.elems a (out.get r)=replaceSlice (MObj.elems a (hp.get r)) x.2.2
      (sliceElems hp r a x.1 x.2.1) := by
  obtain ⟨hs,hd,rfl⟩ := (checkedCaptureOverwrite_some_iff _ _ _ _ _ _ _ _ _).mp h
  dsimp only [captureOverwrite]
  rw [overwriteSlice_elems]

namespace DisjointReferenceScheduleControls
open ScheduleControls
private abbrev B := BoolChildRef
private abbrev P : RefTy := .array (.ref B)
private abbrev H : HTy := [B,B,P,P,B]
private def leaf0 : HRef H B := ⟨0,rfl⟩
private def leaf1 : HRef H B := ⟨1,rfl⟩
private def parent0 : HRef H P := ⟨2,rfl⟩
private def parent1 : HRef H P := ⟨3,rfl⟩
private def neighbor : HRef H B := ⟨4,rfl⟩
private def old0 (n : Nat) := [leaf0,leaf1,leaf1]++List.replicate n leaf0
private def old1 (n : Nat) := [leaf1,leaf0,leaf0]++List.replicate n leaf1
private def hp (n : Nat) (hn : n+3<2^256) : Heap H :=
  (⟨[true,false],by decide⟩,⟨[false,true],by decide⟩,
   ⟨old0 n,by simp only [old0,List.length_append,List.length_cons,List.length_nil,List.length_replicate];omega⟩,
   ⟨old1 n,by simp only [old1,List.length_append,List.length_cons,List.length_nil,List.length_replicate];omega⟩,
   ⟨[true,false,true],by decide⟩,())
private theorem len0 (n : Nat) (hn : n+3<2^256) : (hp n hn).len parent0 .dyn=n+3 := by
  simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,parent0,old0,
    List.length_append,List.length_cons,List.length_nil,List.length_replicate];omega
private theorem len1 (n : Nat) (hn : n+3<2^256) : (hp n hn).len parent1 .dyn=n+3 := by
  simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,parent1,old1,
    List.length_append,List.length_cons,List.length_nil,List.length_replicate];omega
private theorem first_valid (size : Nat) (hs : 2≤size) : CapturesValid size [first] := by
  intro x hx
  have he : x=first := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hx
  subst x
  change 0≤1 ∧ 1≤size ∧ 1+(1-0)≤size
  omega

/-- An inhabited initial heap supplies arbitrary-length source schedules from
input bounds, not supplied runs or a desired final heap. Parents share both
children; local distinct parent identities still suffice for exact seriality.
All selected reads and all unchanged child/neighbor observations are included. -/
theorem runtime_schedules (n : Nat) (hn : n+3<2^256) (xs ys : List SnapshotArgs)
    (hx : CapturesValid (n+3) xs) (hy : CapturesValid (n+3) ys) :
    ∃ mr mq out : Heap H,
      runCaptures (hp n hn) parent0 .dyn xs=some mr ∧
      runCaptures (hp n hn) parent1 .dyn ys=some mq ∧
      runCaptures mr parent1 .dyn ys=some out ∧
      runCaptures mq parent0 .dyn xs=some out ∧
      MObj.elems .dyn (mr.get parent1)=old1 n ∧ MObj.elems .dyn (mq.get parent0)=old0 n ∧
      (∀ k,(MObj.elems .dyn (out.get parent0))[k]?=(old0 n)[captureOrigin xs k]?) ∧
      (∀ k,(MObj.elems .dyn (out.get parent1))[k]?=(old1 n)[captureOrigin ys k]?) ∧
      [MObj.elems .dyn ((hp n hn).get leaf0),MObj.elems .dyn ((hp n hn).get leaf1),
       MObj.elems .dyn (mr.get leaf0),MObj.elems .dyn (mr.get leaf1),
       MObj.elems .dyn (mq.get leaf0),MObj.elems .dyn (mq.get leaf1),
       MObj.elems .dyn (out.get leaf0),MObj.elems .dyn (out.get leaf1),MObj.elems .dyn (out.get neighbor)]=
        [[true,false],[false,true],[true,false],[false,true],[true,false],[false,true],[true,false],[false,true],[true,false,true]] := by
  obtain ⟨mr,mq,out,hr,hq,hl,ht,hread0,hread1,hframe⟩ :=
    runCaptures_disjoint_success (hp n hn) parent0 .dyn xs parent1 .dyn ys (by decide)
      (by rw [len0];exact hx) (by rw [len1];exact hy)
  have hleaves : [MObj.elems .dyn ((hp n hn).get leaf0),MObj.elems .dyn ((hp n hn).get leaf1),
      MObj.elems .dyn (mr.get leaf0),MObj.elems .dyn (mr.get leaf1),
      MObj.elems .dyn (mq.get leaf0),MObj.elems .dyn (mq.get leaf1),
      MObj.elems .dyn (out.get leaf0),MObj.elems .dyn (out.get leaf1),MObj.elems .dyn (out.get neighbor)]=
      [[true,false],[false,true],[true,false],[false,true],[true,false],[false,true],[true,false],[false,true],[true,false,true]] := by
    rw [runCaptures_frame _ _ _ _ _ hr leaf0 (by decide),runCaptures_frame _ _ _ _ _ hr leaf1 (by decide),
      runCaptures_frame _ _ _ _ _ hq leaf0 (by decide),runCaptures_frame _ _ _ _ _ hq leaf1 (by decide),
      hframe leaf0 (by decide) (by decide),hframe leaf1 (by decide) (by decide),hframe neighbor (by decide) (by decide)]
    simp only [MObj.elems_dyn];rfl
  refine ⟨mr,mq,out,hr,hq,hl,ht,?_,?_,?_,?_,hleaves⟩
  · rw [runCaptures_frame _ _ _ _ _ hr parent1 (by decide)]
    simp only [MObj.elems_dyn];rfl
  · rw [runCaptures_frame _ _ _ _ _ hq parent0 (by decide)]
    simp only [MObj.elems_dyn];rfl
  · intro k
    simpa only [MObj.elems_dyn] using hread0 k
  · intro k
    simpa only [MObj.elems_dyn] using hread1 k

/-- Complete ordered parent identities: BOTH writes materially change one
reference slot; shared children and neighbor contents do not change. -/
theorem both_material (n : Nat) (hn : n+3<2^256) :
    ∃ mr mq out : Heap H,
      runCaptures (hp n hn) parent0 .dyn [first]=some mr ∧
      runCaptures (hp n hn) parent1 .dyn [first]=some mq ∧
      runCaptures mr parent1 .dyn [first]=some out ∧
      runCaptures mq parent0 .dyn [first]=some out ∧
      [MObj.elems .dyn ((hp n hn).get parent0),MObj.elems .dyn ((hp n hn).get parent1),
       MObj.elems .dyn (mr.get parent0),MObj.elems .dyn (mr.get parent1),
       MObj.elems .dyn (mq.get parent0),MObj.elems .dyn (mq.get parent1),
       MObj.elems .dyn (out.get parent0),MObj.elems .dyn (out.get parent1)]=
       [old0 n,old1 n,[leaf0,leaf0,leaf1]++List.replicate n leaf0,old1 n,
        old0 n,[leaf1,leaf1,leaf0]++List.replicate n leaf1,
        [leaf0,leaf0,leaf1]++List.replicate n leaf0,[leaf1,leaf1,leaf0]++List.replicate n leaf1] ∧
      MObj.elems .dyn (out.get leaf0)=[true,false] ∧ MObj.elems .dyn (out.get leaf1)=[false,true] ∧
      MObj.elems .dyn (out.get neighbor)=[true,false,true] ∧
      (MObj.elems .dyn (out.get parent0)).map HRef.id=[0,0,1]++List.replicate n 0 ∧
      (MObj.elems .dyn (out.get parent1)).map HRef.id=[1,1,0]++List.replicate n 1 := by
  obtain ⟨mr,mq,out,hr,hq,hl,ht,hread0,hread1,hframe⟩ :=
    runCaptures_disjoint_success (hp n hn) parent0 .dyn [first] parent1 .dyn [first] (by decide)
      (by rw [len0];exact first_valid _ (by omega)) (by rw [len1];exact first_valid _ (by omega))
  have hstep0 : runCaptures (hp n hn) parent0 .dyn [first]=some mr := hr
  have hstep1 : runCaptures (hp n hn) parent1 .dyn [first]=some mq := hq
  rw [runCaptures_singleton] at hstep0 hstep1
  have hv0 : MObj.elems .dyn (mr.get parent0)=[leaf0,leaf0,leaf1]++List.replicate n leaf0 := by
    rw [schedule_capture_elems _ _ _ _ first hstep0]
    simp only [sliceElems,MObj.elems_dyn];rfl
  have hv1 : MObj.elems .dyn (mq.get parent1)=[leaf1,leaf1,leaf0]++List.replicate n leaf1 := by
    rw [schedule_capture_elems _ _ _ _ first hstep1]
    simp only [sliceElems,MObj.elems_dyn];rfl
  have hf0 : out.get parent0=mr.get parent0 := runCaptures_frame mr out parent1 .dyn [first] hl parent0 (by decide)
  have hf1 : out.get parent1=mq.get parent1 := runCaptures_frame mq out parent0 .dyn [first] ht parent1 (by decide)
  have hparent : [MObj.elems .dyn ((hp n hn).get parent0),MObj.elems .dyn ((hp n hn).get parent1),
      MObj.elems .dyn (mr.get parent0),MObj.elems .dyn (mr.get parent1),
      MObj.elems .dyn (mq.get parent0),MObj.elems .dyn (mq.get parent1),
      MObj.elems .dyn (out.get parent0),MObj.elems .dyn (out.get parent1)]=
      [old0 n,old1 n,[leaf0,leaf0,leaf1]++List.replicate n leaf0,old1 n,
       old0 n,[leaf1,leaf1,leaf0]++List.replicate n leaf1,
       [leaf0,leaf0,leaf1]++List.replicate n leaf0,[leaf1,leaf1,leaf0]++List.replicate n leaf1] := by
    rw [hf0,hf1,hv0,hv1,runCaptures_frame _ _ _ _ _ hr parent1 (by decide),
      runCaptures_frame _ _ _ _ _ hq parent0 (by decide)]
    simp only [MObj.elems_dyn];rfl
  refine ⟨mr,mq,out,hr,hq,hl,ht,hparent,?_,?_,?_,?_,?_⟩
  · rw [hframe leaf0 (by decide) (by decide)];simp only [MObj.elems_dyn];rfl
  · rw [hframe leaf1 (by decide) (by decide)];simp only [MObj.elems_dyn];rfl
  · rw [hframe neighbor (by decide) (by decide)];simp only [MObj.elems_dyn];rfl
  · rw [hf0,hv0,List.map_append,List.map_cons,List.map_cons,List.map_cons,List.map_nil,List.map_replicate];rfl
  · rw [hf1,hv1,List.map_append,List.map_cons,List.map_cons,List.map_cons,List.map_nil,List.map_replicate];rfl

/-- A valid nonempty first copy and independently valid other-object copy
precede the invalid reversed call in the two respective orderings. None is
only Option failure: the two failure prefixes are explicitly not equated. -/
theorem late_rejection (n : Nat) (hn : n+3<2^256) :
    ∃ mr mq : Heap H,
      runCaptures (hp n hn) parent0 .dyn [first]=some mr ∧
      runCaptures (hp n hn) parent1 .dyn [first]=some mq ∧
      checkedCaptureOverwrite mr parent0 .dyn parent0 .dyn 1 0 0=none ∧
      runCaptures (hp n hn) parent0 .dyn [first,(1,0,0)]=none ∧
      runCaptures mq parent0 .dyn [first,(1,0,0)]=none ∧
      (runCaptures (hp n hn) parent0 .dyn [first,(1,0,0)]).bind
        (fun mid => runCaptures mid parent1 .dyn [first])=
      (runCaptures (hp n hn) parent1 .dyn [first]).bind
        (fun mid => runCaptures mid parent0 .dyn [first,(1,0,0)]) := by
  obtain ⟨mr,hr⟩ := (runCaptures_success_iff (hp n hn) parent0 .dyn [first]).mpr
    (by rw [len0];exact first_valid _ (by omega))
  obtain ⟨mq,hq⟩ := (runCaptures_success_iff (hp n hn) parent1 .dyn [first]).mpr
    (by rw [len1];exact first_valid _ (by omega))
  have hb : checkedCaptureOverwrite mr parent0 .dyn parent0 .dyn 1 0 0=none :=
    (checkedCaptureOverwrite_none_iff _ _ _ _ _ _ _ _).mpr (.inl (by decide))
  have hf : runCaptures (hp n hn) parent0 .dyn [first,(1,0,0)]=none := by
    exact (runCaptures_none_first _ _ _ _).mpr ⟨[first],(1,0,0),[],mr,rfl,hr,hb⟩
  exact ⟨mr,mq,hr,hq,hb,hf,(runCaptures_none_after_run _ _ _ _ _ _ _ _ hq).mpr hf,
    runCaptures_disjoint_comm _ _ _ _ _ _ _ (by decide)⟩

/-- Empty exact-end captures on BOTH runtime parents are actual identities.
This is logical element indexing, not physical word/byte encoding. -/
theorem empty_endpoints (n : Nat) (hn : n+3<2^256) :
    runCaptures (hp n hn) parent0 .dyn [(n+3,n+3,n+3)]=some (hp n hn) ∧
    runCaptures (hp n hn) parent1 .dyn [(n+3,n+3,n+3)]=some (hp n hn) := by
  constructor
  · rw [runCaptures_singleton]
    exact checkedCaptureOverwrite_empty _ _ _ _ _ _ _ (by rw [len0];exact Nat.le_refl _) (by rw [len0];exact Nat.le_refl _)
  · rw [runCaptures_singleton]
    exact checkedCaptureOverwrite_empty _ _ _ _ _ _ _ (by rw [len1];exact Nat.le_refl _) (by rw [len1];exact Nat.le_refl _)

/-- Distinct parents may share descendants; aliased PARENTS do not generally
commute. One ordering restores the entire heap, the reverse materializes a
wrong old-child identity despite equal schedule lengths and valid bounds. -/
theorem same_parent_negative (n : Nat) (hn : n+3<2^256) :
    ∃ out : Heap H,
      runCaptures (hp n hn) parent0 .dyn [first,repair]=some (hp n hn) ∧
      runCaptures (hp n hn) parent0 .dyn [repair,first]=some out ∧
      MObj.elems .dyn (out.get parent0)=[leaf1,leaf1,leaf1]++List.replicate n leaf0 ∧
      out≠hp n hn := by
  have hv : CapturesValid ((hp n hn).len parent0 .dyn) cycle := by
    rw [len0];exact cycle_valid _ (by omega)
  obtain ⟨restored,hrest⟩ := (runCaptures_success_iff (hp n hn) parent0 .dyn cycle).mpr hv
  have hagree : ∀ k,(MObj.elems .dyn ((hp n hn).get parent0))[captureOrigin cycle k]?=
      (MObj.elems .dyn ((hp n hn).get parent0))[k]? := by
    intro k
    rw [cycle_origin]
    by_cases hk : k=1
    · subst k;rw [if_pos rfl];simp only [MObj.elems_dyn];rfl
    · rw [if_neg hk]
  have hrestore : restored=hp n hn := (runCaptures_heap_restore_iff _ _ _ _ _ hrest).mpr hagree
  have hforward : runCaptures (hp n hn) parent0 .dyn [first,repair]=some (hp n hn) :=
    hrest.trans (congrArg some hrestore)
  have hvalid : CapturesValid ((hp n hn).len parent0 .dyn) [repair,first] := by
    rw [len0]
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · change 1≤3 ∧ 3≤n+3 ∧ 0+(3-1)≤n+3;omega
    · change 0≤1 ∧ 1≤n+3 ∧ 1+(1-0)≤n+3;omega
  obtain ⟨out,ho⟩ := (runCaptures_success_iff (hp n hn) parent0 .dyn [repair,first]).mpr hvalid
  obtain ⟨mid,hfirst,hsecond⟩ := (runCaptures_cons_some _ _ _ _ repair [first]).mp ho
  rw [runCaptures_singleton] at hsecond
  have hmid : MObj.elems .dyn (mid.get parent0)=[leaf1,leaf1,leaf1]++List.replicate n leaf0 := by
    rw [schedule_capture_elems _ _ _ _ repair hfirst]
    simp only [sliceElems,MObj.elems_dyn];rfl
  have hout : MObj.elems .dyn (out.get parent0)=[leaf1,leaf1,leaf1]++List.replicate n leaf0 := by
    rw [schedule_capture_elems _ _ _ _ first hsecond]
    simp only [sliceElems,hmid];rfl
  refine ⟨out,hforward,ho,hout,?_⟩
  intro he
  have hwrong : ((MObj.elems .dyn (out.get parent0))[0]?).map HRef.id =
      ((MObj.elems .dyn ((hp n hn).get parent0))[0]?).map HRef.id := congrArg (fun heap : Heap H => ((MObj.elems .dyn (heap.get parent0))[0]?).map HRef.id) he
  rw [hout] at hwrong
  simp only [MObj.elems_dyn] at hwrong
  exact (by decide : (some 1 : Option Nat)≠some 0) hwrong

/-- Actual length33 witness, element32 retained in BOTH materially changed
parents, derived from complete singleton vectors rather than a byte claim. -/
theorem boundary33 :
    ∃ mr mq out : Heap H,
      runCaptures (hp 30 (by decide)) parent0 .dyn [first]=some mr ∧
      runCaptures (hp 30 (by decide)) parent1 .dyn [first]=some mq ∧
      runCaptures mr parent1 .dyn [first]=some out ∧ runCaptures mq parent0 .dyn [first]=some out ∧
      (MObj.elems .dyn (out.get parent0))[32]?=some leaf0 ∧
      (MObj.elems .dyn (out.get parent1))[32]?=some leaf1 := by
  obtain ⟨mr,mq,out,hr,hq,hl,ht,hvec,h0,h1,hn,hi0,hi1⟩ := both_material 30 (by decide)
  have hparent0 : MObj.elems .dyn (out.get parent0)=[leaf0,leaf0,leaf1]++List.replicate 30 leaf0 := by
    have h : some (MObj.elems .dyn (out.get parent0)) =
        some ([leaf0,leaf0,leaf1]++List.replicate 30 leaf0) := congrArg (fun lists => lists[6]?) hvec
    simpa only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] using h
  have hparent1 : MObj.elems .dyn (out.get parent1)=[leaf1,leaf1,leaf0]++List.replicate 30 leaf1 := by
    have h : some (MObj.elems .dyn (out.get parent1)) =
        some ([leaf1,leaf1,leaf0]++List.replicate 30 leaf1) := congrArg (fun lists => lists[7]?) hvec
    simpa only [List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] using h
  refine ⟨mr,mq,out,hr,hq,hl,ht,?_,?_⟩
  · rw [hparent0];rfl
  · rw [hparent1];rfl

/- Expected pins, NOT observed validation. -/
/-- info: 'Solidity.Backend.MemoryOps.DisjointReferenceScheduleControls.runtime_schedules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runtime_schedules
/-- info: 'Solidity.Backend.MemoryOps.DisjointReferenceScheduleControls.both_material' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms both_material
/-- info: 'Solidity.Backend.MemoryOps.DisjointReferenceScheduleControls.late_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms late_rejection
/-- info: 'Solidity.Backend.MemoryOps.DisjointReferenceScheduleControls.empty_endpoints' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_endpoints
/-- info: 'Solidity.Backend.MemoryOps.DisjointReferenceScheduleControls.same_parent_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms same_parent_negative
/-- info: 'Solidity.Backend.MemoryOps.DisjointReferenceScheduleControls.boundary33' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundary33
end DisjointReferenceScheduleControls

namespace DisjointPrimitiveScheduleControls
open ScheduleControls
private abbrev B := BoolChildRef
private abbrev H : HTy := [B,B,B]
private def r : HRef H B := ⟨0,rfl⟩
private def q : HRef H B := ⟨1,rfl⟩
private def neighbor : HRef H B := ⟨2,rfl⟩
private def hp : Heap H := (⟨[true,false,false],by decide⟩,⟨[false,true,true],by decide⟩,⟨[true,false],by decide⟩,())

/-- Primitive and reference-valued clients consume the SAME generic theorem.
This client records complete initial/reached/final Bool vectors for both orders. -/
theorem material_primitive :
    ∃ mr mq out : Heap H,
      runCaptures hp r .dyn [first]=some mr ∧ runCaptures hp q .dyn [first]=some mq ∧
      runCaptures mr q .dyn [first]=some out ∧ runCaptures mq r .dyn [first]=some out ∧
      [MObj.elems .dyn (hp.get r),MObj.elems .dyn (hp.get q),
       MObj.elems .dyn (mr.get r),MObj.elems .dyn (mr.get q),
       MObj.elems .dyn (mq.get r),MObj.elems .dyn (mq.get q),
       MObj.elems .dyn (out.get r),MObj.elems .dyn (out.get q),MObj.elems .dyn (out.get neighbor)]=
        [[true,false,false],[false,true,true],[true,true,false],[false,true,true],
         [true,false,false],[false,false,true],[true,true,false],[false,false,true],[true,false]] := by
  have hv : CapturesValid 3 [first] := by
    intro x hx
    have he : x=first := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hx
    subst x
    change 0≤1 ∧ 1≤3 ∧ 1+(1-0)≤3
    decide
  obtain ⟨mr,mq,out,hr,hq,hl,ht,hread0,hread1,hframe⟩ :=
    runCaptures_disjoint_success hp r .dyn [first] q .dyn [first] (by decide)
      (by simpa only [Heap.len,MObj.elems_dyn] using hv)
      (by simpa only [Heap.len,MObj.elems_dyn] using hv)
  have h0 : runCaptures hp r .dyn [first]=some mr := hr
  have h1 : runCaptures hp q .dyn [first]=some mq := hq
  rw [runCaptures_singleton] at h0 h1
  have hv0 : MObj.elems .dyn (mr.get r)=[true,true,false] := by
    rw [schedule_capture_elems _ _ _ _ first h0];simp only [sliceElems,MObj.elems_dyn];rfl
  have hv1 : MObj.elems .dyn (mq.get q)=[false,false,true] := by
    rw [schedule_capture_elems _ _ _ _ first h1];simp only [sliceElems,MObj.elems_dyn];rfl
  refine ⟨mr,mq,out,hr,hq,hl,ht,?_⟩
  rw [runCaptures_frame mr out q .dyn [first] hl r (by decide),
    runCaptures_frame mq out r .dyn [first] ht q (by decide),hv0,hv1,
    runCaptures_frame hp mr r .dyn [first] hr q (by decide),
    runCaptures_frame hp mq q .dyn [first] hq r (by decide),hframe neighbor (by decide) (by decide)]
  simp only [MObj.elems_dyn];rfl

/-- info: 'Solidity.Backend.MemoryOps.DisjointPrimitiveScheduleControls.material_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms material_primitive
end DisjointPrimitiveScheduleControls
end Solidity.Backend.MemoryOps
