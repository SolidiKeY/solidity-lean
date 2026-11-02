import Solidity.Backend.MemoryOps.DisjointSnapshotSchedules

/-! DRAFT / UNVALIDATED C78 applications of the unchanged C77 source input.
These are actual intrinsic fixed-array/State/MPath clients. No Source type,
byte-memory, allocator, emitted-code or EVM correspondence is introduced.
The C77 dependency is itself unvalidated and must be checked first in the
concrete private closure; no supplied theorem is an axiom or trusted oracle.
-/
namespace Solidity.Backend.MemoryOps.FixedDisjointPathApplications

private abbrev B := BoolChildRef
private def P (n : Nat) : RefTy := .fixed (.ref B) (n+3)
private def H (n : Nat) : HTy := [B,B,P n,P n,B]
private def leaf0 (n : Nat) : HRef (H n) B := ⟨0,rfl⟩
private def leaf1 (n : Nat) : HRef (H n) B := ⟨1,rfl⟩
private def parent0 (n : Nat) : HRef (H n) (P n) := ⟨2,rfl⟩
private def parent1 (n : Nat) : HRef (H n) (P n) := ⟨3,rfl⟩
private def neighbor (n : Nat) : HRef (H n) B := ⟨4,rfl⟩
private def old0 (n : Nat) := [leaf0 n,leaf1 n,leaf1 n]++List.replicate n (leaf0 n)
private def old1 (n : Nat) := [leaf1 n,leaf0 n,leaf0 n]++List.replicate n (leaf1 n)
private def changed0 (n : Nat) := [leaf0 n,leaf0 n,leaf1 n]++List.replicate n (leaf0 n)
private def changed1 (n : Nat) := [leaf1 n,leaf1 n,leaf0 n]++List.replicate n (leaf1 n)
private def hp (n : Nat) : Heap (H n) :=
  (⟨[true,false],by change (2 : Nat)<2^256;decide⟩,⟨[false,true],by change (2 : Nat)<2^256;decide⟩,
   ⟨old0 n,by simp only [old0,List.length_append,List.length_cons,List.length_nil,List.length_replicate];omega⟩,
   ⟨old1 n,by simp only [old1,List.length_append,List.length_cons,List.length_nil,List.length_replicate];omega⟩,
   ⟨[true,false,true],by change (3 : Nat)<2^256;decide⟩,())
private def C : Contract := {vars := []}
private def Γ (n : Nat) : Ctx := [.mem (P n),.mem (P n),.val .uint,.val .uint]
private def root0 (n : Nat) : Idx (Γ n) (.mem (P n)) := .here
private def root1 (n : Nat) : Idx (Γ n) (.mem (P n)) := .there .here
private def index1 (n : Nat) : Idx (Γ n) (.val .uint) := .there (.there .here)
private def index0 (n : Nat) : Idx (Γ n) (.val .uint) := .there (.there (.there .here))
private def one : PrimTy.uint.Denote := ⟨1,by decide⟩
private def zero : PrimTy.uint.Denote := ⟨0,by decide⟩
private def state (n : Nat) : State C (Γ n) :=
  {storage := Storage.init C,H := H n,heap := hp n,
   env := (some (parent0 n),some (parent1 n),one,zero,())}
private def first : SnapshotArgs := (0,1,1)
private def selected0 (n : Nat) : MPath C (Γ n) (.ref B) :=
  .loc (.index .fixed (.var (root0 n) rfl) (.simple (.local (index1 n))))
private def selected1 (n : Nat) : MPath C (Γ n) (.ref B) :=
  .loc (.index .fixed (.var (root1 n) rfl) (.simple (.local (index1 n))))
private def nested0 (n : Nat) : MPath C (Γ n) (.prim .bool) :=
  .loc (.index .dyn (selected0 n) (.simple (.local (index0 n))))
private def nested1 (n : Nat) : MPath C (Γ n) (.prim .bool) :=
  .loc (.index .dyn (selected1 n) (.simple (.local (index0 n))))

private theorem fixed_len0 (n : Nat) : (hp n).len (parent0 n) .fixed=n+3 := by
  simpa only [Heap.len,MObj.elems_fixed] using ((hp n).get (parent0 n)).2
private theorem fixed_len1 (n : Nat) : (hp n).len (parent1 n) .fixed=n+3 := by
  simpa only [Heap.len,MObj.elems_fixed] using ((hp n).get (parent1 n)).2
private theorem valid_first (size : Nat) (hs : 2≤size) : CapturesValid size [first] := by
  intro x hx
  have he : x=first := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hx
  subst x
  change 0≤1 ∧ 1≤size ∧ 1+(1-0)≤size
  omega
private theorem capture_elems {K : HTy} {R : RefTy} {E : Ty}
    (before after : Heap K) (r : HRef K R) (a : ArrTy R E)
    (h : runCaptures before r a [first]=some after) :
    MObj.elems a (after.get r)=replaceSlice (MObj.elems a (before.get r)) 1 (sliceElems before r a 0 1) := by
  rw [runCaptures_singleton] at h
  obtain ⟨hs,hd,rfl⟩ := (checkedCaptureOverwrite_some_iff _ _ _ _ _ _ _ _ _).mp h
  dsimp only [captureOverwrite]
  rw [overwriteSlice_elems]
  rfl
private theorem selected0_run (n : Nat) (heap : Heap (H n)) (child : HRef (H n) B)
    (h : heap.index (parent0 n) .fixed one=some child) :
    (selected0 n).mvalT ((state n).withHeap heap)=.ok child := by
  change TRes.ofOpt (heap.index (parent0 n) .fixed one)=.ok child
  rw [h];rfl
private theorem selected1_run (n : Nat) (heap : Heap (H n)) (child : HRef (H n) B)
    (h : heap.index (parent1 n) .fixed one=some child) :
    (selected1 n).mvalT ((state n).withHeap heap)=.ok child := by
  change TRes.ofOpt (heap.index (parent1 n) .fixed one)=.ok child
  rw [h];rfl
private theorem nested0_run (n : Nat) (heap : Heap (H n)) (child : HRef (H n) B) (value : Bool)
    (hs : (selected0 n).mvalT ((state n).withHeap heap)=.ok child)
    (hv : heap.index child .dyn zero=some value) :
    (nested0 n).mvalT ((state n).withHeap heap)=.ok value := by
  rw [nested0,MPath.mvalT,MLoc.addrT,hs]
  change TRes.ofOpt (heap.index child .dyn zero)=.ok value
  rw [hv];rfl
private theorem nested1_run (n : Nat) (heap : Heap (H n)) (child : HRef (H n) B) (value : Bool)
    (hs : (selected1 n).mvalT ((state n).withHeap heap)=.ok child)
    (hv : heap.index child .dyn zero=some value) :
    (nested1 n).mvalT ((state n).withHeap heap)=.ok value := by
  rw [nested1,MPath.mvalT,MLoc.addrT,hs]
  change TRes.ofOpt (heap.index child .dyn zero)=.ok value
  rw [hv];rfl

/-- Actual fixed arrays, not a dynamic-type cast. All four reached schedules
are derived from INITIAL lengths. The two selected reference-valued MPaths
and two-level Boolean MPaths materially change; both orderings are explicit.
Top-level separation permits repeated/shared descendant identities. -/
theorem fixed_shared_paths (n : Nat) :
    ∃ mr mq left right : Heap (H n),
      runCaptures (hp n) (parent0 n) .fixed [first]=some mr ∧
      runCaptures (hp n) (parent1 n) .fixed [first]=some mq ∧
      runCaptures mr (parent1 n) .fixed [first]=some left ∧
      runCaptures mq (parent0 n) .fixed [first]=some right ∧
      [MObj.elems .fixed ((hp n).get (parent0 n)),MObj.elems .fixed ((hp n).get (parent1 n)),
       MObj.elems .fixed (mr.get (parent0 n)),MObj.elems .fixed (mr.get (parent1 n)),
       MObj.elems .fixed (mq.get (parent0 n)),MObj.elems .fixed (mq.get (parent1 n)),
       MObj.elems .fixed (left.get (parent0 n)),MObj.elems .fixed (left.get (parent1 n)),
       MObj.elems .fixed (right.get (parent0 n)),MObj.elems .fixed (right.get (parent1 n))]=
       [old0 n,old1 n,changed0 n,old1 n,old0 n,changed1 n,changed0 n,changed1 n,changed0 n,changed1 n] ∧
      (selected0 n).mvalT (state n)=.ok (leaf1 n) ∧
      (selected1 n).mvalT (state n)=.ok (leaf0 n) ∧
      (selected0 n).mvalT ((state n).withHeap left)=.ok (leaf0 n) ∧
      (selected0 n).mvalT ((state n).withHeap right)=.ok (leaf0 n) ∧
      (selected1 n).mvalT ((state n).withHeap left)=.ok (leaf1 n) ∧
      (selected1 n).mvalT ((state n).withHeap right)=.ok (leaf1 n) ∧
      (nested0 n).mvalT (state n)=.ok false ∧ (nested1 n).mvalT (state n)=.ok true ∧
      (nested0 n).mvalT ((state n).withHeap left)=.ok true ∧
      (nested0 n).mvalT ((state n).withHeap right)=.ok true ∧
      (nested1 n).mvalT ((state n).withHeap left)=.ok false ∧
      (nested1 n).mvalT ((state n).withHeap right)=.ok false ∧
      (selected0 n).mvalT ((state n).withHeap left)=(selected0 n).mvalT ((state n).withHeap right) ∧
      (nested1 n).mvalT ((state n).withHeap left)=(nested1 n).mvalT ((state n).withHeap right) ∧
      [MObj.elems .dyn (left.get (leaf0 n)),MObj.elems .dyn (left.get (leaf1 n)),
       MObj.elems .dyn (left.get (neighbor n)),MObj.elems .dyn (right.get (leaf0 n)),
       MObj.elems .dyn (right.get (leaf1 n)),MObj.elems .dyn (right.get (neighbor n))]=
       [[true,false],[false,true],[true,false,true],[true,false],[false,true],[true,false,true]] ∧
      ((state n).withHeap left).env=(state n).env ∧
      ((state n).withHeap right).storage=(state n).storage := by
  have hv0 : CapturesValid ((hp n).len (parent0 n) .fixed) [first] := by
    rw [fixed_len0];exact valid_first _ (by omega)
  have hv1 : CapturesValid ((hp n).len (parent1 n) .fixed) [first] := by
    rw [fixed_len1];exact valid_first _ (by omega)
  obtain ⟨mr,hr⟩ := (runCaptures_success_iff (hp n) (parent0 n) .fixed [first]).mpr hv0
  obtain ⟨mq,hq⟩ := (runCaptures_success_iff (hp n) (parent1 n) .fixed [first]).mpr hv1
  have hv1' : CapturesValid (mr.len (parent1 n) .fixed) [first] := by
    rw [runCaptures_all_len _ _ _ _ _ hr (parent1 n) .fixed];exact hv1
  have hv0' : CapturesValid (mq.len (parent0 n) .fixed) [first] := by
    rw [runCaptures_all_len _ _ _ _ _ hq (parent0 n) .fixed];exact hv0
  obtain ⟨left,hl⟩ := (runCaptures_success_iff mr (parent1 n) .fixed [first]).mpr hv1'
  obtain ⟨right,ht⟩ := (runCaptures_success_iff mq (parent0 n) .fixed [first]).mpr hv0'
  have hpath : (selected0 n).mvalT ((state n).withHeap left) =
      (selected0 n).mvalT ((state n).withHeap right) := runCaptures_disjoint_path (state n) (parent0 n) .fixed [first] (parent1 n) .fixed [first]
    (by change (2 : Nat)≠3;decide) mr mq left right hr hq hl ht (selected0 n)
  have hnested : (nested1 n).mvalT ((state n).withHeap left) =
      (nested1 n).mvalT ((state n).withHeap right) := runCaptures_disjoint_path (state n) (parent0 n) .fixed [first] (parent1 n) .fixed [first]
    (by change (2 : Nat)≠3;decide) mr mq left right hr hq hl ht (nested1 n)
  have heq : left=right := runCaptures_disjoint_outputs_eq (hp n) mr mq left right (parent0 n) .fixed [first]
    (parent1 n) .fixed [first] (by change (2 : Nat)≠3;decide) hr hq hl ht
  have hmr : MObj.elems .fixed (mr.get (parent0 n))=changed0 n := by
    rw [capture_elems _ _ _ _ hr]
    simp only [sliceElems,MObj.elems_fixed];rfl
  have hmq : MObj.elems .fixed (mq.get (parent1 n))=changed1 n := by
    rw [capture_elems _ _ _ _ hq]
    simp only [sliceElems,MObj.elems_fixed];rfl
  have hother0 : mr.get (parent1 n)=(hp n).get (parent1 n) := runCaptures_frame _ _ _ _ _ hr (parent1 n) (by change (2 : Nat)≠3;decide)
  have hother1 : mq.get (parent0 n)=(hp n).get (parent0 n) := runCaptures_frame _ _ _ _ _ hq (parent0 n) (by change (3 : Nat)≠2;decide)
  have hleft0 : left.get (parent0 n)=mr.get (parent0 n) := runCaptures_frame _ _ _ _ _ hl (parent0 n) (by change (3 : Nat)≠2;decide)
  have hright1 : right.get (parent1 n)=mq.get (parent1 n) := runCaptures_frame _ _ _ _ _ ht (parent1 n) (by change (2 : Nat)≠3;decide)
  have hl0 : MObj.elems .fixed (left.get (parent0 n))=changed0 n := by rw [hleft0,hmr]
  have hl1 : MObj.elems .fixed (left.get (parent1 n))=changed1 n := by rw [heq,hright1,hmq]
  have htable : [MObj.elems .fixed ((hp n).get (parent0 n)),MObj.elems .fixed ((hp n).get (parent1 n)),
      MObj.elems .fixed (mr.get (parent0 n)),MObj.elems .fixed (mr.get (parent1 n)),
      MObj.elems .fixed (mq.get (parent0 n)),MObj.elems .fixed (mq.get (parent1 n)),
      MObj.elems .fixed (left.get (parent0 n)),MObj.elems .fixed (left.get (parent1 n)),
      MObj.elems .fixed (right.get (parent0 n)),MObj.elems .fixed (right.get (parent1 n))]=
      [old0 n,old1 n,changed0 n,old1 n,old0 n,changed1 n,changed0 n,changed1 n,changed0 n,changed1 n] := by
    rw [hmr,hmq,hother0,hother1,←heq,hl0,hl1]
    simp only [MObj.elems_fixed];rfl
  have hleaf0 : left.get (leaf0 n)=(hp n).get (leaf0 n) :=
    (runCaptures_frame _ _ _ _ _ hl (leaf0 n) (by change (3 : Nat)≠0;decide)).trans (runCaptures_frame _ _ _ _ _ hr (leaf0 n) (by change (2 : Nat)≠0;decide))
  have hleaf1 : left.get (leaf1 n)=(hp n).get (leaf1 n) :=
    (runCaptures_frame _ _ _ _ _ hl (leaf1 n) (by change (3 : Nat)≠1;decide)).trans (runCaptures_frame _ _ _ _ _ hr (leaf1 n) (by change (2 : Nat)≠1;decide))
  have hneighbor : left.get (neighbor n)=(hp n).get (neighbor n) :=
    (runCaptures_frame _ _ _ _ _ hl (neighbor n) (by change (3 : Nat)≠4;decide)).trans (runCaptures_frame _ _ _ _ _ hr (neighbor n) (by change (2 : Nat)≠4;decide))
  have hsel0 : (selected0 n).mvalT ((state n).withHeap left)=.ok (leaf0 n) := by
    apply selected0_run
    change (MObj.elems .fixed (left.get (parent0 n)))[one.1.toNat]?=some (leaf0 n)
    rw [hl0];rfl
  have hsel1 : (selected1 n).mvalT ((state n).withHeap left)=.ok (leaf1 n) := by
    apply selected1_run
    change (MObj.elems .fixed (left.get (parent1 n)))[one.1.toNat]?=some (leaf1 n)
    rw [hl1];rfl
  have hinit0 : (selected0 n).mvalT (state n)=.ok (leaf1 n) := by
    exact selected0_run n (hp n) (leaf1 n) (by change (MObj.elems .fixed ((hp n).get (parent0 n)))[one.1.toNat]?=_;rw [MObj.elems_fixed];rfl)
  have hinit1 : (selected1 n).mvalT (state n)=.ok (leaf0 n) := by
    exact selected1_run n (hp n) (leaf0 n) (by change (MObj.elems .fixed ((hp n).get (parent1 n)))[one.1.toNat]?=_;rw [MObj.elems_fixed];rfl)
  have hread0 : left.index (leaf0 n) .dyn zero=some true := by
    change (MObj.elems .dyn (left.get (leaf0 n)))[zero.1.toNat]?=_
    rw [hleaf0,MObj.elems_dyn];rfl
  have hread1 : left.index (leaf1 n) .dyn zero=some false := by
    change (MObj.elems .dyn (left.get (leaf1 n)))[zero.1.toNat]?=_
    rw [hleaf1,MObj.elems_dyn];rfl
  have hbool0 : (nested0 n).mvalT ((state n).withHeap left)=.ok true := nested0_run n left (leaf0 n) true hsel0 hread0
  have hbool1 : (nested1 n).mvalT ((state n).withHeap left)=.ok false := nested1_run n left (leaf1 n) false hsel1 hread1
  have hboolInit0 : (nested0 n).mvalT (state n)=.ok false :=
    nested0_run n (hp n) (leaf1 n) false hinit0 (by change (MObj.elems .dyn ((hp n).get (leaf1 n)))[zero.1.toNat]?=_;rw [MObj.elems_dyn];rfl)
  have hboolInit1 : (nested1 n).mvalT (state n)=.ok true :=
    nested1_run n (hp n) (leaf0 n) true hinit1 (by change (MObj.elems .dyn ((hp n).get (leaf0 n)))[zero.1.toNat]?=_;rw [MObj.elems_dyn];rfl)
  have hleaves : [MObj.elems .dyn (left.get (leaf0 n)),MObj.elems .dyn (left.get (leaf1 n)),
      MObj.elems .dyn (left.get (neighbor n)),MObj.elems .dyn (right.get (leaf0 n)),
      MObj.elems .dyn (right.get (leaf1 n)),MObj.elems .dyn (right.get (neighbor n))]=
      [[true,false],[false,true],[true,false,true],[true,false],[false,true],[true,false,true]] := by
    rw [←heq,hleaf0,hleaf1,hneighbor];simp only [MObj.elems_dyn];rfl
  refine ⟨mr,mq,left,right,hr,hq,hl,ht,htable,hinit0,hinit1,hsel0,?_,hsel1,?_,
    hboolInit0,hboolInit1,hbool0,?_,hbool1,?_,hpath,hnested,hleaves,rfl,rfl⟩
  all_goals rw [←heq];assumption

/-- The selected reference and nested primitive observation are materially
different from the INITIAL path. These are real evaluated path outcomes. -/
theorem stale_initial_path_negative (n : Nat) :
    ∃ mr mq left right : Heap (H n),
      runCaptures (hp n) (parent0 n) .fixed [first]=some mr ∧
      runCaptures (hp n) (parent1 n) .fixed [first]=some mq ∧
      runCaptures mr (parent1 n) .fixed [first]=some left ∧
      runCaptures mq (parent0 n) .fixed [first]=some right ∧
      (selected0 n).mvalT ((state n).withHeap left)≠(selected0 n).mvalT (state n) ∧
      (nested0 n).mvalT ((state n).withHeap right)≠(nested0 n).mvalT (state n) := by
  obtain ⟨mr,mq,left,right,hr,hq,hl,ht,htable,hinit0,hinit1,hsel0,hsel0R,hsel1,hsel1R,
    hboolInit0,hboolInit1,hbool0,hbool0R,hbool1,hbool1R,hpath,hnested,hleaves,henv,hstorage⟩ := fixed_shared_paths n
  refine ⟨mr,mq,left,right,hr,hq,hl,ht,?_,?_⟩
  · rw [hsel0,hinit0]
    intro h
    have hid : (0 : Nat)=1 := congrArg HRef.id (Except.ok.inj h)
    exact (by decide : (0 : Nat)≠1) hid
  · rw [hbool0R,hboolInit0]
    intro h
    exact (by decide : (true : Bool)≠false) (Except.ok.inj h)

/-- Fixed runtime length33; the interior path remains a reference-valued
fixed-array path, not a logical-index-as-byte claim. -/
theorem length33 : ∃ mr mq left right : Heap (H 30),
    runCaptures (hp 30) (parent0 30) .fixed [first]=some mr ∧
    runCaptures (hp 30) (parent1 30) .fixed [first]=some mq ∧
    runCaptures mr (parent1 30) .fixed [first]=some left ∧
    runCaptures mq (parent0 30) .fixed [first]=some right ∧
    (hp 30).len (parent0 30) .fixed=33 ∧
    (selected0 30).mvalT ((state 30).withHeap left)=.ok (leaf0 30) := by
  obtain ⟨mr,mq,left,right,hr,hq,hl,ht,htable,hinit0,hinit1,hsel0,rest⟩ := fixed_shared_paths 30
  exact ⟨mr,mq,left,right,hr,hq,hl,ht,fixed_len0 30,hsel0⟩

/- Expected axiom pins are diagnostic requests only, not measured output. -/
/-- info: 'Solidity.Backend.MemoryOps.FixedDisjointPathApplications.fixed_shared_paths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_shared_paths
/-- info: 'Solidity.Backend.MemoryOps.FixedDisjointPathApplications.stale_initial_path_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_initial_path_negative
/-- info: 'Solidity.Backend.MemoryOps.FixedDisjointPathApplications.length33' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms length33
end Solidity.Backend.MemoryOps.FixedDisjointPathApplications

namespace Solidity.Backend.MemoryOps.EmptyDisjointPathApplications
private abbrev B := BoolChildRef
private abbrev F : RefTy := .fixed (.ref B) 0
private abbrev D : RefTy := .array (.ref B)
private abbrev H : HTy := [B,F,D]
private def leaf : HRef H B := ⟨0,rfl⟩
private def fixedEmpty : HRef H F := ⟨1,rfl⟩
private def dynamicEmpty : HRef H D := ⟨2,rfl⟩
private def hp : Heap H := (⟨[true,false],by decide⟩,⟨[],rfl⟩,⟨[],by decide⟩,())
private def zero : PrimTy.uint.Denote := ⟨0,by decide⟩
private def C : Contract := {vars := []}
private abbrev Γ : Ctx := [.mem F,.mem D]
private def state : State C Γ := {storage := Storage.init C,H := H,heap := hp,env := (some fixedEmpty,some dynamicEmpty,())}
private def fixedPath : MPath C Γ (.ref B) :=
  .loc (.index .fixed (.var (.here : Idx Γ (.mem F)) rfl) (.simple (.lit 0 (by decide))))
private def dynamicPath : MPath C Γ (.ref B) :=
  .loc (.index .dyn (.var (.there .here : Idx Γ (.mem D)) rfl) (.simple (.lit 0 (by decide))))
private theorem fixed_len : hp.len fixedEmpty .fixed=0 := by
  simp only [Heap.len,MObj.elems_fixed];rfl
private theorem dynamic_len : hp.len dynamicEmpty .dyn=0 := by
  simp only [Heap.len,MObj.elems_dyn];rfl

/-- Literal empty objects in BOTH existing intrinsic shapes. Empty interval
[0,0) at offset0 succeeds as whole-heap identity. The fixed0 value is NOT a
claim that zero-length Source fixed arrays are admitted or compiled. -/
theorem literal_empty_endpoints :
    MObj.elems .fixed (hp.get fixedEmpty)=[] ∧ MObj.elems .dyn (hp.get dynamicEmpty)=[] ∧
    runCaptures hp fixedEmpty .fixed [(0,0,0)]=some hp ∧
    runCaptures hp dynamicEmpty .dyn [(0,0,0)]=some hp ∧
    (runCaptures hp fixedEmpty .fixed [(0,0,0)]).bind
      (fun mid => runCaptures mid dynamicEmpty .dyn [(0,0,0)])=some hp ∧
    (runCaptures hp dynamicEmpty .dyn [(0,0,0)]).bind
      (fun mid => runCaptures mid fixedEmpty .fixed [(0,0,0)])=some hp ∧
    (runCaptures hp fixedEmpty .fixed [(0,0,0)]).bind
      (fun mid => runCaptures mid dynamicEmpty .dyn [(0,0,0)])=
    (runCaptures hp dynamicEmpty .dyn [(0,0,0)]).bind
      (fun mid => runCaptures mid fixedEmpty .fixed [(0,0,0)]) ∧
    MObj.elems .dyn (hp.get leaf)=[true,false] := by
  have hf : runCaptures hp fixedEmpty .fixed [(0,0,0)]=some hp := by
    rw [runCaptures_singleton]
    exact checkedCaptureOverwrite_empty _ _ _ _ _ _ _ (by rw [fixed_len];exact Nat.le_refl _) (by rw [fixed_len];exact Nat.le_refl _)
  have hd : runCaptures hp dynamicEmpty .dyn [(0,0,0)]=some hp := by
    rw [runCaptures_singleton]
    exact checkedCaptureOverwrite_empty _ _ _ _ _ _ _ (by rw [dynamic_len];exact Nat.le_refl _) (by rw [dynamic_len];exact Nat.le_refl _)
  have hc : (runCaptures hp fixedEmpty .fixed [(0,0,0)]).bind
      (fun mid => runCaptures mid dynamicEmpty .dyn [(0,0,0)]) =
      (runCaptures hp dynamicEmpty .dyn [(0,0,0)]).bind
      (fun mid => runCaptures mid fixedEmpty .fixed [(0,0,0)]) := runCaptures_disjoint_comm hp fixedEmpty .fixed [(0,0,0)] dynamicEmpty .dyn [(0,0,0)] (by decide)
  refine ⟨?_,?_,hf,hd,?_,?_,hc,?_⟩
  · rw [MObj.elems_fixed];rfl
  · rw [MObj.elems_dyn];rfl
  · rw [hf,Option.bind_some,hd]
  · rw [hd,Option.bind_some,hf]
  · rw [MObj.elems_dyn];rfl

/-- No element exists at endpoint0 of either literal empty object. Actual
checked nonempty captures reject; existing reference-valued MPaths revert.
None/revert gives no suffix heap or target panic-payload correspondence. -/
theorem literal_empty_bounds :
    checkedCaptureOverwrite hp fixedEmpty .fixed fixedEmpty .fixed 0 1 0=none ∧
    checkedCaptureOverwrite hp dynamicEmpty .dyn dynamicEmpty .dyn 0 1 0=none ∧
    runCaptures hp fixedEmpty .fixed [(0,1,0)]=none ∧
    runCaptures hp dynamicEmpty .dyn [(0,1,0)]=none ∧
    hp.index fixedEmpty .fixed zero=none ∧ hp.index dynamicEmpty .dyn zero=none ∧
    fixedPath.mvalT state=.error .revert ∧ dynamicPath.mvalT state=.error .revert := by
  have hf : checkedCaptureOverwrite hp fixedEmpty .fixed fixedEmpty .fixed 0 1 0=none := by
    apply (checkedCaptureOverwrite_none_iff _ _ _ _ _ _ _ _).mpr
    exact .inr (.inl (by rw [fixed_len];decide))
  have hd : checkedCaptureOverwrite hp dynamicEmpty .dyn dynamicEmpty .dyn 0 1 0=none := by
    apply (checkedCaptureOverwrite_none_iff _ _ _ _ _ _ _ _).mpr
    exact .inr (.inl (by rw [dynamic_len];decide))
  have hiF : hp.index fixedEmpty .fixed zero=none := by
    change (MObj.elems .fixed (hp.get fixedEmpty))[zero.1.toNat]?=none
    rw [MObj.elems_fixed];rfl
  have hiD : hp.index dynamicEmpty .dyn zero=none := by
    change (MObj.elems .dyn (hp.get dynamicEmpty))[zero.1.toNat]?=none
    rw [MObj.elems_dyn];rfl
  refine ⟨hf,hd,?_,?_,hiF,hiD,?_,?_⟩
  · rw [runCaptures_singleton];exact hf
  · rw [runCaptures_singleton];exact hd
  · change TRes.ofOpt (hp.index fixedEmpty .fixed zero)=.error .revert
    rw [hiF];rfl
  · change TRes.ofOpt (hp.index dynamicEmpty .dyn zero)=.error .revert
    rw [hiD];rfl

/- Expected standard-only pins, not observed validation. -/
/-- info: 'Solidity.Backend.MemoryOps.EmptyDisjointPathApplications.literal_empty_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms literal_empty_endpoints
/-- info: 'Solidity.Backend.MemoryOps.EmptyDisjointPathApplications.literal_empty_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms literal_empty_bounds
end Solidity.Backend.MemoryOps.EmptyDisjointPathApplications
