import Solidity.Backend.MemoryOps.CalldataSequence
import Solidity.Backend.MemoryOps.SnapshotProvenance

/-! Composition only: an existing immutable decoded uint256 transfer followed by the
existing finite reached-heap recapture schedule. No payload is an operation
input, and Option rejection states no Source halt or rollback. -/
namespace Solidity.Backend.MemoryOps

section
variable {D : Source.Layout} {H : HTy} {R : RefTy}
variable (c : Source.Calldata D) (off : Nat) (hp : Heap H)
variable (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)

def checkedUintCaptures (xs : List SnapshotArgs) : Option (Heap H) :=
  (checkedCalldataUints c off hp r a s t d).bind fun mid => runCaptures mid r a xs

theorem checkedUintCaptures_some (xs : List SnapshotArgs) (out : Heap H) :
    checkedUintCaptures c off hp r a s t d xs = some out ↔
      ∃ mid, checkedCalldataUints c off hp r a s t d = some mid ∧
        runCaptures mid r a xs = some out := Option.bind_eq_some_iff

/-- Bounds for all recaptures are checked against ORIGINAL length, derived
unchanged by the actual decoded write, not supplied as a preservation premise. -/
theorem checkedUintCaptures_success (xs : List SnapshotArgs) :
    (∃ out, checkedUintCaptures c off hp r a s t d xs = some out) ↔
      (∃ mid, checkedCalldataUints c off hp r a s t d = some mid) ∧
        CapturesValid (hp.len r a) xs := by
  constructor
  · rintro ⟨out,ho⟩
    obtain ⟨mid,hi,hs⟩ := (checkedUintCaptures_some c off hp r a s t d xs out).mp ho
    refine ⟨⟨mid,hi⟩,?_⟩
    have hv := (runCaptures_success_iff mid r a xs).mp ⟨out,hs⟩
    rw [uintTransfer_all_len c off hp r a s t d mid hi r a] at hv
    exact hv
  · rintro ⟨⟨mid,hi⟩,hv⟩
    have hl := uintTransfer_all_len c off hp r a s t d mid hi r a
    rw [← hl] at hv
    obtain ⟨out,hs⟩ := (runCaptures_success_iff mid r a xs).mpr hv
    exact ⟨out,(checkedUintCaptures_some c off hp r a s t d xs out).mpr ⟨mid,hi,hs⟩⟩

/-- Exact input-side success: actual extracted decoded values and ORIGINAL
bounds, without assuming a transfer/poststate exists as an input certificate. -/
theorem checkedUintCaptures_success_lookup (xs : List SnapshotArgs) :
    (∃ out, checkedUintCaptures c off hp r a s t d xs = some out) ↔
      ∃ bs, calldataUints c off = some bs ∧ SliceBounds bs.length s t ∧
        d+(t-s) ≤ hp.len r a ∧ CapturesValid (hp.len r a) xs := by
  rw [checkedUintCaptures_success]
  constructor
  · rintro ⟨⟨mid,hi⟩,hv⟩
    obtain ⟨bs,hb,hs,hd,he⟩ := uintTransfer_result_lookup c off hp r a s t d mid hi
    exact ⟨bs,hb,hs,by simpa only [hs.length] using hd,hv⟩
  · rintro ⟨bs,hb,hs,hd,hv⟩
    refine ⟨?_,hv⟩
    unfold checkedCalldataUints
    rw [hb]
    simp only [Bind.bind,Option.bind,dif_pos (show s ≤ t ∧ t ≤ bs.length from ⟨hs.ordered,hs.bounded⟩),dif_pos hd]
    exact ⟨_,rfl⟩

/-- Ordered rejection: either the actual decoded call fails, or it succeeds
and a real successful schedule prefix reaches its first failing call. -/
theorem checkedUintCaptures_none (xs : List SnapshotArgs) :
    checkedUintCaptures c off hp r a s t d xs = none ↔
      checkedCalldataUints c off hp r a s t d = none ∨
      ∃ mid pre x post reached,
        checkedCalldataUints c off hp r a s t d = some mid ∧
        xs = pre ++ x::post ∧ runCaptures mid r a pre = some reached ∧
        checkedCaptureOverwrite reached r a r a x.1 x.2.1 x.2.2 = none := by
  unfold checkedUintCaptures
  cases hi : checkedCalldataUints c off hp r a s t d with
  | none => simp only [Option.bind_none,true_or]
  | some mid =>
    simp only [Option.bind_some,Option.some_ne_none,false_or]
    constructor
    · intro h
      obtain ⟨pre,x,post,reached,he,hp,hf⟩ := (runCaptures_none_first mid r a xs).mp h
      exact ⟨mid,pre,x,post,reached,rfl,he,hp,hf⟩
    · rintro ⟨mid',pre,x,post,reached,he,hx,hp,hf⟩
      cases Option.some.inj he
      exact (runCaptures_none_first mid r a xs).mpr ⟨pre,x,post,reached,hx,hp,hf⟩

/-- The complete final read uses the REAL extracted immutable payload at the
backwards origin. Neither payload nor conversion correctness is a premise. -/
theorem checkedUintCaptures_read (xs : List SnapshotArgs) (out : Heap H)
    (ho : checkedUintCaptures c off hp r a s t d xs = some out) :
    ∃ bs, calldataUints c off = some bs ∧
      ∀ k, (MObj.elems a (out.get r))[k]? =
        (replaceSlice (MObj.elems a (hp.get r)) d ((bs.drop s).take (t-s)))[captureOrigin xs k]? := by
  obtain ⟨mid,hi,hs⟩ := (checkedUintCaptures_some c off hp r a s t d xs out).mp ho
  obtain ⟨bs,hb,hbounds,hd,he⟩ := uintTransfer_result_lookup c off hp r a s t d mid hi
  refine ⟨bs,hb,?_⟩
  intro k
  rw [runCaptures_read mid out r a xs hs k,he,overwriteSlice_elems]

/-- If backwards provenance lands inside the decoded destination, the final
value is an exact read from the immutable decoded Source array. -/
theorem checkedUintCaptures_source_read {n : Option Nat} {len : Nat}
    {hn : ∀ m, n = some m → m = len} {values : Fin len → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off len hn values) (xs : List SnapshotArgs) (out : Heap H)
    (ho : checkedUintCaptures c off hp r a s t d xs = some out) (k : Nat)
    (hk : d ≤ captureOrigin xs k ∧ captureOrigin xs k < d+(t-s)) :
    ∃ b, (MObj.elems a (out.get r))[k]? = some b ∧
      DecodedArrayRead c off (.int .u256) n (s+(captureOrigin xs k-d)) (.val (sourceUint b)) := by
  obtain ⟨mid,hi,hs⟩ := (checkedUintCaptures_some c off hp r a s t d xs out).mp ho
  obtain ⟨b,hb,hr⟩ := checkedCalldataUints_read hc hp r a s t d mid hi
    (captureOrigin xs k-d) (by omega)
  refine ⟨b,?_,hr⟩
  rw [runCaptures_read mid out r a xs hs k]
  have he : d+(captureOrigin xs k-d) = captureOrigin xs k := by omega
  rw [he] at hb
  exact hb

theorem checkedUintCaptures_all_len {Q : RefTy} {F : Ty}
    (xs : List SnapshotArgs) (out : Heap H)
    (ho : checkedUintCaptures c off hp r a s t d xs = some out)
    (q : HRef H Q) (b : ArrTy Q F) : out.len q b = hp.len q b := by
  obtain ⟨mid,hi,hs⟩ := (checkedUintCaptures_some c off hp r a s t d xs out).mp ho
  exact (runCaptures_all_len mid out r a xs hs q b).trans
    (uintTransfer_all_len c off hp r a s t d mid hi q b)

theorem checkedUintCaptures_frame {Q : RefTy} (xs : List SnapshotArgs) (out : Heap H)
    (ho : checkedUintCaptures c off hp r a s t d xs = some out)
    (q : HRef H Q) (hne : r.id ≠ q.id) : out.get q = hp.get q := by
  obtain ⟨mid,hi,hs⟩ := (checkedUintCaptures_some c off hp r a s t d xs out).mp ho
  obtain ⟨bs,hb,hbounds,hd,he⟩ := uintTransfer_result_lookup c off hp r a s t d mid hi
  exact (runCaptures_frame mid out r a xs hs q hne).trans
    (he ▸ overwriteSlice_frame hp r q a d _ hd hne)

/-- Exact restoration criterion computed from INITIAL values and the actual
immutable payload; individual stages need not preserve anything. -/
theorem checkedUintCaptures_restore (xs : List SnapshotArgs) (out : Heap H)
    (ho : checkedUintCaptures c off hp r a s t d xs = some out) :
    out = hp ↔ ∃ bs, calldataUints c off = some bs ∧
      ∀ k, (replaceSlice (MObj.elems a (hp.get r)) d ((bs.drop s).take (t-s)))[captureOrigin xs k]? =
        (MObj.elems a (hp.get r))[k]? := by
  obtain ⟨bs,hb,hr⟩ := checkedUintCaptures_read c off hp r a s t d xs out ho
  constructor
  · intro he
    refine ⟨bs,hb,?_⟩
    intro k
    exact (hr k).symm.trans (congrArg (fun h : Heap H => (MObj.elems a (h.get r))[k]?) he)
  · rintro ⟨bs',hb',ha⟩
    have he : bs = bs' := Option.some.inj (hb.symm.trans hb')
    subst bs'
    have ht : out.get r = hp.get r := by
      have hv : MObj.elems a (out.get r) = MObj.elems a (hp.get r) :=
        List.ext_getElem? (fun k => (hr k).trans (ha k))
      cases a <;> apply Subtype.ext <;> simpa only [MObj.elems_dyn,MObj.elems_fixed] using hv
    apply memoryOps_heap_ext
    intro Q q
    by_cases hid : r.id = q.id
    · obtain ⟨rfl,hq⟩ := HRef.heq_of_id r q hid
      cases hq
      exact ht
    · exact checkedUintCaptures_frame c off hp r a s t d xs out ho q hid
end


/-- info: 'Solidity.Backend.MemoryOps.checkedUintCaptures_success_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedUintCaptures_success_lookup
/-- info: 'Solidity.Backend.MemoryOps.checkedUintCaptures_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedUintCaptures_some
/-- info: 'Solidity.Backend.MemoryOps.checkedUintCaptures_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedUintCaptures_success
/-- info: 'Solidity.Backend.MemoryOps.checkedUintCaptures_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedUintCaptures_none
/-- info: 'Solidity.Backend.MemoryOps.checkedUintCaptures_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintCaptures_read
/-- info: 'Solidity.Backend.MemoryOps.checkedUintCaptures_source_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintCaptures_source_read
/-- info: 'Solidity.Backend.MemoryOps.checkedUintCaptures_all_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedUintCaptures_all_len
/-- info: 'Solidity.Backend.MemoryOps.checkedUintCaptures_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedUintCaptures_frame
/-- info: 'Solidity.Backend.MemoryOps.checkedUintCaptures_restore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintCaptures_restore
end Solidity.Backend.MemoryOps
