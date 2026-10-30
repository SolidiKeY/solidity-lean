import Solidity.Backend.MemoryOps.CalldataSequence
import Solidity.Backend.MemoryOps.SnapshotProvenance

/-! Composition only: an existing immutable decoded transfer followed by the
existing finite reached-heap recapture schedule. No payload is an operation
input, and Option rejection states no Source halt or rollback. -/
namespace Solidity.Backend.MemoryOps

section
variable {D : Source.Layout} {H : HTy} {R : RefTy}
variable (c : Source.Calldata D) (off : Nat) (hp : Heap H)
variable (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)

def checkedBoolCaptures (xs : List SnapshotArgs) : Option (Heap H) :=
  (checkedCalldataBools c off hp r a s t d).bind fun mid => runCaptures mid r a xs

theorem checkedBoolCaptures_some (xs : List SnapshotArgs) (out : Heap H) :
    checkedBoolCaptures c off hp r a s t d xs = some out ↔
      ∃ mid, checkedCalldataBools c off hp r a s t d = some mid ∧
        runCaptures mid r a xs = some out := Option.bind_eq_some_iff

/-- Bounds for all recaptures are checked against ORIGINAL length, derived
unchanged by the actual decoded write, not supplied as a preservation premise. -/
theorem checkedBoolCaptures_success (xs : List SnapshotArgs) :
    (∃ out, checkedBoolCaptures c off hp r a s t d xs = some out) ↔
      (∃ mid, checkedCalldataBools c off hp r a s t d = some mid) ∧
        CapturesValid (hp.len r a) xs := by
  constructor
  · rintro ⟨out,ho⟩
    obtain ⟨mid,hi,hs⟩ := (checkedBoolCaptures_some c off hp r a s t d xs out).mp ho
    refine ⟨⟨mid,hi⟩,?_⟩
    have hv := (runCaptures_success_iff mid r a xs).mp ⟨out,hs⟩
    rw [boolTransfer_all_len c off hp r a s t d mid hi r a] at hv
    exact hv
  · rintro ⟨⟨mid,hi⟩,hv⟩
    have hl := boolTransfer_all_len c off hp r a s t d mid hi r a
    rw [← hl] at hv
    obtain ⟨out,hs⟩ := (runCaptures_success_iff mid r a xs).mpr hv
    exact ⟨out,(checkedBoolCaptures_some c off hp r a s t d xs out).mpr ⟨mid,hi,hs⟩⟩

/-- Ordered rejection: either the actual decoded call fails, or it succeeds
and a real successful schedule prefix reaches its first failing call. -/
theorem checkedBoolCaptures_none (xs : List SnapshotArgs) :
    checkedBoolCaptures c off hp r a s t d xs = none ↔
      checkedCalldataBools c off hp r a s t d = none ∨
      ∃ mid pre x post reached,
        checkedCalldataBools c off hp r a s t d = some mid ∧
        xs = pre ++ x::post ∧ runCaptures mid r a pre = some reached ∧
        checkedCaptureOverwrite reached r a r a x.1 x.2.1 x.2.2 = none := by
  unfold checkedBoolCaptures
  cases hi : checkedCalldataBools c off hp r a s t d with
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
theorem checkedBoolCaptures_read (xs : List SnapshotArgs) (out : Heap H)
    (ho : checkedBoolCaptures c off hp r a s t d xs = some out) :
    ∃ bs, calldataBools c off = some bs ∧
      ∀ k, (MObj.elems a (out.get r))[k]? =
        (replaceSlice (MObj.elems a (hp.get r)) d ((bs.drop s).take (t-s)))[captureOrigin xs k]? := by
  obtain ⟨mid,hi,hs⟩ := (checkedBoolCaptures_some c off hp r a s t d xs out).mp ho
  obtain ⟨bs,hb,hbounds,hd,he⟩ := boolTransfer_result_lookup c off hp r a s t d mid hi
  refine ⟨bs,hb,?_⟩
  intro k
  rw [runCaptures_read mid out r a xs hs k,he,overwriteSlice_elems]

/-- If backwards provenance lands inside the decoded destination, the final
value is an exact read from the immutable decoded Source array. -/
theorem checkedBoolCaptures_source_read {n : Option Nat} {len : Nat}
    {hn : ∀ m, n = some m → m = len} {values : Fin len → Source.Data D .bool}
    (hc : DecodedArrayAt c off len hn values) (xs : List SnapshotArgs) (out : Heap H)
    (ho : checkedBoolCaptures c off hp r a s t d xs = some out) (k : Nat)
    (hk : d ≤ captureOrigin xs k ∧ captureOrigin xs k < d+(t-s)) :
    ∃ b, (MObj.elems a (out.get r))[k]? = some b ∧
      DecodedArrayRead c off .bool n (s+(captureOrigin xs k-d)) (.val (.bool b)) := by
  obtain ⟨mid,hi,hs⟩ := (checkedBoolCaptures_some c off hp r a s t d xs out).mp ho
  obtain ⟨b,hb,hr⟩ := checkedCalldataBools_read hc hp r a s t d mid hi
    (captureOrigin xs k-d) (by omega)
  refine ⟨b,?_,hr⟩
  rw [runCaptures_read mid out r a xs hs k]
  have he : d+(captureOrigin xs k-d) = captureOrigin xs k := by omega
  rw [he] at hb
  exact hb

theorem checkedBoolCaptures_all_len {Q : RefTy} {F : Ty}
    (xs : List SnapshotArgs) (out : Heap H)
    (ho : checkedBoolCaptures c off hp r a s t d xs = some out)
    (q : HRef H Q) (b : ArrTy Q F) : out.len q b = hp.len q b := by
  obtain ⟨mid,hi,hs⟩ := (checkedBoolCaptures_some c off hp r a s t d xs out).mp ho
  exact (runCaptures_all_len mid out r a xs hs q b).trans
    (boolTransfer_all_len c off hp r a s t d mid hi q b)

theorem checkedBoolCaptures_frame {Q : RefTy} (xs : List SnapshotArgs) (out : Heap H)
    (ho : checkedBoolCaptures c off hp r a s t d xs = some out)
    (q : HRef H Q) (hne : r.id ≠ q.id) : out.get q = hp.get q := by
  obtain ⟨mid,hi,hs⟩ := (checkedBoolCaptures_some c off hp r a s t d xs out).mp ho
  obtain ⟨bs,hb,hbounds,hd,he⟩ := boolTransfer_result_lookup c off hp r a s t d mid hi
  exact (runCaptures_frame mid out r a xs hs q hne).trans
    (he ▸ overwriteSlice_frame hp r q a d _ hd hne)

/-- Exact restoration criterion computed from INITIAL values and the actual
immutable payload; individual stages need not preserve anything. -/
theorem checkedBoolCaptures_restore (xs : List SnapshotArgs) (out : Heap H)
    (ho : checkedBoolCaptures c off hp r a s t d xs = some out) :
    out = hp ↔ ∃ bs, calldataBools c off = some bs ∧
      ∀ k, (replaceSlice (MObj.elems a (hp.get r)) d ((bs.drop s).take (t-s)))[captureOrigin xs k]? =
        (MObj.elems a (hp.get r))[k]? := by
  obtain ⟨bs,hb,hr⟩ := checkedBoolCaptures_read c off hp r a s t d xs out ho
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
    · exact checkedBoolCaptures_frame c off hp r a s t d xs out ho q hid
end

/-- An old child relation may be broken by the decoded write and restored by
later recaptures. This iff assumes only its INITIAL immutable-table relation. -/
theorem BoolChildRepr.calldata_schedule_iff {D : Source.Layout} {H : HTy}
    {old c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hi : BoolChildRepr old address hp sv r) (off s t d : Nat)
    (xs : List SnapshotArgs) (out : Heap H)
    (ho : checkedBoolCaptures c off hp r .dyn s t d xs = some out) :
    BoolChildRepr old address out sv r ↔ ∃ bs, calldataBools c off = some bs ∧
      ∀ k, (replaceSlice (MObj.elems .dyn (hp.get r)) d ((bs.drop s).take (t-s)))[captureOrigin xs k]? =
        (MObj.elems .dyn (hp.get r))[k]? := by
  rw [hi.at_heap_iff out]
  obtain ⟨bs,hb,hr⟩ := checkedBoolCaptures_read c off hp r .dyn s t d xs out ho
  constructor
  · intro he
    exact ⟨bs,hb,fun k => (hr k).symm.trans (congrArg (fun ob => (MObj.elems .dyn ob)[k]?) he)⟩
  · rintro ⟨bs',hb',ha⟩
    have he : bs = bs' := Option.some.inj (hb.symm.trans hb')
    subst bs'
    have hv : MObj.elems .dyn (out.get r) = MObj.elems .dyn (hp.get r) :=
      List.ext_getElem? (fun k => (hr k).trans (ha k))
    apply Subtype.ext
    simpa only [MObj.elems_dyn] using hv

/-- info: 'Solidity.Backend.MemoryOps.checkedBoolCaptures_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolCaptures_some
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolCaptures_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolCaptures_success
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolCaptures_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolCaptures_none
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolCaptures_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolCaptures_read
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolCaptures_source_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolCaptures_source_read
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolCaptures_all_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolCaptures_all_len
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolCaptures_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolCaptures_frame
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolCaptures_restore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolCaptures_restore
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.calldata_schedule_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.calldata_schedule_iff
end Solidity.Backend.MemoryOps
