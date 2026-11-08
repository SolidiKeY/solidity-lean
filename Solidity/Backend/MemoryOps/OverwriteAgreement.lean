import Solidity.Backend.MemoryOps.CalldataSequenceChildren

/-! Pointwise agreement with INITIAL contents makes an actual overwrite an
identity. No desired final heap equality, output relation or conversion proof
is a premise. The generic law covers primitive and reference-valued arrays. -/
namespace Solidity.Backend.MemoryOps

/-- Initial interval agreement, under actual capacity, implies list identity. -/
theorem replaceSlice_eq_self_of_agrees {α : Type} (xs payload : List α) (d : Nat)
    (hd : d+payload.length ≤ xs.length)
    (ha : ∀ i, i < payload.length → payload[i]? = xs[d+i]?) :
    replaceSlice xs d payload = xs := by
  apply List.ext_getElem?
  intro k
  rw [replaceSlice_read_cases xs payload d k hd]
  by_cases hk : d ≤ k ∧ k < d+payload.length
  · rw [if_pos hk,ha (k-d) (by omega)]
    rw [Nat.add_sub_of_le hk.1]
  · rw [if_neg hk]

/-- Whole intrinsic heap identity follows from pointwise initial target reads. -/
theorem overwriteSlice_eq_self_of_agrees {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (d : Nat)
    (payload : List (MVal H E)) (hd : d+payload.length ≤ hp.len r a)
    (ha : ∀ i, i < payload.length → payload[i]? = (MObj.elems a (hp.get r))[d+i]?) :
    overwriteSlice hp r a d payload hd = hp := by
  apply memoryOps_heap_ext
  intro Q q
  by_cases he : r.id = q.id
  · obtain ⟨rfl,hq⟩ := HRef.heq_of_id r q he
    cases hq
    have hv : MObj.elems a ((overwriteSlice hp r a d payload hd).get r) = MObj.elems a (hp.get r) := by
      rw [overwriteSlice_elems,replaceSlice_eq_self_of_agrees _ payload d hd ha]
    cases a <;> apply Subtype.ext <;> simpa only [MObj.elems_dyn,MObj.elems_fixed] using hv
  · exact overwriteSlice_frame hp r q a d payload hd he

/-- A single initial interval disagreement refutes whole-heap identity. -/
theorem overwriteSlice_ne_of_disagrees {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (d : Nat)
    (payload : List (MVal H E)) (hd : d+payload.length ≤ hp.len r a)
    (i : Nat) (hi : i < payload.length)
    (ha : payload[i]? ≠ (MObj.elems a (hp.get r))[d+i]?) :
    overwriteSlice hp r a d payload hd ≠ hp := by
  intro he
  have hr := overwriteSlice_inside hp r a d i payload hd hi
  rw [he] at hr
  exact ha hr.symm

/-- A condition on the actual computed decoded payload and INITIAL target.
Missing/unsupported entries do not agree. This is not a state or evaluator. -/
def BoolTransferAgrees {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .bool)) (s t d : Nat) : Prop :=
  match calldataBools c off with
  | none => False
  | some bs => ∀ i, i < t-s → ((bs.drop s).take (t-s))[i]? = (MObj.elems a (hp.get r))[d+i]?

set_option backward.isDefEq.respectTransparency false in
/-- The existing operation supplies its real payload, bounds and capacity;
initial agreement then proves heap equality rather than assuming it. -/
theorem boolTransfer_eq_self_of_agrees {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .bool)) (s t d : Nat) (out : Heap H)
    (ho : checkedCalldataBools c off hp r a s t d = some out)
    (ha : BoolTransferAgrees c off hp r a s t d) : out = hp := by
  obtain ⟨bs,hb,hs,hd,rfl⟩ := boolTransfer_result_lookup c off hp r a s t d out ho
  unfold BoolTransferAgrees at ha
  rw [hb] at ha
  apply overwriteSlice_eq_self_of_agrees
  intro i hi
  rw [hs.length] at hi
  exact ha i hi

set_option backward.isDefEq.respectTransparency false in
/-- An existing child's own immutable decoded interval agrees with its initial
memory interval at the SAME offset, with no supplied conversion hypothesis. -/
theorem BoolChildRepr.self_agrees {D : Source.Layout} {H : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hr : BoolChildRepr c address hp sv r) (s t : Nat) :
    BoolTransferAgrees c (address r.id) hp r .dyn s t s := by
  unfold BoolTransferAgrees
  have hc : DecodedArrayAt (n := none) c (address r.id) (MObj.elems .dyn (hp.get r)).length
      (fun _ h => by cases h) (fun i => .val (.bool (MObj.elems .dyn (hp.get r))[i])) := hr.2
  rw [calldataBools_lookup hc]
  intro i hi
  rw [SliceBounds.read hi,List.getElem?_ofFn]
  by_cases hb : s+i < (MObj.elems .dyn (hp.get r)).length
  · rw [dif_pos hb,List.getElem?_eq_getElem hb]
    simp only [calldataBool,Fin.getElem_fin]
  · rw [dif_neg hb,List.getElem?_eq_none_iff.mpr (by omega)]

/-- info: 'Solidity.Backend.MemoryOps.replaceSlice_eq_self_of_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms replaceSlice_eq_self_of_agrees
/-- info: 'Solidity.Backend.MemoryOps.overwriteSlice_eq_self_of_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overwriteSlice_eq_self_of_agrees
/-- info: 'Solidity.Backend.MemoryOps.overwriteSlice_ne_of_disagrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overwriteSlice_ne_of_disagrees
/-- info: 'Solidity.Backend.MemoryOps.boolTransfer_eq_self_of_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boolTransfer_eq_self_of_agrees
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.self_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.self_agrees
set_option backward.isDefEq.respectTransparency false in
/-- Actual computed-source agreement is invariant under an initial preserving
prefix extension, with primitive weakening reduced to identity. -/
theorem BoolTransferAgrees.keeps_iff {D : Source.Layout} {H H' : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) {hp : Heap H} {hp' : Heap H'}
    (e : H <+: H') (hk : Heap.Keeps e hp hp') (r : HRef H R)
    (a : ArrTy R (.prim .bool)) (s t d : Nat) :
    BoolTransferAgrees c off hp' (r.wk e) a s t d ↔ BoolTransferAgrees c off hp r a s t d := by
  unfold BoolTransferAgrees
  rw [hk r,MObj.elems_wk,List.map_id'' (f := MVal.wk e (.prim .bool)) (fun _ => rfl)]
  cases calldataBools c off <;> rfl
/-- info: 'Solidity.Backend.MemoryOps.BoolTransferAgrees.keeps_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BoolTransferAgrees.keeps_iff
end Solidity.Backend.MemoryOps
