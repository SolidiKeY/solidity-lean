import Solidity.Backend.MemoryOps.CalldataArrayRead
import Solidity.Backend.MemoryOps.SnapshotExtension
import Solidity.Backend.MemoryOps.DisjointOverwrite

/-! Actual immutable decoded uint256 array transfer. This consumes the existing
Source table, not ABI bytes. Only uint256 array objects are handled here;
other objects and failed bounds return None, without a Source halt claim. -/
namespace Solidity.Backend.MemoryOps

/-- Exact range bridge between the two published uint256 value types. -/
def sourceUint {D : Source.Layout} (v : PrimTy.uint.Denote) : Source.Val D (.int .u256) :=
  .int v.val (by
    have hv : 0 ≤ v.val ∧ v.val < ((2 ^ 256 : Nat) : Int) := of_decide_eq_true v.property
    have hb : ((2 ^ 256 - 1 : Nat) : Int) + 1 = ((2 ^ 256 : Nat) : Int) := by decide
    simp only [Source.IntTy.lo, Source.IntTy.hi, Source.IntTy.u256, Bool.false_eq_true, ↓reduceIte]
    constructor
    · exact hv.1
    · omega)

/-- Eliminate the existing typed uint256 value, deriving the intrinsic range. -/
def calldataUint {D : Source.Layout} (d : Source.Data D (.int .u256)) : PrimTy.uint.Denote := by
  cases d with
  | val v =>
    cases v with
    | int x h =>
      refine ⟨x, ?_⟩
      simp only [Source.IntTy.lo, Source.IntTy.hi, Source.IntTy.u256, Bool.false_eq_true, ↓reduceIte] at h
      have hb : ((2 ^ 256 - 1 : Nat) : Int) + 1 = ((2 ^ 256 : Nat) : Int) := by decide
      change decide (0 ≤ x ∧ x < ((2 ^ 256 : Nat) : Int)) = true
      exact decide_eq_true (by constructor; exact h.1; omega)
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ _ => cases h

/-- Extract finite decoded contents, retaining arbitrary runtime lengths. A
reference-valued Data.val is not mistaken for the decoded object it names. -/
def calldataUintPayload {D : Source.Layout} {n : Option Nat}
    (d : Source.Data D (.array .calldata (.int .u256) n)) : Option (List PrimTy.uint.Denote) := by
  cases d with
  | array _ _ xs => exact some (List.ofFn (fun i => calldataUint (xs i)))
  | val _ => exact none

/-- Lookup and eliminate an existing decoded object; no payload is an input. -/
def calldataUints {D : Source.Layout} (c : Source.Calldata D) (off : Nat) : Option (List PrimTy.uint.Denote) :=
  match c.objects off with
  | some ⟨.array .calldata (.int ⟨false, 256, _⟩) _, d⟩ => calldataUintPayload d
  | _ => none

set_option backward.isDefEq.respectTransparency false in
/-- Checked operation-side transfer into an existing typed array. -/
def checkedCalldataUints {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .uint)) (start stop offset : Nat) : Option (Heap H) := do
  let bs ← calldataUints c off
  if hs : start ≤ stop ∧ stop ≤ bs.length then
    if hd : offset + (stop - start) ≤ hp.len dst a then
      some (overwriteSlice hp dst a offset ((bs.drop start).take (stop - start))
        (by rw [(show SliceBounds bs.length start stop from ⟨hs.1, hs.2⟩).length]; exact hd))
    else none
  else none

theorem calldataUints_lookup {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D (.int .u256)} (hc : DecodedArrayAt c off len hn xs) :
    calldataUints c off = some (List.ofFn (fun i => calldataUint (xs i))) := by
  unfold calldataUints
  rw [hc]
  rfl

theorem calldataUint_exact {D : Source.Layout} (d : Source.Data D (.int .u256)) :
    d = .val (sourceUint (calldataUint d)) := by
  cases d with
  | val v =>
    cases v with
    | int _ _ => rfl
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ _ => cases h

/-- The exact uint range conversion retains the value, not a truncated word. -/
theorem calldataUint_sourceUint {D : Source.Layout} (v : PrimTy.uint.Denote) :
    calldataUint (Source.Data.val (sourceUint (D := D) v)) = v := by
  apply Subtype.ext
  rfl

/-- Reconstructing already typed Source values proves extraction directly. -/
theorem calldataUint_values {D : Source.Layout} (bs : List PrimTy.uint.Denote) :
    List.ofFn (fun i : Fin bs.length => calldataUint
      (Source.Data.val (sourceUint (D := D) bs[i]))) = bs := by
  apply List.ext_getElem
  · exact List.length_ofFn
  · intro i hi hj
    simp only [List.getElem_ofFn, calldataUint_sourceUint, Fin.getElem_fin]

set_option backward.isDefEq.respectTransparency false in
theorem checkedCalldataUints_some {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D (.int .u256)} (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .uint)) (start stop offset : Nat)
    (hs : SliceBounds len start stop) (hd : offset + (stop - start) ≤ hp.len dst a) :
    checkedCalldataUints c off hp dst a start stop offset =
      some (overwriteSlice hp dst a offset
        (((List.ofFn (fun i => calldataUint (xs i))).drop start).take (stop - start))
        (by rw [SliceBounds.length]; exact hd; simpa only [List.length_ofFn] using hs)) := by
  unfold checkedCalldataUints
  rw [calldataUints_lookup hc]
  simp only [Bind.bind, Option.bind, List.length_ofFn, dif_pos (show start ≤ stop ∧ stop ≤ len from ⟨hs.ordered, hs.bounded⟩), dif_pos hd]

/-- The extracted slice has the actual runtime interval length. -/
theorem calldataUints_slice_length {D : Source.Layout} {len : Nat}
    (xs : Fin len → Source.Data D (.int .u256)) {start stop : Nat}
    (hs : SliceBounds len start stop) :
    (((List.ofFn (fun i => calldataUint (xs i))).drop start).take (stop - start)).length = stop - start :=
  SliceBounds.length (by simpa only [List.length_ofFn] using hs)

/-- Exact guard failures for an existing decoded uint256 array. -/
theorem checkedCalldataUints_none_iff {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D (.int .u256)} (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .uint)) (start stop offset : Nat) :
    checkedCalldataUints c off hp dst a start stop offset = none ↔
      stop < start ∨ len < stop ∨ hp.len dst a < offset + (stop - start) := by
  unfold checkedCalldataUints
  rw [calldataUints_lookup hc]
  simp only [Bind.bind, Option.bind, List.length_ofFn]
  by_cases hs : start ≤ stop ∧ stop ≤ len
  · rw [dif_pos hs]
    by_cases hd : offset + (stop - start) ≤ hp.len dst a
    · rw [dif_pos hd]
      simp only [Option.some_ne_none, false_iff]
      omega
    · rw [dif_neg hd]
      simp only [true_iff]
      omega
  · rw [dif_neg hs]
    simp only [true_iff]
    omega

/-- A successful operation is the actual overwrite of the extracted payload. -/
theorem checkedCalldataUints_result {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D (.int .u256)} (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .uint)) (start stop offset : Nat) (out : Heap H)
    (h : checkedCalldataUints c off hp dst a start stop offset = some out) :
    ∃ (_hs : SliceBounds len start stop)
      (hd : offset + (((List.ofFn (fun i => calldataUint (xs i))).drop start).take (stop - start)).length ≤ hp.len dst a),
      out = overwriteSlice hp dst a offset
        (((List.ofFn (fun i => calldataUint (xs i))).drop start).take (stop - start)) hd := by
  unfold checkedCalldataUints at h
  rw [calldataUints_lookup hc] at h
  simp only [Bind.bind, Option.bind, List.length_ofFn] at h
  split at h
  next hs =>
    split at h
    next hd => exact ⟨⟨hs.1, hs.2⟩, _, (Option.some.inj h).symm⟩
    next hd => cases h
  next hs => cases h

set_option backward.isDefEq.respectTransparency false in
/-- Every written element agrees with an immutable source-table read. -/
theorem checkedCalldataUints_read {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D (.int .u256)} (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .uint)) (start stop offset : Nat) (out : Heap H)
    (h : checkedCalldataUints c off hp dst a start stop offset = some out)
    (i : Nat) (hi : i < stop - start) :
    ∃ b, (MObj.elems a (out.get dst))[offset + i]? = some b ∧
      DecodedArrayRead c off (.int .u256) n (start + i) (.val (sourceUint b)) := by
  obtain ⟨hs, hd, rfl⟩ := checkedCalldataUints_result hc hp dst a start stop offset out h
  refine ⟨calldataUint (xs ⟨start + i, hs.index hi⟩), ?_, ?_⟩
  · rw [overwriteSlice_inside]
    · rw [SliceBounds.read hi, List.getElem?_ofFn]
      simp only [dif_pos (hs.index hi)]
    · rw [calldataUints_slice_length xs hs]
      exact hi
  · exact (decodedArrayRead_iff hc _).mpr ⟨hs.index hi, calldataUint_exact _⟩

/-- Complete ordered destination contents, including its untouched exterior. -/
theorem checkedCalldataUints_elems {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D (.int .u256)} (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .uint)) (start stop offset : Nat) (out : Heap H)
    (h : checkedCalldataUints c off hp dst a start stop offset = some out) :
    MObj.elems a (out.get dst) = replaceSlice (MObj.elems a (hp.get dst)) offset
      (((List.ofFn (fun i => calldataUint (xs i))).drop start).take (stop - start)) := by
  obtain ⟨_, hd, rfl⟩ := checkedCalldataUints_result hc hp dst a start stop offset out h
  exact overwriteSlice_elems hp dst a offset _ hd

set_option backward.isDefEq.respectTransparency false in
theorem checkedCalldataUints_outside {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D (.int .u256)} (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .uint)) (start stop offset : Nat) (out : Heap H)
    (h : checkedCalldataUints c off hp dst a start stop offset = some out)
    (i : Nat) (hi : i < offset ∨ offset + (stop - start) ≤ i) :
    (MObj.elems a (out.get dst))[i]? = (MObj.elems a (hp.get dst))[i]? := by
  obtain ⟨hs, hd, rfl⟩ := checkedCalldataUints_result hc hp dst a start stop offset out h
  apply overwriteSlice_outside
  rw [calldataUints_slice_length xs hs]
  exact hi

/-- Other typed objects are framed, even when they contain aliases to dst. -/
theorem checkedCalldataUints_frame {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D (.int .u256)} (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R Q : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .uint)) (start stop offset : Nat) (out : Heap H)
    (h : checkedCalldataUints c off hp dst a start stop offset = some out)
    (q : HRef H Q) (hne : dst.id ≠ q.id) : out.get q = hp.get q := by
  obtain ⟨_, hd, rfl⟩ := checkedCalldataUints_result hc hp dst a start stop offset out h
  exact overwriteSlice_frame hp dst q a offset _ hd hne

/-- info: 'Solidity.Backend.MemoryOps.calldataUints_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms calldataUints_lookup
/-- info: 'Solidity.Backend.MemoryOps.calldataUint_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms calldataUint_exact
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataUints_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataUints_some
/-- info: 'Solidity.Backend.MemoryOps.calldataUints_slice_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms calldataUints_slice_length
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataUints_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataUints_none_iff
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataUints_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataUints_result
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataUints_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataUints_read
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataUints_elems' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataUints_elems
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataUints_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataUints_outside
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataUints_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataUints_frame
/-- Missing/unsupported decoded objects are adapter rejection, not profile exclusions. -/
theorem checkedCalldataUints_no_payload {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .uint)) (start stop offset : Nat)
    (h : calldataUints c off = none) :
    checkedCalldataUints c off hp dst a start stop offset = none := by
  unfold checkedCalldataUints
  rw [h]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The computed primitive payload is independent of heap growth. Success and
all old typed observations transport through actual preserving extension. -/
theorem checkedCalldataUints_keeps {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D (.int .u256)} (hc : DecodedArrayAt c off len hn xs)
    {H H' : HTy} {R : RefTy} {hp : Heap H} {hp' : Heap H'}
    (e : H <+: H') (hk : Heap.Keeps e hp hp') (dst : HRef H R)
    (a : ArrTy R (.prim .uint)) (start stop offset : Nat) (out : Heap H)
    (h : checkedCalldataUints c off hp dst a start stop offset = some out) :
    ∃ out', checkedCalldataUints c off hp' (dst.wk e) a start stop offset = some out' ∧
      Heap.Keeps e out out' := by
  obtain ⟨hs, hd, rfl⟩ := checkedCalldataUints_result hc hp dst a start stop offset out h
  let payload := ((List.ofFn (fun i => calldataUint (xs i))).drop start).take (stop - start)
  have hl : payload.length = stop - start := calldataUints_slice_length xs hs
  have hd' : offset + (stop - start) ≤ hp'.len (dst.wk e) a := by
    rw [← hl]
    simpa only [Heap.len, hk dst, MObj.elems_wk, List.length_map] using hd
  refine ⟨_, checkedCalldataUints_some hc hp' (dst.wk e) a start stop offset hs hd', ?_⟩
  have hw : payload.map (MVal.wk e (.prim .uint)) = payload := List.map_id'' (fun _ => rfl) payload
  intro Q q
  have ho := overwriteSlice_keeps e hk dst a offset payload hd q
  simpa only [hw] using ho

/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataUints_no_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataUints_no_payload
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataUints_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataUints_keeps
/-- info: 'Solidity.Backend.MemoryOps.calldataUint_sourceUint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms calldataUint_sourceUint
/-- info: 'Solidity.Backend.MemoryOps.calldataUint_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms calldataUint_values
set_option backward.isDefEq.respectTransparency false in
/-- Every valid empty source interval is actual heap identity at any fitting
runtime destination endpoint. No Source/target rollback semantics is inferred. -/
theorem checkedCalldataUints_empty {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D (.int .u256)} (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .uint)) (start offset : Nat)
    (hs : start ≤ len) (hd : offset ≤ hp.len dst a) :
    checkedCalldataUints c off hp dst a start start offset = some hp := by
  have h := checkedCalldataUints_some hc hp dst a start start offset ⟨Nat.le_refl _, hs⟩
    (by simpa only [Nat.sub_self, Nat.add_zero] using hd)
  simpa only [Nat.sub_self, List.take_zero, overwriteSlice_empty] using h

/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataUints_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataUints_empty
end Solidity.Backend.MemoryOps
