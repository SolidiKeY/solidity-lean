import Solidity.Backend.MemoryOps.CalldataArrayRead
import Solidity.Backend.MemoryOps.SnapshotExtension

/-! Actual immutable decoded Boolean array transfer. This consumes the existing
Source table, not ABI bytes. Only Boolean array objects are handled here;
other objects and failed bounds return None, without a Source halt claim. -/
namespace Solidity.Backend.MemoryOps

/-- Eliminate the existing intrinsically typed Boolean value. -/
def calldataBool {D : Source.Layout} (d : Source.Data D .bool) : Bool := by
  cases d with
  | val v =>
    cases v with
    | bool b => exact b
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ _ => cases h

/-- Extract finite decoded contents, retaining arbitrary runtime lengths. A
reference-valued Data.val is not mistaken for the decoded object it names. -/
def calldataBoolPayload {D : Source.Layout} {n : Option Nat}
    (d : Source.Data D (.array .calldata .bool n)) : Option (List Bool) := by
  cases d with
  | array _ _ xs => exact some (List.ofFn (fun i => calldataBool (xs i)))
  | val _ => exact none

/-- Lookup and eliminate an existing decoded object; no payload is an input. -/
def calldataBools {D : Source.Layout} (c : Source.Calldata D) (off : Nat) : Option (List Bool) :=
  match c.objects off with
  | some ⟨.array .calldata .bool _, d⟩ => calldataBoolPayload d
  | _ => none

set_option backward.isDefEq.respectTransparency false in
/-- Checked operation-side transfer into an existing typed array. -/
def checkedCalldataBools {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .bool)) (start stop offset : Nat) : Option (Heap H) := do
  let bs ← calldataBools c off
  if hs : start ≤ stop ∧ stop ≤ bs.length then
    if hd : offset + (stop - start) ≤ hp.len dst a then
      some (overwriteSlice hp dst a offset ((bs.drop start).take (stop - start))
        (by rw [(show SliceBounds bs.length start stop from ⟨hs.1, hs.2⟩).length]; exact hd))
    else none
  else none

theorem calldataBools_lookup {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D .bool} (hc : DecodedArrayAt c off len hn xs) :
    calldataBools c off = some (List.ofFn (fun i => calldataBool (xs i))) := by
  unfold calldataBools
  rw [hc]
  rfl

theorem calldataBool_exact {D : Source.Layout} (d : Source.Data D .bool) :
    d = .val (.bool (calldataBool d)) := by
  cases d with
  | val v =>
    cases v with
    | bool b => rfl
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ _ => cases h

set_option backward.isDefEq.respectTransparency false in
theorem checkedCalldataBools_some {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D .bool} (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .bool)) (start stop offset : Nat)
    (hs : SliceBounds len start stop) (hd : offset + (stop - start) ≤ hp.len dst a) :
    checkedCalldataBools c off hp dst a start stop offset =
      some (overwriteSlice hp dst a offset
        (((List.ofFn (fun i => calldataBool (xs i))).drop start).take (stop - start))
        (by rw [SliceBounds.length]; exact hd; simpa only [List.length_ofFn] using hs)) := by
  unfold checkedCalldataBools
  rw [calldataBools_lookup hc]
  simp only [Bind.bind, Option.bind, List.length_ofFn, dif_pos (show start ≤ stop ∧ stop ≤ len from ⟨hs.ordered, hs.bounded⟩), dif_pos hd]

/-- The extracted slice has the actual runtime interval length. -/
theorem calldataBools_slice_length {D : Source.Layout} {len : Nat}
    (xs : Fin len → Source.Data D .bool) {start stop : Nat}
    (hs : SliceBounds len start stop) :
    (((List.ofFn (fun i => calldataBool (xs i))).drop start).take (stop - start)).length = stop - start :=
  SliceBounds.length (by simpa only [List.length_ofFn] using hs)

/-- Exact guard failures for an existing decoded Boolean array. -/
theorem checkedCalldataBools_none_iff {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D .bool} (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .bool)) (start stop offset : Nat) :
    checkedCalldataBools c off hp dst a start stop offset = none ↔
      stop < start ∨ len < stop ∨ hp.len dst a < offset + (stop - start) := by
  unfold checkedCalldataBools
  rw [calldataBools_lookup hc]
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
theorem checkedCalldataBools_result {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D .bool} (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .bool)) (start stop offset : Nat) (out : Heap H)
    (h : checkedCalldataBools c off hp dst a start stop offset = some out) :
    ∃ (_hs : SliceBounds len start stop)
      (hd : offset + (((List.ofFn (fun i => calldataBool (xs i))).drop start).take (stop - start)).length ≤ hp.len dst a),
      out = overwriteSlice hp dst a offset
        (((List.ofFn (fun i => calldataBool (xs i))).drop start).take (stop - start)) hd := by
  unfold checkedCalldataBools at h
  rw [calldataBools_lookup hc] at h
  simp only [Bind.bind, Option.bind, List.length_ofFn] at h
  split at h
  next hs =>
    split at h
    next hd => exact ⟨⟨hs.1, hs.2⟩, _, (Option.some.inj h).symm⟩
    next hd => cases h
  next hs => cases h

set_option backward.isDefEq.respectTransparency false in
/-- Every written element agrees with an immutable source-table read. -/
theorem checkedCalldataBools_read {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D .bool} (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .bool)) (start stop offset : Nat) (out : Heap H)
    (h : checkedCalldataBools c off hp dst a start stop offset = some out)
    (i : Nat) (hi : i < stop - start) :
    ∃ b, (MObj.elems a (out.get dst))[offset + i]? = some b ∧
      DecodedArrayRead c off .bool n (start + i) (.val (.bool b)) := by
  obtain ⟨hs, hd, rfl⟩ := checkedCalldataBools_result hc hp dst a start stop offset out h
  refine ⟨calldataBool (xs ⟨start + i, hs.index hi⟩), ?_, ?_⟩
  · rw [overwriteSlice_inside]
    · rw [SliceBounds.read hi, List.getElem?_ofFn]
      simp only [dif_pos (hs.index hi)]
    · rw [calldataBools_slice_length xs hs]
      exact hi
  · exact (decodedArrayRead_iff hc _).mpr ⟨hs.index hi, calldataBool_exact _⟩

/-- Complete ordered destination contents, including its untouched exterior. -/
theorem checkedCalldataBools_elems {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D .bool} (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .bool)) (start stop offset : Nat) (out : Heap H)
    (h : checkedCalldataBools c off hp dst a start stop offset = some out) :
    MObj.elems a (out.get dst) = replaceSlice (MObj.elems a (hp.get dst)) offset
      (((List.ofFn (fun i => calldataBool (xs i))).drop start).take (stop - start)) := by
  obtain ⟨_, hd, rfl⟩ := checkedCalldataBools_result hc hp dst a start stop offset out h
  exact overwriteSlice_elems hp dst a offset _ hd

set_option backward.isDefEq.respectTransparency false in
theorem checkedCalldataBools_outside {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D .bool} (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .bool)) (start stop offset : Nat) (out : Heap H)
    (h : checkedCalldataBools c off hp dst a start stop offset = some out)
    (i : Nat) (hi : i < offset ∨ offset + (stop - start) ≤ i) :
    (MObj.elems a (out.get dst))[i]? = (MObj.elems a (hp.get dst))[i]? := by
  obtain ⟨hs, hd, rfl⟩ := checkedCalldataBools_result hc hp dst a start stop offset out h
  apply overwriteSlice_outside
  rw [calldataBools_slice_length xs hs]
  exact hi

/-- Other typed objects are framed, even when they contain aliases to dst. -/
theorem checkedCalldataBools_frame {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D .bool} (hc : DecodedArrayAt c off len hn xs)
    {H : HTy} {R Q : RefTy} (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .bool)) (start stop offset : Nat) (out : Heap H)
    (h : checkedCalldataBools c off hp dst a start stop offset = some out)
    (q : HRef H Q) (hne : dst.id ≠ q.id) : out.get q = hp.get q := by
  obtain ⟨_, hd, rfl⟩ := checkedCalldataBools_result hc hp dst a start stop offset out h
  exact overwriteSlice_frame hp dst q a offset _ hd hne

/-- info: 'Solidity.Backend.MemoryOps.calldataBools_lookup' depends on axioms: [propext] -/
#guard_msgs in #print axioms calldataBools_lookup
/-- info: 'Solidity.Backend.MemoryOps.calldataBool_exact' depends on axioms: [propext] -/
#guard_msgs in #print axioms calldataBool_exact
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataBools_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataBools_some
/-- info: 'Solidity.Backend.MemoryOps.calldataBools_slice_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms calldataBools_slice_length
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataBools_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataBools_none_iff
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataBools_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataBools_result
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataBools_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataBools_read
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataBools_elems' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataBools_elems
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataBools_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataBools_outside
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataBools_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataBools_frame
/-- Missing/unsupported decoded objects are adapter rejection, not profile exclusions. -/
theorem checkedCalldataBools_no_payload {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (dst : HRef H R)
    (a : ArrTy R (.prim .bool)) (start stop offset : Nat)
    (h : calldataBools c off = none) :
    checkedCalldataBools c off hp dst a start stop offset = none := by
  unfold checkedCalldataBools
  rw [h]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The computed primitive payload is independent of heap growth. Success and
all old typed observations transport through actual preserving extension. -/
theorem checkedCalldataBools_keeps {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {xs : Fin len → Source.Data D .bool} (hc : DecodedArrayAt c off len hn xs)
    {H H' : HTy} {R : RefTy} {hp : Heap H} {hp' : Heap H'}
    (e : H <+: H') (hk : Heap.Keeps e hp hp') (dst : HRef H R)
    (a : ArrTy R (.prim .bool)) (start stop offset : Nat) (out : Heap H)
    (h : checkedCalldataBools c off hp dst a start stop offset = some out) :
    ∃ out', checkedCalldataBools c off hp' (dst.wk e) a start stop offset = some out' ∧
      Heap.Keeps e out out' := by
  obtain ⟨hs, hd, rfl⟩ := checkedCalldataBools_result hc hp dst a start stop offset out h
  let payload := ((List.ofFn (fun i => calldataBool (xs i))).drop start).take (stop - start)
  have hl : payload.length = stop - start := calldataBools_slice_length xs hs
  have hd' : offset + (stop - start) ≤ hp'.len (dst.wk e) a := by
    rw [← hl]
    simpa only [Heap.len, hk dst, MObj.elems_wk, List.length_map] using hd
  refine ⟨_, checkedCalldataBools_some hc hp' (dst.wk e) a start stop offset hs hd', ?_⟩
  have hw : payload.map (MVal.wk e (.prim .bool)) = payload := List.map_id'' (fun _ => rfl) payload
  intro Q q
  have ho := overwriteSlice_keeps e hk dst a offset payload hd q
  simpa only [hw] using ho

/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataBools_no_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataBools_no_payload
/-- info: 'Solidity.Backend.MemoryOps.checkedCalldataBools_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedCalldataBools_keeps
end Solidity.Backend.MemoryOps
