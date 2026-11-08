import Solidity.Backend.MemoryOps.CalldataSequence

/-! Actual decoded-transfer observations and local same-object interval
commutation. Payloads are extracted from immutable Source tables by the existing
operations. Overlap remains supported; interval separation is a theorem case. -/
namespace Solidity.Backend.MemoryOps

set_option backward.isDefEq.respectTransparency false in
/-- Both actual checked transfers produce the two existing overwrites; second
capacity follows from the first write's proved unchanged runtime length. -/
theorem checkedBoolSequence_same_checked {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D .bool} {ys : Fin L' → Source.Data D .bool}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R : RefTy} (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool))
    (s t d u v f : Nat) (hs : SliceBounds L s t) (hd : d+(t-s) ≤ hp.len r a)
    (hu : SliceBounds L' u v) (he : f+(v-u) ≤ hp.len r a) :
    checkedBoolSequence c off c' off' hp r a s t d r a u v f =
      some (overwriteIntervals hp r a d (((List.ofFn (fun i => calldataBool (xs i))).drop s).take (t-s)) (by rw [calldataBools_slice_length xs hs]; exact hd) f (((List.ofFn (fun i => calldataBool (ys i))).drop u).take (v-u)) (by rw [calldataBools_slice_length ys hu]; exact he)) := by
  unfold checkedBoolSequence
  rw [checkedCalldataBools_some hc hp r a s t d hs hd]
  simp only [Option.bind_some]
  exact checkedCalldataBools_some hc' _ r a u v f hu (by rw [overwriteSlice_len]; exact he)

/-- The complete ordered destination list derives from both reached operations,
not an assumed final relation or a caller-supplied payload. -/
theorem checkedBoolSequence_same_elems {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D .bool} {ys : Fin L' → Source.Data D .bool}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R : RefTy} (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool))
    (s t d u v f : Nat) (out : Heap H)
    (ho : checkedBoolSequence c off c' off' hp r a s t d r a u v f = some out) :
    MObj.elems a (out.get r) =
      replaceSlice (replaceSlice (MObj.elems a (hp.get r)) d (((List.ofFn (fun i => calldataBool (xs i))).drop s).take (t-s))) f (((List.ofFn (fun i => calldataBool (ys i))).drop u).take (v-u)) := by
  obtain ⟨mid, hfirst, hsecond⟩ := (checkedBoolSequence_some_iff c off c' off' hp r a s t d r a u v f out).mp ho
  rw [checkedCalldataBools_elems hc' mid r a u v f out hsecond,
    checkedCalldataBools_elems hc hp r a s t d mid hfirst]

/-- Every second-written cell has its actual immutable second-source read,
including cells that the first operation also wrote. -/
theorem checkedBoolSequence_second_read {D : Source.Layout} {n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L' : Nat}
    {hn' : ∀ m, n' = some m → m = L'}
    {ys : Fin L' → Source.Data D .bool}
    (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q : RefTy} (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool))
    (s t d : Nat) (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat)
    (out : Heap H) (ho : checkedBoolSequence c off c' off' hp r a s t d q b u v f = some out)
    (i : Nat) (hi : i < v-u) :
    ∃ z, (MObj.elems b (out.get q))[f+i]? = some z ∧
      DecodedArrayRead c' off' .bool n' (u+i) (.val (.bool z)) := by
  obtain ⟨mid, _, hsecond⟩ := (checkedBoolSequence_some_iff c off c' off' hp r a s t d q b u v f out).mp ho
  exact checkedCalldataBools_read hc' mid q b u v f out hsecond i hi

/-- First-source cells outside the second destination retain their actual
first-source observations, even for overlapping writes elsewhere. -/
theorem checkedBoolSequence_first_exterior {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D .bool} {ys : Fin L' → Source.Data D .bool}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R : RefTy} (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool))
    (s t d u v f : Nat) (out : Heap H)
    (ho : checkedBoolSequence c off c' off' hp r a s t d r a u v f = some out)
    (i : Nat) (hi : i < t-s) (hx : d+i < f ∨ f+(v-u) ≤ d+i) :
    ∃ z, (MObj.elems a (out.get r))[d+i]? = some z ∧
      DecodedArrayRead c off .bool n (s+i) (.val (.bool z)) := by
  obtain ⟨mid, hfirst, hsecond⟩ := (checkedBoolSequence_some_iff c off c' off' hp r a s t d r a u v f out).mp ho
  obtain ⟨z, hm, hz⟩ := checkedCalldataBools_read hc hp r a s t d mid hfirst i hi
  exact ⟨z, (checkedCalldataBools_outside hc' mid r a u v f out hsecond (d+i) hx).trans hm, hz⟩

set_option backward.isDefEq.respectTransparency false in
/-- Disjoint immutable-source transfers commute as actual heaps. No
cross-source noninterference premise is needed for immutable decoded tables. -/
theorem checkedBoolSequence_same_comm {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D .bool} {ys : Fin L' → Source.Data D .bool}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R : RefTy} (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool))
    (s t d u v f : Nat) (hs : SliceBounds L s t) (hd : d+(t-s) ≤ hp.len r a)
    (hu : SliceBounds L' u v) (he : f+(v-u) ≤ hp.len r a)
    (ha : IntervalsApart d (t-s) f (v-u)) :
    checkedBoolSequence c off c' off' hp r a s t d r a u v f =
      checkedBoolSequence c' off' c off hp r a u v f r a s t d := by
  rw [checkedBoolSequence_same_checked hc hc' hp r a s t d u v f hs hd hu he,
    checkedBoolSequence_same_checked hc' hc hp r a u v f s t d hu he hs hd]
  congr 1
  apply overwriteIntervals_comm
  simpa only [calldataBools_slice_length xs hs, calldataBools_slice_length ys hu] using ha

/-- Other typed objects are unchanged by both transfers, regardless of overlap. -/
theorem checkedBoolSequence_frame {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D .bool} {ys : Fin L' → Source.Data D .bool}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q T : RefTy} (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool))
    (s t d : Nat) (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat)
    (out : Heap H) (ho : checkedBoolSequence c off c' off' hp r a s t d q b u v f = some out)
    (k : HRef H T) (hr : r.id ≠ k.id) (hq : q.id ≠ k.id) : out.get k = hp.get k := by
  obtain ⟨mid, hfirst, hsecond⟩ := (checkedBoolSequence_some_iff c off c' off' hp r a s t d q b u v f out).mp ho
  exact (checkedCalldataBools_frame hc' mid q b u v f out hsecond k hq).trans
    (checkedCalldataBools_frame hc hp r a s t d mid hfirst k hr)

/-- Successful composition transports both actual intermediate heaps through
initial preserving growth, deriving the second Keeps from the first operation. -/
theorem checkedBoolSequence_keeps {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D .bool} {ys : Fin L' → Source.Data D .bool}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H H' : HTy} {R Q : RefTy} {hp : Heap H} {hp' : Heap H'}
    (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat)
    (out : Heap H) (ho : checkedBoolSequence c off c' off' hp r a s t d q b u v f = some out) :
    ∃ out', checkedBoolSequence c off c' off' hp' (r.wk e) a s t d (q.wk e) b u v f = some out' ∧
      Heap.Keeps e out out' := by
  obtain ⟨mid, hfirst, hsecond⟩ := (checkedBoolSequence_some_iff c off c' off' hp r a s t d q b u v f out).mp ho
  obtain ⟨mid', hf, hk1⟩ := checkedCalldataBools_keeps hc e hk r a s t d mid hfirst
  obtain ⟨out', hs, hk2⟩ := checkedCalldataBools_keeps hc' e hk1 q b u v f out hsecond
  exact ⟨out', (checkedBoolSequence_some_iff c off c' off' hp' (r.wk e) a s t d (q.wk e) b u v f out').mpr ⟨mid', hf, hs⟩, hk2⟩
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolSequence_same_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolSequence_same_checked
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolSequence_same_elems' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolSequence_same_elems
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolSequence_second_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolSequence_second_read
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolSequence_first_exterior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms checkedBoolSequence_first_exterior
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolSequence_same_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolSequence_same_comm
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolSequence_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolSequence_frame
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolSequence_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolSequence_keeps

set_option backward.isDefEq.respectTransparency false in
/-- Both actual checked transfers produce the two existing overwrites; second
capacity follows from the first write's proved unchanged runtime length. -/
theorem checkedUintSequence_same_checked {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D (.int .u256)} {ys : Fin L' → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R : RefTy} (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .uint))
    (s t d u v f : Nat) (hs : SliceBounds L s t) (hd : d+(t-s) ≤ hp.len r a)
    (hu : SliceBounds L' u v) (he : f+(v-u) ≤ hp.len r a) :
    checkedUintSequence c off c' off' hp r a s t d r a u v f =
      some (overwriteIntervals hp r a d (((List.ofFn (fun i => calldataUint (xs i))).drop s).take (t-s)) (by rw [calldataUints_slice_length xs hs]; exact hd) f (((List.ofFn (fun i => calldataUint (ys i))).drop u).take (v-u)) (by rw [calldataUints_slice_length ys hu]; exact he)) := by
  unfold checkedUintSequence
  rw [checkedCalldataUints_some hc hp r a s t d hs hd]
  simp only [Option.bind_some]
  exact checkedCalldataUints_some hc' _ r a u v f hu (by rw [overwriteSlice_len]; exact he)

/-- The complete ordered destination list derives from both reached operations,
not an assumed final relation or a caller-supplied payload. -/
theorem checkedUintSequence_same_elems {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D (.int .u256)} {ys : Fin L' → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R : RefTy} (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .uint))
    (s t d u v f : Nat) (out : Heap H)
    (ho : checkedUintSequence c off c' off' hp r a s t d r a u v f = some out) :
    MObj.elems a (out.get r) =
      replaceSlice (replaceSlice (MObj.elems a (hp.get r)) d (((List.ofFn (fun i => calldataUint (xs i))).drop s).take (t-s))) f (((List.ofFn (fun i => calldataUint (ys i))).drop u).take (v-u)) := by
  obtain ⟨mid, hfirst, hsecond⟩ := (checkedUintSequence_some_iff c off c' off' hp r a s t d r a u v f out).mp ho
  rw [checkedCalldataUints_elems hc' mid r a u v f out hsecond,
    checkedCalldataUints_elems hc hp r a s t d mid hfirst]

/-- Every second-written cell has its actual immutable second-source read,
including cells that the first operation also wrote. -/
theorem checkedUintSequence_second_read {D : Source.Layout} {n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L' : Nat}
    {hn' : ∀ m, n' = some m → m = L'}
    {ys : Fin L' → Source.Data D (.int .u256)}
    (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q : RefTy} (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .uint))
    (s t d : Nat) (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (out : Heap H) (ho : checkedUintSequence c off c' off' hp r a s t d q b u v f = some out)
    (i : Nat) (hi : i < v-u) :
    ∃ z, (MObj.elems b (out.get q))[f+i]? = some z ∧
      DecodedArrayRead c' off' (.int .u256) n' (u+i) (.val (sourceUint z)) := by
  obtain ⟨mid, _, hsecond⟩ := (checkedUintSequence_some_iff c off c' off' hp r a s t d q b u v f out).mp ho
  exact checkedCalldataUints_read hc' mid q b u v f out hsecond i hi

/-- First-source cells outside the second destination retain their actual
first-source observations, even for overlapping writes elsewhere. -/
theorem checkedUintSequence_first_exterior {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D (.int .u256)} {ys : Fin L' → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R : RefTy} (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .uint))
    (s t d u v f : Nat) (out : Heap H)
    (ho : checkedUintSequence c off c' off' hp r a s t d r a u v f = some out)
    (i : Nat) (hi : i < t-s) (hx : d+i < f ∨ f+(v-u) ≤ d+i) :
    ∃ z, (MObj.elems a (out.get r))[d+i]? = some z ∧
      DecodedArrayRead c off (.int .u256) n (s+i) (.val (sourceUint z)) := by
  obtain ⟨mid, hfirst, hsecond⟩ := (checkedUintSequence_some_iff c off c' off' hp r a s t d r a u v f out).mp ho
  obtain ⟨z, hm, hz⟩ := checkedCalldataUints_read hc hp r a s t d mid hfirst i hi
  exact ⟨z, (checkedCalldataUints_outside hc' mid r a u v f out hsecond (d+i) hx).trans hm, hz⟩

set_option backward.isDefEq.respectTransparency false in
/-- Disjoint immutable-source transfers commute as actual heaps. No
cross-source noninterference premise is needed for immutable decoded tables. -/
theorem checkedUintSequence_same_comm {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D (.int .u256)} {ys : Fin L' → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R : RefTy} (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .uint))
    (s t d u v f : Nat) (hs : SliceBounds L s t) (hd : d+(t-s) ≤ hp.len r a)
    (hu : SliceBounds L' u v) (he : f+(v-u) ≤ hp.len r a)
    (ha : IntervalsApart d (t-s) f (v-u)) :
    checkedUintSequence c off c' off' hp r a s t d r a u v f =
      checkedUintSequence c' off' c off hp r a u v f r a s t d := by
  rw [checkedUintSequence_same_checked hc hc' hp r a s t d u v f hs hd hu he,
    checkedUintSequence_same_checked hc' hc hp r a u v f s t d hu he hs hd]
  congr 1
  apply overwriteIntervals_comm
  simpa only [calldataUints_slice_length xs hs, calldataUints_slice_length ys hu] using ha

/-- Other typed objects are unchanged by both transfers, regardless of overlap. -/
theorem checkedUintSequence_frame {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D (.int .u256)} {ys : Fin L' → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q T : RefTy} (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .uint))
    (s t d : Nat) (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (out : Heap H) (ho : checkedUintSequence c off c' off' hp r a s t d q b u v f = some out)
    (k : HRef H T) (hr : r.id ≠ k.id) (hq : q.id ≠ k.id) : out.get k = hp.get k := by
  obtain ⟨mid, hfirst, hsecond⟩ := (checkedUintSequence_some_iff c off c' off' hp r a s t d q b u v f out).mp ho
  exact (checkedCalldataUints_frame hc' mid q b u v f out hsecond k hq).trans
    (checkedCalldataUints_frame hc hp r a s t d mid hfirst k hr)

/-- Successful composition transports both actual intermediate heaps through
initial preserving growth, deriving the second Keeps from the first operation. -/
theorem checkedUintSequence_keeps {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D (.int .u256)} {ys : Fin L' → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H H' : HTy} {R Q : RefTy} {hp : Heap H} {hp' : Heap H'}
    (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (out : Heap H) (ho : checkedUintSequence c off c' off' hp r a s t d q b u v f = some out) :
    ∃ out', checkedUintSequence c off c' off' hp' (r.wk e) a s t d (q.wk e) b u v f = some out' ∧
      Heap.Keeps e out out' := by
  obtain ⟨mid, hfirst, hsecond⟩ := (checkedUintSequence_some_iff c off c' off' hp r a s t d q b u v f out).mp ho
  obtain ⟨mid', hf, hk1⟩ := checkedCalldataUints_keeps hc e hk r a s t d mid hfirst
  obtain ⟨out', hs, hk2⟩ := checkedCalldataUints_keeps hc' e hk1 q b u v f out hsecond
  exact ⟨out', (checkedUintSequence_some_iff c off c' off' hp' (r.wk e) a s t d (q.wk e) b u v f out').mpr ⟨mid', hf, hs⟩, hk2⟩
/-- info: 'Solidity.Backend.MemoryOps.checkedUintSequence_same_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintSequence_same_checked
/-- info: 'Solidity.Backend.MemoryOps.checkedUintSequence_same_elems' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintSequence_same_elems
/-- info: 'Solidity.Backend.MemoryOps.checkedUintSequence_second_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintSequence_second_read
/-- info: 'Solidity.Backend.MemoryOps.checkedUintSequence_first_exterior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms checkedUintSequence_first_exterior
/-- info: 'Solidity.Backend.MemoryOps.checkedUintSequence_same_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintSequence_same_comm
/-- info: 'Solidity.Backend.MemoryOps.checkedUintSequence_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintSequence_frame
/-- info: 'Solidity.Backend.MemoryOps.checkedUintSequence_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintSequence_keeps

set_option backward.isDefEq.respectTransparency false in
/-- Distinct same-family targets use the existing whole-heap overwrite law. -/
theorem checkedBoolSequence_other_checked {D : Source.Layout} {n n' : Option Nat} {c c' : Source.Calldata D}
    {off off' L L' : Nat} {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D .bool} {ys : Fin L' → Source.Data D .bool}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q : RefTy} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat)
    (hs : SliceBounds L s t) (hd : d+(t-s) ≤ hp.len r a)
    (hu : SliceBounds L' u v) (he : f+(v-u) ≤ hp.len q b) (hne : r.id ≠ q.id) :
    checkedBoolSequence c off c' off' hp r a s t d q b u v f = some
      (overwriteTwo hp r a d (((List.ofFn (fun i => calldataBool (xs i))).drop s).take (t-s)) (by rw [calldataBools_slice_length xs hs]; exact hd)
        q b f (((List.ofFn (fun i => calldataBool (ys i))).drop u).take (v-u)) (by rw [calldataBools_slice_length ys hu]; exact he) hne) := by
  unfold checkedBoolSequence
  rw [checkedCalldataBools_some hc hp r a s t d hs hd]
  simp only [Option.bind_some]
  exact checkedCalldataBools_some hc' _ q b u v f hu (by rw [overwriteSlice_all_len]; exact he)

theorem checkedBoolSequence_other_comm {D : Source.Layout} {n n' : Option Nat} {c c' : Source.Calldata D}
    {off off' L L' : Nat} {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D .bool} {ys : Fin L' → Source.Data D .bool}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q : RefTy} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat)
    (hs : SliceBounds L s t) (hd : d+(t-s) ≤ hp.len r a)
    (hu : SliceBounds L' u v) (he : f+(v-u) ≤ hp.len q b) (hne : r.id ≠ q.id) :
    checkedBoolSequence c off c' off' hp r a s t d q b u v f =
      checkedBoolSequence c' off' c off hp q b u v f r a s t d := by
  rw [checkedBoolSequence_other_checked hc hc' hp r a s t d q b u v f hs hd hu he hne,
    checkedBoolSequence_other_checked hc' hc hp q b u v f r a s t d hu he hs hd hne.symm]
  congr 1
  apply overwriteTwo_comm

/-- info: 'Solidity.Backend.MemoryOps.checkedBoolSequence_other_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms checkedBoolSequence_other_checked
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolSequence_other_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolSequence_other_comm

set_option backward.isDefEq.respectTransparency false in
/-- Distinct same-family targets use the existing whole-heap overwrite law. -/
theorem checkedUintSequence_other_checked {D : Source.Layout} {n n' : Option Nat} {c c' : Source.Calldata D}
    {off off' L L' : Nat} {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D (.int .u256)} {ys : Fin L' → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q : RefTy} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (hs : SliceBounds L s t) (hd : d+(t-s) ≤ hp.len r a)
    (hu : SliceBounds L' u v) (he : f+(v-u) ≤ hp.len q b) (hne : r.id ≠ q.id) :
    checkedUintSequence c off c' off' hp r a s t d q b u v f = some
      (overwriteTwo hp r a d (((List.ofFn (fun i => calldataUint (xs i))).drop s).take (t-s)) (by rw [calldataUints_slice_length xs hs]; exact hd)
        q b f (((List.ofFn (fun i => calldataUint (ys i))).drop u).take (v-u)) (by rw [calldataUints_slice_length ys hu]; exact he) hne) := by
  unfold checkedUintSequence
  rw [checkedCalldataUints_some hc hp r a s t d hs hd]
  simp only [Option.bind_some]
  exact checkedCalldataUints_some hc' _ q b u v f hu (by rw [overwriteSlice_all_len]; exact he)

theorem checkedUintSequence_other_comm {D : Source.Layout} {n n' : Option Nat} {c c' : Source.Calldata D}
    {off off' L L' : Nat} {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D (.int .u256)} {ys : Fin L' → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q : RefTy} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (hs : SliceBounds L s t) (hd : d+(t-s) ≤ hp.len r a)
    (hu : SliceBounds L' u v) (he : f+(v-u) ≤ hp.len q b) (hne : r.id ≠ q.id) :
    checkedUintSequence c off c' off' hp r a s t d q b u v f =
      checkedUintSequence c' off' c off hp q b u v f r a s t d := by
  rw [checkedUintSequence_other_checked hc hc' hp r a s t d q b u v f hs hd hu he hne,
    checkedUintSequence_other_checked hc' hc hp q b u v f r a s t d hu he hs hd hne.symm]
  congr 1
  apply overwriteTwo_comm

/-- info: 'Solidity.Backend.MemoryOps.checkedUintSequence_other_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms checkedUintSequence_other_checked
/-- info: 'Solidity.Backend.MemoryOps.checkedUintSequence_other_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintSequence_other_comm
end Solidity.Backend.MemoryOps
