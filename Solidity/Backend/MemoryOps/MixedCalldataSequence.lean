import Solidity.Backend.MemoryOps.CalldataSequenceLaws

/-! Mixed decoded Boolean/uint transfers compose existing operations only.
Their typed array references necessarily have different logical IDs; no same-ID
cross-type witness, physical address premise or Source execution is invented. -/
namespace Solidity.Backend.MemoryOps

theorem bool_uint_transfer_ne {H : HTy} {R Q : RefTy} (r : HRef H R)
    (a : ArrTy R (.prim .bool)) (q : HRef H Q) (b : ArrTy Q (.prim .uint)) : r.id ≠ q.id := by
  intro he
  obtain ⟨rfl, hq⟩ := HRef.heq_of_id r q he
  cases hq
  cases a <;> cases b

def checkedBoolUintSequence {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) : Option (Heap H) :=
  (checkedCalldataBools c off hp r a s t d).bind fun mid => checkedCalldataUints c' off' mid q b u v f

theorem checkedBoolUintSequence_some_iff {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) (out : Heap H) :
    checkedBoolUintSequence c off c' off' hp r a s t d q b u v f = some out ↔
      ∃ mid, checkedCalldataBools c off hp r a s t d = some mid ∧
        checkedCalldataUints c' off' mid q b u v f = some out := Option.bind_eq_some_iff

theorem checkedBoolUintSequence_none_ordered {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) :
    checkedBoolUintSequence c off c' off' hp r a s t d q b u v f = none ↔
      checkedCalldataBools c off hp r a s t d = none ∨
        ∃ mid, checkedCalldataBools c off hp r a s t d = some mid ∧
          checkedCalldataUints c' off' mid q b u v f = none := by
  unfold checkedBoolUintSequence
  cases hfirst : checkedCalldataBools c off hp r a s t d with
  | none => simp only [Option.bind_none, true_or]
  | some mid => simp only [Option.bind_some, Option.some_ne_none, false_or, Option.some.injEq, exists_eq_left']

theorem checkedBoolUintSequence_none_iff {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) :
    checkedBoolUintSequence c off c' off' hp r a s t d q b u v f = none ↔
      checkedCalldataBools c off hp r a s t d = none ∨ checkedCalldataUints c' off' hp q b u v f = none := by
  unfold checkedBoolUintSequence
  cases hf : checkedCalldataBools c off hp r a s t d with
  | none => simp only [Option.bind_none, true_or]
  | some mid =>
    simp only [Option.bind_some, Option.some_ne_none, false_or]
    exact uintTransfer_none_length c' off' hp mid q b u v f
      (boolTransfer_all_len c off hp r a s t d mid hf q b)

/-- Actual computed payloads feed the existing disjoint-object operation. -/
theorem checkedBoolUintSequence_checked {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D .bool} {ys : Fin L' → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q : RefTy} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (hs : SliceBounds L s t) (hd : d+(t-s) ≤ hp.len r a)
    (hu : SliceBounds L' u v) (he : f+(v-u) ≤ hp.len q b) :
    checkedBoolUintSequence c off c' off' hp r a s t d q b u v f =
      some (overwriteTwo hp r a d (((List.ofFn (fun i => calldataBool (xs i))).drop s).take (t-s)) (by rw [calldataBools_slice_length xs hs]; exact hd)
        q b f (((List.ofFn (fun i => calldataUint (ys i))).drop u).take (v-u)) (by rw [calldataUints_slice_length ys hu]; exact he) (bool_uint_transfer_ne r a q b)) := by
  unfold checkedBoolUintSequence
  rw [checkedCalldataBools_some hc hp r a s t d hs hd]
  simp only [Option.bind_some]
  exact checkedCalldataUints_some hc' _ q b u v f hu
    (by rw [overwriteSlice_all_len]; exact he)

/-- Complete ordered observations of both differently typed destinations. -/
theorem checkedBoolUintSequence_elems {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D .bool} {ys : Fin L' → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q : RefTy} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (out : Heap H) (ho : checkedBoolUintSequence c off c' off' hp r a s t d q b u v f = some out) :
    MObj.elems a (out.get r) = replaceSlice (MObj.elems a (hp.get r)) d (((List.ofFn (fun i => calldataBool (xs i))).drop s).take (t-s)) ∧
    MObj.elems b (out.get q) = replaceSlice (MObj.elems b (hp.get q)) f (((List.ofFn (fun i => calldataUint (ys i))).drop u).take (v-u)) := by
  have hne : r.id ≠ q.id := bool_uint_transfer_ne r a q b
  obtain ⟨mid, hf, hs⟩ := (checkedBoolUintSequence_some_iff c off c' off' hp r a s t d q b u v f out).mp ho
  constructor
  · rw [checkedCalldataUints_frame hc' mid q b u v f out hs r hne.symm,
      checkedCalldataBools_elems hc hp r a s t d mid hf]
  · rw [checkedCalldataUints_elems hc' mid q b u v f out hs,
      checkedCalldataBools_frame hc hp r a s t d mid hf q hne]

theorem checkedBoolUintSequence_frame {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D .bool} {ys : Fin L' → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q T : RefTy} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (out : Heap H) (ho : checkedBoolUintSequence c off c' off' hp r a s t d q b u v f = some out)
    (k : HRef H T) (hr : r.id ≠ k.id) (hq : q.id ≠ k.id) : out.get k = hp.get k := by
  obtain ⟨mid, hf, hs⟩ := (checkedBoolUintSequence_some_iff c off c' off' hp r a s t d q b u v f out).mp ho
  exact (checkedCalldataUints_frame hc' mid q b u v f out hs k hq).trans (checkedCalldataBools_frame hc hp r a s t d mid hf k hr)

theorem checkedBoolUintSequence_keeps {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D .bool} {ys : Fin L' → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H H' : HTy} {R Q : RefTy} {hp : Heap H} {hp' : Heap H'}
    (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (out : Heap H) (ho : checkedBoolUintSequence c off c' off' hp r a s t d q b u v f = some out) :
    ∃ out', checkedBoolUintSequence c off c' off' hp' (r.wk e) a s t d (q.wk e) b u v f = some out' ∧ Heap.Keeps e out out' := by
  obtain ⟨mid, hf, hs⟩ := (checkedBoolUintSequence_some_iff c off c' off' hp r a s t d q b u v f out).mp ho
  obtain ⟨mid', hf', hk1⟩ := checkedCalldataBools_keeps hc e hk r a s t d mid hf
  obtain ⟨out', hs', hk2⟩ := checkedCalldataUints_keeps hc' e hk1 q b u v f out hs
  exact ⟨out', (checkedBoolUintSequence_some_iff c off c' off' hp' (r.wk e) a s t d (q.wk e) b u v f out').mpr ⟨mid', hf', hs'⟩, hk2⟩

theorem checkedBoolUintSequence_none_keeps {D : Source.Layout} {H H' : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) :
    checkedBoolUintSequence c off c' off' hp' (r.wk e) a s t d (q.wk e) b u v f = none ↔
      checkedBoolUintSequence c off c' off' hp r a s t d q b u v f = none := by
  simp only [checkedBoolUintSequence_none_iff, boolTransfer_none_keeps c off e hk r a s t d,
    uintTransfer_none_keeps c' off' e hk q b u v f]
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolUintSequence_some_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolUintSequence_some_iff
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolUintSequence_none_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolUintSequence_none_ordered
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolUintSequence_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolUintSequence_none_iff
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolUintSequence_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolUintSequence_checked
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolUintSequence_elems' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolUintSequence_elems
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolUintSequence_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolUintSequence_frame
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolUintSequence_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolUintSequence_keeps
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolUintSequence_none_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms checkedBoolUintSequence_none_keeps

def checkedUintBoolSequence {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat) : Option (Heap H) :=
  (checkedCalldataUints c off hp r a s t d).bind fun mid => checkedCalldataBools c' off' mid q b u v f

theorem checkedUintBoolSequence_some_iff {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat) (out : Heap H) :
    checkedUintBoolSequence c off c' off' hp r a s t d q b u v f = some out ↔
      ∃ mid, checkedCalldataUints c off hp r a s t d = some mid ∧
        checkedCalldataBools c' off' mid q b u v f = some out := Option.bind_eq_some_iff

theorem checkedUintBoolSequence_none_ordered {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat) :
    checkedUintBoolSequence c off c' off' hp r a s t d q b u v f = none ↔
      checkedCalldataUints c off hp r a s t d = none ∨
        ∃ mid, checkedCalldataUints c off hp r a s t d = some mid ∧
          checkedCalldataBools c' off' mid q b u v f = none := by
  unfold checkedUintBoolSequence
  cases hfirst : checkedCalldataUints c off hp r a s t d with
  | none => simp only [Option.bind_none, true_or]
  | some mid => simp only [Option.bind_some, Option.some_ne_none, false_or, Option.some.injEq, exists_eq_left']

theorem checkedUintBoolSequence_none_iff {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat) :
    checkedUintBoolSequence c off c' off' hp r a s t d q b u v f = none ↔
      checkedCalldataUints c off hp r a s t d = none ∨ checkedCalldataBools c' off' hp q b u v f = none := by
  unfold checkedUintBoolSequence
  cases hf : checkedCalldataUints c off hp r a s t d with
  | none => simp only [Option.bind_none, true_or]
  | some mid =>
    simp only [Option.bind_some, Option.some_ne_none, false_or]
    exact boolTransfer_none_length c' off' hp mid q b u v f
      (uintTransfer_all_len c off hp r a s t d mid hf q b)

/-- Actual computed payloads feed the existing disjoint-object operation. -/
theorem checkedUintBoolSequence_checked {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D (.int .u256)} {ys : Fin L' → Source.Data D .bool}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q : RefTy} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat)
    (hs : SliceBounds L s t) (hd : d+(t-s) ≤ hp.len r a)
    (hu : SliceBounds L' u v) (he : f+(v-u) ≤ hp.len q b) :
    checkedUintBoolSequence c off c' off' hp r a s t d q b u v f =
      some (overwriteTwo hp r a d (((List.ofFn (fun i => calldataUint (xs i))).drop s).take (t-s)) (by rw [calldataUints_slice_length xs hs]; exact hd)
        q b f (((List.ofFn (fun i => calldataBool (ys i))).drop u).take (v-u)) (by rw [calldataBools_slice_length ys hu]; exact he) ((bool_uint_transfer_ne q b r a).symm)) := by
  unfold checkedUintBoolSequence
  rw [checkedCalldataUints_some hc hp r a s t d hs hd]
  simp only [Option.bind_some]
  exact checkedCalldataBools_some hc' _ q b u v f hu
    (by rw [overwriteSlice_all_len]; exact he)

/-- Complete ordered observations of both differently typed destinations. -/
theorem checkedUintBoolSequence_elems {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D (.int .u256)} {ys : Fin L' → Source.Data D .bool}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q : RefTy} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat)
    (out : Heap H) (ho : checkedUintBoolSequence c off c' off' hp r a s t d q b u v f = some out) :
    MObj.elems a (out.get r) = replaceSlice (MObj.elems a (hp.get r)) d (((List.ofFn (fun i => calldataUint (xs i))).drop s).take (t-s)) ∧
    MObj.elems b (out.get q) = replaceSlice (MObj.elems b (hp.get q)) f (((List.ofFn (fun i => calldataBool (ys i))).drop u).take (v-u)) := by
  have hne : r.id ≠ q.id := (bool_uint_transfer_ne q b r a).symm
  obtain ⟨mid, hf, hs⟩ := (checkedUintBoolSequence_some_iff c off c' off' hp r a s t d q b u v f out).mp ho
  constructor
  · rw [checkedCalldataBools_frame hc' mid q b u v f out hs r hne.symm,
      checkedCalldataUints_elems hc hp r a s t d mid hf]
  · rw [checkedCalldataBools_elems hc' mid q b u v f out hs,
      checkedCalldataUints_frame hc hp r a s t d mid hf q hne]

theorem checkedUintBoolSequence_frame {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D (.int .u256)} {ys : Fin L' → Source.Data D .bool}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q T : RefTy} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat)
    (out : Heap H) (ho : checkedUintBoolSequence c off c' off' hp r a s t d q b u v f = some out)
    (k : HRef H T) (hr : r.id ≠ k.id) (hq : q.id ≠ k.id) : out.get k = hp.get k := by
  obtain ⟨mid, hf, hs⟩ := (checkedUintBoolSequence_some_iff c off c' off' hp r a s t d q b u v f out).mp ho
  exact (checkedCalldataBools_frame hc' mid q b u v f out hs k hq).trans (checkedCalldataUints_frame hc hp r a s t d mid hf k hr)

theorem checkedUintBoolSequence_keeps {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D (.int .u256)} {ys : Fin L' → Source.Data D .bool}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H H' : HTy} {R Q : RefTy} {hp : Heap H} {hp' : Heap H'}
    (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat)
    (out : Heap H) (ho : checkedUintBoolSequence c off c' off' hp r a s t d q b u v f = some out) :
    ∃ out', checkedUintBoolSequence c off c' off' hp' (r.wk e) a s t d (q.wk e) b u v f = some out' ∧ Heap.Keeps e out out' := by
  obtain ⟨mid, hf, hs⟩ := (checkedUintBoolSequence_some_iff c off c' off' hp r a s t d q b u v f out).mp ho
  obtain ⟨mid', hf', hk1⟩ := checkedCalldataUints_keeps hc e hk r a s t d mid hf
  obtain ⟨out', hs', hk2⟩ := checkedCalldataBools_keeps hc' e hk1 q b u v f out hs
  exact ⟨out', (checkedUintBoolSequence_some_iff c off c' off' hp' (r.wk e) a s t d (q.wk e) b u v f out').mpr ⟨mid', hf', hs'⟩, hk2⟩

theorem checkedUintBoolSequence_none_keeps {D : Source.Layout} {H H' : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat) :
    checkedUintBoolSequence c off c' off' hp' (r.wk e) a s t d (q.wk e) b u v f = none ↔
      checkedUintBoolSequence c off c' off' hp r a s t d q b u v f = none := by
  simp only [checkedUintBoolSequence_none_iff, uintTransfer_none_keeps c off e hk r a s t d,
    boolTransfer_none_keeps c' off' e hk q b u v f]
/-- info: 'Solidity.Backend.MemoryOps.checkedUintBoolSequence_some_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedUintBoolSequence_some_iff
/-- info: 'Solidity.Backend.MemoryOps.checkedUintBoolSequence_none_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedUintBoolSequence_none_ordered
/-- info: 'Solidity.Backend.MemoryOps.checkedUintBoolSequence_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintBoolSequence_none_iff
/-- info: 'Solidity.Backend.MemoryOps.checkedUintBoolSequence_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedUintBoolSequence_checked
/-- info: 'Solidity.Backend.MemoryOps.checkedUintBoolSequence_elems' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedUintBoolSequence_elems
/-- info: 'Solidity.Backend.MemoryOps.checkedUintBoolSequence_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedUintBoolSequence_frame
/-- info: 'Solidity.Backend.MemoryOps.checkedUintBoolSequence_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedUintBoolSequence_keeps
/-- info: 'Solidity.Backend.MemoryOps.checkedUintBoolSequence_none_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms checkedUintBoolSequence_none_keeps

/-- Both orders are actual table-derived operations, equal as entire heaps. -/
theorem checkedBoolUintSequence_comm {D : Source.Layout} {n n' : Option Nat}
    {c c' : Source.Calldata D} {off off' L L' : Nat}
    {hn : ∀ m, n = some m → m = L} {hn' : ∀ m, n' = some m → m = L'}
    {xs : Fin L → Source.Data D .bool} {ys : Fin L' → Source.Data D (.int .u256)}
    (hc : DecodedArrayAt c off L hn xs) (hc' : DecodedArrayAt c' off' L' hn' ys)
    {H : HTy} {R Q : RefTy} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (hs : SliceBounds L s t) (hd : d+(t-s) ≤ hp.len r a)
    (hu : SliceBounds L' u v) (he : f+(v-u) ≤ hp.len q b) :
    checkedBoolUintSequence c off c' off' hp r a s t d q b u v f =
      checkedUintBoolSequence c' off' c off hp q b u v f r a s t d := by
  rw [checkedBoolUintSequence_checked hc hc' hp r a s t d q b u v f hs hd hu he,
    checkedUintBoolSequence_checked hc' hc hp q b u v f r a s t d hu he hs hd]
  congr 1
  apply overwriteTwo_comm

/-- info: 'Solidity.Backend.MemoryOps.bool_uint_transfer_ne' does not depend on any axioms -/
#guard_msgs in #print axioms bool_uint_transfer_ne
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolUintSequence_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolUintSequence_comm
end Solidity.Backend.MemoryOps
