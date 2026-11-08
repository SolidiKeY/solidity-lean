import Solidity.Backend.MemoryOps.CalldataTransfer
import Solidity.Backend.MemoryOps.CalldataUintTransfer
import Solidity.Backend.MemoryOps.IntervalOverwrite

/-! Option composition of actual immutable decoded transfers. No payload is an
operation input. These laws do not define Source halts, rollback, ABI decoding
or target execution. Missing entries remain adapter rejection, not exclusions. -/
namespace Solidity.Backend.MemoryOps

/-- Expose only payloads actually extracted by the existing operation. -/
theorem boolTransfer_result_lookup {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .bool)) (s t d : Nat) (out : Heap H)
    (ho : checkedCalldataBools c off hp r a s t d = some out) :
    ∃ bs : List Bool, calldataBools c off = some bs ∧
      ∃ (_hs : SliceBounds bs.length s t)
        (hd : d + ((bs.drop s).take (t-s)).length ≤ hp.len r a),
        out = overwriteSlice hp r a d ((bs.drop s).take (t-s)) hd := by
  unfold checkedCalldataBools at ho
  cases hl : calldataBools c off with
  | none => rw [hl] at ho; cases ho
  | some bs =>
    rw [hl] at ho
    simp only [Bind.bind, Option.bind] at ho
    split at ho
    next hs =>
      split at ho
      next hd => exact ⟨bs, rfl, ⟨hs.1, hs.2⟩, _, (Option.some.inj ho).symm⟩
      next hd => cases ho
    next hs => cases ho

/-- Successful transfers preserve every actual typed array length. -/
theorem boolTransfer_all_len {D : Source.Layout} {H : HTy} {R Q : RefTy} {F : Ty}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .bool)) (s t d : Nat) (out : Heap H)
    (ho : checkedCalldataBools c off hp r a s t d = some out)
    (q : HRef H Q) (b : ArrTy Q F) : out.len q b = hp.len q b := by
  obtain ⟨_, _, _, hd, rfl⟩ := boolTransfer_result_lookup c off hp r a s t d out ho
  exact overwriteSlice_all_len hp r a d _ hd q b

/-- Complete rejection classification includes missing/unsupported entries. -/
theorem boolTransfer_none_lookup {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .bool)) (s t d : Nat) :
    checkedCalldataBools c off hp r a s t d = none ↔
      match calldataBools c off with
      | none => True
      | some bs => t < s ∨ bs.length < t ∨ hp.len r a < d + (t-s) := by
  unfold checkedCalldataBools
  cases hl : calldataBools c off with
  | none => simp only [Bind.bind, Option.bind]
  | some bs =>
    simp only [Bind.bind, Option.bind]
    by_cases hs : s ≤ t ∧ t ≤ bs.length
    · rw [dif_pos hs]
      by_cases hd : d + (t-s) ≤ hp.len r a
      · rw [dif_pos hd]
        simp only [Option.some_ne_none, false_iff]
        omega
      · rw [dif_neg hd]
        simp only [true_iff]
        omega
    · rw [dif_neg hs]
      simp only [true_iff]
      omega

/-- Rejection depends on the actual target length, never its changed contents. -/
theorem boolTransfer_none_length {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp mid : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .bool)) (s t d : Nat) (hl : mid.len r a = hp.len r a) :
    checkedCalldataBools c off mid r a s t d = none ↔ checkedCalldataBools c off hp r a s t d = none := by
  simp only [boolTransfer_none_lookup, hl]

/-- Unknown or unsupported inputs retain rejection across preserving growth. -/
theorem boolTransfer_none_keeps {D : Source.Layout} {H H' : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) {hp : Heap H} {hp' : Heap H'}
    (e : H <+: H') (hk : Heap.Keeps e hp hp') (r : HRef H R)
    (a : ArrTy R (.prim .bool)) (s t d : Nat) :
    checkedCalldataBools c off hp' (r.wk e) a s t d = none ↔ checkedCalldataBools c off hp r a s t d = none := by
  simp only [boolTransfer_none_lookup, hk.len]

/-- Two existing decoded transfers, in actual execution order. -/
def checkedBoolSequence {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat) : Option (Heap H) :=
  (checkedCalldataBools c off hp r a s t d).bind fun mid => checkedCalldataBools c' off' mid q b u v f

theorem checkedBoolSequence_some_iff {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat) (out : Heap H) :
    checkedBoolSequence c off c' off' hp r a s t d q b u v f = some out ↔
      ∃ mid, checkedCalldataBools c off hp r a s t d = some mid ∧
        checkedCalldataBools c' off' mid q b u v f = some out := Option.bind_eq_some_iff

/-- Ordered failure: first rejection short-circuits, otherwise the second
operation rejects on the actually reached intermediate. -/
theorem checkedBoolSequence_none_ordered {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat) :
    checkedBoolSequence c off c' off' hp r a s t d q b u v f = none ↔
      checkedCalldataBools c off hp r a s t d = none ∨
        ∃ mid, checkedCalldataBools c off hp r a s t d = some mid ∧
          checkedCalldataBools c' off' mid q b u v f = none := by
  unfold checkedBoolSequence
  cases hfirst : checkedCalldataBools c off hp r a s t d with
  | none => simp only [Option.bind_none, true_or]
  | some mid => simp only [Option.bind_some, Option.some_ne_none, false_or, Option.some.injEq, exists_eq_left']

/-- Both rejection tests can be expressed at the original heap: the second
length fact follows from the first operation, not an assumed frame. -/
theorem checkedBoolSequence_none_iff {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat) :
    checkedBoolSequence c off c' off' hp r a s t d q b u v f = none ↔
      checkedCalldataBools c off hp r a s t d = none ∨ checkedCalldataBools c' off' hp q b u v f = none := by
  unfold checkedBoolSequence
  cases hf : checkedCalldataBools c off hp r a s t d with
  | none => simp only [Option.bind_none, true_or]
  | some mid =>
    simp only [Option.bind_some, Option.some_ne_none, false_or]
    exact boolTransfer_none_length c' off' hp mid q b u v f
      (boolTransfer_all_len c off hp r a s t d mid hf q b)

/-- Actual failure behavior transports even when either source lookup fails. -/
theorem checkedBoolSequence_none_keeps {D : Source.Layout} {H H' : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .bool)) (u v f : Nat) :
    checkedBoolSequence c off c' off' hp' (r.wk e) a s t d (q.wk e) b u v f = none ↔
      checkedBoolSequence c off c' off' hp r a s t d q b u v f = none := by
  simp only [checkedBoolSequence_none_iff, boolTransfer_none_keeps c off e hk r a s t d,
    boolTransfer_none_keeps c' off' e hk q b u v f]
/-- info: 'Solidity.Backend.MemoryOps.boolTransfer_result_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boolTransfer_result_lookup
/-- info: 'Solidity.Backend.MemoryOps.boolTransfer_all_len' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boolTransfer_all_len
/-- info: 'Solidity.Backend.MemoryOps.boolTransfer_none_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boolTransfer_none_lookup
/-- info: 'Solidity.Backend.MemoryOps.boolTransfer_none_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boolTransfer_none_length
/-- info: 'Solidity.Backend.MemoryOps.boolTransfer_none_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boolTransfer_none_keeps
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolSequence_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolSequence_some_iff
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolSequence_none_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolSequence_none_ordered
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolSequence_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolSequence_none_iff
/-- info: 'Solidity.Backend.MemoryOps.checkedBoolSequence_none_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedBoolSequence_none_keeps

/-- Expose only payloads actually extracted by the existing operation. -/
theorem uintTransfer_result_lookup {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .uint)) (s t d : Nat) (out : Heap H)
    (ho : checkedCalldataUints c off hp r a s t d = some out) :
    ∃ bs : List PrimTy.uint.Denote, calldataUints c off = some bs ∧
      ∃ (_hs : SliceBounds bs.length s t)
        (hd : d + ((bs.drop s).take (t-s)).length ≤ hp.len r a),
        out = overwriteSlice hp r a d ((bs.drop s).take (t-s)) hd := by
  unfold checkedCalldataUints at ho
  cases hl : calldataUints c off with
  | none => rw [hl] at ho; cases ho
  | some bs =>
    rw [hl] at ho
    simp only [Bind.bind, Option.bind] at ho
    split at ho
    next hs =>
      split at ho
      next hd => exact ⟨bs, rfl, ⟨hs.1, hs.2⟩, _, (Option.some.inj ho).symm⟩
      next hd => cases ho
    next hs => cases ho

/-- Successful transfers preserve every actual typed array length. -/
theorem uintTransfer_all_len {D : Source.Layout} {H : HTy} {R Q : RefTy} {F : Ty}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .uint)) (s t d : Nat) (out : Heap H)
    (ho : checkedCalldataUints c off hp r a s t d = some out)
    (q : HRef H Q) (b : ArrTy Q F) : out.len q b = hp.len q b := by
  obtain ⟨_, _, _, hd, rfl⟩ := uintTransfer_result_lookup c off hp r a s t d out ho
  exact overwriteSlice_all_len hp r a d _ hd q b

/-- Complete rejection classification includes missing/unsupported entries. -/
theorem uintTransfer_none_lookup {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .uint)) (s t d : Nat) :
    checkedCalldataUints c off hp r a s t d = none ↔
      match calldataUints c off with
      | none => True
      | some bs => t < s ∨ bs.length < t ∨ hp.len r a < d + (t-s) := by
  unfold checkedCalldataUints
  cases hl : calldataUints c off with
  | none => simp only [Bind.bind, Option.bind]
  | some bs =>
    simp only [Bind.bind, Option.bind]
    by_cases hs : s ≤ t ∧ t ≤ bs.length
    · rw [dif_pos hs]
      by_cases hd : d + (t-s) ≤ hp.len r a
      · rw [dif_pos hd]
        simp only [Option.some_ne_none, false_iff]
        omega
      · rw [dif_neg hd]
        simp only [true_iff]
        omega
    · rw [dif_neg hs]
      simp only [true_iff]
      omega

/-- Rejection depends on the actual target length, never its changed contents. -/
theorem uintTransfer_none_length {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp mid : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .uint)) (s t d : Nat) (hl : mid.len r a = hp.len r a) :
    checkedCalldataUints c off mid r a s t d = none ↔ checkedCalldataUints c off hp r a s t d = none := by
  simp only [uintTransfer_none_lookup, hl]

/-- Unknown or unsupported inputs retain rejection across preserving growth. -/
theorem uintTransfer_none_keeps {D : Source.Layout} {H H' : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) {hp : Heap H} {hp' : Heap H'}
    (e : H <+: H') (hk : Heap.Keeps e hp hp') (r : HRef H R)
    (a : ArrTy R (.prim .uint)) (s t d : Nat) :
    checkedCalldataUints c off hp' (r.wk e) a s t d = none ↔ checkedCalldataUints c off hp r a s t d = none := by
  simp only [uintTransfer_none_lookup, hk.len]

/-- Two existing decoded transfers, in actual execution order. -/
def checkedUintSequence {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) : Option (Heap H) :=
  (checkedCalldataUints c off hp r a s t d).bind fun mid => checkedCalldataUints c' off' mid q b u v f

theorem checkedUintSequence_some_iff {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) (out : Heap H) :
    checkedUintSequence c off c' off' hp r a s t d q b u v f = some out ↔
      ∃ mid, checkedCalldataUints c off hp r a s t d = some mid ∧
        checkedCalldataUints c' off' mid q b u v f = some out := Option.bind_eq_some_iff

/-- Ordered failure: first rejection short-circuits, otherwise the second
operation rejects on the actually reached intermediate. -/
theorem checkedUintSequence_none_ordered {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) :
    checkedUintSequence c off c' off' hp r a s t d q b u v f = none ↔
      checkedCalldataUints c off hp r a s t d = none ∨
        ∃ mid, checkedCalldataUints c off hp r a s t d = some mid ∧
          checkedCalldataUints c' off' mid q b u v f = none := by
  unfold checkedUintSequence
  cases hfirst : checkedCalldataUints c off hp r a s t d with
  | none => simp only [Option.bind_none, true_or]
  | some mid => simp only [Option.bind_some, Option.some_ne_none, false_or, Option.some.injEq, exists_eq_left']

/-- Both rejection tests can be expressed at the original heap: the second
length fact follows from the first operation, not an assumed frame. -/
theorem checkedUintSequence_none_iff {D : Source.Layout} {H : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (hp : Heap H) (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) :
    checkedUintSequence c off c' off' hp r a s t d q b u v f = none ↔
      checkedCalldataUints c off hp r a s t d = none ∨ checkedCalldataUints c' off' hp q b u v f = none := by
  unfold checkedUintSequence
  cases hf : checkedCalldataUints c off hp r a s t d with
  | none => simp only [Option.bind_none, true_or]
  | some mid =>
    simp only [Option.bind_some, Option.some_ne_none, false_or]
    exact uintTransfer_none_length c' off' hp mid q b u v f
      (uintTransfer_all_len c off hp r a s t d mid hf q b)

/-- Actual failure behavior transports even when either source lookup fails. -/
theorem checkedUintSequence_none_keeps {D : Source.Layout} {H H' : HTy} {R Q : RefTy}
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R (.prim .uint)) (s t d : Nat)
    (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat) :
    checkedUintSequence c off c' off' hp' (r.wk e) a s t d (q.wk e) b u v f = none ↔
      checkedUintSequence c off c' off' hp r a s t d q b u v f = none := by
  simp only [checkedUintSequence_none_iff, uintTransfer_none_keeps c off e hk r a s t d,
    uintTransfer_none_keeps c' off' e hk q b u v f]
/-- info: 'Solidity.Backend.MemoryOps.uintTransfer_result_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms uintTransfer_result_lookup
/-- info: 'Solidity.Backend.MemoryOps.uintTransfer_all_len' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms uintTransfer_all_len
/-- info: 'Solidity.Backend.MemoryOps.uintTransfer_none_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms uintTransfer_none_lookup
/-- info: 'Solidity.Backend.MemoryOps.uintTransfer_none_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms uintTransfer_none_length
/-- info: 'Solidity.Backend.MemoryOps.uintTransfer_none_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms uintTransfer_none_keeps
/-- info: 'Solidity.Backend.MemoryOps.checkedUintSequence_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintSequence_some_iff
/-- info: 'Solidity.Backend.MemoryOps.checkedUintSequence_none_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintSequence_none_ordered
/-- info: 'Solidity.Backend.MemoryOps.checkedUintSequence_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintSequence_none_iff
/-- info: 'Solidity.Backend.MemoryOps.checkedUintSequence_none_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintSequence_none_keeps
end Solidity.Backend.MemoryOps
