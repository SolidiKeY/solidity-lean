import Solidity.Backend.MemoryOps.CalldataUintSchedule
import Solidity.Backend.MemoryOps.SnapshotScheduleGrowth

/-! Concrete context applications of the decoded-initialized finite schedule.
Initial Keeps is independent; actual Heap.alloc corollaries discharge it. No
fresh Source object or deep-child liveness follows from fresh own-field frames. -/
namespace Solidity.Backend.MemoryOps

theorem checkedUintCaptures_keeps {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {values : Fin len → Source.Data D (.int .u256)} (hc : DecodedArrayAt c off len hn values)
    {H H' : HTy} {R : RefTy} {hp : Heap H} {hp' : Heap H'}
    (e : H <+: H') (hk : Heap.Keeps e hp hp') (r : HRef H R)
    (a : ArrTy R (.prim .uint)) (s t d : Nat) (xs : List SnapshotArgs) (out : Heap H)
    (ho : checkedUintCaptures c off hp r a s t d xs = some out) :
    ∃ out', checkedUintCaptures c off hp' (r.wk e) a s t d xs = some out' ∧ Heap.Keeps e out out' := by
  obtain ⟨mid,hfirst,htail⟩ := (checkedUintCaptures_some c off hp r a s t d xs out).mp ho
  obtain ⟨mid',hfirst',hk1⟩ := checkedCalldataUints_keeps hc e hk r a s t d mid hfirst
  obtain ⟨out',htail',hk2⟩ := runCaptures_keeps e hk1 r a xs out htail
  exact ⟨out',(checkedUintCaptures_some c off hp' (r.wk e) a s t d xs out').mpr ⟨mid',hfirst',htail'⟩,hk2⟩

theorem checkedUintCaptures_none_keeps {D : Source.Layout} {n : Option Nat}
    {c : Source.Calldata D} {off len : Nat} {hn : ∀ m, n = some m → m = len}
    {values : Fin len → Source.Data D (.int .u256)} (hc : DecodedArrayAt c off len hn values)
    {H H' : HTy} {R : RefTy} {hp : Heap H} {hp' : Heap H'}
    (e : H <+: H') (hk : Heap.Keeps e hp hp') (r : HRef H R)
    (a : ArrTy R (.prim .uint)) (s t d : Nat) (xs : List SnapshotArgs) :
    checkedUintCaptures c off hp' (r.wk e) a s t d xs = none ↔
      checkedUintCaptures c off hp r a s t d xs = none := by
  cases hf : checkedCalldataUints c off hp r a s t d with
  | none =>
    have hf' := (uintTransfer_none_keeps c off e hk r a s t d).mpr hf
    simp only [checkedUintCaptures,hf,hf',Option.bind_none]
  | some mid =>
    obtain ⟨mid',hf',hk1⟩ := checkedCalldataUints_keeps hc e hk r a s t d mid hf
    simp only [checkedUintCaptures,hf,hf',Option.bind_some]
    exact runCaptures_none_keeps e hk1 r a xs

/-- Actual allocation occurs AFTER the real decoded transfer, whose contents
may have broken the old child relation. The finite tail reads that changed mid. -/
theorem checkedUintCaptures_interstage_alloc {D : Source.Layout} {H : HTy} {R A : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp out : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .uint)) (s t d : Nat) (xs : List SnapshotArgs)
    (ho : checkedUintCaptures c off hp r a s t d xs = some out) (obj : MObj H A) :
    let e := List.prefix_append H [A]
    ∃ mid out', checkedCalldataUints c off hp r a s t d = some mid ∧
      runCaptures (mid.alloc obj).1 (r.wk e) a xs = some out' ∧ Heap.Keeps e out out' ∧
      out'.get (mid.alloc obj).2 = (mid.alloc obj).1.get (mid.alloc obj).2 := by
  dsimp only
  obtain ⟨mid,hfirst,htail⟩ := (checkedUintCaptures_some c off hp r a s t d xs out).mp ho
  obtain ⟨out',htail',hk,hfresh⟩ := runCaptures_alloc mid obj r a xs out htail
  exact ⟨mid,out',hfirst,htail',hk,hfresh⟩

/-- info: 'Solidity.Backend.MemoryOps.checkedUintCaptures_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedUintCaptures_keeps
/-- info: 'Solidity.Backend.MemoryOps.checkedUintCaptures_none_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkedUintCaptures_none_keeps
/-- info: 'Solidity.Backend.MemoryOps.checkedUintCaptures_interstage_alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checkedUintCaptures_interstage_alloc
end Solidity.Backend.MemoryOps
