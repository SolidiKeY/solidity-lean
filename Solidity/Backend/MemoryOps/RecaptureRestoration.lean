import Solidity.Backend.MemoryOps.OverwriteRestoration
import Solidity.Backend.MemoryOps.SequentialSnapshot
import Solidity.Backend.MemoryOps.CalldataSequenceFixtures

/-! Actual memory-to-memory recapture restoration. The second payload comes
from the REAL first output, not the immutable calldata or a frozen input list.
No alternate copy evaluator, fresh allocation or target execution is defined. -/
namespace Solidity.Backend.MemoryOps

/-- The captured second payload has exact INITIAL source observations selected
by whether its source cell was changed by the first write. -/
theorem recapturedPayload_read {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (s t d : Nat)
    (hs : SliceBounds (hp.len r a) s t) (hd : d+(t-s) ≤ hp.len r a)
    (u v : Nat) (hu : SliceBounds (hp.len r a) u v) (i : Nat) (hi : i < v-u) :
    (sliceElems (captureOverwrite hp r a r a s t d hs hd) r a u v)[i]? =
      if d ≤ u+i ∧ u+i < d+(t-s) then
        (MObj.elems a (hp.get r))[s+(u+i-d)]? else (MObj.elems a (hp.get r))[u+i]? := by
  rw [(sliceElems_read _ r a (by simpa only [captureOverwrite_all_len] using hu) hi).1,
    captureOverwrite_read_cases]

/-- Reuse the two-write theorem with the actual captured payloads. All second
bounds follow first-output length preservation; no payload equality is assumed. -/
theorem captureTwice_restore_iff {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (s t d : Nat)
    (hs : SliceBounds (hp.len r a) s t) (hd : d+(t-s) ≤ hp.len r a)
    (u v f : Nat) (hu : SliceBounds (hp.len r a) u v) (he : f+(v-u) ≤ hp.len r a) :
    captureTwice hp r a s t d hs hd u v f hu he = hp ↔
      LastWriteAgrees (MObj.elems a (hp.get r)) d (sliceElems hp r a s t) f
        (sliceElems (captureOverwrite hp r a r a s t d hs hd) r a u v) := by
  have hmid : SliceBounds ((captureOverwrite hp r a r a s t d hs hd).len r a) u v := by
    simpa only [captureOverwrite_all_len] using hu
  have h1 : d+(sliceElems hp r a s t).length ≤ hp.len r a := by rw [sliceElems_length hp r a hs]; exact hd
  have h2 : f+(sliceElems (captureOverwrite hp r a r a s t d hs hd) r a u v).length ≤ hp.len r a := by
    rw [sliceElems_length _ r a hmid]; exact he
  exact overwriteIntervals_eq_self_iff hp r a d _ h1 f _ h2

/-- Actual checked Some(initial heap) iff the actual recaptured last-write
criterion. Valid source/destination bounds remain explicit, not inferred from
an assumed successful result. -/
theorem checkedCaptureSequence_restore_iff {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (s t d : Nat)
    (hs : SliceBounds (hp.len r a) s t) (hd : d+(t-s) ≤ hp.len r a)
    (u v f : Nat) (hu : SliceBounds (hp.len r a) u v) (he : f+(v-u) ≤ hp.len r a) :
    checkedCaptureSequence hp r a r a s t d r a r a u v f = some hp ↔
      LastWriteAgrees (MObj.elems a (hp.get r)) d (sliceElems hp r a s t) f
        (sliceElems (captureOverwrite hp r a r a s t d hs hd) r a u v) := by
  rw [captureTwice_checked hp r a s t d hs hd u v f hu he,Option.some.injEq]
  exact captureTwice_restore_iff hp r a s t d hs hd u v f hu he

namespace RecaptureControls
open SequenceFixtures
private abbrev B := BoolChildRef
private abbrev H : HTy := [B,B]
private def r : HRef H B := ⟨0,rfl⟩
private def neighbor : HRef H B := ⟨1,rfl⟩
private def old (n : Nat) := [true,false,false] ++ List.replicate n false
set_option backward.isDefEq.respectTransparency false in
private def hp (n : Nat) (hn : n+3 < 2^256) : Heap H :=
  (⟨old n,by simp only [old,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,⟨[false,true],by decide⟩,())
set_option backward.isDefEq.respectTransparency false in
private theorem len (n : Nat) (hn : n+3 < 2^256) : (hp n hn).len r .dyn = n+3 := by
  simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,r,old,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
private theorem hs (n : Nat) (hn : n+3 < 2^256) : SliceBounds ((hp n hn).len r .dyn) 0 1 := by
  rw [len]; exact ⟨by decide,by omega⟩
private theorem hd (n : Nat) (hn : n+3 < 2^256) : 1+(1-0) ≤ (hp n hn).len r .dyn := by rw [len]; omega
private theorem hu (n : Nat) (hn : n+3 < 2^256) : SliceBounds ((hp n hn).len r .dyn) 1 3 := by
  rw [len]; exact ⟨by decide,by omega⟩
private theorem he (n : Nat) (hn : n+3 < 2^256) : 0+(3-1) ≤ (hp n hn).len r .dyn := by rw [len]; omega
private def mid (n : Nat) (hn : n+3 < 2^256) := captureOverwrite (hp n hn) r .dyn r .dyn 0 1 1 (hs n hn) (hd n hn)
private def out (n : Nat) (hn : n+3 < 2^256) := captureTwice (hp n hn) r .dyn 0 1 1 (hs n hn) (hd n hn) 1 3 0 (hu n hn) (he n hn)
private def sv : Source.Data D BoolChildTy := .val (.cdRef rfl 7 0)
private theorem initial (n : Nat) (hn : n+3 < 2^256) : BoolChildRepr (bools (old n)) (fun _ => 7) (hp n hn) sv r := by
  refine ⟨rfl,?_⟩; simp only [MObj.elems_dyn]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- All payload/source and intermediate vectors are derived from actual heap
operations. The recaptured payload differs from its initial-heap counterpart. -/
theorem payloads (n : Nat) (hn : n+3 < 2^256) :
    sliceElems (hp n hn) r .dyn 0 1 = [true] ∧
    MObj.elems .dyn ((mid n hn).get r) = [true,true,false] ++ List.replicate n false ∧
    sliceElems (mid n hn) r .dyn 1 3 = [true,false] ∧
    sliceElems (hp n hn) r .dyn 1 3 = [false,false] := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [sliceElems,MObj.elems_dyn]; rfl
  · dsimp only [mid,captureOverwrite]
    rw [overwriteSlice_elems]; simp only [sliceElems,MObj.elems_dyn]; rfl
  · dsimp only [mid,captureOverwrite,sliceElems]
    rw [overwriteSlice_elems]; simp only [MObj.elems_dyn]; rfl
  · simp only [sliceElems,MObj.elems_dyn]; rfl

theorem criterion (n : Nat) (hn : n+3 < 2^256) :
    LastWriteAgrees (MObj.elems .dyn ((hp n hn).get r)) 1 (sliceElems (hp n hn) r .dyn 0 1) 0 (sliceElems (mid n hn) r .dyn 1 3) := by
  rw [(payloads n hn).1,(payloads n hn).2.2.1]
  constructor
  · intro i hi
    have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases hi' with rfl | rfl <;> simp only [MObj.elems_dyn] <;> rfl
  · intro i hi hx
    change i < 1 at hi
    change 1+i < 0 ∨ 0+2 ≤ 1+i at hx
    omega

/-- Checked execution restores an initially represented child, although its
intermediate representation is false. The second snapshot reads actual mid. -/
theorem actual_restore (n : Nat) (hn : n+3 < 2^256) :
    checkedCaptureOverwrite (hp n hn) r .dyn r .dyn 0 1 1 = some (mid n hn) ∧
    ¬ BoolChildRepr (bools (old n)) (fun _ => 7) (mid n hn) sv r ∧
    checkedCaptureSequence (hp n hn) r .dyn r .dyn 0 1 1 r .dyn r .dyn 1 3 0 = some (hp n hn) ∧
    out n hn = hp n hn ∧ BoolChildRepr (bools (old n)) (fun _ => 7) (out n hn) sv r ∧
    MObj.elems .dyn ((out n hn).get neighbor) = [false,true] := by
  have hc := (checkedCaptureSequence_restore_iff (hp n hn) r .dyn 0 1 1 (hs n hn) (hd n hn) 1 3 0 (hu n hn) (he n hn)).mpr (criterion n hn)
  have ho : out n hn = hp n hn := (captureTwice_restore_iff (hp n hn) r .dyn 0 1 1 (hs n hn) (hd n hn) 1 3 0 (hu n hn) (he n hn)).mpr (criterion n hn)
  refine ⟨checkedCaptureOverwrite_some _ _ _ _ _ _ _ _ (hs n hn) (hd n hn),?_,hc,ho,?_,?_⟩
  · intro hi
    have hx := congrArg (fun obj : MObj H B => (MObj.elems .dyn obj)[1]?) ((initial n hn).object_eq hi)
    rw [(payloads n hn).2.1] at hx
    simp only [MObj.elems_dyn] at hx
    exact (by decide : (some true : Option Bool) ≠ some false) hx
  · rw [ho]; exact initial n hn
  · rw [ho]; simp only [MObj.elems_dyn]; rfl

/-- Freezing the second payload from the initial heap produces a different
result. This refutes replacing ordered recapture with two original snapshots. -/
theorem frozen_negative (n : Nat) (hn : n+3 < 2^256) :
    ∃ (h1 : 1+(sliceElems (hp n hn) r .dyn 0 1).length ≤ (hp n hn).len r .dyn)
      (h2 : 0+(sliceElems (hp n hn) r .dyn 1 3).length ≤ (hp n hn).len r .dyn),
      let frozen := overwriteIntervals (hp n hn) r .dyn 1 (sliceElems (hp n hn) r .dyn 0 1) h1 0 (sliceElems (hp n hn) r .dyn 1 3) h2
      MObj.elems .dyn (frozen.get r) = [false,false,false] ++ List.replicate n false ∧ frozen ≠ out n hn := by
  have h1 : 1+(sliceElems (hp n hn) r .dyn 0 1).length ≤ (hp n hn).len r .dyn := by rw [sliceElems_length _ _ _ (hs n hn)]; exact hd n hn
  have h2 : 0+(sliceElems (hp n hn) r .dyn 1 3).length ≤ (hp n hn).len r .dyn := by rw [sliceElems_length _ _ _ (hu n hn)]; exact he n hn
  refine ⟨h1,h2,?_,?_⟩
  · dsimp only [overwriteIntervals]
    rw [overwriteSlice_elems,overwriteSlice_elems,(payloads n hn).1,(payloads n hn).2.2.2]
    simp only [MObj.elems_dyn]; rfl
  intro ho
  rw [(actual_restore n hn).2.2.2.1] at ho
  have ha := (overwriteIntervals_eq_self_iff _ r .dyn 1 _ h1 0 _ h2).mp ho
  have hx := ha.1 0 (by rw [(payloads n hn).2.2.2]; decide)
  rw [(payloads n hn).2.2.2] at hx
  simp only [MObj.elems_dyn] at hx
  exact (by decide : (some false : Option Bool) ≠ some true) hx

/-- Explicit actual secondSome, complete final child/neighbor observations,
and both branches of the general recaptured-read theorem are inhabited. -/
theorem reached_reads (n : Nat) (hn : n+3 < 2^256) :
    checkedCaptureOverwrite (mid n hn) r .dyn r .dyn 1 3 0 = some (hp n hn) ∧
    MObj.elems .dyn ((out n hn).get r) = old n ∧
    MObj.elems .dyn ((mid n hn).get neighbor) = [false,true] ∧
    (sliceElems (mid n hn) r .dyn 1 3)[0]? = (MObj.elems .dyn ((hp n hn).get r))[0]? ∧
    (sliceElems (mid n hn) r .dyn 1 3)[1]? = (MObj.elems .dyn ((hp n hn).get r))[2]? := by
  have hm : SliceBounds ((mid n hn).len r .dyn) 1 3 := by
    simpa only [mid,captureOverwrite_all_len] using hu n hn
  have hd' : 0+(3-1) ≤ (mid n hn).len r .dyn := by
    simpa only [mid,captureOverwrite_all_len] using he n hn
  have hc := checkedCaptureOverwrite_some (mid n hn) r .dyn r .dyn 1 3 0 hm hd'
  change checkedCaptureOverwrite (mid n hn) r .dyn r .dyn 1 3 0 = some (out n hn) at hc
  have ho := (actual_restore n hn).2.2.2.1
  rw [ho] at hc
  refine ⟨hc,?_,?_,?_,?_⟩
  · rw [ho]; simp only [MObj.elems_dyn]; rfl
  · dsimp only [mid,captureOverwrite]
    rw [overwriteSlice_frame _ r neighbor .dyn 1 _ _ (by decide)]
    simp only [MObj.elems_dyn]; rfl
  · have hr := recapturedPayload_read (hp n hn) r .dyn 0 1 1 (hs n hn) (hd n hn) 1 3 (hu n hn) 0 (by decide)
    rw [ite_eq_left (by decide)] at hr
    simpa only [mid,Nat.reduceAdd,Nat.reduceSub,Nat.add_zero] using hr
  · have hr := recapturedPayload_read (hp n hn) r .dyn 0 1 1 (hs n hn) (hd n hn) 1 3 (hu n hn) 1 (by decide)
    rw [ite_eq_right (by decide)] at hr
    simpa only [mid,Nat.reduceAdd,Nat.reduceSub,Nat.add_zero] using hr

/-- info: 'Solidity.Backend.MemoryOps.RecaptureControls.reached_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reached_reads
/-- info: 'Solidity.Backend.MemoryOps.RecaptureControls.payloads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms payloads
/-- info: 'Solidity.Backend.MemoryOps.RecaptureControls.criterion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms criterion
/-- info: 'Solidity.Backend.MemoryOps.RecaptureControls.actual_restore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms actual_restore
/-- info: 'Solidity.Backend.MemoryOps.RecaptureControls.frozen_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms frozen_negative
end RecaptureControls
/-- info: 'Solidity.Backend.MemoryOps.recapturedPayload_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms recapturedPayload_read
/-- info: 'Solidity.Backend.MemoryOps.captureTwice_restore_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms captureTwice_restore_iff
/-- info: 'Solidity.Backend.MemoryOps.checkedCaptureSequence_restore_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms checkedCaptureSequence_restore_iff
end Solidity.Backend.MemoryOps
