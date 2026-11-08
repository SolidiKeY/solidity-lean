import Solidity.Backend.MemoryOps.CopyMirrorFrame
import Solidity.Backend.MemoryOps.SnapshotScheduleGrowth

/-! Arbitrary finite reached-heap schedules preserve published recursive
mirrors when their destination is older than every mirrored node. This derives
operation frames, not a second traversal or copy implementation. -/
namespace Solidity.Backend.MemoryOps

theorem runCaptures_mirrors {H : HTy} {R : RefTy} {E T : Ty} {n : Nat}
    (hp out : Heap H) (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs)
    (ho : runCaptures hp r a xs=some out) (hn : r.id < n)
    (sv : SVal T) (val : MVal H T) (hm : sv.Mirrors hp n val) : sv.Mirrors out n val :=
  mirrors_frame (fun q hq => runCaptures_frame hp out r a xs ho q
    (Nat.ne_of_lt (Nat.lt_of_lt_of_le hn hq))) sv val hm

theorem copy_schedule_mirrors {H : HTy} {R A : RefTy} {E : Ty}
    (hp : Heap H) (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree=true)
    (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs)
    (out : Heap (sv.copyStToM hp hm).H')
    (ho : runCaptures (sv.copyStToM hp hm).heap (r.wk (sv.copyStToM hp hm).ext) a xs=some out) :
    sv.Mirrors out H.length (sv.copyStToM hp hm).val :=
  runCaptures_mirrors _ out _ a xs ho r.id_lt sv _ (SVal.mirrors_copyStToM hp sv hm)

theorem default_schedule_mirrors {H : HTy} {R A : RefTy} {E : Ty}
    (hp : Heap H) (hm : (Ty.ref A).mapFree=true) (r : HRef H R) (a : ArrTy R E)
    (xs : List SnapshotArgs) (out : Heap (hp.allocDefault A hm).H')
    (ho : runCaptures (hp.allocDefault A hm).heap (r.wk (hp.allocDefault A hm).ext) a xs=some out) :
    (SVal.dflt (.ref A)).Mirrors out H.length (hp.allocDefault A hm).val :=
  copy_schedule_mirrors hp (SVal.dflt (.ref A)) hm r a xs out ho

/-- Actual successful old run is lifted through the real recursive builder.
Keeps relates its reached output, not a frozen original payload. -/
theorem copy_schedule_transport {H : HTy} {R A : RefTy} {E : Ty}
    (hp out : Heap H) (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree=true)
    (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs)
    (ho : runCaptures hp r a xs=some out) :
    let g := sv.copyStToM hp hm
    ∃ out', runCaptures g.heap (r.wk g.ext) a xs=some out' ∧ Heap.Keeps g.ext out out' ∧
      sv.Mirrors out' H.length g.val ∧
      ∀ {Q : RefTy} (q : HRef g.H' Q), H.length ≤ q.id → out'.get q=g.heap.get q := by
  dsimp only
  obtain ⟨out',ho',hk⟩ := runCaptures_keeps _ (SVal.keeps_copyStToM sv hm hp) r a xs out ho
  exact ⟨out',ho',hk,copy_schedule_mirrors hp sv hm r a xs out' ho',
    fun q hq => runCaptures_frame _ _ _ _ _ ho' q (Nat.ne_of_lt (Nat.lt_of_lt_of_le r.id_lt hq))⟩

/-- Exact reached-prefix failure also lifts through the real builder. There is
no output heap for the unexecuted failing suffix. -/
theorem copy_schedule_none_first {H : HTy} {R A : RefTy} {E : Ty}
    (hp : Heap H) (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree=true)
    (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs) :
    let g := sv.copyStToM hp hm
    runCaptures g.heap (r.wk g.ext) a xs=none ↔
      ∃ pre x post mid, xs=pre++x::post ∧ runCaptures g.heap (r.wk g.ext) a pre=some mid ∧
        checkedCaptureOverwrite mid (r.wk g.ext) a (r.wk g.ext) a x.1 x.2.1 x.2.2=none ∧
        sv.Mirrors mid H.length g.val := by
  dsimp only
  constructor
  · intro hf
    obtain ⟨pre,x,post,mid,he,hpre,hbad⟩ := (runCaptures_none_first _ _ _ _).mp hf
    exact ⟨pre,x,post,mid,he,hpre,hbad,copy_schedule_mirrors hp sv hm r a pre mid hpre⟩
  · rintro ⟨pre,x,post,mid,he,hpre,hbad,_⟩
    exact (runCaptures_none_first _ _ _ _).mpr ⟨pre,x,post,mid,he,hpre,hbad⟩

/-- Two actual recursive builders, with arbitrary successful old-root tails
between and after them. Both recursive mirrors survive the second tail. -/
theorem two_builder_schedules_mirrors {H : HTy} {R A B : RefTy} {E : Ty}
    (hp : Heap H) (sv : SVal (.ref A)) (hm : (Ty.ref A).mapFree=true)
    (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs)
    (mid : Heap (sv.copyStToM hp hm).H')
    (hmid : runCaptures (sv.copyStToM hp hm).heap (r.wk (sv.copyStToM hp hm).ext) a xs=some mid)
    (sv' : SVal (.ref B)) (hm' : (Ty.ref B).mapFree=true) (ys : List SnapshotArgs)
    (out : Heap (sv'.copyStToM mid hm').H')
    (ho : runCaptures (sv'.copyStToM mid hm').heap
      ((r.wk (sv.copyStToM hp hm).ext).wk (sv'.copyStToM mid hm').ext) a ys=some out) :
    sv.Mirrors out H.length (MVal.wk (sv'.copyStToM mid hm').ext (.ref A) (sv.copyStToM hp hm).val) ∧
    sv'.Mirrors out (sv.copyStToM hp hm).H'.length (sv'.copyStToM mid hm').val := by
  have first := copy_schedule_mirrors hp sv hm r a xs mid hmid
  have grown := SVal.Mirrors.wk (SVal.keeps_copyStToM sv' hm' mid) sv _ first
  exact ⟨runCaptures_mirrors _ _ _ _ _ ho r.id_lt sv _ grown,
    copy_schedule_mirrors mid sv' hm' (r.wk (sv.copyStToM hp hm).ext) a ys out ho⟩
/-- Runtime repetition of an exact-end empty operation is an executed identity. -/
theorem runCaptures_end_replicate {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (k copies : Nat) (hk : hp.len r a=k) :
    runCaptures hp r a (List.replicate copies (k,k,k))=some hp := by
  induction copies with
  | zero => rfl
  | succ copies ih =>
    rw [List.replicate_succ,runCaptures,
      checkedCaptureOverwrite_empty hp r a r a k k (by rw [hk]; exact Nat.le_refl _) (by rw [hk]; exact Nat.le_refl _),Option.bind_some]
    exact ih

/-- info: 'Solidity.Backend.MemoryOps.runCaptures_mirrors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_mirrors
/-- info: 'Solidity.Backend.MemoryOps.copy_schedule_mirrors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_schedule_mirrors
/-- info: 'Solidity.Backend.MemoryOps.default_schedule_mirrors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms default_schedule_mirrors
/-- info: 'Solidity.Backend.MemoryOps.copy_schedule_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_schedule_transport
/-- info: 'Solidity.Backend.MemoryOps.copy_schedule_none_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_schedule_none_first
/-- info: 'Solidity.Backend.MemoryOps.two_builder_schedules_mirrors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms two_builder_schedules_mirrors
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_end_replicate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_end_replicate
end Solidity.Backend.MemoryOps
