import Solidity.Backend.MemoryOps.RecaptureRestoration

/-! Finite List/Option composition of existing checkedCaptureOverwrite calls.
Each triple is exactly its existing (start,stop,destination) arguments on ONE
existing intrinsic array. No AST, copy evaluator, fresh allocation or public
schedule-length limit is introduced. Failure has no suffix heap or rollback. -/
namespace Solidity.Backend.MemoryOps

abbrev SnapshotArgs := Nat × Nat × Nat

def runCaptures {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) : List SnapshotArgs → Option (Heap H)
  | [] => some hp
  | x::xs => (checkedCaptureOverwrite hp r a r a x.1 x.2.1 x.2.2).bind
      (fun mid => runCaptures mid r a xs)

def SnapshotArgs.Valid (size : Nat) (x : SnapshotArgs) : Prop :=
  x.1 ≤ x.2.1 ∧ x.2.1 ≤ size ∧ x.2.2+(x.2.1-x.1) ≤ size

def CapturesValid (size : Nat) (xs : List SnapshotArgs) : Prop :=
  ∀ x ∈ xs, SnapshotArgs.Valid size x

theorem runCaptures_cons_some {H : HTy} {R : RefTy} {E : Ty}
    (hp out : Heap H) (r : HRef H R) (a : ArrTy R E) (x : SnapshotArgs) (xs : List SnapshotArgs) :
    runCaptures hp r a (x::xs) = some out ↔
      ∃ mid, checkedCaptureOverwrite hp r a r a x.1 x.2.1 x.2.2 = some mid ∧ runCaptures mid r a xs = some out :=
  Option.bind_eq_some_iff

theorem runCaptures_append {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (xs ys : List SnapshotArgs) :
    runCaptures hp r a (xs++ys) = (runCaptures hp r a xs).bind (fun mid => runCaptures mid r a ys) := by
  induction xs generalizing hp with
  | nil => rfl
  | cons x xs ih =>
    cases hf : checkedCaptureOverwrite hp r a r a x.1 x.2.1 x.2.2 with
    | none => simp only [List.cons_append,runCaptures,hf,Option.bind_none]
    | some mid =>
      simp only [List.cons_append,runCaptures,hf,Option.bind_some]
      exact ih mid

theorem runCaptures_split_some {H : HTy} {R : RefTy} {E : Ty}
    (hp out : Heap H) (r : HRef H R) (a : ArrTy R E) (xs ys : List SnapshotArgs) :
    runCaptures hp r a (xs++ys) = some out ↔
      ∃ mid, runCaptures hp r a xs = some mid ∧ runCaptures mid r a ys = some out := by
  rw [runCaptures_append]
  exact Option.bind_eq_some_iff

theorem runCaptures_all_len {H : HTy} {R Q : RefTy} {E F : Ty}
    (hp out : Heap H) (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs)
    (ho : runCaptures hp r a xs = some out) (q : HRef H Q) (b : ArrTy Q F) :
    out.len q b = hp.len q b := by
  induction xs generalizing hp with
  | nil => have he := Option.some.inj ho; subst out; rfl
  | cons x xs ih =>
    obtain ⟨mid,hf,ht⟩ := (runCaptures_cons_some hp out r a x xs).mp ho
    rw [ih mid ht]
    obtain ⟨hs,hd,rfl⟩ := (checkedCaptureOverwrite_some_iff hp r a r a x.1 x.2.1 x.2.2 mid).mp hf
    exact captureOverwrite_all_len hp r a r a _ _ _ hs hd q b

theorem runCaptures_frame {H : HTy} {R Q : RefTy} {E : Ty}
    (hp out : Heap H) (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs)
    (ho : runCaptures hp r a xs = some out) (q : HRef H Q) (hne : r.id ≠ q.id) : out.get q = hp.get q := by
  induction xs generalizing hp with
  | nil => have he := Option.some.inj ho; subst out; rfl
  | cons x xs ih =>
    obtain ⟨mid,hf,ht⟩ := (runCaptures_cons_some hp out r a x xs).mp ho
    exact (ih mid ht).trans (checkedCaptureOverwrite_frame hp r a r a _ _ _ mid hf q hne)

/-- Original bounds suffice for every reached operation because all lengths
are derived unchanged. This is a checkable input certificate, not a run relation. -/
theorem runCaptures_success_iff {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs) :
    (∃ out, runCaptures hp r a xs = some out) ↔ CapturesValid (hp.len r a) xs := by
  induction xs generalizing hp with
  | nil =>
    constructor
    · intro _ x hx
      cases hx
    · intro _
      exact ⟨hp,rfl⟩
  | cons x xs ih =>
    constructor
    · rintro ⟨out,ho⟩
      obtain ⟨mid,hf,ht⟩ := (runCaptures_cons_some hp out r a x xs).mp ho
      obtain ⟨hs,hd,hm⟩ := (checkedCaptureOverwrite_some_iff hp r a r a x.1 x.2.1 x.2.2 mid).mp hf
      have hl : mid.len r a = hp.len r a := by rw [hm,captureOverwrite_all_len]
      have hv := (ih mid).mp ⟨out,ht⟩
      rw [hl] at hv
      intro y hy
      rcases List.mem_cons.mp hy with he | hy
      · subst y; exact ⟨hs.ordered,hs.bounded,hd⟩
      · exact hv y hy
    · intro hv
      have hx := hv x (List.mem_cons_self)
      let mid := captureOverwrite hp r a r a x.1 x.2.1 x.2.2 ⟨hx.1,hx.2.1⟩ hx.2.2
      have hf : checkedCaptureOverwrite hp r a r a x.1 x.2.1 x.2.2 = some mid :=
        checkedCaptureOverwrite_some _ _ _ _ _ _ _ _ ⟨hx.1,hx.2.1⟩ hx.2.2
      have ht : CapturesValid (mid.len r a) xs := by
        rw [captureOverwrite_all_len]
        intro y hy
        exact hv y (List.mem_cons_of_mem x hy)
      obtain ⟨out,ho⟩ := (ih mid).mpr ht
      exact ⟨out,(runCaptures_cons_some hp out r a x xs).mpr ⟨mid,hf,ho⟩⟩

/-- Exact failure exposes a real successful prefix and the FIRST invalid
reached call. No state for the unexecuted suffix is invented. -/
theorem runCaptures_none_first {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs) :
    runCaptures hp r a xs = none ↔
      ∃ pre x post mid, xs = pre++x::post ∧ runCaptures hp r a pre = some mid ∧
        checkedCaptureOverwrite mid r a r a x.1 x.2.1 x.2.2 = none := by
  constructor
  · intro ho
    induction xs generalizing hp with
    | nil => cases ho
    | cons x xs ih =>
      cases hf : checkedCaptureOverwrite hp r a r a x.1 x.2.1 x.2.2 with
      | none => exact ⟨[],x,xs,hp,rfl,rfl,hf⟩
      | some mid =>
        have ht : runCaptures mid r a xs = none := by simpa only [runCaptures,hf,Option.bind_some] using ho
        obtain ⟨pre,y,post,last,he,hpre,hbad⟩ := ih mid ht
        refine ⟨x::pre,y,post,last,?_,?_,hbad⟩
        · rw [List.cons_append,he]
        · exact (runCaptures_cons_some hp last r a x pre).mpr ⟨mid,hf,hpre⟩
  · rintro ⟨pre,x,post,mid,rfl,hpre,hbad⟩
    rw [runCaptures_append,hpre]
    simp only [Option.bind_some,runCaptures,hbad,Option.bind_none]

theorem runCaptures_reached {H : HTy} {R : RefTy} {E : Ty}
    (hp out : Heap H) (r : HRef H R) (a : ArrTy R E) (pre post : List SnapshotArgs) (x : SnapshotArgs)
    (ho : runCaptures hp r a (pre++x::post) = some out) :
    ∃ before after, runCaptures hp r a pre = some before ∧
      checkedCaptureOverwrite before r a r a x.1 x.2.1 x.2.2 = some after ∧ runCaptures after r a post = some out := by
  obtain ⟨before,hpre,ht⟩ := (runCaptures_split_some hp out r a pre (x::post)).mp ho
  obtain ⟨after,hstep,hpost⟩ := (runCaptures_cons_some before out r a x post).mp ht
  exact ⟨before,after,hpre,hstep,hpost⟩

theorem runCaptures_two {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (s t d u v f : Nat) :
    runCaptures hp r a [(s,t,d),(u,v,f)] = checkedCaptureSequence hp r a r a s t d r a r a u v f := by
  cases hf : checkedCaptureOverwrite hp r a r a s t d with
  | none => simp only [runCaptures,checkedCaptureSequence,hf,Option.bind_none]
  | some mid =>
    cases hs : checkedCaptureOverwrite mid r a r a u v f <;>
      simp only [runCaptures,checkedCaptureSequence,hf,hs,Option.bind_some,Option.bind_none]

theorem runCaptures_none_iff {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs) :
    runCaptures hp r a xs = none ↔ ¬ CapturesValid (hp.len r a) xs := by
  constructor
  · intro ho hv
    obtain ⟨out,hs⟩ := (runCaptures_success_iff hp r a xs).mpr hv
    rw [ho] at hs
    cases hs
  · intro hv
    cases ho : runCaptures hp r a xs with
    | none => rfl
    | some out => exact (hv ((runCaptures_success_iff hp r a xs).mp ⟨out,ho⟩)).elim

theorem runCaptures_associative {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (xs ys zs : List SnapshotArgs) :
    ((runCaptures hp r a xs).bind (fun mid => runCaptures mid r a ys)).bind (fun mid => runCaptures mid r a zs) =
      (runCaptures hp r a xs).bind (fun mid => (runCaptures mid r a ys).bind (fun last => runCaptures last r a zs)) := by
  cases hx : runCaptures hp r a xs with
  | none => rfl
  | some mid => cases hy : runCaptures mid r a ys <;> rfl

theorem runCaptures_singleton {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (x : SnapshotArgs) :
    runCaptures hp r a [x] = checkedCaptureOverwrite hp r a r a x.1 x.2.1 x.2.2 := by
  cases hf : checkedCaptureOverwrite hp r a r a x.1 x.2.1 x.2.2 <;>
    simp only [runCaptures,hf,Option.bind_some,Option.bind_none]

/-- The same first reached failure is exactly a valid original-bounds prefix
followed by an invalid original-bounds step. Length transport is derived. -/
theorem runCaptures_none_bounds {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs) :
    runCaptures hp r a xs = none ↔ ∃ pre x post,
      xs = pre++x::post ∧ CapturesValid (hp.len r a) pre ∧ ¬ SnapshotArgs.Valid (hp.len r a) x := by
  constructor
  · intro ho
    obtain ⟨pre,x,post,mid,he,hpre,hbad⟩ := (runCaptures_none_first hp r a xs).mp ho
    have hl := runCaptures_all_len hp mid r a pre hpre r a
    refine ⟨pre,x,post,he,(runCaptures_success_iff hp r a pre).mp ⟨mid,hpre⟩,?_⟩
    intro hx
    have hs : SliceBounds (mid.len r a) x.1 x.2.1 := ⟨hx.1,by rw [hl]; exact hx.2.1⟩
    have hd : x.2.2+(x.2.1-x.1) ≤ mid.len r a := by rw [hl]; exact hx.2.2
    have hc := checkedCaptureOverwrite_some mid r a r a x.1 x.2.1 x.2.2 hs hd
    rw [hbad] at hc
    cases hc
  · rintro ⟨pre,x,post,he,hvalid,hbad⟩
    obtain ⟨mid,hpre⟩ := (runCaptures_success_iff hp r a pre).mpr hvalid
    have hl := runCaptures_all_len hp mid r a pre hpre r a
    have hf : checkedCaptureOverwrite mid r a r a x.1 x.2.1 x.2.2 = none := by
      apply (checkedCaptureOverwrite_none_iff _ _ _ _ _ _ _ _).mpr
      rw [hl]
      unfold SnapshotArgs.Valid at hbad
      omega
    exact (runCaptures_none_first hp r a xs).mpr ⟨pre,x,post,mid,he,hpre,hf⟩

/-- info: 'Solidity.Backend.MemoryOps.runCaptures_none_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_none_bounds
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_none_iff
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_associative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_associative
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_singleton
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_cons_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_cons_some
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_append
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_split_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_split_some
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_all_len' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_all_len
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_frame
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_success_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_success_iff
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_none_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_none_first
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_reached' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_reached
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runCaptures_two
end Solidity.Backend.MemoryOps
