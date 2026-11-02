import Solidity.Backend.MemoryOps.SnapshotProvenance

/-! DRAFT / UNVALIDATED. Arbitrary finite schedules on distinct logical typed
objects commute, although every source is recaptured from its actual reached
heap. Only existing runCaptures, Heap and MPath are used. Reference elements
may share descendant identities. Separation is a local theorem case, not a
Source admission restriction. Option equality does not equate failure traces,
retain a heap after None, or prove Source/target/byte-memory execution. -/
namespace Solidity.Backend.MemoryOps

/-- Actual successful schedules preserve all array lengths, hence the exact
rejection guard of another schedule, even if the identities happen to alias. -/
theorem runCaptures_none_after_run {H : HTy} {R Q : RefTy} {E F : Ty}
    (hp mid : Heap H) (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs)
    (q : HRef H Q) (b : ArrTy Q F) (ys : List SnapshotArgs)
    (hq : runCaptures hp q b ys=some mid) :
    runCaptures mid r a xs=none ↔ runCaptures hp r a xs=none := by
  simp only [runCaptures_none_iff,runCaptures_all_len hp mid q b ys hq r a]

/-- Initial selected-object equality derives final selected-object equality
for two actual executions of the SAME schedule. It is not an assumed final
relation or a replacement copy evaluator. Other objects may differ initially. -/
theorem runCaptures_target_eq_of_input_eq {H : HTy} {R : RefTy} {E : Ty}
    (hp hq out out' : Heap H) (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs)
    (hin : hp.get r=hq.get r)
    (ho : runCaptures hp r a xs=some out) (ho' : runCaptures hq r a xs=some out') :
    out.get r=out'.get r := by
  have hv : MObj.elems a (out.get r)=MObj.elems a (out'.get r) := by
    apply List.ext_getElem?
    intro k
    rw [runCaptures_read hp out r a xs ho k,runCaptures_read hq out' r a xs ho' k,hin]
  cases a <;> apply Subtype.ext <;> simpa only [MObj.elems_dyn,MObj.elems_fixed] using hv

/-- Equality of actual serial outputs. Initial object frame facts discharge
all input-equality clauses; captured payloads are never frozen globally. -/
theorem runCaptures_disjoint_outputs_eq {H : HTy} {R Q : RefTy} {E F : Ty}
    (hp mr mq left right : Heap H)
    (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs)
    (q : HRef H Q) (b : ArrTy Q F) (ys : List SnapshotArgs)
    (hne : r.id≠q.id)
    (hr : runCaptures hp r a xs=some mr) (hq : runCaptures hp q b ys=some mq)
    (hl : runCaptures mr q b ys=some left) (ht : runCaptures mq r a xs=some right) :
    left=right := by
  have her : mr.get r=right.get r :=
    runCaptures_target_eq_of_input_eq hp mq mr right r a xs
      (runCaptures_frame hp mq q b ys hq r hne.symm).symm hr ht
  have heq : mq.get q=left.get q :=
    runCaptures_target_eq_of_input_eq hp mr mq left q b ys
      (runCaptures_frame hp mr r a xs hr q hne).symm hq hl
  apply memoryOps_heap_ext
  intro T t
  by_cases hrt : r.id=t.id
  · obtain ⟨rfl,he⟩ := HRef.heq_of_id r t hrt
    cases he
    exact (runCaptures_frame mr left q b ys hl r hne.symm).trans her
  · by_cases hqt : q.id=t.id
    · obtain ⟨rfl,he⟩ := HRef.heq_of_id q t hqt
      cases he
      exact heq.symm.trans (runCaptures_frame mq right r a xs ht q hne).symm
    · calc
        left.get t=mr.get t := runCaptures_frame mr left q b ys hl t hqt
        _=hp.get t := runCaptures_frame hp mr r a xs hr t hrt
        _=mq.get t := (runCaptures_frame hp mq q b ys hq t hqt).symm
        _=right.get t := (runCaptures_frame mq right r a xs ht t hrt).symm

/-- Complete Option equality, including rejection. When either schedule is
invalid, both serial Option results are None. Their reached failure histories
can differ; no equality of histories or post-rejection heaps is asserted. -/
theorem runCaptures_disjoint_comm {H : HTy} {R Q : RefTy} {E F : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs)
    (q : HRef H Q) (b : ArrTy Q F) (ys : List SnapshotArgs) (hne : r.id≠q.id) :
    (runCaptures hp r a xs).bind (fun mid => runCaptures mid q b ys)=
      (runCaptures hp q b ys).bind (fun mid => runCaptures mid r a xs) := by
  cases hr : runCaptures hp r a xs with
  | none =>
    cases hq : runCaptures hp q b ys with
    | none => simp only [Option.bind_none]
    | some mq =>
      have hf : runCaptures mq r a xs=none := (runCaptures_none_after_run hp mq r a xs q b ys hq).mpr hr
      simp only [hf,Option.bind_none,Option.bind_some]
  | some mr =>
    cases hq : runCaptures hp q b ys with
    | none =>
      have hf : runCaptures mr q b ys=none := (runCaptures_none_after_run hp mr q b ys r a xs hr).mpr hq
      simp only [hf,Option.bind_none,Option.bind_some]
    | some mq =>
      have hvr : CapturesValid (hp.len r a) xs := (runCaptures_success_iff hp r a xs).mp ⟨mr,hr⟩
      have hvq : CapturesValid (hp.len q b) ys := (runCaptures_success_iff hp q b ys).mp ⟨mq,hq⟩
      have hvr' : CapturesValid (mq.len r a) xs := by
        rw [runCaptures_all_len hp mq q b ys hq r a];exact hvr
      have hvq' : CapturesValid (mr.len q b) ys := by
        rw [runCaptures_all_len hp mr r a xs hr q b];exact hvq
      obtain ⟨left,hl⟩ := (runCaptures_success_iff mr q b ys).mpr hvq'
      obtain ⟨right,ht⟩ := (runCaptures_success_iff mq r a xs).mpr hvr'
      have he : left=right := runCaptures_disjoint_outputs_eq hp mr mq left right r a xs q b ys hne hr hq hl ht
      simp only [hl,ht,Option.bind_some]
      exact congrArg some he

/-- Input bounds derive all four actual runs and a common final heap. Every
selected read comes from its INITIAL object's computed backwards provenance;
all other typed objects are framed. Runtime lengths/counts are uncapped. -/
theorem runCaptures_disjoint_success {H : HTy} {R Q : RefTy} {E F : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (xs : List SnapshotArgs)
    (q : HRef H Q) (b : ArrTy Q F) (ys : List SnapshotArgs) (hne : r.id≠q.id)
    (hvr : CapturesValid (hp.len r a) xs) (hvq : CapturesValid (hp.len q b) ys) :
    ∃ mr mq out,
      runCaptures hp r a xs=some mr ∧ runCaptures hp q b ys=some mq ∧
      runCaptures mr q b ys=some out ∧ runCaptures mq r a xs=some out ∧
      (∀ k,(MObj.elems a (out.get r))[k]?=(MObj.elems a (hp.get r))[captureOrigin xs k]?) ∧
      (∀ k,(MObj.elems b (out.get q))[k]?=(MObj.elems b (hp.get q))[captureOrigin ys k]?) ∧
      (∀ {T : RefTy} (t : HRef H T),r.id≠t.id → q.id≠t.id → out.get t=hp.get t) := by
  obtain ⟨mr,hr⟩ := (runCaptures_success_iff hp r a xs).mpr hvr
  obtain ⟨mq,hq⟩ := (runCaptures_success_iff hp q b ys).mpr hvq
  have hvq' : CapturesValid (mr.len q b) ys := by
    rw [runCaptures_all_len hp mr r a xs hr q b];exact hvq
  obtain ⟨out,hl⟩ := (runCaptures_success_iff mr q b ys).mpr hvq'
  have hcomm : (runCaptures hp r a xs).bind (fun mid => runCaptures mid q b ys) =
      (runCaptures hp q b ys).bind (fun mid => runCaptures mid r a xs) := runCaptures_disjoint_comm hp r a xs q b ys hne
  rw [hr,hq,Option.bind_some,Option.bind_some,hl] at hcomm
  have ht : runCaptures mq r a xs=some out := hcomm.symm
  refine ⟨mr,mq,out,hr,hq,hl,ht,?_,?_,?_⟩
  · intro k
    rw [runCaptures_frame mr out q b ys hl r hne.symm]
    exact runCaptures_read hp mr r a xs hr k
  · intro k
    rw [runCaptures_read mr out q b ys hl k,runCaptures_frame hp mr r a xs hr q hne]
  · intro T t hrt hqt
    exact (runCaptures_frame mr out q b ys hl t hqt).trans (runCaptures_frame hp mr r a xs hr t hrt)

/-- Any existing typed path observes the same successful common heap, including
reference-valued paths and failures; no second path evaluator is defined. -/
theorem runCaptures_disjoint_path {C : Contract} {Γ : Ctx} {R Q : RefTy} {E F T : Ty}
    (σ : State C Γ) (r : HRef σ.H R) (a : ArrTy R E) (xs : List SnapshotArgs)
    (q : HRef σ.H Q) (b : ArrTy Q F) (ys : List SnapshotArgs) (hne : r.id≠q.id)
    (mr mq left right : Heap σ.H)
    (hr : runCaptures σ.heap r a xs=some mr) (hq : runCaptures σ.heap q b ys=some mq)
    (hl : runCaptures mr q b ys=some left) (ht : runCaptures mq r a xs=some right)
    (path : MPath C Γ T) :
    path.mvalT (σ.withHeap left)=path.mvalT (σ.withHeap right) := by
  rw [runCaptures_disjoint_outputs_eq σ.heap mr mq left right r a xs q b ys hne hr hq hl ht]

/- Expected pins below are UNVALIDATED, not actual output. -/
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_none_after_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runCaptures_none_after_run
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_target_eq_of_input_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runCaptures_target_eq_of_input_eq
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_disjoint_outputs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runCaptures_disjoint_outputs_eq
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_disjoint_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runCaptures_disjoint_comm
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_disjoint_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runCaptures_disjoint_success
/-- info: 'Solidity.Backend.MemoryOps.runCaptures_disjoint_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runCaptures_disjoint_path
end Solidity.Backend.MemoryOps
