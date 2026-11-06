import Solidity.Backend.MemoryCopies.SourceCopyHorizonInterface

/-! Generic preservation for existing storage-copy traversals under added fuel.
Only timeout may be replaced by a later observation. No Source operation changes. -/
namespace Solidity.Backend.MemoryCopies
variable {E : Source.Env} {Γ : Source.RCtx}

theorem CopyHorizonExtends.refl {α : Type} (operation : Source.EM E Γ α) : CopyHorizonExtends operation operation :=
  fun _ _ => rfl

theorem CopyHorizonExtends.timeout {α : Type} (upper : Source.EM E Γ α) :
    CopyHorizonExtends (Source.EM.halt .timeout) upper := by
  intro before finished
  exact False.elim (finished rfl)

theorem CopyHorizonExtends.bind {α β : Type} {lower upper : Source.EM E Γ α}
    {first last : α → Source.EM E Γ β} (head : CopyHorizonExtends lower upper)
    (tail : ∀ value, CopyHorizonExtends (first value) (last value)) :
    CopyHorizonExtends (lower >>= first) (upper >>= last) := by
  intro before finished
  simp only [Source.Hoare.run_bind] at finished ⊢
  rcases step : lower.run before with ⟨result,middle⟩
  cases result with
  | ok value =>
    have notTimeout : (lower.run before).1 ≠ .error .timeout := by
      rw [step]
      intro impossible
      cases impossible
    have same : upper.run before = (.ok value,middle) := (head before notTimeout).trans step
    rw [same]
    apply tail value middle
    simpa only [step] using finished
  | error halt =>
    have notTimeout : (lower.run before).1 ≠ .error .timeout := by
      intro impossible
      have timed : halt = .timeout := Except.error.inj (by simpa only [step] using impossible)
      apply finished
      rw [step,timed]
    rw [head before notTimeout,step]

theorem CopyHorizonExtends.success {α : Type} {lower upper : Source.EM E Γ α}
    (extension : CopyHorizonExtends lower upper) (before after : Source.EMState E Γ) (value : α)
    (execution : lower.run before = (.ok value,after)) : upper.run before = (.ok value,after) := by
  have finished : (lower.run before).1 ≠ .error .timeout := by
    rw [execution]
    intro impossible
    cases impossible
  exact (extension before finished).trans execution

mutual

theorem loadMem_horizon (frame : Source.Fr) : ∀ (fuel slack : Nat) (type : Source.STy) (path : Source.SPath),
    CopyHorizonExtends (Source.loadMem (E := E) (Γ := Γ) frame fuel type path)
      (Source.loadMem frame (fuel + slack) type path)
  | 0, slack, type, path => CopyHorizonExtends.timeout _
  | fuel + 1, slack, type, path => by
    have budget : fuel + 1 + slack = (fuel + slack) + 1 := by omega
    rw [budget]
    simp only [Source.loadMem]
    split
    · exact CopyHorizonExtends.bind (.refl _) (fun length =>
        .bind (loadBytes_horizon frame fuel slack path 0 length) (fun _ => .refl _))
    · exact CopyHorizonExtends.bind (.refl _) (fun length =>
        .bind (loadBytes_horizon frame fuel slack path 0 length) (fun _ => .refl _))
    · exact CopyHorizonExtends.bind (.refl _) (fun length =>
        .bind (loadElems_horizon frame fuel slack _ path 0 length) (fun _ => .refl _))
    · exact CopyHorizonExtends.bind (loadElems_horizon frame fuel slack _ path 0 _) (fun _ => .refl _)
    · exact CopyHorizonExtends.bind (loadFields_horizon frame fuel slack _ path 0) (fun _ => .refl _)
    · exact CopyHorizonExtends.refl _
    · exact CopyHorizonExtends.bind (.refl _) (fun _ => .refl _)

theorem loadElem_horizon (frame : Source.Fr) : ∀ (fuel slack : Nat) (type : Source.STy) (path : Source.SPath),
    CopyHorizonExtends (Source.loadElem (E := E) (Γ := Γ) frame fuel type path)
      (Source.loadElem frame (fuel + slack) type path)
  | 0, slack, type, path => CopyHorizonExtends.timeout _
  | fuel + 1, slack, type, path => by
    have budget : fuel + 1 + slack = (fuel + slack) + 1 := by omega
    rw [budget]
    simp only [Source.loadElem]
    split
    · exact CopyHorizonExtends.bind (loadMem_horizon frame fuel slack type path) (fun _ => .refl _)
    · exact CopyHorizonExtends.refl _

theorem loadElems_horizon (frame : Source.Fr) :
    ∀ (fuel slack : Nat) (type : Source.STy) (path : Source.SPath) (start count : Nat),
    CopyHorizonExtends (Source.loadElems (E := E) (Γ := Γ) frame fuel type path start count)
      (Source.loadElems frame (fuel + slack) type path start count)
  | 0, slack, type, path, start, count => by cases count <;> exact CopyHorizonExtends.timeout _
  | fuel + 1, slack, type, path, start, 0 => by
    have budget : fuel + 1 + slack = (fuel + slack) + 1 := by omega
    rw [budget]
    exact CopyHorizonExtends.refl _
  | fuel + 1, slack, type, path, start, count + 1 => by
    have budget : fuel + 1 + slack = (fuel + slack) + 1 := by omega
    rw [budget]
    exact CopyHorizonExtends.bind (loadElem_horizon frame fuel slack type _) (fun _ =>
      .bind (loadElems_horizon frame fuel slack type path (start + 1) count) (fun _ => .refl _))

theorem loadFields_horizon (frame : Source.Fr) :
    ∀ (fuel slack : Nat) (types : List Source.STy) (path : Source.SPath) (start : Nat),
    CopyHorizonExtends (Source.loadFields (E := E) (Γ := Γ) frame fuel types path start)
      (Source.loadFields frame (fuel + slack) types path start)
  | 0, slack, types, path, start => by cases types <;> exact CopyHorizonExtends.timeout _
  | fuel + 1, slack, [], path, start => by
    have budget : fuel + 1 + slack = (fuel + slack) + 1 := by omega
    rw [budget]
    exact CopyHorizonExtends.refl _
  | fuel + 1, slack, type :: types, path, start => by
    have budget : fuel + 1 + slack = (fuel + slack) + 1 := by omega
    rw [budget]
    exact CopyHorizonExtends.bind (loadElem_horizon frame fuel slack type _) (fun _ =>
      .bind (loadFields_horizon frame fuel slack types path (start + 1)) (fun _ => .refl _))

theorem loadBytes_horizon (frame : Source.Fr) :
    ∀ (fuel slack : Nat) (path : Source.SPath) (start count : Nat),
    CopyHorizonExtends (Source.loadBytes (E := E) (Γ := Γ) frame fuel path start count)
      (Source.loadBytes frame (fuel + slack) path start count)
  | 0, slack, path, start, count => by cases count <;> exact CopyHorizonExtends.timeout _
  | fuel + 1, slack, path, start, 0 => by
    have budget : fuel + 1 + slack = (fuel + slack) + 1 := by omega
    rw [budget]
    exact CopyHorizonExtends.refl _
  | fuel + 1, slack, path, start, count + 1 => by
    have budget : fuel + 1 + slack = (fuel + slack) + 1 := by omega
    rw [budget]
    apply CopyHorizonExtends.bind (.refl _)
    intro value
    cases value with
    | fixedBytes bytes bound =>
      exact CopyHorizonExtends.bind (loadBytes_horizon frame fuel slack path (start + 1) count) (fun _ => .refl _)
    | memRef impossible _ => cases impossible
    | storRef impossible _ => cases impossible
    | cdRef impossible _ _ => cases impossible
end

def sourceCopyHorizons (E : Source.Env) (Γ : Source.RCtx) (frame : Source.Fr) :
    SourceCopyHorizonCertificate E Γ frame :=
  ⟨loadMem_horizon frame,loadElem_horizon frame,loadElems_horizon frame,loadFields_horizon frame,loadBytes_horizon frame⟩

#print axioms CopyHorizonExtends.refl
#print axioms CopyHorizonExtends.timeout
#print axioms CopyHorizonExtends.bind
#print axioms CopyHorizonExtends.success
#print axioms loadMem_horizon
#print axioms loadElem_horizon
#print axioms loadElems_horizon
#print axioms loadFields_horizon
#print axioms loadBytes_horizon
#print axioms sourceCopyHorizons
end Solidity.Backend.MemoryCopies
