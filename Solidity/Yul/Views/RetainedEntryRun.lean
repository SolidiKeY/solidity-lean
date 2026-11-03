import Solidity.Yul.Views.RetainedEntryPaths

namespace Solidity.Yul.Views

/-- Total observation of an ACTUAL typed-value computation. The source run is
executed unchanged. Entry locals, final locals, and a successful returned value
are scanned, even when no index event occurred in this run. This does not scan
unobserved intermediate values or establish global producer completeness. -/
def captureValueRun {E Γ σ} (F : Source.Fr) (prior : List (EntryReferenceScope E))
    (m : Source.EM E Γ (Source.Val E.layout σ)) (s : Source.EMState E Γ) :=
  let result := m.run s
  let endpoints := [entryLocalScope F s.1,entryLocalScope F result.2.1]
  let returned := match result.1 with
    | .ok v => [EntryReferenceScope.mk F.this (valueStoragePaths v)]
    | .error _ => []
  (result,prior++endpoints++returned)

theorem captureValueRun_source {E Γ σ} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.Val E.layout σ)) (s : Source.EMState E Γ) :
    (captureValueRun F prior m s).1=m.run s := rfl

theorem captureValueRun_prefix {E Γ σ} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.Val E.layout σ)) (s : Source.EMState E Γ)
    (scope : EntryReferenceScope E) (member : scope ∈ prior) :
    scope ∈ (captureValueRun F prior m s).2 :=
  List.mem_append_left _ (List.mem_append_left _ member)

theorem captureValueRun_return {E Γ σ} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.Val E.layout σ)) (s out : Source.EMState E Γ) (v)
    (run : m.run s=(.ok v,out)) :
    (captureValueRun F prior m s).2=prior++[entryLocalScope F s.1,entryLocalScope F out.1]++[⟨F.this,valueStoragePaths v⟩] := by
  unfold captureValueRun
  rw [run]

theorem captureValueRun_halt {E Γ σ} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.Val E.layout σ)) (s out : Source.EMState E Γ) (error)
    (run : m.run s=(.error error,out)) :
    (captureValueRun F prior m s).2=prior++[entryLocalScope F s.1,entryLocalScope F out.1] := by
  unfold captureValueRun
  rw [run]
  exact List.append_nil _

theorem captureValueRun_entry_local {E Γ σ ρ} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.Val E.layout σ)) (s : Source.EMState E Γ)
    (i : Source.Idx Γ ρ) (p) (inside : p ∈ valueStoragePaths (s.1.get i)) :
    ∃ scope ∈ (captureValueRun F prior m s).2, scope.account=F.this ∧ p ∈ scope.paths := by
  refine ⟨entryLocalScope F s.1,?_,rfl,localStoragePaths_get s.1 i p inside⟩
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self))

/-- Existing owner sub semantics, for EVERY callee computation/result. Caller
locals stay in the actual output on success AND halt. No body trace premise. -/
theorem actualSub_endpoints {E Γ Δ α} (m : Source.EM E Δ α)
    (caller : Source.Locals E.layout Γ) (callee : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.EM.sub (Γ := Γ) callee m).run (caller,state) =
      match m.run (callee,state) with
      | (.ok value,(next,after)) => (.ok (value,next),(caller,after))
      | (.error error,(_,after)) => (.error error,(caller,after)) := rfl

/-- Capture the saved caller BEFORE substituting callee locals and the returned
callee value AFTER the actual sub run. Same account only: sub is a local-context
operation, not an external-account call. -/
def captureSubValueRun {E Γ Δ σ} (F : Source.Fr) (prior : List (EntryReferenceScope E))
    (caller : Source.Locals E.layout Γ) (callee : Source.Locals E.layout Δ)
    (m : Source.EM E Δ (Source.Val E.layout σ)) (state : Source.St E) :=
  ((Source.EM.sub (Γ := Γ) callee m).run (caller,state),
    (captureValueRun F (prior++[entryLocalScope F caller]) m (callee,state)).2)

theorem captureSubValueRun_caller {E Γ Δ σ} (F : Source.Fr) (prior)
    (caller : Source.Locals E.layout Γ) (callee : Source.Locals E.layout Δ)
    (m : Source.EM E Δ (Source.Val E.layout σ)) (state : Source.St E) :
    entryLocalScope F caller ∈ (captureSubValueRun F prior caller callee m state).2 := by
  apply captureValueRun_prefix
  exact List.mem_append_right _ List.mem_cons_self

theorem captureSubValueRun_return {E : Source.Env} {Γ Δ : Source.RCtx} {σ : Source.STy} (F : Source.Fr) (prior : List (EntryReferenceScope E))
    (caller : Source.Locals E.layout Γ) (callee : Source.Locals E.layout Δ) (finalLocals : Source.Locals E.layout Δ)
    (m : Source.EM E Δ (Source.Val E.layout σ)) (state after : Source.St E) (value : Source.Val E.layout σ)
    (run : m.run (callee,state)=(Except.ok value,(finalLocals,after))) :
    (captureSubValueRun F prior caller callee m state).1=(Except.ok (value,finalLocals),(caller,after)) ∧
      ⟨F.this,valueStoragePaths value⟩ ∈ (captureSubValueRun F prior caller callee m state).2 := by
  constructor
  · change (Source.EM.sub callee m).run (caller,state)=_
    rw [actualSub_endpoints,run]
  · change _ ∈ (captureValueRun F _ m _).2
    rw [captureValueRun_return F _ m _ _ value run]
    exact List.mem_append_right _ List.mem_cons_self

/-- Constructive sequencing for actual typed reference-value producers. First
return/endpoint observations survive even when the continuation halts. This
wraps source computations, not a second evaluator or an assumed trace law. -/
def captureValueBindRun {E Γ σ ρ} (F : Source.Fr) (prior : List (EntryReferenceScope E))
    (first : Source.EM E Γ (Source.Val E.layout σ))
    (next : Source.Val E.layout σ → Source.EM E Γ (Source.Val E.layout ρ))
    (s : Source.EMState E Γ) :=
  let captured := captureValueRun F prior first s
  match captured.1.1 with
  | .error error => ((Except.error error,captured.1.2),captured.2)
  | .ok value => captureValueRun F captured.2 (next value) captured.1.2

theorem captureValueBindRun_source {E Γ σ ρ} (F : Source.Fr) (prior)
    (first : Source.EM E Γ (Source.Val E.layout σ))
    (next : Source.Val E.layout σ → Source.EM E Γ (Source.Val E.layout ρ))
    (s : Source.EMState E Γ) :
    (captureValueBindRun F prior first next s).1=(first >>= next).run s := by
  rw [Source.Hoare.run_bind]
  unfold captureValueBindRun captureValueRun
  cases first.run s with
  | mk result after => cases result <;> rfl

theorem captureValueBindRun_keeps_first {E Γ σ ρ} (F : Source.Fr) (prior)
    (first : Source.EM E Γ (Source.Val E.layout σ))
    (next : Source.Val E.layout σ → Source.EM E Γ (Source.Val E.layout ρ))
    (s : Source.EMState E Γ) (scope)
    (inside : scope ∈ (captureValueRun F prior first s).2) :
    scope ∈ (captureValueBindRun F prior first next s).2 := by
  unfold captureValueBindRun
  dsimp only
  split
  · exact inside
  · exact captureValueRun_prefix F _ _ _ scope inside

end Solidity.Yul.Views
