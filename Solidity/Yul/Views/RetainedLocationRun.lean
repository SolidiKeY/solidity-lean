import Solidity.Yul.Views.RetainedRuntimeRun

namespace Solidity.Yul.Views

def locationStoragePathsM {D Γ σ} (loc : Source.Loc D Γ σ) : List Source.SPath := by
  cases loc with
  | stor p => exact [p]
  | «local» _ => exact []
  | mem _ _ => exact []
  | memByte _ _ => exact []
  | cd _ => exact []
  | cdBytes _ _ => exact []
  | cdString _ _ => exact []
  | cdArray _ _ => exact []
  | cdFixedArray _ _ => exact []

/-- Locations are observed before reading: scalar storage locations still carry
paths. This syntactic collector establishes neither pathTy nor reachability.
Local indices remain local; heap-contained references need separate traversal.
Calldata locations carry offsets, not storage paths; their actual bytes remain
in the independently preserved Source.Fr.cd carrier. -/
@[implemented_by locationStoragePathsM]
def locationStoragePaths {D Γ σ} (loc : Source.Loc D Γ σ) : List Source.SPath :=
  Source.Loc.rec (motive := fun _ _ => List Source.SPath)
    (fun _ => []) (fun p => [p]) (fun _ _ => []) (fun _ _ => []) (fun _ => [])
    (fun _ _ => []) (fun _ _ => []) (fun _ _ => []) (fun _ _ => []) loc

theorem locationStoragePaths_eq_M {D Γ σ} (loc : Source.Loc D Γ σ) :
    locationStoragePaths loc=locationStoragePathsM loc := by
  cases loc <;> rfl

def locationScope {E Γ σ} (F : Source.Fr) (loc : Source.Loc E.layout Γ σ) : EntryReferenceScope E :=
  ⟨F.this,locationStoragePaths loc⟩

def captureLocationRun {E Γ σ} (F : Source.Fr) (prior : List (EntryReferenceScope E))
    (m : Source.EM E Γ (Source.Loc E.layout Γ σ)) (s : Source.EMState E Γ) :=
  let result := m.run s
  let returned := match result.1 with | .ok loc => [locationScope F loc] | .error _ => []
  (result,prior++[entryLocalScope F s.1,entryLocalScope F result.2.1]++returned)

theorem captureLocationRun_source {E Γ σ} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.Loc E.layout Γ σ)) (s : Source.EMState E Γ) :
    (captureLocationRun F prior m s).1=m.run s := rfl

theorem captureLocationRun_prefix {E Γ σ} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.Loc E.layout Γ σ)) (s : Source.EMState E Γ) (scope)
    (member : scope ∈ prior) : scope ∈ (captureLocationRun F prior m s).2 :=
  List.mem_append_left _ (List.mem_append_left _ member)

theorem captureLocationRun_return {E Γ σ} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.Loc E.layout Γ σ)) (s after : Source.EMState E Γ) (loc)
    (run : m.run s=(.ok loc,after)) : locationScope F loc ∈ (captureLocationRun F prior m s).2 := by
  unfold captureLocationRun
  rw [run]
  exact List.mem_append_right _ List.mem_cons_self

/-- The real location computation, then the real runtime continuation. Successful
locations survive failed reads/conversions/writes. No recursive producer inside
m or next is implicitly instrumented. -/
def captureLocationBindRun {E Γ σ ρ} (F : Source.Fr) (prior : List (EntryReferenceScope E))
    (m : Source.EM E Γ (Source.Loc E.layout Γ σ))
    (next : Source.Loc E.layout Γ σ → Source.EM E Γ (Source.RVal E.layout ρ))
    (s : Source.EMState E Γ) :=
  let first := captureLocationRun F prior m s
  match first.1.1 with
  | .error error => ((Except.error error,first.1.2),first.2)
  | .ok loc => captureRuntimeRun F first.2 (next loc) first.1.2

theorem captureLocationBindRun_source {E Γ σ ρ} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.Loc E.layout Γ σ))
    (next : Source.Loc E.layout Γ σ → Source.EM E Γ (Source.RVal E.layout ρ))
    (s : Source.EMState E Γ) :
    (captureLocationBindRun F prior m next s).1=(m >>= next).run s := by
  rw [Source.Hoare.run_bind]
  unfold captureLocationBindRun captureLocationRun captureRuntimeRun
  cases m.run s with
  | mk result after => cases result <;> rfl

theorem captureLocationBindRun_keeps {E Γ σ ρ} (F : Source.Fr) (prior)
    (m : Source.EM E Γ (Source.Loc E.layout Γ σ))
    (next : Source.Loc E.layout Γ σ → Source.EM E Γ (Source.RVal E.layout ρ))
    (s : Source.EMState E Γ) (scope) (inside : scope ∈ (captureLocationRun F prior m s).2) :
    scope ∈ (captureLocationBindRun F prior m next s).2 := by
  unfold captureLocationBindRun
  dsimp only
  split
  · exact inside
  · exact captureRuntimeRun_prefix F _ _ _ scope inside

/-- The callee context stays in the returned Loc type. In particular a callee
local index is never reinterpreted as an index in the caller context. -/
def captureSubLocationRun {E Γ Δ σ} (F : Source.Fr) (prior : List (EntryReferenceScope E))
    (caller : Source.Locals E.layout Γ) (callee : Source.Locals E.layout Δ)
    (m : Source.EM E Δ (Source.Loc E.layout Δ σ)) (state : Source.St E) :=
  ((Source.EM.sub (Γ := Γ) callee m).run (caller,state),
    (captureLocationRun F (prior++[entryLocalScope F caller]) m (callee,state)).2)

theorem captureSubLocationRun_caller {E Γ Δ σ} (F : Source.Fr) (prior)
    (caller : Source.Locals E.layout Γ) (callee : Source.Locals E.layout Δ)
    (m : Source.EM E Δ (Source.Loc E.layout Δ σ)) (state : Source.St E) :
    entryLocalScope F caller ∈ (captureSubLocationRun F prior caller callee m state).2 := by
  apply captureLocationRun_prefix
  exact List.mem_append_right _ List.mem_cons_self

theorem captureSubLocationRun_success {E : Source.Env} {Γ Δ : Source.RCtx} {σ : Source.STy} (F : Source.Fr) (prior)
    (caller : Source.Locals E.layout Γ) (callee finalLocals : Source.Locals E.layout Δ)
    (m : Source.EM E Δ (Source.Loc E.layout Δ σ)) (state after : Source.St E) (loc : Source.Loc E.layout Δ σ)
    (run : m.run (callee,state)=(.ok loc,(finalLocals,after))) :
    (captureSubLocationRun F prior caller callee m state).1=(Except.ok (loc,finalLocals),(caller,after)) ∧
      locationScope F loc ∈ (captureSubLocationRun F prior caller callee m state).2 := by
  constructor
  · change (Source.EM.sub callee m).run (caller,state)=_
    rw [actualSub_endpoints,run]
  · exact captureLocationRun_return F _ m _ _ loc run

end Solidity.Yul.Views
