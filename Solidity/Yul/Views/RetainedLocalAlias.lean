import Solidity.Yul.Views.RetainedExpressionCapture
import Solidity.Backend.MemoryOps.SourceAlias

/-! Constructive retained-path capture for the actual typed local-assignment
producer. Reuse the published Source alias evaluator law; no reference history
or current ancestor bound is invented. Entry, exit and return scopes differ,
and entry aliases survive overwriting and later Source halt. -/
namespace Solidity.Yul.Views.RetainedLocalAlias
open Solidity.Backend.MemoryOps

def value {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (dst src : Source.Idx Γ τ) : Source.EM E Γ (Source.Val E.layout τ) := do
  Source.getV (← Source.evalE G F (n+2) (sourceLocalAlias dst src))

theorem value_run {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ) (dst src : Source.Idx Γ τ) :
    (value G F n dst src).run s=(.ok (s.1.get src),(s.1.set dst (s.1.get src),s.2)) := by
  first | (simp only;done) | skip
  unfold value
  rw [Source.Hoare.run_bind,source_local_alias_run G F n s dst src _ rfl]
  rfl

/-- Exact producer capture for every intrinsic Source type and local index. -/
theorem captured {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ) (dst src : Source.Idx Γ τ)
    (prior : List (EntryReferenceScope E)) :
    captureEvaluatedValue G F (n+2) (sourceLocalAlias dst src) prior s=
      ((.ok (s.1.get src),(s.1.set dst (s.1.get src),s.2)),
        prior++[entryLocalScope F s.1,entryLocalScope F (s.1.set dst (s.1.get src))]++
          [⟨F.this,valueStoragePaths (s.1.get src)⟩]) := by
  first | (simp only;done) | skip
  change captureValueRun F prior (value G F n dst src) s=_
  unfold captureValueRun
  rw [value_run]

/-- Overwriting a local cannot erase its incoming retained-path observation. -/
theorem overwritten {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ) (dst src : Source.Idx Γ τ)
    (prior : List (EntryReferenceScope E)) (p : Source.SPath) (inside : p ∈ valueStoragePaths (s.1.get dst)) :
    ∃ scope ∈ (captureEvaluatedValue G F (n+2) (sourceLocalAlias dst src) prior s).2,
      scope.account=F.this ∧ p ∈ scope.paths :=
  captureValueRun_entry_local F prior (value G F n dst src) s dst p inside

/-- The actual returned value, not an assumed successful index event. -/
theorem returned {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ) (dst src : Source.Idx Γ τ)
    (prior : List (EntryReferenceScope E)) :
    ⟨F.this,valueStoragePaths (s.1.get src)⟩ ∈
      (captureEvaluatedValue G F (n+2) (sourceLocalAlias dst src) prior s).2 := by
  rw [captured]
  exact List.mem_append_right _ List.mem_cons_self

/-- Genuine RefOK supplies static path typing separately from capture. -/
theorem typed_return {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ) (dst src : Source.Idx Γ τ)
    (prior : List (EntryReferenceScope E)) (H : Source.HeapTy) (ok : Source.MemOK E H s)
    (location : τ.loc?=some .storage) (p : Source.SPath)
    (found : s.1.get src=Source.Val.storRef location p) :
    E.pathTy p=some τ ∧
    (s.1.set dst (s.1.get src)).get dst=Source.Val.storRef location p ∧
    ⟨F.this,[p]⟩ ∈ (captureEvaluatedValue G F (n+2) (sourceLocalAlias dst src) prior s).2 := by
  first | (simp only;done) | skip
  have typed := typedEntryReference s.2.heap.ty s.1 src location p found ok.1.2
  refine ⟨typed.1,?_,?_⟩
  · rw [source_locals_get_set,found]
  · have kept := returned G F n s dst src prior
    rw [found] at kept
    exact kept

/-- A later halt preserves the assignment's actual local effects and capture.
This is an explicit bind, not recursive instrumentation of arbitrary programs. -/
theorem late_halt {E : Source.Env} {Γ : Source.RCtx} {τ ρ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ) (dst src : Source.Idx Γ τ)
    (prior : List (EntryReferenceScope E)) (halt : Source.Halt) :
    let captured := captureValueBindRun F prior (value G F n dst src)
      (fun _ => Source.EM.halt halt : Source.Val E.layout τ → Source.EM E Γ (Source.Val E.layout ρ)) s
    captured.1=(.error halt,(s.1.set dst (s.1.get src),s.2)) ∧
      ⟨F.this,valueStoragePaths (s.1.get src)⟩ ∈ captured.2 ∧ entryLocalScope F s.1 ∈ captured.2 := by
  first | (simp only;done) | skip
  dsimp only
  constructor
  · rw [captureValueBindRun_source,Source.Hoare.run_bind,value_run]
    rfl
  · constructor
    · apply captureValueBindRun_keeps_first
      change _ ∈ (captureEvaluatedValue G F (n+2) (sourceLocalAlias dst src) prior s).2
      exact returned G F n s dst src prior
    · apply captureValueBindRun_keeps_first
      change _ ∈ (captureEvaluatedValue G F (n+2) (sourceLocalAlias dst src) prior s).2
      rw [captured]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)

/-- The actual assignment transports every original owner heap typing. -/
theorem MemOK {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ) (dst src : Source.Idx Γ τ)
    (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H ((value G F n dst src).run s).2 := by
  rw [value_run]
  exact source_local_alias_memOK F (n+1) s dst src H ok
end Solidity.Yul.Views.RetainedLocalAlias
