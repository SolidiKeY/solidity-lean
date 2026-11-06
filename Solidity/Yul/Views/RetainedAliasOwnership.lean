import Solidity.Yul.Views.RetainedLocalAlias
import Solidity.Yul.Views.RetainedEntryFrame

/-! One actual Source run assigns a local alias, then applies a checked storage
ownership update. The residual journal advances only after source success.
A static storage failure retains the completed local-assignment prefix. This
adapter does not instrument arbitrary calls or supply global alias coverage. -/
namespace Solidity.Yul.Views.RetainedAliasOwnership
open Solidity.Backend.MemoryOps

abbrev Plan {E τ b child active Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (dst src : Source.Idx Γ σ) (prior : List (EntryReferenceScope E))
    (layout : @RetainedArrayLayout E τ b child active F.this) (fixed : Roadmap.Evm.Fixed)
    (history : RetainedIndexHistory layout) (written word : Roadmap.Word)
    (r : ResidualJournal complementCarrierOwnership) :=
  CapturedOwnershipPlan F layout fixed history
    (captureEvaluatedValue G F (n+2) (sourceLocalAlias dst src) prior s).2 written word
    (s.1.set dst (s.1.get src),s.2) r

def program {E : Source.Env} {Γ : Source.RCtx} {σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (dst src : Source.Idx Γ σ)
    (op : Source.Op E.layout E.lay E.lay) : Source.EM E Γ (Source.Val E.layout σ) := do
  let v ← RetainedLocalAlias.value G F n dst src
  Source.applyOp F op
  pure v

def execute {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r) :=
  let source := (program G F n dst src p.sourceOp).run s
  (source,match source.1 with | .error _ => r | .ok _ => residualRun r p.updates)

/-- The actual compound Source run and existing ownership step share the same
state, result status and complementary journal; no two runs are postulated. -/
theorem execute_eq {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r) :
    execute p=
      ((match p.step.1.1 with | .ok _ => .ok (s.1.get src) | .error h => .error h,p.step.1.2),p.step.2) := by
  first | (simp only;done) | skip
  unfold execute program
  rw [Source.Hoare.run_bind,RetainedLocalAlias.value_run]
  dsimp only
  rw [Source.Hoare.run_bind]
  unfold CapturedOwnershipPlan.step
  rcases actual : (Source.applyOp F p.sourceOp).run (s.1.set dst (s.1.get src),s.2) with ⟨result,after⟩
  cases result <;> rfl

/-- Real static refusal is after alias assignment, with no residual updates. -/
theorem static {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    (blocked : F.static=true) :
    execute p=((.error (.revert []),(s.1.set dst (s.1.get src),s.2)),r) := by
  rw [execute_eq,p.static blocked]

/-- The successful source status and journal arise from the actual compound run. -/
theorem nonstatic {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    (allowed : F.static=false) :
    execute p=((.ok (s.1.get src),(s.1.set dst (s.1.get src),{s.2 with ex:=s.2.ex.apply p.sourceOp})),
      residualRun r p.updates) := by
  rw [execute_eq,p.nonstatic allowed]

/-- Complete physical map reconstruction for the SAME actual compound result. -/
theorem reencode {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    (allowed : F.static=false) :
    finiteEncode p.next ((execute p).1.2.2.ex.world.accounts F.this).storage
      (fun q => (execute p).2.cells (complementKey false F.this q))=some p.nextRaw := by
  rw [execute_eq]
  exact p.reencode allowed

/-- Every original heap typing survives the actual alias plus storage sequence. -/
theorem MemOK {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    (H : Source.HeapTy) (ok : Source.MemOK E H s) : Source.MemOK E H (execute p).1.2 := by
  rw [execute_eq]
  exact p.MemOK H (source_local_alias_memOK F (n+1) s dst src H ok)

/-- The actual compound result supplies the existing paired frame carrier. -/
theorem companion {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r) :
    (⟨(execute p).1.2.2.ex,(execute p).2⟩ : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership)=p.after := by
  rw [execute_eq]
  rfl

/-- Existing complement keys outside this persistent account are unchanged.
This carrier isolation does not admit transient aggregate declarations. -/
theorem other_journal {E τ b child active Γ σ G F n s dst src prior layout fixed history written word r}
    (p : @Plan E τ b child active Γ σ G F n s dst src prior layout fixed history written word r)
    (key : ResidualKey complementCarrierOwnership)
    (outside : key.transient=true ∨ key.address≠F.this) : (execute p).2.cells key=r.cells key := by
  first | (simp only;done) | skip
  cases mode : F.static
  · rw [nonstatic p mode]
    apply residualRun_other
    intro update member
    dsimp only [CapturedOwnershipPlan.updates,ownershipUpdates] at member
    obtain ⟨q,_,same⟩ := List.mem_map.mp member
    subst update
    intro equal
    rcases outside with transient | different
    · have flag := congrArg ResidualKey.transient equal
      change key.transient=false at flag
      rw [transient] at flag
      cases flag
    · exact different (congrArg ResidualKey.address equal)
  · rw [static p mode]
end Solidity.Yul.Views.RetainedAliasOwnership
