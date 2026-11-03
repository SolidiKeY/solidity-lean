import Solidity.Yul.Views.RetainedOwnershipSub

namespace Solidity.Yul.Views

/-- Proof-only chronological provenance indexed by the ACTUAL Source.EM action
and its complete result/state. This is not another source AST/interpreter/state.
Only listed operations have constructors; arbitrary producer instrumentation and
initial alias completeness are not inferred. No arbitrary action/erasure axiom. -/
inductive RetainedSourceTrace {E τ b child active a} (layout : @RetainedArrayLayout E τ b child active a) :
    {Γ : Source.RCtx} → {α : Type} → Source.EM E Γ α → Source.EMState E Γ →
    RetainedIndexHistory layout → (Except Source.Halt α × Source.EMState E Γ) → RetainedIndexHistory layout → Prop where
  | pure {Γ α} (s : Source.EMState E Γ) (history) (v : α) :
      RetainedSourceTrace layout (pure v) s history (.ok v,s) history
  | halt {Γ α} (s : Source.EMState E Γ) (history) (error : Source.Halt) :
      RetainedSourceTrace layout (Source.EM.halt error : Source.EM E Γ α) s history (.error error,s) history
  | index {Γ} (F : Source.Fr) (s : Source.EMState E Γ) (history) (i) (account : F.this=a)
      (formed : (Source.indexLoc F (Source.Val.storRef (τ := .array .storage τ none) (by rfl) layout.path) i).run s =
        (.ok (.stor (layout.path.go (.index i))),s)) :
      RetainedSourceTrace layout (Source.indexLoc F (Source.Val.storRef (τ := .array .storage τ none) (by rfl) layout.path) i)
        s history (.ok (.stor (layout.path.go (.index i))),s)
        (history++[recordRetainedIndex layout F s i account formed])
  | writeLen {Γ} (F : Source.Fr) (s : Source.EMState E Γ) (history) (p : Source.SPath) (n : Nat) :
      RetainedSourceTrace layout (Source.writeLen F p n) s history ((Source.writeLen F p n).run s) history
  | readLoc {Γ σ} (F : Source.Fr) (s : Source.EMState E Γ) (history) (loc : Source.Loc E.layout Γ σ) :
      RetainedSourceTrace layout (Source.readLoc F loc) s history ((Source.readLoc F loc).run s) history
  | lengthOf {Γ σ} (F : Source.Fr) (s : Source.EMState E Γ) (history) (v : Source.Val E.layout σ) :
      RetainedSourceTrace layout (Source.lengthOf F v) s history ((Source.lengthOf F v).run s) history
  | rawWrite {Γ} {F : Source.Fr} (fixed : Roadmap.Evm.Fixed) (history : RetainedIndexHistory layout)
      (written value : Roadmap.Word) (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership)
      (account : F.this=a) (plan : RetainedOwnershipPlan F (account.symm ▸ layout) fixed (account.symm ▸ history) written value s r) :
      RetainedSourceTrace layout (Source.applyOp F plan.sourceOp) s history plan.step.1 history
  | bindOK {Γ α β} {m : Source.EM E Γ α} {next : α → Source.EM E Γ β} {s mid out : Source.EMState E Γ}
      {h h' h''} {v : α} {result : Except Source.Halt β}
      (first : RetainedSourceTrace layout m s h (.ok v,mid) h')
      (second : RetainedSourceTrace layout (next v) mid h' (result,out) h'') :
      RetainedSourceTrace layout (m >>= next) s h (result,out) h''
  | bindHalt {Γ α β} {m : Source.EM E Γ α} {next : α → Source.EM E Γ β} {s out : Source.EMState E Γ}
      {h h'} {error : Source.Halt} (first : RetainedSourceTrace layout m s h (.error error,out) h') :
      RetainedSourceTrace layout (m >>= next) s h (.error error,out) h'
  | subOK {Γ Δ α} {m : Source.EM E Δ α} (caller : Source.Locals E.layout Γ)
      {callee next : Source.Locals E.layout Δ} {before after : Source.St E} {h h'} {v : α}
      (body : RetainedSourceTrace layout m (callee,before) h (.ok v,(next,after)) h') :
      RetainedSourceTrace layout (Source.EM.sub callee m) (caller,before) h (.ok (v,next),(caller,after)) h'
  | subHalt {Γ Δ α} {m : Source.EM E Δ α} (caller : Source.Locals E.layout Γ)
      {callee next : Source.Locals E.layout Δ} {before after : Source.St E} {h h'} {error : Source.Halt}
      (body : RetainedSourceTrace layout m (callee,before) h (.error error,(next,after)) h') :
      RetainedSourceTrace layout (Source.EM.sub callee m) (caller,before) h (.error error,(caller,after)) h'

theorem RetainedSourceTrace.actual_run {E τ b child active a} {layout : @RetainedArrayLayout E τ b child active a}
    {Γ : Source.RCtx} {α : Type} {m : Source.EM E Γ α} {s : Source.EMState E Γ}
    {h h' : RetainedIndexHistory layout} {result : Except Source.Halt α × Source.EMState E Γ}
    (trace : RetainedSourceTrace layout m s h result h') : m.run s=result := by
  induction trace with
  | pure => rfl
  | halt => rfl
  | index F s h i account formed => exact formed
  | writeLen => rfl
  | readLoc => rfl
  | lengthOf => rfl
  | rawWrite fixed history written value s r account plan => rfl
  | bindOK first second ih₁ ih₂ =>
    rw [Source.Hoare.run_bind,ih₁]
    exact ih₂
  | bindHalt first ih =>
    rw [Source.Hoare.run_bind,ih]
  | subOK caller body ih =>
    unfold Source.EM.sub
    have run := ih
    simp only [ExceptT.run] at run
    simp only [ExceptT.run,ExceptT.mk,run]
  | subHalt caller body ih =>
    unfold Source.EM.sub
    have run := ih
    simp only [ExceptT.run] at run
    simp only [ExceptT.run,ExceptT.mk,run]

end Solidity.Yul.Views
