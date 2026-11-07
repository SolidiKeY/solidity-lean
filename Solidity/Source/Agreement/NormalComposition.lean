import Solidity.Source.Agreement.NormalCuts

/-! Compositional normal-result agreement from explicit single-statement
producer facts. The Source prefix and its intermediate journal are derived
from the actual run. The model sequence keeps the actual heap extensions.
No statement association, step producer or full-state relation is fabricated. -/
namespace Solidity.Source.Agreement

variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Empty programs supply a concrete base; horizon zero is not normal. -/
theorem normal_nil (ps : List PrimTy) (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E)) :
    NormalLocalsObligation (C := C) (R := R) (M := M) (k := k)
      ps ps G F nps ph .nil .nil := by
  intro ls st model related n ls' journal ran
  cases n with
  | zero => cases ran
  | succ n =>
    change (Except.ok (Source.Out.normal ls), (.nil, st)) =
      (Except.ok (Source.Out.normal ls'), journal) at ran
    have he : ls = ls' := Source.Out.normal.inj (Except.ok.inj (Prod.mk.inj ran).1)
    subst ls'
    exact ⟨⟨model, List.prefix_refl _⟩, rfl, related⟩

/-- The first producer hypothesis is single-statement normal agreement; the
second is the already-built tail proof. Neither supplies a chosen whole run,
intermediate state, journal or final result. All source error/control arms
remain outside the explicit normal-result antecedent. -/
theorem normal_cons {ps ms qs : List PrimTy} (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E))
    (s : RStmt E R M k (sourceContext ps) (sourceContext ms))
    (rest : RItems E R M k (sourceContext ms) (sourceContext qs))
    (S : Solidity.Stmt C (modelContext ps) (modelContext ms))
    (P : Prog C (modelContext ms) (modelContext qs))
    (step : NormalStmtObligation ps ms G F nps ph s S)
    (tail : NormalLocalsObligation ms qs G F nps ph rest P) :
    NormalLocalsObligation ps qs G F nps ph (.stmt s rest) (.cons S P) := by
  intro ls st model related fuel ls' journal ran
  cases fuel with
  | zero => cases ran
  | succ n =>
    obtain ⟨mid, midState, first, next⟩ := source_cons_cut G F n nps ph s rest ls st ls' journal ran
    obtain ⟨out₁, modelFirst, relatedMid⟩ := step ls st model related n mid (.nil, midState) first
    obtain ⟨out₂, modelNext, relatedFinal⟩ := tail mid midState out₁.st relatedMid n ls' journal next
    refine ⟨⟨out₂.st, out₁.ext.trans out₂.ext⟩, ?_, relatedFinal⟩
    change TRun.seq (Solidity.Stmt.runC S) (Prog.runC P) model = _
    simp only [TRun.seq, modelFirst, modelNext, Except.map]

/-- An importing client with exactly two explicit per-statement facts. The
whole-program normal agreement is proved here rather than assumed. -/
theorem normal_two {ps ms qs : List PrimTy} (G : Glob E) (F : Fr)
    (nps : Nat) (ph : Option (Ph E))
    (s₁ : RStmt E R M k (sourceContext ps) (sourceContext ms))
    (s₂ : RStmt E R M k (sourceContext ms) (sourceContext qs))
    (S₁ : Solidity.Stmt C (modelContext ps) (modelContext ms))
    (S₂ : Solidity.Stmt C (modelContext ms) (modelContext qs))
    (first : NormalStmtObligation ps ms G F nps ph s₁ S₁)
    (second : NormalStmtObligation ms qs G F nps ph s₂ S₂) :
    NormalLocalsObligation ps qs G F nps ph (.stmt s₁ (.stmt s₂ .nil))
      (.cons S₁ (.cons S₂ .nil)) := by
  exact normal_cons G F nps ph s₁ _ S₁ _ first
    (normal_cons G F nps ph s₂ .nil S₂ .nil second (normal_nil qs G F nps ph))

end Solidity.Source.Agreement
