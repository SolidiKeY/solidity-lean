import Solidity.Yul.Views.RetainedEntryRun

namespace Solidity.Yul.Views

/-- The ACTUAL owner evaluator followed by its ACTUAL getV conversion. Tuple or
literal conversion failures remain those source failures; no alternative parser,
AST, evaluation, admission predicate or fuel policy is introduced. Endpoint
collection is total for every evaluator horizon, but not intermediate capture. -/
def captureEvaluatedValue {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (e : Source.RExpr E Γ σ) (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  captureValueRun F prior (do Source.getV (← Source.evalE G F n e)) s

theorem captureEvaluatedValue_source {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (e : Source.RExpr E Γ σ) (prior) (s : Source.EMState E Γ) :
    (captureEvaluatedValue G F n e prior s).1=(do Source.getV (← Source.evalE G F n e)).run s := rfl

/-- Constructive producer coverage, for EVERY actual local index, frame, entry
state and positive owner horizon. Incoming aliases need no invented index event. -/
theorem captureEvaluatedValue_local {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (i : Source.Idx Γ σ) (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :
    captureEvaluatedValue G F (n+1) (.local i) prior s =
      ((Except.ok (s.1.get i),s),prior++[entryLocalScope F s.1,entryLocalScope F s.1]++[⟨F.this,valueStoragePaths (s.1.get i)⟩]) := rfl

theorem captureEvaluatedValue_timeout {E Γ σ} (G : Source.Glob E) (F : Source.Fr)
    (e : Source.RExpr E Γ σ) (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :
    captureEvaluatedValue G F 0 e prior s =
      ((Except.error .timeout,s),prior++[entryLocalScope F s.1,entryLocalScope F s.1]) := by
  change (_,(_++_)++[])=_
  rw [List.append_nil]
  rfl

/-- ACTUAL location evaluation followed by ACTUAL readLoc, retaining every
success/error/store effect. It captures the returned reference, not all paths
visited by the internal recursive evaluator. -/
def captureEvaluatedLocation {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (loc : Source.RLVal E Γ σ) (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  captureValueRun F prior (do Source.readLoc F (← Source.evalLoc G F n loc)) s

theorem captureEvaluatedLocation_source {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (loc : Source.RLVal E Γ σ) (prior) (s : Source.EMState E Γ) :
    (captureEvaluatedLocation G F n loc prior s).1=(do Source.readLoc F (← Source.evalLoc G F n loc)).run s := rfl

theorem captureEvaluatedLocation_local {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (i : Source.Idx Γ σ) (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :
    captureEvaluatedLocation G F (n+1) (.local i) prior s =
      ((Except.ok (s.1.get i),s),prior++[entryLocalScope F s.1,entryLocalScope F s.1]++[⟨F.this,valueStoragePaths (s.1.get i)⟩]) := rfl

end Solidity.Yul.Views
