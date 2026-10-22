import Solidity.Calculus.ReadTrace
import Solidity.Calculus.QueryReadBounds
import Solidity.Calculus.ProgramReduction

/-!
# Original-source countermodels from dependent read occurrences

Exact program/update normalization produces the same typed leaf used by
the query reader. Occurrence values determine the read locations during
replay; only an alias-consistent false trace is materialized. The resulting
certificate refutes the original formula, including its universal prefix.
This interface replays solver-supplied values; it does not choose them.
-/

namespace Solidity.Decide

open ReadRealization Semantics

variable {C : Contract}

/-- Source equivalences and the leaf's original typed query syntax. -/
structure TraceReduction (φ : Fml C []) where
  normalization : DeclarationReduction φ
  source : SourceReduction normalization.formula
  sentence : ReadSentence source.leaf.elim

/-- Unsupported syntax and normalization budgets have no semantic verdict. -/
def traceReduction? (φ : Fml C []) : Option (TraceReduction φ) := do
  let d ← ProgramNormalization.ofFormula? 2048 φ
  let r ← sourceReduction? d.formula
  let sentence ← ReadSentence.ofFormula? r.leaf.elim
  return ⟨d, r, sentence⟩

namespace TraceReduction

/-- No source counterexample is lost: the original validity question is
exactly validity over replay values satisfying their finite alias gate. -/
theorem valid_iff {φ : Fml C []} (r : TraceReduction φ) :
    Fml.Valid φ ↔ ∀ (g : State C []) (args : List CallValue) (values : ReadValues),
      (Query.replay values 0 (r.sentence.query g AEnv.dflt args)).2.Consistent →
      (Query.replay values 0 (r.sentence.query g AEnv.dflt args)).1 = true := by
  constructor
  · intro h g args
    apply (r.sentence.query g AEnv.dflt args).all_storage_iff_traces.mp
    intro st
    exact r.sentence.query_of_holds g AEnv.dflt args st
      ((r.source.elim_holds_iff _).mpr ((r.normalization.correct _).mpr (h _)))
  · intro h σ
    apply (r.normalization.correct σ).mp
    apply (r.source.elim_holds_iff σ).mp
    exact r.sentence.holds_of_queries σ AEnv.dflt σ.storage (fun args =>
      ((r.sentence.query σ AEnv.dflt args).all_storage_iff_traces.mpr (h σ args)) σ.storage)

/-- An actual counterstore to one typed query instance refutes the original
source formula, retaining every premise and universal binder. -/
def countermodelFromQuery {φ : Fml C []} (r : TraceReduction φ) (g : State C [])
    (args : List CallValue)
    (cm : { st : Storage C // (r.sentence.query g AEnv.dflt args).runStorage st = false }) :
    { σ : State C [] // ¬ holds σ φ } :=
  let σ : State C [] := { g with storage := cm.val }
  ⟨σ, fun h => Bool.false_ne_true (cm.property.symm.trans
    (r.sentence.query_of_holds g AEnv.dflt args cm.val
      ((r.source.elim_holds_iff σ).mpr ((r.normalization.correct σ).mpr h))))⟩

/-- Materialize a false selected instance, then transport it through both
source equivalences. Conflicting aliases are rejected before reconstruction. -/
def countermodelFromTrace? {φ : Fml C []} (r : TraceReduction φ) (g : State C [])
    (args : List CallValue) (values : ReadValues) :
    Option { σ : State C [] // ¬ holds σ φ } :=
  ((r.sentence.query g AEnv.dflt args).countermodelFromTrace? values).map
    (r.countermodelFromQuery g args)

/-- A solver supplies only finite typed occurrence values. Replay selects
the actual locations and checks every alias before certifying the source. -/
def countermodelFromValues? {φ : Fml C []} (r : TraceReduction φ) (g : State C [])
    (args values : List CallValue) : Option { σ : State C [] // ¬ holds σ φ } :=
  r.countermodelFromTrace? g args (ReadValues.ofList values)

end TraceReduction

end Solidity.Decide
