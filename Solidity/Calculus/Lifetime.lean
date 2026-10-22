import Solidity.Calculus.Correct
import Solidity.Semantics.Lifetime

/-!
# Function correctness establishes lifetime invariants

An external call's precondition is checked in its fresh frame, after crediting
the incoming payment. A proved `Spec` box then establishes the invariant on
every committed outcome. Constructor establishment and stability under time
remain explicit obligations. The box's acceptance of exhaustion cannot create
a committed outcome: `System.run_ok` requires an actual successful run.
-/

namespace Solidity.Lifetime

variable {C : Contract} {D A : Type}

/-- Read a proved box at an actual successful outcome. -/
theorem post_of_box {P : Prog C [] []} {φ : Spec C []} {σ : State C []}
    {o : Out C σ.H []} (box : Spec.sat σ (.box P φ))
    (run : P.run σ = .ok o) : Spec.sat o.st φ := by
  simp only [Spec.sat, run] at box
  exact box

/-- A per-function correctness theorem preserves a lifetime predicate on each
successful commit. Entry premises are owed after the transaction's payment. -/
theorem System.preserves_of_spec {M : System C D A} {I : World C → Prop}
    {a : A} (pre post : Spec C [])
    (proved : Spec.Valid (.imp pre (.box (M.call a) post)))
    (entry : ∀ s tx σ, s.accepts tx → M.allowCall s a tx → I s →
      s.enter tx = .ok σ → Spec.sat σ pre)
    (reflect : ∀ σ, Spec.sat σ post → I (World.ofState σ))
    {s t : World C} {tx : TTx} (accepted : s.accepts tx) (allowed : M.allowCall s a tx)
    (hi : I s) (run : M.run s a tx = .ok t) : I t :=
  let ⟨σ, o, enter, ran, eq⟩ := System.run_ok run
  eq ▸ reflect o.st (post_of_box (proved σ (entry s tx σ accepted allowed hi enter)) ran)

/-- Combine existing function correctness proofs into an inductive invariant.
Each action may use its own precondition and postcondition. -/
theorem Invariant.ofSpecs {M : System C D A} {I : World C → Prop}
    (deploy : ∀ d tx σ, M.allowDeploy d tx →
      C.deployT (M.deploy d) tx = .ok σ → I (World.ofState σ))
    (pre post : A → Spec C [])
    (proved : ∀ a, Spec.Valid (.imp (pre a) (.box (M.call a) (post a))))
    (entry : ∀ s a tx σ, s.accepts tx → M.allowCall s a tx → I s →
      s.enter tx = .ok σ → Spec.sat σ (pre a))
    (reflect : ∀ a σ, Spec.sat σ (post a) → I (World.ofState σ))
    (time : ∀ s t, s.timestamp.1 ≤ t.1 → I s → I (s.atTime t)) : Invariant M I :=
  .ofRuns deploy
    (fun _ a _ _ accepted allowed hi run =>
      System.preserves_of_spec (pre a) (post a) (proved a)
        (fun s tx σ => entry s a tx σ) (reflect a) accepted allowed hi run)
    time

/-- The same successful-outcome bridge for an internal dynamic-logic box. -/
theorem post_of_fml_box {P : Prog C [] []} {φ : Fml C []} {σ : State C []}
    {o : Out C σ.H []} (box : holds σ (.modal .box P .nil φ))
    (run : P.run σ = .ok o) : holds o.st φ := by
  change Modality.afterRunTR .box (holds · φ) (Prog.runFrames σ P .nil) at box
  have hr : Prog.runFrames σ P .nil = .ok o.st := by
    unfold Prog.runFrames
    rw [run]
    rfl
  rw [hr] at box
  exact box.1

/-- A constructor box supplies its postcondition at successful deployment,
after the deployment value guard has actually passed. -/
theorem post_of_deploy_box {P : Prog C [] []} {φ : Fml C []} {tx : TTx}
    {σ : State C []} (box : holds (State.deploy C tx) (.modal .box P .nil φ))
    (run : C.deployT P tx = .ok σ) : holds σ φ := by
  unfold Contract.deployT at run
  split at run
  · cases run
  · cases hr : P.run (State.deploy C tx) with
    | error e => simp only [hr, bind, Except.bind] at run; cases run
    | ok o =>
      simp only [hr, bind, Except.bind] at run
      cases run
      exact post_of_fml_box box hr

/-- Reuse an internal formula proof, with explicit interpretation of its
precondition and postcondition as a persistent invariant. -/
theorem System.preserves_of_fml {M : System C D A} {I : World C → Prop}
    {a : A} (pre post : Fml C [])
    (proved : Fml.Valid (.imp pre (.modal .box (M.call a) .nil post)))
    (entry : ∀ s tx σ, s.accepts tx → M.allowCall s a tx → I s →
      s.enter tx = .ok σ → holds σ pre)
    (reflect : ∀ σ, holds σ post → I (World.ofState σ))
    {s t : World C} {tx : TTx} (accepted : s.accepts tx) (allowed : M.allowCall s a tx)
    (hi : I s) (run : M.run s a tx = .ok t) : I t :=
  let ⟨σ, o, enter, ran, eq⟩ := System.run_ok run
  eq ▸ reflect o.st (post_of_fml_box (proved σ (entry s tx σ accepted allowed hi enter)) ran)

end Solidity.Lifetime
