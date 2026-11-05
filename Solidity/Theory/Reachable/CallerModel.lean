import Solidity.Theory.Reachable.CleanTail
import Solidity.Calculus.CleanTailBoundary

/-!
# Reachable states under a caller model (O12 orthogonal to O11)

`Lifetime.Reachable` runs each entry call deterministically. Here an entry
call runs under an execution relation `Exec C`: the outcomes a caller model
admits for a program from an entry frame (`COut`: a result, a halt, or the
callback invariant broken where control leaves the contract). The
transaction layer is the same as `Lifetime`'s: the payable guard, the
entry frame, a commit of a result, a rollback of a revert or a panic,
waiting. A `violated` run admits any outcome, so an invariant proved under a
caller model owes that its entries never violate the callback invariant.

The caller model is a stub until O11 (lane VC2) publishes its lattice
`none < staticOnly < nonReentrant < any`: `CallerStub` has the two readings
that exist today, `noCallback` (the deterministic run, `COut.ofRes`) and
`withCallback J` (`ExecP J`, `Semantics/Callback.lean`). What O12 needs from
O11 is only an `Exec C` per model and its order (`Exec.Le`): reachability is
monotone in it (`ReachableE.mono`), so an invariant proved against a
stronger attacker holds against a weaker one (`InvariantE.weaken`).

`ReachableE (noCallback) M` is exactly `Lifetime.Reachable M`
(`reachableE_noCallback_iff`), so `ValidStartE` under `noCallback` is
`ValidStart (.reachable M)`. Clean tails are an invariant under callbacks
too, for entries that keep them across the callback boundary
(`cleanTail_invariantE`, `Prog.CleanTailCallbackBoundary`).

Deployment stays deterministic (`Lifetime.System.Init`): a constructor's
callbacks are not modelled here.
-/

namespace Solidity.Reachable

open Lifetime

variable {C : Contract} {D A : Type}

/-- **An entry call's admitted outcomes**: from an entry frame, what a run of
the program may end in. -/
abbrev Exec (C : Contract) := (σ : State C []) → Prog C [] [] → COut C σ.H [] → Prop

/-- `E₁` admits no more than `E₂`: a weaker attacker. -/
def Exec.Le (E₁ E₂ : Exec C) : Prop := ∀ σ P r, E₁ σ P r → E₂ σ P r

/-- **Stub of O11's caller models**: the two readings `ValidT` has today. -/
inductive CallerStub (C : Contract) where
  | noCallback
  | withCallback (J : StateInv C)

/-- The execution relation of a caller model. -/
def CallerStub.exec : CallerStub C → Exec C
  | .noCallback => fun σ P r => r = COut.ofRes (P.run σ)
  | .withCallback J => fun σ P r => ExecP J σ P r

/-- Whether an entry call is refused before it runs (`System.run`'s guard). -/
def _root_.Solidity.Lifetime.System.refuses (M : System C D A) (a : A) (tx : TTx) : Bool :=
  !M.payable a && tx.msgValue.1 != 0

/-- **One entry call under `E`**: refused, failing to enter, or run under
`E` from the entry frame. A run that violates the callback invariant admits
any result. -/
inductive RunE (E : Exec C) (M : System C D A) (s : World C) (a : A) (tx : TTx) :
    TRes (World C) → Prop where
  | refused (h : M.refuses a tx = true) : RunE E M s a tx (.error .revert)
  | enterFail {e : THalt} (h : M.refuses a tx = false) (en : s.enter tx = .error e) :
      RunE E M s a tx (.error e)
  | ok {σ : State C []} {o : Out C σ.H []} (h : M.refuses a tx = false)
      (en : s.enter tx = .ok σ) (run : E σ (M.call a) (.ok o)) :
      RunE E M s a tx (.ok (World.ofState o.st))
  | halt {σ : State C []} {e : THalt} (h : M.refuses a tx = false)
      (en : s.enter tx = .ok σ) (run : E σ (M.call a) (.halt e)) : RunE E M s a tx (.error e)
  | violated {σ : State C []} (h : M.refuses a tx = false)
      (en : s.enter tx = .ok σ) (run : E σ (M.call a) .violated) (r : TRes (World C)) :
      RunE E M s a tx r

/-- `Lifetime.Step` with entry calls run under `E`. -/
inductive StepE (E : Exec C) (M : System C D A) : World C → Event A → World C → Prop where
  | commit {s t : World C} {a : A} {tx : TTx}
      (accepted : s.accepts tx) (allowed : M.allowCall s a tx)
      (run : RunE E M s a tx (.ok t)) : StepE E M s (.call a tx) t
  | rollback {s : World C} {a : A} {tx : TTx} {e : THalt}
      (accepted : s.accepts tx) (allowed : M.allowCall s a tx)
      (run : RunE E M s a tx (.error e))
      (failed : e = .revert ∨ (∃ data, e = .revertWith data) ∨ e = .panic) :
      StepE E M s (.call a tx) (s.atTime tx.timestamp)
  | wait {s : World C} {t : PrimTy.uint.Denote} (later : s.timestamp.1 ≤ t.1) :
      StepE E M s (.wait t) (s.atTime t)

/-- **The worlds reachable under `E`**: a successful deployment, then
admitted steps. -/
inductive ReachableE (E : Exec C) (M : System C D A) : World C → Prop where
  | init {s : World C} (deployed : M.Init s) : ReachableE E M s
  | step {s t : World C} {a : Event A} (before : ReachableE E M s)
      (next : StepE E M s a t) : ReachableE E M t

/-- An invariant under `E`, by induction over the entry points. -/
structure InvariantE (E : Exec C) (M : System C D A) (I : World C → Prop) : Prop where
  initially : ∀ s, M.Init s → I s
  preserved : ∀ {s t a}, I s → StepE E M s a t → I t

theorem InvariantE.always {E : Exec C} {M : System C D A} {I : World C → Prop}
    (h : InvariantE E M I) : ∀ s, ReachableE E M s → I s := by
  intro s hs
  induction hs with
  | init deployed => exact h.initially _ deployed
  | step _ next ih => exact h.preserved ih next

/-! ## Monotone in the caller model -/

theorem RunE.mono {E₁ E₂ : Exec C} (hE : Exec.Le E₁ E₂) {M : System C D A} {s : World C}
    {a : A} {tx : TTx} {r : TRes (World C)} (h : RunE E₁ M s a tx r) : RunE E₂ M s a tx r :=
  match h with
  | .refused g => .refused g
  | .enterFail g en => .enterFail g en
  | .ok g en run => .ok g en (hE _ _ _ run)
  | .halt g en run => .halt g en (hE _ _ _ run)
  | .violated g en run r => .violated g en (hE _ _ _ run) r

theorem StepE.mono {E₁ E₂ : Exec C} (hE : Exec.Le E₁ E₂) {M : System C D A} {s t : World C}
    {a : Event A} (h : StepE E₁ M s a t) : StepE E₂ M s a t :=
  match h with
  | .commit acc al run => .commit acc al (run.mono hE)
  | .rollback acc al run failed => .rollback acc al (run.mono hE) failed
  | .wait later => .wait later

/-- **A weaker attacker reaches no more worlds.** -/
theorem ReachableE.mono {E₁ E₂ : Exec C} (hE : Exec.Le E₁ E₂) {M : System C D A}
    {s : World C} (h : ReachableE E₁ M s) : ReachableE E₂ M s := by
  induction h with
  | init deployed => exact .init deployed
  | step _ next ih => exact .step ih (next.mono hE)

/-- **An invariant against a stronger attacker holds against a weaker one.** -/
theorem InvariantE.weaken {E₁ E₂ : Exec C} (hE : Exec.Le E₁ E₂) {M : System C D A}
    {I : World C → Prop} (h : InvariantE E₂ M I) : InvariantE E₁ M I where
  initially := h.initially
  preserved := fun hi step => h.preserved hi (step.mono hE)

/-! ## `noCallback` is `Lifetime` -/

theorem runE_noCallback_iff {M : System C D A} {s : World C} {a : A} {tx : TTx}
    {r : TRes (World C)} :
    RunE (CallerStub.noCallback (C := C)).exec M s a tx r ↔ M.run s a tx = r := by
  constructor
  · intro h
    cases h with
    | refused g =>
      unfold System.run
      rw [if_pos (show (!M.payable a && tx.msgValue.1 != 0) = true from g)]
    | enterFail g en =>
      unfold System.run
      rw [if_neg (by simp only [System.refuses] at g; simp only [g]; decide)]
      simp only [en, bind, Except.bind]
    | ok g en run =>
      unfold System.run
      rw [if_neg (by simp only [System.refuses] at g; simp only [g]; decide)]
      simp only [en, bind, Except.bind]
      simp only [CallerStub.exec] at run
      cases hr : (M.call a).run _ with
      | error e => rw [hr] at run; cases run
      | ok o' =>
        rw [hr] at run
        cases run
        rfl
    | halt g en run =>
      unfold System.run
      rw [if_neg (by simp only [System.refuses] at g; simp only [g]; decide)]
      simp only [en, bind, Except.bind]
      simp only [CallerStub.exec] at run
      cases hr : (M.call a).run _ with
      | error e' => rw [hr] at run; cases run; rfl
      | ok o' => rw [hr] at run; cases run
    | violated g en run r =>
      simp only [CallerStub.exec] at run
      cases hr : (M.call a).run _ with
      | error e' => rw [hr] at run; cases run
      | ok o' => rw [hr] at run; cases run
  · intro h
    subst h
    cases g : M.refuses a tx with
    | true =>
      unfold System.run
      rw [if_pos (show (!M.payable a && tx.msgValue.1 != 0) = true from g)]
      exact .refused g
    | false =>
      unfold System.run
      rw [if_neg (by simp only [System.refuses] at g; simp only [g]; decide)]
      cases en : s.enter tx with
      | error e => exact .enterFail g en
      | ok σ =>
        simp only [bind, Except.bind]
        cases hr : (M.call a).run σ with
        | error e => exact .halt g en (by simp only [CallerStub.exec, hr, COut.ofRes])
        | ok o => exact .ok g en (by simp only [CallerStub.exec, hr, COut.ofRes])

theorem stepE_noCallback_iff {M : System C D A} {s t : World C} {a : Event A} :
    StepE (CallerStub.noCallback (C := C)).exec M s a t ↔ Step M s a t := by
  constructor
  · intro h
    cases h with
    | commit acc al run => exact .commit acc al (runE_noCallback_iff.1 run)
    | rollback acc al run failed => exact .rollback acc al (runE_noCallback_iff.1 run) failed
    | wait later => exact .wait later
  · intro h
    cases h with
    | commit acc al run => exact .commit acc al (runE_noCallback_iff.2 run)
    | rollback acc al run failed => exact .rollback acc al (runE_noCallback_iff.2 run) failed
    | wait later => exact .wait later

/-- **Under `noCallback` the reachable worlds are `Lifetime`'s.** -/
theorem reachableE_noCallback_iff {M : System C D A} {s : World C} :
    ReachableE (CallerStub.noCallback (C := C)).exec M s ↔ Reachable M s := by
  constructor
  · intro h
    induction h with
    | init deployed => exact .init deployed
    | step _ next ih => exact .step ih (stepE_noCallback_iff.1 next)
  · intro h
    induction h with
    | init deployed => exact .init deployed
    | step _ next ih => exact .step ih (stepE_noCallback_iff.2 next)

/-! ## The mode under a caller model -/

/-- The entry states of the worlds reachable under `E`. -/
def EntryStateE (E : Exec C) (M : System C D A) (σ : State C []) : Prop :=
  ∃ s tx, ReachableE E M s ∧ s.accepts tx ∧ s.enter tx = .ok σ

/-- **`Fml.Valid` at the entry states reachable under a caller model.** -/
def ValidStartE (E : Exec C) (M : System C D A) (φ : Fml C []) : Prop :=
  ∀ σ, EntryStateE E M σ → holds σ φ

/-- Under `noCallback` the mode is `ValidStart (.reachable M)`. -/
theorem validStartE_noCallback_iff {M : System C D A} {φ : Fml C []} :
    ValidStartE (CallerStub.noCallback (C := C)).exec M φ ↔ ValidStart (.reachable M) φ := by
  constructor
  · intro h σ ⟨s, tx, hs, acc, en⟩
    exact h σ ⟨s, tx, reachableE_noCallback_iff.2 hs, acc, en⟩
  · intro h σ ⟨s, tx, hs, acc, en⟩
    exact h σ ⟨s, tx, reachableE_noCallback_iff.1 hs, acc, en⟩

/-- What holds against a stronger attacker holds against a weaker one. -/
theorem ValidStartE.weaken {E₁ E₂ : Exec C} (hE : Exec.Le E₁ E₂) {M : System C D A}
    {φ : Fml C []} (h : ValidStartE E₂ M φ) : ValidStartE E₁ M φ :=
  fun σ ⟨s, tx, hs, acc, en⟩ => h σ ⟨s, tx, hs.mono hE, acc, en⟩

/-- Validity under a caller model from its invariant. -/
theorem ValidStartE.of_invariant {E : Exec C} {M : System C D A} {I : World C → Prop}
    {J φ : Fml C []} (hI : InvariantE E M I)
    (entry : ∀ s tx σ, I s → s.accepts tx → s.enter tx = .ok σ → holds σ J)
    (h : Fml.Valid (.imp J φ)) : ValidStartE E M φ :=
  fun σ ⟨s, tx, hs, acc, en⟩ => h σ (entry s tx σ (hI.always s hs) acc en)

/-! ## Clean tails under callbacks -/

/-- **Clean tails under callbacks**: a constructor that exposes nothing and
entries that keep clean tails across the callback boundary, the callee
assumed to keep them (`StateInv.cleanTail`). -/
theorem cleanTail_invariantE {M : System C D A} (hd : ∀ d, (M.deploy d).exposesNone = true)
    (hc : ∀ a, (M.call a).CleanTailCallbackBoundary) :
    InvariantE (CallerStub.withCallback (StateInv.cleanTail C)).exec M CleanWorld where
  initially := fun s hs => (cleanTail_invariant (M := { M with call := fun _ => .nil })
    ⟨hd, fun _ => rfl⟩).initially s hs
  preserved := by
    intro s t ev hi step
    cases step with
    | commit _ _ run =>
      cases run with
      | ok _ en run =>
        have hσ : _ := (World.enter_storage en) ▸ Storage.resetTransient_cleanTail hi
        exact Storage.resetTransient_cleanTail
          (Prog.cleanTailCallbackBoundary_exit (hc _) hσ run)
      | violated _ en run =>
        have hσ : _ := (World.enter_storage en) ▸ Storage.resetTransient_cleanTail hi
        exact absurd run (Prog.cleanTailCallbackBoundary_noViolation (hc _) hσ)
    | rollback => exact hi
    | wait => exact hi

/-- **`TailMode.clean` follows from reachability under callbacks.** -/
theorem _root_.Solidity.ValidTail.validStartE_withCallback {M : System C D A}
    (hd : ∀ d, (M.deploy d).exposesNone = true) (hc : ∀ a, (M.call a).CleanTailCallbackBoundary)
    {φ : Fml C []} (h : ValidTail .clean φ) :
    ValidStartE (CallerStub.withCallback (StateInv.cleanTail C)).exec M φ :=
  .of_invariant (cleanTail_invariantE hd hc)
    (fun _ _ _ hs _ en => holds_cleanTail_of
      ((World.enter_storage en) ▸ Storage.resetTransient_cleanTail hs)) h

end Solidity.Reachable
