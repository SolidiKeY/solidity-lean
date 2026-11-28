import Solidity.Theory.Reachable.CleanTail
import Solidity.Calculus.CleanTailBoundary


namespace Solidity.Reachable

open Lifetime

variable {C : Contract} {D A : Type}

abbrev Exec (C : Contract) := (σ : State C []) → Prog C [] [] → COut C σ.H [] → Prop

def Exec.Le (E₁ E₂ : Exec C) : Prop := ∀ σ P r, E₁ σ P r → E₂ σ P r

def Exec.top : Exec C := fun _ _ _ => True

theorem Exec.le_top (E : Exec C) : Exec.Le E Exec.top := fun _ _ _ _ => trivial

inductive CallerStub (C : Contract) where
  | noCallback
  | withCallback (J : StateInv C)

def CallerStub.exec : CallerStub C → Exec C
  | .noCallback => fun σ P r => r = COut.ofRes (P.run σ)
  | .withCallback J => fun σ P r => ExecP J σ P r

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

inductive ReachableE (E : Exec C) (M : System C D A) : World C → Prop where
  | init {s : World C} (deployed : M.Init s) : ReachableE E M s
  | step {s t : World C} {a : Event A} (before : ReachableE E M s)
      (next : StepE E M s a t) : ReachableE E M t

structure InvariantE (E : Exec C) (M : System C D A) (I : World C → Prop) : Prop where
  initially : ∀ s, M.Init s → I s
  preserved : ∀ {s t a}, I s → StepE E M s a t → I t

theorem InvariantE.always {E : Exec C} {M : System C D A} {I : World C → Prop}
    (h : InvariantE E M I) : ∀ s, ReachableE E M s → I s := by
  intro s hs
  induction hs with
  | init deployed => exact h.initially _ deployed
  | step _ next ih => exact h.preserved ih next


def Exec.LeOn (M : System C D A) (E₁ E₂ : Exec C) : Prop :=
  ∀ a σ r, E₁ σ (M.call a) r → E₂ σ (M.call a) r

theorem Exec.Le.on {E₁ E₂ : Exec C} (h : Exec.Le E₁ E₂) (M : System C D A) :
    Exec.LeOn M E₁ E₂ :=
  fun _ _ _ => h _ _ _

theorem RunE.mono {E₁ E₂ : Exec C} {M : System C D A} (hE : Exec.LeOn M E₁ E₂) {s : World C}
    {a : A} {tx : TTx} {r : TRes (World C)} (h : RunE E₁ M s a tx r) : RunE E₂ M s a tx r :=
  match h with
  | .refused g => .refused g
  | .enterFail g en => .enterFail g en
  | .ok g en run => .ok g en (hE _ _ _ run)
  | .halt g en run => .halt g en (hE _ _ _ run)
  | .violated g en run r => .violated g en (hE _ _ _ run) r

theorem StepE.mono {E₁ E₂ : Exec C} {M : System C D A} (hE : Exec.LeOn M E₁ E₂) {s t : World C}
    {a : Event A} (h : StepE E₁ M s a t) : StepE E₂ M s a t :=
  match h with
  | .commit acc al run => .commit acc al (run.mono hE)
  | .rollback acc al run failed => .rollback acc al (run.mono hE) failed
  | .wait later => .wait later

theorem ReachableE.mono {E₁ E₂ : Exec C} {M : System C D A} (hE : Exec.LeOn M E₁ E₂)
    {s : World C} (h : ReachableE E₁ M s) : ReachableE E₂ M s := by
  induction h with
  | init deployed => exact .init deployed
  | step _ next ih => exact .step ih (next.mono hE)

theorem InvariantE.weaken {E₁ E₂ : Exec C} {M : System C D A} (hE : Exec.LeOn M E₁ E₂)
    {I : World C → Prop} (h : InvariantE E₂ M I) : InvariantE E₁ M I where
  initially := h.initially
  preserved := fun hi step => h.preserved hi (step.mono hE)


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


def EntryStateE (E : Exec C) (M : System C D A) (σ : State C []) : Prop :=
  ∃ s tx a, ReachableE E M s ∧ s.accepts tx ∧ M.refuses a tx = false ∧ M.allowCall s a tx ∧
    s.enter tx = .ok σ

def ValidStartE (E : Exec C) (M : System C D A) (φ : Fml C []) : Prop :=
  ∀ σ, EntryStateE E M σ → holds σ φ

theorem validStartE_noCallback_iff {M : System C D A} {φ : Fml C []} :
    ValidStartE (CallerStub.noCallback (C := C)).exec M φ ↔ ValidStart (.reachable M) φ := by
  constructor
  · intro h σ ⟨s, tx, a, hs, rest⟩
    exact h σ ⟨s, tx, a, reachableE_noCallback_iff.2 hs, rest⟩
  · intro h σ ⟨s, tx, a, hs, rest⟩
    exact h σ ⟨s, tx, a, reachableE_noCallback_iff.1 hs, rest⟩

theorem ValidStartE.weaken {E₁ E₂ : Exec C} {M : System C D A} (hE : Exec.LeOn M E₁ E₂)
    {φ : Fml C []} (h : ValidStartE E₂ M φ) : ValidStartE E₁ M φ :=
  fun σ ⟨s, tx, a, hs, rest⟩ => h σ ⟨s, tx, a, hs.mono hE, rest⟩

theorem ValidStartE.of_invariant {E : Exec C} {M : System C D A} {I : World C → Prop}
    {J φ : Fml C []} (hI : InvariantE E M I)
    (entry : ∀ s tx a σ, I s → s.accepts tx → M.refuses a tx = false → M.allowCall s a tx →
      s.enter tx = .ok σ → holds σ J)
    (h : Fml.Valid (.imp J φ)) : ValidStartE E M φ :=
  fun σ ⟨s, tx, a, hs, acc, g, al, en⟩ => h σ (entry s tx a σ (hI.always s hs) acc g al en)

theorem exec_noCallback_iff_withCallback {J : StateInv C} {σ : State C []} {P : Prog C [] []}
    (hc : Prog.callsBack J.pay P = false) {r : COut C σ.H []} :
    (CallerStub.noCallback (C := C)).exec σ P r ↔ (CallerStub.withCallback J).exec σ P r := by
  constructor
  · intro h
    simp only [CallerStub.exec] at h ⊢
    subst h
    exact ExecP.of_run hc
  · intro h
    exact ExecP.eq_run h hc

theorem leOn_of_callsBack {M : System C D A} {J : StateInv C}
    (hc : ∀ a, Prog.callsBack J.pay (M.call a) = false) :
    Exec.LeOn M (CallerStub.noCallback (C := C)).exec (CallerStub.withCallback J).exec ∧
      Exec.LeOn M (CallerStub.withCallback J).exec (CallerStub.noCallback (C := C)).exec :=
  ⟨fun a _ _ h => (exec_noCallback_iff_withCallback (hc a)).1 h,
   fun a _ _ h => (exec_noCallback_iff_withCallback (hc a)).2 h⟩


def KeepsCleanC (P : Prog C [] []) : Prop :=
  ∀ σ : State C [], σ.storage.CleanTail → ∀ o, ExecP (StateInv.cleanTail C) σ P o →
    match o with
    | .ok o' => o'.st.storage.CleanTail
    | .halt _ => True
    | .violated => False

theorem KeepsCleanC.of_boundary {P : Prog C [] []} (h : P.CleanTailCallbackBoundary) :
    KeepsCleanC P := by
  intro σ hσ o ho
  have hb := h σ hσ o ho
  cases o with
  | ok o' => exact hb
  | halt e => trivial
  | violated => exact hb

theorem KeepsCleanC.of_run {P : Prog C [] []} (hc : Prog.callsBack true P = false)
    (he : P.exposesNone = true) : KeepsCleanC P := by
  intro σ hσ o ho
  have heq := ExecP.eq_run ho hc
  subst heq
  cases hr : Prog.run σ P with
  | ok o' =>
    simp only [COut.ofRes]
    exact Prog.run_cleanTail P he hσ rfl hr
  | error e => simp only [COut.ofRes]

theorem cleanTail_invariantE {M : System C D A} (hd : ∀ d, (M.deploy d).exposesNone = true)
    (hc : ∀ a, KeepsCleanC (M.call a)) :
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
        exact Storage.resetTransient_cleanTail (hc _ _ hσ _ run)
      | violated _ en run =>
        have hσ : _ := (World.enter_storage en) ▸ Storage.resetTransient_cleanTail hi
        exact (hc _ _ hσ _ run).elim
    | rollback => exact hi
    | wait => exact hi

theorem _root_.Solidity.ValidTail.validStartE_withCallback {M : System C D A}
    (hd : ∀ d, (M.deploy d).exposesNone = true) (hc : ∀ a, KeepsCleanC (M.call a))
    {φ : Fml C []} (h : ValidTail .clean φ) :
    ValidStartE (CallerStub.withCallback (StateInv.cleanTail C)).exec M φ :=
  .of_invariant (cleanTail_invariantE hd hc)
    (fun _ _ _ _ hs _ _ _ en => holds_cleanTail_of
      ((World.enter_storage en) ▸ Storage.resetTransient_cleanTail hs)) h

end Solidity.Reachable
