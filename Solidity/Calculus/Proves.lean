import Solidity.Calculus.Taclet
import Solidity.Calculus.FirstOrder
import Solidity.Calculus.Graft
import Solidity.Calculus.Hyp
import Solidity.Calculus.SeqRewrite

/-!
# Sequents on scoped formulas: the skeleton

`Logic.lean`'s judgement `Γ ⊢ φ` over the scoped formulas of
`Calculus/Fml.lean` (`docs/intrinsic.md`, M6a): the context is a
telescope (`Hyps C Γ₀ Γ`), each entry read where the ones before it leave,
so an update that declares a local, a `∀` and the hidden binder extend the
scope of what follows them, and the goal is a formula of the last scope.

The rules are stated, one per kind of premise, as `Proves` has them today,
under solkey's names where solkey has the rule:

* `intro` (`impRight`), `allIntro` (`allRight`), `updIntro`, `bindIntro`
  (the hidden binder, Lean only: it puts the local of `T v = e;` in scope);
* `update`, `updates`, `unfold`, `bind`, `split`, `check`, `done`, `branches`,
  `cases`, `inv`, `inline`: a taclet's premise in front of the rest `ω` and
  the frames `κ` (`Premise.fml`, its parts apart), one goal per conjunct.
  `split` has KeY's two goals, under either modality: a `bool` local of
  the typed state holds a `bool`, so one of a branch's conditions holds and
  no third goal covers a stuck one;
* `empty` (`emptyModality`): a finished program goes through its frames
  (`Frames.exit`), a scope end a popping update, which `updIntro` takes;
* `closeTrue`, behind a context with no diamond update but scope ends
  (`Hyps.boxOnly`);
* `closeFalse`: a context that refutes itself closes any goal, the shape
  of KeY's `cut` on `false` and `closeFalse`; `sol_prove` closes a split's branch so when its
  condition is ground under the context (`Calculus/ProvesDerive.lean`);
* the rules on the context's updates: `merge`
  (`sequentialToParallel`, over a storage write too, KeY's `mergeStorage`;
  past the hidden binders between the two updates) and `updRw` (a term
  taclet in the last box update's right-hand sides), both while a modality
  may still be open (`Calculus/Graft.lean`);
* `rewrite`: a Theory equation (a term taclet's, `TermTaclet.sound`) in
  every equation of the sequent, its context's preconditions and its goal,
  at any depth and under a modality still open (`Fml.rwEqC`,
  `Calculus/SeqRewrite.lean`): today's `Proves.rewrite`, the closer's
  rewrite, on the scoped sequent (decision 90);
* `closeHolds`: a sequent with no modality left, proved over the typed
  reading (`sol_leaf`, `Proves.closeValid`); the steps after the program
  (`Proves.eqDSplit`, `definedWritten`, `applyOnRigidBox`, `simplify`, the
  rewrites of the goal) are derived from it (`Calculus/UpdateRules.lean`).

A program rule fires the rule the strategy fires (`Stmt.step`, one per
statement): its premise is `s.step k m = p`, which `rfl` proves and
`Taclet.step_eq` gives from a named taclet (`Calculus/Taclet.lean`).
The rule must be one of `R`'s (`hR : R.admits m s = true`, last, proved by
default): every rule under `.all`; under `.solkey` the statement must be one
whose rule is solkey's (`Stmt.keyStep`: no argument to capture, no payment
or `try` under the diamond, no exhausted unwinding bound), so a derivation of `⊢ₖ` fires
`Taclet`s alone (`Stmt.taclet_of_admits`,
`Calculus/SolkeyFragment.lean`; decision 36).  `Stmt.stepIn` is the
step with `R`'s rules, the walk's (`Calculus/ProvesDerive.lean`).
The fresh index `k` is one above every index in the sequent
(`Hyps.fresh`).  `Hyps.wrap` is written with
`casesOn` (Gate G0, condition 1): the kernel evaluates it when it checks
that index.

Soundness is `Calculus/ProvesSound.lean` (the structure) and
`Calculus/Sound.lean` (the rules).
-/

namespace Solidity

open Solidity (Modality RuleSet)

variable {C : Contract}

/-- Whether the rule `Stmt.step` fires on `s` under `m` is one of solkey's
(`Taclet`), read off the statement alone: a call with an argument to capture
(`functionCallArgCapture`), a payment or a `try` under the diamond
(`transferDiamond`, `tryCallDiamond`), an exhausted loop bound (`loopExit`)
and unsupported invariant shapes have Lean's rules only (`LeanTaclet.keyStep`).
Automatic and positive-bound loops use `whileUnwind`; framed invariants use
the upstream box rule, or its diamond rule when a variant is supplied. -/
def Stmt.keyStep (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Bool :=
  Stmt.casesOn (motive_1 := fun _ _ _ => Bool) s
    (assign := fun _ r => !r.isMemory && !r.isFixedCopy) (rebind := fun _ _ => true) (assignLocal := fun _ v => !v.isModular)
    (declLocal := fun _ _ _ => true) (declStorage := fun _ _ _ => true)
    (opAssign := fun _ _ _ _ _ => true) (incDec := fun _ _ _ => true)
    (assignIncDec := fun _ _ _ _ _ => true) (assignLocalPush := fun _ _ => true)
    (push := fun b v _ => v.elim true Src.keyPushSource || !b.isSimple) (pop := fun _ => true)
    (transfer := fun _ _ => m == .box) (send := fun _ _ _ => true)
    (declMem := fun _ _ _ _ _ => true) (rebindMem := fun _ _ => true)
    (assignFromMem := fun _ _ => true) (assignMem := fun _ _ => true) (delete := fun _ => true)
    (deleteMem := fun _ _ => true) (assignNew := fun _ _ _ => true)
    (ite := fun _ _ _ => true) (require := fun _ => true) (assert := fun _ => true)
    (revert := true) (call := fun _ args _ _ => (Args.capture args).isNone)
    (tryCall := fun _ _ _ _ _ _ _ => m == .box)
    (loop := fun a _ body => match a with
      | .auto | .unwind (_ + 1) => true
      | .unwind 0 => false
      | .inv _ dec _ qs => body.frame.isSome && (m == .box || (dec.isSome && qs.isEmpty)))
    (block := fun _ => true)
    (pushOpAssign := fun _ _ _ b r => !r.isSimple || b.isSimple)
    (pushIncDec := fun _ _ b => b.isSimple)
    (callReceiver := fun _ _ _ _ _ => true)
    (callReceiverPush := fun _ _ _ _ _ _ => true)

/-- Whether the rule set `R` has the rule `Stmt.step` fires on `s` under `m`:
`.all` every rule, `.solkey` solkey's (`Stmt.keyStep`). -/
def _root_.Solidity.RuleSet.admits (R : RuleSet) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') :
    Bool :=
  RuleSet.casesOn (motive := fun _ => Bool) R (s.keyStep m) true

/-- The step of `s` with the rules of `R`: `Stmt.step`'s premise where `R`
has its rule (`RuleSet.admits`), none where it does not. -/
def Stmt.stepIn (R : RuleSet) (k : Nat) (m : Modality) {Γ Γ' : Ctx}
    (s : Stmt C Γ Γ') : Option (Premise C Γ Γ') :=
  match R with
  | .solkey => cond (s.keyStep m) (some (s.step k m)) none
  | .all => some (s.step k m)

/-- A step with the rules of `R` is the strategy's. -/
theorem Stmt.step_of_stepIn {R : RuleSet} {k : Nat} {m : Modality} {Γ Γ' : Ctx}
    {s : Stmt C Γ Γ'} {p : Premise C Γ Γ'} (h : s.stepIn R k m = some p) : s.step k m = p := by
  cases R with
  | all => exact Option.some.inj h
  | solkey =>
    cases hk : s.keyStep m with
    | true => simpa only [Stmt.stepIn, hk, cond_true, Option.some.injEq] using h
    | false => simp only [Stmt.stepIn, hk, cond_false, reduceCtorEq] at h

/-- A step with the rules of `R` is one `R` has the rule of. -/
theorem Stmt.admits_of_stepIn {R : RuleSet} {k : Nat} {m : Modality} {Γ Γ' : Ctx}
    {s : Stmt C Γ Γ'} {p : Premise C Γ Γ'} (h : s.stepIn R k m = some p) : R.admits m s = true := by
  cases R with
  | all => rfl
  | solkey =>
    cases hk : s.keyStep m with
    | true => exact hk
    | false => simp only [Stmt.stepIn, hk, cond_false, reduceCtorEq] at h

/-- The strategy's step is one with the rules of `R` where `R` has the rule. -/
theorem Stmt.stepIn_of_step {R : RuleSet} {k : Nat} {m : Modality} {Γ Γ' : Ctx}
    {s : Stmt C Γ Γ'} {p : Premise C Γ Γ'} (hR : R.admits m s = true) (h : s.step k m = p) :
    s.stepIn R k m = some p := by
  cases R with
  | all => exact congrArg some h
  | solkey =>
    have hk : s.keyStep m = true := hR
    simp only [Stmt.stepIn, hk, cond_true, h]

/-- **A rule solkey does not have fires only where `Stmt.keyStep` says so.** -/
theorem LeanTaclet.keyStep {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (d : LeanTaclet C k m s p) : s.keyStep m = false := by
  cases d with
  | functionCallArgCapture hcap =>
    show (Args.capture _).isNone = false
    rw [hcap]; rfl
  | pushCompoundUnfoldReceiver h => exact h
  | pushIncrementUnfoldReceiver h => exact h
  | storageMemorySourceSave hmem =>
    simp only [Stmt.keyStep, hmem, Bool.not_true, Bool.false_and]
  | storageFixedCopySave hshape =>
    simp only [Stmt.keyStep, hshape, Bool.not_true, Bool.and_false]
  | pushFixedCopySave hshape hsp =>
    simp only [Stmt.keyStep, Option.elim, Src.keyPushSource_ofFixedCopy hshape, hsp,
      Bool.not_true, Bool.false_or]
  | pushMemorySourceCapture hsp hnmp =>
    simp only [Stmt.keyStep, Option.elim, Src.keyPushSource, hnmp, hsp,
      Bool.not_true, Bool.false_or]
  | whileClose hf => simp only [Stmt.keyStep, hf, Option.isSome_none, Bool.false_and]
  | whileNoVariantDiamond _ hd =>
    cases ‹Option (Val C Γ .uint)› <;> cases ‹List (LoopQ C Γ)› <;>
      simp_all only [Stmt.keyStep, Option.isNone, Option.isSome, List.isEmpty, Bool.false_eq_true,
        Bool.false_or, Bool.or_false, Bool.and_false, Bool.and_true, Bool.not_true,
        Bool.not_false, Bool.true_or] <;> rfl
  | _ => rfl

/-- The default proof of a step rule's `hR`: `RuleSet.admits` of a closed
statement reduces (`rfl`), or is decided. -/
macro "rule_admits" : tactic => `(tactic| first | rfl | decide)

/-- The context of a sequent, from the scope `Γ₀` of the whole goal to the
scope `Γ` of its last formula. -/
inductive Hyps (C : Contract) (Γ₀ : Ctx) : Ctx → Type where
  | nil : Hyps C Γ₀ Γ₀
  /-- `a → …` -/
  | pre {Γ : Ctx} (H : Hyps C Γ₀ Γ) (a : Fml C Γ) : Hyps C Γ₀ Γ
  /-- `{U} …`, produced under the modality `m`: its declarations extend
  the scope. -/
  | upd {Γ Δ : Ctx} (H : Hyps C Γ₀ Γ) (m : Modality) (U : Upd C Γ Δ) : Hyps C Γ₀ Δ
  /-- `{havoc} …` -/
  | havoc {Γ : Ctx} (H : Hyps C Γ₀ Γ) : Hyps C Γ₀ Γ
  /-- `∀ p x. …`, KeY's skolem constant for `x`. -/
  | all {Γ : Ctx} (H : Hyps C Γ₀ Γ) (x : Var) (p : PrimTy) : Hyps C Γ₀ (.val p :: Γ)
  /-- The hidden binder: the local `x` a declaration put in scope under `m`,
  any value of its type. -/
  | bind {Γ : Ctx} (H : Hyps C Γ₀ Γ) (m : Modality) (x : Var) (t : LTy) : Hyps C Γ₀ (t :: Γ)
  /-- `{anon(xs)} …` -/
  | anon {Γ : Ctx} (H : Hyps C Γ₀ Γ) (xs : List ((t : LTy) × Idx Γ t)) : Hyps C Γ₀ Γ

/-- The hidden binders `bs` joined to the context, the first one first. -/
def Hyps.binds {Γ₀ : Ctx} : {Γ : Ctx} → Hyps C Γ₀ Γ → (bs : List (Modality × Var × LTy)) →
    Hyps C Γ₀ (Binds.ctx bs Γ)
  | _, H, [] => H
  | _, H, (m, x, t) :: bs => Hyps.binds (H.bind m x t) bs

/-- No modality: what `closeHolds` leaves the calculus with. -/
def Fml.modalFree : {Γ : Ctx} → Fml C Γ → Bool
  | _, φ => Fml.casesOn (motive := fun _ _ => Bool) φ
    (tt := true) (eq := fun _ _ => true) (defined := fun _ => true)
    (not := fun φ => Fml.modalFree φ) (and := fun φ ψ => Fml.modalFree φ && Fml.modalFree ψ)
    (imp := fun φ ψ => Fml.modalFree φ && Fml.modalFree ψ) (upd := fun _ _ φ => Fml.modalFree φ)
    (modal := fun _ _ _ _ => false) (havoc := fun φ => Fml.modalFree φ)
    (all := fun _ _ φ => Fml.modalFree φ) (bind := fun _ _ _ φ => Fml.modalFree φ)
    (anon := fun _ φ => Fml.modalFree φ)
  termination_by structural _ φ => φ

/-- The context put back in front of a formula. -/
def Hyps.wrap {Γ₀ : Ctx} : {Γ : Ctx} → Hyps C Γ₀ Γ → Fml C Γ → Fml C Γ₀
  | _, H, φ => Hyps.casesOn (motive := fun Γ _ => Fml C Γ → Fml C Γ₀) H
      (fun φ => φ)
      (fun H a φ => Hyps.wrap H (.imp a φ))
      (fun H m U φ => Hyps.wrap H (.upd m U φ))
      (fun H φ => Hyps.wrap H (.havoc φ))
      (fun H x p φ => Hyps.wrap H (.all x p φ))
      (fun H m x t φ => Hyps.wrap H (.bind m x t φ))
      (fun H xs φ => Hyps.wrap H (.anon xs φ)) φ
  termination_by structural _ H => H

/-- The fresh index of a step on the goal `φ`: one above every index in the
sequent. -/
def Hyps.fresh {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ) (φ : Fml C Γ) : Nat := (H.wrap φ).fresh

/-- The update only pops: scope ends, which always terminate. -/
def Upd.popsOnly {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, U => Upd.casesOn (motive := fun _ _ => Bool) U true
      (fun _ _ => false) (fun _ _ _ => false) (fun U _ => Upd.popsOnly U)
      (fun U _ => Upd.popsOnly U)
  termination_by structural _ U => U

/-- No update of the context was produced under the diamond, but scope
ends (`Upd.popsOnly`).  A hidden binder is universal under both modalities
(`Modality.forallB`), so it asks nothing. -/
def Hyps.boxOnly {Γ₀ : Ctx} : {Γ : Ctx} → Hyps C Γ₀ Γ → Bool
  | _, H => Hyps.casesOn (motive := fun _ _ => Bool) H true
      (fun H _ => Hyps.boxOnly H)
      (fun H m U => match m with
        | .diamond => U.popsOnly && Hyps.boxOnly H
        | .box => Hyps.boxOnly H)
      (fun H => Hyps.boxOnly H) (fun H _ _ => Hyps.boxOnly H)
      (fun H _ _ _ => Hyps.boxOnly H)
      (fun H _ => Hyps.boxOnly H)
  termination_by structural _ H => H

/-- `{anon(xs)}`, and `{anon(xs)} {havoc}` when the loop's frame writes the
storage too (`Fml.anonHavoc`), joined to the context. -/
def Hyps.anonHavoc {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ) (xs : List ((t : LTy) × Idx Γ t)) (hv : Bool) :
    Hyps C Γ₀ Γ :=
  if hv then (H.anon xs).havoc else H.anon xs

/-- `Hyps.rwEqC`'s compiled twin. -/
def Hyps.rwEqCM {p : PrimTy} (q : Tm C [] (.val p) × Tm C [] (.val p)) {Γ₀ : Ctx} :
    {Γ : Ctx} → Hyps C Γ₀ Γ → Hyps C Γ₀ Γ
  | _, .nil => .nil
  | _, .pre H a => .pre (Hyps.rwEqCM q H) (a.rwEqCM q)
  | _, .upd H m U => .upd (Hyps.rwEqCM q H) m U
  | _, .havoc H => .havoc (Hyps.rwEqCM q H)
  | _, .all H x p => .all (Hyps.rwEqCM q H) x p
  | _, .bind H m x t => .bind (Hyps.rwEqCM q H) m x t
  | _, .anon H xs => .anon (Hyps.rwEqCM q H) xs

/-- A Theory rewrite of the context (`Fml.rwEqC`): in every precondition;
an update, a `havoc`, a quantifier or a binder stays as it is.  By the
recursor, as `Fml.rwEqC`
(`Calculus/SeqRewrite.lean`). -/
@[implemented_by Hyps.rwEqCM]
def Hyps.rwEqC {p : PrimTy} (q : Tm C [] (.val p) × Tm C [] (.val p)) {Γ₀ Γ : Ctx}
    (H : Hyps C Γ₀ Γ) :
    Hyps C Γ₀ Γ :=
  Hyps.rec (motive := fun Γ _ => Hyps C Γ₀ Γ) .nil (fun _ a ih => .pre ih (a.rwEqC q))
    (fun _ m U ih => .upd ih m U) (fun _ ih => .havoc ih) (fun _ x p ih => .all ih x p)
    (fun _ m x t ih => .bind ih m x t) (fun _ xs ih => .anon ih xs) H

/-- The recursor's rewrite is the twin's. -/
theorem Hyps.rwEqC_eq_rwEqCM {p : PrimTy} (q : Tm C [] (.val p) × Tm C [] (.val p)) {Γ₀ Γ : Ctx}
    (H : Hyps C Γ₀ Γ) : H.rwEqC q = H.rwEqCM q := by
  induction H with
  | nil => rfl
  | pre H a ih => simp only [Hyps.rwEqCM, ← ih, ← Fml.rwEqC_eq_rwEqCM]; rfl
  | upd H m U ih | havoc H ih | all H x p ih | bind H m x t ih | anon H xs ih =>
    simp only [Hyps.rwEqCM, ← ih]; rfl

/-- `H ⊢ φ`: the calculus proves `φ` in the context `H` (with `R`, solkey's
rules alone or all of them). -/
inductive Proves (C : Contract) (R : RuleSet) (Γ₀ : Ctx) :
    {Γ : Ctx} → Hyps C Γ₀ Γ → Fml C Γ → Prop where
  /-- `impRight`: the precondition moves into the context. -/
  | intro {Γ : Ctx} {H : Hyps C Γ₀ Γ} {a φ : Fml C Γ} (h : Proves C R Γ₀ (H.pre a) φ) :
      Proves C R Γ₀ H (.imp a φ)
  /-- `andRight`: a conjunction from each conjunct, in the same context; the
  walk takes it where a conjunct is still a program's (a loop body's
  `(¬broke → inv) ∧ (broke → ⟨[ ]⟩)`), the closer reads the others. -/
  | andIntro {Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ ψ : Fml C Γ} (h₁ : Proves C R Γ₀ H φ)
      (h₂ : Proves C R Γ₀ H ψ) : Proves C R Γ₀ H (.and φ ψ)
  /-- `allRight`: a quantified local joins the context. -/
  | allIntro {Γ : Ctx} {H : Hyps C Γ₀ Γ} {x : Var} {p : PrimTy} {φ : Fml C (.val p :: Γ)}
      (h : Proves C R Γ₀ (H.all x p) φ) : Proves C R Γ₀ H (.all x p φ)
  /-- An update in front of the formula joins the context. -/
  | updIntro {Γ Δ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ}
      (h : Proves C R Γ₀ (H.upd m U) φ) : Proves C R Γ₀ H (.upd m U φ)
  /-- The hidden binder joins the context (Lean only). -/
  | bindIntro {Γ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {x : Var} {t : LTy}
      {φ : Fml C (t :: Γ)} (h : Proves C R Γ₀ (H.bind m x t) φ) : Proves C R Γ₀ H (.bind m x t φ)
  /-- A taclet that produces an update: the update joins the context, the
  rest of the program goes on. -/
  | update {Γ Γ' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {U : Upd C Γ Γ'}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = .update U)
      (h : Proves C R Γ₀ (H.upd m U) (.modalK m ω κ φ))
      (hR : R.admits m s = true := by rule_admits) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- Two sequential updates join the context in order: the second can read
  the slot appended by `a.push()`. -/
  | updates {Γ Δ Γ' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
      {U : Upd C Γ Δ} {V : Upd C Δ Γ'}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = .updates U V)
      (h : Proves C R Γ₀ ((H.upd m U).upd m V) (.modalK m ω κ φ))
      (hR : R.admits m s = true := by rule_admits) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- `sp.push() /= se`: the zero-divisor branch encloses both updates. -/
  | guardedUpdates {Γ Δ Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality}
      {s : Stmt C Γ Γ} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
      {c : Fml C Γ} {U : Upd C Γ Δ} {V : Upd C Δ Γ}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = .guardedUpdates c U V)
      (thn : Proves C R Γ₀ (H.pre c) (.upd m U (.upd m V (.modalK m ω κ φ))))
      (els : Proves C R Γ₀ (H.pre (.not c)) (.modal m (.cons .revert ω) κ φ))
      (hR : R.admits m s = true := by rule_admits) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A taclet that produces statements: they replace the first one, their
  fresh locals popped after them (`pop .capture`). -/
  | unfold {Γ Γ' Γ'' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {P : Prog C Γ Γ''} {e : Ext Γ' Γ''}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = .unfold P e)
      (h : Proves C R Γ₀ H (.modal m P (.pop .capture e (.seq ω κ)) φ))
      (hR : R.admits m s = true := by rule_admits) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A declaration with its initializer dropped (`localValueDeclInitDrop`):
  the local joins the context, the assignment replaces the declaration. -/
  | bind {Γ Γ' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {x : Var} {t : LTy}
      {P : Prog C (t :: Γ) Γ'}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = .bind x t P)
      (h : Proves C R Γ₀ (H.bind m x t) (.modal m P (.seq ω κ) φ))
      (hR : R.admits m s = true := by rule_admits) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A taclet that branches: two goals, KeY's, each branch a block ended
  as the premise says (`}` for an `if`). -/
  | split {Γ Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {b : BlockKind} {c c' : Fml C Γ}
      {P : Prog C Γ Δ₁} {Q : Prog C Γ Δ₂}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = .split b c c' P Q)
      (thn : Proves C R Γ₀ (H.pre c) (.modalK m P (.pop b P.ext (.seq ω κ)) φ))
      (els : Proves C R Γ₀ (H.pre c') (.modalK m Q (.pop b Q.ext (.seq ω κ)) φ))
      (hR : R.admits m s = true := by rule_admits) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A taclet that checks (`assertSimple`): the goal with the condition
  assumed ("Holds"), and the condition ("Violated"). -/
  | check {Γ Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {c : Fml C Γ}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = .check c)
      (thn : Proves C R Γ₀ (H.pre c) (.modalK m ω κ φ)) (els : Proves C R Γ₀ H c)
      (hR : R.admits m s = true := by rule_admits) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A taclet that closes the modality (`revertBox`, `revertDiamond`). -/
  | done {Γ Γ' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {b : Bool}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = .done b)
      (h : Proves C R Γ₀ H (if b then .tt else .ff))
      (hR : R.admits m s = true := by rule_admits) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A taclet with a goal per way an external call may end
  (`tryCallNoCallbackBox`): each clause's block in the statement's place,
  for every value of the locals its outcome binds, its scope ended (`}`).
  There is at least one clause: a rule with no goal would prove its
  statement behind any context. -/
  | branches {Γ Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {bs : List (Branch C Γ)}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = .branches bs)
      (hne : bs.isEmpty = false)
      (h : ∀ b ∈ bs, Proves C R Γ₀ H
        (b.bs.all (.modalK m b.P (.pop .block ((Ext.append Γ b.ρ).trans b.P.ext) (.seq ω κ)) φ)))
      (hR : R.admits m s = true := by rule_admits) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A taclet with labelled goals (`sendNoCallbackBox`): each formula, then
  the rest after each update, one per way the statement may end. -/
  | cases {Γ Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {fs : List (Fml C Γ)}
      {us : List (Upd C Γ Γ)}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = .cases fs us)
      (hne : (fs.isEmpty && us.isEmpty) = false)
      (fml : ∀ f ∈ fs, Proves C R Γ₀ H f)
      (upd : ∀ U ∈ us, Proves C R Γ₀ (H.upd m U) (.modalK m ω κ φ))
      (hR : R.admits m s = true := by rule_admits) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A loop's invariant (`whileInvariantBox`, `whileInvariantDiamond`): the
  invariant now ("invariant initially valid"), and past the frame's
  anonymising update, the invariant and the condition's update, the body to
  its postcondition where the condition holds ("body preserves
  invariant"), the rest where it does not ("use case").  With a break test
  the iteration assumes `I ∧ ¬B` and a body that breaks goes on to the rest
  (`Fml.invHyp`, `Fml.invPost`). -/
  | inv {Γ Γ₁ Γ₂ Δ₀ Δ Γ₃ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {I : Fml C Γ} {B : Option (Fml C Γ)}
      {xs : List ((t : LTy) × Idx Γ t)} {hv : Bool} {U : Upd C Γ Δ} {c c' : Fml C Δ}
      {hu : Ext Γ Δ₀} {hb : Ext Δ₀ Δ} {P : Prog C Δ₀ Γ₃} {post : Fml C Δ₀}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m =
        .inv I B xs hv U c c' hu hb P post)
      (init : Proves C R Γ₀ H (I.invHyp B))
      (thn : Proves C R Γ₀ ((((H.anonHavoc xs hv).pre (I.invHyp B)).upd m U).pre c)
        (.upd m (Upd.nil.pop hb) (.modalK m P (.pop .block P.ext .nil)
          (Fml.invPost m hu ω κ φ post B))))
      (els : Proves C R Γ₀ ((((H.anonHavoc xs hv).pre (I.invHyp B)).upd m U).pre c')
        (.upd m (Upd.nil.pop (hu.trans hb)) (.modalK m ω κ φ)))
      (hR : R.admits m s = true := by rule_admits) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A taclet that produces a block whose end drops a frame from under the
  locals it keeps (`expand_function_body` of a call that leaves its return
  variables): the block replaces the statement. -/
  | inline {Γ Γ' Γ'' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {P : Prog C Γ Γ''} {e : Thin Γ' Γ''}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = .inline P e)
      (h : Proves C R Γ₀ H (.modal m P (.drop e (.seq ω κ)) φ))
      (hR : R.admits m s = true := by rule_admits) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- `emptyModality`: a finished program goes through its frames, the rest
  of the program next, a scope end a popping update. -/
  | empty {Γ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {κ : Frames C Γ Γ₂} {φ : Fml C Γ₂}
      (h : Proves C R Γ₀ H (κ.exit m φ)) : Proves C R Γ₀ H (.modal m .nil κ φ)
  /-- `closeTrue`, behind a context with no diamond update. -/
  | closeTrue {Γ : Ctx} {H : Hyps C Γ₀ Γ} (h : H.boxOnly = true) : Proves C R Γ₀ H .tt
  /-- `closeFalse`: a context that refutes itself closes any goal.  As
  today's `Proves.closeFalse`, KeY's `cut` on `false` followed by
  `closeFalse` on the TRUE goal; the FALSE goal, the context refuted, is the
  premise, which the closer proves.  A deviation in shape. -/
  | closeFalse {Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ} (h : Proves C R Γ₀ H .ff) :
      Proves C R Γ₀ H φ
  /-- **`sequentialToParallel`** (`merge`, and `mergeStorage` over a storage
  write): the last update and the one before it, past the hidden binders `bs`
  between them, as one parallel update, the later one read in the earlier
  one's state (`Upd.seqPar`); the earlier one moved under the binders, which
  print as nothing (`Upd.liftBinds?`, Lean only). -/
  | merge {Γ Δ Ε : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {bs : List (Modality × Var × LTy)}
      {U : Upd C Γ Δ} {U' : Upd C (Binds.ctx bs Γ) (Binds.ctx bs Δ)}
      {V : Upd C (Binds.ctx bs Δ) Ε} {W : Upd C (Binds.ctx bs Γ) Ε} {φ : Fml C Ε}
      (hU : U.liftBinds? bs = some U') (hW : U'.seqPar V = some W)
      (h : Proves C R Γ₀ ((H.binds bs).upd m W) φ) :
      Proves C R Γ₀ (((H.upd m U).binds bs).upd m V) φ
  /-- A term taclet `t ⇝ t'` in the right-hand sides of the last update, under
  the box, where `t'` returns wherever `t` does, the same value
  (`Tm.EvalRefines`; a Theory law onto a literal): today's `updRw`, its
  closed occurrences read at the empty scope (`Upd.rwC`). -/
  | updRw {Γ Δ : Ctx} {H : Hyps C Γ₀ Γ} {U : Upd C Γ Δ} {φ : Fml C Δ}
      {p : PrimTy} (q : Tm C [] (.val p) × Tm C [] (.val p)) (hq : Tm.EvalRefines q.1 q.2)
      (h : Proves C R Γ₀ (H.upd .box (U.rwC q)) φ) : Proves C R Γ₀ (H.upd .box U) φ
  /-- **A term taclet as a rewrite rule** (today's `Proves.rewrite`): a
  side of an equation that is a closed term reading `q.1` at the empty
  scope becomes `q.2`, in every equation of the sequent (`Hyps.rwEqC`,
  `Fml.rwEqC`), a modality still open or not.  `hq` is the Theory equation
  (`TermTaclet.sound` of a taclet, `TermTaclet.theory` of a law). -/
  | rewrite {Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ} {p : PrimTy}
      (q : Tm C [] (.val p) × Tm C [] (.val p))
      (hq : Tm.Theq q.1 q.2) (h : Proves C R Γ₀ (H.rwEqC q) (φ.rwEqC q)) :
      Proves C R Γ₀ H φ
  /-- Leave the calculus: with no modality left anywhere in the sequent
  (`Fml.modalFree`), what is left is proved over the typed reading.  The
  steps KeY takes after
  the program are derived from it (`Calculus/UpdateRules.lean`). -/
  | closeHolds {Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ} (h : ∀ σ, holds σ (H.wrap φ))
      (hm : (H.wrap φ).modalFree = true := by first | rfl | decide) : Proves C R Γ₀ H φ

/-! ## A derivation

`[ if (b) { } else { } ] true`, `b` a `bool` local: `ifElseSplit`, then in
each goal the block's end (an update that pops nothing, taken into the
context) and `closeTrue`. -/

example : Proves StandardExample .all [.val .bool] .nil
    (.modal .box (.cons (.ite (.simple (.local .here)) .nil .nil) .nil) .nil .tt) :=
  .split (Taclet.step_eq .ifElseSplit) (.updIntro (.closeTrue rfl)) (.updIntro (.closeTrue rfl))

/-- The diamond twin: a scope end pops, so `closeTrue` still fires in the two
branches, and there is no third goal. -/
example : Proves StandardExample .all [.val .bool] .nil
    (.modal .diamond (.cons (.ite (.simple (.local .here)) .nil .nil) .nil) .nil .tt) :=
  .split rfl (.updIntro (.closeTrue rfl)) (.updIntro (.closeTrue rfl))

end Solidity
