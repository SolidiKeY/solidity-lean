import Solidity.Update

/-!
# The callback semantics of `transfer`

KeY offers two semantics of `a.transfer(v);` (`transferSemantics`, solkey's
`docs/net.md`).  Without callbacks the recipient cannot run code, and the
transfer is the debit `Stmt.run` books.  **With callbacks** the recipient
may call back into the contract before control returns: the contract's
storage, its ledger `net` and its funds `selfBalance` are then whatever the
re-entrant code left, and all that is known of them is the **contract
invariant** `I`, which the contract owes whenever control leaves it (after
the debit) and may assume whenever control comes back.

A callback is nondeterministic, so it cannot live in the total interpreter.
This module is a *relational* layer over it (the removed untyped layer's
`ExecC`, here over the typed syntax and through branches and calls):
`ExecS I σ s o` runs `s` exactly as `Stmt.run` does, except at a `transfer`,
where the run either leaves the contract with `I` broken (`violated`, an
outcome no formula accepts) or resumes in any state the callee may leave
(`State.havoc`: storage, ledger and funds replaced, locals and memory kept)
that satisfies `I`.  `holdsC I` reads the modalities over it; everything else
is `holds`.  `TransferSem` names the two semantics, and `holdsT` is the
judgement parameterised by it.

What is proved here: the deterministic run is one of the callback runs
(`Prog.exec_run`), so a formula valid with callbacks is valid without
(`holds_of_holdsC_modal`); a program with no `transfer` has only its
deterministic run (`ExecP.eq_run`), so the two readings agree on it
(`holdsC_iff_holds`); and the relation respects agreement off scratch names
(`ExecP.frame`, `holdsC_frame`), which is what lets the ordinary rules run
under the callback reading (`Calculus/Callback.lean`).

The invariant is a formula with no locals (`Invariant`), as solkey's
`CInv(storage, net)` is a predicate of the storage and the ledger: whatever
the callee does to the contract's locals it cannot do, since it has none of
them.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## Outcomes -/

/-- How a run with callbacks ends: in a state, halted, or leaving the
contract with its invariant broken. -/
inductive COut where
  | ok (σ : State)
  | halt (e : Halt)
  | violated

/-- The outcome of a deterministic run. -/
def COut.ofRes : Res State → COut
  | .ok σ => .ok σ
  | .error e => .halt e

def COut.isOk : COut → Bool
  | .ok _ => true
  | _ => false

/-- `p` after a run under `m`: of the state it ends in, `m.onHalt` of a halt,
and never of a broken invariant. -/
def COut.after (m : Modality) (p : State → Prop) : COut → Prop
  | .ok τ => p τ
  | .halt _ => m.onHalt
  | .violated => False

@[simp] theorem COut.after_ofRes (m : Modality) (p : State → Prop) (r : Res State) :
    (COut.ofRes r).after m p = m.after p r := by
  cases r <;> rfl

/-! ## Which statements the callback reading sees -/

/-- The statements the relation does not take from `Stmt.run`: a `transfer`,
and the two that run others (`if`, a call). -/
def Stmt.forks : Stmt C → Bool
  | .transfer .. | .ite .. | .call .. => true
  | _ => false

mutual

/-- Whether a `transfer` occurs in the statement, in a branch or a callee
included. -/
def Stmt.hasTransfer : Stmt C → Bool
  | .transfer .. => true
  | .ite _ thn els => Prog.hasTransfer thn || Prog.hasTransfer els
  | .call _ _ _ _ body => Prog.hasTransfer body
  | _ => false

def Prog.hasTransfer : List (Stmt C) → Bool
  | [] => false
  | s :: P => s.hasTransfer || Prog.hasTransfer P

end

/-- Whether a `transfer` occurs in a program of the formula. -/
def Fml.hasTransfer : Fml C → Bool
  | .tt | .eq .. => false
  | .not φ | .upd _ _ φ | .havoc φ | .all _ _ φ => φ.hasTransfer
  | .and φ ψ | .imp φ ψ => φ.hasTransfer || ψ.hasTransfer
  | .modal _ P φ => Prog.hasTransfer P || φ.hasTransfer

/-- A contract invariant: a formula over the contract's state, with no local
and no payment in it (solkey's `CInv(storage, net)`),
`balance + paidOut == deposited`. -/
structure Invariant (C : Contract) where
  fml : Fml C
  closed : fml.vars = [] := by rfl
  noTransfer : fml.hasTransfer = false := by rfl

/-! ## Runs with callbacks -/

mutual

/-- `ExecS I σ s o`: run from `σ`, `s` may end in `o` when every `transfer`
may call back into a contract with invariant `I`. -/
inductive ExecS (I : Fml C) : State → Stmt C → COut → Prop where
  /-- A statement that runs no other and pays nothing runs as `Stmt.run`. -/
  | det {σ : State} {s : Stmt C} : s.forks = false → ExecS I σ s (.ofRes (s.run σ))
  /-- A transfer that halts (an unfunded one reverts). -/
  | transferHalt {σ : State} {r a : Val C .uint} {e : Halt} :
      (Stmt.transfer r a).run σ = .error e → ExecS I σ (.transfer r a) (.halt e)
  /-- KeY's "invariant on exit": control leaves with `I` broken. -/
  | transferViolated {σ σ₁ : State} {r a : Val C .uint} :
      (Stmt.transfer r a).run σ = .ok σ₁ → ¬ holds σ₁ I → ExecS I σ (.transfer r a) .violated
  /-- KeY's "resume after callback": control leaves with `I` kept and comes
  back to any state the callee may leave in which `I` holds. -/
  | transferResume {σ σ₁ : State} {r a : Val C .uint} {st : List (Name × SVal)}
      {nt : List (Int × Int)} {bal : Int} :
      (Stmt.transfer r a).run σ = .ok σ₁ → holds σ₁ I → holds (σ₁.havoc st nt bal) I →
        ExecS I σ (.transfer r a) (.ok (σ₁.havoc st nt bal))
  | iteHalt {σ : State} {c : Val C .bool} {thn els : List (Stmt C)} {e : Halt} :
      c.eval σ = .error e → ExecS I σ (.ite c thn els) (.halt e)
  | iteStuck {σ : State} {c : Val C .bool} {thn els : List (Stmt C)} {n : Int} :
      c.eval σ = .ok (.int n) → ExecS I σ (.ite c thn els) (.halt .stuck)
  | iteThen {σ : State} {c : Val C .bool} {thn els : List (Stmt C)} {o : COut} :
      c.eval σ = .ok (.bool true) → ExecP I σ thn o → ExecS I σ (.ite c thn els) o
  | iteElse {σ : State} {c : Val C .bool} {thn els : List (Stmt C)} {o : COut} :
      c.eval σ = .ok (.bool false) → ExecP I σ els o → ExecS I σ (.ite c thn els) o
  | callHalt {σ : State} {f : Name} {args : List (Arg C)} {hsep : Arg.separatedFrom [] args = true}
      {ret : CallRet} {body : List (Stmt C)} {e : Halt} :
      Arg.bindSeq args σ = .error e → ExecS I σ (.call f args hsep ret body) (.halt e)
  | callDone {σ σ₁ σ₂ : State} {f : Name} {args : List (Arg C)}
      {hsep : Arg.separatedFrom [] args = true} {ret : CallRet} {body : List (Stmt C)} :
      Arg.bindSeq args σ = .ok σ₁ → ExecP I (ret.enter σ₁) body (.ok σ₂) →
        ExecS I σ (.call f args hsep ret body) (.ofRes (CallRet.leave (C := C) σ₂ ret))
  | callStop {σ σ₁ : State} {f : Name} {args : List (Arg C)}
      {hsep : Arg.separatedFrom [] args = true} {ret : CallRet} {body : List (Stmt C)} {o : COut} :
      Arg.bindSeq args σ = .ok σ₁ → ExecP I (ret.enter σ₁) body o → o.isOk = false →
        ExecS I σ (.call f args hsep ret body) o

/-- `ExecP I σ P o`: the same, for a block. -/
inductive ExecP (I : Fml C) : State → List (Stmt C) → COut → Prop where
  | nil {σ : State} : ExecP I σ [] (.ok σ)
  | cons {σ σ₁ : State} {s : Stmt C} {P : List (Stmt C)} {o : COut} :
      ExecS I σ s (.ok σ₁) → ExecP I σ₁ P o → ExecP I σ (s :: P) o
  | stop {σ : State} {s : Stmt C} {P : List (Stmt C)} {o : COut} :
      ExecS I σ s o → o.isOk = false → ExecP I σ (s :: P) o

end

/-! ## Formulas read with callbacks -/

/-- Whether `φ` holds in `σ` when every `transfer` may call back into a
contract with invariant `I`: `holds`, but a modality ranges over every run
with callbacks, and none of them may break `I`. -/
def holdsC (I : Fml C) (σ : State) : Fml C → Prop
  | .tt => True
  | .eq a b => holds σ (.eq a b)
  | .not φ => ¬ holdsC I σ φ
  | .and φ ψ => holdsC I σ φ ∧ holdsC I σ ψ
  | .imp φ ψ => holdsC I σ φ → holdsC I σ ψ
  | .upd m U φ => m.after (holdsC I · φ) (U.apply σ)
  | .modal m P φ => ∀ o, ExecP I σ P o → o.after m (holdsC I · φ)
  | .havoc φ => ∀ st nt bal, holdsC I (σ.havoc st nt bal) φ
  | .all x p φ => ∀ v, p.admits v → holdsC I (σ.setEnv x (.val v)) φ

/-- Valid with callbacks: true in every state. -/
def ValidC (I : Invariant C) (φ : Fml C) : Prop := ∀ σ, holdsC I.fml σ φ

/-- The two semantics of `transfer` (KeY's `transferSemantics` option). -/
inductive TransferSem (C : Contract) where
  | noCallback
  | withCallback (I : Invariant C)

/-- **The judgement, parameterised by the transfer semantics**: `holds`
without callbacks, `holdsC` with them. -/
def holdsT : TransferSem C → State → Fml C → Prop
  | .noCallback => holds
  | .withCallback I => holdsC I.fml

/-- Valid under a transfer semantics. -/
def ValidT (ts : TransferSem C) (φ : Fml C) : Prop := ∀ σ, holdsT ts σ φ

theorem validT_noCallback {φ : Fml C} : ValidT .noCallback φ ↔ Valid φ := Iff.rfl

theorem validT_withCallback {I : Invariant C} {φ : Fml C} :
    ValidT (.withCallback I) φ ↔ ValidC I φ := Iff.rfl

/-! ## The deterministic run is a run with callbacks -/

mutual

/-- **The run `Stmt.run` makes is a callback run**, the callee changing
nothing — unless it leaves `I` broken on the way. -/
theorem Stmt.exec_run (I : Fml C) :
    (s : Stmt C) → ∀ σ, ExecS I σ s (.ofRes (s.run σ)) ∨ ExecS I σ s .violated
  | .transfer r a, σ => by
    cases h : (Stmt.transfer r a).run σ with
    | error e => exact .inl (.transferHalt h)
    | ok σ₁ =>
      by_cases hI : holds σ₁ I
      · left
        have := ExecS.transferResume (I := I) (st := σ₁.storage) (nt := σ₁.net)
          (bal := σ₁.selfBalance) h hI (by simpa using hI)
        simpa using this
      · exact .inr (.transferViolated h hI)
  | .ite c thn els, σ => by
    cases hc : c.eval σ with
    | error e =>
      left
      have : (Stmt.ite c thn els).run σ = .error e := by simp [Stmt.run, hc, bind, Except.bind]
      rw [this]; exact .iteHalt hc
    | ok v =>
      rcases v with n | (_ | _)
      · left
        have : (Stmt.ite c thn els).run σ = .error .stuck := by
          simp [Stmt.run, hc, bind, Except.bind]
        rw [this]; exact .iteStuck hc
      · have : (Stmt.ite c thn els).run σ = Prog.run σ els := by
          simp [Stmt.run, hc, bind, Except.bind]
        rw [this]
        rcases Prog.exec_run I els σ with h | h
        · exact .inl (.iteElse hc h)
        · exact .inr (.iteElse hc h)
      · have : (Stmt.ite c thn els).run σ = Prog.run σ thn := by
          simp [Stmt.run, hc, bind, Except.bind]
        rw [this]
        rcases Prog.exec_run I thn σ with h | h
        · exact .inl (.iteThen hc h)
        · exact .inr (.iteThen hc h)
  | .call f args hsep ret body, σ => by
    cases hb : Arg.bindSeq args σ with
    | error e =>
      left
      have : (Stmt.call f args hsep ret body).run σ = .error e := by
        simp [Stmt.run, hb, bind, Except.bind]
      rw [this]; exact .callHalt hb
    | ok σ₁ =>
      rcases Prog.exec_run I body (ret.enter σ₁) with h | h
      · cases hr : Prog.run (ret.enter σ₁) body with
        | error e =>
          rw [hr] at h
          left
          have : (Stmt.call f args hsep ret body).run σ = .error e := by
            simp [Stmt.run, hb, hr, bind, Except.bind]
          rw [this]; exact .callStop hb h rfl
        | ok σ₂ =>
          rw [hr] at h
          left
          have : (Stmt.call f args hsep ret body).run σ = CallRet.leave (C := C) σ₂ ret := by
            simp [Stmt.run, hb, hr, bind, Except.bind]
          rw [this]; exact .callDone hb h
      · exact .inr (.callStop hb h rfl)
  | .assign .., σ | .rebind .., σ | .assignLocal .., σ | .declLocal .., σ | .declStorage .., σ
  | .opAssign .., σ | .incDec .., σ | .assignIncDec .., σ | .push .., σ | .pop .., σ
  | .declMem .., σ | .rebindMem .., σ | .assignFromMem .., σ | .assignMem .., σ | .delete .., σ
  | .deleteMem .., σ | .assignNew .., σ | .require .., σ | .assert .., σ | .revert, σ =>
    .inl (.det rfl)

/-- The same, for a block. -/
theorem Prog.exec_run (I : Fml C) :
    (P : List (Stmt C)) → ∀ σ, ExecP I σ P (.ofRes (Prog.run σ P)) ∨ ExecP I σ P .violated
  | [], σ => .inl .nil
  | s :: P, σ => by
    rcases Stmt.exec_run I s σ with h | h
    · cases hs : s.run σ with
      | error e =>
        rw [hs] at h
        left
        have : Prog.run σ (s :: P) = .error e := by simp [Prog.run, hs, bind, Except.bind]
        rw [this]; exact .stop h rfl
      | ok σ₁ =>
        rw [hs] at h
        have : Prog.run σ (s :: P) = Prog.run σ₁ P := by simp [Prog.run, hs, bind, Except.bind]
        rw [this]
        rcases Prog.exec_run I P σ₁ with h' | h'
        · exact .inl (.cons h h')
        · exact .inr (.cons h h')
    · exact .inr (.stop h rfl)

end

/-! ## With no `transfer`, the run is the deterministic one -/

mutual

theorem ExecS.eq_run {I : Fml C} {σ : State} {s : Stmt C} {o : COut} :
    ExecS I σ s o → s.hasTransfer = false → o = .ofRes (s.run σ)
  | .det _, _ => rfl
  | .transferHalt _, h | .transferViolated _ _, h | .transferResume _ _ _, h => by
    simp [Stmt.hasTransfer] at h
  | .iteHalt hc, _ => by simp [Stmt.run, hc, bind, Except.bind, COut.ofRes]
  | .iteStuck hc, _ => by simp [Stmt.run, hc, bind, Except.bind, COut.ofRes]
  | .iteThen hc hp, h => by
    simp only [Stmt.hasTransfer, Bool.or_eq_false_iff] at h
    rw [ExecP.eq_run hp h.1]
    simp [Stmt.run, hc, bind, Except.bind]
  | .iteElse hc hp, h => by
    simp only [Stmt.hasTransfer, Bool.or_eq_false_iff] at h
    rw [ExecP.eq_run hp h.2]
    simp [Stmt.run, hc, bind, Except.bind]
  | .callHalt hb, _ => by simp [Stmt.run, hb, bind, Except.bind, COut.ofRes]
  | .callDone (ret := ret) (body := body) hb hp, h => by
    have := ExecP.eq_run hp h
    simp only [Stmt.run, hb, bind, Except.bind]
    cases hr : Prog.run (ret.enter _) body with
    | error e => rw [hr] at this; simp [COut.ofRes] at this
    | ok τ =>
      rw [hr] at this
      simp only [COut.ofRes, COut.ok.injEq] at this
      subst this
      rfl
  | .callStop hb hp ho, h => by
    have := ExecP.eq_run hp h
    subst this
    simp only [Stmt.run, hb, bind, Except.bind]
    cases hr : Prog.run _ _ <;> simp_all [COut.ofRes, COut.isOk]

theorem ExecP.eq_run {I : Fml C} {σ : State} {P : List (Stmt C)} {o : COut} :
    ExecP I σ P o → Prog.hasTransfer P = false → o = .ofRes (Prog.run σ P)
  | .nil, _ => rfl
  | .cons hs hp, h => by
    simp only [Prog.hasTransfer, Bool.or_eq_false_iff] at h
    have h₁ := ExecS.eq_run hs h.1
    have h₂ := ExecP.eq_run hp h.2
    cases hr : Stmt.run _ _ with
    | error e => rw [hr] at h₁; cases h₁
    | ok τ =>
      rw [hr] at h₁
      cases h₁
      simp [Prog.run, hr, bind, Except.bind, h₂]
  | .stop hs ho, h => by
    simp only [Prog.hasTransfer, Bool.or_eq_false_iff] at h
    have h₁ := ExecS.eq_run hs h.1
    subst h₁
    cases hr : Stmt.run _ _ with
    | error e => simp [Prog.run, hr, bind, Except.bind, COut.ofRes]
    | ok τ => simp [hr, COut.ofRes, COut.isOk] at ho

end

/-- The empty program: its one run ends where it starts. -/
theorem holdsC_modal_nil {I : Fml C} {σ : State} {m : Modality} {φ : Fml C} :
    holdsC I σ (.modal m [] φ) ↔ holdsC I σ φ := by
  simp only [holdsC]
  exact ⟨fun h => h _ .nil, fun h o he => by cases he; exact h⟩

/-- A statement that runs no other and pays nothing, run to a state, is a
run with callbacks. -/
theorem ExecS.of_run {I : Fml C} {σ τ : State} {s : Stmt C} (hs : s.forks = false)
    (h : s.run σ = .ok τ) : ExecS I σ s (.ok τ) := by
  have := ExecS.det (I := I) (σ := σ) hs
  rwa [h] at this

/-- **With no `transfer`, the two readings agree.** -/
theorem holdsC_iff_holds {I : Fml C} : (φ : Fml C) → φ.hasTransfer = false →
    ∀ {σ : State}, (holdsC I σ φ ↔ holds σ φ)
  | .tt, _, _ => Iff.rfl
  | .eq _ _, _, _ => Iff.rfl
  | .not φ, h, _ => by simp only [holdsC, holds, holdsC_iff_holds φ h]
  | .and φ ψ, h, _ => by
    simp only [Fml.hasTransfer, Bool.or_eq_false_iff] at h
    simp only [holdsC, holds, holdsC_iff_holds φ h.1, holdsC_iff_holds ψ h.2]
  | .imp φ ψ, h, _ => by
    simp only [Fml.hasTransfer, Bool.or_eq_false_iff] at h
    simp only [holdsC, holds, holdsC_iff_holds φ h.1, holdsC_iff_holds ψ h.2]
  | .upd m U φ, h, σ => by
    simp only [holdsC, holds]
    cases U.apply σ with
    | error _ => exact Iff.rfl
    | ok τ => exact holdsC_iff_holds φ h
  | .modal m P φ, h, σ => by
    simp only [Fml.hasTransfer, Bool.or_eq_false_iff] at h
    simp only [holdsC, holds]
    constructor
    · intro H
      rcases Prog.exec_run I P σ with he | he
      · have := H _ he
        rw [COut.after_ofRes] at this
        cases hr : Prog.run σ P with
        | error _ => rw [hr] at this; exact this
        | ok τ => rw [hr] at this; exact (holdsC_iff_holds φ h.2).1 this
      · have := ExecP.eq_run he h.1
        cases hr : Prog.run σ P <;> rw [hr] at this <;> cases this
    · intro H o he
      rw [ExecP.eq_run he h.1, COut.after_ofRes]
      cases hr : Prog.run σ P with
      | error _ => rw [hr] at H; exact H
      | ok τ => rw [hr] at H; exact (holdsC_iff_holds φ h.2).2 H
  | .havoc φ, h, _ => by
    simp only [holdsC, holds]
    exact forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
      holdsC_iff_holds φ h
  | .all _ _ φ, h, _ => by
    simp only [holdsC, holds]
    exact forall_congr' fun _ => imp_congr_right fun _ => holdsC_iff_holds φ h

/-- **A modal formula true with callbacks is true without**, when its
postcondition has no program paying: the deterministic run is among the
callback runs (`Prog.exec_run`), and none of those breaks the invariant. -/
theorem holds_of_holdsC_modal {I : Fml C} {σ : State} {m : Modality} {P : Prog C} {φ : Fml C}
    (H : holdsC I σ (.modal m P φ)) (hφ : φ.hasTransfer = false) : holds σ (.modal m P φ) := by
  simp only [holdsC] at H
  simp only [holds]
  rcases Prog.exec_run I P σ with he | he
  · have := H _ he
    rw [COut.after_ofRes] at this
    cases hr : Prog.run σ P with
    | error _ => rw [hr] at this; exact this
    | ok τ => rw [hr] at this; exact (holdsC_iff_holds φ hφ).1 this
  · exact (H _ he).elim

/-- A precondition and a modal formula, true with callbacks, are true without
(`holds_of_holdsC_modal`), when neither the precondition nor the
postcondition has a program paying. -/
theorem holds_of_holdsC_imp {I : Fml C} {σ : State} {a : Fml C} {m : Modality} {P : Prog C}
    {φ : Fml C} (H : holdsC I σ (.imp a (.modal m P φ))) (ha : a.hasTransfer = false)
    (hφ : φ.hasTransfer = false) : holds σ (.imp a (.modal m P φ)) :=
  fun h => holds_of_holdsC_modal (H ((holdsC_iff_holds a ha).2 h)) hφ

/-- **Valid with callbacks is valid without**, for `pre → [ P ] post`. -/
theorem valid_of_validC {I : Invariant C} {a : Fml C} {m : Modality} {P : Prog C} {φ : Fml C}
    (H : ValidC I (.imp a (.modal m P φ))) (ha : a.hasTransfer = false)
    (hφ : φ.hasTransfer = false) : Valid (.imp a (.modal m P φ)) :=
  fun σ => holds_of_holdsC_imp (H σ) ha hφ

/-! ## Frames -/

section Frame

variable {ns : List Var}

theorem Semantics.EnvAgreeExcept.symm' {σ τ : State} (h : EnvAgreeExcept ns σ τ) :
    EnvAgreeExcept ns τ σ :=
  ⟨h.storage.symm, h.heap.symm, h.nextId.symm, h.net.symm, fun n hn => (h.env n hn).symm,
    h.selfBalance.symm, h.tx.symm⟩

/-- Two outcomes alike off `ns`. -/
def COut.Agree (ns : List Var) : COut → COut → Prop
  | .ok a, .ok b => EnvAgreeExcept ns a b
  | .halt e, .halt e' => e = e'
  | .violated, .violated => True
  | _, _ => False

theorem COut.Agree.ofRes {r r' : Res State} (h : ResultsAgree ns r r') :
    COut.Agree ns (.ofRes r) (.ofRes r') := by
  cases r <;> cases r' <;> simp_all [ResultsAgree, COut.ofRes, COut.Agree]

theorem COut.Agree.isOk {o o' : COut} (h : COut.Agree ns o o') : o.isOk = o'.isOk := by
  cases o <;> cases o' <;> simp_all [COut.Agree, COut.isOk]

theorem COut.Agree.after {o o' : COut} (h : COut.Agree ns o o') (m : Modality)
    {p q : State → Prop} (hpq : ∀ a b, EnvAgreeExcept ns a b → (p a ↔ q b)) :
    o.after m p ↔ o'.after m q := by
  cases o <;> cases o' <;> simp only [COut.Agree, COut.after] at h ⊢
  · exact hpq _ _ h
  all_goals simp_all

theorem holds_I_frame {I : Fml C} (hI : I.vars = []) {σ τ : State}
    (h : EnvAgreeExcept ns σ τ) : holds σ I ↔ holds τ I :=
  holds_frame I (fun x hx => by simp [hI] at hx) h

mutual

/-- **Frame, for runs with callbacks**: a run from `τ` of a statement that
avoids `ns` has a twin from any `σ` that agrees with `τ` off `ns`, ending
alike. -/
theorem ExecS.frame {I : Fml C} (hI : I.vars = []) {σ τ : State} {s : Stmt C} {o' : COut} :
    ExecS I τ s o' → Avoids s.vars ns → EnvAgreeExcept ns σ τ →
      ∃ o, ExecS I σ s o ∧ COut.Agree ns o o'
  | .det hf, hs, hag => ⟨_, .det hf, .ofRes (Stmt.run_frame hag s hs)⟩
  | .transferHalt (r := r) (a := a) h, hs, hag => by
    have := Stmt.run_frame hag (.transfer r a) hs
    rw [h] at this
    cases hr : (Stmt.transfer r a).run σ with
    | error e => rw [hr] at this; cases this; exact ⟨_, .transferHalt hr, rfl⟩
    | ok _ => rw [hr] at this; exact this.elim
  | .transferViolated (r := r) (a := a) h hn, hs, hag => by
    have := Stmt.run_frame hag (.transfer r a) hs
    rw [h] at this
    cases hr : (Stmt.transfer r a).run σ with
    | error e => rw [hr] at this; exact this.elim
    | ok σ₁ =>
      rw [hr] at this
      exact ⟨_, .transferViolated hr (fun h' => hn ((holds_I_frame hI this).1 h')), trivial⟩
  | .transferResume (r := r) (a := a) (st := st) (nt := nt) (bal := bal) h h₁ h₂, hs, hag => by
    have := Stmt.run_frame hag (.transfer r a) hs
    rw [h] at this
    cases hr : (Stmt.transfer r a).run σ with
    | error e => rw [hr] at this; exact this.elim
    | ok σ₁ =>
      rw [hr] at this
      exact ⟨_, .transferResume hr ((holds_I_frame hI this).2 h₁)
        ((holds_I_frame hI (this.havoc st nt bal)).2 h₂), this.havoc st nt bal⟩
  | .iteHalt (c := c) hc, hs, hag => by
    have hc' : c.eval σ = c.eval _ := c.eval_frame hag hs.left.left
    rw [hc] at hc'
    exact ⟨_, .iteHalt hc', rfl⟩
  | .iteStuck (c := c) hc, hs, hag => by
    have hc' : c.eval σ = c.eval _ := c.eval_frame hag hs.left.left
    rw [hc] at hc'
    exact ⟨_, .iteStuck hc', rfl⟩
  | .iteThen (c := c) hc hp, hs, hag => by
    have hc' : c.eval σ = c.eval _ := c.eval_frame hag hs.left.left
    rw [hc] at hc'
    obtain ⟨o, ho, hag'⟩ := ExecP.frame hI hp hs.left.right hag
    exact ⟨o, .iteThen hc' ho, hag'⟩
  | .iteElse (c := c) hc hp, hs, hag => by
    have hc' : c.eval σ = c.eval _ := c.eval_frame hag hs.left.left
    rw [hc] at hc'
    obtain ⟨o, ho, hag'⟩ := ExecP.frame hI hp hs.right hag
    exact ⟨o, .iteElse hc' ho, hag'⟩
  | .callHalt (args := args) hb, hs, hag => by
    have := Arg.bindSeq_frame args hs.left.left hag
    rw [hb] at this
    cases hb' : Arg.bindSeq args σ with
    | error e => rw [hb'] at this; cases this; exact ⟨_, .callHalt hb', rfl⟩
    | ok _ => rw [hb'] at this; exact this.elim
  | .callDone (args := args) (ret := ret) hb hp, hs, hag => by
    have := Arg.bindSeq_frame args hs.left.left hag
    rw [hb] at this
    cases hb' : Arg.bindSeq args σ with
    | error e => rw [hb'] at this; exact this.elim
    | ok σ₁ =>
      rw [hb'] at this
      obtain ⟨o, ho, hag'⟩ := ExecP.frame hI hp hs.right (CallRet.enter_frame this ret)
      cases o with
      | ok σ₂ =>
        exact ⟨_, .callDone hb' ho, .ofRes (CallRet.leave_frame hag' ret hs.left.right)⟩
      | halt _ => exact hag'.elim
      | violated => exact hag'.elim
  | .callStop (args := args) (ret := ret) hb hp ho, hs, hag => by
    have := Arg.bindSeq_frame args hs.left.left hag
    rw [hb] at this
    cases hb' : Arg.bindSeq args σ with
    | error e => rw [hb'] at this; exact this.elim
    | ok σ₁ =>
      rw [hb'] at this
      obtain ⟨o, ho', hag'⟩ := ExecP.frame hI hp hs.right (CallRet.enter_frame this ret)
      exact ⟨o, .callStop hb' ho' (by rw [hag'.isOk]; exact ho), hag'⟩

/-- **Frame, for blocks with callbacks.** -/
theorem ExecP.frame {I : Fml C} (hI : I.vars = []) {σ τ : State} {P : List (Stmt C)}
    {o' : COut} :
    ExecP I τ P o' → Avoids (Prog.vars P) ns → EnvAgreeExcept ns σ τ →
      ∃ o, ExecP I σ P o ∧ COut.Agree ns o o'
  | .nil, _, hag => ⟨_, .nil, hag⟩
  | .cons hs hp, h, hag => by
    obtain ⟨o₁, ho₁, hag₁⟩ := ExecS.frame hI hs h.left hag
    cases o₁ with
    | ok σ₁ =>
      obtain ⟨o, ho, hag'⟩ := ExecP.frame hI hp h.right hag₁
      exact ⟨o, .cons ho₁ ho, hag'⟩
    | halt _ => exact hag₁.elim
    | violated => exact hag₁.elim
  | .stop hs ho, h, hag => by
    obtain ⟨o₁, ho₁, hag₁⟩ := ExecS.frame hI hs h.left hag
    exact ⟨o₁, .stop ho₁ (by rw [hag₁.isOk]; exact ho), hag₁⟩

end

/-- **Frame, for formulas read with callbacks.** -/
theorem holdsC_frame {I : Fml C} (hI : I.vars = []) :
    (φ : Fml C) → Avoids φ.vars ns → ∀ {σ τ : State},
      EnvAgreeExcept ns σ τ → (holdsC I σ φ ↔ holdsC I τ φ)
  | .tt, _, _, _, _ => Iff.rfl
  | .eq a b, h, _, _, hag => holds_frame (.eq a b) h hag
  | .not φ, h, _, _, hag => by simp only [holdsC, holdsC_frame hI φ h hag]
  | .and φ ψ, h, _, _, hag => by
    simp only [holdsC, holdsC_frame hI φ h.left hag, holdsC_frame hI ψ h.right hag]
  | .imp φ ψ, h, _, _, hag => by
    simp only [holdsC, holdsC_frame hI φ h.left hag, holdsC_frame hI ψ h.right hag]
  | .upd m U φ, h, _, _, hag => by
    simp only [holdsC]
    exact m.after_frame (Upd.apply_frame hag U h.left) fun _ _ h' => holdsC_frame hI φ h.right h'
  | .modal m P φ, h, σ, τ, hag => by
    simp only [holdsC]
    constructor
    · intro H o' he'
      obtain ⟨o, he, hag'⟩ := ExecP.frame hI he' h.left hag
      exact (hag'.after m fun _ _ h' => holdsC_frame hI φ h.right h').1 (H o he)
    · intro H o he
      obtain ⟨o', he', hag'⟩ := ExecP.frame hI he h.left hag.symm'
      exact (hag'.after m fun _ _ h' => holdsC_frame hI φ h.right h').1 (H o' he')
  | .havoc φ, h, _, _, hag => by
    simp only [holdsC]
    exact forall_congr' fun st => forall_congr' fun nt => forall_congr' fun bal =>
      holdsC_frame hI φ h (hag.havoc st nt bal)
  | .all x _ φ, h, _, _, hag => by
    simp only [holdsC]
    exact forall_congr' fun v => imp_congr_right fun _ =>
      holdsC_frame hI φ h.tail (hag.setEnv_both x (.val v))

end Frame

end Solidity
