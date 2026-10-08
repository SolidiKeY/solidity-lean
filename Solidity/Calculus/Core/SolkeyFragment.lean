import Solidity.Calculus.Core.RuleExists

/-!
# solkey's rules on the scoped syntax

`Calculus/SolkeyFragment.lean` on scoped statements, at the level of the
rule table.  The table is two lists (`Calculus/Core/Rules.lean`): `Taclet`,
the rules that transcribe a taclet of solkey, and `LeanTaclet`, the rules
solkey does not have.  A statement is **in solkey's fragment** under a
modality (`Stmt.inSolkey m`) when no `LeanTaclet` is needed to run it
there: every call's arguments are simple, in its branches, blocks and the
bodies it inlines too; under the diamond it pays no one; and it has no
`try` and no loop.  On the fragment the rule the strategy fires is one of
solkey's (`Stmt.step_taclet`); off it, a loop has a rule of the calculus
and none of solkey's (`Taclet.not_loop`).

Today's module also states the fragment for the judgement
(`Proves.solkey_iff`: on it, solkey's rules derive what the calculus
derives).  The scoped `Core.Proves` takes the rule set `R` as an index but
no rule reads it, so `⊢ₖ` and `⊢` have the same derivations and that
statement says nothing; it waits for `R` to restrict the steps
(`docs/intrinsic.md`, W4 `theorems`, proposed decision 33).
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

mutual

/-- No call of `s`, however deep, has an argument to capture
(`functionCallArgCapture`); a payment is under the box, where solkey books
it (`transferNoCallbackBox`; the diamond is `LeanTaclet.transferDiamond`); a
send is under either modality; and there is no `try` (solkey has its rule
under the box only, with its blocks outside the claim) and no loop (its
rules here are Lean's: `whileUnwind`, `loopExit`, the invariant rules). -/
def Stmt.inSolkey (m : Modality) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Bool
  | _, _, s => Stmt.casesOn (motive_1 := fun _ _ _ => Bool) s
    (assign := fun _ _ => true) (rebind := fun _ _ => true) (assignLocal := fun _ _ => true)
    (declLocal := fun _ _ _ => true) (declStorage := fun _ _ _ => true)
    (opAssign := fun _ _ _ _ _ => true) (incDec := fun _ _ _ => true)
    (assignIncDec := fun _ _ _ _ _ => true) (push := fun _ _ _ => true) (pop := fun _ => true)
    (transfer := fun _ _ => m == .box) (send := fun _ _ _ => true)
    (declMem := fun _ _ _ _ _ => true) (rebindMem := fun _ _ => true)
    (assignFromMem := fun _ _ => true) (assignMem := fun _ _ => true) (delete := fun _ => true)
    (deleteMem := fun _ _ => true) (assignNew := fun _ _ _ => true)
    (ite := fun _ thn els => Prog.inSolkey m thn && Prog.inSolkey m els)
    (require := fun _ => true) (assert := fun _ => true) (revert := true)
    (call := fun _ args _ body => (Args.capture args).isNone && Prog.inSolkey m body)
    (tryCall := fun _ _ _ _ _ _ _ => false) (loop := fun _ _ _ => false)
    (block := fun body => Prog.inSolkey m body)
  termination_by structural _ _ s => s

/-- Every statement of the block is in the fragment. -/
def Prog.inSolkey (m : Modality) : {Γ Γ' : Ctx} → Prog C Γ Γ' → Bool
  | _, _, P => Prog.casesOn (motive_2 := fun _ _ _ => Bool) P true
      (fun s P => Stmt.inSolkey m s && Prog.inSolkey m P)
  termination_by structural _ _ P => P

end

/-- **No Lean rule fires on the fragment.** -/
theorem LeanTaclet.not_inSolkey {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (d : LeanTaclet C k m s p) : s.inSolkey m = false := by
  cases d with
  | functionCallArgCapture hcap =>
    show ((Args.capture _).isNone && _) = false
    rw [hcap]; rfl
  | _ => rfl

/-- **On the fragment, the rule the strategy fires is solkey's.** -/
theorem Stmt.step_taclet {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (h : s.inSolkey m = true) (hs : s.step k m = some p) :
    Taclet C k m s p :=
  match Rule.ofStep hs with
  | .key d => d
  | .lean d => absurd h (by rw [d.not_inSolkey]; decide)

/-- **On the fragment, solkey has the rule**: `Stmt.step` leaves a premise,
and one of solkey's taclets rewrites the statement to it. -/
theorem Stmt.solkey_rule_exists (k : Nat) {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    (h : s.inSolkey m = true) : ∃ p, s.step k m = some p ∧ Taclet C k m s p :=
  let ⟨p, hs, _⟩ := Stmt.rule_exists k m s
  ⟨p, hs, Stmt.step_taclet h hs⟩

/-- Whether a statement is a loop. -/
def Stmt.isLoop : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Bool
  | _, _, s => Stmt.casesOn (motive_1 := fun _ _ _ => Bool) s
    (assign := fun _ _ => false) (rebind := fun _ _ => false)
    (assignLocal := fun _ _ => false) (declLocal := fun _ _ _ => false)
    (declStorage := fun _ _ _ => false) (opAssign := fun _ _ _ _ _ => false)
    (incDec := fun _ _ _ => false) (assignIncDec := fun _ _ _ _ _ => false)
    (push := fun _ _ _ => false) (pop := fun _ => false) (transfer := fun _ _ => false)
    (send := fun _ _ _ => false) (declMem := fun _ _ _ _ _ => false)
    (rebindMem := fun _ _ => false) (assignFromMem := fun _ _ => false)
    (assignMem := fun _ _ => false) (delete := fun _ => false)
    (deleteMem := fun _ _ => false) (assignNew := fun _ _ _ => false)
    (ite := fun _ _ _ => false) (require := fun _ => false) (assert := fun _ => false)
    (revert := false) (call := fun _ _ _ _ => false)
    (tryCall := fun _ _ _ _ _ _ _ => false) (loop := fun _ _ _ => true)
    (block := fun _ => false)

/-- **No taclet of solkey's runs a loop**: its rules here are Lean's
(`whileUnwind`, `loopExit`, the invariant rules), at the pinned checkout. -/
theorem Taclet.not_loop {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (d : Taclet C k m s p) : s.isLoop = false := by
  cases d <;> first | rfl | (core_cases_hole <;> rfl)

/-- **Off the fragment, solkey's rules fall short**: a loop has a rule of the
calculus, and no taclet of solkey's rewrites it. -/
theorem Stmt.solkey_lt_calculus (k : Nat) (m : Modality) {Γ Γ₁ : Ctx} (a : LoopAnn C Γ)
    (c : Val C Γ .bool) (body : Prog C Γ Γ₁) :
    (∃ p, Rule C k m (.loop a c body) p) ∧ ∀ p, ¬ Taclet C k m (.loop a c body) p :=
  ⟨let ⟨p, _, d⟩ := Stmt.rule_exists k m (.loop a c body); ⟨p, d⟩,
    fun _ d => Bool.noConfusion (d.not_loop : true = false)⟩

end Solidity.Core
