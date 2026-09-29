import Solidity.Calculus.Logic
import Solidity.Calculus.Completeness

/-!
# solkey's rules on the refined syntax

The calculus is two lists (`Rules.lean`): `Taclet`, the rules that transcribe
a taclet of solkey, and `LeanTaclet`, the rules solkey does not have.  Both
are sound (`Rule.sound`), for everything the typed syntax can write.

This module is the other half of the claim, about solkey itself.  A
statement is **in solkey's fragment** (`Stmt.inSolkey`) when no rule of
`LeanTaclet` is ever needed to run it: every call's arguments are simple, in
its branches and in the bodies it inlines too.  On the fragment:

* every statement has a rule of solkey's (`Stmt.step_taclet`), and no Lean
  rule fires (`LeanTaclet.not_inSolkey`);
* solkey's rules keep a program in the fragment (`Taclet.premise_inSolkey`);
* so a derivation of the whole calculus is one of solkey's rules alone
  (`Proves.toSolkey`), and what solkey derives is valid
  (`Proves.solkey_valid`).

So soundness of the whole syntax is solkey's rules, plus the `LeanTaclet`s or
the refinement.  The fragment is the one syntactic restriction the rule table
adds.  The typed syntax is already narrower than solkey's in other ways (no
storage copy of a mapping, no recursion, only the five compound operators,
…), and each of those is a condition of `Taclet.sound`;
`docs/solkey-feedback.md` lists them.
-/

namespace Solidity

variable {C : Contract} {k : Nat} {m : Modality}

/-! ## The fragment -/

mutual

/-- No call of `s`, however deep, has an argument to capture. -/
def Stmt.inSolkey : Stmt C → Bool
  | .ite _ thn els => Prog.inSolkey thn && Prog.inSolkey els
  | .call _ args _ _ body => (Arg.firstNonSimple args).isNone && Prog.inSolkey body
  | _ => true

/-- Every statement of the block is in the fragment. -/
def Prog.inSolkey : List (Stmt C) → Bool
  | [] => true
  | s :: P => s.inSolkey && Prog.inSolkey P

end

/-- Every program under a modality of `φ` is in the fragment. -/
def Fml.inSolkey : Fml C → Bool
  | .tt | .eq .. => true
  | .not φ | .upd _ _ φ | .havoc φ | .all _ _ φ => φ.inSolkey
  | .and φ ψ | .imp φ ψ => φ.inSolkey && ψ.inSolkey
  | .modal _ P φ => Prog.inSolkey P && φ.inSolkey

/-- The programs and conditions of a premise are in the fragment. -/
def Premise.inSolkey : Premise C → Bool
  | .update _ | .done _ => true
  | .unfold P => Prog.inSolkey P
  | .split c c' P Q => c.inSolkey && c'.inSolkey && Prog.inSolkey P && Prog.inSolkey Q

@[simp] theorem Prog.inSolkey_nil : Prog.inSolkey ([] : Prog C) = true := rfl

@[simp] theorem Prog.inSolkey_cons {s : Stmt C} {P : Prog C} :
    Prog.inSolkey (s :: P) = (s.inSolkey && Prog.inSolkey P) := rfl

@[simp] theorem Prog.inSolkey_append {P Q : Prog C} :
    Prog.inSolkey (P ++ Q) = (Prog.inSolkey P && Prog.inSolkey Q) := by
  induction P with
  | nil => rfl
  | cons s P ih => simp [ih, Bool.and_assoc]

/-! ## Solkey's rules keep the fragment -/

@[simp] theorem Hole.fill_inSolkey {T : Ty} (h : Hole C T) (p : SPath C T) :
    (h.fill p).inSolkey = true := by
  cases h <;> cases p <;> rfl

@[simp] theorem MHole.fill_inSolkey {T : Ty} (h : MHole C T) (l : MLoc C T) :
    (h.fill l).inSolkey = true := by
  cases h <;> rfl

@[simp] theorem VHole.fill_inSolkey {p : PrimTy} (h : VHole C p) (v : Val C p) :
    (h.fill v).inSolkey = true := by
  cases h <;> rfl

@[simp] theorem NewLhs.fill_inSolkey {R : RefTy} (l : NewLhs C R) (p : MPath C (.ref R)) :
    (l.fill p).inSolkey = true := by
  cases l <;> rfl

@[simp] theorem Premise.cover_inSolkey {c c' : Fml C} :
    (Premise.cover m c c').inSolkey = (m = .box || c.inSolkey && c'.inSolkey) := by
  cases m <;> simp [Premise.cover, Fml.inSolkey]

theorem Arg.decls_inSolkey (args : List (Arg C)) :
    Prog.inSolkey (args.map Arg.decl) = true := by
  induction args with
  | nil => rfl
  | cons a as ih => simpa [Arg.decl, Stmt.inSolkey] using ih

theorem CallRet.decl_inSolkey (ret : CallRet) : Prog.inSolkey (ret.decl : Prog C) = true := by
  cases ret <;> rfl

theorem CallRet.result_inSolkey (ret : CallRet) :
    Prog.inSolkey (ret.result : Prog C) = true := by
  rcases ret with _ | ⟨p, r, _ | x⟩ <;> rfl

set_option maxHeartbeats 4000000 in
/-- **Solkey's rules keep the fragment**: the premise of a statement in it
is in it.  Only three rules put a call or a branch in their premise: the two
that run an `if` hand on its branches, and `functionBodyExpand` inlines a body
that is in the fragment with its simple arguments. -/
theorem Taclet.premise_inSolkey {s : Stmt C} {p : Premise C} (d : Taclet C k m s p)
    (h : s.inSolkey = true) : p.inSolkey = true := by
  cases d <;> (try cases ‹Hole _ _›) <;> (try cases ‹MHole _ _›) <;> (try cases ‹VHole _ _›) <;>
    simp_all [Premise.inSolkey, Stmt.inSolkey, Fml.inSolkey, Stmt.expandBody,
      Arg.decls_inSolkey, CallRet.decl_inSolkey, CallRet.result_inSolkey]

/-! ## On the fragment, solkey's rules are the calculus -/

/-- A rule solkey does not have fires only outside the fragment. -/
theorem LeanTaclet.not_inSolkey {s : Stmt C} {p : Premise C} (d : LeanTaclet C k m s p) :
    s.inSolkey = false := by
  cases d with
  | functionCallArgCapture h => simp [Stmt.inSolkey, h]

/-- **solkey's rules are complete on the fragment**: the rule `Stmt.step`
fires on a statement of the fragment is one of solkey's. -/
theorem Stmt.step_taclet {s : Stmt C} (h : s.inSolkey = true) :
    Taclet C k m s (s.step k m).premise := by
  cases (s.step k m).rule with
  | key d => exact d
  | lean d => exact absurd h (by simp [d.not_inSolkey])

/-- **A derivation on the fragment is solkey's**: whatever the calculus
derives about a formula whose programs are in the fragment, solkey's rules
derive alone. -/
theorem Proves.toSolkey {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C} (h : Proves R Γ φ)
    (hφ : φ.inSolkey = true) : Proves .solkey Γ φ := by
  induction h with
  | intro _ ih => exact .intro (ih (by simp_all [Fml.inSolkey]))
  | update d _ ih => exact .update d (ih (by simp_all [Fml.inSolkey]))
  | unfold d _ ih =>
    simp only [Fml.inSolkey, Prog.inSolkey_cons, Bool.and_eq_true] at hφ
    have := d.premise_inSolkey hφ.1.1
    exact .unfold d (ih (by simp_all [Fml.inSolkey, Premise.inSolkey]))
  | unfoldLean d _ _ =>
    simp only [Fml.inSolkey, Prog.inSolkey_cons, Bool.and_eq_true] at hφ
    exact absurd hφ.1.1 (by simp [d.not_inSolkey])
  | split d _ _ _ ih₁ ih₂ ih₃ =>
    simp only [Fml.inSolkey, Prog.inSolkey_cons, Bool.and_eq_true] at hφ
    have := d.premise_inSolkey hφ.1.1
    simp only [Premise.inSolkey, Bool.and_eq_true] at this
    exact .split d (ih₁ (by simp_all [Fml.inSolkey])) (ih₂ (by simp_all [Fml.inSolkey]))
      (ih₃ (by simp_all))
  | done d _ ih =>
    exact .done d (ih (by rename_i b _; cases b <;> rfl))
  | empty _ ih => exact .empty (ih (by simp_all [Fml.inSolkey]))
  | close h hm => exact .close h hm

/-- On the fragment, solkey's rules derive exactly what the calculus does. -/
theorem Proves.solkey_iff {Γ : List (Hyp C)} {φ : Fml C} (hφ : φ.inSolkey = true) :
    Proves .solkey Γ φ ↔ Proves .all Γ φ :=
  ⟨Proves.toAll, fun h => h.toSolkey hφ⟩

open Proves in
/-- **Solkey is sound on the refined syntax**: a derivation by solkey's rules
alone proves its sequent. -/
theorem Proves.solkey_valid {φ : Fml C} (h : ⊢ₖ φ) : Valid φ := h.sound

/-! `y = f(x + 1);` is outside the fragment: solkey has no rule to capture
`x + 1`.  `y = f(x);` is in it. -/

example : (Stmt.call (C := C) "f" [⟨.uint, .user "a", .binop .add rfl rfl
    (.simple (.local (.user "x"))) (.simple (.lit 1 rfl))⟩] rfl .none []).inSolkey = false := rfl

example : (Stmt.call (C := C) "f" [⟨.uint, .user "a", .simple (.local (.user "x"))⟩] rfl
    .none []).inSolkey = true := rfl

/-! ## Off the fragment the two differ

`Proves.solkey_iff` needs its hypothesis: `[ f(x + 1); ] true` is derived by
the calculus (the capture, then the call) and not by solkey's rules, which
have no rule for the call and may not leave for the logic while a modality
is left (`close`). -/

set_option maxHeartbeats 4000000 in
/-- The one taclet of solkey's that fires on a call, `functionBodyExpand`,
asks every argument to be simple. -/
theorem Taclet.call_simple {s : Stmt C} {p : Premise C} (d : Taclet C k m s p) :
    ∀ {f args hsep ret body}, s = .call f args hsep ret body → Arg.firstNonSimple args = none := by
  cases d <;> (try cases ‹Hole _ _›) <;> (try cases ‹MHole _ _›) <;> (try cases ‹VHole _ _›) <;>
    intro _ _ _ _ _ h <;> cases h <;> assumption

/-- A sequent with no modality has none in its formula. -/
theorem Hyp.modalFree_wrap {φ : Fml C} :
    (Γ : List (Hyp C)) → (Hyp.wrap Γ φ).modalFree = true → φ.modalFree = true
  | [], h => h
  | .pre _ :: Γ, h => by
    simp only [Hyp.wrap, Fml.modalFree, Bool.and_eq_true] at h
    exact Hyp.modalFree_wrap Γ h.2
  | .upd _ _ :: Γ, h | .havoc :: Γ, h => Hyp.modalFree_wrap Γ h

/-- **solkey's rules derive nothing about a call whose argument is not
simple**, in any context. -/
theorem Proves.solkey_not_call {Γ : List (Hyp C)} {f : Name} {args : List (Arg C)}
    {hsep : Arg.separatedFrom [] args = true} {ret : CallRet} {body ω : Prog C} {φ : Fml C}
    {a : Arg C} (ha : Arg.firstNonSimple args = some a) :
    ¬ Proves .solkey Γ (.modal m (.call f args hsep ret body :: ω) φ) := by
  intro h
  cases h with
  | update d _ | unfold d _ | split d _ _ _ | done d _ => simp [d.call_simple rfl] at ha
  | close _ hm => exact absurd (Hyp.modalFree_wrap Γ hm) (by simp [Fml.modalFree])

/-- `[ f(x + 1); ] true`, `f(uint a)` with an empty body: a call whose
argument is not simple. -/
def captureCall : Fml C :=
  .modal .box [.call "f" [⟨.uint, .user "a", .binop .add rfl rfl
    (.simple (.local (.user "x"))) (.simple (.lit 1 rfl))⟩] rfl .none []] .tt

open Proves in
/-- The calculus derives it: the capture, then the call. -/
theorem captureCall_derived : ⊢ (captureCall : Fml C) := by
  apply unfoldLean .functionCallArgCapture   -- uint se = x + 1; f(se);
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply unfold .functionBodyExpand          -- uint a = se;
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply empty
  refine close fun σ => ?_
  simp only [Hyp.wrap, List.nil_append, List.cons_append, holds]
  cases Upd.apply _ σ <;> simp only [Modality.after, Modality.onHalt] <;>
    (try cases Upd.apply _ _) <;> trivial

open Proves in
/-- **Off the fragment solkey's rules fall short**: the calculus derives
`[ f(x + 1); ] true`, solkey's rules do not.  So `Proves.solkey_iff` needs
its hypothesis. -/
theorem Proves.solkey_lt_calculus : ∃ φ : Fml C, (⊢ φ) ∧ ¬ (⊢ₖ φ) :=
  ⟨captureCall, captureCall_derived, Proves.solkey_not_call rfl⟩

end Solidity
