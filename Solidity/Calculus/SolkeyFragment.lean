import Solidity.Calculus.RuleExists
import Solidity.Calculus.Proves

/-!
# solkey's rules on the scoped syntax

Today's `Calculus/SolkeyFragment` (deleted at W4 `calc-del`) on scoped statements, at the level of the
rule table.  The table is two lists (`Calculus/Rules.lean`): `Taclet`,
the rules that transcribe a taclet of solkey, and `LeanTaclet`, the rules
solkey does not have.  A statement is **in solkey's fragment** under a
modality (`Stmt.inSolkey m`) when no `LeanTaclet` is needed to run it
there: every call's arguments are simple, in its branches, blocks and the
bodies it inlines too; under the diamond it pays no one; and it has no
`try` and no loop.  On the fragment the rule the strategy fires is one of
solkey's (`Stmt.step_taclet`); off it, a loop has a rule of the calculus
and none of solkey's (`Taclet.not_loop`).

The judgement reads the rule set (decision 36): a step of `⊢ₖ` asks
`RuleSet.admits .solkey`, which is `Stmt.keyStep`, so the rule it fires is
a `Taclet` (`Stmt.taclet_of_admits`).  On the fragment the step is always
admitted (`Stmt.keyStep_of_inSolkey`), and solkey's rules keep a program in
the fragment (`Taclet.premise_inSolkey`, over `Fml.inSolkey` and
`Premise.inSolkey`): the judgement-level statements that follow from these
are `Calculus/SolkeyProves.lean`'s.
-/

namespace Solidity

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
    {p : Premise C Γ Γ'} (h : s.inSolkey m = true) (hs : s.step k m = p) :
    Taclet C k m s p :=
  match Rule.ofStep hs with
  | .key d => d
  | .lean d => absurd h (by rw [d.not_inSolkey]; decide)

/-- **On the fragment, solkey has the rule**: one of solkey's taclets
rewrites the statement to the premise `Stmt.step` leaves. -/
theorem Stmt.solkey_rule_exists (k : Nat) {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    (h : s.inSolkey m = true) : Taclet C k m s (s.step k m) :=
  Stmt.step_taclet h rfl

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
  ⟨⟨_, Stmt.rule_exists k m (.loop a c body)⟩,
    fun _ d => Bool.noConfusion (d.not_loop : true = false)⟩


/-! ## The step `⊢ₖ` admits -/

/-- **A step of `⊢ₖ` fires one of solkey's taclets**: where `.solkey` admits
the statement (`Stmt.keyStep`), the rule `Stmt.step` fires is a `Taclet`. -/
theorem Stmt.taclet_of_admits {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (hR : RuleSet.admits .solkey m s = true) (hs : s.step k m = p) :
    Taclet C k m s p :=
  match Rule.ofStep hs with
  | .key d => d
  | .lean d => absurd (d.keyStep : s.keyStep m = false) (by rw [show s.keyStep m = true from hR]; decide)

/-- On the fragment, solkey's rule set admits the step. -/
theorem Stmt.keyStep_of_inSolkey {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    (h : s.inSolkey m = true) : s.keyStep m = true := by
  cases s with
  | call f args ret body =>
    have h' : ((Args.capture args).isNone && Prog.inSolkey m body) = true := h
    exact (Bool.and_eq_true _ _ ▸ h').1
  | tryCall => exact absurd h Bool.false_ne_true
  | loop => exact absurd h Bool.false_ne_true
  | transfer => exact h
  | _ => rfl

/-! ## Solkey's rules keep the fragment -/

/-- The frames' statements are in the fragment, under `m`. -/
def Frames.inSolkey (m : Modality) : {Γ Γ₀ : Ctx} → Frames C Γ Γ₀ → Bool
  | _, _, .nil => true
  | _, _, .seq ω κ => Prog.inSolkey m ω && Frames.inSolkey m κ
  | _, _, .pop _ _ κ => Frames.inSolkey m κ
  | _, _, .drop _ κ => Frames.inSolkey m κ

/-- Every program under a modality of `φ`, its frames' too, is in the
fragment, under that modality. -/
def Fml.inSolkey : {Γ : Ctx} → Fml C Γ → Bool
  | _, .tt | _, .eq .. | _, .defined _ => true
  | _, .not φ => Fml.inSolkey φ
  | _, .and φ ψ | _, .imp φ ψ => Fml.inSolkey φ && Fml.inSolkey ψ
  | _, .upd _ _ φ => Fml.inSolkey φ
  | _, .modal m P κ φ => Prog.inSolkey m P && Frames.inSolkey m κ && Fml.inSolkey φ
  | _, .havoc φ | _, .all _ _ φ | _, .bind _ _ _ φ | _, .anon _ φ => Fml.inSolkey φ

/-- The programs and conditions of a premise are in the fragment.  A `try`'s
clauses (`branches`) and a loop's invariant rule (`inv`) are not: neither
statement is in it. -/
def Premise.inSolkey (m : Modality) {Γ Γ' : Ctx} : Premise C Γ Γ' → Bool
  | .update _ | .done _ => true
  | .unfold P _ | .bind _ _ P | .inline P _ => Prog.inSolkey m P
  | .split _ c c' P Q => c.inSolkey && c'.inSolkey && Prog.inSolkey m P && Prog.inSolkey m Q
  | .check c => c.inSolkey
  | .branches _ | .inv .. => false
  | .cases fs _ => fs.all Fml.inSolkey

theorem Prog.inSolkey_cons {m : Modality} {Γ Γ₁ Γ₂ : Ctx} (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) :
    Prog.inSolkey m (.cons s P) = (s.inSolkey m && Prog.inSolkey m P) := rfl

theorem Frames.exit_inSolkey (m : Modality) {Γ Γ₀ : Ctx} (κ : Frames C Γ Γ₀) :
    ∀ φ : Fml C Γ₀, (κ.exit m φ).inSolkey = (κ.inSolkey m && φ.inSolkey) := by
  intro φ
  induction κ with
  | nil => rfl
  | seq ω κ ih =>
    cases ω with
    | nil => exact ih φ
    | cons s ω =>
      show (Prog.inSolkey m (.cons s ω) && κ.inSolkey m && φ.inSolkey) = _
      simp only [Frames.inSolkey, Bool.and_assoc]
  | pop _ _ κ ih => exact ih φ
  | drop _ κ ih => exact ih φ

theorem Fml.modalK_inSolkey (m : Modality) {Γ Γ₁ Γ₀ : Ctx} (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    (Fml.modalK m ω κ φ).inSolkey = (Prog.inSolkey m ω && κ.inSolkey m && φ.inSolkey) := by
  cases ω with
  | nil => exact Frames.exit_inSolkey m κ φ
  | cons s ω => rfl

theorem Val.isSimple_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {p : PrimTy} (e : Val C Γ p) :
    (e.wk h).isSimple = e.isSimple := by
  cases e <;> rfl

theorem Args.capture_snoc_isNone {Γ : Ctx} {ps : Ctx} (as : Args C Γ ps) (p : PrimTy) (x : Var)
    (e : Val C Γ p) :
    (Args.capture (.snoc as p x e)).isNone = ((Args.capture as).isNone && e.isSimple) := by
  rw [Args.capture]
  dsimp only
  split
  · rename_i h; simp only [h, Option.isNone_some, Bool.false_and]
  · rename_i h
    simp only [h, Option.isNone_none, Bool.true_and]
    cases e.isSimple <;> rfl

/-- Weakening keeps the arguments to capture. -/
theorem Args.capture_wk_isNone {Γ Δ : Ctx} (h : Thin Γ Δ) {ps : Ctx} (args : Args C Γ ps) :
    (Args.capture (args.wk h)).isNone = (Args.capture args).isNone := by
  induction args with
  | nil => rfl
  | snoc as p x e ih =>
    show (Args.capture (.snoc (as.wk h) p x (e.wk h))).isNone = (Args.capture (.snoc as p x e)).isNone
    rw [Args.capture_snoc_isNone, Args.capture_snoc_isNone, ih, Val.isSimple_wk]

mutual

/-- Weakening keeps a statement in the fragment. -/
theorem Stmt.inSolkey_wk (m : Modality) {Γ Δ : Ctx} (h : Thin Γ Δ) :
    {Γ' : Ctx} → (s : Stmt C Γ Γ') → (s.wk h).2.2.inSolkey m = s.inSolkey m
  | _, .ite c thn els => by
    show (Prog.inSolkey m (thn.wk h).2.2 && Prog.inSolkey m (els.wk h).2.2) = _
    rw [Prog.inSolkey_wk m h thn, Prog.inSolkey_wk m h els]; rfl
  | _, .call f args ret body => by
    simp only [Stmt.wk]
    show ((Args.capture (args.wk h)).isNone && Prog.inSolkey m body) = _
    rw [Args.capture_wk_isNone]; rfl
  | _, .block body => by
    show Prog.inSolkey m (body.wk h).2.2 = _
    rw [Prog.inSolkey_wk m h body]; rfl
  | _, .assign .. | _, .rebind .. | _, .assignLocal .. | _, .declLocal .. | _, .declStorage ..
  | _, .opAssign .. | _, .incDec .. | _, .assignIncDec .. | _, .push .. | _, .pop ..
  | _, .transfer .. | _, .send .. | _, .declMem .. | _, .rebindMem .. | _, .assignFromMem ..
  | _, .assignMem .. | _, .delete .. | _, .deleteMem .. | _, .assignNew .. | _, .require ..
  | _, .assert .. | _, .revert | _, .tryCall .. | _, .loop .. => rfl

/-- Weakening keeps a block in the fragment. -/
theorem Prog.inSolkey_wk (m : Modality) {Γ Δ : Ctx} (h : Thin Γ Δ) :
    {Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.inSolkey m (P.wk h).2.2 = Prog.inSolkey m P
  | _, .nil => rfl
  | _, .cons s P => by
    simp only [Prog.wk]
    show (Stmt.inSolkey m (s.wk h).2.2 && Prog.inSolkey m (P.wk (s.wk h).2.1).2.2) = _
    rw [Stmt.inSolkey_wk m h s, Prog.inSolkey_wk m _ P]; rfl

end

theorem Args.declsThen_inSolkey (m : Modality) {Γ Δ : Ctx} {ps : Ctx} (args : Args C Γ ps) :
    ∀ rest : Prog C (ps ++ Γ) Δ, Prog.inSolkey m (args.declsThen rest) = Prog.inSolkey m rest := by
  induction args with
  | nil => intro _; rfl
  | snoc as p x e ih => intro rest; exact ih _

theorem Binders.declsThen_inSolkey (m : Modality) {Γ Δ : Ctx} {ρ : Ctx} (bs : Binders ρ) :
    ∀ rest : Prog C (ρ ++ Γ) Δ, Prog.inSolkey m (bs.declsThen (Γ := Γ) rest) = Prog.inSolkey m rest := by
  induction bs with
  | nil => intro _; rfl
  | snoc bs p x ih => intro rest; exact ih _

/-- A call's expansion is in the fragment when its body is. -/
theorem Premise.expandCall_inSolkey (m : Modality) (k : Nat) {Γ Γ' ps rs Γf : Ctx}
    (args : Args C Γ ps) (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf)
    (h : Prog.inSolkey m body = true) : (Premise.expandCall k args ret body).inSolkey m = true := by
  cases ret with
  | none =>
    show Prog.inSolkey m (args.declsThen _) = true
    rw [Args.declsThen_inSolkey]
    show (Prog.inSolkey m (body.wk _).2.2 && true) = true
    rw [Prog.inSolkey_wk, h]; rfl
  | val p r res =>
    show Prog.inSolkey m (args.declsThen _) = true
    rw [Args.declsThen_inSolkey]
    show (true && (Prog.inSolkey m (body.wk _).2.2 && _)) = true
    rw [Prog.inSolkey_wk, h]
    cases res <;> rfl
  | rets bs =>
    show Prog.inSolkey m (args.declsThen _) = true
    rw [Args.declsThen_inSolkey, Binders.declsThen_inSolkey]
    show (Prog.inSolkey m (body.wk _).2.2 && true) = true
    rw [Prog.inSolkey_wk, h]; rfl
  | mem R r hd hm =>
    show Prog.inSolkey m (args.declsThen _) = true
    rw [Args.declsThen_inSolkey]
    show (true && (Prog.inSolkey m (body.wk _).2.2 && true)) = true
    rw [Prog.inSolkey_wk, h]; rfl

/-- **Solkey's rules keep the fragment**: the premise of a statement in it
is in it. -/
theorem Taclet.premise_inSolkey {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (d : Taclet C k m s p) (h : s.inSolkey m = true) :
    p.inSolkey m = true := by
  cases d <;> (try core_cases_hole) <;> first
    | rfl
    | exact h
    | exact absurd h Bool.false_ne_true
    | (cases m <;> first | rfl | exact absurd h Bool.false_ne_true)
    | exact Premise.expandCall_inSolkey m k _ _ _ (Bool.and_eq_true _ _ ▸ h).2
    | (cases ‹NewLhs C Γ _› <;> rfl)
    | (show (true && ((true && (Prog.inSolkey m (Prog.up _) && Prog.inSolkey m (Prog.up _))) && true))
          = true
       rw [Prog.inSolkey_wk, Prog.inSolkey_wk]
       simpa only [Bool.true_and, Bool.and_true] using h)

end Solidity
