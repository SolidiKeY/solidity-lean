import Solidity.Calculus.RuleExists
import Solidity.Calculus.Proves
import Solidity.Calculus.KeyValues

/-!
# solkey's rules on the scoped syntax

Today's `Calculus/SolkeyFragment` (deleted at W4 `calc-del`) on scoped statements, at the level of the
rule table.  The table is two lists (`Calculus/Rules.lean`): `Taclet`,
the rules that transcribe a taclet of solkey, and `LeanTaclet`, the rules
solkey does not have.  A statement is **in solkey's fragment** under a
modality (`Stmt.inSolkey m`) when no `LeanTaclet` is needed to run it
there: every call's arguments are simple, in its branches, blocks and the
bodies it inlines too; no program operand, including a path index, contains
a native modular builtin; under the diamond it pays no one; and it has no
`try` and no annotated loop. This is a conservative program-rule fragment:
it does not restrict symbols inside arbitrary formula atoms or updates. The table now
also contains restricted upstream loop rules. On the fragment the strategy
fires one of solkey's (`Stmt.step_taclet`); a zero-bound loop instead uses
Lean's `loopExit` (`Taclet.not_unwindZero`).

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
under the box only, with its blocks outside the claim) and no loop. The
loop-free restriction is sufficient, not necessary: bounded unwinding and
the restricted invariant rules now transcribe upstream taclets. -/
def Stmt.inSolkey (m : Modality) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Bool
  | _, _, s => Stmt.casesOn (motive_1 := fun _ _ _ => Bool) s
    (assign := fun l r => !r.isMemory && l.keyValue && r.keyValue)
    (rebind := fun _ r => r.keyValue) (assignLocal := fun _ r => r.keyValue)
    (declLocal := fun _ _ v => v.elim true Val.keyValue)
    (declStorage := fun _ _ v => v.elim true ARhs.keyValue)
    (opAssign := fun _ _ _ l r => l.keyValue && r.keyValue)
    (incDec := fun _ _ l => l.keyValue)
    (assignIncDec := fun _ _ _ l _ => l.keyValue)
    (assignLocalPush := fun _ b => b.keyValue)
    (push := fun b v _ => b.keyValue && v.elim true (fun r => r.keyPushSource && r.keyValue))
    (pop := fun b => b.keyValue)
    (transfer := fun r a => (m == .box) && r.keyValue && a.keyValue)
    (send := fun _ r a _ => r.keyValue && a.keyValue)
    (declMem := fun _ _ v _ _ => v.elim true MRhs.keyValue)
    (rebindMem := fun _ r => r.keyValue)
    (assignFromMem := fun l p => l.keyValue && p.keyValue)
    (assignMem := fun l r => l.keyValue && r.keyValue)
    (delete := fun l => l.keyValue)
    (deleteMem := fun p _ => p.keyValue) (assignNew := fun l _ _ => l.keyValue)
    (ite := fun c thn els => c.keyValue && Prog.inSolkey m thn && Prog.inSolkey m els)
    (require := fun c => c.keyValue) (assert := fun c => c.keyValue) (revert := true)
    (assumeFalse := false)
    (call := fun _ args _ body => (Args.capture args).isNone && args.keyValues && Prog.inSolkey m body)
    (tryCall := fun _ _ _ _ _ _ _ _ _ _ => false)
    (loop := fun a c body => match a with | .auto => c.keyValue && Prog.inSolkey m body | _ => false)
    (block := fun body => Prog.inSolkey m body)
    (pushOpAssign := fun _ _ _ b r => b.isSimple && b.keyValue && r.keyValue)
    (pushIncDec := fun _ _ b => b.isSimple && b.keyValue)
    (callReceiver := fun _ args _ body op =>
      (Args.capture args).isNone && args.keyValues && Prog.inSolkey m body &&
        match op with | .push v _ => v.elim true (fun r => r.keyPushSource && r.keyValue) | .pop => true)
    (callReceiverPush := fun _ args _ body code value =>
      (Args.capture args).isNone && args.keyValues && Prog.inSolkey m body &&
        Prog.inSolkey m code && value.keyPushSource && value.keyValue)
    -- `recursiveCallUnfold` is Lean's
    (callRec := fun _ _ _ _ _ => false)
    -- revert data is Lean's
    (revertData := fun _ => false) (catchData := fun _ _ _ _ _ _ _ _ => false)
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
    show ((Args.capture _).isNone && _ && _) = false
    rw [hcap]; rfl
  | pushCompoundUnfoldReceiver h =>
    simp only [Stmt.inSolkey, h, Bool.false_and]
  | pushIncrementUnfoldReceiver h =>
    simp only [Stmt.inSolkey, h, Bool.false_and]
  | storageMemorySourceSave hmem =>
    simp only [Stmt.inSolkey, hmem, Bool.not_true, Bool.false_and]
  | storageFixedCopySave hshape =>
    simp only [Stmt.inSolkey, Src.keyValue_ofFixedCopy hshape, Bool.and_false]
  | pushFixedCopySave hshape _ =>
    simp only [Stmt.inSolkey, Option.elim, Src.keyValue_ofFixedCopy hshape, Bool.and_false]
  | pushMemorySourceCapture _ hnmp =>
    simp only [Stmt.inSolkey, Option.elim, Src.keyPushSource, hnmp, Bool.false_and,
      Bool.and_false]
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

/-- A loop at `unwind 0` needs Lean's `loopExit`; the bounded port of
`whileUnwind` requires a positive bound, and invariant rules need an invariant. -/
def Stmt.isUnwindZero : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Bool
  | _, _, .loop (.unwind 0) _ _ => true
  | _, _, _ => false

/-- No upstream taclet selects Lean's zero-bound loop-exit annotation. -/
theorem Taclet.not_unwindZero {k : Nat} {m : Modality} {Γ Γ' : Ctx}
    {s : Stmt C Γ Γ'} {p : Premise C Γ Γ'} (d : Taclet C k m s p) :
    s.isUnwindZero = false := by
  cases d <;> first
    | rfl
    | (cases ‹ReceiverValue C Γ _› <;> rfl)
    | (cases ‹LoopUnwind› <;> rfl)
    | (core_cases_hole <;> rfl)

/-- **Off the fragment, the tables still differ**: a zero-bound loop has
Lean's exit rule and no upstream taclet at that annotation. -/
theorem Stmt.solkey_lt_calculus (k : Nat) (m : Modality) {Γ Γ₁ : Ctx}
    (c : Val C Γ .bool) (body : Prog C Γ Γ₁) :
    (∃ p, Rule C k m (.loop (.unwind 0) c body) p) ∧
      ∀ p, ¬ Taclet C k m (.loop (.unwind 0) c body) p :=
  ⟨⟨_, Stmt.rule_exists k m (.loop (.unwind 0) c body)⟩,
    fun _ d => Bool.noConfusion (d.not_unwindZero : true = false)⟩


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
  | call f args ret body => exact (Bool.and_eq_true _ _ ▸ (Bool.and_eq_true _ _ ▸ h).1).1
  | tryCall => exact absurd h Bool.false_ne_true
  | loop a _ _ => cases a <;> first | rfl | exact absurd h Bool.false_ne_true
  | transfer => exact (Bool.and_eq_true _ _ ▸ (Bool.and_eq_true _ _ ▸ h).1).1
  | pushOpAssign _ _ _ b r =>
    show (!r.isSimple || b.isSimple) = true
    rw [show b.isSimple = true from (Bool.and_eq_true _ _ ▸ (Bool.and_eq_true _ _ ▸ h).1).1,
      Bool.or_true]
  | pushIncDec => exact (Bool.and_eq_true _ _ ▸ h).1
  | assign l r =>
    have hr : r.keyValue = true := (Bool.and_eq_true _ _ ▸ h).2
    show (!r.isMemory && !r.isFixedCopy) = true
    rw [Src.notFixedCopy_of_keyValue hr, Bool.not_false, Bool.and_true]
    exact (Bool.and_eq_true _ _ ▸ (Bool.and_eq_true _ _ ▸ h).1).1
  | assignLocal _ r =>
    cases r <;> first | rfl | exact absurd h Bool.false_ne_true
  | push b v _ =>
    have hv := (Bool.and_eq_true _ _ ▸ h).2
    cases v with
    | none => rfl
    | some r =>
      show (r.keyPushSource || !b.isSimple) = true
      rw [show r.keyPushSource = true from (Bool.and_eq_true _ _ ▸ hv).1]
      rfl
  | assumeFalse | callRec | revertData | catchData => exact absurd h Bool.false_ne_true
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
  | _, .tt | _, .eq .. | _, .wellFormed _ => true
  | _, .not φ => Fml.inSolkey φ
  | _, .and φ ψ | _, .imp φ ψ => Fml.inSolkey φ && Fml.inSolkey ψ
  | _, .upd _ _ φ => Fml.inSolkey φ
  | _, .modal m P κ φ => Prog.inSolkey m P && Frames.inSolkey m κ && Fml.inSolkey φ
  | _, .havoc φ | _, .all _ _ φ | _, .bind _ _ _ φ | _, .anon _ φ => Fml.inSolkey φ
  | _, .allocAll .. => false

/-- The programs and conditions of a premise are in the fragment.  A `try`'s
clauses (`branches`) and a loop's invariant rule (`inv`) are not: neither
statement is in it. -/
def Premise.inSolkey (m : Modality) {Γ Γ' : Ctx} : Premise C Γ Γ' → Bool
  | .update _ | .updates _ _ | .done _ => true
  | .guardedUpdates c _ _ => c.inSolkey
  | .unfold P _ | .bind _ _ P | .inline P _ => Prog.inSolkey m P
  | .split _ c c' P Q => c.inSolkey && c'.inSolkey && Prog.inSolkey m P && Prog.inSolkey m Q
  | .check c => c.inSolkey
  | .branches _ | .inv .. | .allocBranches .. => false
  | .cases fs _ => fs.all Fml.inSolkey

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

theorem Args.capture_snocStorage_isNone {Γ : Ctx} {ps : Ctx} (as : Args C Γ ps)
    (R : RefTy) (x : Var) (e : SPath C Γ (.ref R)) :
    (Args.capture (.snocStorage as R x e)).isNone = (Args.capture as).isNone := by
  cases h : Args.capture as <;> simp only [Args.capture, h, Option.isNone_none, Option.isNone_some]

theorem Args.capture_snocMemory_isNone {Γ : Ctx} {ps : Ctx} (as : Args C Γ ps)
    (R : RefTy) (x : Var) (e : MPath C Γ (.ref R)) :
    (Args.capture (.snocMemory as R x e)).isNone = (Args.capture as).isNone := by
  cases h : Args.capture as <;> simp only [Args.capture, h, Option.isNone_none, Option.isNone_some]

/-- Weakening keeps the arguments to capture. -/
theorem Args.capture_wk_isNone {Γ Δ : Ctx} (h : Thin Γ Δ) {ps : Ctx} (args : Args C Γ ps) :
    (Args.capture (args.wk h)).isNone = (Args.capture args).isNone := by
  induction args with
  | nil => rfl
  | snoc as p x e ih =>
    show (Args.capture (.snoc (as.wk h) p x (e.wk h))).isNone = (Args.capture (.snoc as p x e)).isNone
    rw [Args.capture_snoc_isNone, Args.capture_snoc_isNone, ih, Val.isSimple_wk]
  | snocStorage as R x e ih =>
    show (Args.capture (.snocStorage (as.wk h) R x (e.wk h))).isNone = _
    rw [Args.capture_snocStorage_isNone, Args.capture_snocStorage_isNone, ih]
  | snocMemory as R x e ih =>
    show (Args.capture (.snocMemory (as.wk h) R x (e.wk h))).isNone = _
    rw [Args.capture_snocMemory_isNone, Args.capture_snocMemory_isNone, ih]

mutual

/-- Weakening keeps a statement in the fragment. -/
theorem Stmt.inSolkey_wk (m : Modality) {Γ Δ : Ctx} (h : Thin Γ Δ) :
    {Γ' : Ctx} → (s : Stmt C Γ Γ') → (s.wk h).2.2.inSolkey m = s.inSolkey m
  | _, .ite c thn els => by
    show ((c.wk h).keyValue && Prog.inSolkey m (thn.wk h).2.2 &&
      Prog.inSolkey m (els.wk h).2.2) = _
    rw [Val.keyValue_wk, Prog.inSolkey_wk m h thn, Prog.inSolkey_wk m h els]; rfl
  | _, .call f args ret body => by
    simp only [Stmt.wk]
    show ((Args.capture (args.wk h)).isNone && (args.wk h).keyValues && Prog.inSolkey m body) = _
    rw [Args.capture_wk_isNone, Args.keyValues_wk]; rfl
  | _, .callReceiver _ args _ body op => by
    cases op with
    | pop => simp only [Stmt.wk, Stmt.inSolkey, ReceiverOp.wk, Args.capture_wk_isNone, Args.keyValues_wk]
    | push v _ =>
      cases v <;> simp only [Stmt.wk, Stmt.inSolkey, ReceiverOp.wk, Args.capture_wk_isNone, Args.keyValues_wk,
        Option.map_none, Option.map_some, Option.elim, Src.keyPushSource_wk, Src.keyValue_wk]
  | _, .callReceiverPush _ args _ body code value => by
    simp only [Stmt.wk, Stmt.inSolkey, Args.capture_wk_isNone, Args.keyValues_wk, Src.keyPushSource_wk,
      Src.keyValue_wk]
    rw [Prog.inSolkey_wk m h code]
  | _, .loop a c body => by
    cases a <;> simp only [Stmt.wk, LoopAnn.wk, Stmt.inSolkey, Val.keyValue_wk,
      Prog.inSolkey_wk m h body]
  | _, .block body => by
    show Prog.inSolkey m (body.wk h).2.2 = _
    rw [Prog.inSolkey_wk m h body]; rfl
  | _, .callRec _ _ _ ret _ => by cases ret <;> rfl
  | _, .revertData _ | _, .catchData .. => rfl
  | _, .declLocal _ _ v | _, .declStorage _ _ v | _, .declMem _ _ v _ _
  | _, .push _ v _ => by
    cases v <;> simp only [Stmt.wk, Stmt.inSolkey, Option.map_none, Option.map_some,
      Option.elim, SPath.keyValue_wk, Loc.keyValue_wk, MPath.keyValue_wk, MLoc.keyValue_wk, Val.keyValue_wk, Src.keyValue_wk, MSrc.keyValue_wk, ARhs.keyValue_wk, MRhs.keyValue_wk, OpLoc.keyValue_wk, NewLhs.keyValue_wk, Src.keyPushSource_wk]
  | _, .rebind .. | _, .assignLocal .. | _, .assign ..
  | _, .opAssign .. | _, .incDec .. | _, .assignIncDec .. | _, .assignLocalPush ..
  | _, .pop .. | _, .pushOpAssign .. | _, .pushIncDec ..
  | _, .transfer .. | _, .send .. | _, .rebindMem .. | _, .assignFromMem ..
  | _, .assignMem .. | _, .delete .. | _, .deleteMem .. | _, .assignNew .. | _, .require ..
  | _, .assert .. | _, .revert | _, .assumeFalse | _, .tryCall .. => by
    simp only [Stmt.wk, Stmt.inSolkey, SPath.keyValue_wk, Loc.keyValue_wk, MPath.keyValue_wk, MLoc.keyValue_wk, Val.keyValue_wk, Src.keyValue_wk, MSrc.keyValue_wk, ARhs.keyValue_wk, MRhs.keyValue_wk, OpLoc.keyValue_wk, NewLhs.keyValue_wk,
      SPath.isSimple_wk, Src.isMemory_wk]

/-- Weakening keeps a block in the fragment. -/
theorem Prog.inSolkey_wk (m : Modality) {Γ Δ : Ctx} (h : Thin Γ Δ) :
    {Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.inSolkey m (P.wk h).2.2 = Prog.inSolkey m P
  | _, .nil => rfl
  | _, .cons s P => by
    simp only [Prog.wk]
    show (Stmt.inSolkey m (s.wk h).2.2 && Prog.inSolkey m (P.wk (s.wk h).2.1).2.2) = _
    rw [Stmt.inSolkey_wk m h s, Prog.inSolkey_wk m _ P]; rfl

end

theorem Val.keyValue_unders {Γ : Ctx} {p : PrimTy} (e : Val C Γ p) (ρ : Ctx) :
    (e.unders ρ).keyValue = e.keyValue := by
  induction ρ with
  | nil => rfl
  | cons t ρ ih =>
    show ((e.unders ρ).up).keyValue = _
    rw [Val.up_eq, Val.keyValue_wk, ih]

theorem SPath.keyValue_unders {Γ : Ctx} {T : Ty} (e : SPath C Γ T) (ρ : Ctx) :
    (e.unders ρ).keyValue = e.keyValue := by
  induction ρ with
  | nil => rfl
  | cons t ρ ih =>
    show ((e.unders ρ).up).keyValue = _
    rw [SPath.up_eq, SPath.keyValue_wk, ih]

theorem MPath.keyValue_unders {Γ : Ctx} {T : Ty} (e : MPath C Γ T) (ρ : Ctx) :
    (e.unders ρ).keyValue = e.keyValue := by
  induction ρ with
  | nil => rfl
  | cons t ρ ih =>
    show ((e.unders ρ).up).keyValue = _
    rw [MPath.up_eq, MPath.keyValue_wk, ih]

theorem Args.declsThen_inSolkey (m : Modality) {Γ Δ : Ctx} {ps : Ctx} (args : Args C Γ ps)
    (ha : args.keyValues = true) :
    ∀ rest : Prog C (ps ++ Γ) Δ, Prog.inSolkey m (args.declsThen rest) = Prog.inSolkey m rest := by
  induction args with
  | nil => intro _; rfl
  | snoc as p x e ih =>
    intro rest
    change (as.keyValues && e.keyValue) = true at ha
    have hs := Bool.and_eq_true _ _ ▸ ha
    change Prog.inSolkey m (as.declsThen (.cons (.declLocal p x (some _)) rest)) = _
    rw [ih hs.1]
    show ((e.unders _).keyValue && rest.inSolkey m) = _
    rw [Val.keyValue_unders, hs.2]
    rfl
  | snocStorage as R x e ih =>
    intro rest
    change (as.keyValues && e.keyValue) = true at ha
    have hs := Bool.and_eq_true _ _ ▸ ha
    change Prog.inSolkey m (as.declsThen (.cons (.declStorage R x (some _)) rest)) = _
    rw [ih hs.1]
    show ((e.unders _).keyValue && rest.inSolkey m) = _
    rw [SPath.keyValue_unders, hs.2]; rfl
  | snocMemory as R x e ih =>
    intro rest
    change (as.keyValues && e.keyValue) = true at ha
    have hs := Bool.and_eq_true _ _ ▸ ha
    change Prog.inSolkey m (as.declsThen (.cons (.declMem R x (some _) _ _) rest)) = _
    rw [ih hs.1]
    show ((e.unders _).keyValue && rest.inSolkey m) = _
    rw [MPath.keyValue_unders, hs.2]; rfl

theorem Binders.declsThen_inSolkey (m : Modality) {Γ Δ : Ctx} {ρ : Ctx} (bs : Binders ρ) :
    ∀ rest : Prog C (ρ ++ Γ) Δ, Prog.inSolkey m (bs.declsThen (Γ := Γ) rest) = Prog.inSolkey m rest := by
  induction bs with
  | nil => intro _; rfl
  | snoc bs p x ih => intro rest; exact ih _

/-- A call's expansion is in the fragment when its body is. -/
theorem Premise.expandCall_inSolkey (m : Modality) (k : Nat) {Γ Γ' ps rs Γf : Ctx}
    (args : Args C Γ ps) (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf)
    (ha : args.keyValues = true)
    (h : Prog.inSolkey m body = true) : (Premise.expandCall k args ret body).inSolkey m = true := by
  cases ret with
  | none =>
    show Prog.inSolkey m (args.declsThen _) = true
    rw [Args.declsThen_inSolkey m args ha]
    show (Prog.inSolkey m (body.wk _).2.2 && true) = true
    rw [Prog.inSolkey_wk, h]; rfl
  | val p r res =>
    show Prog.inSolkey m (args.declsThen _) = true
    rw [Args.declsThen_inSolkey m args ha]
    show (true && (Prog.inSolkey m (body.wk _).2.2 && _)) = true
    rw [Prog.inSolkey_wk, h]
    cases res <;> rfl
  | rets bs =>
    show Prog.inSolkey m (args.declsThen _) = true
    rw [Args.declsThen_inSolkey m args ha, Binders.declsThen_inSolkey]
    show (Prog.inSolkey m (body.wk _).2.2 && true) = true
    rw [Prog.inSolkey_wk, h]; rfl
  | mem R r hd hm =>
    show Prog.inSolkey m (args.declsThen _) = true
    rw [Args.declsThen_inSolkey m args ha]
    show (true && (Prog.inSolkey m (body.wk _).2.2 && true)) = true
    rw [Prog.inSolkey_wk, h]; rfl
  | storage R r =>
    show Prog.inSolkey m (args.declsThen _) = true
    rw [Args.declsThen_inSolkey m args ha]
    show (true && (Prog.inSolkey m (body.wk _).2.2 && true)) = true
    rw [Prog.inSolkey_wk, h]
    rfl

/-- Joining the operand prefix and `sp.push(e)` preserves their SolKey membership. -/
theorem Prog.inSolkey_join (m : Modality) : {Γ Δ Θ : Ctx} →
    (P : Prog C Γ Δ) → (Q : Prog C Δ Θ) →
    (P.join Q).inSolkey m = (P.inSolkey m && Q.inSolkey m)
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons s P, Q => by
    change (s.inSolkey m && (P.join Q).inSolkey m) =
      ((s.inSolkey m && P.inSolkey m) && Q.inSolkey m)
    rw [Prog.inSolkey_join m P Q, Bool.and_assoc]

/-- Capturing `f()` before push/pop keeps the getter and source in the fragment. -/
theorem callReceiverStep_inSolkey (m : Modality) (k : Nat) {Γ ps Γf : Ctx} {E : Ty}
    (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (op : ReceiverOp C Γ E)
    (h : (Stmt.callReceiver f args r body op).inSolkey m = true) :
    (callReceiverStep k f args r body op).inSolkey m = true := by
  change (((Args.capture args).isNone && args.keyValues && Prog.inSolkey m body) &&
    (true && ((((op.wk (.drop .refl)).wk (.drop .refl)).toStmt (.alias .here)).inSolkey m && true)))
      = true
  cases op with
  | pop => simpa only [ReceiverOp.wk, ReceiverOp.toStmt, Stmt.inSolkey, SPath.keyValue,
      Bool.true_and, Bool.and_true] using h
  | push v _ =>
    cases v <;> simpa only [ReceiverOp.wk, ReceiverOp.toStmt, Stmt.inSolkey,
      Src.keyPushSource_wk, Src.keyValue_wk, SPath.keyValue,
      Option.elim, Option.map_some, Option.map_none,
      Bool.true_and, Bool.and_true] using h

/-- Capturing `f()` before either spelling of `e` keeps `f().push(e)` in the fragment. -/
theorem ReceiverValue.step_inSolkey (m : Modality) (k : Nat) {Γ ps Γf : Ctx} {E : Ty}
    (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : ReceiverValue C Γ E)
    (h : (e.statement f args r body).inSolkey m = true) :
    (e.step k f args r body).inSolkey m = true := by
  cases e with
  | pure value => exact callReceiverStep_inSolkey m k f args r body (.push (some value) rfl) h
  | deferred code value =>
    let p := code.wk (.drop (t := .alias (.array E)) .refl)
    let q := p.2.2.wk (.drop (t := .alias (.array E)) .refl)
    let push : Prog C q.1 q.1 := .cons (.push (.alias (Idx.here.ext q.2.2.ext))
      (some ((value.wk p.2.1).wk q.2.1)) rfl) .nil
    change (((Args.capture args).isNone && args.keyValues && body.inSolkey m) &&
      (true && ((q.2.2.join push).inSolkey m && true))) = true
    rw [Prog.inSolkey_join, Prog.inSolkey_wk, Prog.inSolkey_wk]
    have hs : push.inSolkey m =
        (((value.wk p.2.1).wk q.2.1).keyPushSource &&
          ((value.wk p.2.1).wk q.2.1).keyValue) := by
      simp only [push, Prog.inSolkey, Stmt.inSolkey, Option.elim, Bool.and_true,
        SPath.keyValue, Bool.true_and]
    rw [hs, Src.keyPushSource_wk, Src.keyPushSource_wk, Src.keyValue_wk, Src.keyValue_wk]
    simpa only [ReceiverValue.statement, Stmt.inSolkey, Bool.true_and,
      Bool.and_true, Bool.and_assoc] using h

/-- Automatic `whileUnwind` keeps its body in the SolKey-only fragment. -/
theorem loopUnwindStep_inSolkey (m : Modality) (u : LoopUnwind) {Γ Γ₁ : Ctx}
    (c : Val C Γ .bool) (body : Prog C Γ Γ₁)
    (h : (Stmt.loop u.before c body).inSolkey m = true) :
    (loopUnwindStep u c body).inSolkey m = true := by
  cases u with
  | bounded _ => exact absurd h Bool.false_ne_true
  | automatic =>
    have hc : c.keyValue = true := (Bool.and_eq_true _ _ ▸ h).1
    have hb : body.inSolkey m = true := (Bool.and_eq_true _ _ ▸ h).2
    simp only [loopUnwindStep, Premise.inSolkey, Prog.inSolkey, Stmt.inSolkey,
      LoopUnwind.after, hc, hb, Bool.and_self]

namespace FragmentProof
open Lean Meta Elab Tactic

elab "fragment_wrapper_cases" : tactic => do
  unless ← coreCasesFirst [``ARhs, ``MRhs, ``OpLoc, ``Src, ``MSrc, ``NewLhs] do
    throwError "no initializer wrapper"

/-- Each rule has a separate declaration and the existing heartbeat budget. -/
elab "#check_fragment_rules" : command => do
  let some (.inductInfo info) := (← getEnv).find? ``Taclet
    | throwError "Taclet is not an inductive"
  for c in info.ctors do
    let ty : TermElabM Expr := do
      let ty ← forallTelescope (← getConstInfo c).type fun xs body => do
        let args := body.getAppArgs
        let hs ← mkEq (← mkAppM ``Stmt.inSolkey #[args[2]!, args[5]!]) (mkConst ``Bool.true)
        let hp ← mkEq (← mkAppM ``Premise.inSolkey #[args[2]!, args[6]!]) (mkConst ``Bool.true)
        mkForallFVars xs (← mkArrow hs hp)
      return ty.dropAutoParams
    discard <| addCtorLemma c `inSolkey ty (err := m!"{c}: incomplete fragment proof") do
        match c.getString! with
        | "storagePushValue_unfold_leftCallReceiver" =>
          evalTactic (← `(tactic| (intros; rename_i h; exact ReceiverValue.step_inSolkey _ _ _ _ _ _ _ h)))
        | "storagePush_unfold_leftCallReceiver" | "storagePop_unfold_leftCallReceiver" =>
          evalTactic (← `(tactic| (intros; rename_i h; exact callReceiverStep_inSolkey _ _ _ _ _ _ _ h)))
        | "functionBodyExpand" | "internalCallExpand" =>
          evalTactic (← `(tactic| (intros; rename_i h; exact Premise.expandCall_inSolkey _ _ _ _ _ (Bool.and_eq_true _ _ ▸ (Bool.and_eq_true _ _ ▸ h).1).2 (Bool.and_eq_true _ _ ▸ h).2)))
        | "whileUnwind" =>
          evalTactic (← `(tactic| (intros; rename_i h; exact loopUnwindStep_inSolkey _ _ _ _ h)))
        | "ifElseUnfold" =>
          evalTactic (← `(tactic| (intro C k m Γ c Γ₁ thn Γ₂ els _ h; change (c.keyValue && ((true && Prog.inSolkey m thn.up && Prog.inSolkey m els.up) && true)) = true; rw [Prog.inSolkey_wk, Prog.inSolkey_wk]; simpa only [Stmt.inSolkey, Bool.true_and, Bool.and_true, Bool.and_assoc] using h)))
        | _ =>
          evalTactic (← `(tactic| (intros; rename_i h; (try core_cases_hole) <;>
            (try fragment_wrapper_cases) <;> first
    | rfl
    | exact h
    | (simp_all only [Premise.capture, Premise.captureSP, Premise.captureMV,
        SHole.up, SHole.fill, MHole.up, MHole.fill, VHole.up, VHole.fill,
        Premise.inSolkey, Prog.inSolkey, Stmt.inSolkey,
        Val.up_eq, SPath.up_eq, Loc.up_eq, MPath.up_eq, MLoc.up_eq, Src.up_eq, MSrc.up_eq,
        ARhs.up_eq, MRhs.up_eq, ARhs.wk, MRhs.wk, OpLoc.wk, Src.wk, MSrc.wk, NewLhs.wk,
        NewLhs.up_eq, NewLhs.fill, OpLoc.up_eq, Prog.up,
        SPath.keyValue_wk, Loc.keyValue_wk, MPath.keyValue_wk, MLoc.keyValue_wk,
        Val.keyValue_wk, Src.keyValue_wk, MSrc.keyValue_wk, ARhs.keyValue_wk,
        MRhs.keyValue_wk, NewLhs.keyValue_wk, OpLoc.keyValue_wk, Prog.inSolkey_wk,
        SPath.keyValue, Loc.keyValue, MPath.keyValue, MLoc.keyValue, Val.keyValue,
        Src.keyValue, MSrc.keyValue, ARhs.keyValue, MRhs.keyValue, NewLhs.keyValue,
        OpLoc.keyValue, Src.isMemory, Src.keyPushSource, SPath.isSimple_wk, MPath.isSimple_wk,
        Bool.and_eq_true, Bool.not_eq_true, Bool.true_and, Bool.and_true, Bool.false_and,
        Bool.and_false, Bool.false_eq_true, Bool.true_eq_false, Option.elim])
    | exact absurd h Bool.false_ne_true
    | (cases ‹NewLhs _ _ _› <;> simp_all only [NewLhs.fill, NewLhs.keyValue,
        Loc.up_eq, MLoc.up_eq, Loc.keyValue_wk, MLoc.keyValue_wk,
        Premise.inSolkey, Prog.inSolkey, Stmt.inSolkey, MSrc.keyValue, MPath.keyValue,
        Bool.true_and, Bool.and_true, Bool.and_self, Option.elim]))))
        let gs ← getGoals
        unless gs.isEmpty do throwError "open fragment goals {goalsToMessageData gs}"

elab "apply_fragment_rule" : tactic => do
  let tag ← getMainTag
  let n := ``Taclet ++ tag ++ `inSolkey
  evalTactic (← `(tactic| (apply $(mkIdent n) <;> assumption)))

end FragmentProof

open FragmentProof in
#check_fragment_rules

/-- **Solkey's rules keep the fragment**: the premise of a statement in it
is in it. -/
theorem Taclet.premise_inSolkey {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (d : Taclet C k m s p) (h : s.inSolkey m = true) :
    p.inSolkey m = true := by
  cases d <;> apply_fragment_rule

end Solidity
