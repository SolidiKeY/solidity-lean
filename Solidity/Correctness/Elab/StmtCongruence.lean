import Solidity.Correctness.Elab.Congruence

/-! Run-level callback agreement for statement arms. -/
namespace Solidity.ElabAgree
open Solidity Semantics
variable (C : Contract) [FreshNames]

omit [FreshNames] in
/-- Traversal accumulates captures in order, threading the output state of
one hoist into the next, including failures of either computation. -/
theorem hoistTraversal_agree (H K : RawExpr → ElabM (SProg C × RawExpr))
    (sc : ElabScope) (s : RawStmt)
    (h : ∀ e ∈ s.exprs, Agree sc (H e) (K e))
    (hs : ∀ T x r a b, s = .send (some T) x r a b → Agree sc (H x) (K x))
    (P : SProg C) :
    Agree sc
      ((s.mapExprsM fun e => do
        let (Q, e) ← H e
        modify (· ++ Q)
        pure e : StateT (SProg C) ElabM RawStmt).run P)
      ((s.mapExprsM fun e => do
        let (Q, e) ← K e
        modify (· ++ Q)
        pure e : StateT (SProg C) ElabM RawStmt).run P) := by
  apply mapExprsM_agree
  · intro e he acc
    simp only [StateT.run_bind, liftM, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
    apply agree_bind (h e he)
    intro out _
    cases out
    exact agree_refl _ _
  · intro T x r a b he acc
    simp only [StateT.run_bind, liftM, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
    apply agree_bind (hs T x r a b he)
    intro out _
    cases out
    exact agree_refl _ _

/-- Hoisting preserves captures, rewritten syntax, errors and both states
when the callbacks agree at the scope of the statement. -/
theorem hoistStmtWith_agree (rc rc' : ElabRec C) (sc : ElabScope) (s : RawStmt)
    (hh : ∀ e, Agree sc (rc.hoist e) (rc'.hoist e))
    (ht : ∀ e, Agree sc (rc.hoistTop e) (rc'.hoistTop e))
    (ha : ∀ l r, Agree sc (rc.hoistAssign l r) (rc'.hoistAssign l r))
    (has : ∀ as, Agree sc (rc.hoistArgs as) (rc'.hoistArgs as))
    (hc : ∀ f as, Agree sc (rc.hoistCallArgs f as) (rc'.hoistCallArgs f as))
    (hs : ∀ ss, Agree sc (rc.elabStmtsP ss) (rc'.elabStmtsP ss)) :
    Agree sc (hoistStmtWith C rc s) (hoistStmtWith C rc' s) := by
  unfold hoistStmtWith
  agree_run
  all_goals first
    | exact hh _
    | exact ht _
    | exact ha _ _
    | exact has _
    | exact hc _ _
    | exact hs _
    | exact hoistTraversal_agree C _ _ sc _ (fun e _ => hh e) (fun _ x _ _ _ _ => hh x) _
    | (apply eagerArgsWith_agree; intros; exact hh _)

/-- Statement preprocessing agrees through rewriting and capture before
passing the resulting statement to its elaboration callback. -/
theorem elabStmtPWith_agree (rc rc' : ElabRec C) (sc : ElabScope) (s : RawStmt)
    (hh : ∀ e, Agree sc (rc.hoist e) (rc'.hoist e))
    (hp : ∀ s, Agree sc (rc.elabStmtP s) (rc'.elabStmtP s))
    (hhs : ∀ s, Agree sc (rc.hoistStmt s) (rc'.hoistStmt s))
    (hs : ∀ ss, Agree sc (rc.elabStmtsP ss) (rc'.elabStmtsP ss))
    (h1 : ∀ s, Agree sc (rc.elabStmt1 s) (rc'.elabStmt1 s)) :
    Agree sc (elabStmtPWith C rc s) (elabStmtPWith C rc' s) := by
  unfold elabStmtPWith
  agree_run
  all_goals first
    | exact hh _
    | exact hp _
    | exact hhs _
    | exact hs _
    | exact h1 _

omit [FreshNames] in
/-- Loop annotations traverse their list in order at the current reader. -/
theorem agree_listMapM {α β : Type} (sc : ElabScope) (f g : α → ElabM β)
    (xs : List α) (h : ∀ a ∈ xs, Agree sc (f a) (g a)) :
    Agree sc (xs.mapM f) (xs.mapM g) := by
  induction xs with
  | nil => exact agree_refl _ _
  | cons a as ih =>
    simp only [List.mapM_cons]
    exact agree_bind (h a (by simp)) fun _ _ =>
      agree_bind (ih fun e he => h e (by simp [he])) fun _ _ => agree_refl _ _

omit [FreshNames] in
/-- An absent loop variant invokes no callback. -/
theorem agree_optionMapM {α β : Type} (sc : ElabScope) (f g : α → ElabM β)
    (x : Option α) (h : ∀ a ∈ x, Agree sc (f a) (g a)) :
    Agree sc (x.mapM f) (x.mapM g) := by
  cases x with
  | none => exact agree_refl _ _
  | some a =>
    simp only [Option.mapM, ← bind_pure_comp]
    exact agree_bind (h a rfl) fun _ _ => agree_refl _ _

/-- Elaboration agrees at the original reader and at the two reader updates
used for checked and unchecked blocks. State restoration, abrupt control,
loop annotations, and errors are included in the run equality. -/
theorem elabStmt1With_agree (rc rc' : ElabRec C) (sc : ElabScope) (s : RawStmt)
    (h_hoist : ∀ e, Agree sc (rc.hoist e) (rc'.hoist e))
    (h_abiMemBytes : ∀ e, Agree sc (rc.abiMemBytes e) (rc'.abiMemBytes e))
    (h_abiEncode : ∀ std strs as marks sel, Agree sc (rc.abiEncode std strs as marks sel) (rc'.abiEncode std strs as marks sel))
    (h_elabCall : ∀ f as res w b, Agree sc (rc.elabCall f as res w b) (rc'.elabCall f as res w b))
    (h_elabMemCall : ∀ f as R bind, Agree sc (rc.elabMemCall f as R bind) (rc'.elabMemCall f as R bind))
    (h_elabStorageCall : ∀ f as R bind, Agree sc (rc.elabStorageCall f as R bind) (rc'.elabStorageCall f as R bind))
    (h_elabCallReceiver : ∀ f as op, Agree sc (rc.elabCallReceiver f as op) (rc'.elabCallReceiver f as op))
    (h_elabCallReceiverPush : ∀ f as a, Agree sc (rc.elabCallReceiverPush f as a) (rc'.elabCallReceiverPush f as a))
    (h_elabValueCall : ∀ Γ ix n e a, Agree sc (rc.elabValueCall Γ ix n e a) (rc'.elabValueCall Γ ix n e a))
    (h_elabCtor : ∀ as, Agree sc (rc.elabCtor as) (rc'.elabCtor as))
    (h_elabStmtP : ∀ s, Agree sc (rc.elabStmtP s) (rc'.elabStmtP s))
    (h_elabStmt1 : ∀ s, Agree sc (rc.elabStmt1 s) (rc'.elabStmt1 s))
    (h_loopExpr : ∀ Γ p e what, Agree sc (rc.loopExpr Γ p e what) (rc'.loopExpr Γ p e what))
    (h_loopQ : ∀ Γ inv, Agree sc (rc.loopQ Γ inv) (rc'.loopQ Γ inv))
    (h_elabStmtsP : ∀ ss, Agree sc (rc.elabStmtsP ss) (rc'.elabStmtsP ss))
    (h_elabScope : ∀ Γ ss, Agree sc (rc.elabScope Γ ss) (rc'.elabScope Γ ss))
    (h_elabTuple : ∀ ts rhs direct, Agree sc (rc.elabTuple ts rhs direct) (rc'.elabTuple ts rhs direct))
    (h_self : ∀ g (Γ : NCtx) as ρ,
      Agree sc (rc.trySelfBody g (Γ := Γ) as ρ) (rc'.trySelfBody g (Γ := Γ) as ρ))
    (h_branch : ∀ ss, Agree sc (rc.elabBranch ss) (rc'.elabBranch ss))
    (h_unchecked : ∀ ss, Agree {sc with unchecked := true}
      (rc.elabBranch ss) (rc'.elabBranch ss))
    (h_checked : ∀ o ss, Agree {sc with overflow := some o}
      (rc.elabBranch ss) (rc'.elabBranch ss)) :
    Agree sc (elabStmt1With C rc s) (elabStmt1With C rc' s) := by
  cases s <;> unfold elabStmt1With <;> agree_run
  all_goals first
    | contradiction
    | exact agree_refl _ _
    | (apply agree_listMapM; intro a ha; first | exact h_loopQ _ _ | exact h_loopExpr _ _ _ _)
    | (apply agree_optionMapM; intro a ha; exact h_loopExpr _ _ _ _)
    | exact h_hoist _
    | exact h_abiMemBytes _
    | exact h_abiEncode _ _ _ _ _
    | exact h_elabCall _ _ _ _ _
    | exact h_elabMemCall _ _ _ _
    | exact h_elabStorageCall _ _ _ _
    | exact h_elabCallReceiver _ _ _
    | exact h_elabCallReceiverPush _ _ _
    | exact h_elabValueCall _ _ _ _ _
    | exact h_elabCtor _
    | exact h_elabStmtP _
    | exact h_elabStmt1 _
    | exact h_loopExpr _ _ _ _
    | exact h_loopQ _ _
    | exact h_elabStmtsP _
    | exact h_elabScope _ _
    | exact h_elabTuple _ _ _
    | exact h_self _ _ _ _
    | exact h_branch _
    | exact h_unchecked _
    | exact h_checked _ _
    | (apply eagerArgsWith_agree; intros; exact h_hoist _)

end Solidity.ElabAgree
