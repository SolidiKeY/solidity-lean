import Solidity.Kernel.Taclet
import Solidity.Kernel.Elab

/-!
# The taclets are sound

`Taclet.sound`: every storage-family taclet's premise is correct for the
statement it rewrites, against the denotation of `Semantics.lean`, and so
(`Prog.run_eq`) against the interpreter.  What "correct" means depends on the
premise (`Premise.Correct`): an update has the statement's effect; new
statements have its effect off their scratch names, which are fresh for the
context the statement leaves; a split runs the branch its condition picks; a
closed goal is a revert, closed as the modality says.

No hypothesis beyond the constructor's own.  The per-rule freshness
conditions the untyped soundness theorems carry are the freshness proofs the
constructor takes, and the frame lemmas (`Frame.lean`) turn them into the
fact that binding a scratch name moves nothing the statement reads.
-/

namespace Solidity
namespace Kernel

open Semantics RuleSoundness

variable {C : Contract}

/-- Two runs end alike: both normally, in states that agree off `ns`, or both
abnormally.  The kind of abnormal end (revert, stuck) is not compared: the
modalities of the kernel do not tell them apart (a box holds unless the run
ends normally in a bad state, a diamond needs a normal end).  That is what
lets a rule evaluate the same pure parts in another order: `nsp.fld = sp2`
reads `sp2` before it resolves `nsp`, its premise resolves `nsp` first, and
when both fail they may fail differently. -/
def SameOk (ns : List Name) : Res State → Res State → Prop
  | .ok a, .ok b => EnvAgreeExcept ns a b
  | .error _, .error _ => True
  | _, _ => False

/-- Agreement is a same outcome. -/
theorem SameOk.of_agree {ns : List Name} {x y : Res State} (h : ResultsAgree ns x y) :
    SameOk ns x y := by
  cases x <;> cases y <;> simp_all [SameOk, ResultsAgree]

/-- Saving in two agreeing states ends alike. -/
theorem SameOk.save {ns : List Name} {σ' σ : State} (h : EnvAgreeExcept ns σ' σ) (r : Name)
    (segs : List Seg) (v : SVal) : SameOk ns (σ'.saveStorage r segs v) (σ.saveStorage r segs v) :=
  .of_agree (saveStorage_agree h r segs v)

/-- `σ` is a state of context `Γ`: the storage has the contract's layout, and
every local holds what `Γ` says (`Typing.StateWT`, for some heap typing).
The initial state of a contract is one, and running a statement keeps it one
(`execStmt_sound`, through `Stmt.erase_wt`). -/
def Typed (C : Contract) (Γ : Ctx) (σ : State) : Prop := ∃ H, StateWT Γ H C.layout σ

/-- In a state of `Γ`, a `bool` value evaluates to a boolean. -/
theorem Val.eval_bool {Γ : Ctx} {σ : State} (hσ : Typed C Γ σ) (v : Val C Γ .bool) {w : Value}
    (h : v.eval σ = .ok w) : ∃ b, w = .bool b := by
  obtain ⟨H, hwt⟩ := hσ
  have hev : evalValue σ v.erase = .ok (σ, w) := by rw [v.evalValue_erase σ, h]; rfl
  have := (evalValue_wt _ hwt v.erase_wt hev).2
  rw [v.erase_ty] at this
  cases w with
  | bool b => exact ⟨b, rfl⟩
  | int n => simp [Value.toSVal, SVal.hasTy] at this

/-- What a premise means for the statement it replaces, under the modality
`m`, from every state of the statement's context. -/
def Premise.Correct (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Premise C Γ Γ' → Prop
  | .update U => ∀ σ, Typed C Γ σ → s.run σ = U.apply σ
  | .unfold ns P _ =>
    (∀ n ∈ ns, isFresh C Γ' n = true) ∧ ∀ σ, Typed C Γ σ → SameOk ns (P.run σ) (s.run σ)
  | .split c P Q => ∀ σ, Typed C Γ σ → s.run σ = (do
      match ← c.eval σ with
      | .bool true => P.run σ
      | .bool false => Q.run σ
      | .int _ => .error .stuck)
  | .done b => ∀ σ, Typed C Γ σ → s.run σ = .error .revert ∧ (b = true ↔ m = .box)

/-! ## Binding a fresh name moves nothing -/

theorem _root_.Solidity.RuleSoundness.EnvAgreeExcept.setEnv_left {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) {n : Name} (hn : n ∈ ns) (b : Binding) :
    EnvAgreeExcept ns (s₁.setEnv n b) s₂ :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun m hm => by
    have hne : m ≠ n := fun heq => hm (heq ▸ hn)
    simpa [State.setEnv, lookupBy_setBy_ne hne] using h.env m hm,
    h.selfBalance⟩

/-- The `pure` a block ends with. -/
@[simp] theorem res_match_id {α : Type} (x : Res α) :
    (match x with | .error e => .error e | .ok v => .ok v) = x := by
  cases x <;> rfl

@[simp] theorem setEnv_env (σ : State) (n : Name) (b : Binding) :
    (σ.setEnv n b).env = setBy n b σ.env := rfl

@[simp] theorem getEnv_setEnv_self (σ : State) (n : Name) (b : Binding) :
    (σ.setEnv n b).getEnv n = .ok b := by
  simp [State.getEnv]

theorem getEnv_setEnv_ne (σ : State) {n n' : Name} (h : n ≠ n') (b : Binding) :
    (σ.setEnv n' b).getEnv n = σ.getEnv n := by
  simp [State.getEnv, lookupBy_setBy_ne h]

@[simp] theorem findStorage_setEnv (σ : State) (n : Name) (b : Binding) (r : Name) (segs : List Seg) :
    (σ.setEnv n b).findStorage r segs = σ.findStorage r segs := rfl

/-- A copy from a weakened path reads what the original does. -/
@[simp] theorem Src.value_copy_weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') (σ : State) {R : RefTy}
    (p : SPath C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true) :
    Src.value σ (.copy (p.weaken h) hm) = Src.value σ (.copy p hm) := by
  simp only [Src.value, SPath.resolve_weaken]

/-- A bound name is not a fresh one. -/
theorem ne_of_bound_fresh {Γ : Ctx} {x y : Name} {b : BTy} (hx : lookupBy x Γ = some b)
    (hy : isFresh C Γ y = true) : x ≠ y := fun he => by
  subst he; rw [(isFresh_iff.mp hy).1] at hx; cases hx

/-- Binding `n` agrees with not binding it, off `[n]`. -/
theorem agree_setEnv (σ : State) (n : Name) (b : Binding) :
    EnvAgreeExcept [n] (σ.setEnv n b) σ :=
  (EnvAgreeExcept.refl [n] σ).setEnv_left (by simp) b

section Fresh

variable {Γ : Ctx} {n : Name} (hn : isFresh C Γ n = true) (σ : State) (b : Binding)
include hn

theorem Simple.eval_setEnv {p : PrimTy} (s : Simple C Γ p) : s.eval (σ.setEnv n b) = s.eval σ :=
  s.eval_frame (agree_setEnv σ n b) (by simpa using hn)

theorem Val.eval_setEnv {p : PrimTy} (v : Val C Γ p) : v.eval (σ.setEnv n b) = v.eval σ :=
  v.eval_frame (agree_setEnv σ n b) (by simpa using hn)

theorem SPath.resolve_setEnv {T : Ty} (p : SPath C Γ T) : p.resolve (σ.setEnv n b) = p.resolve σ :=
  p.resolve_frame (agree_setEnv σ n b) (by simpa using hn)

theorem Loc.resolve_setEnv {T : Ty} (l : Loc C Γ T) : l.resolve (σ.setEnv n b) = l.resolve σ :=
  l.resolve_frame (agree_setEnv σ n b) (by simpa using hn)

theorem Loc.target_setEnv {T : Ty} (l : Loc C Γ T) : l.target (σ.setEnv n b) = l.target σ :=
  l.target_frame (agree_setEnv σ n b) (by simpa using hn)

theorem Src.value_setEnv {T : Ty} (r : Src C Γ T) : r.value (σ.setEnv n b) = r.value σ :=
  r.value_frame (agree_setEnv σ n b) (by simpa using hn)

end Fresh


/-! ## Operators after a capture -/

/-- The local just declared reads what it was set to. -/
@[simp] theorem Simple.eval_new {Γ : Ctx} (x : Name) (p : PrimTy) (σ : State) (v : Value) :
    (Simple.new (C := C) (Γ := Γ) x p).eval (σ.setEnv x (.val v)) = .ok v := by
  simp [Simple.new, Simple.eval]; rfl

section Capture

variable {Γ : Ctx} {p : PrimTy} {se : Name} (hse : isFresh C Γ se = true)
include hse

/-- The left operand captured: `se ⊕ e` after `T se = nse;` is `nse ⊕ e`. -/
theorem binop_left_eval (op : BinOp) (hop : op.accepts p = true) (nse e : Val C Γ p)
    (hw : Ctx.Sub C Γ (Ctx.val Γ se p)) (σ : State) {v : Value} (hv : nse.eval σ = .ok v) :
    (Val.binop op hop (.simple (Simple.new se p)) (e.weaken hw)).eval (σ.setEnv se (.val v)) =
      (Val.binop op hop nse e).eval σ := by
  simp only [Val.eval, hv, Simple.eval_new, Val.eval_weaken, bind, Except.bind, pure, Except.pure]
  rw [e.eval_setEnv hse]

/-- The right operand captured, for an operator that does not short-circuit:
`se ⊕ se'` after `T se' = nse;` is `se ⊕ nse`, up to which one fails first. -/
theorem binop_right_eval (op : BinOp) (hop : op.accepts p = true) (hsc : op.shortCircuits = false)
    (a : Simple C Γ p) (nse : Val C Γ p) (hw : Ctx.Sub C Γ (Ctx.val Γ se p)) (σ : State)
    {v : Value} (hv : nse.eval σ = .ok v) :
    (Val.binop op hop (.simple (a.weaken hw)) (.simple (Simple.new se p))).eval (σ.setEnv se (.val v)) =
      (Val.binop op hop (.simple a) nse).eval σ := by
  simp only [Val.eval, Simple.eval_weaken, Simple.eval_new]
  rw [a.eval_setEnv hse]
  cases a.eval σ with
  | error _ => rfl
  | ok lv =>
    cases op <;> simp [BinOp.shortCircuits] at hsc <;> simp [hv, bind, Except.bind]

omit hse in
/-- The operand captured: `⊖se` after `T se = nse;` is `⊖nse`. -/
theorem unop_capture_eval (op : UnOp) (hop : op.accepts p = true) (nse : Val C Γ p) (σ : State)
    {v : Value} (hv : nse.eval σ = .ok v) :
    (Val.unop op hop (.simple (Simple.new (C := C) (Γ := Γ) se p))).eval (σ.setEnv se (.val v)) =
      (Val.unop op hop nse).eval σ := by
  simp only [Val.eval, hv, Simple.eval_new, bind, Except.bind]

end Capture

/-- A local set to the same value in two agreeing states. -/
theorem SameOk.setEnv_val {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (x : Name)
    (r : Res Value) :
    SameOk ns (do pure (σ₁.setEnv x (.val (← r)))) (do pure (σ.setEnv x (.val (← r)))) := by
  cases r
  · trivial
  · exact h.setEnv_both _ _

/-- Close `EnvAgreeExcept ns (…(σ.setEnv a _)….setEnv b _) σ` with `a b ∈ ns`, and
`EnvAgreeExcept ns (σ'.setEnv x b) (σ.setEnv x b)` from the same inside. -/
macro "agree_tac" : tactic => `(tactic| (
  repeat (first
    | exact EnvAgreeExcept.refl _ _
    | refine EnvAgreeExcept.setEnv_both ?_ _ _
    | refine EnvAgreeExcept.setEnv_left ?_ (by simp) _)))

/-! ## Soundness -/

-- The cases share their simp sets, so each uses only part of them.
set_option linter.unusedSimpArgs false in
/-- **The taclets are sound.**  Every storage-family taclet's premise is
correct for its statement.  `alice.age = 10;` is `storageFieldWriteSave`, and
its update saves `10` at `alice.age` exactly as running the statement does;
`people[i].age = 10;` is `storageFieldWrite_unfold_leftFst`, whose three
statements run as it does except on the fresh `se` and `sp`. -/
theorem Taclet.sound {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {pr : Premise C Γ Γ'}
    (d : Taclet C m s pr) : pr.Correct m s := by
  cases d
  all_goals first
    | (intro σ _; rfl)
    | skip
  case valueDeclSkip p x hx => intro σ _; cases p <;> rfl
  case revertBox h => intro σ _; exact ⟨rfl, by simp [h]⟩
  case revertDiamond h => intro σ _; exact ⟨rfl, by simp [h]⟩
  case storageFieldWrite_unfold_leftFst s p nsp hn f hf e se sp hse hsp =>
    have hsp₀ := isFresh_of_sub (Ctx.Sub.fresh hse _) hsp
    refine ⟨by simp [hse, hsp₀], fun σ _ => SameOk.of_agree ?_⟩
    simp only [Prog.run, Stmt.run, SPath.resolve_weaken, Simple.eval_weaken, Src.value, Val.eval,
      bind_pure]
    cases he : e.eval σ with
    | error _ => rfl
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [nsp.resolve_setEnv hse]
      simp only [Loc.target, Loc.resolve]
      cases hr : nsp.resolve σ with
      | error _ => rfl
      | ok rs =>
        have hne := ne_of_isFresh_setBy hsp
        simp only [SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval,
          getEnv_setEnv_ne _ hne, getEnv_setEnv_self, setEnv_env, lookupBy_setBy_self, bind,
          Except.bind, pure, Except.pure, res_match_id]
        apply saveStorage_agree
        exact ((EnvAgreeExcept.refl [se, sp] σ).setEnv_left (n := se) (by simp) _).setEnv_left
          (n := sp) (by simp) _
  case storageFieldWriteStorageRef_unfold_leftFst s R nsp hn f hf src hm sp hsp =>
    refine ⟨by simp [hsp], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Loc.target, Loc.resolve, Src.value_copy_weaken]
    cases h₁ : nsp.resolve σ with
    | error e => cases Src.value σ (.copy src hm) <;> simp [bind, Except.bind, SameOk]
    | ok rs =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [Src.value_setEnv hsp]
      cases h₂ : Src.value σ (.copy src hm) <;>
        simp [SameOk, SPath.new, SPath.resolve, envPath, h₁, bind, Except.bind, pure, Except.pure]
      exact SameOk.save (by agree_tac) _ _ _

  -- A value capture in front of a write: the source is read first either way.
  case storageRootWriteValueRhsCapture p r hΓ hr nse hn se hse =>
    refine ⟨by simp [hse], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
    cases nse.eval σ with
    | error _ => simp [SameOk, bind, Except.bind]
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [Loc.target_setEnv hse]
      simp only [Val.eval, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure]
      cases Loc.target σ (.root r hΓ hr) <;> simp [SameOk]
      exact SameOk.save (by agree_tac) _ _ _
  case fieldWriteValueRhsCapture s p sp hs f hf nse hn se hse =>
    refine ⟨by simp [hse], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
    cases nse.eval σ with
    | error _ => simp [SameOk, bind, Except.bind]
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [Loc.target_setEnv hse]
      simp only [Val.eval, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure]
      cases Loc.target σ (.field sp f hf) <;> simp [SameOk]
      exact SameOk.save (by agree_tac) _ _ _
  case indexWriteValueRhsCapture R₀ kp p it sp hs ie nse hn se hse =>
    refine ⟨by simp [hse], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
    cases nse.eval σ with
    | error _ => simp [SameOk, bind, Except.bind]
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [Loc.target_setEnv hse]
      simp only [Val.eval, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure]
      cases Loc.target σ (.index it sp (.simple ie)) <;> simp [SameOk]
      exact SameOk.save (by agree_tac) _ _ _
  -- `uint v = e` is `uint v; v = e`: `e` does not read the fresh `v`.
  case localValueDeclInitDrop p x hx e =>
    refine ⟨by simp, fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Val.eval_weaken, bind, Except.bind, pure, Except.pure]
    rw [Val.eval_setEnv hx]
    cases e.eval σ <;> simp [SameOk, SemanticsProperties.State.setEnv_setEnv_absorb] <;> agree_tac
  -- Delete through a captured receiver.
  case storageFieldDelete_unfold_leftFst s T nsp hn f hf sp hsp =>
    refine ⟨by simp [hsp], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Loc.resolve]
    cases nsp.resolve σ with
    | error _ => simp [SameOk, bind, Except.bind]
    | ok rs =>
      simp only [Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure, findStorage_setEnv]
      cases σ.findStorage rs.1 (rs.2 ++ [.field f]) <;> simp [SameOk]
      exact SameOk.save (by agree_tac) _ _ _
  case storageIndexDelete_unfold_leftFst R₀ kp V it nsp hn e sp hsp =>
    refine ⟨by simp [hsp], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
    cases nsp.resolve σ with
    | error _ => simp [SameOk, bind, Except.bind]
    | ok rs =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [Val.eval_setEnv hsp]
      simp only [Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure, findStorage_setEnv]
      cases e.eval σ with
      | error _ => simp [SameOk, bind, Except.bind]
      | ok v =>
        cases v with
        | bool _ => simp [SameOk, Value.asInt, bind, Except.bind]
        | int i =>
          simp only [Value.asInt, bind, Except.bind, pure, Except.pure]
          cases σ.findStorage rs.1 (rs.2 ++ [.at i]) <;> simp [SameOk]
          exact SameOk.save (by agree_tac) _ _ _
  case storageIndexDeleteNonSimpleIndexCapture R₀ kp V it sp hs nse hn ie hie =>
    refine ⟨by simp [hie], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
    cases h₁ : nse.eval σ with
    | error _ => cases sp.resolve σ <;> simp [SameOk, h₁, bind, Except.bind, pure, Except.pure]
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [SPath.resolve_setEnv hie]
      cases h₂ : sp.resolve σ with
      | error _ => simp [SameOk, h₁, bind, Except.bind, pure, Except.pure]
      | ok rs =>
        cases v with
        | bool _ => simp [SameOk, h₁, Value.asInt, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure]
        | int i =>
          simp only [h₁, Value.asInt, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure, findStorage_setEnv]
          cases σ.findStorage rs.1 (rs.2 ++ [.at i]) <;> simp [SameOk]
          exact SameOk.save (by agree_tac) _ _ _

  -- A copy from a member or an entry, through a captured alias: same order.
  case storageFieldRead_unfold_rightSndResult s R l hl hm sp hs f hf se hse =>
    refine ⟨by simp [hse], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
    cases sp.resolve σ with
    | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
    | ok rs =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [Loc.target_setEnv hse]
      simp only [Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure, findStorage_setEnv]
      cases σ.findStorage rs.1 (rs.2 ++ [.field f]) with
      | error _ => simp [SameOk]
      | ok v =>
        simp only [bind, Except.bind, pure, Except.pure]
        cases Loc.target σ l <;> simp [SameOk]
        exact SameOk.save (by agree_tac) _ _ _
  case storageIndexRead_unfold_rightSndResult R₀ kp R l hl hm it sp hs ie se hse =>
    refine ⟨by simp [hse], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
    cases sp.resolve σ with
    | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
    | ok rs =>
      simp only [bind, Except.bind, pure, Except.pure]
      cases hi : ie.eval σ with
      | error _ => simp [SameOk, Val.eval, hi, bind, Except.bind, pure, Except.pure]
      | ok v =>
        cases v with
        | bool _ => simp [SameOk, Val.eval, hi, Value.asInt, bind, Except.bind, pure, Except.pure]
        | int i =>
          simp only [Val.eval, hi, Value.asInt, bind, Except.bind, pure, Except.pure]
          rw [Loc.target_setEnv hse]
          simp only [Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure, findStorage_setEnv]
          cases σ.findStorage rs.1 (rs.2 ++ [.at i]) with
          | error _ => simp [SameOk]
          | ok v =>
            simp only [bind, Except.bind, pure, Except.pure]
            cases Loc.target σ l <;> simp [SameOk]
            exact SameOk.save (by agree_tac) _ _ _
  -- An index write through a captured receiver and index: same order.
  case storageIndexWrite_unfold_leftFst R₀ kp p it nsp hn e₁ e₂ se sp ie hse hsp hie =>
    have hsp₀ := isFresh_of_sub (Ctx.Sub.fresh hse _) hsp
    have hie₁ := isFresh_of_sub (Ctx.Sub.fresh hsp _) hie
    have hie₀ := isFresh_of_sub (Ctx.Sub.fresh hse _) hie₁
    have h₁ := ne_of_isFresh_setBy hsp
    have h₂ := ne_of_isFresh_setBy hie
    have h₃ := ne_of_bound_fresh ((Ctx.Sub.fresh hsp _).local_ _ _ (lookupBy_setBy_self ..)) hie
    refine ⟨by simp [hse, hsp₀, hie₀], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Src.value, Loc.target, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
    cases e₂.eval σ with
    | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
    | ok v₂ =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [nsp.resolve_setEnv hse]
      cases nsp.resolve σ with
      | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
      | ok rs =>
        simp only [bind, Except.bind, pure, Except.pure]
        rw [e₁.eval_setEnv hsp₀, e₁.eval_setEnv hse]
        cases e₁.eval σ with
        | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
        | ok v₁ =>
          cases v₁ with
          | bool _ =>
            simp [SameOk, Value.asInt, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure, getEnv_setEnv_ne _ h₃,
              getEnv_setEnv_ne _ h₁, lookupBy_setBy_ne h₂]
          | int i =>
            simp only [Value.asInt, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure, getEnv_setEnv_ne _ h₃, getEnv_setEnv_ne _ h₁,
              lookupBy_setBy_ne h₂]
            exact SameOk.save (by agree_tac) _ _ _

  -- Order-changing rules: the premise evaluates the same parts, in another order.
  case storageIndexWriteStorageRef_unfold_leftFst R₀ kp R it nsp hn e src hm sp ie hsp hie =>
    have hie₀ := isFresh_of_sub (Ctx.Sub.fresh hsp _) hie
    have hne := ne_of_isFresh_setBy hie
    refine ⟨by simp [hsp, hie₀], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Loc.target, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
    cases h₁ : nsp.resolve σ with
    | error _ => cases Src.value σ (.copy src hm) <;> simp [SameOk, bind, Except.bind, pure, Except.pure, h₁]
    | ok rs =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [e.eval_setEnv hsp]
      cases h₂ : e.eval σ with
      | error _ => cases Src.value σ (.copy src hm) <;> simp [SameOk, bind, Except.bind, pure, Except.pure, h₁, h₂]
      | ok v =>
        simp only [bind, Except.bind, pure, Except.pure]
        rw [Src.value_setEnv hie₀, Src.value_setEnv hsp]
        cases h₃ : Src.value σ (.copy src hm) with
        | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
        | ok sv =>
          cases v with
          | bool _ => simp [SameOk, bind, Except.bind, pure, Except.pure, h₁, h₂, Value.asInt, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, lookupBy_setBy_ne hne]
          | int i =>
            simp only [h₁, h₂, Value.asInt, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure, lookupBy_setBy_ne hne]
            exact SameOk.save (by agree_tac) _ _ _
  case storageIndexWriteNonSimpleIndexCapture R₀ kp p it sp hs nse hn e se ie hse hie =>
    have hie₀ := isFresh_of_sub (Ctx.Sub.fresh hse _) hie
    have hne := ne_of_isFresh_setBy hie
    refine ⟨by simp [hse, hie₀], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Src.value, Loc.target, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
    cases h₁ : e.eval σ with
    | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [nse.eval_setEnv hse]
      cases h₂ : nse.eval σ with
      | error _ => cases sp.resolve σ <;> simp [SameOk, bind, Except.bind, pure, Except.pure, h₂]
      | ok w =>
        simp only [bind, Except.bind, pure, Except.pure]
        rw [sp.resolve_setEnv hie₀, sp.resolve_setEnv hse]
        cases h₃ : sp.resolve σ with
        | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, getEnv_setEnv_ne _ hne]
        | ok rs =>
          cases w with
          | bool _ => simp [SameOk, bind, Except.bind, pure, Except.pure, h₂, Value.asInt, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, getEnv_setEnv_ne _ hne]
          | int i =>
            simp only [h₂, Value.asInt, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure, getEnv_setEnv_ne _ hne]
            exact SameOk.save (by agree_tac) _ _ _
  case storageIndexWriteStorageRefNonSimpleIndexCapture R₀ kp R it sp hs nse hn src hm ie hie =>
    refine ⟨by simp [hie], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Loc.target, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
    cases h₁ : nse.eval σ with
    | error _ =>
      cases Src.value σ (.copy src hm) <;> cases sp.resolve σ <;> simp [SameOk, bind, Except.bind, pure, Except.pure, h₁]
    | ok w =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [Src.value_setEnv hie, sp.resolve_setEnv hie]
      cases h₂ : Src.value σ (.copy src hm) with
      | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
      | ok sv =>
        simp only [bind, Except.bind, pure, Except.pure]
        cases h₃ : sp.resolve σ with
        | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
        | ok rs =>
          cases w with
          | bool _ => simp [SameOk, bind, Except.bind, pure, Except.pure, h₁, Value.asInt, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
          | int i =>
            simp only [h₁, Value.asInt, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure]
            exact SameOk.save (by agree_tac) _ _ _


  -- Operators into a local.
  case binopUnfoldLeft p op hop x h nse hn e se hse =>
    refine ⟨by simp [hse], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure]
    cases hv : nse.eval σ with
    | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, hv]
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [binop_left_eval hse op hop nse e _ σ hv]
      exact SameOk.setEnv_val (by agree_tac) _ _
  case binopUnfoldRight p op hop hsc x h a nse hn se hse =>
    refine ⟨by simp [hse], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure]
    cases hv : nse.eval σ with
    | error _ =>
      simp only [bind, Except.bind, pure, Except.pure, Val.eval]
      cases a.eval σ with
      | error _ => simp [SameOk]
      | ok lv => cases op <;> simp [BinOp.shortCircuits] at hsc <;> simp [SameOk, hv, bind, Except.bind, pure, Except.pure]
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [binop_right_eval hse op hop hsc a nse _ σ hv]
      exact SameOk.setEnv_val (by agree_tac) _ _
  case unopCapture p op hop x h nse hn se hse =>
    refine ⟨by simp [hse], fun σ _ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure]
    cases hv : nse.eval σ with
    | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, hv]
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [unop_capture_eval op hop nse σ hv]
      exact SameOk.setEnv_val (by agree_tac) _ _
  -- Short-circuit: in a state of `Γ` the right operand is a boolean.
  case logicalAndShortCircuitRhs hop x h a nse hn =>
    refine ⟨by simp, fun σ hσ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Val.eval]
    cases a.eval σ with
    | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
    | ok lv =>
      cases lv with
      | int _ =>
        simp only [bind, Except.bind, pure, Except.pure]
        cases hv : nse.eval σ <;> simp [SameOk, applyBinOp, Value.asBool, bind, Except.bind, pure, Except.pure]
      | bool b =>
        cases b with
        | false => simp [SameOk, bind, Except.bind, pure, Except.pure, Simple.eval]; exact EnvAgreeExcept.refl _ _
        | true =>
          simp only [bind, Except.bind, pure, Except.pure]
          cases hv : nse.eval σ with
          | error _ => simp [SameOk]
          | ok w =>
            obtain ⟨c, rfl⟩ := Val.eval_bool hσ nse hv
            simp [SameOk, applyBinOp, Value.asBool, checkArith, bind, Except.bind, pure, Except.pure]
            exact EnvAgreeExcept.refl _ _
  case logicalOrShortCircuitRhs hop x h a nse hn =>
    refine ⟨by simp, fun σ hσ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Val.eval]
    cases a.eval σ with
    | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
    | ok lv =>
      cases lv with
      | int _ =>
        simp only [bind, Except.bind, pure, Except.pure]
        cases hv : nse.eval σ <;> simp [SameOk, applyBinOp, Value.asBool, bind, Except.bind, pure, Except.pure]
      | bool b =>
        cases b with
        | true => simp [SameOk, bind, Except.bind, pure, Except.pure, Simple.eval]; exact EnvAgreeExcept.refl _ _
        | false =>
          simp only [bind, Except.bind, pure, Except.pure]
          cases hv : nse.eval σ with
          | error _ => simp [SameOk]
          | ok w =>
            obtain ⟨c, rfl⟩ := Val.eval_bool hσ nse hv
            simp [SameOk, applyBinOp, Value.asBool, checkArith, bind, Except.bind, pure, Except.pure]
            exact EnvAgreeExcept.refl _ _
  -- Step 1, for every `lhs`: read a member through a captured receiver.
  case storageFieldRead_unfold_rightFst s T nsp hn f hf sp k hsp =>
    refine ⟨by simp [hsp], fun σ _ => ?_⟩
    cases k with
    | «local» x h =>
      simp only [Hole.fill, Hole.extend, Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken, Val.eval]
      cases nsp.resolve σ with
      | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
      | ok rs =>
        simp only [bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, findStorage_setEnv, Loc.resolve]
        cases σ.findStorage rs.1 (rs.2 ++ [.field f]) with
        | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
        | ok v => cases hv : v.asValue <;> simp [SameOk, hv, bind, Except.bind, pure, Except.pure] <;> agree_tac
    | rebind x h =>
      simp only [Hole.fill, Hole.extend, Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
      cases nsp.resolve σ <;> simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self] <;> agree_tac
    | decl c R x hx =>
      simp only [Hole.fill, Hole.extend, Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
      cases nsp.resolve σ <;> simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self] <;> agree_tac
    | copy l h =>
      simp only [Hole.fill, Hole.extend, Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
      cases nsp.resolve σ with
      | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
      | ok rs =>
        simp only [bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, findStorage_setEnv, Loc.resolve]
        rw [Loc.target_setEnv hsp]
        cases σ.findStorage rs.1 (rs.2 ++ [.field f]) with
        | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
        | ok v =>
          simp only [bind, Except.bind, pure, Except.pure]
          cases Loc.target σ l <;> simp [SameOk]
          exact SameOk.save (by agree_tac) _ _ _
  -- Step 1, for every `lhs`: read an entry through a captured receiver.
  case storageIndexRead_unfold_rightFst R₀ kp V it nsp hn e sp k hsp =>
    refine ⟨by simp [hsp], fun σ _ => ?_⟩
    have hsp₀ := isFresh_of_sub k.sub hsp
    cases k with
    | «local» x h =>
      simp only [Hole.fill, Hole.extend, Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken, Val.eval]
      cases nsp.resolve σ with
      | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
      | ok rs =>
        simp only [bind, Except.bind, pure, Except.pure]
        rw [e.eval_setEnv hsp₀]
        cases e.eval σ with
        | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
        | ok w =>
          cases w with
          | bool _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Value.asInt, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
          | int i =>
            simp only [Value.asInt, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, findStorage_setEnv, Loc.resolve]
            cases σ.findStorage rs.1 (rs.2 ++ [.at i]) with
            | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
            | ok v => cases hv : v.asValue <;> simp [SameOk, hv, bind, Except.bind, pure, Except.pure] <;> agree_tac
    | rebind x h =>
      simp only [Hole.fill, Hole.extend, Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
      cases nsp.resolve σ with
      | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
      | ok rs =>
        simp only [bind, Except.bind, pure, Except.pure]
        rw [e.eval_setEnv hsp₀]
        cases e.eval σ with
        | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
        | ok w => cases w <;> simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, Value.asInt] <;> agree_tac
    | decl c R x hx =>
      simp only [Hole.fill, Hole.extend, Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
      cases nsp.resolve σ with
      | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
      | ok rs =>
        simp only [bind, Except.bind, pure, Except.pure]
        rw [e.eval_setEnv hsp₀]
        cases e.eval σ with
        | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
        | ok w => cases w <;> simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, Value.asInt] <;> agree_tac
    | copy l h =>
      simp only [Hole.fill, Hole.extend, Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
      cases nsp.resolve σ with
      | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
      | ok rs =>
        simp only [bind, Except.bind, pure, Except.pure]
        rw [e.eval_setEnv hsp₀]
        cases e.eval σ with
        | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
        | ok w =>
          cases w with
          | bool _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Value.asInt, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
          | int i =>
            simp only [Value.asInt, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, findStorage_setEnv, Loc.resolve]
            rw [Loc.target_setEnv hsp₀]
            cases σ.findStorage rs.1 (rs.2 ++ [.at i]) with
            | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
            | ok v =>
              simp only [bind, Except.bind, pure, Except.pure]
              cases Loc.target σ l <;> simp [SameOk]
              exact SameOk.save (by agree_tac) _ _ _
  -- Step 1, for every `lhs`: capture a non-simple index (the receiver is
  -- then resolved after it).
  case storageIndexRead_unfold_rightSndIndex R₀ kp V it sp hs nse hn ie k hie =>
    refine ⟨by simp [hie], fun σ _ => ?_⟩
    have hie₀ := isFresh_of_sub k.sub hie
    cases k with
    | «local» x h =>
      simp only [Hole.fill, Hole.extend, Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken, Val.eval]
      cases h₁ : nse.eval σ with
      | error _ => cases sp.resolve σ <;> simp [SameOk, bind, Except.bind, pure, Except.pure, h₁]
      | ok w =>
        simp only [bind, Except.bind, pure, Except.pure]
        rw [sp.resolve_setEnv hie₀]
        cases sp.resolve σ with
        | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
        | ok rs =>
          cases w with
          | bool _ => simp [SameOk, bind, Except.bind, pure, Except.pure, h₁, Value.asInt, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
          | int i =>
            simp only [h₁, Value.asInt, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, findStorage_setEnv, Loc.resolve]
            cases σ.findStorage rs.1 (rs.2 ++ [.at i]) with
            | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
            | ok v => cases hv : v.asValue <;> simp [SameOk, hv, bind, Except.bind, pure, Except.pure] <;> agree_tac
    | rebind x h =>
      simp only [Hole.fill, Hole.extend, Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
      cases h₁ : nse.eval σ with
      | error _ => cases sp.resolve σ <;> simp [SameOk, bind, Except.bind, pure, Except.pure, h₁]
      | ok w =>
        simp only [bind, Except.bind, pure, Except.pure]
        rw [sp.resolve_setEnv hie₀]
        cases sp.resolve σ with
        | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
        | ok rs => cases w <;> simp [SameOk, bind, Except.bind, pure, Except.pure, h₁, Value.asInt, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self] <;> agree_tac
    | decl c R x hx =>
      simp only [Hole.fill, Hole.extend, Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
      cases h₁ : nse.eval σ with
      | error _ => cases sp.resolve σ <;> simp [SameOk, bind, Except.bind, pure, Except.pure, h₁]
      | ok w =>
        simp only [bind, Except.bind, pure, Except.pure]
        rw [sp.resolve_setEnv hie₀]
        cases sp.resolve σ with
        | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
        | ok rs => cases w <;> simp [SameOk, bind, Except.bind, pure, Except.pure, h₁, Value.asInt, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self] <;> agree_tac
    | copy l h =>
      simp only [Hole.fill, Hole.extend, Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve, Loc.resolve, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
      cases h₁ : nse.eval σ with
      | error _ => cases sp.resolve σ <;> simp [SameOk, bind, Except.bind, pure, Except.pure, h₁]
      | ok w =>
        simp only [bind, Except.bind, pure, Except.pure]
        rw [sp.resolve_setEnv hie₀]
        cases sp.resolve σ with
        | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
        | ok rs =>
          cases w with
          | bool _ => simp [SameOk, bind, Except.bind, pure, Except.pure, h₁, Value.asInt, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
          | int i =>
            simp only [h₁, Value.asInt, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, findStorage_setEnv, Loc.resolve]
            rw [Loc.target_setEnv hie₀]
            cases σ.findStorage rs.1 (rs.2 ++ [.at i]) with
            | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, SPath.new, SPath.resolve, Loc.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self]
            | ok v =>
              simp only [bind, Except.bind, pure, Except.pure]
              cases Loc.target σ l <;> simp [SameOk]
              exact SameOk.save (by agree_tac) _ _ _

section Examples

/-- `alice.age = 10;` is `storageFieldWriteSave`, and its update is the
statement's effect from every state. -/
example : match ksol[StandardExample]{ alice.age = 10; } with
    | .cons s .nil => ∀ σ, Typed StandardExample [] σ → s.run σ = (Upd.save (.field (.loc (.root "alice" rfl rfl)) "age" rfl)
        (.val (.simple (.lit 10 rfl))) : Upd StandardExample []).apply σ
    | _ => False :=
  Taclet.sound (m := .box) (.storageFieldWriteSave _ rfl _ _ _)

/-- `people[1].age = 10;` (a mapping of `Person`s is `folks`) is
`storageFieldWrite_unfold_leftFst`: its three statements end as it does,
off the fresh `se` and `sp`. -/
example : match ksol[StandardExample]{ folks[1].age = 10; } with
    | .cons s .nil => ∃ ns Γ₁ P h, Taclet StandardExample .diamond s (.unfold (Γ₁ := Γ₁) ns P h) ∧
        ∀ σ, Typed StandardExample [] σ → SameOk ns (P.run σ) (s.run σ)
    | _ => False :=
  let d := Taclet.storageFieldWrite_unfold_leftFst (m := .diamond) _ rfl _ rfl _ "se" "sp" rfl rfl
  ⟨_, _, _, _, d, (Taclet.sound d).2⟩

end Examples

end Kernel
end Solidity
