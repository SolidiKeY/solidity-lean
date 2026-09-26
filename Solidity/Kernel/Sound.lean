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

/-- A run ends as itself. -/
theorem SameOk.refl (ns : List Name) : (x : Res State) → SameOk ns x x
  | .ok _ => EnvAgreeExcept.refl _ _
  | .error _ => trivial

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
`m`, from every state. -/
def Premise.Correct (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Premise C Γ Γ' → Prop
  | .update U => ∀ σ, s.run σ = U.apply σ
  | .unfold ns P _ =>
    (∀ n ∈ ns, isFresh C Γ' n = true) ∧ ∀ σ, SameOk ns (P.run σ) (s.run σ)
  | .split c P Q => ∀ σ, s.run σ = (do
      match ← c.eval σ with
      | .bool true => P.run σ
      | .bool false => Q.run σ
      | .int _ => .error .stuck)
  | .done b => ∀ σ, s.run σ = .error .revert ∧ (b = true ↔ m = .box)

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
theorem binop_left_eval {q : PrimTy} (op : BinOp) (hop : op.accepts p = true) (hq : op.ret p = q)
    (nse e : Val C Γ p) (hw : Ctx.Sub C Γ (Ctx.val Γ se p)) (σ : State) {v : Value}
    (hv : nse.eval σ = .ok v) :
    (Val.binop op hop hq (.simple (Simple.new se p)) (e.weaken hw)).eval (σ.setEnv se (.val v)) =
      (Val.binop op hop hq nse e).eval σ := by
  simp only [Val.eval, hv, Simple.eval_new, Val.eval_weaken, bind, Except.bind, pure, Except.pure]
  rw [e.eval_setEnv hse]

/-- The right operand captured, for an operator that does not short-circuit:
`se ⊕ se'` after `T se' = nse;` is `se ⊕ nse`, up to which one fails first. -/
theorem binop_right_eval {q : PrimTy} (op : BinOp) (hop : op.accepts p = true) (hq : op.ret p = q)
    (hsc : op.shortCircuits = false) (a : Simple C Γ p) (nse : Val C Γ p)
    (hw : Ctx.Sub C Γ (Ctx.val Γ se p)) (σ : State) {v : Value} (hv : nse.eval σ = .ok v) :
    (Val.binop op hop hq (.simple (a.weaken hw)) (.simple (Simple.new se p))).eval
        (σ.setEnv se (.val v)) =
      (Val.binop op hop hq (.simple a) nse).eval σ := by
  simp only [Val.eval, Simple.eval_weaken, Simple.eval_new]
  rw [a.eval_setEnv hse]
  cases a.eval σ with
  | error _ => rfl
  | ok lv =>
    cases op <;> simp [BinOp.shortCircuits] at hsc <;> simp [hv, bind, Except.bind]

omit hse in
/-- The operand captured: `⊖se` after `T se = nse;` is `⊖nse`. -/
theorem unop_capture_eval {q : PrimTy} (op : UnOp) (hop : op.accepts p = true) (hq : op.ret p = q)
    (nse : Val C Γ p) (σ : State) {v : Value} (hv : nse.eval σ = .ok v) :
    (Val.unop op hop hq (.simple (Simple.new (C := C) (Γ := Γ) se p))).eval (σ.setEnv se (.val v)) =
      (Val.unop op hop hq nse).eval σ := by
  simp only [Val.eval, hv, Simple.eval_new, bind, Except.bind]

end Capture

/-- A local set to the same value in two agreeing states. -/
theorem SameOk.setEnv_val {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (x : Name)
    (r : Res Value) :
    SameOk ns (do pure (σ₁.setEnv x (.val (← r)))) (do pure (σ.setEnv x (.val (← r)))) := by
  cases r
  · trivial
  · exact h.setEnv_both _ _

/-- A compound write at a resolved location, in two agreeing states. -/
theorem opStore_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (op : BinOp)
    (p : PrimTy) (r : Name) (segs : List Seg) (v : Value) :
    SameOk ns (opStore σ₁ op p r segs v) (opStore σ op p r segs v) := by
  simp only [opStore, findStorage_congr h, bind, Except.bind]
  repeat' split
  all_goals first | trivial | exact SameOk.save h _ _ _ | simp_all

/-- A memory location reads alike in two agreeing states. -/
theorem readLoc_mem_congr {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) :
    (loc : Semantics.Loc) → (hl : (∃ id f, loc = .memoryField id f) ∨ ∃ id i, loc = .memoryIndex id i) →
      readLoc σ₁ loc = readLoc σ loc
  | .memoryField id f, _ => by simp only [readLoc, getObj_congr h]
  | .memoryIndex id i, _ => by simp only [readLoc, getObj_congr h]
  | .stack _, hl | .storage .., hl | .storageLocal _, hl | .memoryRoot _, hl => by
    rcases hl with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h

/-- A memory location is written alike in two agreeing states. -/
theorem writeLoc_mem_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (v : Value) :
    (loc : Semantics.Loc) → (hl : (∃ id f, loc = .memoryField id f) ∨ ∃ id i, loc = .memoryIndex id i) →
      SameOk ns (writeLoc σ₁ loc v) (writeLoc σ loc v)
  | .memoryField id f, _ => by
    simp only [writeLoc, getObj_congr h]
    cases σ.getObj id with
    | error _ => trivial
    | ok o =>
      cases o with
      | array _ => trivial
      | struct _ => exact ⟨h.storage, by simp [State.setObj, h.heap], h.nextId, h.net, h.env, h.selfBalance⟩
  | .memoryIndex id i, _ => by
    simp only [writeLoc, getObj_congr h]
    cases σ.getObj id with
    | error _ => trivial
    | ok o =>
      cases o with
      | struct _ => trivial
      | array elems =>
        simp only [bind, Except.bind]
        split
        · exact ⟨h.storage, by simp [State.setObj, h.heap], h.nextId, h.net, h.env, h.selfBalance⟩
        · trivial
  | .stack _, hl | .storage .., hl | .storageLocal _, hl | .memoryRoot _, hl => by
    rcases hl with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h

theorem opMem_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (op : BinOp) (p : PrimTy)
    (loc : Semantics.Loc) (hl : (∃ id f, loc = .memoryField id f) ∨ ∃ id i, loc = .memoryIndex id i)
    (v : Value) : SameOk ns (opMem σ₁ op p loc v) (opMem σ op p loc v) := by
  simp only [opMem, readLoc_mem_congr h loc hl]
  cases readLoc σ loc with
  | error _ => trivial
  | ok old =>
    simp only [bind, Except.bind]
    cases applyBinOp op old v with
    | error _ => trivial
    | ok new =>
      simp only
      cases checkArith (.prim p) new with
      | error _ => trivial
      | ok new => exact writeLoc_mem_agree h _ loc hl

/-- Two runs that return a value end alike: both normally, in states that
agree off `ns` and with the same value, or both abnormally. -/
def SameOkV (ns : List Name) : Res (State × Value) → Res (State × Value) → Prop
  | .ok a, .ok b => EnvAgreeExcept ns a.1 b.1 ∧ a.2 = b.2
  | .error _, .error _ => True
  | _, _ => False

/-- A `++` at a resolved location, in two agreeing states. -/
theorem bumpStore_agreeV {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (op : IncDec)
    (p : PrimTy) (r : Name) (segs : List Seg) :
    SameOkV ns (bumpStore σ₁ op p r segs) (bumpStore σ op p r segs) := by
  simp only [bumpStore, findStorage_congr h]
  cases σ.findStorage r segs with
  | error _ => trivial
  | ok sv =>
    dsimp only [bind, Except.bind]
    cases sv.asValue with
    | error _ => trivial
    | ok old =>
      dsimp only
      cases old.asInt with
      | error _ => trivial
      | ok oi =>
        dsimp only
        cases checkArith (.prim p) (.int (if op.isIncrement then oi + 1 else oi - 1)) with
        | error _ => trivial
        | ok new =>
          dsimp only
          have := saveStorage_agree h r segs new.toSVal
          revert this
          cases σ₁.saveStorage r segs new.toSVal <;> cases σ.saveStorage r segs new.toSVal <;>
            simp [ResultsAgree, SameOkV, pure, Except.pure]

/-- The states a `++` leaves, in two agreeing states. -/
theorem bumpStore_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (op : IncDec)
    (p : PrimTy) (r : Name) (segs : List Seg) :
    SameOk ns (do pure (← bumpStore σ₁ op p r segs).1) (do pure (← bumpStore σ op p r segs).1) := by
  have := bumpStore_agreeV h op p r segs
  revert this
  cases bumpStore σ₁ op p r segs <;> cases bumpStore σ op p r segs <;> intro h <;>
    first | trivial | exact h.elim | exact h.1

theorem bumpMem_agreeV {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (op : IncDec)
    (p : PrimTy) (loc : Semantics.Loc)
    (hl : (∃ id f, loc = .memoryField id f) ∨ ∃ id i, loc = .memoryIndex id i) :
    SameOkV ns (bumpMem σ₁ op p loc) (bumpMem σ op p loc) := by
  simp only [bumpMem, readLoc_mem_congr h loc hl]
  cases readLoc σ loc with
  | error _ => trivial
  | ok old =>
    simp only [bind, Except.bind]
    cases old.asInt with
    | error _ => trivial
    | ok oi =>
      simp only
      cases checkArith (.prim p) (.int (if op.isIncrement then oi + 1 else oi - 1)) with
      | error _ => trivial
      | ok new =>
        simp only
        have := writeLoc_mem_agree h new loc hl
        revert this
        cases writeLoc σ₁ loc new <;> cases writeLoc σ loc new <;> simp [SameOk, SameOkV, pure, Except.pure]

theorem bumpMem_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (op : IncDec)
    (p : PrimTy) (loc : Semantics.Loc)
    (hl : (∃ id f, loc = .memoryField id f) ∨ ∃ id i, loc = .memoryIndex id i) :
    SameOk ns (do pure (← bumpMem σ₁ op p loc).1) (do pure (← bumpMem σ op p loc).1) := by
  have := bumpMem_agreeV h op p loc hl
  revert this
  cases bumpMem σ₁ op p loc <;> cases bumpMem σ op p loc <;> intro h <;>
    first | trivial | exact h.elim | exact h.1

/-- **A `++` frames**: on a target typed at `Γ`, in two states that agree off
names fresh at `Γ`, it ends alike, with the same value. -/
theorem OpLoc.bump_agree {Γ : Ctx} {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ)
    (hns : ∀ n ∈ ns, Fresh C Γ n) (op : IncDec) {p : PrimTy} (l : OpLoc C Γ p) :
    SameOkV ns (l.bump σ₁ op) (l.bump σ op) := by
  cases l with
  | «local» x hx =>
    have hg : σ₁.getEnv x = σ.getEnv x := by
      simp only [State.getEnv, h.env x (not_mem_of_bound hns hx)]
    simp only [OpLoc.bump, bumpLocal, hg, bind, Except.bind, pure, Except.pure]
    repeat' split
    all_goals first | trivial | exact ⟨h.setEnv_both _ _, rfl⟩ | simp_all [SameOkV]
  | root r => exact bumpStore_agreeV h op p r []
  | field b f hf =>
    simp only [OpLoc.bump, Loc.resolve_frame h hns]
    cases (Loc.field b f hf).resolve σ with
    | error _ => trivial
    | ok a => exact bumpStore_agreeV h op p a.1 a.2
  | index it b i =>
    simp only [OpLoc.bump, Loc.resolve_frame h hns]
    cases (Loc.index it b (.simple i)).resolve σ with
    | error _ => trivial
    | ok a => exact bumpStore_agreeV h op p a.1 a.2
  | mfield b f hf =>
    simp only [OpLoc.bump, b.mval_frame h hns]
    cases b.mval σ with
    | error _ => trivial
    | ok w =>
      simp only [bind, Except.bind]
      cases w.asRef with
      | error _ => trivial
      | ok id => exact bumpMem_agreeV h op p _ (.inl ⟨_, _, rfl⟩)
  | mindex b i =>
    simp only [OpLoc.bump, b.mval_frame h hns, i.eval_frame h hns]
    cases b.mval σ with
    | error _ => trivial
    | ok w =>
      simp only [bind, Except.bind]
      cases w.asRef with
      | error _ => trivial
      | ok id =>
        simp only
        cases i.eval σ with
        | error _ => trivial
        | ok iv =>
          simp only
          cases iv.asInt with
          | error _ => trivial
          | ok n => exact bumpMem_agreeV h op p _ (.inr ⟨_, _, rfl⟩)

/-- A push, in two agreeing states, of elements that agree. -/
theorem pushAt_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (E : Ty)
    (root : Name) (segs : List Seg) {val₁ val : SVal → Res SVal} (hv : ∀ slot, val₁ slot = val slot) :
    SameOk ns (pushAt σ₁ E root segs val₁) (pushAt σ E root segs val) := by
  simp only [pushAt, findStorage_congr h, hv]
  cases σ.findStorage root segs with
  | error _ => trivial
  | ok sv =>
    cases sv with
    | prim _ | struct _ | map _ _ => trivial
    | array elems shadow =>
      simp only [bind, Except.bind]
      cases val (pushSlot E shadow).1 with
      | error _ => trivial
      | ok e => exact SameOk.save h _ _ _

/-- A push of an element that fails, fails. -/
theorem SameOk.error_pushAt {ns : List Name} {e : Halt} {σ : State} (E : Ty) (root : Name)
    (segs : List Seg) {val : SVal → Res SVal} (hv : ∀ slot, ∃ e', val slot = .error e') :
    SameOk ns (.error e) (pushAt σ E root segs val) := by
  simp only [pushAt]
  cases σ.findStorage root segs with
  | error _ => trivial
  | ok sv =>
    cases sv with
    | prim _ | struct _ | map _ _ => trivial
    | array elems shadow =>
      obtain ⟨e', he⟩ := hv (pushSlot E shadow).1
      simp only [bind, Except.bind, he]; trivial

/-- A pop in two agreeing states. -/
theorem popAt_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (root : Name)
    (segs : List Seg) : SameOk ns (popAt σ₁ root segs) (popAt σ root segs) := by
  simp only [popAt, findStorage_congr h]
  cases σ.findStorage root segs with
  | error _ => trivial
  | ok sv =>
    cases sv with
    | prim _ | struct _ | map _ _ => trivial
    | array elems shadow =>
      simp only [bind, Except.bind]
      cases elems.reverse with
      | nil => trivial
      | cons last rest => exact SameOk.save h _ _ _

/-- A transfer in two agreeing states: the funds and the ledger agree. -/
theorem transferAt_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (addr amt : Int) :
    SameOk ns (transferAt σ₁ addr amt) (transferAt σ addr amt) := by
  simp only [transferAt, h.selfBalance]
  split
  · trivial
  split
  · trivial
  exact ⟨h.storage, h.heap, h.nextId, by simp [State.setNet, State.getNet, h.net], h.env, rfl⟩

/-- **A compound write frames**: into a target typed at `Γ`, in two states
that agree off names fresh at `Γ`, it ends alike. -/
theorem OpLoc.store_agree {Γ : Ctx} {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ)
    (hns : ∀ n ∈ ns, Fresh C Γ n) (op : BinOp) {p : PrimTy} (l : OpLoc C Γ p) (v : Value) :
    SameOk ns (l.store σ₁ op v) (l.store σ op v) := by
  cases l with
  | «local» x hx =>
    have hg : σ₁.getEnv x = σ.getEnv x := by
      simp only [State.getEnv, h.env x (not_mem_of_bound hns hx)]
    simp only [OpLoc.store, opLocal, hg, bind, Except.bind, pure, Except.pure]
    repeat' split
    all_goals first | trivial | exact h.setEnv_both _ _ | simp_all
  | root r => exact opStore_agree h op p r [] v
  | field b f hf =>
    simp only [OpLoc.store, Loc.resolve_frame h hns]
    cases (Loc.field b f hf).resolve σ with
    | error _ => trivial
    | ok a => exact opStore_agree h op p a.1 a.2 v
  | index it b i =>
    simp only [OpLoc.store, Loc.resolve_frame h hns]
    cases (Loc.index it b (.simple i)).resolve σ with
    | error _ => trivial
    | ok a => exact opStore_agree h op p a.1 a.2 v
  | mfield b f hf =>
    simp only [OpLoc.store, b.mval_frame h hns]
    cases b.mval σ with
    | error _ => trivial
    | ok w =>
      simp only [bind, Except.bind]
      cases w.asRef with
      | error _ => trivial
      | ok id => exact opMem_agree h op p _ (.inl ⟨_, _, rfl⟩) v
  | mindex b i =>
    simp only [OpLoc.store, b.mval_frame h hns, i.eval_frame h hns]
    cases b.mval σ with
    | error _ => trivial
    | ok w =>
      simp only [bind, Except.bind]
      cases w.asRef with
      | error _ => trivial
      | ok id =>
        simp only
        cases i.eval σ with
        | error _ => trivial
        | ok iv =>
          simp only
          cases iv.asInt with
          | error _ => trivial
          | ok n => exact opMem_agree h op p _ (.inr ⟨_, _, rfl⟩) v

/-- Close `EnvAgreeExcept ns (…(σ.setEnv a _)….setEnv b _) σ` with `a b ∈ ns`, and
`EnvAgreeExcept ns (σ'.setEnv x b) (σ.setEnv x b)` from the same inside. -/
macro "agree_tac" : tactic => `(tactic| (
  repeat (first
    | exact EnvAgreeExcept.refl _ _
    | refine EnvAgreeExcept.setEnv_both ?_ _ _
    | refine EnvAgreeExcept.setEnv_left ?_ (by simp) _)))

/-! ## Memory frames -/

@[simp] theorem getObj_setEnv (σ : State) (n : Name) (b : Binding) (id : Nat) :
    (σ.setEnv n b).getObj id = σ.getObj id := rfl

theorem setObj_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (id : Nat)
    (o : MObj) : EnvAgreeExcept ns (σ₁.setObj id o) (σ.setObj id o) :=
  ⟨h.storage, by simp [State.setObj, h.heap], h.nextId, h.net, h.env, h.selfBalance⟩

theorem memWriteField_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (id : Nat)
    (f : Name) (mv : MVal) : SameOk ns (memWriteField σ₁ id f mv) (memWriteField σ id f mv) := by
  simp only [memWriteField, getObj_congr h]
  cases σ.getObj id with
  | error _ => trivial
  | ok o => cases o with
    | array _ => trivial
    | struct _ => exact setObj_agree h _ _

theorem memWriteIndex_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (id : Nat)
    (i : Int) (mv : MVal) : SameOk ns (memWriteIndex σ₁ id i mv) (memWriteIndex σ id i mv) := by
  simp only [memWriteIndex, getObj_congr h]
  cases σ.getObj id with
  | error _ => trivial
  | ok o => cases o with
    | struct _ => trivial
    | array elems =>
      simp only [bind, Except.bind]
      split
      · exact setObj_agree h _ _
      · trivial

/-- **A memory write frames**: at a location typed at `Γ`, in two states
that agree off names fresh at `Γ`, it ends alike. -/
theorem MLoc.write_agree {Γ : Ctx} {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ)
    (hns : ∀ n ∈ ns, Fresh C Γ n) (mv : MVal) {T : Ty} (l : MLoc C Γ T) :
    SameOk ns (l.write σ₁ mv) (l.write σ mv) := by
  cases l with
  | field b f _ =>
    simp only [MLoc.write, b.mval_frame h hns]
    cases b.mval σ with
    | error _ => trivial
    | ok v =>
      simp only [bind, Except.bind]
      cases v.asRef with
      | error _ => trivial
      | ok id => exact memWriteField_agree h _ _ _
  | index b i =>
    simp only [MLoc.write, b.mval_frame h hns, i.eval_frame h hns]
    cases b.mval σ with
    | error _ => trivial
    | ok v =>
      simp only [bind, Except.bind]
      cases v.asRef with
      | error _ => trivial
      | ok id =>
        simp only
        cases i.eval σ with
        | error _ => trivial
        | ok iv =>
          simp only
          cases iv.asInt with
          | error _ => trivial
          | ok n => exact memWriteIndex_agree h _ _ _

theorem MLoc.write_weaken {Γ Γ' : Ctx} (hs : Ctx.Sub C Γ Γ') (σ : State) (mv : MVal) {T : Ty}
    (l : MLoc C Γ T) : (l.weaken hs).write σ mv = l.write σ mv := by
  cases l <;> simp only [MLoc.weaken, MLoc.write, MPath.mval_weaken, Val.eval_weaken]

/-- What a memory hole's statement does with the slot it reads. -/
def MHole.runWith (σ : State) {Γ Γ' : Ctx} {T : Ty} : MHole C Γ Γ' T → Res MVal → Res State
  | .local x _, r => do pure (σ.setEnv x (.val (← (← r).asValue)))
  | .rebind x _, r => do
    let id ← (← r).asRef
    pure (σ.setEnv x (.mref id))
  | .decl _ x _, r => do
    let id ← (← r).asRef
    pure (σ.setEnv x (.mref id))
  | .write l, r => do l.write σ (← r)

theorem MHole.run_fill (σ : State) {Γ Γ' : Ctx} {T : Ty} (k : MHole C Γ Γ' T) (l : MLoc C Γ T) :
    (k.fill l).run σ = k.runWith σ (l.read σ) := by
  cases k <;> simp only [MHole.fill, MHole.runWith, Stmt.run, Val.eval, MRhs.bind, MPath.mval,
    MSrc.mval] <;> cases l.read σ <;> rfl

/-- A memory hole's statement, past a fresh binding of `y`, ends as it does
without it, off `[y]`. -/
theorem MHole.runWith_extend {Γ Γ' : Ctx} {T : Ty} {y : Name} {b : BTy} (hy : isFresh C Γ' y = true)
    (k : MHole C Γ Γ' T) (σ : State) (v : Binding) (r : Res MVal) :
    SameOk [y] ((k.extend y b hy).runWith (σ.setEnv y v) r) (k.runWith σ r) := by
  cases r with
  | error _ =>
    cases k <;> trivial
  | ok mv =>
    cases k with
    | «local» x h =>
      simp only [MHole.extend, MHole.runWith, bind, Except.bind]
      cases mv.asValue with
      | error _ => trivial
      | ok w => simp only [SameOk, pure, Except.pure]; agree_tac
    | rebind x h =>
      simp only [MHole.extend, MHole.runWith, bind, Except.bind]
      cases mv.asRef with
      | error _ => trivial
      | ok id => simp only [SameOk, pure, Except.pure]; agree_tac
    | decl R x hx =>
      simp only [MHole.extend, MHole.runWith, bind, Except.bind]
      cases mv.asRef with
      | error _ => trivial
      | ok id => simp only [SameOk, pure, Except.pure]; agree_tac
    | write l =>
      simp only [MHole.extend, MHole.runWith, bind, Except.bind, MLoc.write_weaken]
      exact MLoc.write_agree (agree_setEnv σ y v) (by simpa using isFresh_of_sub (Ctx.Sub.refl _) hy) mv l

/-- Two runs that return a result end alike: both normally, in states that
agree off `ns` and with the same result, or both abnormally. -/
def SameOkR {α : Type} (ns : List Name) : Res (State × α) → Res (State × α) → Prop
  | .ok a, .ok b => EnvAgreeExcept ns a.1 b.1 ∧ a.2 = b.2
  | .error _, .error _ => True
  | _, _ => False

theorem alloc_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (o : MObj) :
    EnvAgreeExcept ns (σ₁.alloc o).1 (σ.alloc o).1 ∧ (σ₁.alloc o).2 = (σ.alloc o).2 :=
  ⟨⟨h.storage, by simp [State.alloc, h.heap, h.nextId], by simp [State.alloc, h.nextId], h.net, h.env,
    h.selfBalance⟩, by simp [State.alloc, h.nextId]⟩

mutual

/-- **A deep copy into memory frames**: from two agreeing states it
allocates alike. -/
theorem copyStToM_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) :
    (v : SVal) → SameOkR ns (copyStToM σ₁ v) (copyStToM σ v)
  | .prim (.int _) => ⟨h, rfl⟩
  | .prim (.bool _) => ⟨h, rfl⟩
  | .map _ _ => trivial
  | .struct fields => by
    have ih := copyStFields_agree h fields
    simp only [copyStToM]
    revert ih
    cases copyStFields σ₁ fields <;> cases copyStFields σ fields <;> intro ih <;>
      first | trivial | exact ih.elim | skip
    rename_i a b
    obtain ⟨hab, he⟩ := ih
    simp only [bind, Except.bind, he]
    exact ⟨(alloc_agree hab _).1, by rw [(alloc_agree hab _).2]⟩
  | .array elems _ => by
    have ih := copyStElems_agree h elems
    simp only [copyStToM]
    revert ih
    cases copyStElems σ₁ elems <;> cases copyStElems σ elems <;> intro ih <;>
      first | trivial | exact ih.elim | skip
    rename_i a b
    obtain ⟨hab, he⟩ := ih
    simp only [bind, Except.bind, he]
    exact ⟨(alloc_agree hab _).1, by rw [(alloc_agree hab _).2]⟩

theorem copyStFields_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) :
    (fields : List (Name × SVal)) → SameOkR ns (copyStFields σ₁ fields) (copyStFields σ fields)
  | [] => ⟨h, rfl⟩
  | (n, v) :: rest => by
    have ih := copyStToM_agree h v
    simp only [copyStFields]
    revert ih
    cases copyStToM σ₁ v <;> cases copyStToM σ v <;> intro ih <;> first | trivial | exact ih.elim | skip
    rename_i a b
    obtain ⟨hab, he⟩ := ih
    have ih' := copyStFields_agree hab rest
    simp only [bind, Except.bind]
    revert ih'
    cases copyStFields a.1 rest <;> cases copyStFields b.1 rest <;> intro ih' <;>
      first | trivial | exact ih'.elim | skip
    obtain ⟨hab', he'⟩ := ih'
    exact ⟨hab', by simp [he, he']⟩

theorem copyStElems_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) :
    (elems : List SVal) → SameOkR ns (copyStElems σ₁ elems) (copyStElems σ elems)
  | [] => ⟨h, rfl⟩
  | v :: rest => by
    have ih := copyStToM_agree h v
    simp only [copyStElems]
    revert ih
    cases copyStToM σ₁ v <;> cases copyStToM σ v <;> intro ih <;> first | trivial | exact ih.elim | skip
    rename_i a b
    obtain ⟨hab, he⟩ := ih
    have ih' := copyStElems_agree hab rest
    simp only [bind, Except.bind]
    revert ih'
    cases copyStElems a.1 rest <;> cases copyStElems b.1 rest <;> intro ih' <;>
      first | trivial | exact ih'.elim | skip
    obtain ⟨hab', he'⟩ := ih'
    exact ⟨hab', by simp [he, he']⟩

end

theorem allocDefault_agree {ns : List Name} {σ₁ σ : State} (h : EnvAgreeExcept ns σ₁ σ) (R : RefTy) :
    SameOkR ns (allocDefault σ₁ R) (allocDefault σ R) := by
  have ih := copyStToM_agree h (defaultForRef R)
  simp only [allocDefault]
  revert ih
  cases copyStToM σ₁ (defaultForRef R) <;> cases copyStToM σ (defaultForRef R) <;> intro ih <;>
    first | trivial | exact ih.elim | skip
  rename_i a b
  obtain ⟨hab, he⟩ := ih
  obtain ⟨sa, ma⟩ := a
  obtain ⟨sb, mb⟩ := b
  simp only at he hab
  subst he
  cases ma <;> first | trivial | exact ⟨hab, rfl⟩

theorem MHole.runWith_error (σ : State) {Γ Γ' : Ctx} {T : Ty} (k : MHole C Γ Γ' T) (e : Halt) :
    k.runWith σ (.error e) = .error e := by
  cases k <;> rfl

theorem MPath.mval_setEnv {Γ : Ctx} {n : Name} (hn : isFresh C Γ n = true) (σ : State) (b : Binding)
    {T : Ty} (p : MPath C Γ T) : p.mval (σ.setEnv n b) = p.mval σ :=
  p.mval_frame (agree_setEnv σ n b) (by simpa using hn)

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
    | (intro σ; rfl)
    | skip
  case valueDeclSkip p x hx => intro σ; cases p <;> rfl
  case revertBox h => intro σ; exact ⟨rfl, by simp [h]⟩
  case revertDiamond h => intro σ; exact ⟨rfl, by simp [h]⟩
  case storageFieldWrite_unfold_leftFst s p nsp hn f hf e se sp hse hsp _hnt =>
    have hsp₀ := isFresh_of_sub (Ctx.Sub.fresh hse _) hsp
    refine ⟨by simp [hse, hsp₀], fun σ => SameOk.of_agree ?_⟩
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
    refine ⟨by simp [hsp], fun σ => ?_⟩
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
  case storageRootWriteValueRhsCapture p r hΓ hr nse hn se hse _hnt =>
    refine ⟨by simp [hse], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
    cases nse.eval σ with
    | error _ => simp [SameOk, bind, Except.bind]
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [Loc.target_setEnv hse]
      simp only [Val.eval, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure]
      cases Loc.target σ (.root r hΓ hr) <;> simp [SameOk]
      exact SameOk.save (by agree_tac) _ _ _
  case fieldWriteValueRhsCapture s p sp hs f hf nse hn se hse _hnt =>
    refine ⟨by simp [hse], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Src.value, SPath.resolve_weaken, Val.eval_weaken, Simple.eval_weaken, Loc.resolve_weaken, Loc.target_weaken, Src.value_weaken, Src.value_copy_weaken]
    cases nse.eval σ with
    | error _ => simp [SameOk, bind, Except.bind]
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [Loc.target_setEnv hse]
      simp only [Val.eval, Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure]
      cases Loc.target σ (.field sp f hf) <;> simp [SameOk]
      exact SameOk.save (by agree_tac) _ _ _
  case indexWriteValueRhsCapture R₀ kp p it sp hs ie nse hn se hse _hnt =>
    refine ⟨by simp [hse], fun σ => ?_⟩
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
    refine ⟨by simp, fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Val.eval_weaken, bind, Except.bind, pure, Except.pure]
    rw [Val.eval_setEnv hx]
    cases e.eval σ <;> simp [SameOk, SemanticsProperties.State.setEnv_setEnv_absorb] <;> agree_tac
  -- Delete through a captured receiver.
  case storageFieldDelete_unfold_leftFst s T nsp hn f hf sp hsp =>
    refine ⟨by simp [hsp], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Loc.resolve]
    cases nsp.resolve σ with
    | error _ => simp [SameOk, bind, Except.bind]
    | ok rs =>
      simp only [Val.eval, SPath.new, SPath.resolve, envPath, Simple.new, Simple.eval, Simple.weaken, SPath.weaken, setEnv_env, lookupBy_setBy_self, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure, findStorage_setEnv]
      cases σ.findStorage rs.1 (rs.2 ++ [.field f]) <;> simp [SameOk]
      exact SameOk.save (by agree_tac) _ _ _
  case storageIndexDelete_unfold_leftFst R₀ kp V it nsp hn e sp hsp =>
    refine ⟨by simp [hsp], fun σ => ?_⟩
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
    refine ⟨by simp [hie], fun σ => ?_⟩
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
    refine ⟨by simp [hse], fun σ => ?_⟩
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
    refine ⟨by simp [hse], fun σ => ?_⟩
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
  case storageIndexWrite_unfold_leftFst R₀ kp p it nsp hn e₁ e₂ se sp ie hse hsp hie _hnt =>
    have hsp₀ := isFresh_of_sub (Ctx.Sub.fresh hse _) hsp
    have hie₁ := isFresh_of_sub (Ctx.Sub.fresh hsp _) hie
    have hie₀ := isFresh_of_sub (Ctx.Sub.fresh hse _) hie₁
    have h₁ := ne_of_isFresh_setBy hsp
    have h₂ := ne_of_isFresh_setBy hie
    have h₃ := ne_of_bound_fresh ((Ctx.Sub.fresh hsp _).local_ _ _ (lookupBy_setBy_self ..)) hie
    refine ⟨by simp [hse, hsp₀, hie₀], fun σ => ?_⟩
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

  -- A conditional lowered to a branch: the condition, then the branch taken.
  case ternaryToIf p x h c a b =>
    refine ⟨by simp, fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Val.eval]
    cases c.eval σ with
    | error _ => trivial
    | ok v =>
      cases v with
      | int _ => trivial
      | bool bv =>
        cases bv <;> simp only [bind, Except.bind, pickBranch, pure, Except.pure] <;>
          exact SameOk.refl _ _
  case ternaryToIfStorage p l c a b =>
    refine ⟨by simp, fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Val.eval, Src.value]
    cases c.eval σ with
    | error _ => trivial
    | ok v =>
      cases v with
      | int _ => trivial
      | bool bv =>
        cases bv <;> simp only [bind, Except.bind, pickBranch, pure, Except.pure] <;>
          exact SameOk.refl _ _
  case ternaryCaptureCond p k nse hn a b se hse =>
    refine ⟨by simp [hse], fun σ => ?_⟩
    cases k with
    | «local» x h =>
      simp only [VHole.fill, VHole.weaken, Prog.run, Stmt.run, bind_pure, Val.eval, Val.eval_weaken]
      cases nse.eval σ with
      | error _ => trivial
      | ok v =>
        simp only [bind, Except.bind, pure, Except.pure, Simple.eval_new]
        rw [a.eval_setEnv hse, b.eval_setEnv hse]
        cases pickBranch v (a.eval σ) (b.eval σ) with
        | error _ => trivial
        | ok w => simp only [SameOk]; agree_tac
    | mem l =>
      simp only [VHole.fill, VHole.weaken, Prog.run, Stmt.run, bind_pure, Val.eval, Val.eval_weaken,
        MSrc.mval, MLoc.write_weaken]
      cases nse.eval σ with
      | error _ => trivial
      | ok v =>
        simp only [bind, Except.bind, pure, Except.pure, Simple.eval_new]
        rw [a.eval_setEnv hse, b.eval_setEnv hse]
        cases pickBranch v (a.eval σ) (b.eval σ) with
        | error _ => trivial
        | ok w => exact MLoc.write_agree (agree_setEnv σ se _) (by simpa using hse) _ l
    | store l =>
      simp only [VHole.fill, VHole.weaken, Prog.run, Stmt.run, bind_pure, Val.eval, Val.eval_weaken,
        Src.value, Loc.target_weaken]
      cases nse.eval σ with
      | error _ => trivial
      | ok v =>
        simp only [bind, Except.bind, pure, Except.pure, Simple.eval_new]
        rw [a.eval_setEnv hse, b.eval_setEnv hse, Loc.target_setEnv hse]
        cases pickBranch v (a.eval σ) (b.eval σ) with
        | error _ => trivial
        | ok w =>
          cases l.target σ with
          | error _ => trivial
          | ok rs => exact SameOk.save (agree_setEnv σ se _) _ _ _

  -- Arrays: a receiver captured first, then the push; an argument captured before the receiver.
  case storagePushValue_unfold_leftFstReceiver E nsp hn e sp hsp hd =>
    refine ⟨by simp [hsp], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure]
    cases nsp.resolve σ with
    | error _ => trivial
    | ok rs =>
      simp only [bind, Except.bind, pure, Except.pure, SPath.new, SPath.resolve, envPath,
        setEnv_env, lookupBy_setBy_self]
      exact pushAt_agree (agree_setEnv σ sp _) E _ _ fun _ => by
        simp only [Src.pushVal, Src.value_weaken, e.value_setEnv hsp]
  case storagePush_unfold_leftFstReceiver E nsp hn sp hsp hd =>
    refine ⟨by simp [hsp], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure]
    cases nsp.resolve σ with
    | error _ => trivial
    | ok rs =>
      simp only [bind, Except.bind, pure, Except.pure, SPath.new, SPath.resolve, envPath,
        setEnv_env, lookupBy_setBy_self]
      exact pushAt_agree (agree_setEnv σ sp _) E _ _ fun _ => rfl
  case storagePop_unfold_leftFstReceiver E nsp hn sp hsp =>
    refine ⟨by simp [hsp], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure]
    cases nsp.resolve σ with
    | error _ => trivial
    | ok rs =>
      simp only [bind, Except.bind, pure, Except.pure, SPath.new, SPath.resolve, envPath,
        setEnv_env, lookupBy_setBy_self]
      exact popAt_agree (agree_setEnv σ sp _) _ _
  case storagePushValue_unfold_rightSndArgument E sp hs r hr se hse hd =>
    refine ⟨by simp [hse], fun σ => ?_⟩
    cases r with
    | val v =>
      simp only [Src.decl, Src.fresh, Prog.run, Stmt.run, bind_pure, SPath.resolve_weaken]
      cases hv : v.eval σ with
      | error e =>
        simp only [bind, Except.bind]
        cases sp.resolve σ with
        | error _ => trivial
        | ok rs => exact SameOk.error_pushAt _ _ _ fun _ => ⟨e, by simp [Src.pushVal, Src.value, hv, bind, Except.bind]⟩
      | ok w =>
        simp only [bind, Except.bind, pure, Except.pure]
        rw [sp.resolve_setEnv hse]
        cases sp.resolve σ with
        | error _ => trivial
        | ok rs =>
          exact pushAt_agree (agree_setEnv σ se _) _ _ _ fun _ => by
            simp [Src.pushVal, Src.value, Val.eval, hv, Simple.eval_new, bind, Except.bind, pure, Except.pure]
    | copy p hm =>
      simp only [Src.decl, Src.fresh, Prog.run, Stmt.run, bind_pure, SPath.resolve_weaken]
      cases hp : p.resolve σ with
      | error e =>
        simp only [bind, Except.bind]
        cases sp.resolve σ with
        | error _ => trivial
        | ok rs => exact SameOk.error_pushAt _ _ _ fun _ => ⟨e, by simp [Src.pushVal, Src.value, hp, bind, Except.bind]⟩
      | ok ps =>
        simp only [bind, Except.bind, pure, Except.pure]
        rw [sp.resolve_setEnv hse]
        cases sp.resolve σ with
        | error _ => trivial
        | ok rs =>
          exact pushAt_agree (agree_setEnv σ se _) _ _ _ fun _ => by
            simp [Src.pushVal, Src.value, hp, SPath.new, SPath.resolve, envPath, setEnv_env,
              lookupBy_setBy_self, bind, Except.bind, pure, Except.pure]

  -- Transfer: a receiver captured first; an amount captured before the receiver is read.
  case transfer_unfold_leftFstReceiver nr hn a se hse =>
    refine ⟨by simp [hse], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Val.eval, Val.eval_weaken]
    cases nr.eval σ with
    | error _ => trivial
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure, Simple.eval_new]
      rw [a.eval_setEnv hse]
      cases v.asInt with
      | error _ => trivial
      | ok addr =>
        simp only
        cases a.eval σ with
        | error _ => trivial
        | ok w =>
          simp only
          cases w.asInt with
          | error _ => trivial
          | ok amt => exact transferAt_agree (agree_setEnv σ se _) addr amt
  case transfer_unfold_rightSndArgument r na hn se hse =>
    refine ⟨by simp [hse], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Val.eval, Simple.eval_weaken]
    cases hna : na.eval σ with
    | error _ =>
      simp only [bind, Except.bind]
      cases r.eval σ with
      | error _ => trivial
      | ok v =>
        dsimp only
        cases v.asInt with
        | error _ => trivial
        | ok _ => simp only [hna]; trivial
    | ok w =>
      simp only [bind, Except.bind, pure, Except.pure, Simple.eval_new]
      rw [r.eval_setEnv hse]
      cases r.eval σ with
      | error _ => trivial
      | ok v =>
        simp only
        cases v.asInt with
        | error _ => trivial
        | ok addr =>
          simp only
          cases w.asInt with
          | error _ => trivial
          | ok amt => exact transferAt_agree (agree_setEnv σ se _) addr amt

  -- Memory: a read through a captured receiver or index.
  case memoryFieldRead_unfold_rightFst s T nmp hn f hf mv k hmv =>
    have hmv₀ := isFresh_of_sub k.sub hmv
    refine ⟨by simp [hmv], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MRhs.bind, MHole.run_fill]
    have hread : (MLoc.field nmp f hf).read σ = (do
        let id ← (← nmp.mval σ).asRef
        match ← σ.getObj id with
        | .struct fields =>
          match lookupBy f fields with
          | some v => pure v
          | none => .error .stuck
        | .array _ => .error .stuck) := rfl
    rw [hread]
    cases nmp.mval σ with
    | error e => simp only [bind, Except.bind, MHole.runWith_error]; trivial
    | ok v =>
      simp only [bind, Except.bind]
      cases v.asRef with
      | error e => simp only [MHole.runWith_error]; trivial
      | ok id =>
        simp only [pure, Except.pure, MLoc.read, MPath.new, MPath.mval, getEnv_setEnv_self, MVal.asRef,
          getObj_setEnv, bind, Except.bind]
        exact MHole.runWith_extend hmv k σ _ _
  case memoryIndexRead_unfold_rightFst E nmp hn e mv k hmv =>
    have hmv₀ := isFresh_of_sub k.sub hmv
    refine ⟨by simp [hmv], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MRhs.bind, MHole.run_fill]
    simp only [MLoc.read, Val.eval_weaken, e.eval_setEnv hmv₀]
    cases nmp.mval σ with
    | error e => simp only [bind, Except.bind, MHole.runWith_error]; trivial
    | ok v =>
      simp only [bind, Except.bind]
      cases v.asRef with
      | error e => simp only [MHole.runWith_error]; trivial
      | ok id =>
        simp only [pure, Except.pure, MPath.new, MPath.mval, getEnv_setEnv_self, MVal.asRef,
          getObj_setEnv, bind, Except.bind, e.eval_setEnv hmv₀]
        exact MHole.runWith_extend hmv k σ _ _
  case memoryIndexRead_unfold_rightSndIndex E b hb nse hn ie k hie =>
    have hie₀ := isFresh_of_sub k.sub hie
    refine ⟨by simp [hie], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MHole.run_fill]
    simp only [MLoc.read, MPath.mval_weaken, b.mval_setEnv hie₀]
    cases hw : nse.eval σ with
    | error e =>
      simp only [bind, Except.bind]
      cases b.mval σ with
      | error _ => simp only [MHole.runWith_error]; trivial
      | ok v =>
        simp only
        cases v.asRef with
        | error _ => simp only [MHole.runWith_error]; trivial
        | ok id => simp only [hw, MHole.runWith_error]; trivial
    | ok w =>
      simp only [bind, Except.bind, pure, Except.pure, Val.eval, Simple.eval_new, hw, b.mval_setEnv hie₀,
        getObj_setEnv]
      exact MHole.runWith_extend hie k σ _ _

  case ternaryToIfMemory p l c a b =>
    refine ⟨by simp, fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Val.eval, MSrc.mval]
    cases c.eval σ with
    | error _ => trivial
    | ok v =>
      cases v with
      | int _ => trivial
      | bool bv =>
        cases bv <;> simp only [bind, Except.bind, pickBranch, pure, Except.pure]
        · cases b.eval σ <;> exact SameOk.refl _ _
        · cases a.eval σ <;> exact SameOk.refl _ _
  -- Memory arithmetic through a captured receiver.
  case memoryFieldOpAssignUnfoldLeftFst s p op hop hp nmp hn f hf se mv hmv =>
    refine ⟨by simp [hmv], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MRhs.bind, OpLoc.store, Val.eval, Simple.eval_weaken]
    cases hs : se.eval σ with
    | error _ =>
      cases nmp.mval σ with
      | error _ => trivial
      | ok w =>
        simp only [bind, Except.bind]
        cases w.asRef with
        | error _ => trivial
        | ok id => simp only [pure, Except.pure, se.eval_setEnv hmv, hs]; trivial
    | ok v =>
      cases nmp.mval σ with
      | error _ => trivial
      | ok w =>
        simp only [bind, Except.bind]
        cases w.asRef with
        | error _ => trivial
        | ok id =>
          simp only [pure, Except.pure, se.eval_setEnv hmv, hs, MPath.new, MPath.mval, getEnv_setEnv_self,
            MVal.asRef]
          exact opMem_agree (agree_setEnv σ mv _) op p _ (.inl ⟨_, _, rfl⟩) v
  case memoryIndexOpAssignUnfoldLeftFst p op hop hp nmp hn ie se mv hmv =>
    refine ⟨by simp [hmv], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MRhs.bind, OpLoc.store, Val.eval, Simple.eval_weaken]
    cases hs : se.eval σ with
    | error _ =>
      cases nmp.mval σ with
      | error _ => trivial
      | ok w =>
        simp only [bind, Except.bind]
        cases w.asRef with
        | error _ => trivial
        | ok id => simp only [pure, Except.pure, se.eval_setEnv hmv, hs]; trivial
    | ok v =>
      cases nmp.mval σ with
      | error _ => trivial
      | ok w =>
        simp only [bind, Except.bind]
        cases w.asRef with
        | error _ => trivial
        | ok id =>
          simp only [pure, Except.pure, se.eval_setEnv hmv, hs, MPath.new, MPath.mval, getEnv_setEnv_self,
            MVal.asRef, ie.eval_setEnv hmv]
          cases ie.eval σ with
          | error _ => trivial
          | ok iv =>
            simp only
            cases iv.asInt with
            | error _ => trivial
            | ok n => exact opMem_agree (agree_setEnv σ mv _) op p _ (.inr ⟨_, _, rfl⟩) v
  case memoryFieldIncrementUnfoldLeftFst s p op hp nmp hn f hf mv hmv =>
    refine ⟨by simp [hmv], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MRhs.bind, OpLoc.bump]
    cases nmp.mval σ with
    | error _ => trivial
    | ok w =>
      simp only [bind, Except.bind]
      cases w.asRef with
      | error _ => trivial
      | ok id =>
        simp only [pure, Except.pure, MPath.new, MPath.mval, getEnv_setEnv_self, MVal.asRef]
        exact bumpMem_agree (agree_setEnv σ mv _) op p _ (.inl ⟨_, _, rfl⟩)
  case memoryIndexIncrementUnfoldLeftFst p op hp nmp hn ie mv hmv =>
    refine ⟨by simp [hmv], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MRhs.bind, OpLoc.bump, Simple.eval_weaken]
    cases nmp.mval σ with
    | error _ => trivial
    | ok w =>
      simp only [bind, Except.bind]
      cases w.asRef with
      | error _ => trivial
      | ok id =>
        simp only [pure, Except.pure, MPath.new, MPath.mval, getEnv_setEnv_self, MVal.asRef,
          ie.eval_setEnv hmv]
        cases ie.eval σ with
        | error _ => trivial
        | ok iv =>
          simp only
          cases iv.asInt with
          | error _ => trivial
          | ok n => exact bumpMem_agree (agree_setEnv σ mv _) op p _ (.inr ⟨_, _, rfl⟩)

  -- Memory: a copy into storage through a captured receiver or index.
  case memoryToStorageField_unfold_leftFst s R nsp hn f hf p sp hsp =>
    refine ⟨by simp [hsp], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MPath.mval_weaken, Loc.target, Loc.resolve]
    cases hp : p.mval σ with
    | error _ =>
      cases nsp.resolve σ with
      | error _ => trivial
      | ok rs => simp only [bind, Except.bind, pure, Except.pure, p.mval_setEnv hsp, hp]; trivial
    | ok mv =>
      cases nsp.resolve σ with
      | error _ =>
        simp only [bind, Except.bind]
        cases copyMem σ mv <;> trivial
      | ok rs =>
        simp only [bind, Except.bind, pure, Except.pure, p.mval_setEnv hsp, hp,
          copyMem_congr (agree_setEnv σ sp (.spath rs.1 rs.2)), SPath.new, SPath.resolve, envPath,
          setEnv_env, lookupBy_setBy_self]
        cases copyMem σ mv with
        | error _ => trivial
        | ok sv => exact SameOk.save (agree_setEnv σ sp _) _ _ _
  case memoryToStorageIndex_unfold_leftFst R₀ kp R it nsp hn e p sp hsp =>
    refine ⟨by simp [hsp], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MPath.mval_weaken, Val.eval_weaken, Loc.target,
      Loc.resolve]
    cases hp : p.mval σ with
    | error _ =>
      cases nsp.resolve σ with
      | error _ => trivial
      | ok rs => simp only [bind, Except.bind, pure, Except.pure, p.mval_setEnv hsp, hp]; trivial
    | ok mv =>
      cases nsp.resolve σ with
      | error _ =>
        simp only [bind, Except.bind]
        cases copyMem σ mv <;> trivial
      | ok rs =>
        simp only [bind, Except.bind, pure, Except.pure, p.mval_setEnv hsp, hp,
          copyMem_congr (agree_setEnv σ sp (.spath rs.1 rs.2)), SPath.new, SPath.resolve, envPath,
          setEnv_env, lookupBy_setBy_self, e.eval_setEnv hsp]
        cases copyMem σ mv with
        | error _ => cases e.eval σ <;> trivial
        | ok sv =>
          simp only
          cases e.eval σ with
          | error _ => trivial
          | ok iv =>
            simp only
            cases iv.asInt with
            | error _ => trivial
            | ok n => exact SameOk.save (agree_setEnv σ sp _) _ _ _
  case memoryToStorageIndexNonSimpleIndexCapture R₀ kp R it sp hs nse hn p ie hie =>
    refine ⟨by simp [hie], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MPath.mval_weaken, Loc.target, Loc.resolve,
      SPath.resolve_weaken, Val.eval]
    cases hn' : nse.eval σ with
    | error _ =>
      simp only [bind, Except.bind]
      cases p.mval σ with
      | error _ => trivial
      | ok mv =>
        simp only
        cases copyMem σ mv with
        | error _ => trivial
        | ok sv =>
          simp only
          cases sp.resolve σ with
          | error _ => trivial
          | ok rs => simp only [hn']; trivial
    | ok iw =>
      simp only [bind, Except.bind, pure, Except.pure, p.mval_setEnv hie, sp.resolve_setEnv hie,
        Simple.eval_new]
      cases p.mval σ with
      | error _ => trivial
      | ok mv =>
        simp only [copyMem_congr (agree_setEnv σ ie (.val iw))]
        cases copyMem σ mv with
        | error _ => trivial
        | ok sv =>
          simp only
          cases sp.resolve σ with
          | error _ => trivial
          | ok rs =>
            simp only [hn']
            cases iw.asInt with
            | error _ => trivial
            | ok n => exact SameOk.save (agree_setEnv σ ie _) _ _ _

  -- Memory: a copy from storage through a captured path.
  case storageToMemoryDeclUnfoldRightFst R x hx p hp hnf hm sp hsp hd =>
    have hsp₀ := isFresh_of_sub (Ctx.Sub.fresh hx _) hsp
    have hne := ne_of_isFresh_setBy hsp
    refine ⟨by simp [hsp], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MRhs.bind]
    cases p.resolve σ with
    | error _ => trivial
    | ok rs =>
      simp only [bind, Except.bind, pure, Except.pure, SPath.new, SPath.resolve, envPath, setEnv_env,
        lookupBy_setBy_self, findStorage_setEnv]
      cases σ.findStorage rs.1 rs.2 with
      | error _ => trivial
      | ok sv =>
        simp only
        have h := copyStToM_agree (agree_setEnv σ sp (.spath rs.1 rs.2)) sv
        revert h
        cases copyStToM (σ.setEnv sp (.spath rs.1 rs.2)) sv <;> cases copyStToM σ sv <;> intro h <;>
          first | trivial | exact h.elim | skip
        rename_i a b
        obtain ⟨hab, he⟩ := h
        obtain ⟨σa, ma⟩ := a
        obtain ⟨σb, mb⟩ := b
        simp only at he hab
        subst he
        cases ma with
        | prim _ => trivial
        | ref id => exact hab.setEnv_both _ _
  case memoryStorageCopyUnfold R x h p hp hm sp hsp =>
    refine ⟨by simp [hsp], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MRhs.bind]
    cases p.resolve σ with
    | error _ => trivial
    | ok rs =>
      simp only [bind, Except.bind, pure, Except.pure, SPath.new, SPath.resolve, envPath, setEnv_env,
        lookupBy_setBy_self, findStorage_setEnv]
      cases σ.findStorage rs.1 rs.2 with
      | error _ => trivial
      | ok sv =>
        simp only
        have h := copyStToM_agree (agree_setEnv σ sp (.spath rs.1 rs.2)) sv
        revert h
        cases copyStToM (σ.setEnv sp (.spath rs.1 rs.2)) sv <;> cases copyStToM σ sv <;> intro h <;>
          first | trivial | exact h.elim | skip
        rename_i a b
        obtain ⟨hab, he⟩ := h
        obtain ⟨σa, ma⟩ := a
        obtain ⟨σb, mb⟩ := b
        simp only at he hab
        subst he
        cases ma with
        | prim _ => trivial
        | ref id => exact hab.setEnv_both _ _

  -- Memory: a write through a captured receiver, index or source.
  case memoryFieldWrite_unfold_leftFst s p nmp hn f hf e se mv hse hmv _hnt =>
    have hmv₀ := isFresh_of_sub (Ctx.Sub.fresh hse _) hmv
    have hne := ne_of_isFresh_setBy hmv
    refine ⟨by simp [hse, hmv₀], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MRhs.bind, MSrc.mval, MLoc.write, Val.eval,
      MPath.mval_weaken]
    cases e.eval σ with
    | error _ => trivial
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [nmp.mval_setEnv hse]
      cases nmp.mval σ with
      | error _ => trivial
      | ok w =>
        simp only
        cases w.asRef with
        | error _ => trivial
        | ok id =>
          simp only [MPath.new, MPath.mval, getEnv_setEnv_self, MVal.asRef, Simple.new, Simple.weaken,
            Simple.eval, getEnv_setEnv_ne _ hne, Val.eval_weaken, bind, Except.bind, pure, Except.pure]
          exact memWriteField_agree (by agree_tac) _ _ _
  case memoryIndexWrite_unfold_leftFst p nmp hn e₁ e₂ se mv hse hmv _hnt =>
    have hmv₀ := isFresh_of_sub (Ctx.Sub.fresh hse _) hmv
    have hne := ne_of_isFresh_setBy hmv
    refine ⟨by simp [hse, hmv₀], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MRhs.bind, MSrc.mval, MLoc.write, Val.eval,
      MPath.mval_weaken, Val.eval_weaken]
    cases e₂.eval σ with
    | error _ => trivial
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [nmp.mval_setEnv hse]
      cases nmp.mval σ with
      | error _ => trivial
      | ok w =>
        simp only
        cases w.asRef with
        | error _ => trivial
        | ok id =>
          simp only [MPath.new, MPath.mval, getEnv_setEnv_self, MVal.asRef, Simple.new, Simple.weaken,
            Simple.eval, getEnv_setEnv_ne _ hne, Val.eval_weaken, bind, Except.bind, pure, Except.pure]
          rw [e₁.eval_setEnv hmv₀, e₁.eval_setEnv hse]
          cases e₁.eval σ with
          | error _ => trivial
          | ok iv =>
            simp only
            cases iv.asInt with
            | error _ => trivial
            | ok n => exact memWriteIndex_agree (by agree_tac) _ _ _
  case memoryFieldWriteMemRef_unfold_leftFst s R nmp hn f hf src hsrc mv hmv =>
    refine ⟨by simp [hmv], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MRhs.bind, MSrc.mval, MLoc.write, MPath.mval_weaken]
    cases hs : src.mval σ with
    | error _ =>
      simp only [bind, Except.bind]
      cases nmp.mval σ with
      | error _ => trivial
      | ok w =>
        simp only
        cases w.asRef with
        | error _ => trivial
        | ok id => simp only [pure, Except.pure, src.mval_setEnv hmv, hs]; trivial
    | ok sv =>
      simp only [bind, Except.bind]
      cases nmp.mval σ with
      | error _ => trivial
      | ok w =>
        simp only
        cases w.asRef with
        | error _ => trivial
        | ok id =>
          simp only [pure, Except.pure, src.mval_setEnv hmv, hs, MPath.new, MPath.mval,
            getEnv_setEnv_self, MVal.asRef]
          exact memWriteField_agree (agree_setEnv σ mv _) _ _ _
  case memoryIndexWriteMemRef_unfold_leftFst R nmp hn e src hsrc mv hmv =>
    refine ⟨by simp [hmv], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MRhs.bind, MSrc.mval, MLoc.write, MPath.mval_weaken,
      Val.eval_weaken]
    cases hs : src.mval σ with
    | error _ =>
      simp only [bind, Except.bind]
      cases nmp.mval σ with
      | error _ => trivial
      | ok w =>
        simp only
        cases w.asRef with
        | error _ => trivial
        | ok id => simp only [pure, Except.pure, src.mval_setEnv hmv, hs]; trivial
    | ok sv =>
      simp only [bind, Except.bind]
      cases nmp.mval σ with
      | error _ => trivial
      | ok w =>
        simp only
        cases w.asRef with
        | error _ => trivial
        | ok id =>
          simp only [pure, Except.pure, src.mval_setEnv hmv, hs, MPath.new, MPath.mval,
            getEnv_setEnv_self, MVal.asRef, e.eval_setEnv hmv]
          cases e.eval σ with
          | error _ => trivial
          | ok iv =>
            simp only
            cases iv.asInt with
            | error _ => trivial
            | ok n => exact memWriteIndex_agree (agree_setEnv σ mv _) _ _ _
  case memoryIndexWriteNonSimpleIndexCapture p b hb nse hn e se ie hse hie _hnt =>
    have hie₀ := isFresh_of_sub (Ctx.Sub.fresh hse _) hie
    have hne := ne_of_isFresh_setBy hie
    refine ⟨by simp [hse, hie₀], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MSrc.mval, MLoc.write, Val.eval, MPath.mval_weaken,
      Val.eval_weaken]
    cases e.eval σ with
    | error _ => trivial
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [nse.eval_setEnv hse]
      cases hn' : nse.eval σ with
      | error _ =>
        simp only
        cases b.mval σ with
        | error _ => trivial
        | ok w =>
          simp only
          cases w.asRef with
          | error _ => trivial
          | ok id => simp only [hn']; trivial
      | ok iw =>
        simp only [Simple.new, Simple.weaken, Simple.eval, getEnv_setEnv_self,
          getEnv_setEnv_ne _ hne, MPath.mval_weaken, bind, Except.bind, pure, Except.pure]
        rw [b.mval_setEnv hie₀, b.mval_setEnv hse]
        cases b.mval σ with
        | error _ => trivial
        | ok w =>
          simp only
          cases w.asRef with
          | error _ => trivial
          | ok id =>
            simp only [hn']
            cases iw.asInt with
            | error _ => trivial
            | ok n => exact memWriteIndex_agree (by agree_tac) _ _ _
  case memoryIndexWriteMemRefNonSimpleIndexCapture R b hb nse hn src hsrc ie hie =>
    refine ⟨by simp [hie], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MSrc.mval, MLoc.write, Val.eval, MPath.mval_weaken]
    cases hn' : nse.eval σ with
    | error _ =>
      simp only [bind, Except.bind]
      cases src.mval σ with
      | error _ => trivial
      | ok sv =>
        simp only
        cases b.mval σ with
        | error _ => trivial
        | ok w =>
          simp only
          cases w.asRef with
          | error _ => trivial
          | ok id => simp only [hn']; trivial
    | ok iw =>
      simp only [bind, Except.bind, pure, Except.pure, Simple.new, Simple.eval, getEnv_setEnv_self,
        src.mval_setEnv hie, b.mval_setEnv hie]
      cases src.mval σ with
      | error _ => trivial
      | ok sv =>
        simp only
        cases b.mval σ with
        | error _ => trivial
        | ok w =>
          simp only
          cases w.asRef with
          | error _ => trivial
          | ok id =>
            simp only [hn']
            cases iw.asInt with
            | error _ => trivial
            | ok n => exact memWriteIndex_agree (agree_setEnv σ ie _) _ _ _
  case memoryFieldWriteUnfoldSource s p b hb f hf nse hn se hse _hnt =>
    refine ⟨by simp [hse], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MSrc.mval, MLoc.write, Val.eval, MPath.mval_weaken]
    cases nse.eval σ with
    | error _ => trivial
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure, Simple.eval_new, b.mval_setEnv hse]
      cases b.mval σ with
      | error _ => trivial
      | ok w =>
        simp only
        cases w.asRef with
        | error _ => trivial
        | ok id => exact memWriteField_agree (agree_setEnv σ se _) _ _ _
  case memoryIndexWriteUnfoldSource p b hb ie nse hn se hse _hnt =>
    refine ⟨by simp [hse], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, MSrc.mval, MLoc.write, Val.eval, MPath.mval_weaken,
      Simple.eval_weaken]
    cases nse.eval σ with
    | error _ => trivial
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure, Simple.eval_new, b.mval_setEnv hse,
        ie.eval_setEnv hse]
      cases b.mval σ with
      | error _ => trivial
      | ok w =>
        simp only
        cases w.asRef with
        | error _ => trivial
        | ok id =>
          simp only
          cases ie.eval σ with
          | error _ => trivial
          | ok iv =>
            simp only
            cases iv.asInt with
            | error _ => trivial
            | ok n => exact memWriteIndex_agree (agree_setEnv σ se _) _ _ _

  -- Compound assignment: the source first, then the target.
  case compoundAssignValueRhsCapture p op hop hp l nse hn se hse =>
    refine ⟨by simp [hse], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Val.eval]
    cases nse.eval σ with
    | error _ => trivial
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure, Simple.eval_new, OpLoc.store_weaken]
      exact OpLoc.store_agree (agree_setEnv σ se _) (by simpa using hse) op l v
  case storageFieldOpAssignUnfoldLeftFst s p op hop hp nsp hn f hf se sp hsp =>
    refine ⟨by simp [hsp], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Val.eval, Simple.eval_weaken, OpLoc.store, Loc.resolve]
    cases nsp.resolve σ with
    | error _ => cases se.eval σ <;> trivial
    | ok rs =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [se.eval_setEnv hsp]
      cases se.eval σ with
      | error _ => trivial
      | ok v =>
        simp only [SPath.new, SPath.resolve, envPath, setEnv_env, lookupBy_setBy_self]
        exact opStore_agree (agree_setEnv σ sp _) op p _ _ v
  case storageIndexOpAssignUnfoldLeftFst R kp p op hop hp it nsp hn ie se sp hsp =>
    refine ⟨by simp [hsp], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Val.eval, Simple.eval_weaken, OpLoc.store, Loc.resolve]
    cases nsp.resolve σ with
    | error _ => cases se.eval σ <;> trivial
    | ok rs =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [se.eval_setEnv hsp, ie.eval_setEnv hsp]
      cases se.eval σ with
      | error _ => trivial
      | ok v =>
        simp only [SPath.new, SPath.resolve, envPath, setEnv_env, lookupBy_setBy_self]
        cases ie.eval σ with
        | error _ => trivial
        | ok iv =>
          cases iv with
          | bool _ => trivial
          | int i => exact opStore_agree (agree_setEnv σ sp _) op p _ _ v

  -- Increment through a captured receiver: the receiver is resolved first either way.
  case storageFieldIncrementUnfoldLeftFst s p op hp nsp hn f hf sp hsp =>
    refine ⟨by simp [hsp], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, OpLoc.bump, Loc.resolve]
    cases nsp.resolve σ with
    | error _ => trivial
    | ok rs =>
      simp only [bind, Except.bind, pure, Except.pure, SPath.new, SPath.resolve, envPath,
        setEnv_env, lookupBy_setBy_self]
      exact bumpStore_agree (agree_setEnv σ sp _) op p _ _
  case storageIndexIncrementUnfoldLeftFst R kp p op hp it nsp hn ie sp hsp =>
    refine ⟨by simp [hsp], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, OpLoc.bump, Loc.resolve, Val.eval, Simple.eval_weaken]
    cases nsp.resolve σ with
    | error _ => trivial
    | ok rs =>
      simp only [bind, Except.bind, pure, Except.pure, SPath.new, SPath.resolve, envPath,
        setEnv_env, lookupBy_setBy_self]
      rw [ie.eval_setEnv hsp]
      cases ie.eval σ with
      | error _ => trivial
      | ok iv =>
        cases iv with
        | bool _ => trivial
        | int i => exact bumpStore_agree (agree_setEnv σ sp _) op p _ _

  -- Order-changing rules: the premise evaluates the same parts, in another order.
  case storageIndexWriteStorageRef_unfold_leftFst R₀ kp R it nsp hn e src hm sp ie hsp hie =>
    have hie₀ := isFresh_of_sub (Ctx.Sub.fresh hsp _) hie
    have hne := ne_of_isFresh_setBy hie
    refine ⟨by simp [hsp, hie₀], fun σ => ?_⟩
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
  case storageIndexWriteNonSimpleIndexCapture R₀ kp p it sp hs nse hn e se ie hse hie _hnt =>
    have hie₀ := isFresh_of_sub (Ctx.Sub.fresh hse _) hie
    have hne := ne_of_isFresh_setBy hie
    refine ⟨by simp [hse, hie₀], fun σ => ?_⟩
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
    refine ⟨by simp [hie], fun σ => ?_⟩
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
  case binopUnfoldLeft p q op hop hq x h nse hn e se hse =>
    refine ⟨by simp [hse], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure]
    cases hv : nse.eval σ with
    | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, hv]
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [binop_left_eval hse op hop hq nse e _ σ hv]
      exact SameOk.setEnv_val (by agree_tac) _ _
  case binopUnfoldRight p q op hop hq hsc x h a nse hn se hse =>
    refine ⟨by simp [hse], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure]
    cases hv : nse.eval σ with
    | error _ =>
      simp only [bind, Except.bind, pure, Except.pure, Val.eval]
      cases a.eval σ with
      | error _ => simp [SameOk]
      | ok lv => cases op <;> simp [BinOp.shortCircuits] at hsc <;> simp [SameOk, hv, bind, Except.bind, pure, Except.pure]
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [binop_right_eval hse op hop hq hsc a nse _ σ hv]
      exact SameOk.setEnv_val (by agree_tac) _ _
  case unopCapture p q op hop hq x h nse hn se hse =>
    refine ⟨by simp [hse], fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure]
    cases hv : nse.eval σ with
    | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure, Val.eval, hv]
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure]
      rw [unop_capture_eval op hop hq nse σ hv]
      exact SameOk.setEnv_val (by agree_tac) _ _
  -- Short-circuit: in a state of `Γ` the right operand is a boolean.
  case logicalAndShortCircuitRhs hop hq x h a nse hn =>
    refine ⟨by simp, fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Val.eval]
    cases a.eval σ with
    | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
    | ok lv =>
      cases lv with
      | int _ =>
        simp only [bind, Except.bind, pure, Except.pure]
        cases nse.eval σ <;> simp [SameOk, applyBinOp, Value.asBool, bind, Except.bind, pure, Except.pure]
      | bool b =>
        cases b with
        | false => simp [SameOk, bind, Except.bind, pure, Except.pure, Simple.eval]; exact EnvAgreeExcept.refl _ _
        | true =>
          simp only [bind, Except.bind, pure, Except.pure]
          cases nse.eval σ with
          | error _ => simp [SameOk]
          | ok w =>
            cases w with
            | int _ => simp [SameOk, applyBinOp, Value.asBool, Simple.eval, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure]
            | bool c =>
              cases c <;> simp [SameOk, applyBinOp, Value.asBool, checkArith, Simple.eval,
                getEnv_setEnv_self, SemanticsProperties.State.setEnv_setEnv_absorb, bind, Except.bind, pure, Except.pure] <;>
                exact EnvAgreeExcept.refl _ _
  case logicalOrShortCircuitRhs hop hq x h a nse hn =>
    refine ⟨by simp, fun σ => ?_⟩
    simp only [Prog.run, Stmt.run, bind_pure, Val.eval]
    cases a.eval σ with
    | error _ => simp [SameOk, bind, Except.bind, pure, Except.pure]
    | ok lv =>
      cases lv with
      | int _ =>
        simp only [bind, Except.bind, pure, Except.pure]
        cases nse.eval σ <;> simp [SameOk, applyBinOp, Value.asBool, bind, Except.bind, pure, Except.pure]
      | bool b =>
        cases b with
        | true => simp [SameOk, bind, Except.bind, pure, Except.pure, Simple.eval]; exact EnvAgreeExcept.refl _ _
        | false =>
          simp only [bind, Except.bind, pure, Except.pure]
          cases nse.eval σ with
          | error _ => simp [SameOk]
          | ok w =>
            cases w with
            | int _ => simp [SameOk, applyBinOp, Value.asBool, Simple.eval, getEnv_setEnv_self, bind, Except.bind, pure, Except.pure]
            | bool c =>
              cases c <;> simp [SameOk, applyBinOp, Value.asBool, checkArith, Simple.eval,
                getEnv_setEnv_self, SemanticsProperties.State.setEnv_setEnv_absorb, bind, Except.bind, pure, Except.pure] <;>
                exact EnvAgreeExcept.refl _ _
  -- Step 1, for every `lhs`: read a member through a captured receiver.
  case storageFieldRead_unfold_rightFst s T nsp hn f hf sp k hsp =>
    refine ⟨by simp [hsp], fun σ => ?_⟩
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
    refine ⟨by simp [hsp], fun σ => ?_⟩
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
    refine ⟨by simp [hie], fun σ => ?_⟩
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
    | .cons s .nil => ∀ σ, s.run σ = (Upd.save (.field (.loc (.root "alice" rfl rfl)) "age" rfl)
        (.val (.simple (.lit 10 rfl))) : Upd StandardExample []).apply σ
    | _ => False :=
  Taclet.sound (m := .box) (.storageFieldWriteSave _ rfl _ _ _)

/-- `people[1].age = 10;` (a mapping of `Person`s is `folks`) is
`storageFieldWrite_unfold_leftFst`: its three statements end as it does,
off the fresh `se` and `sp`. -/
example : match ksol[StandardExample]{ folks[1].age = 10; } with
    | .cons s .nil => ∃ ns Γ₁ P h, Nonempty (Taclet StandardExample .diamond s (.unfold (Γ₁ := Γ₁) ns P h)) ∧
        ∀ σ, SameOk ns (P.run σ) (s.run σ)
    | _ => False :=
  let d := Taclet.storageFieldWrite_unfold_leftFst (m := .diamond) _ rfl _ rfl _ "se" "sp" rfl rfl rfl
  ⟨_, _, _, _, ⟨d⟩, (Taclet.sound d).2⟩

end Examples

end Kernel
end Solidity
