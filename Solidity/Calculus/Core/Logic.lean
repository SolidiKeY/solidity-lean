import Solidity.Calculus.Core.Step
import Solidity.Semantics.Core
import Solidity.Update
import Solidity.Theory.Observe
import Solidity.Typing.Soundness

/-!
# What a scoped formula means

`Update.lean`'s `holds` for the scoped formulas of `Calculus/Core/Fml.lean`
(`docs/intrinsic.md`, M6a), over M3's typed states (`State C Γ`,
`Semantics/Core.lean`): a local is read by its position, so no term reads a
local that is not there.  A term's symbols are `Update.lean`'s, read on the
global part of the state (`State.glob`), so a scoped term means what its
erasure means wherever the locals agree.  An update is parallel (every
right-hand side read in the state it is applied in) and leaves the context
`Δ` its type says: a declaration pushes, a pop drops a suffix, a `drop`
thins.  A modality runs its program, then its frames (`Frames.run`: the
rest of the program, the scope ends); a hidden binder (`Fml.bind`) is a
universal over the local's values.

Soundness of the strategy is stated rule by rule against M3's interpreter
(`Core.Stmt.run`), with no freshness premise: a rule's fresh locals are
positions its premise pushes and pops.  `Premise.sound_*` are the
premise shapes (an update, a block, a binder, a split, a check, a closed
goal), and `Stmt.step_sound_*` the rules proved so far from them.
-/

namespace Solidity.Core

open Semantics (Value SVal MVal Seg Halt Res lookupBy setBy allocDefault applyUnOp)
open Solidity (evalBinop unopCheck)
open Theory Theory.StValue
open Solidity (Srt Op0 Op1 Op2 Op3 Modality IntOp)

variable {C : Contract}

/-! ## Terms -/

section Terms

variable {Γ : Ctx}

/-- A term read by the interpreter in `σ`: a local by its position, a symbol
on the global part. -/
def Tm.eval (σ : State C Γ) : {s : Srt} → Tm C Γ s → s.Ev
  | _, .pvV i => pure (Env.get i σ.env)
  | _, .pvP i => aliasPath σ i
  | _, .pvS i => pure { σ.glob with storage := Env.get i σ.env }
  | _, .pvI i => memRef σ i
  | _, .netOf i a => do
    let l : List (Int × Int) := Env.get i σ.env
    pure (.int ((lookupBy (← (← a.eval σ).asInt) l).getD 0))
  | _, .app0 o => o.eval σ.glob
  | _, .app1 o _ a => o.eval σ.glob (a.eval σ)
  | _, .app2 o a b => o.eval σ.glob (a.eval σ) (b.eval σ)
  | _, .app3 o a b c => o.eval σ.glob (a.eval σ) (b.eval σ) (c.eval σ)

/-- A term in the Theory, over `State.abs σ.glob` (`Update.lean`'s
`Tm.denote`). -/
def Tm.denote (σ : State C Γ) : {s : Srt} → Tm C Γ s → s.Den
  | _, .pvV i => .prim (Env.get i σ.env)
  | _, .pvP i => match aliasPath σ i with
    | .ok (r, segs) => rootPath r segs
    | .error _ => []
  | _, .pvS i => SVal.abs.fields (Env.get i σ.env)
  | _, .pvI _ => ()
  | _, .netOf i a => match a.denote σ with
    | .prim (.int n) => .prim (.int ((lookupBy n (Env.get i σ.env : List (Int × Int))).getD 0))
    | _ => .st .mtSt
  | _, .app0 o => o.denote σ.glob
  | _, .app1 o _ a => o.denote σ.glob (a.denote σ)
  | _, .app2 o a b => o.denote σ.glob (a.eval σ) (b.eval σ) (a.denote σ) (b.denote σ)
  | _, .app3 o a b c => o.denote (a.denote σ) (b.denote σ) (c.denote σ)

end Terms

/-! ## Updates -/

section Updates

/-- A scope's locals dropped by a thinning: the ones `Γ` keeps. -/
def Env.thin : {Γ Δ : Ctx} → Thin Γ Δ → Env C Δ → Env C Γ
  | _, _, .refl, e => e
  | _, _, .keep h, e => (e.1, Env.thin h e.2)
  | _, _, .drop h, e => Env.thin h e.2

/-- A state's locals thinned. -/
def State.thin {Γ Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) : State C Γ :=
  σ.withEnv (Env.thin h σ.env)

variable {Γ : Ctx}

/-- What a local is set to, read in `σ₀`. -/
def Rhs.eval (σ₀ : State C Γ) : {t : LTy} → Rhs C Γ t → Res (t.Denote C)
  | _, .val t => t.eval σ₀
  | _, .path p => do pure (some (← p.eval σ₀))
  | _, .unset => pure none
  | _, .mref i => do pure (some (← i.eval σ₀))
  | _, .store s => do pure (← s.eval σ₀).storage
  | _, .saveNet => pure σ₀.net
  | _, .saveNetMt => pure []

/-- One assigning element: its right-hand sides read in `σ₀`, the write
into `τ` (`Update.lean`'s `UpdElem.write`). -/
def UpdElem.write {Δ : Ctx} (σ₀ : State C Γ) : UpdElem C Γ Δ → State C Δ → Res (State C Δ)
  | .local i r, τ => do pure (τ.setLocal i (← r.eval σ₀))
  | .storage s, τ => do
    let st := (← s.eval σ₀).storage
    pure (τ.withGlob { τ.glob with storage := st })
  | .memory m, τ => do
    let μ ← m.eval σ₀
    pure (τ.withGlob { τ.glob with heap := μ.heap, nextId := μ.nextId })
  | .selfBalance op a, τ => do
    let amt ← (← a.eval σ₀).asInt
    pure (τ.withGlob { τ.glob with selfBalance := op.apply σ₀.selfBalance amt })
  | .net r op a, τ => do
    let addr ← (← r.eval σ₀).asInt
    let amt ← (← a.eval σ₀).asInt
    pure (τ.withGlob { τ.glob with net := setBy addr (op.apply (τ.glob.getNet addr) amt) τ.net })
  | .pay r a, τ => do
    let addr ← (← r.eval σ₀).asInt
    let amt ← (← a.eval σ₀).asInt
    if amt < 0 then .error .revert
    else pure (τ.withGlob { τ.glob with
      net := if addr = σ₀.tx.selfAddress then τ.net else setBy addr (τ.glob.getNet addr - amt) τ.net })
  | .netMt r a, τ => do
    let addr ← (← r.eval σ₀).asInt
    let amt ← (← a.eval σ₀).asInt
    pure (τ.withGlob { τ.glob with net := [(addr, amt)] })
  | .setBalance a, τ => do
    let amt ← (← a.eval σ₀).asInt
    pure (τ.withGlob { τ.glob with selfBalance := amt })

/-- The state an update applied in `σ₀` leaves, in the context its type
says. -/
def Upd.apply (σ₀ : State C Γ) : {Δ : Ctx} → Upd C Γ Δ → Res (State C Δ)
  | _, .nil => pure σ₀
  | _, .snoc U e => do e.write σ₀ (← U.apply σ₀)
  | _, .decl U _ r => do
    let τ ← U.apply σ₀
    pure (τ.push (← r.eval σ₀))
  | _, .pop U h => (U.apply σ₀).map (State.drop h)
  | _, .drop U h => (U.apply σ₀).map (State.thin h)

end Updates

/-! ## Formulas -/

/-- `p` after an outcome under `m`: `p` of the state, or `m.onHalt`. -/
def _root_.Solidity.Modality.afterC {α : Type} (m : Modality) (p : α → Prop) : Res α → Prop
  | .ok τ => p τ
  | .error _ => m.onHalt

/-- `p` after a run under `m`: as `afterC`, and the run did not panic. -/
def _root_.Solidity.Modality.afterRunC {α : Type} (m : Modality) (p : α → Prop) (r : Res α) : Prop :=
  m.afterC p r ∧ r ≠ .error .panic

/-- What the frames do after the program: the rest run, a scope's locals
popped or dropped. -/
def Frames.run {Γ₀ : Ctx} : {Γ : Ctx} → State C Γ → Frames C Γ Γ₀ → Res (State C Γ₀)
  | _, σ, .nil => pure σ
  | _, σ, .seq ω κ => do Frames.run (← Prog.run σ ω) κ
  | _, σ, .pop _ h κ => Frames.run (σ.drop h) κ
  | _, σ, .drop h κ => Frames.run (σ.thin h) κ

/-- The locals `xs` set as `b` says: a loop body's frame anonymised. -/
def State.anon {Γ : Ctx} (σ : State C Γ) (xs : List ((t : LTy) × Idx Γ t))
    (b : (x : (t : LTy) × Idx Γ t) → x.1.Denote C) : State C Γ :=
  xs.foldl (fun τ x => τ.setLocal x.2 (b x)) σ

/-- A local holds what a branch reads it as: a `bool` local a `bool`. -/
def LTy.BoolOK : (t : LTy) → t.Denote C → Prop
  | .val .bool, v => ∃ b, v = .bool b
  | _, _ => True

/-- Every `bool` local of the state holds a `bool`.  M3's values are untyped,
so a `bool` local may hold a number (a binder's value, a storage read), and a
branch on it is stuck; the diamond is read from and into such states only
(`Modality.afterT`), what the typed run (M4) has by construction. -/
def State.BoolOK {Γ : Ctx} (σ : State C Γ) : Prop := Env.All LTy.BoolOK σ.env

/-- `p`, and under the diamond `ok` too, of the state an outcome ends in. -/
def _root_.Solidity.Modality.okP {α : Type} (m : Modality) (ok p : α → Prop) : α → Prop :=
  match m with
  | .box => p
  | .diamond => fun τ => ok τ ∧ p τ

/-- What an update says from a state `T` describes: the box as `afterC`;
the diamond from a state with its `bool` locals `bool`s (`T`), into one
(`ok`). -/
def _root_.Solidity.Modality.afterT {α : Type} (m : Modality) (T : Prop) (ok p : α → Prop)
    (r : Res α) : Prop :=
  match m with
  | .box => Modality.afterC .box p r
  | .diamond => T → Modality.afterC .diamond (fun τ => ok τ ∧ p τ) r

/-- What a modality says of a run, as `afterT` (and no panic). -/
def _root_.Solidity.Modality.afterRunT {α : Type} (m : Modality) (T : Prop) (ok p : α → Prop)
    (r : Res α) : Prop :=
  match m with
  | .box => Modality.afterRunC .box p r
  | .diamond => T → Modality.afterRunC .diamond (fun τ => ok τ ∧ p τ) r

theorem _root_.Solidity.Modality.afterT_iff {α : Type} {m : Modality} {T : Prop}
    {ok p : α → Prop} {r : Res α} :
    m.afterT T ok p r ↔ ((m = .diamond → T) → m.afterC (m.okP ok p) r) := by
  cases m with
  | box => exact ⟨fun h _ => h, fun h => h nofun⟩
  | diamond => exact ⟨fun h hT => h (hT rfl), fun h hT => h fun _ => hT⟩

theorem _root_.Solidity.Modality.afterRunT_iff {α : Type} {m : Modality} {T : Prop}
    {ok p : α → Prop} {r : Res α} :
    m.afterRunT T ok p r ↔ ((m = .diamond → T) → m.afterRunC (m.okP ok p) r) := by
  cases m with
  | box => exact ⟨fun h _ => h, fun h => h nofun⟩
  | diamond => exact ⟨fun h hT => h (hT rfl), fun h hT => h fun _ => hT⟩

/-- **Whether `φ` holds in `σ`** (`Update.lean`'s `holds`; the diamond from
and into states whose `bool` locals hold `bool`s, `Modality.afterT`). -/
def holds : {Γ : Ctx} → State C Γ → Fml C Γ → Prop
  | _, _, .tt => True
  | _, σ, .eq a b => Theory.StValue.Equiv (a.denote σ) (b.denote σ)
  | _, σ, .defined t => ∃ x, t.eval σ = .ok x
  | _, σ, .not φ => ¬ holds σ φ
  | _, σ, .and φ ψ => holds σ φ ∧ holds σ ψ
  | _, σ, .imp φ ψ => holds σ φ → holds σ ψ
  | _, σ, .upd m U φ => m.afterT σ.BoolOK State.BoolOK (holds · φ) (U.apply σ)
  | _, σ, .modal m P κ φ =>
    m.afterRunT σ.BoolOK State.BoolOK (holds · φ) (do Frames.run (← Prog.run σ P) κ)
  | _, σ, .havoc φ => ∀ st nt, holds (σ.withGlob (σ.glob.havoc st nt)) φ
  | _, σ, .all _ p φ => ∀ v, p.admits v → holds (σ.push (t := .val p) v) φ
  | _, σ, .bind m _ _ φ => m.forallB fun v => holds (σ.push v) φ
  | _, σ, .anon xs φ => ∀ b, holds (σ.anon xs b) φ

/-- Valid: true in every state of the empty context. -/
def Valid (φ : Fml C []) : Prop := ∀ σ, holds σ φ

/-- A hidden binder holds where its body holds for every value
(`Modality.forallB`, universal under both modalities). -/
theorem holds_bind_intro {m : Modality} {x : Var} {t : LTy} {φ : Fml C (t :: Γ)} {σ : State C Γ}
    (h : ∀ v, holds (σ.push v) φ) : holds σ (.bind m x t φ) :=
  Modality.forallB_intro h

/-! ## States whose `bool` locals hold `bool`s -/

section BoolOK

variable {Γ : Ctx}

theorem Env.All.thin {P : (t : LTy) → t.Denote C → Prop} :
    {Γ Δ : Ctx} → (h : Thin Γ Δ) → {e : Env C Δ} → Env.All P e → Env.All P (Env.thin h e)
  | _, _, .refl, _, he => he
  | _, _, .keep h, _, he => ⟨he.1, Env.All.thin h he.2⟩
  | _, _, .drop h, _, he => Env.All.thin h he.2

theorem State.BoolOK.drop {Δ : Ctx} {σ : State C Δ} (hT : σ.BoolOK) (h : Ext Γ Δ) :
    (σ.drop h).BoolOK :=
  Env.All.drop h hT

theorem State.BoolOK.thin {Δ : Ctx} {σ : State C Δ} (hT : σ.BoolOK) (h : Thin Γ Δ) :
    (σ.thin h).BoolOK :=
  Env.All.thin h hT

theorem State.BoolOK.push {t : LTy} {σ : State C Γ} {v : t.Denote C} (hT : σ.BoolOK)
    (hv : LTy.BoolOK t v) : (σ.push v).BoolOK :=
  ⟨hv, hT⟩

theorem State.BoolOK.pop {t : LTy} {σ : State C Γ} {v : t.Denote C} (hT : (σ.push v).BoolOK) :
    σ.BoolOK :=
  hT.2

theorem State.BoolOK.setLocal {t : LTy} {σ : State C Γ} (hT : σ.BoolOK) (i : Idx Γ t)
    {v : t.Denote C} (hv : LTy.BoolOK t v) : (σ.setLocal i v).BoolOK :=
  Env.All.set i hT hv

theorem State.BoolOK.withGlob {σ : State C Γ} (hT : σ.BoolOK) (g : Semantics.State) :
    (σ.withGlob g).BoolOK :=
  hT

theorem State.BoolOK.get {t : LTy} {σ : State C Γ} (hT : σ.BoolOK) (i : Idx Γ t) :
    LTy.BoolOK t (Env.get i σ.env) :=
  Env.All.get i hT

/-- A value of a type that is not `bool`, or a `bool`, is one a local holds. -/
theorem LTy.BoolOK.default (p : PrimTy) : LTy.BoolOK (C := C) (.val p) (PrimTy.default p) := by
  cases p <;> first | trivial | exact ⟨false, rfl⟩

end BoolOK

/-! ## The program after a rule -/

section After

variable {Γ Γ₁ Γ₀ : Ctx} (m : Modality)

/-- A modality from a state the diamond reads from: what running says. -/
theorem holds_modal {m : Modality} {Γ Γ' : Ctx} (P : Prog C Γ Γ') (κ : Frames C Γ' Γ₀)
    (φ : Fml C Γ₀) {σ : State C Γ} (hT : m = .diamond → σ.BoolOK) :
    holds σ (.modal m P κ φ) ↔
      m.afterRunC (m.okP State.BoolOK (holds · φ)) (do Frames.run (← Prog.run σ P) κ) :=
  Modality.afterRunT_iff.trans ⟨fun h => h hT, fun h _ => h⟩

/-- A modality holds when running says so from a state the diamond reads
from. -/
theorem holds_modal_intro {m : Modality} {Γ Γ' : Ctx} {P : Prog C Γ Γ'} {κ : Frames C Γ' Γ₀}
    {φ : Fml C Γ₀} {σ : State C Γ}
    (h : (m = .diamond → σ.BoolOK) →
      m.afterRunC (m.okP State.BoolOK (holds · φ)) (do Frames.run (← Prog.run σ P) κ)) :
    holds σ (.modal m P κ φ) :=
  Modality.afterRunT_iff.2 h

/-- An update from a state the diamond reads from: what applying it says. -/
theorem holds_upd {m : Modality} {Γ Δ : Ctx} (U : Upd C Γ Δ) (φ : Fml C Δ) {σ : State C Γ}
    (hT : m = .diamond → σ.BoolOK) :
    holds σ (.upd m U φ) ↔ m.afterC (m.okP State.BoolOK (holds · φ)) (U.apply σ) :=
  Modality.afterT_iff.trans ⟨fun h => h hT, fun h _ => h⟩

theorem holds_upd_intro {m : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ}
    {σ : State C Γ}
    (h : (m = .diamond → σ.BoolOK) → m.afterC (m.okP State.BoolOK (holds · φ)) (U.apply σ)) :
    holds σ (.upd m U φ) :=
  Modality.afterT_iff.2 h

/-- `okP` of a state the diamond reads from is `p`. -/
theorem _root_.Solidity.Modality.okP_iff {α : Type} {m : Modality} {ok p : α → Prop} {a : α}
    (hT : m = .diamond → ok a) : m.okP ok p a ↔ p a := by
  cases m with
  | box => exact Iff.rfl
  | diamond => exact ⟨fun h => h.2, fun h => ⟨hT rfl, h⟩⟩

/-- The state `okP` holds of is one the diamond reads from. -/
theorem _root_.Solidity.Modality.okP_ok {α : Type} {m : Modality} {ok p : α → Prop} {a : α}
    (h : m.okP ok p a) : m = .diamond → ok a := by
  cases m with
  | box => nofun
  | diamond => exact fun _ => h.1

/-- The frames exited: what running them says. -/
theorem holds_exit {Γ : Ctx} (κ : Frames C Γ Γ₀) : ∀ (φ : Fml C Γ₀) (σ : State C Γ),
    (m = .diamond → σ.BoolOK) →
    (holds σ (κ.exit m φ) ↔ m.afterRunC (m.okP State.BoolOK (holds · φ)) (κ.run σ)) := by
  induction κ with
  | nil =>
    intro φ σ hT
    show holds σ φ ↔ m.okP State.BoolOK (holds · φ) σ ∧ (Except.ok σ : Res _) ≠ .error .panic
    rw [Modality.okP_iff hT]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_true]
  | seq ω κ ih =>
    intro φ σ hT
    rw [Frames.exit_seq]
    cases ω with
    | nil => exact ih φ σ hT
    | cons s ω => exact holds_modal (.cons s ω) κ φ hT
  | pop _ h κ ih =>
    intro φ σ hT
    rw [Frames.exit_pop, holds_upd _ _ hT]
    show m.okP State.BoolOK _ (σ.drop h) ↔ _
    rw [Modality.okP_iff fun e => (hT e).drop h]
    exact ih φ (σ.drop h) fun e => (hT e).drop h
  | drop h κ ih =>
    intro φ σ hT
    show holds σ (.upd m (Upd.nil.drop h) (κ.exit m φ)) ↔ _
    rw [holds_upd _ _ hT]
    show m.okP State.BoolOK _ (σ.thin h) ↔ _
    rw [Modality.okP_iff fun e => (hT e).thin h]
    exact ih φ (σ.thin h) fun e => (hT e).thin h

/-- The rest of the program from a state, gone into the frames when it is
empty. -/
theorem holds_modalK (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) (σ : State C Γ)
    (hT : m = .diamond → σ.BoolOK) :
    holds σ (Fml.modalK m ω κ φ) ↔
      m.afterRunC (m.okP State.BoolOK (holds · φ)) (do Frames.run (← Prog.run σ ω) κ) := by
  cases ω with
  | nil => exact holds_exit m κ φ σ hT
  | cons s ω => exact holds_modal (.cons s ω) κ φ hT

end After

/-! ## Premise shapes

What each kind of premise needs of the statement it replaces, for
`Premise.fml m ω κ φ` to give `⟨ s; ω κ ⟩ φ`. -/

section Shapes

variable {Γ Γ' Γ₁ Γ₀ : Ctx} {m : Modality}

/-- The outcome of `s` and then the rest: the run of `s; ω` and the frames. -/
theorem run_cons_frames (s : Stmt C Γ Γ') (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) (σ : State C Γ) :
    (do Frames.run (← Prog.run σ (.cons s ω)) κ) =
      (do let τ ← s.run σ; Frames.run (← Prog.run τ ω) κ) := by
  rw [Prog.run_cons]
  cases s.run σ <;> rfl

/-- An outcome that is the same after `r` as after `r'`, `r` not a panic,
satisfies the same: the step every shape ends with. -/
theorem afterRunC_bind {α β : Type} {p : β → Prop} {r r' : Res α} (f : α → Res β)
    (hr : r = r') (hp : r' ≠ .error .panic) :
    m.afterC (fun a => m.afterRunC p (f a)) r → m.afterRunC p (r'.bind f) := by
  subst hr
  cases r with
  | ok a => exact id
  | error e => exact fun h => ⟨h, fun h' => hp (congrArg Except.error (Except.error.inj h'))⟩

/-- **An update**: `{U} ⟨ ω κ ⟩ φ` gives `⟨ s; ω κ ⟩ φ` when `U` leaves
what `s` does, and never panics there. -/
theorem Premise.sound_update {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} (σ : State C Γ)
    (hs : U.apply σ = s.run σ) (hp : s.run σ ≠ .error .panic) (ω : Prog C Γ' Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.update U).fml m ω κ φ) → holds σ (.modal m (.cons s ω) κ φ) := by
  intro h
  refine holds_modal_intro fun hT => ?_
  have h' := (holds_upd U _ hT).1 h
  rw [run_cons_frames]
  refine afterRunC_bind (fun τ => do Frames.run (← Prog.run τ ω) κ) hs hp ?_
  cases hU : U.apply σ with
  | ok τ =>
    rw [hU] at h'
    exact (holds_modalK m ω κ φ τ (Modality.okP_ok h')).1 ((Modality.okP_iff (Modality.okP_ok h')).1 h')
  | error e => rw [hU] at h'; exact h'

/-- **A block**: `⟨ P (pop) ω κ ⟩ φ` gives `⟨ s; ω κ ⟩ φ` when `P`, its
fresh locals popped, runs as `s`. -/
theorem Premise.sound_unfold {Γ'' : Ctx} {P : Prog C Γ Γ''} {h : Ext Γ' Γ''} {s : Stmt C Γ Γ'}
    (σ : State C Γ) (hs : (Prog.run σ P).map (State.drop h) = s.run σ) (ω : Prog C Γ' Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.unfold P h).fml m ω κ φ) → holds σ (.modal m (.cons s ω) κ φ) := by
  intro hp
  refine holds_modal_intro fun hT => ?_
  have h' := (holds_modal P (.pop .capture h (.seq ω κ)) φ hT).1 hp
  rw [run_cons_frames, ← hs]
  revert h'
  cases Prog.run σ P <;> exact id

/-- **A block dropping a frame from under what it keeps**
(`Premise.inline`). -/
theorem Premise.sound_inline {Γ'' : Ctx} {P : Prog C Γ Γ''} {h : Thin Γ' Γ''} {s : Stmt C Γ Γ'}
    (σ : State C Γ) (hs : (Prog.run σ P).map (State.thin h) = s.run σ) (ω : Prog C Γ' Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.inline P h).fml m ω κ φ) → holds σ (.modal m (.cons s ω) κ φ) := by
  intro hp
  refine holds_modal_intro fun hT => ?_
  have h' := (holds_modal P (.drop h (.seq ω κ)) φ hT).1 hp
  rw [run_cons_frames, ← hs]
  revert h'
  cases Prog.run σ P <;> exact id

/-- **A hidden binder**: `∀ v. ⟨ P ω κ ⟩ φ` from `σ` with `v` pushed gives
`⟨ s; ω κ ⟩ φ` when, for some `v` of its type, `P` runs from there as `s`
from `σ`. -/
theorem Premise.sound_bind {x : Var} {t : LTy} {P : Prog C (t :: Γ) Γ'} {s : Stmt C Γ Γ'}
    (σ : State C Γ) (hs : ∃ v, LTy.BoolOK t v ∧ Prog.run (σ.push v) P = s.run σ)
    (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.bind x t P).fml m ω κ φ) → holds σ (.modal m (.cons s ω) κ φ) := by
  intro h
  obtain ⟨v, hvT, hv⟩ := hs
  refine holds_modal_intro fun hT => ?_
  have h' := (holds_modal P (.seq ω κ) φ fun e => (hT e).push hvT).1 (Modality.forallB_all h v)
  rw [run_cons_frames, ← hv]
  exact h'

/-- **A capture**: `T se = e; s'`, `se` popped after `s'`, runs as `s` when
`e` halts as `s` does, and otherwise `s'` from `σ` with the value pushed
runs as `s` from `σ`. -/
theorem Premise.sound_capture {p : PrimTy} {x : Var} {e : Val C Γ p}
    {s' : Stmt C (.val p :: Γ) (.val p :: Γ)} {s : Stmt C Γ Γ} (σ : State C Γ)
    (hok : ∀ v, e.eval σ = .ok v → (s'.run (σ.push v)).map (State.drop (.push .refl)) = s.run σ)
    (herr : ∀ h, e.eval σ = .error h → s.run σ = .error h) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.capture p x e s').fml m ω κ φ) → holds σ (.modal m (.cons s ω) κ φ) := by
  refine Premise.sound_unfold σ ?_ ω κ φ
  rw [Prog.run_cons]
  show (Except.bind (Run.declLocal p (some e) σ) fun τ => Prog.run τ (.cons s' .nil)).map _ = _
  cases he : e.eval σ with
  | error h => simp only [Run.declLocal, he, herr h he]; rfl
  | ok v =>
    rw [← hok v he]
    simp only [Run.declLocal, he]
    show (Prog.run (σ.push v) (.cons s' .nil)).map _ = _
    rw [Prog.run_cons]
    cases s'.run (σ.push v) <;> rfl

/-- A block's run, its locals popped, then the rest and the frames: the
frame a branch ends with (`pop b P.ext`). -/
theorem run_block_frames {Δ : Ctx} (b : BlockKind) (P : Prog C Γ Δ) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (σ : State C Γ) :
    (do Frames.run (← Prog.run σ P) (.pop b P.ext (.seq ω κ))) =
      (do let τ ← (Prog.run σ P).map (State.drop P.ext); Frames.run (← Prog.run τ ω) κ) := by
  cases Prog.run σ P <;> rfl

/-- **Two goals**: `(c → ⟨ P } ω κ ⟩ φ) ∧ (c' → ⟨ Q } ω κ ⟩ φ)` gives
`⟨ s; ω κ ⟩ φ` when one of `c`, `c'` holds, and the branch it guards, its
locals popped, runs as `s`.  `Calculus/Core/SoundLocal.lean`'s
`Premise.Sound.split` gives one from a typed state (a `bool` condition), the
box's stuck case apart. -/
theorem Premise.sound_split {b : BlockKind} {Δ₁ Δ₂ : Ctx} {c c' : Fml C Γ} {P : Prog C Γ Δ₁}
    {Q : Prog C Γ Δ₂} {s : Stmt C Γ Γ} (σ : State C Γ)
    (hc : holds σ c → (Prog.run σ P).map (State.drop P.ext) = s.run σ)
    (hc' : holds σ c' → (Prog.run σ Q).map (State.drop Q.ext) = s.run σ)
    (hcov : holds σ c ∨ holds σ c') (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.split b c c' P Q).fml m ω κ φ) → holds σ (.modal m (.cons s ω) κ φ) := by
  rintro ⟨h₁, h₂⟩
  refine holds_modal_intro fun hT => ?_
  rw [run_cons_frames]
  rcases hcov with h | h
  · have := (holds_modalK m P _ φ σ hT).1 (h₁ h)
    rw [run_block_frames, hc h] at this
    exact this
  · have := (holds_modalK m Q _ φ σ hT).1 (h₂ h)
    rw [run_block_frames, hc' h] at this
    exact this

/-- **A check**: `(c → ⟨ ω κ ⟩ φ) ∧ c` gives `⟨ s; ω κ ⟩ φ` when, `c`
holding, `s` does nothing. -/
theorem Premise.sound_check {c : Fml C Γ} {s : Stmt C Γ Γ} (σ : State C Γ)
    (hc : holds σ c → s.run σ = .ok σ) (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.check c).fml m ω κ φ) → holds σ (.modal m (.cons s ω) κ φ) := by
  rintro ⟨h₁, h₂⟩
  refine holds_modal_intro fun hT => ?_
  rw [run_cons_frames, hc h₂]
  exact (holds_modalK m ω κ φ σ hT).1 (h₁ h₂)

/-- **A closed goal**: `true` gives a box over a statement that halts, not in
a panic, from every state. -/
theorem Premise.sound_done {s : Stmt C Γ Γ'} (σ : State C Γ) (b : Bool)
    (hs : b = true → m = .box ∧ ∃ e, s.run σ = .error e ∧ e ≠ .panic) (ω : Prog C Γ' Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.done b).fml m ω κ φ) → holds σ (.modal m (.cons s ω) κ φ) := by
  intro h
  cases b with
  | false => exact absurd trivial h
  | true =>
    obtain ⟨rfl, e, he, hp⟩ := hs rfl
    show Modality.afterRunC .box _ _
    rw [run_cons_frames, he]
    exact ⟨trivial, fun h => hp (Except.error.inj h)⟩

end Shapes

/-! ## A shifted part reads as it did

A rule reads the parts of its `\find` under its fresh locals (`Val.up` and
its kin): pushed a local, the state reads them as before. -/

section Shift

variable {Γ : Ctx} {t : LTy}

theorem State.glob_push (σ : State C Γ) (w : t.Denote C) : (σ.push w).glob = σ.glob := rfl

theorem Simple.eval_up {p : PrimTy} (s : Simple C Γ p) (σ : State C Γ) (w : t.Denote C) :
    (s.up (t := t)).eval (σ.push w) = s.eval σ := by
  cases s <;> rfl

theorem aliasPath_there {R : RefTy} (i : Idx Γ (.alias R)) (σ : State C Γ) (w : t.Denote C) :
    aliasPath (σ.push w) i.there = aliasPath σ i := rfl

mutual

theorem SPath.resolve_up (σ : State C Γ) (w : t.Denote C) : {T : Ty} → (b : SPath C Γ T) →
    (b.up (t := t)).resolve (σ.push w) = b.resolve σ
  | _, .alias _ => rfl
  | _, .loc l => Loc.resolve_up σ w l

theorem Loc.resolve_up (σ : State C Γ) (w : t.Denote C) : {T : Ty} → (l : Loc C Γ T) →
    (l.up (t := t)).resolve (σ.push w) = l.resolve σ
  | _, .root .. => rfl
  | _, .field b f h => by
    show (do let (r, segs) ← b.up.resolve (σ.push w); pure (r, segs ++ [Seg.field f])) = _
    rw [SPath.resolve_up σ w b]; rfl
  | _, .index it b i => by
    show (do
      let (r, segs) ← b.up.resolve (σ.push w)
      let i ← (← i.up.eval (σ.push w)).keyAt _
      (σ.push w).glob.checkIndex r segs i
      pure (r, segs ++ [Seg.at i])) = _
    rw [SPath.resolve_up σ w b, Val.eval_up σ w i]; rfl

theorem MPath.mval_up (σ : State C Γ) (w : t.Denote C) : {T : Ty} → (b : MPath C Γ T) →
    (b.up (t := t)).mval (σ.push w) = b.mval σ
  | _, .var .. => rfl
  | _, .loc l => MLoc.read_up σ w l

theorem MLoc.read_up (σ : State C Γ) (w : t.Denote C) : {T : Ty} → (l : MLoc C Γ T) →
    (l.up (t := t)).read (σ.push w) = l.read σ
  | _, .field b f h => by
    show (do
      let id ← (← b.up.mval (σ.push w)).asRef
      match ← (σ.push w).glob.getObj id with
      | .struct fields =>
        match lookupBy f fields with
        | some v => pure v
        | none => .error .stuck
      | .array _ _ => .error .stuck) = _
    rw [MPath.mval_up σ w b]; rfl
  | _, .index a b i => by
    show (do
      let id ← (← b.up.mval (σ.push w)).asRef
      let iv ← (← i.up.eval (σ.push w)).asInt
      match ← (σ.push w).glob.getObj id with
      | .array elems _ =>
        if h : 0 ≤ iv ∧ iv.toNat < elems.length then pure (elems.get ⟨iv.toNat, h.2⟩)
        else .error .revert
      | .struct _ => .error .stuck) = _
    rw [MPath.mval_up σ w b, Val.eval_up σ w i]; rfl

theorem Val.eval_up (σ : State C Γ) (w : t.Denote C) : {p : PrimTy} → (v : Val C Γ p) →
    (v.up (t := t)).eval (σ.push w) = v.eval σ
  | _, .simple s => Simple.eval_up s σ w
  | _, .read l => by
    show (do
      let (r, segs) ← l.up.resolve (σ.push w)
      (← (σ.push w).glob.findStorage r segs).asValue) = _
    rw [Loc.resolve_up σ w l]; rfl
  | _, .binop op _ _ a b => by
    show (do evalBinop op _ (← a.up.eval (σ.push w)) (b.up.eval (σ.push w))) = _
    rw [Val.eval_up σ w a, Val.eval_up σ w b]; rfl
  | _, .unop op _ _ a => by
    show (do unopCheck op _ (← applyUnOp op (← a.up.eval (σ.push w)))) = _
    rw [Val.eval_up σ w a]; rfl
  | _, .ternary c a b => by
    show (do pickBranch (← c.up.eval (σ.push w)) (a.up.eval (σ.push w)) (b.up.eval (σ.push w))) = _
    rw [Val.eval_up σ w c, Val.eval_up σ w a, Val.eval_up σ w b]; rfl
  | _, .readMem l => by
    show (do (← l.up.read (σ.push w)).asValue) = _
    rw [MLoc.read_up σ w l]; rfl
  | _, .len b _ => by
    show (do
      let (r, segs) ← b.up.resolve (σ.push w)
      arrayLen (σ.push w).glob r segs) = _
    rw [SPath.resolve_up σ w b]; rfl
  | _, .mlen b _ => by
    show (do memArrayLen (σ.push w).glob (← (← b.up.mval (σ.push w)).asRef)) = _
    rw [MPath.mval_up σ w b]; rfl

end

end Shift

/-! ## Rules -/

section Rules

variable {Γ Γ₁ Γ₀ : Ctx} {m : Modality}

/-- A simple value lowered reads as it evaluates. -/
theorem Simple.eval_lower {p : PrimTy} (s : Simple C Γ p) (σ : State C Γ) :
    s.lower.eval σ = s.eval σ := by
  cases s <;> rfl

/-- `localValueAssign`: `⟨[ v = se; ]⟩ ⇝ { v := se } ⟨[ ]⟩`. -/
theorem Stmt.step_sound_localValueAssign {p : PrimTy} (i : Idx Γ (.val p)) (se : Simple C Γ p)
    (σ : State C Γ) (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.setLocal i (.simple se)).fml m ω κ φ) →
      holds σ (.modal m (.cons (.assignLocal i (.simple se)) ω) κ φ) := by
  refine Premise.sound_update σ ?_ ?_ ω κ φ
  · show (do let v ← (Val.simple se).lower.eval σ; pure (σ.setLocal i v)) =
      (do pure (σ.setLocal i (← (Val.simple se).eval σ)))
    rw [show (Val.simple se).lower = se.lower from rfl, Simple.eval_lower]; rfl
  · show (do pure (σ.setLocal i (← se.eval σ))) ≠ _
    cases se <;> (intro h; cases h)

/-- `valueDeclSkip`: `⟨[ T v; ]⟩ ⇝ { v := defVal(T) } ⟨[ ]⟩`. -/
theorem Stmt.step_sound_valueDeclSkip (p : PrimTy) (x : Var) (σ : State C Γ)
    (ω : Prog C (.val p :: Γ) Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.update (Upd.nil.decl x (.val (p := p) (.app0 (.lit p.default))))).fml m ω κ φ) →
      holds σ (.modal m (.cons (.declLocal p x none) ω) κ φ) :=
  Premise.sound_update σ rfl (by intro h; cases h) ω κ φ

/-- `storageLocalDeclSkip`: `⟨[ T storage lsv; ]⟩ ⇝ { lsv := unset } ⟨[ ]⟩`. -/
theorem Stmt.step_sound_storageLocalDeclSkip (R : RefTy) (x : Var) (σ : State C Γ)
    (ω : Prog C (.alias R :: Γ) Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.update (Upd.nil.decl (t := .alias R) x .unset)).fml m ω κ φ) →
      holds σ (.modal m (.cons (.declStorage R x none) ω) κ φ) :=
  Premise.sound_update σ rfl (by intro h; cases h) ω κ φ

/-- `revertBox`, `revertDiamond`: `[ revert(); ] ⇝ true`, `⟨ revert(); ⟩ ⇝ false`. -/
theorem Stmt.step_sound_revert (σ : State C Γ) (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) :
    holds σ ((Premise.done (C := C) (Γ := Γ) (Γ' := Γ) (m == .box)).fml m ω κ φ) →
      holds σ (.modal m (.cons .revert ω) κ φ) :=
  Premise.sound_done σ _ (fun h => ⟨by cases m <;> first | rfl | exact absurd h (by decide), .revert, rfl, by decide⟩) ω κ φ

/-- `localValueDeclInitDrop`: `⟨[ T v = e; ]⟩ ⇝ ⟨[ v = e; ]⟩`, `v` bound by
the hidden binder, `e` read under it. -/
theorem Stmt.step_sound_localValueDeclInitDrop {p : PrimTy} (x : Var) (e : Val C Γ p)
    (σ : State C Γ) (ω : Prog C (.val p :: Γ) Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.bind x (.val p) (.cons (.assignLocal .here e.up) .nil)).fml m ω κ φ) →
      holds σ (.modal m (.cons (.declLocal p x (some e)) ω) κ φ) := by
  refine Premise.sound_bind σ ⟨PrimTy.default p, LTy.BoolOK.default p, ?_⟩
    ω κ φ
  rw [Prog.run_cons]
  show Except.bind (Run.assignLocal (Γ := .val p :: Γ) .here e.up (σ.push (PrimTy.default p)))
      (fun τ => Prog.run τ .nil) = Run.declLocal p (some e) σ
  simp only [Run.assignLocal, Run.declLocal, Val.eval_up]
  cases e.eval σ <;> rfl

/-- `binopUnfoldLeft`: `⟨[ v = nse ⊕ e; ]⟩ ⇝ ⟨[ T se = nse; v = se ⊕ e; ]⟩`. -/
theorem Stmt.step_sound_binopUnfoldLeft {p p' : PrimTy} (k : Nat) (i : Idx Γ (.val p)) (op : BinOp)
    (ha : op.accepts p' = true) (hq : op.ret p' = p) (a b : Val C Γ p') (σ : State C Γ)
    (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.capture p' (fse k) a
      (.assignLocal i.there (.binop op ha hq (.simple (.local .here)) b.up))).fml m ω κ φ) →
      holds σ (.modal m (.cons (.assignLocal i (.binop op ha hq a b)) ω) κ φ) := by
  refine Premise.sound_capture σ (fun v hv => ?_) (fun h hh => ?_) ω κ φ
  · show (Run.assignLocal i.there _ (σ.push (t := .val p') v)).map _ = Run.assignLocal i _ σ
    have hv' : a.eval σ = pure v := hv
    simp only [Run.assignLocal, Val.eval, Simple.eval, Val.eval_up, hv', pure_bind]
    show Except.map _ (Except.bind (evalBinop op p' v (b.eval σ))
        fun x => pure ((σ.push (t := .val p') v).setLocal i.there x)) =
      Except.bind (evalBinop op p' v (b.eval σ)) fun x => pure (σ.setLocal i x)
    cases evalBinop op p' v (b.eval σ) <;> rfl
  · show Run.assignLocal i _ σ = _
    simp only [Run.assignLocal]
    show (do pure (σ.setLocal i (← (do evalBinop op p' (← a.eval σ) (b.eval σ))))) = _
    rw [hh]; rfl

/-- `unopCapture`: `⟨[ v = ⊖nse; ]⟩ ⇝ ⟨[ T se = nse; v = ⊖se; ]⟩`. -/
theorem Stmt.step_sound_unopCapture {p p' : PrimTy} (k : Nat) (i : Idx Γ (.val p)) (op : UnOp)
    (ha : op.accepts p' = true) (hq : op.ret p' = p) (a : Val C Γ p') (σ : State C Γ)
    (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.capture p' (fse k) a
      (.assignLocal i.there (.unop op ha hq (.simple (.local .here))))).fml m ω κ φ) →
      holds σ (.modal m (.cons (.assignLocal i (.unop op ha hq a)) ω) κ φ) := by
  refine Premise.sound_capture σ (fun v hv => ?_) (fun h hh => ?_) ω κ φ
  · show (Run.assignLocal i.there _ (σ.push (t := .val p') v)).map _ = Run.assignLocal i _ σ
    have hv' : a.eval σ = pure v := hv
    simp only [Run.assignLocal, Val.eval, Simple.eval, hv', pure_bind]
    show Except.map _ (Except.bind (Except.bind (applyUnOp op v) (unopCheck op p'))
        fun x => pure ((σ.push (t := .val p') v).setLocal i.there x)) =
      Except.bind (Except.bind (applyUnOp op v) (unopCheck op p')) fun x => pure (σ.setLocal i x)
    cases applyUnOp op v with
    | error => rfl
    | ok u =>
      show Except.map _ (Except.bind (unopCheck op p' u)
          fun x => pure ((σ.push (t := .val p') v).setLocal i.there x)) =
        Except.bind (unopCheck op p' u) fun x => pure (σ.setLocal i x)
      cases unopCheck op p' u <;> rfl
  · show Run.assignLocal i _ σ = _
    simp only [Run.assignLocal]
    show (do pure (σ.setLocal i (← (do unopCheck op p' (← applyUnOp op (← a.eval σ)))))) = _
    rw [hh]; rfl

/-- `requireConditionCapture`: `⟨[ require(nse); ]⟩ ⇝ ⟨[ bool se = nse; require(se); ]⟩`. -/
theorem Stmt.step_sound_requireConditionCapture (k : Nat) (c : Val C Γ .bool) (σ : State C Γ)
    (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.capture .bool (fse k) c (.require (.simple (.local .here)))).fml m ω κ φ) →
      holds σ (.modal m (.cons (.require c) ω) κ φ) := by
  refine Premise.sound_capture σ (fun v hv => ?_) (fun h hh => ?_) ω κ φ
  · show (do guardOk v (σ.push (t := .val .bool) v)).map _ = (do guardOk (← c.eval σ) σ)
    rw [hv]
    cases v with
    | bool b => cases b <;> rfl
    | int => rfl
  · show (do guardOk (← c.eval σ) σ) = _
    rw [hh]; rfl

/-- `assertConditionCapture`: `⟨[ assert(nse); ]⟩ ⇝ ⟨[ bool se = nse; assert(se); ]⟩`. -/
theorem Stmt.step_sound_assertConditionCapture (k : Nat) (c : Val C Γ .bool) (σ : State C Γ)
    (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.capture .bool (fse k) c (.assert (.simple (.local .here)))).fml m ω κ φ) →
      holds σ (.modal m (.cons (.assert c) ω) κ φ) := by
  refine Premise.sound_capture σ (fun v hv => ?_) (fun h hh => ?_) ω κ φ
  · show (do assertOk v (σ.push (t := .val .bool) v)).map _ = (do assertOk (← c.eval σ) σ)
    rw [hv]
    cases v with
    | bool b => cases b <;> rfl
    | int => rfl
  · show (do assertOk (← c.eval σ) σ) = _
    rw [hh]; rfl

/-- A simple value denotes what it evaluates to. -/
theorem Simple.denote_lower {p : PrimTy} (se : Simple C Γ p) (σ : State C Γ) {v : Value}
    (h : se.eval σ = .ok v) : se.lower.denote σ = .prim v := by
  cases se <;> cases h <;> rfl

/-- `se = b` holds where `se` evaluates to `b`. -/
theorem holds_isBool (se : Simple C Γ .bool) (σ : State C Γ) {v : Value}
    (h : se.eval σ = .ok v) (b : Bool) : holds σ (Fml.isBool se.lower b) ↔ v = .bool b := by
  show Theory.StValue.Equiv _ _ ↔ _
  rw [Simple.denote_lower se σ h]
  show Theory.StValue.Equiv (.prim v) (.prim (.bool b)) ↔ _
  rw [Theory.StValue.Equiv.prim_iff]
  exact ⟨fun h => by cases h; rfl, fun h => by rw [h]⟩

/-- `ifElseSplit`: `⟨[ if (se) thenStm else elseStm; ]⟩ ⇝ se = true ⟹ ⟨[ thenStm ]⟩ ;
se = false ⟹ ⟨[ elseStm ]⟩`, where `se` holds a `bool` (`hb`, M4a's typing). -/
theorem Stmt.step_sound_ifElseSplit {Δ₁ Δ₂ : Ctx} (se : Simple C Γ .bool) (thn : Prog C Γ Δ₁)
    (els : Prog C Γ Δ₂) (σ : State C Γ) (hb : ∃ b : Bool, se.eval σ = .ok (.bool b))
    (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.split .block (Fml.isBool se.lower true) (Fml.isBool se.lower false) thn
      els).fml m ω κ φ) → holds σ (.modal m (.cons (.ite (.simple se) thn els) ω) κ φ) := by
  obtain ⟨b, hb⟩ := hb
  refine Premise.sound_split σ (fun h => ?_) (fun h => ?_) ?_ ω κ φ
  · cases (holds_isBool se σ hb true).1 h
    show _ = Run.ite _ _ _ _ _ σ
    simp only [Run.ite, Val.eval, hb]; rfl
  · cases (holds_isBool se σ hb false).1 h
    show _ = Run.ite _ _ _ _ _ σ
    simp only [Run.ite, Val.eval, hb]; rfl
  · cases b
    · exact .inr ((holds_isBool se σ hb false).2 rfl)
    · exact .inl ((holds_isBool se σ hb true).2 rfl)

/-- `requireSimple`: `⟨[ require(se); ]⟩ ⇝ se = true ⟹ ⟨[ ]⟩ ; se = false ⟹ ⟨[ revert(); ]⟩`,
where `se` holds a `bool` (`hb`). -/
theorem Stmt.step_sound_requireSimple (se : Simple C Γ .bool) (σ : State C Γ)
    (hb : ∃ b : Bool, se.eval σ = .ok (.bool b)) (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) :
    holds σ ((Premise.split .capture (Fml.isBool se.lower true) (Fml.isBool se.lower false) .nil
      (.cons .revert .nil)).fml m ω κ φ) → holds σ (.modal m (.cons (.require (.simple se)) ω) κ φ) := by
  obtain ⟨b, hb⟩ := hb
  refine Premise.sound_split σ (fun h => ?_) (fun h => ?_) ?_ ω κ φ
  · cases (holds_isBool se σ hb true).1 h
    show _ = (do guardOk (← (Val.simple se).eval σ) σ)
    simp only [Val.eval, hb]; rfl
  · cases (holds_isBool se σ hb false).1 h
    show _ = (do guardOk (← (Val.simple se).eval σ) σ)
    simp only [Val.eval, hb]; rfl
  · cases b
    · exact .inr ((holds_isBool se σ hb false).2 rfl)
    · exact .inl ((holds_isBool se σ hb true).2 rfl)

/-- `assertSimple`: `⟨[ assert(se); ]⟩ ⇝ se = true ⟹ ⟨[ ]⟩ ; se = true`. -/
theorem Stmt.step_sound_assertSimple (se : Simple C Γ .bool) (σ : State C Γ) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.check (Fml.isBool se.lower true)).fml m ω κ φ) →
      holds σ (.modal m (.cons (.assert (.simple se)) ω) κ φ) := by
  refine Premise.sound_check σ (fun h => ?_) ω κ φ
  obtain ⟨v, hv⟩ : ∃ v, se.eval σ = .ok v := by cases se <;> exact ⟨_, rfl⟩
  cases (holds_isBool se σ hv true).1 h
  show (do assertOk (← (Val.simple se).eval σ) σ) = _
  simp only [Val.eval, hv]; rfl

/-- A block, its locals popped after it: `⟨[ { body } ]⟩ ⇝ ⟨[ body ]⟩`. -/
theorem Stmt.step_sound_block {Γ₂ : Ctx} (body : Prog C Γ Γ₂) (σ : State C Γ) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    holds σ ((Premise.unfold body body.ext).fml m ω κ φ) →
      holds σ (.modal m (.cons (.block body) ω) κ φ) :=
  Premise.sound_unfold σ rfl ω κ φ

end Rules

end Solidity.Core
