import Solidity.Calculus.CallFunctionOperationalBase
import Solidity.Calculus.CallResultRestore

/-! # Complete intrinsic call-table family leaves
Fresh logical function/result locals are discarded before the caller post.
Definitions and terminal obligations are ordinary existing intrinsic formulas.
-/
namespace Solidity.CallFunctionLeaf
open CallFunctionTable CallFunctionGraph
variable {C : Contract} {Γ Δ : Ctx}

/-- Ordinary nonreturn has precisely the original modality observation. -/
def haltPost (m : Modality) : Fml C Δ :=
  match m with
  | .box => .tt
  | .diamond => .not .tt

theorem holds_haltPost (m : Modality) (τ : State C Δ) :
    holds τ (haltPost m) ↔ m.onHalt := by
  cases m with
  | box => rfl
  | diamond =>
    change (¬ True) ↔ False
    exact not_true

/-- A fresh result local is selected by its exact table code, copied to
an old target, then every logical local is dropped before the original post. -/
def terminal (m : Modality) (resultName : Var) (h : Ext Γ Δ)
    (j : Idx Γ (.val .uint)) (fn : Idx Δ .oldNet) (x : Idx Δ (.val .uint))
    (φ : Fml C Γ) : Fml C Δ :=
  .and
    (.imp (equalZ (.netOf fn (.pvV x)) (.app0 (.zlit (-1)))) (haltPost m))
    (.all resultName .uint
      (.imp (equalZ (.netOf fn.there (.pvV x.there)) (.app1 .toInt (.pvV .here)))
        (.upd m (CallResultRestore.copyDrop (.push h) j .here) φ)))

/-- Every intrinsic guard and the caller-restoration update has its exact
state interpretation, including modal continuations in the old context. -/
theorem holds_terminal_shape (m : Modality) (resultName : Var) (h : Ext Γ Δ)
    (j : Idx Γ (.val .uint)) (fn : Idx Δ .oldNet) (x : Idx Δ (.val .uint))
    (φ : Fml C Γ) (τ : State C Δ) :
    holds τ (terminal m resultName h j fn x φ) ↔
      ((TEnv.get fn τ.env).at (τ.getV x) = -1 → m.onHalt) ∧
      (∀ r : Key, (TEnv.get fn τ.env).at (τ.getV x) = r.val →
        holds ((τ.drop h).setLocal j r) φ) := by
  change (holds τ (equalZ (.netOf fn (.pvV x)) (.app0 (.zlit (-1)))) →
      holds τ (haltPost m)) ∧
    (∀ r : Key, holds (τ.push (t := .val .uint) r)
      (equalZ (.netOf fn.there (.pvV x.there)) (.app1 .toInt (.pvV .here))) →
      holds (τ.push (t := .val .uint) r)
        (.upd m (CallResultRestore.copyDrop (.push h) j .here) φ)) ↔ _
  simp only [CallResultRestore.holds_copyDrop, holds_haltPost]
  change (((some (decide ((TEnv.get fn τ.env).at (τ.getV x) = -1)) : Option Bool) =
      some true → m.onHalt) ∧
    (∀ r : Key, (some (decide ((TEnv.get fn τ.env).at (τ.getV x) = r.val)) : Option Bool) =
      some true → holds ((τ.drop h).setLocal j r) φ)) ↔ _
  simp only [Option.some.injEq, decide_eq_true_eq]

/-- The observable result of an operational partial function. Exhaustion
is excluded only by internally established producer no-push certificates. -/
def afterOption (m : Modality) (o : Option Key) (P : Key → Prop) : Prop :=
  match o with
  | none => m.onHalt
  | some r => P r

/-- A represented function determines exactly the old-context observation.
Representation is discharged from actual definition clauses by the producer. -/
theorem holds_terminal (m : Modality) (resultName : Var) (h : Ext Γ Δ)
    (j : Idx Γ (.val .uint)) (fn : Idx Δ .oldNet) (x : Idx Δ (.val .uint))
    (φ : Fml C Γ) (τ : State C Δ) (f : Key → Option Key)
    (hf : Represents (TEnv.get fn τ.env) f) :
    holds τ (terminal m resultName h j fn x φ) ↔
      afterOption m (f (τ.getV x)) (fun r => holds ((τ.drop h).setLocal j r) φ) := by
  rw [holds_terminal_shape]
  have hfail : (TEnv.get fn τ.env).at (τ.getV x) = -1 ↔ f (τ.getV x) = none :=
    failure_iff hf (τ.getV x)
  have hreturn (r : Key) : (TEnv.get fn τ.env).at (τ.getV x) = r.val ↔
      f (τ.getV x) = some r := returns_iff hf (τ.getV x) r
  simp only [hfail, hreturn]
  cases he : f (τ.getV x) with
  | none =>
    simp only [afterOption, reduceCtorEq, false_implies, true_implies]
    exact ⟨And.left, fun hp => ⟨hp, fun _ => trivial⟩⟩
  | some r => simp only [afterOption, reduceCtorEq, Option.some.injEq, false_implies,
      true_and, forall_eq']

/-- Complete terminal formula size, counting the fresh result binder,
all guards, the copy/drop update and the old continuation exactly once. -/
theorem terminal_size (m : Modality) (resultName : Var) (h : Ext Γ Δ)
    (j : Idx Γ (.val .uint)) (fn : Idx Δ .oldNet) (x : Idx Δ (.val .uint))
    (φ : Fml C Γ) :
    (terminal m resultName h j fn x φ).tmSize = φ.tmSize + 20 + (haltPost (C := C) (Δ := Δ) m).tmSize := by
  simp only [terminal, equalZ, Fml.tmSize, CallResultRestore.copyDrop, Upd.tmSize,
    UpdElem.size, Rhs.size, Tm.size]
  omega

/-- Doubling call composition retains failure before the second application. -/
def power (f : Key → Option Key) : Nat → Key → Option Key
  | 0 => f
  | k+1 => power (fun x => (f x).bind f) k

/-- The source-shaped doubling equation, retaining evaluation order. -/
theorem power_succ (f : Key → Option Key) (k : Nat) (x : Key) :
    power f (k+1) x = (power f k x).bind (power f k) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => exact ih (fun a => (f a).bind f)

/-- Each stage introduces one actual oldNet local and one composition clause.
Every recursive continuation is typed under precisely that new local. -/
def stages (m : Modality) (inputName resultName : Var)
    (j : Idx Γ (.val .uint)) (φ : Fml C Γ) :
    (k : Nat) → {Δ : Ctx} → Ext Γ Δ → Idx Δ .oldNet → Idx Δ (.val .uint) → Fml C Δ
  | 0, _, h, fn, x => terminal m resultName h j fn x φ
  | k+1, _, h, fn, x =>
    .bind m inputName .oldNet
      (.imp (compose inputName resultName fn.there fn.there .here)
        (stages m inputName resultName j φ k (.push h) .here x.there))

/-- Universal definition binders are inhabited: the forward direction picks
an actually represented composition, ruling out vacuous definition premises. -/
theorem holds_stages (m : Modality) (inputName resultName : Var)
    (j : Idx Γ (.val .uint)) (φ : Fml C Γ) (k : Nat)
    (h : Ext Γ Δ) (fn : Idx Δ .oldNet) (x : Idx Δ (.val .uint))
    (τ : State C Δ) (f : Key → Option Key) (hf : Represents (TEnv.get fn τ.env) f) :
    holds τ (stages m inputName resultName j φ k h fn x) ↔
      afterOption m (power f k (τ.getV x))
        (fun r => holds ((τ.drop h).setLocal j r) φ) := by
  induction k generalizing Δ f with
  | zero => exact holds_terminal m resultName h j fn x φ τ f hf
  | succ k ih =>
    change (∀ L : Ledger,
      holds (τ.push (t := .oldNet) L) (compose inputName resultName fn.there fn.there .here) →
      holds (τ.push (t := .oldNet) L)
        (stages m inputName resultName j φ k (.push h) .here x.there)) ↔ _
    constructor
    · intro hh
      obtain ⟨L, hL⟩ := exists_represents (fun a => (f a).bind f)
      have hc : holds (τ.push (t := .oldNet) L)
          (compose inputName resultName fn.there fn.there .here) :=
        (holds_compose inputName resultName fn.there fn.there .here _).mpr
          ((squares_iff hf).mpr hL)
      exact (ih (.push h) .here x.there (τ.push (t := .oldNet) L) _ hL).mp (hh L hc)
    · intro hp L hc
      have hL : Represents L (fun a => (f a).bind f) :=
        (squares_iff hf).mp
          ((holds_compose inputName resultName fn.there fn.there .here _).mp hc)
      exact (ih (.push h) .here x.there (τ.push (t := .oldNet) L) _ hL).mpr hp

/-- All stage clauses/binders and the unchanged terminal/post are counted. -/
theorem stages_size (m : Modality) (inputName resultName : Var)
    (j : Idx Γ (.val .uint)) (φ : Fml C Γ) (k : Nat)
    (h : Ext Γ Δ) (fn : Idx Δ .oldNet) (x : Idx Δ (.val .uint)) :
    (stages m inputName resultName j φ k h fn x).tmSize =
      φ.tmSize + 33*k + 20 + (haltPost (C := C) (Δ := Γ) m).tmSize := by
  induction k generalizing Δ with
  | zero =>
    cases m <;> simp only [stages, terminal_size, haltPost, Fml.tmSize, Nat.mul_zero,
      Nat.add_zero]
  | succ k ih =>
    simp only [stages, Fml.tmSize, compose_size, ih]
    omega

/-- A complete call-family leaf: an operational base definition, all actual
composition definitions, one fresh result selection and exact caller restore. -/
def leaf (m : Modality) (tableName inputName resultName : Var)
    (t : Tm C (.val .uint :: Γ) (.val .uint)) (k : Nat)
    (j x : Idx Γ (.val .uint)) (φ : Fml C Γ) : Fml C Γ :=
  .bind m tableName .oldNet
    (.imp (CallFunctionOperationalBase.clause inputName resultName t)
      (stages m inputName resultName j φ k (.push .refl) .here x.there))

/-- Complete leaf semantics follow from actual operational definition models.
The existing no-push certificate is an internal producer fact, not a user premise. -/
theorem holds_leaf (m : Modality) (tableName inputName resultName : Var)
    (t : Tm C (.val .uint :: Γ) (.val .uint)) (hp : t.pushFree = true) (k : Nat)
    (j x : Idx Γ (.val .uint)) (φ : Fml C Γ) (σ : State C Γ) :
    holds σ (leaf m tableName inputName resultName t k j x φ) ↔
      afterOption m (power (fun a => t.eval (σ.push (t := .val .uint) a)) k (σ.getV x))
        (fun r => holds (σ.setLocal j r) φ) := by
  change (∀ L : Ledger,
    holds (σ.push (t := .oldNet) L) (CallFunctionOperationalBase.clause inputName resultName t) →
    holds (σ.push (t := .oldNet) L)
      (stages m inputName resultName j φ k (.push .refl) .here x.there)) ↔ _
  constructor
  · intro hh
    obtain ⟨L, hL⟩ := CallFunctionOperationalBase.satisfiable inputName resultName t hp σ
    have hr : Represents L (fun a => t.eval (σ.push (t := .val .uint) a)) :=
      (CallFunctionOperationalBase.holds_clause inputName resultName t hp σ L).mp hL
    exact (holds_stages m inputName resultName j φ k (.push .refl) .here x.there
      (σ.push (t := .oldNet) L) _ hr).mp (hh L hL)
  · intro hs L hL
    have hr : Represents L (fun a => t.eval (σ.push (t := .val .uint) a)) :=
      (CallFunctionOperationalBase.holds_clause inputName resultName t hp σ L).mp hL
    exact (holds_stages m inputName resultName j φ k (.push .refl) .here x.there
      (σ.push (t := .oldNet) L) _ hr).mpr hs

/-- Full emitted leaf size includes the operational base, all function-table
binders and definitions, result binder, copy/drop and caller post. -/
theorem leaf_size (m : Modality) (tableName inputName resultName : Var)
    (t : Tm C (.val .uint :: Γ) (.val .uint)) (k : Nat)
    (j x : Idx Γ (.val .uint)) (φ : Fml C Γ) :
    (leaf m tableName inputName resultName t k j x φ).tmSize =
      2*t.size + φ.tmSize + 33*k + 44 + (haltPost (C := C) (Δ := Γ) m).tmSize := by
  simp only [leaf, Fml.tmSize, CallFunctionOperationalBase.clause_size, stages_size]
  omega

end Solidity.CallFunctionLeaf
