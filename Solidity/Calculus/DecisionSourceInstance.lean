import Solidity.Calculus.AllLeft
import Solidity.Calculus.HashPremise
import Solidity.Calculus.MemStructCut

/-! # Actual intrinsic source literal instances
Reuse the existing update/substitution certificate before leaf translation.
This does not yet add a global decision route.
-/
namespace Solidity.Decide

/-- The source guard on the innermost unsigned binder. -/
def sourceUIntBelow {C : Contract} {Γ : Ctx} (bound : PrimTy.uint.Denote) :
    Fml C (.val .uint :: Γ) :=
  .eq (.app2 (.binop .lt (p := .uint) rfl) (.pvV .here) (.app0 (.lit bound)))
    (.app0 (.lit true))

/-- The literal satisfies the actual typed source guard in every starting state. -/
theorem sourceUIntBelow_holds {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (bound value : PrimTy.uint.Denote) (hv : value.1 < bound.1) :
    holds (σ.push (t := .val .uint) value) (sourceUIntBelow bound) := by
  change (some (decide (value.1 < bound.1)) : Option Bool) = some true
  simp only [hv, decide_true]

/-- A computed intrinsic substitution proves the literal instance, with no
restriction on partial storage/memory observations in the body. -/
theorem sourceUInt_literal_instance_valid {C : Contract} {Γ : Ctx}
    (x : Var) (bound value : PrimTy.uint.Denote)
    (body : Fml C (.val .uint :: Γ)) (rhs : Fml C Γ)
    (hv : value.1 < bound.1) (hi : Fml.instLit x .uint body value = some rhs) :
    ∀ σ : State C Γ,
      holds σ (.imp (.all x .uint (.imp (sourceUIntBelow bound) body)) rhs) := by
  intro σ hall
  have hg : holds (σ.push (t := .val .uint) value) (sourceUIntBelow bound) :=
    sourceUIntBelow_holds σ bound value hv
  exact (Fml.substU_holds
    (Upd.lands_decl (Upd.lands_nil σ) x
      (r := .val (.app0 (.lit value))) (v := value) rfl) body hi).2 (hall value hg)

/-- Full primitive equation comparison using the existing typed term comparison. -/
def sourceEquationSame? {C : Contract} {Γ : Ctx} (a b : Fml C Γ) :
    Option (PLift (a = b)) := do
  let ⟨p, xa, xb, hx⟩ ← MemoryWitness.eqView a
  let ⟨q, ya, yb, hy⟩ ← MemoryWitness.eqView b
  if hp : p = q then
    if ha : (hp ▸ xa).beqR ya = true then
      if hb : (hp ▸ xb).beqR yb = true then
        some ⟨by
          cases hp
          exact hx.trans ((congr (congrArg Fml.eq (Tm.eq_of_beqR ha))
            (Tm.eq_of_beqR hb)).trans hy.symm)⟩
      else none
    else none
  else none

/-- An actual bounded universal source and its computed literal instance.
The body can include intrinsically typed storage/memory terms not translated
by the leaf compiler. Bound and literal are explicit classification parameters. -/
structure SourceUIntLiteralInstance {C : Contract} {Γ : Ctx}
    (φ : Fml C Γ) (bound value : PrimTy.uint.Denote) where
  name : Var
  body : Fml C (.val .uint :: Γ)
  prim : PrimTy
  lhs : Tm C Γ (.val prim)
  rhs : Tm C Γ (.val prim)
  inside : value.1 < bound.1
  instanceEq : Fml.instLit name .uint body value = some (.eq lhs rhs)
  equation : φ = .imp (.all name .uint (.imp (sourceUIntBelow bound) body)) (.eq lhs rhs)

structure SourceImpView {C : Contract} {Γ : Ctx} (φ : Fml C Γ) where
  lhs : Fml C Γ
  rhs : Fml C Γ
  equation : φ = .imp lhs rhs

/-- Constructor dispatch generalizes the intrinsic context index. -/
def sourceImpView? {C : Contract} {Γ : Ctx} (φ : Fml C Γ) : Option (SourceImpView φ) := by
  apply @Fml.casesOn C (fun Γ φ => Option (SourceImpView φ)) Γ φ
  case imp => intro Γ lhs rhs; exact some ⟨lhs, rhs, rfl⟩
  all_goals intros; exact none

structure SourceUIntAllView {C : Contract} {Γ : Ctx} (φ : Fml C Γ) where
  name : Var
  body : Fml C (.val .uint :: Γ)
  equation : φ = .all name .uint body

def sourceUIntAllView? {C : Contract} {Γ : Ctx} (φ : Fml C Γ) :
    Option (SourceUIntAllView φ) := by
  apply @Fml.casesOn C (fun Γ φ => Option (SourceUIntAllView φ)) Γ φ
  case all =>
    intro Γ name prim body
    exact if hp : prim = .uint then
      some ⟨name, hp ▸ body, by cases hp; rfl⟩ else none
  all_goals intros; exact none

/-- Recognition checks full source syntax and actual existing substitution. -/
def sourceUIntLiteralInstance? {C : Contract} {Γ : Ctx} (φ : Fml C Γ)
    (bound value : PrimTy.uint.Denote) : Option (SourceUIntLiteralInstance φ bound value) := do
  let outer ← sourceImpView? φ
  let all ← sourceUIntAllView? outer.lhs
  let inner ← sourceImpView? all.body
  if hv : value.1 < bound.1 then
    let ⟨hg⟩ ← sourceEquationSame? inner.lhs (sourceUIntBelow bound)
    match hi : Fml.instLit all.name .uint inner.rhs value with
    | none => none
    | some inst => do
      let ⟨he⟩ ← sourceEquationSame? inst outer.rhs
      let r ← MemoryWitness.eqView outer.rhs
      return ⟨all.name, inner.rhs, r.p, r.a, r.b, hv,
        hi.trans (congrArg some (he.trans r.eqn)),
        outer.equation.trans (congr (congrArg Fml.imp
          (all.equation.trans (congrArg (Fml.all all.name .uint)
            (inner.equation.trans (congrArg (fun g => Fml.imp g inner.rhs) hg))))) r.eqn)⟩
  else none

/-- Recognized source instances are valid in every actual typed state. -/
theorem SourceUIntLiteralInstance.valid {C : Contract} {Γ : Ctx}
    {φ : Fml C Γ} {bound value : PrimTy.uint.Denote}
    (w : SourceUIntLiteralInstance φ bound value) : ∀ σ : State C Γ, holds σ φ := by
  rw [w.equation]
  exact sourceUInt_literal_instance_valid w.name bound value w.body (.eq w.lhs w.rhs)
    w.inside w.instanceEq

/-- The existing hash-premised reading follows only with explicit hash freedom. -/
theorem SourceUIntLiteralInstance.validH {C : Contract} {φ : Fml C []}
    {bound value : PrimTy.uint.Denote} (w : SourceUIntLiteralInstance φ bound value)
    (hh : φ.hasHash = false) : Fml.ValidH φ :=
  Fml.validH_iff hh |>.mpr w.valid

/-- Reflexivity is proved for the actual typed equation comparator. -/
theorem sourceEquationSame_self {C : Contract} {Γ : Ctx} {p : PrimTy}
    (a b : Tm C Γ (.val p)) : sourceEquationSame? (.eq a b) (.eq a b) = some ⟨rfl⟩ := by
  simp only [sourceEquationSame?, MemoryWitness.eqView, Option.bind_eq_bind,
    Option.bind_some, Tm.beqR_self, dif_pos True.intro]

/-- Every member of this exact source family is recognized at its stated parameters. -/
theorem sourceUIntLiteralInstance_complete {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} (w : SourceUIntLiteralInstance φ bound value) :
    (sourceUIntLiteralInstance? φ bound value).isSome = true := by
  rcases w with ⟨x, body, p, a, b, hv, hi, hφ⟩
  subst φ
  simp only [sourceUIntLiteralInstance?, sourceImpView?, sourceUIntAllView?,
    dif_pos True.intro, dif_pos hv, sourceUIntBelow,
    sourceEquationSame_self, Option.bind_eq_bind, Option.bind_some,
    MemoryWitness.eqView, Option.pure_def]
  split
  · rename_i he
    rw [hi] at he
    cases he
  · rename_i inst he
    have heq : inst = .eq a b := Option.some.inj (he.symm.trans hi)
    subst inst
    simp only [sourceEquationSame_self, Option.bind_some, Option.isSome_some]

/-- Decidable source syntax at supplied arithmetic parameters, not a verdict query. -/
def _root_.Solidity.Fml.sourceUIntLiteralInstance {C : Contract} {Γ : Ctx}
    (φ : Fml C Γ) (bound value : PrimTy.uint.Denote) : Bool :=
  (sourceUIntLiteralInstance? φ bound value).isSome

theorem sourceUIntLiteralInstance_witness {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} (h : φ.sourceUIntLiteralInstance bound value = true) :
    Nonempty (SourceUIntLiteralInstance φ bound value) := by
  unfold Fml.sourceUIntLiteralInstance at h
  cases he : sourceUIntLiteralInstance? φ bound value with
  | none => rw [he] at h; cases h
  | some w => exact ⟨w⟩

theorem sourceUIntLiteralInstance_iff {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} :
    φ.sourceUIntLiteralInstance bound value = true ↔ Nonempty (SourceUIntLiteralInstance φ bound value) :=
  ⟨sourceUIntLiteralInstance_witness, fun ⟨w⟩ => sourceUIntLiteralInstance_complete w⟩

instance sourceUIntLiteralInstance_decidable {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} : Decidable (Nonempty (SourceUIntLiteralInstance φ bound value)) :=
  if h : φ.sourceUIntLiteralInstance bound value = true then
    isTrue (sourceUIntLiteralInstance_witness h)
  else isFalse (fun w => h (sourceUIntLiteralInstance_iff.mpr w))

/-- A prefix of original primitive universal binders, followed by an actual
source literal instance. No translated leaf or future producer is assumed. -/
inductive SourceUIntLiteralChain {C : Contract} (bound value : PrimTy.uint.Denote) :
    {Γ : Ctx} → Fml C Γ → Type
  | leaf {Γ : Ctx} {φ : Fml C Γ} : SourceUIntLiteralInstance φ bound value →
      SourceUIntLiteralChain bound value φ
  | all {Γ : Ctx} (name : Var) (prim : PrimTy) {body : Fml C (.val prim :: Γ)} :
      SourceUIntLiteralChain bound value body →
      SourceUIntLiteralChain bound value (.all name prim body)

/-- Structural source traversal, without an added fuel or search budget. -/
def sourceUIntLiteralChain? {C : Contract} {Γ : Ctx} (φ : Fml C Γ)
    (bound value : PrimTy.uint.Denote) : Option (SourceUIntLiteralChain bound value φ) :=
  by
    apply @Fml.casesOn C (fun Γ φ => Option (SourceUIntLiteralChain bound value φ)) Γ φ
    case all =>
      intro Γ name prim body
      exact (sourceUIntLiteralChain? body bound value).map (.all name prim)
    all_goals intros; exact (sourceUIntLiteralInstance? _ bound value).map .leaf
termination_by structural φ

theorem SourceUIntLiteralChain.valid {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} (w : SourceUIntLiteralChain bound value φ) :
    ∀ σ : State C Γ, holds σ φ := by
  induction w with
  | leaf w => exact w.valid
  | all name prim w ih => intro σ v; exact ih (σ.push (t := .val prim) v)

theorem SourceUIntLiteralChain.validH {C : Contract} {φ : Fml C []}
    {bound value : PrimTy.uint.Denote} (w : SourceUIntLiteralChain bound value φ)
    (hh : φ.hasHash = false) : Fml.ValidH φ :=
  Fml.validH_iff hh |>.mpr w.valid

end Solidity.Decide
