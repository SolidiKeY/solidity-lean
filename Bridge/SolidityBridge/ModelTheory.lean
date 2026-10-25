import Solidity.Calculus.Sound
import Solidity.Calculus.FirstOrder
import Mathlib.ModelTheory.Satisfiability

/-!
# The Theory as a first-order structure

The terms of the calculus (`Tm C Γ s`, `Calculus/Fml.lean`) are built from
the symbols `Op0`…`Op3` of `Signature.lean`, sorted by `Srt`; the formulas'
first-order fragment (`Fml.FO`: `true`, `=`, `wt`, `¬`, `∧`, `→`, `∀`) reads
them by `Tm.denote` (`Calculus/Lands.lean`).  This module makes that Mathlib's
model theory:

* `FO.lang C`, a `FirstOrder.Language`: the symbols of every arity, the
  ledger lookup `x[a]`, and the relations `=` at a value type, `wt` and
  "is a value of type `p`";
* `FO.Carrier C g`, its `Structure` in the global part `g` of a state: a
  sort-tagged reading, the Theory's denotation beside the typed evaluation
  (some symbols read both, `Op2.denote`), or a ledger.  Mathlib's logic is
  one-sorted, so the sorts are tags: a symbol applied to arguments of other
  sorts returns its first argument, and `∀ p x` is relativised to the
  values of `p`;
* `Tm.toTerm` and `Fml.toBF`, the translation, defined exactly on the
  first-order fragment (`Fml.toBF_isSome`), with a local of `Γ` a bound
  variable;
* `Tm.realize_toTerm` and `Fml.realize_toBF`: **a term realizes as it
  denotes, a formula as it holds**;
* `FO.SolTheory C`, the sentences every state satisfies, the intersection of
  the states' complete theories, satisfiable and closed under Mathlib's
  semantic consequence; a valid first-order formula is a member
  (`FO.valid_iff_mem`), so is everything the calculus proves
  (`Proves.mem_solTheory`).
-/

namespace Solidity

namespace FO

open FirstOrder FirstOrder.Language

variable {C : Contract}

/-! ## The language -/

/-- The function symbols by arity: `Op0`…`Op3` with their sorts, and the
ledger lookup `x[a]` (`Tm.netOf`), binary. -/
def Fn (C : Contract) : ℕ → Type
  | 0 => (s : Srt) × Op0 C s
  | 1 => (a : Srt) × (s : Srt) × Op1 C a s
  | 2 => ((a : Srt) × (b : Srt) × (s : Srt) × Op2 C a b s) ⊕ Unit
  | 3 => (a : Srt) × (b : Srt) × (c : Srt) × (s : Srt) × Op3 C a b c s
  | _ + 4 => Empty

/-- The unary relations: `wt(s)`, and "is a value of type `p`", the sort a
binder ranges over. -/
inductive Rel1 where
  | wt
  | val (p : PrimTy)

/-- The relation symbols by arity: the unary ones, and `=` at a value
type. -/
def Rl : ℕ → Type
  | 0 => Empty
  | 1 => Rel1
  | 2 => PrimTy
  | _ + 3 => Empty

/-- **The language of the Theory**. -/
def lang (C : Contract) : Language.{0, 0} := ⟨Fn C, Rl⟩

/-! ## The structure of a state -/

/-- A sort's reading: its denotation in the Theory, beside its typed
evaluation (`none` where it reverts). -/
abbrev Rd (g : State C []) (s : Srt) : Type := s.TDen C × Option (s.Den C g.H)

/-- **The universe of a state's structure**: a reading tagged by its sort,
or a ledger (what an `oldNet` local holds). -/
def Carrier (C : Contract) (g : State C []) : Type := ((s : Srt) × Rd g s) ⊕ Ledger

variable {g : State C []}

/-- A reading tagged by its sort. -/
def Carrier.mk (s : Srt) (r : Rd g s) : Carrier C g := .inl ⟨s, r⟩

/-- The reading at the sort `s`, if the element is tagged by it. -/
def Carrier.as (s : Srt) : Carrier C g → Option (Rd g s)
  | .inl ⟨s', r⟩ => if h : s' = s then some (h ▸ r) else none
  | .inr _ => none

@[simp] theorem Carrier.as_mk (s : Srt) (r : Rd g s) : (Carrier.mk s r).as s = some r := by
  simp only [Carrier.as, Carrier.mk, ↓reduceDIte]

instance : Nonempty (Carrier C g) := ⟨.inr []⟩

/-- The symbols' interpretation in the global part `g`: a symbol reads its
arguments at its sorts by `OpN.denote` and `OpN.eval`; ill-sorted, it
returns its first argument. -/
noncomputable def funMap (g : State C []) : {n : ℕ} → Fn C n → (Fin n → Carrier C g) → Carrier C g
  | 0, ⟨s, o⟩, _ => .mk s (o.denote g, o.eval g)
  | 1, ⟨a, s, o⟩, xs => match (xs 0).as a with
    | some (d, e) => .mk s (o.denote g d, o.eval g e)
    | none => xs 0
  | 2, .inl ⟨a, b, s, o⟩, xs => match (xs 0).as a, (xs 1).as b with
    | some (d, e), some (d', e') => .mk s (o.denote g e e' d d', o.eval g e e')
    | _, _ => xs 0
  | 2, .inr (), xs => match xs 0, (xs 1).as (.val .uint) with
    | .inr l, some (d, e) =>
      .mk .kint (d.map fun n => (Semantics.lookupBy n l).getD 0, e.bind (Tm.netOfT l))
    | _, _ => xs 0
  | 3, ⟨a, b, c, s, o⟩, xs => match (xs 0).as a, (xs 1).as b, (xs 2).as c with
    | some (d, e), some (d', e'), some (d'', e'') =>
      .mk s (o.denote d d' d'', o.eval g e e' e'')
    | _, _, _ => xs 0
  | _ + 4, f, _ => nomatch f

/-- The relations' interpretation: `wt` where the storage evaluates to a
well-typed one, `val p` on the values of `p`, `=` of two denotations. -/
def relMap : {n : ℕ} → Rl n → (Fin n → Carrier C g) → Prop
  | 0, r, _ => nomatch r
  | 1, .wt, xs => match (xs 0).as .st with
    | some (_, e) => ∃ st, e = some st ∧ st.wtB = true
    | none => False
  | 1, .val p, xs => ∃ v : p.Denote, xs 0 = .mk (.val p) (some v, some v)
  | 2, p, xs => match (xs 0).as (.val p), (xs 1).as (.val p) with
    | some r, some r' => r.1 = r'.1
    | _, _ => False
  | _ + 3, r, _ => nomatch r

/-- **The structure of the global part `g`**. -/
noncomputable instance stateStructure (g : State C []) : (lang C).Structure (Carrier C g) where
  funMap := funMap g
  RelMap := relMap

/-! ## Locals as variables -/

/-- What a local of type `t` holds, as an element: its reading as a term
of its sort reads it (`Tm.pvV`, `Tm.pvP`, …), a ledger as itself. -/
def LTy.elt (g : State C []) : (t : LTy) → t.TDenote C g.H → Carrier C g
  | .val p, v => .mk (.val p) (some v, some v)
  | .alias R, a => .mk (.path (.ref R)) ((match a with
      | some r => .ref r
      | none => .dangling _ .nil), a)
  | .mem R, r => .mk (.ident R) ((), r.map (·.id))
  | .old, st => .mk .st (Storage.obs st, some st)
  | .oldNet, l => .inr l
  | .kint, n => .mk .kint (some n, some n)

/-- A position as a bound variable: the innermost local is the last one
Mathlib bound, `∀'` binding at the end. -/
def Idx.pos : {Γ : Ctx} → {t : LTy} → Idx Γ t → Fin Γ.length
  | _, _, .here => Fin.last _
  | _, _, .there i => (Idx.pos i).castSucc

/-- The locals as the bound variables' values. -/
def envVal (g : State C []) : (Γ : Ctx) → TEnv C g.H Γ → Fin Γ.length → Carrier C g
  | [], _ => Fin.elim0
  | t :: Γ, e => Fin.snoc (α := fun _ => Carrier C g) (envVal g Γ e.2) (LTy.elt g t e.1)

theorem envVal_pos {Γ : Ctx} {t : LTy} (e : TEnv C g.H Γ) (i : Idx Γ t) :
    envVal g Γ e (Idx.pos i) = LTy.elt g t (TEnv.get i e) := by
  induction i with
  | here => simp only [envVal, Idx.pos, Fin.snoc_last]; rfl
  | there i ih => simp only [envVal, Idx.pos, Fin.snoc_castSucc]; exact ih e.2

/-- The valuation of a state's locals. -/
abbrev val {Γ : Ctx} (σ : State C Γ) : Fin Γ.length → Carrier C σ.glob := envVal σ.glob Γ σ.env

/-! ## Terms -/

variable {Γ : Ctx}

/-- **A term of the calculus as a Mathlib term**, its locals bound
variables. -/
def _root_.Solidity.Tm.toTerm : {s : Srt} → Tm C Γ s → (lang C).Term (Empty ⊕ Fin Γ.length)
  | _, .pvV i => .var (.inr (Idx.pos i))
  | _, .pvP i => .var (.inr (Idx.pos i))
  | _, .pvS i => .var (.inr (Idx.pos i))
  | _, .pvI i => .var (.inr (Idx.pos i))
  | _, .pvZ i => .var (.inr (Idx.pos i))
  | _, .netOf i a =>
    .func (l := 2) (show Fn C 2 from .inr ()) ![.var (.inr (Idx.pos i)), a.toTerm]
  | s, .app0 o => .func (l := 0) (show Fn C 0 from ⟨s, o⟩) ![]
  | s, .app1 (a := a) o x => .func (l := 1) (show Fn C 1 from ⟨a, s, o⟩) ![x.toTerm]
  | s, .app2 (a := a) (b := b) o x y =>
    .func (l := 2) (show Fn C 2 from .inl ⟨a, b, s, o⟩) ![x.toTerm, y.toTerm]
  | s, .app3 (a := a) (b := b) (c := c) o x y z =>
    .func (l := 3) (show Fn C 3 from ⟨a, b, c, s, o⟩) ![x.toTerm, y.toTerm, z.toTerm]

/-- **A term realizes as it denotes and evaluates.** -/
theorem _root_.Solidity.Tm.realize_toTerm (σ : State C Γ) (v : Empty → Carrier C σ.glob) :
    {s : Srt} → (t : Tm C Γ s) →
      t.toTerm.realize (Sum.elim v (val σ)) = .mk s (t.denote σ, t.eval σ)
  | _, .pvV i => (envVal_pos (g := σ.glob) σ.env i).trans rfl
  | _, .pvP i => by
    simp only [Tm.toTerm, Term.realize, Sum.elim_inr]
    rw [show val σ (Idx.pos i) = LTy.elt σ.glob _ (TEnv.get i σ.env)
      from envVal_pos (g := σ.glob) σ.env i]
    cases h : TEnv.get i σ.env <;> simp only [LTy.elt, Tm.denote, Tm.eval, h]
  | _, .pvS i => (envVal_pos (g := σ.glob) σ.env i).trans rfl
  | _, .pvI i => (envVal_pos (g := σ.glob) σ.env i).trans rfl
  | _, .pvZ i => (envVal_pos (g := σ.glob) σ.env i).trans rfl
  | _, .netOf i a => by
    have ha := Tm.realize_toTerm σ v a
    simp only [Tm.toTerm, Term.realize]
    show funMap σ.glob (n := 2) (.inr ()) _ = _
    simp only [funMap, Matrix.cons_val_zero, Matrix.cons_val_one, Term.realize_var,
      Sum.elim_inr, ha, Carrier.as_mk]
    rw [show val σ (Idx.pos i) = .inr (TEnv.get i σ.env) from envVal_pos (g := σ.glob) σ.env i]
    rfl
  | _, .app0 o => rfl
  | _, .app1 o x => by
    have hx := Tm.realize_toTerm σ v x
    simp only [Tm.toTerm, Term.realize]
    show funMap σ.glob (n := 1) _ _ = _
    simp only [Matrix.cons_val_zero, hx, funMap, Carrier.as_mk]
    rfl
  | _, .app2 o x y => by
    have hx := Tm.realize_toTerm σ v x
    have hy := Tm.realize_toTerm σ v y
    simp only [Tm.toTerm, Term.realize]
    show funMap σ.glob (n := 2) _ _ = _
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hx, hy, funMap,
      Carrier.as_mk]
    rfl
  | _, .app3 o x y z => by
    have hx := Tm.realize_toTerm σ v x
    have hy := Tm.realize_toTerm σ v y
    have hz := Tm.realize_toTerm σ v z
    simp only [Tm.toTerm, Term.realize]
    show funMap σ.glob (n := 3) _ _ = _
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, hx, hy, hz, funMap, Carrier.as_mk]
    rfl

/-! ## Formulas -/

/-- **A formula of the calculus as a Mathlib bounded formula**, defined on
the first-order fragment: `∀ p x; φ` is `∀ x, val p x → φ`. -/
def _root_.Solidity.Fml.toBF : {Γ : Ctx} → Fml C Γ → Option ((lang C).BoundedFormula Empty Γ.length)
  | _, .tt => some ⊤
  | _, .eq (p := p) a b => some (Relations.boundedFormula₂ (L := lang C) (show Rl 2 from p)
      a.toTerm b.toTerm)
  | _, .wellFormed s =>
    some (Relations.boundedFormula₁ (L := lang C) (show Rl 1 from .wt) s.toTerm)
  | _, .not φ => φ.toBF.map BoundedFormula.not
  | _, .and φ ψ => φ.toBF.bind fun a => ψ.toBF.map fun b => a ⊓ b
  | _, .imp φ ψ => φ.toBF.bind fun a => ψ.toBF.map fun b => a.imp b
  | Γ, .all _ p φ => φ.toBF.map fun a => BoundedFormula.all
      ((Relations.boundedFormula₁ (L := lang C) (show Rl 1 from .val p)
        (.var (.inr (Fin.last Γ.length)))).imp a)
  | _, .upd .. | _, .modal .. | _, .havoc .. | _, .bind .. | _, .anon .. | _, .allocAll .. | _, .grow .. =>
    none

/-- The translation is defined exactly on the first-order fragment. -/
theorem _root_.Solidity.Fml.toBF_isSome : {Γ : Ctx} → (φ : Fml C Γ) → φ.toBF.isSome = φ.FO
  | _, .tt | _, .eq .. | _, .wellFormed .. => rfl
  | _, .upd .. | _, .modal .. | _, .havoc .. | _, .bind .. | _, .anon .. | _, .allocAll .. | _, .grow .. => rfl
  | _, .not φ => by
    rw [show (Fml.not φ).FO = φ.FO from rfl, ← Fml.toBF_isSome φ]
    simp only [Fml.toBF, Option.isSome_map]
  | _, .all _ _ φ => by
    rw [show (Fml.all _ _ φ).FO = φ.FO from rfl, ← Fml.toBF_isSome φ]
    simp only [Fml.toBF, Option.isSome_map]
  | _, .and φ ψ => by
    rw [show (Fml.and φ ψ).FO = (φ.FO && ψ.FO) from rfl, ← Fml.toBF_isSome φ,
      ← Fml.toBF_isSome ψ]
    simp only [Fml.toBF]
    cases φ.toBF <;> cases ψ.toBF <;> rfl
  | _, .imp φ ψ => by
    rw [show (Fml.imp φ ψ).FO = (φ.FO && ψ.FO) from rfl, ← Fml.toBF_isSome φ,
      ← Fml.toBF_isSome ψ]
    simp only [Fml.toBF]
    cases φ.toBF <;> cases ψ.toBF <;> rfl

/-- **A formula realizes as it holds**: in the structure of the state's
global part, its locals the bound variables. -/
theorem _root_.Solidity.Fml.realize_toBF {Γ : Ctx} (σ : State C Γ) (φ : Fml C Γ)
    {β : (lang C).BoundedFormula Empty Γ.length} (h : φ.toBF = some β)
    (v : Empty → Carrier C σ.glob) :
    holds σ φ ↔ β.Realize v (val σ) := by
  induction φ with
  | tt =>
    cases h
    simp only [holds, BoundedFormula.realize_top]
  | eq a b =>
    cases h
    rw [holds_eq, BoundedFormula.realize_rel₂, Tm.realize_toTerm, Tm.realize_toTerm]
    show _ ↔ relMap (n := 2) _ _
    simp only [relMap, Matrix.cons_val_zero, Matrix.cons_val_one,
      Carrier.as_mk]
  | wellFormed s =>
    cases h
    rw [holds_wellFormed, BoundedFormula.realize_rel₁, Tm.realize_toTerm]
    show _ ↔ relMap (n := 1) _ _
    simp only [relMap, Matrix.cons_val_zero, Carrier.as_mk]
  | not φ ih =>
    simp only [Fml.toBF, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    rw [BoundedFormula.realize_not, ← ih σ ha v]
    rfl
  | and φ ψ ihφ ihψ =>
    simp only [Fml.toBF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [BoundedFormula.realize_inf, ← ihφ σ ha v, ← ihψ σ hb v]
    rfl
  | imp φ ψ ihφ ihψ =>
    simp only [Fml.toBF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [BoundedFormula.realize_imp, ← ihφ σ ha v, ← ihψ σ hb v]
    rfl
  | all x p φ ih =>
    simp only [Fml.toBF, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    rw [BoundedFormula.realize_all]
    constructor
    · intro hφ m hm
      have hm' : relMap (n := 1) (Rel1.val p) ![Fin.snoc (α := fun _ => Carrier C σ.glob)
          (val σ) m (Fin.last _)] := by
        simpa only [BoundedFormula.realize_rel₁, Term.realize_var, Sum.elim_inr] using hm
      obtain ⟨w, hw⟩ := hm'
      simp only [Matrix.cons_val_zero, Fin.snoc_last] at hw
      subst hw
      exact (ih (σ.push (t := .val p) w) ha v).1 (hφ w)
    · intro hφ w
      refine (ih (σ.push (t := .val p) w) ha v).2 ?_
      refine hφ (LTy.elt σ.glob (.val p) w) ?_
      simp only [BoundedFormula.realize_rel₁, Term.realize_var, Sum.elim_inr]
      exact ⟨w, by simp only [Matrix.cons_val_zero, Fin.snoc_last]; rfl⟩
  | upd | modal | havoc | bind | anon | allocAll | grow => cases h

/-! ## The Theory -/

/-- **The Theory of the contract**: the sentences every state satisfies. -/
def SolTheory (C : Contract) : (lang C).Theory := {ψ | ∀ g : State C [], Carrier C g ⊨ ψ}

/-- It is the intersection of the states' complete theories. -/
theorem solTheory_eq_iInter :
    SolTheory C = ⋂ g : State C [], (lang C).completeTheory (Carrier C g) := by
  ext ψ
  simp only [SolTheory, Set.mem_setOf_eq, Set.mem_iInter, Language.completeTheory]

/-- Every state is a model of the Theory. -/
instance model (g : State C []) : (SolTheory C).Model (Carrier C g) :=
  ⟨fun _ h => h g⟩

/-- The Theory is satisfiable: the initial state models it. -/
theorem solTheory_isSatisfiable : (SolTheory C).IsSatisfiable :=
  ⟨Theory.ModelType.of (SolTheory C) (Carrier C (State.init C))⟩

/-- **The Theory is closed under semantic consequence.** -/
theorem mem_of_models {ψ : (lang C).Sentence}
    (h : ∀ M : Theory.ModelType.{0, 0, 0} (SolTheory C), M ⊨ ψ) : ψ ∈ SolTheory C :=
  fun g => h (Theory.ModelType.of (SolTheory C) (Carrier C g))

/-- A semantic consequence of the contract theory uses finitely many of its
sentences (Mathlib compactness). This is finite support of first-order
entailment, not completeness of the program calculus. -/
theorem finite_support {ψ : (lang C).Sentence} (h : SolTheory C ⊨ᵇ ψ) :
    ∃ T₀ : Finset (lang C).Sentence,
      (T₀ : (lang C).Theory) ⊆ SolTheory C ∧ (T₀ : (lang C).Theory) ⊨ᵇ ψ :=
  FirstOrder.Language.Theory.models_iff_finset_models.mp h

/-- A first-order consequence of any collection of storage facts needs
only finitely many of those facts. The contract theory remains available
in full; compactness is applied to its union with the supplied facts. -/
theorem finite_storage_support (facts : (lang C).Theory) {ψ : (lang C).Sentence}
    (h : SolTheory C ∪ facts ⊨ᵇ ψ) :
    ∃ F : Finset (lang C).Sentence, (F : (lang C).Theory) ⊆ facts ∧
      SolTheory C ∪ (F : (lang C).Theory) ⊨ᵇ ψ := by
  classical
  obtain ⟨T, hT, hmodels⟩ := FirstOrder.Language.Theory.models_iff_finset_models.mp h
  refine ⟨T.filter (· ∈ facts), ?_, ?_⟩
  · intro φ hφ
    exact (Finset.mem_filter.mp hφ).2
  · rw [FirstOrder.Language.Theory.models_iff_not_satisfiable] at hmodels ⊢
    intro hs
    apply hmodels (hs.mono ?_)
    intro φ hφ
    rcases hφ with hφ | hnot
    · left
      rcases hT hφ with hcore | hfact
      · exact Or.inl hcore
      · exact Or.inr (Finset.mem_filter.mpr ⟨hφ, hfact⟩)
    · exact Or.inr hnot

/-- info: 'Solidity.FO.finite_storage_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms finite_storage_support

/-- A sentence realizes in a closed state as its formula holds there. -/
theorem holds_iff_realize (σ : State C []) {φ : Fml C []} {ψ : (lang C).Sentence}
    (h : φ.toBF = some ψ) : holds σ φ ↔ Carrier C σ.glob ⊨ ψ := by
  rw [Fml.realize_toBF σ φ h Empty.elim]
  change BoundedFormula.Realize ψ Empty.elim (val σ) ↔
    BoundedFormula.Realize ψ default default
  have hv : val σ = (default : Fin 0 → Carrier C σ.glob) := funext fun i => Fin.elim0 i
  rw [hv, show (Empty.elim : Empty → Carrier C σ.glob) = default from funext fun e => e.elim]

/-- A closed state is its own global part. -/
theorem glob_eq (σ : State C []) : σ.glob = σ := rfl

/-- **A first-order formula is valid exactly when its sentence is in the
Theory.** -/
theorem valid_iff_mem {φ : Fml C []} {ψ : (lang C).Sentence} (h : φ.toBF = some ψ) :
    Fml.Valid φ ↔ ψ ∈ SolTheory C :=
  ⟨fun hv g => (holds_iff_realize g h).1 (hv g), fun hm σ => (holds_iff_realize σ h).2 (hm σ)⟩

/-- **What the calculus proves is in the Theory**: soundness, read in
Mathlib's model theory. -/
theorem _root_.Solidity.Proves.mem_solTheory {R : RuleSet} {φ : Fml C []}
    {ψ : (lang C).Sentence} (d : Proves C R [] .nil φ) (h : φ.toBF = some ψ) :
    ψ ∈ SolTheory C :=
  (valid_iff_mem h).1 d.fmlValid

/-- A first-order formula the calculus proves is a semantic consequence of
any theory the states model. -/
theorem _root_.Solidity.Proves.realize {R : RuleSet} {φ : Fml C []}
    {ψ : (lang C).Sentence} (d : Proves C R [] .nil φ) (h : φ.toBF = some ψ)
    (g : State C []) : Carrier C g ⊨ ψ :=
  d.mem_solTheory h g

end FO

end Solidity
