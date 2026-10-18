import Solidity.Calculus.QueryArithmetic
import Solidity.Calculus.CheckedLinear
import Solidity.Calculus.SymbolicPaths

/-!
# Symbolic alias constraints from the existing path comparison

The closer's `relSegs` already compares symbolic typed paths, with tests on
their key terms. Reading that case tree as a formula generates the alias
condition used by arithmetic read abstraction. Its correctness is conditional
on both paths evaluating: failed key computations do not acquire locations.
Primitive endpoints turn the prefix comparison into actual reference equality.
-/

namespace Solidity.Decide

open Semantics ReadRealization Linear ScalarCode

variable {C : Contract}

namespace CTree

/-- Read the existing comparison tree as Boolean combinations of defined
key equalities. The leaves can carry any existing leaf formula. -/
def toFormula {α : Type} (leaf : α → LFml C) : CTree C α → LFml C
  | .leaf x => leaf x
  | .node a b t e =>
    .and (.imp (.eq a b) (toFormula leaf t))
      (.imp (.not (.eq a b)) (toFormula leaf e))

theorem toFormula_holds {α : Type} (g : State C []) (ν : AEnv)
    (leaf : α → LFml C) (tree : CTree C α) (ht : tree.TestsOk g ν) :
    (tree.toFormula leaf).holds g ν ↔ (leaf (tree.sel g ν)).holds g ν := by
  induction tree with
  | leaf x => rfl
  | node a b t e iht ihe =>
    obtain ⟨ha, hb, ht, he⟩ := ht
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hb
    simp only [toFormula, LFml.holds, hx, hy, sel, Option.some.injEq]
    rw [iht ht, ihe he]
    by_cases h : x = y <;>
      simp only [h, ↓reduceIte, not_true_eq_false, not_false_eq_true,
        true_implies, false_implies, and_true, true_and]

end CTree

private def aliasLeaf {T U : Ty} : Option (TSegs C T U) → LFml C
  | none => .ff
  | some _ => .tt

/-- Generate the condition for two primitive symbolic paths to name the
same actual location, using the closer's existing key-comparison tree. -/
def SPath.alias {p q : PrimTy} (P : SPath C (.prim p)) (Q : SPath C (.prim q)) : LFml C :=
  if h : P.r = Q.r then
    (relSegs P.segs (root_inj h P.hr Q.hr ▸ Q.segs)).toFormula aliasLeaf
  else .ff

/-- Successful path evaluation is the exact side condition for the alias
formula. The endpoint types and declaration proofs remain intrinsic. -/
theorem SPath.alias_holds (g : State C []) (ν : AEnv) {p q : PrimTy}
    (P : SPath C (.prim p)) (Q : SPath C (.prim q))
    {pr : SRef C (.prim p)} {qr : SRef C (.prim q)}
    (hp : P.eval g ν = some pr) (hq : Q.eval g ν = some qr)
    (hpr : pr.Declared) (hqr : qr.Declared) :
    (P.alias Q).holds g ν ↔ Ref.mk p pr hpr = Ref.mk q qr hqr := by
  apply Iff.trans ?_ (Ref.beq_iff _ _)
  change (P.alias Q).holds g ν ↔ (pr.strip? qr).isSome = true
  cases P with | mk rp hrp sp =>
  cases Q with | mk rq hrq sq =>
  simp only [SPath.eval, Option.map_eq_some_iff] at hp hq
  obtain ⟨pp, hpp, rfl⟩ := hp
  obtain ⟨qp, hqp, rfl⟩ := hq
  by_cases h : rp = rq
  · subst rq
    obtain rfl := root_inj rfl hrp hrq
    obtain ⟨ht, hr⟩ := relSegs_sound g ν sp sq hpp hqp
    simp only [SPath.alias, ↓reduceDIte, CTree.toFormula_holds g ν aliasLeaf _ ht,
      SRef.strip?]
    cases hs : (relSegs sp sq).sel g ν <;> cases hh : pp.strip? qp <;>
      simp only [hs, hh, RelOk, aliasLeaf, LFml.holds, Option.isSome_none,
        Option.isSome_some, Bool.false_eq_true, not_true_eq_false] at hr ⊢
  · simp only [SPath.alias, ↓reduceDIte, LFml.holds,
      SRef.strip?, h, ↓reduceDIte, Option.isSome_none, Bool.false_eq_true,
      not_true_eq_false]

/-- An alias formula for two existing source path terms, with its exact
successful-evaluation side conditions retained. -/
structure AliasCondition {p q : PrimTy} (a : LTm C (.path (.prim p)))
    (b : LTm C (.path (.prim q))) where
  formula : LFml C
  correct : ∀ (g : State C []) (ν : AEnv)
    (pr : SRef C (.prim p)) (qr : SRef C (.prim q)),
    a.eval g ν = some pr → b.eval g ν = some qr →
    ∀ (hpr : pr.Declared) (hqr : qr.Declared),
      formula.holds g ν ↔ Ref.mk p pr hpr = Ref.mk q qr hqr

def aliasCondition? {p q : PrimTy} (a : LTm C (.path (.prim p)))
    (b : LTm C (.path (.prim q))) : Option (AliasCondition a b) := do
  let pa ← SPath.view? a
  let pb ← SPath.view? b
  return ⟨pa.path.alias pb.path, fun g ν _ _ ha hb hpr hqr =>
    SPath.alias_holds g ν pa.path pb.path
      ((pa.correct g ν).trans ha) ((pb.correct g ν).trans hb) hpr hqr⟩

/-- The shared checked compiler translates the generated path tests.
Its usual finite reference/input layout is preserved. -/
structure AliasEncoding {p q : PrimTy} (a : LTm C (.path (.prim p)))
    (b : LTm C (.path (.prim q))) (ps : List Parameter := []) (es : List EnvKey := []) where
  condition : AliasCondition a b
  encoding : StorageEncoding (ps := ps) (es := es) condition.formula

def aliasEncoding? (ps : List Parameter) (es : List EnvKey) {p q : PrimTy}
    (a : LTm C (.path (.prim p))) (b : LTm C (.path (.prim q))) :
    Option (AliasEncoding a b ps es) := do
  let condition ← aliasCondition? a b
  let encoding ← StorageEncoding.ofFormula? condition.formula
  return ⟨condition, encoding⟩

theorem AliasEncoding.correct {p q : PrimTy} {a : LTm C (.path (.prim p))}
    {b : LTm C (.path (.prim q))} {ps : List Parameter} {es : List EnvKey}
    (r : AliasEncoding a b ps es) (rs : List (Ref C)) (hr : ∀ q ∈ r.encoding.refs, q ∈ rs)
    (g : State C []) (ν : AEnv) (pr : SRef C (.prim p)) (qr : SRef C (.prim q))
    (ha : a.eval g ν = some pr) (hb : b.eval g ν = some qr)
    (hpr : pr.Declared) (hqr : qr.Declared) :
    (r.encoding.lower rs).holds (Inputs.observe es ps rs g ν).codes ↔
      Ref.mk p pr hpr = Ref.mk q qr hqr :=
  (r.encoding.correct rs hr g ν).trans (r.condition.correct g ν pr qr ha hb hpr hqr)

/-- One flattened symbolic read. Its result term will normally be the
fresh typed arithmetic atom for this occurrence. -/
structure SymbolicRead (C : Contract) where
  prim : PrimTy
  path : SPath C (.prim prim)
  result : LTm C (.val prim)

namespace SymbolicRead

/-- A successful symbolic occurrence, with its actual declared location
and exact result. Partial keys or result terms require separate guards. -/
structure Witness (g : State C []) (ν : AEnv) (r : SymbolicRead C) where
  ref : SRef C (.prim r.prim)
  declared : ref.Declared
  value : r.prim.Denote
  path_eq : r.path.eval g ν = some ref
  result_eq : r.result.eval g ν = some value

def Witness.entry {g : State C []} {ν : AEnv} {r : SymbolicRead C}
    (w : Witness g ν r) : (q : Ref C) × q.Value := ⟨⟨r.prim, w.ref, w.declared⟩, w.value⟩

/-- Equal locations imply equal values. Different primitive endpoint
types cannot alias and need no constraint. -/
def constraint (r q : SymbolicRead C) : LFml C :=
  if h : r.prim = q.prim then
    .imp (r.path.alias q.path) (.eq r.result (h.symm ▸ q.result))
  else .tt

theorem constraint_holds (g : State C []) (ν : AEnv) (r q : SymbolicRead C)
    (wr : Witness g ν r) (wq : Witness g ν q) :
    (r.constraint q).holds g ν ↔ Assignment.Consistent [wr.entry, wq.entry] := by
  cases r with | mk p P v =>
  cases q with | mk q Q w =>
  by_cases h : p = q
  · subst q
    simp only [constraint, ↓reduceDIte, LFml.holds, wr.result_eq, wq.result_eq]
    rw [SPath.alias_holds g ν P Q wr.path_eq wq.path_eq wr.declared wq.declared]
    exact (Assignment.pair_consistent_typed wr.ref wq.ref wr.declared wq.declared
      wr.value wq.value).symm
  · simp only [constraint, h, ↓reduceDIte, LFml.holds, true_iff]
    rw [Assignment.pair_consistent]
    intro he
    exact (h (congrArg Ref.prim he)).elim

private def conjunction : List (LFml C) → LFml C
  | [] => .tt
  | φ :: fs => .and φ (conjunction fs)

private theorem conjunction_holds (g : State C []) (ν : AEnv) (fs : List (LFml C)) :
    (conjunction fs).holds g ν ↔ ∀ φ ∈ fs, φ.holds g ν := by
  induction fs with
  | nil => simp only [conjunction, LFml.holds, List.not_mem_nil, false_implies, implies_true]
  | cons φ fs ih => simp only [conjunction, LFml.holds, ih, List.forall_mem_cons]

/-- Generate every finite pair's symbolic alias constraint. Repeated
occurrences retain their individual result terms. -/
def constraints (rs : List (SymbolicRead C)) : LFml C :=
  conjunction (rs.flatMap fun r => rs.map fun q => r.constraint q)

theorem constraints_holds (g : State C []) (ν : AEnv) (rs : List (SymbolicRead C)) :
    (constraints rs).holds g ν ↔ ∀ r ∈ rs, ∀ q ∈ rs, (r.constraint q).holds g ν := by
  rw [constraints, conjunction_holds]
  constructor
  · intro h r hr q hq
    exact h _ (List.mem_flatMap.mpr ⟨r, hr, List.mem_map.mpr ⟨q, hq, rfl⟩⟩)
  · intro h φ hφ
    obtain ⟨r, hr, hm⟩ := List.mem_flatMap.mp hφ
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact h r hr q hq

private theorem consistent_map_iff {α : Type} (xs : List α)
    (f : α → (r : Ref C) × r.Value) :
    Assignment.Consistent (xs.map f) ↔
      ∀ x ∈ xs, ∀ y ∈ xs, Assignment.Consistent [f x, f y] := by
  constructor
  · intro hc x hx y hy
    have hm : ∀ e ∈ [f x, f y], e ∈ xs.map f := by
      intro e he
      rcases List.mem_cons.mp he with he | he
      · rw [he]; exact List.mem_map.mpr ⟨x, hx, rfl⟩
      · rw [List.mem_singleton.mp he]; exact List.mem_map.mpr ⟨y, hy, rfl⟩
    exact fun r v w hv hw => hc r v w (hm _ hv) (hm _ hw)
  · intro h r v w hv hw
    obtain ⟨x, hx, hfx⟩ := List.mem_map.mp hv
    obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hw
    exact h x hx y hy r v w (List.mem_cons.mpr (Or.inl hfx.symm))
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hfy.symm))))

/-- Keep each syntactic occurrence together with its successful typed
interpretation. Repeated syntax remains allowed. -/
abbrev Realized (g : State C []) (ν : AEnv) := (r : SymbolicRead C) × Witness g ν r

/-- The generated finite conjunction is exactly alias consistency of the
actual typed assignment used by trace reconstruction. -/
theorem constraints_realized_holds (g : State C []) (ν : AEnv) (rs : List (Realized g ν)) :
    (constraints (rs.map Sigma.fst)).holds g ν ↔
      Assignment.Consistent (rs.map fun r => r.2.entry) := by
  rw [constraints_holds, consistent_map_iff]
  constructor
  · intro h x hx y hy
    exact (constraint_holds g ν x.1 y.1 x.2 y.2).mp
      (h x.1 (List.mem_map.mpr ⟨x, hx, rfl⟩) y.1 (List.mem_map.mpr ⟨y, hy, rfl⟩))
  · intro h r hr q hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq
    exact (constraint_holds g ν x.1 y.1 x.2 y.2).mpr (h x hx y hy)

end SymbolicRead

end Solidity.Decide
