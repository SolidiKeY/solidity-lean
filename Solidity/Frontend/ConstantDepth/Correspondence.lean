import Solidity.Frontend.ConstantDepth.Complete
-- `Determinism` is not used here; importing it puts it in `Controls`, which pins it.
import Solidity.Frontend.ConstantDepth.Determinism

/-! # Exact dependency correspondence and determinism (backfill)

Under the existing clash-free projection of the well-formed contract, the
graph edges of a declared constant are exactly the resolved constant paths
of its own initializer; rank decreases along each of them; and the public
checkers make typed evaluation and array lengths functional.
-/
namespace Solidity.Frontend.ConstantDepth
open Solidity.Source Solidity.Frontend.Static

/-- A declared, named constant normalizes to itself. -/
theorem lookup_declared_constant {E : Env} {d : Decl}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false)
    (hd : d ∈ E.decls) (hc : d.isConst = true) (hn : d.name ≠ "") :
    E.lookup d.scope d.name = [d] := by
  apply lookup_own_singleton
  apply declared_constant_singleton hw _ hc
  apply List.mem_filter.mpr
  exact ⟨hd, by simpa only [beq_self_eq_true, Bool.true_and, bne_iff_ne] using hn⟩

/-- **Exact correspondence**: a declared constant's graph edges are precisely
the constants its initializer's paths resolve to, from its own scope. -/
theorem constDeps_declared_iff {E : Env} {d : Decl} {e : Syn .expr} {b : Node}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false)
    (hd : d ∈ E.decls) (hc : d.isConst = true) (hn : d.name ≠ "") (he : d.init? = some e) :
    b ∈ E.constDeps (d.scope, d.name) ↔
      ∃ p d', p ∈ e.paths ∧ E.lookupPath d.scope p = [d'] ∧ d'.isConst = true ∧
        b = (d'.scope, d'.name) := by
  have hl := lookup_declared_constant hw hd hc hn
  rw [mem_constDeps_iff]
  constructor
  · rintro ⟨d₁, e₁, p, d', hl₁, _, he₁, hp, hd', hc', rfl⟩
    rw [hl] at hl₁; cases hl₁
    rw [he] at he₁; cases he₁
    exact ⟨p, d', hp, hd', hc', rfl⟩
  · rintro ⟨p, d', hp, hd', hc', rfl⟩
    exact ⟨d, e, p, d', hl, hc, he, hp, hd', hc', rfl⟩

/-- Rank decreases along every resolved path of a declared constant's
initializer that names a constant. (In expressions `Syn.paths` yields only
plain identifiers: a member access `K.X` contributes the path `K`, so a
qualified constant reference is no graph edge; see `Controls.qualified_no_edge`.) -/
theorem rank_declared_dependency_lt {E : Env} {d d' : Decl} {e : Syn .expr} {p : IdPath}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false) (ha : ConstsAcyclic E)
    (hd : d ∈ E.decls) (hc : d.isConst = true) (hn : d.name ≠ "") (he : d.init? = some e)
    (hp : p ∈ e.paths) (hd' : E.lookupPath d.scope p = [d']) (hc' : d'.isConst = true) :
    rank E (d'.scope, d'.name) < rank E (d.scope, d.name) :=
  rank_lt ha (mem_constNodes_iff.mpr ⟨d, hd, hc, rfl⟩)
    ((constDeps_declared_iff hw hd hc hn he).mpr ⟨p, d', hp, hd', hc', rfl⟩)

/-- Along a nonempty dependency path the rank strictly drops, so no path
leads back (a corollary of `rank_lt_path` and `rank_mono`). -/
theorem depPath_rank_no_return {E : Env} (ha : ConstsAcyclic E) {a b : Node}
    (hA : a ∈ constNodes E) (hab : DepPath E a b) :
    rank E b < rank E a ∧ ¬ Reach E.constDeps b a := by
  have h1 := rank_lt_path ha hA hab
  refine ⟨h1, fun hba => ?_⟩
  have hb : b ∈ constNodes E := by
    obtain ⟨c, hc, hcb⟩ := depPath_iff.mp hab
    exact Closed.reach (fun _ _ _ h => constDeps_sub h) hcb (constDeps_sub hc)
  have h2 := rank_mono hb hba
  omega

/-- Typed evaluation is functional under the unchanged contract, here derived
from completeness; `teval_det` (`Determinism.lean`) needs no contract. -/
theorem teval_unique {E : Env} {scope : Option String} {e : Syn .expr} {v w : TVal}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false) (ha : ConstsAcyclic E)
    (hv : TEval E scope e v) (hw' : TEval E scope e w) : v = w := by
  have h1 := evalConst_complete hw ha hv
  rw [evalConst_complete hw ha hw'] at h1
  exact (Option.some.inj h1).symm

/-- Named constants have one type and one value under the unchanged contract. -/
theorem nconst_unique {E : Env} {scope : Option String} {x : String} {t t' : IntTy} {q q' : Q}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false) (ha : ConstsAcyclic E)
    (h : NamedConst E scope x t q) (h' : NamedConst E scope x t' q') : t = t' ∧ q = q' := by
  have e := teval_unique hw ha (.named h) (.named h')
  cases e
  exact ⟨rfl, rfl⟩

/-- Array-length consumers: a length certificate is unique. -/
theorem arrayLen_unique {E : Env} {scope : Option String} {o : Syn (.opt .expr)} {n m : Option Nat}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false) (ha : ConstsAcyclic E)
    (hn : ArrayLenOK E scope o n) (hm : ArrayLenOK E scope o m) : n = m := by
  have h1 := arrayLenB_complete hw ha hn
  rw [arrayLenB_complete hw ha hm] at h1
  exact (Option.some.inj h1).symm

/-- A static length is positive and comes from a constant value. -/
theorem arrayLen_static_value {E : Env} {scope : Option String} {e : Syn .expr} {n : Nat}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false) (ha : ConstsAcyclic E)
    (hl : ArrayLenOK E scope (.some e) (some n)) :
    0 < n ∧ ∃ v, evalConst E scope e = some v ∧ v.2.isInt = true ∧ v.2.toInt.toNat = n := by
  cases hl with
  | static hv hi hp =>
    obtain ⟨t, ht⟩ := hv
    refine ⟨by omega, _, evalConst_complete hw ha ht, hi, rfl⟩

end Solidity.Frontend.ConstantDepth
