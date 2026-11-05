import Solidity.Frontend.ConstantDepth.Lookup

/-! # Declaration-derived fuel completeness

The expression lemma uses only the named occurrences in its syntax. Fuel
for those occurrences is supplied separately from the dependency rank.
-/
namespace Solidity.Frontend.ConstantDepth
open Solidity.Source Solidity.Frontend.Static

/-- Binary expression paths are exactly the two operands' paths. -/
theorem constBin_paths {e a b : Syn .expr} {k : ConstOp}
    (hk : e.constBin? = some (k, a, b)) : e.paths = a.paths ++ b.paths := by
  rw [constBin_eq hk]
  cases k <;> rfl

/-- Structural expression completeness for an independently supplied named oracle. -/
theorem teval_with_oracle {E : Env} : {scope : Option String} → {e : Syn .expr} → {v : TVal} →
    TEval E scope e v →
    (named : (x : String) → Option {p : IntTy × Q // NamedConst E scope x p.1 p.2}) →
    (∀ x t q, (⟨x, []⟩ : IdPath) ∈ e.paths → NamedConst E scope x t q →
      (named x).map Subtype.val = some (t, q)) →
    (tevalP E scope named e).map TRes.val = some v
  | _, _, _, .rational h, _, _ => tevalP_const h
  | _, _, _, .named hn, named, hall => by
    show (withConst E _ (.ident _) _).map TRes.val = _
    rw [withConst_none rfl]
    have h := hall _ _ _ List.mem_cons_self hn
    cases hp : named _ with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp only [Option.map_some, TRes.val, h]
  | _, _, _, .paren he, named, hall => by
    show (withConst E _ (.tuple (.some _) .nil) _).map TRes.val = _
    rw [withConst_none (typed_const_none (.paren he) rfl)]
    apply parenT_val
    exact teval_with_oracle he named (fun x t q hp hn =>
      hall x t q (List.mem_append_left _ hp) hn)
  | _, _, _, .unary hop hx hl hr hr', named, hall => by
    show (withConst E _ (.unaryPrefix _ _) _).map TRes.val = _
    rw [withConst_none (typed_const_none (.unary hop hx hl hr hr') rfl)]
    exact unT_val (teval_with_oracle hx named hall) hop hl hr hr'
  | _, _, _, .binary hk ha hb hs ht hla hlb hr hr', named, hall => by
    rw [tevalP_bin hk, withConst_none (typed_const_none (.binary hk ha hb hs ht hla hlb hr hr') rfl)]
    have hpaths := constBin_paths hk
    have hna := teval_with_oracle ha named (fun x t q hp hn =>
      hall x t q (hpaths ▸ List.mem_append_left _ hp) hn)
    have hnb := teval_with_oracle hb named (fun x t q hp hn =>
      hall x t q (hpaths ▸ List.mem_append_right _ hp) hn)
    exact binT_val hna hnb hs ht hla hlb hr hr'

/-- A named initializer needs no more fuel than its declaration-derived rank. -/
theorem nconst_rank_complete {E : Env}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false) (ha : ConstsAcyclic E) :
    ∀ n {scope : Option String} {x : String} {d : Decl} {t : IntTy} {q : Q},
      E.lookup scope x = [d] → rank E (d.scope, d.name) ≤ n → NamedConst E scope x t q →
      (nconstP E n scope x).map Subtype.val = some (t, q) := by
  intro n
  induction n with
  | zero =>
    intro scope x d t q hl hr hn
    cases hn with
    | mk hl' hc he hv hev hq =>
      rw [hl] at hl'; cases hl'
      have hp := rank_pos (mem_constNodes_iff.mpr
        ⟨d, Env.lookup_sub (by rw [hl]; exact List.mem_cons_self), hc, rfl⟩)
      omega
  | succ n ih =>
    intro scope x d t q hl hr hn
    cases hn with
    | mk hl' hc he hv hev hq =>
      rename_i d' e v
      rw [hl] at hl'; cases hl'
      have hm : (tevalP E d.scope (nconstP E n d.scope) e).map TRes.val = some v := by
        apply teval_with_oracle hev
        intro y ty qy hp hn'
        cases hn' with
        | mk hy hc' he' hv' hev' hq' =>
          have hlt := rank_resolved_dependency_lt hw ha hl hc he hp hy hc'
          exact ih hy (by omega) (.mk hy hc' he' hv' hev' hq')
      unfold nconstP
      split
      · rename_i d' hl'
        rw [hl] at hl'; cases hl'
        rw [dif_pos hc]
        split
        · rename_i e' he'
          rw [he] at he'; cases he'
          split
          · rename_i t' hv'
            rw [hv] at hv'; cases hv'
            split
            · rename_i v' hev' heq
              rw [heq] at hm
              cases hm
              simp only [TRes.val] at hq
              split
              · rename_i q' hq'
                rw [hq] at hq'; cases hq'; rfl
              · rename_i hq'; rw [hq] at hq'; cases hq'
            · rename_i heq; rw [heq] at hm; cases hm
          · rename_i hn'; exact absurd hv (hn' _)
        · rename_i he'; rw [he] at he'; cases he'
      · rename_i hn'; exact absurd hl (hn' d)

/-- The public declaration-count bound suffices for every independently derived named value. -/
theorem nconst_levels_complete {E : Env} {scope : Option String} {x : String} {t : IntTy} {q : Q}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false) (ha : ConstsAcyclic E)
    (hn : NamedConst E scope x t q) :
    (nconstP E (levels E) scope x).map Subtype.val = some (t, q) := by
  cases hn with
  | mk hl hc he hv hev hq =>
    exact nconst_rank_complete hw ha _ hl
      (Nat.le_trans (rank_le_decls E _) (Nat.le_succ _)) (.mk hl hc he hv hev hq)

/-- Evaluation at the actual unchanged public bound returns the TEval value. -/
theorem evalConst_complete {E : Env} {scope : Option String} {e : Syn .expr} {v : TVal}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false) (ha : ConstsAcyclic E)
    (he : TEval E scope e v) : evalConst E scope e = some v :=
  teval_with_oracle he _ (fun _ _ _ _ hn => nconst_levels_complete hw ha hn)

/-- The existing well-formed resolved-unit contract supplies the no-clash projection. -/
theorem evalConst_resolved_complete {settings : Settings} {u : Syn .unit}
    (hw : WellFormed (resolveUnit settings u)) (ha : ConstsAcyclic u.env)
    {scope : Option String} {e : Syn .expr} {v : TVal} (he : TEval u.env scope e v) :
    evalConst u.env scope e = some v :=
  evalConst_complete hw.noClash ha he

/-- Named-constant completeness with exactly the resolved-unit well-formedness contract. -/
theorem nconst_resolved_complete {settings : Settings} {u : Syn .unit}
    (hw : WellFormed (resolveUnit settings u)) (ha : ConstsAcyclic u.env)
    {scope : Option String} {x : String} {t : IntTy} {q : Q}
    (hn : NamedConst u.env scope x t q) :
    (nconstP u.env (levels u.env) scope x).map Subtype.val = some (t, q) :=
  nconst_levels_complete hw.noClash ha hn

/-- Public evaluation decides the exact typed value under the unchanged contract. -/
theorem evalConst_iff {E : Env} {scope : Option String} {e : Syn .expr} {v : TVal}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false) (ha : ConstsAcyclic E) :
    evalConst E scope e = some v ↔ TEval E scope e v :=
  ⟨evalConst_sound, evalConst_complete hw ha⟩

/-- Refusal means no independent typed evaluation exists, including overflow refusals. -/
theorem evalConst_none_iff {E : Env} {scope : Option String} {e : Syn .expr}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false) (ha : ConstsAcyclic E) :
    evalConst E scope e = none ↔ ¬ ∃ v, TEval E scope e v := by
  constructor
  · intro hn ⟨v, hv⟩
    rw [evalConst_complete hw ha hv] at hn
    cases hn
  · intro hn
    cases he : evalConst E scope e with
    | none => rfl
    | some v => exact False.elim (hn ⟨v, evalConst_sound he⟩)

/-- Both dynamic and positive integral static array lengths are complete. -/
theorem arrayLenB_complete {E : Env} {scope : Option String} {o : Syn (.opt .expr)} {n : Option Nat}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false) (ha : ConstsAcyclic E)
    (hl : ArrayLenOK E scope o n) : arrayLenB E scope o = some n := by
  cases hl with
  | dynamic => rfl
  | static hv hi hp =>
    obtain ⟨t, ht⟩ := hv
    simp only [arrayLenB, evalConst_complete hw ha ht, hi, hp, and_self, ↓reduceIte]

/-- Existing array-length consumers can use either certificates or the public checker. -/
theorem arrayLenB_iff {E : Env} {scope : Option String} {o : Syn (.opt .expr)} {n : Option Nat}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false) (ha : ConstsAcyclic E) :
    arrayLenB E scope o = some n ↔ ArrayLenOK E scope o n :=
  ⟨arrayLenB_sound, arrayLenB_complete hw ha⟩

/-- Refused static lengths have no ArrayLenOK witness under the same contract. -/
theorem arrayLenB_none_iff {E : Env} {scope : Option String} {o : Syn (.opt .expr)}
    (hw : E.decls.Pairwise fun a b => a.clash E b = false) (ha : ConstsAcyclic E) :
    arrayLenB E scope o = none ↔ ¬ ∃ n, ArrayLenOK E scope o n := by
  constructor
  · intro hn ⟨n, hl⟩
    rw [arrayLenB_complete hw ha hl] at hn
    cases hn
  · intro hn
    cases he : arrayLenB E scope o with
    | none => rfl
    | some n => exact False.elim (hn ⟨n, arrayLenB_sound he⟩)

/-- The array-length completeness corollary under the original resolved-unit contract. -/
theorem arrayLenB_resolved_complete {settings : Settings} {u : Syn .unit}
    (hw : WellFormed (resolveUnit settings u)) (ha : ConstsAcyclic u.env)
    {scope : Option String} {o : Syn (.opt .expr)} {n : Option Nat}
    (hl : ArrayLenOK u.env scope o n) : arrayLenB u.env scope o = some n :=
  arrayLenB_complete hw.noClash ha hl

end Solidity.Frontend.ConstantDepth
