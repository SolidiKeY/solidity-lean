import Solidity.Frontend.Static.Consts

/-! # Determinism of typed constant evaluation, with no contract

`TEval` and `NamedConst` are syntax-directed: at most one value, for every
environment (no clash-freedom or acyclicity premise). -/
namespace Solidity.Frontend.ConstantDepth
open Solidity.Source Solidity.Frontend.Static

mutual
theorem teval_det {E : Env} : {s : Option String} → {e : Syn .expr} → {v w : TVal} →
    TEval E s e v → TEval E s e w → v = w
  | _, _, _, _, .rational h, h2 => by
    cases h2 with
    | rational h' => rw [h] at h'; cases h'; rfl
    | named hn => rw [typed_const_none (.named hn) rfl] at h; cases h
    | paren hp => rw [typed_const_none (.paren hp) rfl] at h; cases h
    | unary hop hx hl hr hr' => rw [typed_const_none (.unary hop hx hl hr hr') rfl] at h; cases h
    | binary hk ha hb hs ht hla hlb hr hr' =>
      rw [typed_const_none (.binary hk ha hb hs ht hla hlb hr hr') rfl] at h; cases h
  | _, _, _, _, .named hn, h2 => by
    cases h2 with
    | rational h' => rw [typed_const_none (.named hn) rfl] at h'; cases h'
    | named hn' =>
      obtain ⟨rfl, rfl⟩ := nconst_det hn hn'
      rfl
    | binary hk => cases hk
  | _, _, _, _, .paren hp, h2 => by
    cases h2 with
    | rational h' => rw [typed_const_none (.paren hp) rfl] at h'; cases h'
    | paren hp' => exact teval_det hp hp'
    | binary hk => cases hk
  | _, _, _, _, .unary hop hx hl hr hr', h2 => by
    cases h2 with
    | rational h' => rw [typed_const_none (.unary hop hx hl hr hr') rfl] at h'; cases h'
    | unary _ hx' hl' hr₂ hr₂' =>
      have e := teval_det hx hx'
      cases e
      rw [hl] at hl'; cases hl'
      rw [hr] at hr₂; cases hr₂
      rw [hr'] at hr₂'; cases hr₂'
      rfl
    | binary hk => cases hk
  | _, _, _, _, .binary hk ha hb hs ht hla hlb hr hr', h2 => by
    cases h2 with
    | rational h' => rw [typed_const_none (.binary hk ha hb hs ht hla hlb hr hr') rfl] at h'; cases h'
    | named => cases hk
    | paren => cases hk
    | unary => cases hk
    | binary hk' ha' hb' _ ht' hla' hlb' hr₂ hr₂' =>
      rw [hk] at hk'; cases hk'
      have e1 := teval_det ha ha'
      have e2 := teval_det hb hb'
      subst e1; subst e2
      rw [ht] at ht'; cases ht'
      rw [hla] at hla'; cases hla'
      rw [hlb] at hlb'; cases hlb'
      rw [hr] at hr₂; cases hr₂
      rw [hr'] at hr₂'; cases hr₂'
      rfl

theorem nconst_det {E : Env} : {s : Option String} → {x : String} → {t t' : IntTy} → {q q' : Q} →
    NamedConst E s x t q → NamedConst E s x t' q' → t = t' ∧ q = q'
  | _, _, _, _, _, _, .mk hl hc he hv hev hq, .mk hl' _ he' hv' hev' hq' => by
    rw [hl] at hl'; cases hl'
    rw [he] at he'; cases he'
    rw [hv] at hv'; cases hv'
    have e := teval_det hev hev'
    subst e
    rw [hq] at hq'; cases hq'
    exact ⟨rfl, rfl⟩
end

/-- Array-length certificates are unique in every environment. -/
theorem arrayLen_det {E : Env} {scope : Option String} {o : Syn (.opt .expr)} {n m : Option Nat}
    (hn : ArrayLenOK E scope o n) (hm : ArrayLenOK E scope o m) : n = m := by
  cases hn with
  | dynamic => cases hm; rfl
  | static hv _ _ =>
    cases hm with
    | static hv' _ _ =>
      obtain ⟨t, ht⟩ := hv
      obtain ⟨t', ht'⟩ := hv'
      have e := teval_det ht ht'
      cases e
      rfl

end Solidity.Frontend.ConstantDepth
