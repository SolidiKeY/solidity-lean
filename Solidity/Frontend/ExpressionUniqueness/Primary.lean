import Solidity.Frontend.ExpressionUniqueness.Fragments

/-!
# Reconstruction of deterministic primary token yields

These results use existing intrinsic constructors and fully consumed layouts.
The general state lemma is instantiated with kernel-checked yield equations;
no root split or expression uniqueness is a hypothesis.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem derives_pure_yield {c : Cat} (e : Syn c) (items : List (List Tok))
    (h : ∀ L, e.yield L = some (items, L)) (ts : List Tok) :
    e.Derives ts ↔ ts = items.flatten := by
  constructor
  · intro ⟨L, ht⟩
    simp only [Syn.toks, h] at ht
    cases L with
    | nil => exact (Option.some.inj ht).symm
    | cons choice rest => cases ht
  · intro ht
    refine ⟨[], ?_⟩
    simp only [Syn.toks, h, ht]

theorem derives_ident (name : String) (ts : List Tok) :
    (Syn.ident name).Derives ts ↔ ts = [.ident name] := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using
    derives_pure_yield (.ident name) [[.ident name]] (fun _ => rfl) ts

theorem derives_boolean (b : Bool) (ts : List Tok) :
    (Syn.lit (.bool b)).Derives ts ↔ ts = [.bool b] := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using
    derives_pure_yield (.lit (.bool b)) [[.bool b]] (fun _ => rfl) ts

theorem derives_number (n : NumLit) (ts : List Tok) :
    (Syn.lit (.num n)).Derives ts ↔ ts = [.num n] := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using
    derives_pure_yield (.lit (.num n)) [[.num n]] (fun _ => rfl) ts

theorem derives_unit (n : NumLit) (u : Denom) (ts : List Tok) :
    (Syn.litUnit n u).Derives ts ↔ ts = [.num n, .denom u] := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using
    derives_pure_yield (.litUnit n u) [[.num n, .denom u]] (fun _ => rfl) ts

theorem derives_elementary (e : Elem) (he : e ≠ .addressPayable) (ts : List Tok) :
    (Syn.elemType e he).Derives ts ↔ ts = [.elem e] := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using
    derives_pure_yield (.elemType e he) [[.elem e]] (fun _ => rfl) ts

theorem ident_same_yield (a b : String) (ts : List Tok)
    (ha : (Syn.ident a).Derives ts) (hb : (Syn.ident b).Derives ts) : a = b := by
  have ht : [Tok.ident a] = [.ident b] :=
    ((derives_ident a ts).mp ha).symm.trans ((derives_ident b ts).mp hb)
  exact Tok.ident.inj (List.cons.inj ht).1

theorem boolean_same_yield (a b : Bool) (ts : List Tok)
    (ha : (Syn.lit (.bool a)).Derives ts) (hb : (Syn.lit (.bool b)).Derives ts) : a = b := by
  have ht : [Tok.bool a] = [.bool b] :=
    ((derives_boolean a ts).mp ha).symm.trans ((derives_boolean b ts).mp hb)
  exact Tok.bool.inj (List.cons.inj ht).1

theorem number_same_yield (a b : NumLit) (ts : List Tok)
    (ha : (Syn.lit (.num a)).Derives ts) (hb : (Syn.lit (.num b)).Derives ts) : a = b := by
  have ht : [Tok.num a] = [.num b] :=
    ((derives_number a ts).mp ha).symm.trans ((derives_number b ts).mp hb)
  exact Tok.num.inj (List.cons.inj ht).1

/-- Unwrap a single-item yield while enforcing complete layout consumption. -/
theorem derives_single_item {c : Cat} (e : Syn c) (pr : Pr (List Tok))
    (hy : ∀ L, e.yield L = (pr L).map (fun r => ([r.1], r.2)))
    (ts : List Tok) (h : e.Derives ts) : ∃ L, pr L = some (ts, []) := by
  obtain ⟨L, ht⟩ := h
  cases hp : pr L with
  | none =>
    simp only [Syn.toks, hy, hp, Option.map_none] at ht
    cases ht
  | some result =>
    rcases result with ⟨tokens, rest⟩
    simp only [Syn.toks, hy, hp, Option.map_some] at ht
    cases rest with
    | nil =>
      have he : tokens = ts := by
        simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using Option.some.inj ht
      exact ⟨L, he ▸ hp⟩
    | cons choice rest => cases ht

theorem str_yield_map (bs : Bytes) (L : List Choice) :
    (Syn.lit (.str bs)).yield L =
      (fragsP Tok.str bs L).map (fun r => ([r.1], r.2)) := by
  change ((fragsP Tok.str bs L).bind fun r => some ([r.1], r.2)) = _
  cases fragsP Tok.str bs L <;> rfl

theorem str_payload (bs : Bytes) (ts : List Tok)
    (h : (Syn.lit (.str bs)).Derives ts) : ts.flatMap stringPayload = bs := by
  obtain ⟨L, hL⟩ := derives_single_item (.lit (.str bs))
    (fragsP Tok.str bs) (str_yield_map bs) ts h
  exact fragsP_reconstruct Tok.str (fun _ => rfl) bs L [] ts hL

theorem str_same_yield (a b : Bytes) (ts : List Tok)
    (ha : (Syn.lit (.str a)).Derives ts)
    (hb : (Syn.lit (.str b)).Derives ts) : a = b :=
  (str_payload a ts ha).symm.trans (str_payload b ts hb)

theorem hexStr_yield_map (bs : Bytes) (L : List Choice) :
    (Syn.lit (.hexStr bs)).yield L =
      (fragsP Tok.hexStr bs L).map (fun r => ([r.1], r.2)) := by
  change ((fragsP Tok.hexStr bs L).bind fun r => some ([r.1], r.2)) = _
  cases fragsP Tok.hexStr bs L <;> rfl

theorem hexStr_payload (bs : Bytes) (ts : List Tok)
    (h : (Syn.lit (.hexStr bs)).Derives ts) : ts.flatMap stringPayload = bs := by
  obtain ⟨L, hL⟩ := derives_single_item (.lit (.hexStr bs))
    (fragsP Tok.hexStr bs) (hexStr_yield_map bs) ts h
  exact fragsP_reconstruct Tok.hexStr (fun _ => rfl) bs L [] ts hL

theorem hexStr_same_yield (a b : Bytes) (ts : List Tok)
    (ha : (Syn.lit (.hexStr a)).Derives ts)
    (hb : (Syn.lit (.hexStr b)).Derives ts) : a = b :=
  (hexStr_payload a ts ha).symm.trans (hexStr_payload b ts hb)

theorem unicodeStr_yield_map (bs : Bytes) (L : List Choice) :
    (Syn.lit (.unicodeStr bs)).yield L =
      (fragsP Tok.unicodeStr bs L).map (fun r => ([r.1], r.2)) := by
  change ((fragsP Tok.unicodeStr bs L).bind fun r => some ([r.1], r.2)) = _
  cases fragsP Tok.unicodeStr bs L <;> rfl

theorem unicodeStr_payload (bs : Bytes) (ts : List Tok)
    (h : (Syn.lit (.unicodeStr bs)).Derives ts) : ts.flatMap stringPayload = bs := by
  obtain ⟨L, hL⟩ := derives_single_item (.lit (.unicodeStr bs))
    (fragsP Tok.unicodeStr bs) (unicodeStr_yield_map bs) ts h
  exact fragsP_reconstruct Tok.unicodeStr (fun _ => rfl) bs L [] ts hL

theorem unicodeStr_same_yield (a b : Bytes) (ts : List Tok)
    (ha : (Syn.lit (.unicodeStr a)).Derives ts)
    (hb : (Syn.lit (.unicodeStr b)).Derives ts) : a = b :=
  (unicodeStr_payload a ts ha).symm.trans (unicodeStr_payload b ts hb)

def literalKind : Lit → Nat
  | .bool _ => 0
  | .num _ => 1
  | .str _ => 2
  | .hexStr _ => 3
  | .unicodeStr _ => 4

def tokenLiteralKind : Tok → Option Nat
  | .bool _ => some 0
  | .num _ => some 1
  | .str _ => some 2
  | .hexStr _ => some 3
  | .unicodeStr _ => some 4
  | _ => none

theorem literal_head_kind (l : Lit) (ts : List Tok) (h : (Syn.lit l).Derives ts) :
    ∃ t rest, ts = t :: rest ∧ tokenLiteralKind t = some (literalKind l) := by
  cases l with
  | bool b => exact ⟨.bool b, [], (derives_boolean b ts).mp h, rfl⟩
  | num n => exact ⟨.num n, [], (derives_number n ts).mp h, rfl⟩
  | str bs =>
    obtain ⟨L, hL⟩ := derives_single_item (.lit (.str bs))
      (fragsP Tok.str bs) (str_yield_map bs) ts h
    obtain ⟨cs, _, ht, hne⟩ := fragsP_spec Tok.str bs L [] ts hL
    cases cs with
    | nil => exact False.elim (hne rfl)
    | cons first rest => exact ⟨.str first, rest.map Tok.str, ht, rfl⟩
  | hexStr bs =>
    obtain ⟨L, hL⟩ := derives_single_item (.lit (.hexStr bs))
      (fragsP Tok.hexStr bs) (hexStr_yield_map bs) ts h
    obtain ⟨cs, _, ht, hne⟩ := fragsP_spec Tok.hexStr bs L [] ts hL
    cases cs with
    | nil => exact False.elim (hne rfl)
    | cons first rest => exact ⟨.hexStr first, rest.map Tok.hexStr, ht, rfl⟩
  | unicodeStr bs =>
    obtain ⟨L, hL⟩ := derives_single_item (.lit (.unicodeStr bs))
      (fragsP Tok.unicodeStr bs) (unicodeStr_yield_map bs) ts h
    obtain ⟨cs, _, ht, hne⟩ := fragsP_spec Tok.unicodeStr bs L [] ts hL
    cases cs with
    | nil => exact False.elim (hne rfl)
    | cons first rest => exact ⟨.unicodeStr first, rest.map Tok.unicodeStr, ht, rfl⟩

theorem literal_kind_determined (a b : Lit) (ts : List Tok)
    (ha : (Syn.lit a).Derives ts) (hb : (Syn.lit b).Derives ts) :
    literalKind a = literalKind b := by
  obtain ⟨ta, ra, hta, hka⟩ := literal_head_kind a ts ha
  obtain ⟨tb, rb, htb, hkb⟩ := literal_head_kind b ts hb
  have hh : ta = tb := (List.cons.inj (hta.symm.trans htb)).1
  rw [hh, hkb] at hka
  exact (Option.some.inj hka).symm

/-- All literal families, including cross-family disjointness and arbitrary
string lengths/layouts. This is a component, not the public expression theorem. -/
theorem literal_same_yield (a b : Lit) (ts : List Tok)
    (ha : (Syn.lit a).Derives ts) (hb : (Syn.lit b).Derives ts) : a = b := by
  have hk := literal_kind_determined a b ts ha hb
  cases a <;> cases b <;> simp only [literalKind] at hk
  all_goals try omega
  all_goals first
    | exact congrArg Lit.bool (boolean_same_yield _ _ ts ha hb)
    | exact congrArg Lit.num (number_same_yield _ _ ts ha hb)
    | exact congrArg Lit.str (str_same_yield _ _ ts ha hb)
    | exact congrArg Lit.hexStr (hexStr_same_yield _ _ ts ha hb)
    | exact congrArg Lit.unicodeStr (unicodeStr_same_yield _ _ ts ha hb)

end Solidity.Frontend.ExpressionUniqueness
