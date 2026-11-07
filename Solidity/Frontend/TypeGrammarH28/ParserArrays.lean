import Solidity.Frontend.TypeGrammarH28.ParserPaths
import Solidity.Frontend.TypeGrammarH28.Composition

/-! Array spine parser composition. Length expressions remain independent
read-only parser atoms; no evaluation or expression identity claim is made. -/
namespace Solidity.Frontend.TypeGrammarH28.ParserArray
open Solidity.Source Solidity.Frontend.Checked ParserBasic ParserPath

/-- Raw elementary token parsing before a recognized non-payable boundary. -/
theorem elem_name_token (e : Elem) (a b : Nat) (rest : List Located)
    (ch : List Choice) (eof : Nat)
    (hpay : eat (.kw .payable) ⟨rest, ch, eof⟩ = .ok (false, ⟨rest, ch, eof⟩)) :
    elemTypeName ⟨⟨.elem e, a, b⟩ :: rest, ch, eof⟩ = .ok (e, ⟨rest, ch, eof⟩) := by
  cases e <;> first
    | rfl
    | (change (eat (.kw .payable) ⟨rest, ch, eof⟩ >>= _) = _; rw [hpay]; rfl)

theorem elem_name_payable (a b c d : Nat) (rest : List Located)
    (ch : List Choice) (eof : Nat) :
    elemTypeName ⟨⟨.elem .address, a, b⟩ :: ⟨.kw .payable, c, d⟩ :: rest, ch, eof⟩ =
      .ok (.addressPayable, ⟨rest, ch, eof⟩) := rfl

theorem elem_name_complete (e : Elem) (front rest : List Located)
    (ch : List Choice) (eof : Nat) (hp : front.map Located.tok = e.toks)
    (hpay : eat (.kw .payable) ⟨rest, ch, eof⟩ = .ok (false, ⟨rest, ch, eof⟩)) :
    elemTypeName ⟨front ++ rest, ch, eof⟩ = .ok (e, ⟨rest, ch, eof⟩) := by
  cases e <;> first
    | (obtain ⟨a, b, he⟩ := located_one front _ hp
       cases he
       exact elem_name_token _ a b rest ch eof hpay)
    | (obtain ⟨head, tail, he, hh, ht⟩ := located_cons front (.elem .address) [.kw .payable] hp
       obtain ⟨c, d, he'⟩ := located_one tail _ ht
       cases he
       cases he'
       cases head with
       | mk tok a b =>
         cases hh
         exact elem_name_payable a b c d rest ch eof)

theorem elem_dispatch (fuel : Nat) (e : Elem) (a b : Nat) (rest : List Located)
    (ch : List Choice) (eof : Nat) :
    typeName (fuel + 1) ⟨⟨.elem e, a, b⟩ :: rest, ch, eof⟩ =
      (elemTypeName ⟨⟨.elem e, a, b⟩ :: rest, ch, eof⟩ >>= fun r =>
        typeSuffix fuel (.elem r.1) r.2) := rfl

/-- This composition lemma exposes only the independent elementary spelling
and the genuine suffix parse. It is not full array completeness by assumption. -/
theorem elem_then_suffix (e : Elem) (fuel : Nat) (front rest : List Located)
    (ch : List Choice) (eof : Nat) (hp : front.map Located.tok = e.toks)
    (hpay : eat (.kw .payable) ⟨rest, ch, eof⟩ = .ok (false, ⟨rest, ch, eof⟩)) :
    typeName (fuel + 1) ⟨front ++ rest, ch, eof⟩ = typeSuffix fuel (.elem e) ⟨rest, ch, eof⟩ := by
  have he := elem_name_complete e front rest ch eof hp hpay
  cases e <;> first
    | (obtain ⟨a, b, hf⟩ := located_one front _ hp
       cases hf
       simp only [List.cons_append, List.nil_append] at he
       simp only [List.cons_append, List.nil_append]
       rw [elem_dispatch, he]
       rfl)
    | (obtain ⟨head, tail, hf, hh, ht⟩ := located_cons front (.elem .address) [.kw .payable] hp
       obtain ⟨c, d, ht'⟩ := located_one tail _ ht
       cases hf
       cases ht'
       cases head with
       | mk tok a b =>
         cases hh
         simp only [List.cons_append, List.nil_append] at he
         simp only [List.cons_append, List.nil_append]
         rw [elem_dispatch, he]
         rfl)

theorem brackets_no_payable (k : Nat) (ls : List Located) (ch : List Choice) (eof : Nat)
    (h : ls.map Located.tok = dynamicBrackets k) :
    eat (.kw .payable) ⟨ls, ch, eof⟩ = .ok (false, ⟨ls, ch, eof⟩) := by
  cases k with
  | zero =>
    have he := located_nil ls h
    cases he
    rfl
  | succ k =>
    obtain ⟨head, tail, he, ht, hr⟩ := located_cons ls _ _ h
    cases he
    cases head with
    | mk tok a b => cases ht; rfl

theorem brackets_path_stop (k : Nat) (ls : List Located) (ch : List Choice) (eof : Nat)
    (h : ls.map Located.tok = dynamicBrackets k) :
    pathStep ⟨ls, ch, eof⟩ = .ok (none, ⟨ls, ch, eof⟩) := by
  cases k with
  | zero =>
    have he := located_nil ls h
    cases he
    rfl
  | succ k =>
    obtain ⟨head, tail, he, ht, hr⟩ := located_cons ls _ _ h
    cases he
    cases head with
    | mk tok a b => cases ht; rfl

theorem dynamic_elem_complete (e : Elem) (k n : Nat) (ls : List Located)
    (ch : List Choice) (eof : Nat)
    (h : ls.map Located.tok = e.toks ++ dynamicBrackets k) :
    typeName (n + k + 2) ⟨ls, ch, eof⟩ =
      .ok (dynamicTree (.elem e) k, ⟨[], ch, eof⟩) := by
  obtain ⟨front, rest, he, hf, hr⟩ := located_append ls e.toks (dynamicBrackets k) h
  cases he
  rw [elem_then_suffix e (n + k + 1) front rest ch eof hf (brackets_no_payable k rest ch eof hr)]
  have hs := suffix_dynamic_complete k n (.elem e) rest [] ch eof hr rfl
  simpa only [List.append_nil] using hs

theorem user_then_suffix (p : IdPath) (fuel : Nat) (front rest : List Located)
    (ch : List Choice) (eof : Nat) (hp : front.map Located.tok = p.toks)
    (hstop : pathStep ⟨rest, ch, eof⟩ = .ok (none, ⟨rest, ch, eof⟩)) :
    typeName (fuel + 1) ⟨front ++ rest, ch, eof⟩ = typeSuffix fuel (.userType p) ⟨rest, ch, eof⟩ := by
  have hh := path_complete p front rest ch eof hp hstop
  obtain ⟨head, tail, he, ht, hr⟩ := located_cons front _ _ hp
  cases he
  cases head with
  | mk tok a b =>
    cases ht
    simp only [List.cons_append] at hh
    change (idPath ⟨⟨.ident p.head, a, b⟩ :: (tail ++ rest), ch, eof⟩ >>= _) = _
    rw [hh]
    rfl

theorem dynamic_user_complete (p : IdPath) (k n : Nat) (ls : List Located)
    (ch : List Choice) (eof : Nat)
    (h : ls.map Located.tok = p.toks ++ dynamicBrackets k) :
    typeName (n + k + 2) ⟨ls, ch, eof⟩ =
      .ok (dynamicTree (.userType p) k, ⟨[], ch, eof⟩) := by
  obtain ⟨front, rest, he, hf, hr⟩ := located_append ls p.toks (dynamicBrackets k) h
  cases he
  rw [user_then_suffix p (n + k + 1) front rest ch eof hf (brackets_path_stop k rest ch eof hr)]
  have hs := suffix_dynamic_complete k n (.userType p) rest [] ch eof hr rfl
  simpa only [List.append_nil] using hs

theorem dynamic_yield (base : Syn .typeName) (k : Nat) (ts : List Tok)
    (choices remaining : List Choice) (h : base.yield choices = some ([ts], remaining)) :
    (dynamicTree base k).yield choices = some ([ts ++ dynamicBrackets k], remaining) := by
  induction k generalizing base ts with
  | zero => simpa only [dynamicTree, dynamicBrackets, List.append_nil] using h
  | succ k ih =>
    have ha : (Syn.array base .none).yield choices =
        some ([ts ++ [.punct .lbrack, .punct .rbrack]], remaining) := by
      change (base.yield choices >>= _) = _
      rw [h]
      change some ([(ts ++ []) ++ [.punct .lbrack] ++ [] ++ [.punct .rbrack]], remaining) = _
      simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
    have hh := ih (.array base .none) (ts ++ [.punct .lbrack, .punct .rbrack]) ha
    simpa only [dynamicTree, dynamicBrackets, List.append_assoc, List.cons_append, List.nil_append] using hh

theorem dynamic_toks (base : Syn .typeName) (k : Nat) (ts : List Tok)
    (h : base.yield [] = some ([ts], [])) :
    (dynamicTree base k).toks [] = some (ts ++ dynamicBrackets k) := by
  have hh := dynamic_yield base k ts [] [] h
  unfold Syn.toks
  rw [hh]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

theorem dynamic_prec (base : Syn .typeName) (k : Nat) (h : base.prec = true) :
    (dynamicTree base k).prec = true := by
  induction k generalizing base with
  | zero => exact h
  | succ k ih =>
    apply ih (.array base .none)
    have ha : base.all Syn.precNode = true := (Bool.and_eq_true_iff.mp h).2
    change (true && (true && base.all Syn.precNode && true)) = true
    rw [ha]
    rfl

theorem brackets_budget (k : Nat) : k ≤ (dynamicBrackets k).length := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    change k + 1 ≤ (dynamicBrackets k).length + 1 + 1
    exact Nat.le_trans (Nat.succ_le_succ ih) (Nat.le_succ _)

theorem frozen_budget (m : Nat) : m + 2 ≤ 16 * (m + 1) := by
  calc
    m + 2 ≤ (m + 1) + (m + 1) := Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le m)) (m + 1)
    _ = 2 * (m + 1) := (Nat.two_mul (m + 1)).symm
    _ ≤ 16 * (m + 1) := Nat.mul_le_mul_right (m + 1) (by decide : 2 ≤ 16)

theorem dynamic_frozen_budget (k : Nat) (baseTokens : List Tok) (ls : List Located)
    (h : ls.map Located.tok = baseTokens ++ dynamicBrackets k) :
    k + 2 ≤ 16 * (ls.length + 1) := by
  have hl : ls.length = baseTokens.length + (dynamicBrackets k).length := by
    have he := congrArg List.length h
    simpa only [List.length_map, List.length_append] using he
  have hk : k ≤ ls.length := by
    rw [hl]
    exact Nat.le_trans (brackets_budget k) (Nat.le_add_left _ _)
  exact Nat.le_trans (Nat.add_le_add_right hk 2) (frozen_budget ls.length)

theorem dynamic_elem_complete_ge (e : Elem) (k fuel : Nat) (hf : k + 2 ≤ fuel)
    (ls : List Located) (ch : List Choice) (eof : Nat)
    (h : ls.map Located.tok = e.toks ++ dynamicBrackets k) :
    typeName fuel ⟨ls, ch, eof⟩ = .ok (dynamicTree (.elem e) k, ⟨[], ch, eof⟩) := by
  have he : fuel - (k + 2) + k + 2 = fuel :=
    (Nat.add_assoc _ _ _).trans (Nat.sub_add_cancel hf)
  rw [← he]
  exact dynamic_elem_complete e k _ ls ch eof h

theorem dynamic_user_complete_ge (p : IdPath) (k fuel : Nat) (hf : k + 2 ≤ fuel)
    (ls : List Located) (ch : List Choice) (eof : Nat)
    (h : ls.map Located.tok = p.toks ++ dynamicBrackets k) :
    typeName fuel ⟨ls, ch, eof⟩ = .ok (dynamicTree (.userType p) k, ⟨[], ch, eof⟩) := by
  have he : fuel - (k + 2) + k + 2 = fuel :=
    (Nat.add_assoc _ _ _).trans (Nat.sub_add_cancel hf)
  rw [← he]
  exact dynamic_user_complete p k _ ls ch eof h

theorem dynamic_elem_checked (e : Elem) (k : Nat) (ls : List Located) (eof : Nat)
    (h : ls.map Located.tok = e.toks ++ dynamicBrackets k) :
    parseCatLocated typeName eof ls = .ok (dynamicTree (.elem e) k, []) := by
  have hf := dynamic_frozen_budget k e.toks ls h
  have hr := dynamic_elem_complete_ge e k _ hf ls [] eof h
  apply ParserCheck.checked_category_converse typeName eof ls _ ⟨[], [], eof⟩ hr rfl
  · have hy := dynamic_toks (.elem e) k e.toks rfl
    change (dynamicTree (.elem e) k).toks [] = some (ls.map Located.tok)
    rw [hy, h]
  · exact dynamic_prec (.elem e) k rfl

theorem dynamic_user_checked (p : IdPath) (k : Nat) (ls : List Located) (eof : Nat)
    (h : ls.map Located.tok = p.toks ++ dynamicBrackets k) :
    parseCatLocated typeName eof ls = .ok (dynamicTree (.userType p) k, []) := by
  have hf := dynamic_frozen_budget k p.toks ls h
  have hr := dynamic_user_complete_ge p k _ hf ls [] eof h
  apply ParserCheck.checked_category_converse typeName eof ls _ ⟨[], [], eof⟩ hr rfl
  · have hy := dynamic_toks (.userType p) k p.toks rfl
    change (dynamicTree (.userType p) k).toks [] = some (ls.map Located.tok)
    rw [hy, h]
  · exact dynamic_prec (.userType p) k rfl

theorem parseType_dynamic_elem (e : Elem) (k : Nat) (src : Bytes) (ps : List Piece)
    (hlex : lex src = .ok ps) (ht : tokensOf ps = e.toks ++ dynamicBrackets k) :
    parseType src = .ok (dynamicTree (.elem e) k) := by
  have hl : ((locate .sol 0 ps).map Prod.fst).map Located.tok = e.toks ++ dynamicBrackets k := by
    rw [List.map_map]
    change (locate .sol 0 ps).map (fun x => x.1.tok) = _
    rw [locate_toks]
    exact ht
  unfold parseType parseCat
  rw [hlex]
  change (parseCatLocated typeName src.length ((locate .sol 0 ps).map Prod.fst)).map Prod.fst = _
  rw [dynamic_elem_checked e k _ src.length hl]
  rfl

theorem parseType_dynamic_user (p : IdPath) (k : Nat) (src : Bytes) (ps : List Piece)
    (hlex : lex src = .ok ps) (ht : tokensOf ps = p.toks ++ dynamicBrackets k) :
    parseType src = .ok (dynamicTree (.userType p) k) := by
  have hl : ((locate .sol 0 ps).map Prod.fst).map Located.tok = p.toks ++ dynamicBrackets k := by
    rw [List.map_map]
    change (locate .sol 0 ps).map (fun x => x.1.tok) = _
    rw [locate_toks]
    exact ht
  unfold parseType parseCat
  rw [hlex]
  change (parseCatLocated typeName src.length ((locate .sol 0 ps).map Prod.fst)).map Prod.fst = _
  rw [dynamic_user_checked p k _ src.length hl]
  rfl

theorem dynamic_elem_layout (e : Elem) (k : Nat) (layout : List Choice) :
    (dynamicTree (.elem e) k).toks layout =
      if layout.isEmpty then some (e.toks ++ dynamicBrackets k) else none := by
  have hy := dynamic_yield (.elem e) k e.toks layout layout rfl
  unfold Syn.toks
  rw [hy]
  cases layout with
  | nil => simp only [List.flatten_cons, List.flatten_nil, List.append_nil]; rfl
  | cons a rest => rfl

theorem dynamic_user_layout (p : IdPath) (k : Nat) (layout : List Choice) :
    (dynamicTree (.userType p) k).toks layout =
      if layout.isEmpty then some (p.toks ++ dynamicBrackets k) else none := by
  have hy := dynamic_yield (.userType p) k p.toks layout layout rfl
  unfold Syn.toks
  rw [hy]
  cases layout with
  | nil => simp only [List.flatten_cons, List.flatten_nil, List.append_nil]; rfl
  | cons a rest => rfl

theorem dynamic_elem_checked_yield (e : Elem) (k : Nat) (layout : List Choice)
    (ts : List Tok) (ls : List Located) (eof : Nat)
    (hy : (dynamicTree (.elem e) k).toks layout = some ts)
    (hl : ls.map Located.tok = ts) :
    parseCatLocated typeName eof ls = .ok (dynamicTree (.elem e) k, []) := by
  rw [dynamic_elem_layout] at hy
  cases layout with
  | cons a rest => cases hy
  | nil =>
    have ht : e.toks ++ dynamicBrackets k = ts := Option.some.inj hy
    exact dynamic_elem_checked e k ls eof (hl.trans ht.symm)

theorem dynamic_user_checked_yield (p : IdPath) (k : Nat) (layout : List Choice)
    (ts : List Tok) (ls : List Located) (eof : Nat)
    (hy : (dynamicTree (.userType p) k).toks layout = some ts)
    (hl : ls.map Located.tok = ts) :
    parseCatLocated typeName eof ls = .ok (dynamicTree (.userType p) k, []) := by
  rw [dynamic_user_layout] at hy
  cases layout with
  | cons a rest => cases hy
  | nil =>
    have ht : p.toks ++ dynamicBrackets k = ts := Option.some.inj hy
    exact dynamic_user_checked p k ls eof (hl.trans ht.symm)

/-- Identity of actual dynamically nested types, even at different depths.
The completeness obligations used here were independently proved above. -/
theorem dynamic_elem_yield_unique (e f : Elem) (k j : Nat)
    (left right : List Choice) (ts : List Tok)
    (hl : (dynamicTree (.elem e) k).toks left = some ts)
    (hr : (dynamicTree (.elem f) j).toks right = some ts) :
    dynamicTree (.elem e) k = dynamicTree (.elem f) j ∧
      LayoutEquivalent (dynamicTree (.elem e) k) left right := by
  let ls := ParserCheck.witnessLocations ts
  have hm : ls.map Located.tok = ts := ParserCheck.witness_locations_tokens ts
  have hp := dynamic_elem_checked_yield e k left ts ls 0 hl hm
  have hq := dynamic_elem_checked_yield f j right ts ls 0 hr hm
  have he : dynamicTree (.elem e) k = dynamicTree (.elem f) j :=
    (Prod.mk.inj (Except.ok.inj (hp.symm.trans hq))).1
  refine ⟨he, ts, hl, ?_⟩
  rw [he]
  exact hr

theorem dynamic_user_yield_unique (p q : IdPath) (k j : Nat)
    (left right : List Choice) (ts : List Tok)
    (hl : (dynamicTree (.userType p) k).toks left = some ts)
    (hr : (dynamicTree (.userType q) j).toks right = some ts) :
    dynamicTree (.userType p) k = dynamicTree (.userType q) j ∧
      LayoutEquivalent (dynamicTree (.userType p) k) left right := by
  let ls := ParserCheck.witnessLocations ts
  have hm : ls.map Located.tok = ts := ParserCheck.witness_locations_tokens ts
  have hp := dynamic_user_checked_yield p k left ts ls 0 hl hm
  have hq := dynamic_user_checked_yield q j right ts ls 0 hr hm
  have he : dynamicTree (.userType p) k = dynamicTree (.userType q) j :=
    (Prod.mk.inj (Except.ok.inj (hp.symm.trans hq))).1
  refine ⟨he, ts, hl, ?_⟩
  rw [he]
  exact hr

theorem dynamic_elem_user_yield_unique (e : Elem) (p : IdPath) (k j : Nat)
    (left right : List Choice) (ts : List Tok)
    (hl : (dynamicTree (.elem e) k).toks left = some ts)
    (hr : (dynamicTree (.userType p) j).toks right = some ts) :
    dynamicTree (.elem e) k = dynamicTree (.userType p) j ∧
      LayoutEquivalent (dynamicTree (.elem e) k) left right := by
  let ls := ParserCheck.witnessLocations ts
  have hm : ls.map Located.tok = ts := ParserCheck.witness_locations_tokens ts
  have hp := dynamic_elem_checked_yield e k left ts ls 0 hl hm
  have hq := dynamic_user_checked_yield p j right ts ls 0 hr hm
  have he : dynamicTree (.elem e) k = dynamicTree (.userType p) j :=
    (Prod.mk.inj (Except.ok.inj (hp.symm.trans hq))).1
  refine ⟨he, ts, hl, ?_⟩
  rw [he]
  exact hr

/-- The suffix fuel bound is substantive: one less unit fails after all
bracket pairs, at the original EOF position. -/
theorem suffix_dynamic_insufficient (k : Nat) (base : Syn .typeName)
    (ls : List Located) (ch : List Choice) (eof : Nat)
    (h : ls.map Located.tok = dynamicBrackets k) :
    typeSuffix k base ⟨ls, ch, eof⟩ = .error ⟨eof, "nesting too deep"⟩ := by
  induction k generalizing base ls with
  | zero =>
    have he := located_nil ls h
    cases he
    rfl
  | succ k ih =>
    obtain ⟨first, more, he, hf, hm⟩ := located_cons ls _ _ h
    obtain ⟨second, rest, he', hs, hr⟩ := located_cons more _ _ hm
    cases he
    cases he'
    cases first with
    | mk tok a b =>
      cases hf
      cases second with
      | mk tok c d =>
        cases hs
        change typeSuffix k (.array base .none) ⟨rest, ch, eof⟩ = _
        exact ih (.array base .none) rest hr

theorem dynamic_elem_insufficient (e : Elem) (k : Nat) (ls : List Located)
    (ch : List Choice) (eof : Nat)
    (h : ls.map Located.tok = e.toks ++ dynamicBrackets k) :
    typeName (k + 1) ⟨ls, ch, eof⟩ = .error ⟨eof, "nesting too deep"⟩ := by
  obtain ⟨front, rest, he, hf, hr⟩ := located_append ls e.toks (dynamicBrackets k) h
  cases he
  rw [elem_then_suffix e k front rest ch eof hf (brackets_no_payable k rest ch eof hr)]
  exact suffix_dynamic_insufficient k (.elem e) rest ch eof hr

theorem dynamic_user_insufficient (p : IdPath) (k : Nat) (ls : List Located)
    (ch : List Choice) (eof : Nat)
    (h : ls.map Located.tok = p.toks ++ dynamicBrackets k) :
    typeName (k + 1) ⟨ls, ch, eof⟩ = .error ⟨eof, "nesting too deep"⟩ := by
  obtain ⟨front, rest, he, hf, hr⟩ := located_append ls p.toks (dynamicBrackets k) h
  cases he
  rw [user_then_suffix p k front rest ch eof hf (brackets_path_stop k rest ch eof hr)]
  exact suffix_dynamic_insufficient k (.userType p) rest ch eof hr

#print axioms elem_name_token
#print axioms elem_name_payable
#print axioms elem_name_complete
#print axioms elem_dispatch
#print axioms elem_then_suffix
#print axioms brackets_no_payable
#print axioms brackets_path_stop
#print axioms dynamic_elem_complete
#print axioms user_then_suffix
#print axioms dynamic_user_complete
#print axioms dynamic_yield
#print axioms dynamic_toks
#print axioms dynamic_prec
#print axioms brackets_budget
#print axioms frozen_budget
#print axioms dynamic_frozen_budget
#print axioms dynamic_elem_complete_ge
#print axioms dynamic_user_complete_ge
#print axioms dynamic_elem_checked
#print axioms dynamic_user_checked
#print axioms parseType_dynamic_elem
#print axioms parseType_dynamic_user
#print axioms dynamic_elem_layout
#print axioms dynamic_user_layout
#print axioms dynamic_elem_checked_yield
#print axioms dynamic_user_checked_yield
#print axioms dynamic_elem_yield_unique
#print axioms dynamic_user_yield_unique
#print axioms dynamic_elem_user_yield_unique
#print axioms suffix_dynamic_insufficient
#print axioms dynamic_elem_insufficient
#print axioms dynamic_user_insufficient
end Solidity.Frontend.TypeGrammarH28.ParserArray
