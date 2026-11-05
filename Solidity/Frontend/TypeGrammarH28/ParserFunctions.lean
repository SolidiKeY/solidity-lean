import Solidity.Frontend.TypeGrammarH28.ParserFnAttrs

/-! Function-type constructor composition, including actual returns parsing,
capture/record order and constructive fuel. -/
namespace Solidity.Frontend.TypeGrammarH28.ParserFunction
open Solidity.Source Solidity.Frontend.Checked ParserBasic ParserCheck ParserPath ParserArray
  ParserContext ParserMapping ParserReady ParserParams ParserFnAttrs

/-- Parenthesis wrapper for arbitrary located token prefixes and larger fuel. -/
theorem paren_prefix (ps : Syn (.list .param)) (items : List (List Tok)) (layout : List Choice)
    (budget : Nat) (h : ListReady ps items layout budget) (fuel : Nat) (hf : budget + 1 ≤ fuel)
    (front rest : List Located) (hp : front.map Located.tok = parens (commaSep items))
    (ch : List Choice) (eof : Nat) :
    paramsParen fuel ⟨front ++ rest, ch, eof⟩ = .ok (ps, ⟨rest, layout.reverse ++ ch, eof⟩) := by
  obtain ⟨openToken, afterOpen, he, ho, ht⟩ := located_cons front _ _ hp
  obtain ⟨inner, closeToken, he', hi, hc⟩ := located_append afterOpen (commaSep items) [(.punct .rparen)] ht
  obtain ⟨c, d, hclose⟩ := located_one closeToken _ hc
  cases he
  cases he'
  cases hclose
  cases openToken with
  | mk tok a b =>
    cases ho
    have hpos : 1 ≤ fuel := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le budget)) hf
    have hpred : fuel - 1 + 1 = fuel := Nat.sub_add_cancel hpos
    have hb : budget ≤ fuel - 1 := Nat.le_sub_of_add_le hf
    have hs := params_paren_complete ps items layout budget h (fuel - 1) hb a b c d inner rest hi ch eof
    rw [hpred] at hs
    simpa only [List.cons_append, List.append_assoc, List.nil_append] using hs

def returnsTokens (items : List (List Tok)) : List Tok :=
  if items.isEmpty then [] else tk .returns ++ parens (commaSep items)

def ReturnsAt (rs : Syn (.list .param)) (items : List (List Tok)) (layout : List Choice) (budget : Nat) : Prop :=
  ∀ fuel : Nat, budget ≤ fuel → ∀ front rest : List Located,
    front.map Located.tok = returnsTokens items → Continuation rest → ∀ ch : List Choice, ∀ eof : Nat,
    returnsOpt fuel ⟨front ++ rest, ch, eof⟩ = .ok (rs, ⟨rest, layout.reverse ++ ch, eof⟩)

theorem returns_nil : ReturnsAt .nil [] [] 1 := by
  intro fuel hf front rest hp hb ch eof
  have he := located_nil front hp
  cases he
  have hs := continuation_no_returns (fuel - 1) rest hb ch eof
  rw [Nat.sub_add_cancel hf] at hs
  simpa only [List.nil_append, List.reverse_nil] using hs

theorem returns_cons (p : Syn .param) (ps : Syn (.list .param))
    (head : List Tok) (items : List (List Tok)) (layout : List Choice) (budget : Nat)
    (h : ListReady (.cons p ps) (head :: items) layout budget) :
    ReturnsAt (.cons p ps) (head :: items) layout (budget + 2) := by
  intro fuel hf front rest hp hb ch eof
  change front.map Located.tok = .kw .returns :: parens (commaSep (head :: items)) at hp
  obtain ⟨retToken, parenTokens, he, ht, hparen⟩ := located_cons front _ _ hp
  cases he
  cases retToken with
  | mk tok a b =>
    cases ht
    have hpos : 1 ≤ fuel := Nat.le_trans (by decide : 1 ≤ 2) (Nat.le_trans (Nat.le_add_left 2 budget) hf)
    have hpred : fuel - 1 + 1 = fuel := Nat.sub_add_cancel hpos
    have hf' : budget + 1 ≤ fuel - 1 := Nat.le_sub_of_add_le hf
    have hs := paren_prefix _ _ layout budget h (fuel - 1) hf' parenTokens rest hparen ch eof
    rw [← hpred]
    change (paramsParen (fuel - 1) ⟨parenTokens ++ rest, ch, eof⟩ >>= _) = _
    rw [hs]
    rfl

/-- Empty returns syntax remains refused, not identified with absent returns. -/
theorem empty_returns_refused (a b c d e f : Nat) (rest : List Located)
    (ch : List Choice) (eof : Nat) :
    returnsOpt 6 ⟨⟨.kw .returns, a, b⟩ :: ⟨.punct .lparen, c, d⟩ ::
      ⟨.punct .rparen, e, f⟩ :: rest, ch, eof⟩ =
      .error ⟨(⟨rest, ch, eof⟩ : St).pos, "empty returns list"⟩ := by
  rfl

theorem returns_from_list (rs : Syn (.list .param)) (items : List (List Tok))
    (layout : List Choice) (budget : Nat) (h : ListReady rs items layout budget) :
    ∃ rb : Nat, 1 ≤ rb ∧ ReturnsAt rs items layout rb ∧
      rb ≤ 16 * ((commaSep items).length + 1) + 3 := by
  cases h with
  | nil => exact ⟨1, Nat.le_refl 1, returns_nil, by decide⟩
  | cons p ps head hl pb items rl rb hpos hparser hprinter hbound tail =>
    have hr := ListReady.cons p ps head hl pb items rl rb hpos hparser hprinter hbound tail
    refine ⟨max pb rb + 2, Nat.le_trans (by decide : 1 ≤ 2) (Nat.le_add_left _ _),
      returns_cons p ps head items (hl ++ rl) (max pb rb) hr, ?_⟩
    exact Nat.add_le_add_right (list_ready_budget _ _ _ _ hr) 2

theorem returns_attr_boundary (items : List (List Tok)) (front rest : List Located)
    (hp : front.map Located.tok = returnsTokens items) (hb : Continuation rest) :
    AttrBoundary (front ++ rest) := by
  cases items with
  | nil =>
    have he := located_nil front hp
    cases he
    exact .finish rest hb
  | cons head items =>
    obtain ⟨first, tail, he, ht, hr⟩ := located_cons front _ _ hp
    cases he
    cases first with
    | mk tok a b =>
      cases ht
      exact .returns a b (tail ++ rest)

def fnTokens (p : List (List Tok)) (attrs : List Tok) (r : List (List Tok)) : List Tok :=
  tk .function ++ parens (commaSep p) ++ attrs ++ returnsTokens r

theorem capture_paren_prefix (ps : Syn (.list .param)) (items : List (List Tok)) (layout : List Choice)
    (budget : Nat) (h : ListReady ps items layout budget) (fuel : Nat) (hf : budget + 1 ≤ fuel)
    (front rest : List Located) (hp : front.map Located.tok = parens (commaSep items))
    (ch : List Choice) (eof : Nat) :
    capture (paramsParen fuel) ⟨front ++ rest, ch, eof⟩ = .ok ((ps, layout), ⟨rest, ch, eof⟩) := by
  have hs := paren_prefix ps items layout budget h fuel hf front rest hp [] eof
  simp only [List.append_nil] at hs
  unfold capture
  rw [hs]
  simp only [List.reverse_reverse]

theorem fn_body_complete (ps rs : Syn (.list .param)) (v : Option Visibility) (m : Option Mutability)
    (p r : List (List Tok)) (lp lr : List Choice) (bp br : Nat)
    (hp : ListReady ps p lp bp) (hr : ReturnsAt rs r lr br)
    (order : List Slot) (attrs : List Tok) (ha : arrange order (fnSingles v m) [] = some attrs)
    (fuel : Nat) (hf : bp + 1 ≤ fuel) (hfr : br ≤ fuel)
    (front rest : List Located) (hfront : front.map Located.tok = fnTokens p attrs r)
    (hb : Continuation rest) (ch : List Choice) (eof : Nat) :
    fnType (fuel + 1) ⟨front ++ rest, ch, eof⟩ =
      .ok (.fnType ps v m rs, ⟨rest, (.attrs order :: (lp ++ lr)).reverse ++ ch, eof⟩) := by
  simp only [fnTokens, tk, List.cons_append, List.nil_append, List.append_assoc] at hfront
  obtain ⟨first, afterFirst, he, ht, hafter⟩ := located_cons front _ _ hfront
  obtain ⟨paramsFront, afterParams, he', hparams, hafter'⟩ := located_append afterFirst
    (parens (commaSep p)) (attrs ++ returnsTokens r) hafter
  obtain ⟨attrsFront, returnsFront, he'', hattrs, hreturns⟩ := located_append afterParams attrs (returnsTokens r) hafter'
  cases he
  cases he'
  cases he''
  cases first with
  | mk tok a b =>
    cases ht
    have hpc := capture_paren_prefix ps p lp bp hp fuel hf paramsFront
      (attrsFront ++ (returnsFront ++ rest)) hparams ch eof
    have hac := arranged_attrs_complete v m order attrs ha attrsFront (returnsFront ++ rest) hattrs
      (returns_attr_boundary r returnsFront rest hreturns hb) ch eof
    have hrc := hr fuel hfr returnsFront rest hreturns hb (lp.reverse ++ (.attrs order :: ch)) eof
    simp only [List.cons_append, List.append_assoc] at *
    change (capture (paramsParen fuel)
      ⟨paramsFront ++ (attrsFront ++ (returnsFront ++ rest)), ch, eof⟩ >>= _) = _
    rw [hpc]
    change (fnTypeAttrs 3 none none [] ⟨attrsFront ++ (returnsFront ++ rest), ch, eof⟩ >>= _) = _
    rw [hac]
    change (returnsOpt fuel ⟨returnsFront ++ rest, lp.reverse ++ (.attrs order :: ch), eof⟩ >>= _) = _
    rw [hrc]
    simp only [List.reverse_cons, List.reverse_append, List.append_assoc, List.singleton_append]
    rfl

theorem fn_body_complete_ge (ps rs : Syn (.list .param)) (v : Option Visibility) (m : Option Mutability)
    (p r : List (List Tok)) (lp lr : List Choice) (bp br : Nat)
    (hp : ListReady ps p lp bp) (hr : ReturnsAt rs r lr br)
    (order : List Slot) (attrs : List Tok) (ha : arrange order (fnSingles v m) [] = some attrs)
    (fuel : Nat) (hf : max (bp + 1) br + 1 ≤ fuel)
    (front rest : List Located) (hfront : front.map Located.tok = fnTokens p attrs r)
    (hb : Continuation rest) (ch : List Choice) (eof : Nat) :
    fnType fuel ⟨front ++ rest, ch, eof⟩ =
      .ok (.fnType ps v m rs, ⟨rest, (.attrs order :: (lp ++ lr)).reverse ++ ch, eof⟩) := by
  have hpos : 1 ≤ fuel := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) hf
  have hpred : fuel - 1 + 1 = fuel := Nat.sub_add_cancel hpos
  have hm : max (bp + 1) br ≤ fuel - 1 := Nat.le_sub_of_add_le hf
  have hs := fn_body_complete ps rs v m p r lp lr bp br hp hr order attrs ha (fuel - 1)
    (Nat.le_trans (Nat.le_max_left _ _) hm) (Nat.le_trans (Nat.le_max_right _ _) hm)
    front rest hfront hb ch eof
  rw [hpred] at hs
  exact hs

theorem ready_fn (ps rs : Syn (.list .param)) (v : Option Visibility) (m : Option Mutability)
    (p r : List (List Tok)) (lp lr : List Choice) (bp br : Nat)
    (hp : ListReady ps p lp bp) (hr : ReturnsAt rs r lr br)
    (order : List Slot) (attrs : List Tok) (ha : arrange order (fnSingles v m) [] = some attrs) :
    ReadyAt (.fnType ps v m rs) (fnTokens p attrs r) (.attrs order :: (lp ++ lr))
      1 (max (bp + 1) br + 1) := by
  intro residual hf front rest hfront hb ch eof
  have hs := fn_body_complete_ge ps rs v m p r lp lr bp br hp hr order attrs ha
    residual hf front rest hfront hb ch eof
  simp only [fnTokens, tk, List.cons_append, List.nil_append, List.append_assoc] at hfront
  obtain ⟨first, tail, he, ht, hr⟩ := located_cons front _ _ hfront
  cases he
  cases first with
  | mk tok a b =>
    cases ht
    change (fnType residual ⟨⟨.kw .function, a, b⟩ :: (tail ++ rest), ch, eof⟩ >>= _) = _
    simp only [List.cons_append] at hs
    rw [hs]
    rfl

theorem parens_length (tokens : List Tok) : (parens tokens).length = tokens.length + 2 := by
  simp only [parens, pu, List.length_append, List.length_cons, List.length_nil,
    Nat.add_comm, Nat.add_left_comm]

theorem fn_params_length (p r : List (List Tok)) (attrs : List Tok) :
    (commaSep p).length + 1 ≤ (fnTokens p attrs r).length := by
  have hpar : (commaSep p).length + 1 ≤ (parens (commaSep p)).length := by
    rw [parens_length]
    exact Nat.succ_le_succ (Nat.le_succ _)
  unfold fnTokens
  rw [List.length_append, List.length_append, List.length_append]
  exact Nat.le_trans hpar (Nat.le_trans (Nat.le_add_left _ _)
    (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))

theorem fn_returns_length (p r : List (List Tok)) (attrs : List Tok) :
    (commaSep r).length + 1 ≤ (fnTokens p attrs r).length := by
  cases r with
  | nil => exact Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) (fn_params_length p [] attrs)
  | cons head r =>
    have ht : (commaSep (head :: r)).length + 1 ≤ (returnsTokens (head :: r)).length := by
      change (commaSep (head :: r)).length + 1 ≤ (tk .returns ++ parens (commaSep (head :: r))).length
      rw [List.length_append, parens_length]
      exact Nat.le_trans (Nat.succ_le_succ (Nat.le_succ _)) (Nat.le_add_left _ _)
    unfold fnTokens
    rw [List.length_append]
    exact Nat.le_trans ht (Nat.le_add_left _ _)

theorem fuel_slack (n total : Nat) (h : n + 1 ≤ total) :
    16 * (n + 1) + 5 ≤ 16 * (total + 1) := by
  have ha : 16 * (n + 1) + 5 ≤ 16 * (n + 1) + 16 := Nat.add_le_add_left (by decide : 5 ≤ 16) _
  have he : 16 * (n + 1) + 16 = 16 * (n + 1 + 1) := by
    simpa only [Nat.mul_one] using (Nat.mul_add 16 (n + 1) 1).symm
  rw [he] at ha
  exact Nat.le_trans ha (Nat.mul_le_mul_left 16 (Nat.succ_le_succ h))

theorem fn_budget (p r : List (List Tok)) (attrs : List Tok) (bp br : Nat)
    (hp : bp ≤ 16 * ((commaSep p).length + 1) + 1)
    (hr : br ≤ 16 * ((commaSep r).length + 1) + 3) :
    max (bp + 1) br + 1 + 1 ≤ 16 * ((fnTokens p attrs r).length + 1) := by
  have hb : bp + 1 + 1 + 1 ≤ 16 * ((fnTokens p attrs r).length + 1) := by
    have he := Nat.add_le_add_right hp 3
    exact Nat.le_trans he (Nat.le_trans (Nat.add_le_add_left (by decide : 4 ≤ 5) _)
      (fuel_slack _ _ (fn_params_length p r attrs)))
  have hb' : br + 1 + 1 ≤ 16 * ((fnTokens p attrs r).length + 1) := by
    have he := Nat.add_le_add_right hr 2
    exact Nat.le_trans he (fuel_slack _ _ (fn_returns_length p r attrs))
  rcases Nat.le_total (bp + 1) br with hm | hm
  · rw [Nat.max_eq_right hm]
    exact hb'
  · rw [Nat.max_eq_left hm]
    exact hb

theorem params_prec_node (ps : Syn (.list .param)) : ps.precNode = true := by
  cases ps <;> rfl

theorem fn_prec_converse (ps rs : Syn (.list .param)) (v : Option Visibility) (m : Option Mutability)
    (h : (Syn.fnType ps v m rs).prec = true) : ps.prec = true ∧ rs.prec = true := by
  change (true && (true && ps.all Syn.precNode && rs.all Syn.precNode)) = true at h
  have he := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2
  have hp : ps.all Syn.precNode = true := (Bool.and_eq_true_iff.mp he.1).2
  constructor
  · unfold Syn.prec; rw [params_prec_node, hp]; rfl
  · unfold Syn.prec; rw [params_prec_node, he.2]; rfl

theorem fn_yield_attrs (ps rs : Syn (.list .param)) (v : Option Visibility) (m : Option Mutability)
    (order : List Slot) (input : List Choice) :
    (Syn.fnType ps v m rs).yield (.attrs order :: input) =
      (ps.yield input >>= fun p =>
        attrsP (fnSingles v m) [] order p.2 >>= fun a =>
        rs.yield a.2 >>= fun r => some ([fnTokens p.1 a.1 r.1], r.2)) := rfl

/-- Actual original yield decomposition, including all originally unused
choices; no canonical-layout or parser success is assumed. -/
theorem fn_yield_decompose (ps rs : Syn (.list .param)) (v : Option Visibility) (m : Option Mutability)
    (input remaining : List Choice) (chunks : List (List Tok))
    (h : (Syn.fnType ps v m rs).yield input = some (chunks, remaining)) :
    ∃ order : List Slot, ∃ start middle : List Choice,
    ∃ p r : List (List Tok), ∃ attrs : List Tok,
      input = .attrs order :: start ∧ ps.yield start = some (p, middle) ∧
      arrange order (fnSingles v m) [] = some attrs ∧ rs.yield middle = some (r, remaining) ∧
      chunks = [fnTokens p attrs r] := by
  cases input with
  | nil => cases h
  | cons choice start =>
    cases choice with
    | frags lengths => cases h
    | layoutFirst b => cases h
    | attrs order =>
      rw [fn_yield_attrs] at h
      cases hp : ps.yield start with
      | none => rw [hp] at h; cases h
      | some pair =>
        cases pair with
        | mk p middle =>
          rw [hp] at h
          change (attrsP (fnSingles v m) [] order middle >>= fun a =>
            rs.yield a.2 >>= fun r => some ([fnTokens p a.1 r.1], r.2)) = some (chunks, remaining) at h
          change ((arrange order (fnSingles v m) []).map (fun a => (a, middle)) >>= fun a =>
            rs.yield a.2 >>= fun r => some ([fnTokens p a.1 r.1], r.2)) = some (chunks, remaining) at h
          cases ha : arrange order (fnSingles v m) [] with
          | none => rw [ha] at h; cases h
          | some attrs =>
            rw [ha] at h
            change (rs.yield middle >>= fun r => some ([fnTokens p attrs r.1], r.2)) = some (chunks, remaining) at h
            cases hr : rs.yield middle with
            | none => rw [hr] at h; cases h
            | some result =>
              cases result with
              | mk r afterReturns =>
                rw [hr] at h
                change some ([fnTokens p attrs r], afterReturns) = some (chunks, remaining) at h
                have he := Prod.mk.inj (Option.some.inj h)
                cases he.2
                exact ⟨order, start, middle, p, r, attrs, rfl, hp, ha, hr, he.1.symm⟩

/-- Function constructor closure from strict parameter/return-list evidence.
The result is not a premise and every original successful layout is observed. -/
theorem prefix_fn (ps rs : Syn (.list .param)) (v : Option Visibility) (m : Option Mutability)
    (hp : ParamsCertified ps) (hr : ParamsCertified rs) : PrefixCertified (.fnType ps v m rs) := by
  intro input chunks remaining hy hprec
  obtain ⟨order, start, middle, p, r, attrs, he, hpy, ha, hry, hc⟩ :=
    fn_yield_decompose ps rs v m input remaining chunks hy
  obtain ⟨hpp, hrp⟩ := fn_prec_converse ps rs v m hprec
  obtain ⟨lp, bp, hps⟩ := hp start p middle hpy hpp
  obtain ⟨lr, rb, hrs⟩ := hr middle r remaining hry hrp
  obtain ⟨br, hbrpos, hreturns, hbr⟩ := returns_from_list rs r lr rb hrs
  have hready := ready_fn ps rs v m p r lp lr bp br hps hreturns order attrs ha
  have hprint := exact_fnType ps rs v m order lp lr p r attrs
    (list_ready_exact ps p lp bp hps) (list_ready_exact rs r lr rb hrs) ha
  have hbudget := fn_budget p r attrs bp br (list_ready_budget ps p lp bp hps) hbr
  have hflat : chunks.flatten = fnTokens p attrs r := by
    rw [hc, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [hflat]
  exact ⟨.attrs order :: (lp ++ lr), 1, max (bp + 1) br + 1,
    Nat.succ_le_succ (Nat.zero_le _), hready, hprint, hbudget⟩

theorem certified_fn (ps rs : Syn (.list .param)) (v : Option Visibility) (m : Option Mutability)
    (hp : ParamsCertified ps) (hr : ParamsCertified rs) : Certified (.fnType ps v m rs) := by
  exact prefix_to_certified _ (prefix_fn ps rs v m hp hr)

theorem fn_parseType_iff (ps rs : Syn (.list .param)) (v : Option Visibility) (m : Option Mutability)
    (hp : ParamsCertified ps) (hr : ParamsCertified rs) (src : Bytes) :
    parseType src = .ok (.fnType ps v m rs) ↔ ∃ pieces : List Piece, lex src = .ok pieces ∧
      ∃ layout : List Choice, (Syn.fnType ps v m rs).toks layout = some (tokensOf pieces) ∧
        (Syn.fnType ps v m rs).prec = true := by
  exact certified_parseType_iff _ (certified_fn ps rs v m hp hr) src

/-- A genuine unbounded family: arbitrary elementary parameter/return lists,
all data locations/names and all function visibility/mutability choices. -/
theorem fn_elem_prefix (p r : List (Elem × Option DataLoc × Option String))
    (v : Option Visibility) (m : Option Mutability) :
    PrefixCertified (.fnType (elemParams p) v m (elemParams r)) := by
  exact prefix_fn _ _ v m (elem_params_certified p) (elem_params_certified r)

theorem fn_elem_prec (p r : List (Elem × Option DataLoc × Option String))
    (v : Option Visibility) (m : Option Mutability) :
    (Syn.fnType (elemParams p) v m (elemParams r)).prec = true := by
  have hp : (elemParams p).all Syn.precNode = true := (Bool.and_eq_true_iff.mp (elem_params_prec p)).2
  have hr : (elemParams r).all Syn.precNode = true := (Bool.and_eq_true_iff.mp (elem_params_prec r)).2
  change (true && (true && (elemParams p).all Syn.precNode && (elemParams r).all Syn.precNode)) = true
  rw [hp, hr]
  rfl

theorem fn_elem_tokens (p r : List (Elem × Option DataLoc × Option String))
    (v : Option Visibility) (m : Option Mutability) (order : List Slot) (attrs : List Tok)
    (ha : arrange order (fnSingles v m) [] = some attrs) :
    (Syn.fnType (elemParams p) v m (elemParams r)).toks [.attrs order] =
      some (fnTokens (elemParamItems p) attrs (elemParamItems r)) := by
  have hy := exact_fnType (elemParams p) (elemParams r) v m order [] []
    (elemParamItems p) (elemParamItems r) attrs (elem_params_exact p) (elem_params_exact r) ha
  have ht := exact_toks _ _ _ hy
  simpa only [fnTokens, returnsTokens, List.nil_append, List.flatten_cons, List.flatten_nil,
    List.append_nil] using ht

theorem fn_elem_checked_inhabited (p r : List (Elem × Option DataLoc × Option String))
    (v : Option Visibility) (m : Option Mutability) :
    ∃ order : List Slot, ∃ tokens : List Tok, ∃ layout : List Choice,
      (Syn.fnType (elemParams p) v m (elemParams r)).toks [.attrs order] = some tokens ∧
      parseCatLocated typeName 0 (witnessLocations tokens) =
        .ok (.fnType (elemParams p) v m (elemParams r), layout) := by
  obtain ⟨order, attrs, ha, _⟩ := attrs_inhabited v m
  have ht := fn_elem_tokens p r v m order attrs ha
  obtain ⟨layout, hc⟩ := certified_checked _ (prefix_to_certified _ (fn_elem_prefix p r v m))
    [.attrs order] _ ht (fn_elem_prec p r v m) (witnessLocations _) 0 (witness_locations_tokens _)
  exact ⟨order, _, layout, ht, hc⟩

/-- An arbitrary-depth function control with the previous type in both a
parameter and a return; original intrinsic syntax, not a new producer. -/
def nestedFn (base : Syn .typeName) (v : Option Visibility) (m : Option Mutability)
    (loc : Option DataLoc) (name : Option String) : Nat → Syn .typeName
  | 0 => base
  | depth + 1 =>
    let child := nestedFn base v m loc name depth
    let params := Syn.cons (.param child loc name) .nil
    .fnType params v m params

theorem nested_fn_prefix (base : Syn .typeName) (hc : PrefixCertified base)
    (v : Option Visibility) (m : Option Mutability) (loc : Option DataLoc) (name : Option String)
    (depth : Nat) : PrefixCertified (nestedFn base v m loc name depth) := by
  induction depth with
  | zero => exact hc
  | succ depth ih =>
    have hp := params_cons_certified (.param (nestedFn base v m loc name depth) loc name) .nil
      (param_certified _ ih loc name) params_nil_certified
    exact prefix_fn _ _ v m hp hp

theorem nested_fn_prec (base : Syn .typeName) (hc : base.prec = true)
    (v : Option Visibility) (m : Option Mutability) (loc : Option DataLoc) (name : Option String)
    (depth : Nat) : (nestedFn base v m loc name depth).prec = true := by
  induction depth with
  | zero => exact hc
  | succ depth ih =>
    have hall : (nestedFn base v m loc name depth).all Syn.precNode = true := (Bool.and_eq_true_iff.mp ih).2
    change (true && (true &&
      (true && (true && (nestedFn base v m loc name depth).all Syn.precNode) && true) &&
      (true && (true && (nestedFn base v m loc name depth).all Syn.precNode) && true))) = true
    rw [hall]
    rfl

theorem nested_fn_exact (base : Syn .typeName) (layout : List Choice) (tokens : List Tok)
    (hc : YieldExact base layout [tokens]) (v : Option Visibility) (m : Option Mutability)
    (loc : Option DataLoc) (name : Option String) (depth : Nat) :
    ∃ output : List Choice, ∃ ts : List Tok,
      YieldExact (nestedFn base v m loc name depth) output [ts] := by
  induction depth with
  | zero => exact ⟨layout, tokens, hc⟩
  | succ depth ih =>
    obtain ⟨lc, tc, hx⟩ := ih
    have hp := exact_param (nestedFn base v m loc name depth) loc name lc [tc] hx
    have hp' : YieldExact (.param (nestedFn base v m loc name depth) loc name) lc [paramTokens tc loc name] := by
      simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using hp
    have hl := exact_params_cons (.param (nestedFn base v m loc name depth) loc name) .nil lc []
      [paramTokens tc loc name] [] hp' exact_params_nil
    have hl' : YieldExact (.cons (.param (nestedFn base v m loc name depth) loc name) .nil)
        lc [paramTokens tc loc name] := by
      simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hl
    obtain ⟨order, attrs, ha, _⟩ := attrs_inhabited v m
    have hf := exact_fnType _ _ v m order lc lc [paramTokens tc loc name] [paramTokens tc loc name]
      attrs hl' hl' ha
    exact ⟨.attrs order :: (lc ++ lc), fnTokens [paramTokens tc loc name] attrs [paramTokens tc loc name], hf⟩

theorem nested_fn_elem_checked (e : Elem) (v : Option Visibility) (m : Option Mutability)
    (loc : Option DataLoc) (name : Option String) (depth : Nat) :
    ∃ layout : List Choice, ∃ tokens : List Tok, ∃ parsed : List Choice,
      (nestedFn (.elem e) v m loc name depth).toks layout = some tokens ∧
      parseCatLocated typeName 0 (witnessLocations tokens) =
        .ok (nestedFn (.elem e) v m loc name depth, parsed) := by
  obtain ⟨layout, tokens, hx⟩ := nested_fn_exact (.elem e) [] e.toks (exact_elem e) v m loc name depth
  have ht : (nestedFn (.elem e) v m loc name depth).toks layout = some tokens := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using exact_toks _ _ _ hx
  have hp := nested_fn_prefix (.elem e) (prefix_elem e) v m loc name depth
  obtain ⟨parsed, hc⟩ := certified_checked _ (prefix_to_certified _ hp) layout tokens ht
    (nested_fn_prec (.elem e) rfl v m loc name depth) (witnessLocations tokens) 0 (witness_locations_tokens tokens)
  exact ⟨layout, tokens, parsed, ht, hc⟩

theorem fn_arrays_prefix (ps rs : Syn (.list .param)) (v : Option Visibility) (m : Option Mutability)
    (hp : ParamsCertified ps) (hr : ParamsCertified rs) (depth : Nat) :
    PrefixCertified (dynamicTree (.fnType ps v m rs) depth) := by
  exact prefix_dynamic _ (prefix_fn ps rs v m hp hr) depth

theorem function_two_refused (a b c d : Nat) (rest : List Located) (ch : List Choice) (eof : Nat) :
    typeName 2 ⟨⟨.kw .function, a, b⟩ :: ⟨.punct .lparen, c, d⟩ :: rest, ch, eof⟩ =
      .error ⟨c, "nesting too deep"⟩ := by
  rfl

#print axioms paren_prefix
#print axioms returns_nil
#print axioms returns_cons
#print axioms empty_returns_refused
#print axioms returns_from_list
#print axioms returns_attr_boundary
#print axioms capture_paren_prefix
#print axioms fn_body_complete
#print axioms fn_body_complete_ge
#print axioms ready_fn
#print axioms parens_length
#print axioms fn_params_length
#print axioms fn_returns_length
#print axioms fuel_slack
#print axioms fn_budget
#print axioms params_prec_node
#print axioms fn_prec_converse
#print axioms fn_yield_attrs
#print axioms fn_yield_decompose
#print axioms prefix_fn
#print axioms certified_fn
#print axioms fn_parseType_iff
#print axioms fn_elem_prefix
#print axioms fn_elem_prec
#print axioms fn_elem_tokens
#print axioms fn_elem_checked_inhabited
#print axioms nested_fn_prefix
#print axioms nested_fn_prec
#print axioms nested_fn_exact
#print axioms nested_fn_elem_checked
#print axioms fn_arrays_prefix
#print axioms function_two_refused
end Solidity.Frontend.TypeGrammarH28.ParserFunction
