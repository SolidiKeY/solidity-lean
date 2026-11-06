import Solidity.Frontend.TypeGrammarH28.ParserMapping

/-! Dynamic array closure around mappings. No expression or producer is
changed; the strict mapping value retains its independent certificate. -/
namespace Solidity.Frontend.TypeGrammarH28.ParserDynamicClosure
open Solidity.Source Solidity.Frontend.Checked ParserBasic ParserPath ParserArray ParserContext ParserMapping

theorem dynamic_succ (base : Syn .typeName) (k : Nat) :
    dynamicTree base (k + 1) = .array (dynamicTree base k) .none := by
  induction k generalizing base with
  | zero => rfl
  | succ k ih => exact ih (.array base .none)

theorem brackets_snoc (k : Nat) :
    dynamicBrackets (k + 1) = dynamicBrackets k ++ [.punct .lbrack, .punct .rbrack] := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun ts : List Tok => .punct .lbrack :: .punct .rbrack :: ts) ih

theorem array_none_yield (base : Syn .typeName) (layout : List Choice) :
    (Syn.array base .none).yield layout =
      (base.yield layout >>= fun r => some ([r.1.flatten ++ [.punct .lbrack, .punct .rbrack]], r.2)) := by
  change (base.yield layout >>= _) = _
  cases hy : base.yield layout with
  | none => rfl
  | some pair =>
    cases pair with
    | mk chunks remaining =>
      change some ([chunks.flatten ++ [.punct .lbrack] ++ [] ++ [.punct .rbrack]], remaining) = _
      simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
      rfl

theorem array_none_toks (base : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (hy : base.toks layout = some tokens) :
    (Syn.array base .none).toks layout = some (tokens ++ [.punct .lbrack, .punct .rbrack]) := by
  obtain ⟨chunks, hb, ht⟩ := toks_yield_decompose base layout tokens hy
  unfold Syn.toks
  rw [array_none_yield, hb]
  change some ((chunks.flatten ++ [.punct .lbrack, .punct .rbrack]) ++ []) = _
  rw [List.append_nil, ht]

theorem array_none_toks_decompose (base : Syn .typeName) (layout : List Choice) (tokens : List Tok)
    (h : (Syn.array base .none).toks layout = some tokens) :
    ∃ body : List Tok, base.toks layout = some body ∧ body ++ [.punct .lbrack, .punct .rbrack] = tokens := by
  unfold Syn.toks at h
  rw [array_none_yield] at h
  cases hy : base.yield layout with
  | none => rw [hy] at h; cases h
  | some pair =>
    cases pair with
    | mk chunks remaining =>
      rw [hy] at h
      cases remaining with
      | nil =>
        change some ((chunks.flatten ++ [.punct .lbrack, .punct .rbrack]) ++ []) = some tokens at h
        rw [List.append_nil] at h
        refine ⟨chunks.flatten, ?_, Option.some.inj h⟩
        unfold Syn.toks
        rw [hy]
      | cons choice rest => cases h

theorem dynamic_toks_from_base (base : Syn .typeName) (k : Nat) (tokens : List Tok) (layout : List Choice)
    (hy : base.toks layout = some tokens) :
    (dynamicTree base k).toks layout = some (tokens ++ dynamicBrackets k) := by
  induction k with
  | zero => simpa only [dynamicTree, dynamicBrackets, List.append_nil] using hy
  | succ k ih =>
    have ha := array_none_toks (dynamicTree base k) (tokens ++ dynamicBrackets k) layout ih
    simpa only [dynamic_succ, brackets_snoc, List.append_assoc] using ha

theorem dynamic_toks_decompose (base : Syn .typeName) (k : Nat) (layout : List Choice) (tokens : List Tok)
    (hy : (dynamicTree base k).toks layout = some tokens) :
    ∃ body : List Tok, base.toks layout = some body ∧ body ++ dynamicBrackets k = tokens := by
  induction k generalizing tokens with
  | zero => exact ⟨tokens, hy, List.append_nil tokens⟩
  | succ k ih =>
    rw [dynamic_succ] at hy
    obtain ⟨inner, hi, he⟩ := array_none_toks_decompose (dynamicTree base k) layout tokens hy
    obtain ⟨body, hb, ht⟩ := ih inner hi
    refine ⟨body, hb, ?_⟩
    calc
      body ++ dynamicBrackets (k + 1) = (body ++ dynamicBrackets k) ++ [.punct .lbrack, .punct .rbrack] := by
        rw [brackets_snoc, List.append_assoc]
      _ = inner ++ [.punct .lbrack, .punct .rbrack] := congrArg (fun ts => ts ++ [.punct .lbrack, .punct .rbrack]) ht
      _ = tokens := he

theorem array_none_prec_converse (base : Syn .typeName)
    (h : (Syn.array base .none).prec = true) : base.prec = true := by
  change (true && (true && base.all Syn.precNode && true)) = true at h
  have hi : (true && base.all Syn.precNode && true) = true := (Bool.and_eq_true_iff.mp h).2
  have ha : base.all Syn.precNode = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hi).1).2
  unfold Syn.prec
  rw [type_prec_node, ha]
  rfl

theorem dynamic_prec_converse (base : Syn .typeName) (k : Nat)
    (h : (dynamicTree base k).prec = true) : base.prec = true := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [dynamic_succ] at h
    exact ih (array_none_prec_converse (dynamicTree base k) h)

/-- Raw mapping parsing is composed before suffix consumption, so no premise
asks a greedy typeName parser to stop before an opening array bracket. -/
theorem dynamic_mapping_prefix (value : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (budget k n : Nat) (hc : CompleteAt value tokens layout budget)
    (key : MapKey) (kn vn : Option String) (front rest : List Located)
    (hp : front.map Located.tok = mappingTokens key kn tokens vn ++ dynamicBrackets k)
    (hb : ParserContext.Boundary rest) (ch : List Choice) (eof : Nat) :
    typeName (n + budget + k + 2) ⟨front ++ rest, ch, eof⟩ =
      .ok (dynamicTree (.mapping key kn value vn) k, ⟨rest, layout.reverse ++ ch, eof⟩) := by
  obtain ⟨body, suffix, he, hm, hs⟩ := located_append front (mappingTokens key kn tokens vn) (dynamicBrackets k) hp
  cases he
  rw [List.append_assoc]
  have hf : budget ≤ n + budget + k := Nat.le_trans (Nat.le_add_left budget n) (Nat.le_add_right (n + budget) k)
  have hmap := mapping_body_complete value tokens layout budget (n + budget + k) hc hf key kn vn body (suffix ++ rest) hm ch eof
  rw [mapping_tokens_cons] at hm
  obtain ⟨head, tail, he', ht, hr⟩ := located_cons body _ _ hm
  cases he'
  cases head with
  | mk tok ma mb =>
    cases ht
    simp only [List.cons_append] at hmap
    rw [List.cons_append, mapping_dispatch, hmap]
    exact suffix_dynamic_complete k (n + budget) (.mapping key kn value vn) suffix rest
      (layout.reverse ++ ch) eof hs (boundary_no_suffix rest hb (layout.reverse ++ ch) eof)

theorem complete_dynamic_mapping (value : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (budget k : Nat) (hc : CompleteAt value tokens layout budget)
    (key : MapKey) (kn vn : Option String) :
    CompleteAt (dynamicTree (.mapping key kn value vn) k)
      (mappingTokens key kn tokens vn ++ dynamicBrackets k) layout (budget + k + 2) := by
  intro fuel hf front rest hp hb ch eof
  have he : fuel - (budget + k + 2) + budget + k + 2 = fuel := by
    simpa only [Nat.add_assoc] using (Nat.sub_add_cancel hf)
  rw [← he]
  exact dynamic_mapping_prefix value tokens layout budget k _ hc key kn vn front rest hp hb ch eof

theorem dynamic_mapping_budget (budget k : Nat) (tokens : List Tok)
    (hb : budget ≤ 16 * (tokens.length + 1)) (key : MapKey) (kn vn : Option String) :
    budget + k + 2 ≤ 16 * ((mappingTokens key kn tokens vn ++ dynamicBrackets k).length + 1) := by
  have hm := mapping_budget budget tokens hb key kn vn
  have hk : k ≤ 16 * (dynamicBrackets k).length :=
    Nat.le_trans (brackets_budget k) (Nat.le_mul_of_pos_left (dynamicBrackets k).length (by decide : 0 < 16))
  calc
    budget + k + 2 = (budget + 2) + k := Nat.add_right_comm budget k 2
    _ ≤ 16 * ((mappingTokens key kn tokens vn).length + 1) + 16 * (dynamicBrackets k).length := Nat.add_le_add hm hk
    _ = 16 * (((mappingTokens key kn tokens vn).length + 1) + (dynamicBrackets k).length) :=
      (Nat.mul_add 16 _ _).symm
    _ = 16 * (((mappingTokens key kn tokens vn).length + (dynamicBrackets k).length) + 1) :=
      congrArg (fun n => 16 * n) (Nat.add_right_comm (mappingTokens key kn tokens vn).length 1 (dynamicBrackets k).length)
    _ = 16 * ((mappingTokens key kn tokens vn ++ dynamicBrackets k).length + 1) := by rw [List.length_append]

theorem certified_dynamic_mapping (value : Syn .typeName) (hc : Certified value)
    (key : MapKey) (kn vn : Option String) (k : Nat) : Certified (dynamicTree (.mapping key kn value vn) k) := by
  intro input tokens hy hp
  obtain ⟨body, hb, ht⟩ := dynamic_toks_decompose (.mapping key kn value vn) k input tokens hy
  obtain ⟨values, hv, hm⟩ := mapping_toks_decompose value key kn vn input body hb
  have hvp := mapping_prec_converse value key kn vn (dynamic_prec_converse (.mapping key kn value vn) k hp)
  obtain ⟨layout, budget, hc', hy', hbudget⟩ := hc input values hv hvp
  have he : mappingTokens key kn values vn ++ dynamicBrackets k = tokens :=
    (congrArg (fun ts => ts ++ dynamicBrackets k) hm).trans ht
  refine ⟨layout, budget + k + 2, ?_, ?_, ?_⟩
  · have hraw := complete_dynamic_mapping value values layout budget k hc' key kn vn
    rw [he] at hraw
    exact hraw
  · have hmap := mapping_toks value values layout hy' key kn vn
    have hwhole := dynamic_toks_from_base (.mapping key kn value vn) k _ layout hmap
    rw [he] at hwhole
    exact hwhole
  · have hbound := dynamic_mapping_budget budget k values hbudget key kn vn
    rw [he] at hbound
    exact hbound

/-- A proof-only control family over actual Syn values: arbitrary mapping and
dynamic-array interleavings. Function/static forms remain separate obligations;
this family is never substituted for the assignment's original language. -/
inductive DynamicMappingGrammar : Syn .typeName → Prop where
  | elem (e : Elem) (depth : Nat) : DynamicMappingGrammar (dynamicTree (.elem e) depth)
  | user (p : IdPath) (depth : Nat) : DynamicMappingGrammar (dynamicTree (.userType p) depth)
  | mapping (key : MapKey) (kn : Option String) (value : Syn .typeName) (vn : Option String)
      (depth : Nat) (child : DynamicMappingGrammar value) :
      DynamicMappingGrammar (dynamicTree (.mapping key kn value vn) depth)

theorem grammar_certified (t : Syn .typeName) (h : DynamicMappingGrammar t) : Certified t := by
  induction h with
  | elem e depth => exact certified_dynamic_elem e depth
  | user p depth => exact certified_dynamic_user p depth
  | mapping key kn value vn depth child ih => exact certified_dynamic_mapping value ih key kn vn depth

theorem grammar_prec (t : Syn .typeName) (h : DynamicMappingGrammar t) : t.prec = true := by
  induction h with
  | elem e depth => exact dynamic_prec (.elem e) depth rfl
  | user p depth => exact dynamic_prec (.userType p) depth rfl
  | mapping key kn value vn depth child ih =>
    exact dynamic_prec (.mapping key kn value vn) depth (mapping_prec value ih key kn vn)

theorem grammar_yield_inhabited (t : Syn .typeName) (h : DynamicMappingGrammar t) :
    ∃ tokens : List Tok, t.toks [] = some tokens := by
  induction h with
  | elem e depth => exact ⟨_, dynamic_toks (.elem e) depth e.toks rfl⟩
  | user p depth => exact ⟨_, dynamic_toks (.userType p) depth p.toks rfl⟩
  | mapping key kn value vn depth child ih =>
    obtain ⟨tokens, ht⟩ := ih
    have hm := mapping_toks value tokens [] ht key kn vn
    exact ⟨_, dynamic_toks_from_base (.mapping key kn value vn) depth _ [] hm⟩

theorem grammar_checked_inhabited (t : Syn .typeName) (h : DynamicMappingGrammar t) :
    ∃ tokens : List Tok, t.toks [] = some tokens ∧
      ∃ layout : List Choice, parseCatLocated typeName 0 (ParserCheck.witnessLocations tokens) = .ok (t, layout) := by
  obtain ⟨tokens, ht⟩ := grammar_yield_inhabited t h
  exact ⟨tokens, ht, certified_checked t (grammar_certified t h) [] tokens ht (grammar_prec t h)
    _ 0 (ParserCheck.witness_locations_tokens tokens)⟩

theorem grammar_yield_unique (t u : Syn .typeName) (ht : DynamicMappingGrammar t) (hu : DynamicMappingGrammar u)
    (left right : List Choice) (tokens : List Tok)
    (hl : t.toks left = some tokens) (hr : u.toks right = some tokens) :
    t = u ∧ LayoutEquivalent t left right := by
  exact certified_yield_unique t u (grammar_certified t ht) (grammar_certified u hu)
    left right tokens hl hr (grammar_prec t ht) (grammar_prec u hu)

theorem grammar_parseType_iff (t : Syn .typeName) (h : DynamicMappingGrammar t) (src : Bytes) :
    parseType src = .ok t ↔ ∃ ps : List Piece, lex src = .ok ps ∧
      ∃ layout : List Choice, t.toks layout = some (tokensOf ps) ∧ t.prec = true := by
  exact certified_parseType_iff t (grammar_certified t h) src

/-- A genuine negative yield control for every member of this inhabited
control family: no node consumes any layout choice, so extras are refused. -/
theorem grammar_no_unused_layout (t : Syn .typeName) (h : DynamicMappingGrammar t)
    (choice : Choice) (rest : List Choice) : t.toks (choice :: rest) = none := by
  induction h with
  | elem e depth =>
    rw [dynamic_elem_layout]
    rfl
  | user p depth =>
    rw [dynamic_user_layout]
    rfl
  | mapping key kn value vn depth child ih =>
    cases hy : (dynamicTree (.mapping key kn value vn) depth).toks (choice :: rest) with
    | none => rfl
    | some tokens =>
      obtain ⟨body, hb, ht⟩ := dynamic_toks_decompose (.mapping key kn value vn) depth (choice :: rest) tokens hy
      obtain ⟨values, hv, hm⟩ := mapping_toks_decompose value key kn vn (choice :: rest) body hb
      rw [ih] at hv
      cases hv

#print axioms dynamic_succ
#print axioms brackets_snoc
#print axioms array_none_yield
#print axioms array_none_toks
#print axioms array_none_toks_decompose
#print axioms dynamic_toks_from_base
#print axioms dynamic_toks_decompose
#print axioms array_none_prec_converse
#print axioms dynamic_prec_converse
#print axioms dynamic_mapping_prefix
#print axioms complete_dynamic_mapping
#print axioms dynamic_mapping_budget
#print axioms certified_dynamic_mapping
#print axioms grammar_certified
#print axioms grammar_prec
#print axioms grammar_yield_inhabited
#print axioms grammar_checked_inhabited
#print axioms grammar_yield_unique
#print axioms grammar_parseType_iff
#print axioms grammar_no_unused_layout
end Solidity.Frontend.TypeGrammarH28.ParserDynamicClosure
