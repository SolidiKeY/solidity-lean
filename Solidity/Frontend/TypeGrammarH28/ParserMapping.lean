import Solidity.Frontend.TypeGrammarH28.ParserContexts

/-! Mapping constructor composition over independently established child
prefix support. Key resolution and expression evaluation remain outside scope. -/
namespace Solidity.Frontend.TypeGrammarH28.ParserMapping
open Solidity.Source Solidity.Frontend.Checked ParserBasic ParserPath ParserArray ParserContext

theorem opt_ident_complete (name : Option String) (front rest : List Located)
    (ch : List Choice) (eof : Nat) (hp : front.map Located.tok = optToks idt name)
    (hs : optIdent ⟨rest, ch, eof⟩ = .ok (none, ⟨rest, ch, eof⟩)) :
    optIdent ⟨front ++ rest, ch, eof⟩ = .ok (name, ⟨rest, ch, eof⟩) := by
  cases name with
  | none =>
    have he := located_nil front hp
    cases he
    exact hs
  | some name =>
    obtain ⟨a, b, he⟩ := located_one front _ hp
    cases he
    rfl

theorem name_boundary (name : Option String) (front rest : List Located)
    (hp : front.map Located.tok = optToks idt name) (hb : ParserContext.Boundary rest) :
    ParserContext.Boundary (front ++ rest) := by
  cases name with
  | none =>
    have he := located_nil front hp
    cases he
    exact hb
  | some name =>
    obtain ⟨a, b, he⟩ := located_one front _ hp
    cases he
    exact .named name a b rest

/-- A proof-only name for the frozen mapping body after it reads the key.
It is discharged from child support below, never assumed as global completeness. -/
def TailExact (fuel : Nat) (key : MapKey) (keyName : Option String)
    (value : Syn .typeName) (valueName : Option String) (input output : St) : Prop :=
  (show P (Syn .typeName) from do
    let kn ← optIdent
    expectP .doubleArrow
    let v ← typeName fuel
    let vn ← optIdent
    expectP .rparen
    return .mapping key kn v vn) input = .ok (.mapping key keyName value valueName, output)

theorem tail_complete (value : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (budget fuel : Nat) (hc : CompleteAt value tokens layout budget) (hf : budget ≤ fuel)
    (key : MapKey) (kn vn : Option String) (keyNames values valueNames rest : List Located)
    (hk : keyNames.map Located.tok = optToks idt kn)
    (hv : values.map Located.tok = tokens)
    (hn : valueNames.map Located.tok = optToks idt vn)
    (aa ab ra rb : Nat) (ch : List Choice) (eof : Nat) :
    TailExact fuel key kn value vn
      ⟨keyNames ++ (⟨.punct .doubleArrow, aa, ab⟩ ::
        (values ++ (valueNames ++ (⟨.punct .rparen, ra, rb⟩ :: rest)))), ch, eof⟩
      ⟨rest, layout.reverse ++ ch, eof⟩ := by
  have hkn := opt_ident_complete kn keyNames
    (⟨.punct .doubleArrow, aa, ab⟩ :: (values ++ (valueNames ++ (⟨.punct .rparen, ra, rb⟩ :: rest)))) ch eof hk rfl
  have hb : ParserContext.Boundary (valueNames ++ (⟨.punct .rparen, ra, rb⟩ :: rest)) :=
    name_boundary vn valueNames _ hn (.rparen ra rb rest)
  have hvalue := hc fuel hf values (valueNames ++ (⟨.punct .rparen, ra, rb⟩ :: rest)) hv hb ch eof
  have hvn := opt_ident_complete vn valueNames (⟨.punct .rparen, ra, rb⟩ :: rest)
    (layout.reverse ++ ch) eof hn rfl
  unfold TailExact
  change (optIdent ⟨keyNames ++ (⟨.punct .doubleArrow, aa, ab⟩ ::
    (values ++ (valueNames ++ (⟨.punct .rparen, ra, rb⟩ :: rest)))), ch, eof⟩ >>= _) = _
  rw [hkn]
  change (typeName fuel ⟨values ++ (valueNames ++ (⟨.punct .rparen, ra, rb⟩ :: rest)), ch, eof⟩ >>= _) = _
  rw [hvalue]
  change (optIdent ⟨valueNames ++ (⟨.punct .rparen, ra, rb⟩ :: rest), layout.reverse ++ ch, eof⟩ >>= _) = _
  rw [hvn]
  rfl

theorem mapping_elem_tail (fuel : Nat) (e : Elem) (hne : e ≠ .addressPayable)
    (kn vn : Option String) (value : Syn .typeName) (rest : List Located)
    (ma mb pa pb ka kb : Nat) (ch : List Choice) (eof : Nat) (output : St)
    (ht : TailExact fuel (.elem e hne) kn value vn ⟨rest, ch, eof⟩ output) :
    mappingType (fuel + 1)
      ⟨⟨.kw .mapping, ma, mb⟩ :: ⟨.punct .lparen, pa, pb⟩ :: ⟨.elem e, ka, kb⟩ :: rest, ch, eof⟩ =
      .ok (.mapping (.elem e hne) kn value vn, output) := by
  cases e <;> first
    | exact ht
    | exact False.elim (hne rfl)

theorem mapping_path_tail (fuel : Nat) (p : IdPath) (front rest : List Located)
    (kn vn : Option String) (value : Syn .typeName)
    (ma mb pa pb : Nat) (ch : List Choice) (eof : Nat) (output : St)
    (hp : front.map Located.tok = p.toks)
    (hs : pathStep ⟨rest, ch, eof⟩ = .ok (none, ⟨rest, ch, eof⟩))
    (ht : TailExact fuel (.path p) kn value vn ⟨rest, ch, eof⟩ output) :
    mappingType (fuel + 1)
      ⟨⟨.kw .mapping, ma, mb⟩ :: ⟨.punct .lparen, pa, pb⟩ :: (front ++ rest), ch, eof⟩ =
      .ok (.mapping (.path p) kn value vn, output) := by
  have hh := path_complete p front rest ch eof hp hs
  obtain ⟨head, tail, he, ht', hr⟩ := located_cons front _ _ hp
  cases he
  cases head with
  | mk tok a b =>
    cases ht'
    simp only [List.cons_append] at hh
    change (idPath ⟨⟨.ident p.head, a, b⟩ :: (tail ++ rest), ch, eof⟩ >>= _) = _
    rw [hh]
    exact ht

def keyTokens : MapKey → List Tok
  | .elem e _ => e.toks
  | .path p => p.toks

def mappingTokens (key : MapKey) (kn : Option String) (values : List Tok) (vn : Option String) : List Tok :=
  tk .mapping ++ parens (keyTokens key ++ optToks idt kn ++ pu .doubleArrow ++ values ++ optToks idt vn)

theorem mapping_tokens_cons (key : MapKey) (kn : Option String) (values : List Tok) (vn : Option String) :
    mappingTokens key kn values vn = .kw .mapping :: .punct .lparen ::
      (keyTokens key ++ (optToks idt kn ++ (.punct .doubleArrow :: (values ++ (optToks idt vn ++ [.punct .rparen]))))) := by
  unfold mappingTokens parens tk pu
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem key_elem_spelling (e : Elem) (hne : e ≠ .addressPayable) :
    keyTokens (.elem e hne) = [.elem e] := by
  cases e <;> first
    | rfl
    | exact False.elim (hne rfl)

/-- Every mapping key/name layout composes with a genuine independently
supported value prefix. All marker and field locations remain arbitrary. -/
theorem mapping_body_complete (value : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (budget fuel : Nat) (hc : CompleteAt value tokens layout budget) (hf : budget ≤ fuel)
    (key : MapKey) (kn vn : Option String) (front rest : List Located)
    (hp : front.map Located.tok = mappingTokens key kn tokens vn)
    (ch : List Choice) (eof : Nat) :
    mappingType (fuel + 1) ⟨front ++ rest, ch, eof⟩ =
      .ok (.mapping key kn value vn, ⟨rest, layout.reverse ++ ch, eof⟩) := by
  rw [mapping_tokens_cons] at hp
  obtain ⟨mappingHead, afterMapping, he, hm, hafter⟩ := located_cons front _ _ hp
  obtain ⟨parenHead, inner, he', hp', hi⟩ := located_cons afterMapping _ _ hafter
  obtain ⟨keys, afterKey, hek, hk, hafterKey⟩ := located_append inner (keyTokens key) _ hi
  obtain ⟨keyNames, beforeArrow, hen, hkn, hbeforeArrow⟩ := located_append afterKey (optToks idt kn) _ hafterKey
  obtain ⟨arrowHead, afterArrow, hea, ha, hafterArrow⟩ := located_cons beforeArrow _ _ hbeforeArrow
  obtain ⟨values, afterValues, hev, hv, hafterValues⟩ := located_append afterArrow tokens _ hafterArrow
  obtain ⟨valueNames, closing, hevn, hvn, hclosing⟩ := located_append afterValues (optToks idt vn) _ hafterValues
  obtain ⟨ra, rb, heclose⟩ := located_one closing _ hclosing
  cases he
  cases he'
  cases hek
  cases hen
  cases hea
  cases hev
  cases hevn
  cases heclose
  cases mappingHead with
  | mk tok ma mb =>
    cases hm
    cases parenHead with
    | mk tok pa pb =>
      cases hp'
      cases arrowHead with
      | mk tok aa ab =>
        cases ha
        have htail := tail_complete value tokens layout budget fuel hc hf key kn vn
          keyNames values valueNames rest hkn hv hvn aa ab ra rb ch eof
        cases key with
        | elem e hne =>
          rw [key_elem_spelling] at hk
          obtain ⟨ka, kb, hekey⟩ := located_one keys _ hk
          cases hekey
          have hmap := mapping_elem_tail fuel e hne kn vn value
            (keyNames ++ (⟨.punct .doubleArrow, aa, ab⟩ :: (values ++ (valueNames ++ (⟨.punct .rparen, ra, rb⟩ :: rest)))))
            ma mb pa pb ka kb ch eof ⟨rest, layout.reverse ++ ch, eof⟩ htail
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using hmap
        | path p =>
          have hb : ParserContext.Boundary
              (keyNames ++ (⟨.punct .doubleArrow, aa, ab⟩ :: (values ++ (valueNames ++ (⟨.punct .rparen, ra, rb⟩ :: rest))))) :=
            name_boundary kn keyNames _ hkn (.arrow aa ab _)
          have hs := boundary_no_path _ hb ch eof
          have hmap := mapping_path_tail fuel p keys
            (keyNames ++ (⟨.punct .doubleArrow, aa, ab⟩ :: (values ++ (valueNames ++ (⟨.punct .rparen, ra, rb⟩ :: rest)))))
            kn vn value ma mb pa pb ch eof ⟨rest, layout.reverse ++ ch, eof⟩ hk hs htail
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using hmap

theorem mapping_dispatch (fuel ma mb : Nat) (rest : List Located)
    (ch : List Choice) (eof : Nat) :
    typeName (fuel + 2) ⟨⟨.kw .mapping, ma, mb⟩ :: rest, ch, eof⟩ =
      (mappingType (fuel + 1) ⟨⟨.kw .mapping, ma, mb⟩ :: rest, ch, eof⟩ >>= fun r =>
        typeSuffix (fuel + 1) r.1 r.2) := rfl

theorem mapping_prefix (value : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (budget fuel : Nat) (hc : CompleteAt value tokens layout budget) (hf : budget ≤ fuel)
    (key : MapKey) (kn vn : Option String) (front rest : List Located)
    (hp : front.map Located.tok = mappingTokens key kn tokens vn)
    (hb : ParserContext.Boundary rest) (ch : List Choice) (eof : Nat) :
    typeName (fuel + 2) ⟨front ++ rest, ch, eof⟩ =
      .ok (.mapping key kn value vn, ⟨rest, layout.reverse ++ ch, eof⟩) := by
  have hm := mapping_body_complete value tokens layout budget fuel hc hf key kn vn front rest hp ch eof
  rw [mapping_tokens_cons] at hp
  obtain ⟨head, tail, he, ht, hr⟩ := located_cons front _ _ hp
  cases he
  cases head with
  | mk tok ma mb =>
    cases ht
    simp only [List.cons_append] at hm
    rw [List.cons_append, mapping_dispatch, hm]
    exact suffix_stop fuel (.mapping key kn value vn) ⟨rest, layout.reverse ++ ch, eof⟩
      (boundary_no_suffix rest hb (layout.reverse ++ ch) eof)

theorem complete_mapping (value : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (budget : Nat) (hc : CompleteAt value tokens layout budget)
    (key : MapKey) (kn vn : Option String) :
    CompleteAt (.mapping key kn value vn) (mappingTokens key kn tokens vn) layout (budget + 2) := by
  intro fuel hf front rest hp hb ch eof
  have he : fuel - (budget + 2) + budget + 2 = fuel :=
    (Nat.add_assoc _ _ _).trans (Nat.sub_add_cancel hf)
  have hn : budget ≤ fuel - (budget + 2) + budget := Nat.le_add_left _ _
  rw [← he]
  exact mapping_prefix value tokens layout budget _ hc hn key kn vn front rest hp hb ch eof

theorem toks_yield_decompose {c : Cat} (t : Syn c) (layout : List Choice) (tokens : List Tok)
    (h : t.toks layout = some tokens) :
    ∃ chunks : List (List Tok), t.yield layout = some (chunks, []) ∧ chunks.flatten = tokens := by
  unfold Syn.toks at h
  cases hy : t.yield layout with
  | none => rw [hy] at h; cases h
  | some pair =>
    cases pair with
    | mk chunks remaining =>
      rw [hy] at h
      cases remaining with
      | nil => exact ⟨chunks, rfl, Option.some.inj h⟩
      | cons choice rest => cases h

theorem mapping_toks (value : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (hy : value.toks layout = some tokens) (key : MapKey) (kn vn : Option String) :
    (Syn.mapping key kn value vn).toks layout = some (mappingTokens key kn tokens vn) := by
  obtain ⟨chunks, hv, ht⟩ := toks_yield_decompose value layout tokens hy
  have hm : (Syn.mapping key kn value vn).yield layout =
      some ([mappingTokens key kn tokens vn], []) := by
    change (value.yield layout >>= _) = _
    rw [hv]
    change some ([mappingTokens key kn chunks.flatten vn], ([] : List Choice)) = _
    exact congrArg (fun ts => some ([mappingTokens key kn ts vn], ([] : List Choice))) ht
  unfold Syn.toks
  rw [hm]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

theorem mapping_prec (value : Syn .typeName) (hv : value.prec = true)
    (key : MapKey) (kn vn : Option String) : (Syn.mapping key kn value vn).prec = true := by
  have ha : value.all Syn.precNode = true := (Bool.and_eq_true_iff.mp hv).2
  change (true && (true && value.all Syn.precNode)) = true
  rw [ha]
  rfl

theorem middle_length {α : Type} (left middle right : List α) :
    middle.length ≤ (left ++ (middle ++ right)).length := by
  rw [List.length_append, List.length_append]
  exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_left _ _)

theorem mapping_length (key : MapKey) (kn vn : Option String) (tokens : List Tok) :
    tokens.length + 1 ≤ (mappingTokens key kn tokens vn).length := by
  have hm := middle_length (keyTokens key ++ (optToks idt kn ++ [.punct .doubleArrow]))
    tokens (optToks idt vn ++ [.punct .rparen])
  have hi : tokens.length ≤
      (keyTokens key ++ (optToks idt kn ++ (Tok.punct .doubleArrow :: (tokens ++ (optToks idt vn ++ [Tok.punct .rparen]))))).length := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hm
  rw [mapping_tokens_cons]
  exact Nat.le_trans (Nat.succ_le_succ hi) (Nat.le_succ _)

theorem budget_lift (budget child parent : Nat)
    (hb : budget ≤ 16 * (child + 1)) (hl : child + 1 ≤ parent) :
    budget + 2 ≤ 16 * (parent + 1) := by
  calc
    budget + 2 ≤ 16 * (child + 1) + 16 := Nat.add_le_add hb (by decide : 2 ≤ 16)
    _ = 16 * ((child + 1) + 1) := (Nat.mul_add 16 (child + 1) 1).symm
    _ ≤ 16 * (parent + 1) := Nat.mul_le_mul_left 16 (Nat.succ_le_succ hl)

theorem mapping_budget (budget : Nat) (tokens : List Tok)
    (hb : budget ≤ 16 * (tokens.length + 1)) (key : MapKey) (kn vn : Option String) :
    budget + 2 ≤ 16 * ((mappingTokens key kn tokens vn).length + 1) := by
  exact budget_lift budget tokens.length _ hb (mapping_length key kn vn tokens)

/-- Checked completeness of the mapping constructor, with all child obligations
explicit and its own raw constructor success independently derived above. -/
theorem mapping_checked (value : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (budget : Nat) (hc : CompleteAt value tokens layout budget)
    (hy : value.toks layout = some tokens) (hv : value.prec = true)
    (hbudget : budget ≤ 16 * (tokens.length + 1))
    (key : MapKey) (kn vn : Option String) (ls : List Located) (eof : Nat)
    (hp : ls.map Located.tok = mappingTokens key kn tokens vn) :
    parseCatLocated typeName eof ls = .ok (.mapping key kn value vn, layout) := by
  have hl : ls.length = (mappingTokens key kn tokens vn).length := by
    have he := congrArg List.length hp
    simpa only [List.length_map] using he
  have hf : budget + 2 ≤ 16 * (ls.length + 1) := by
    rw [hl]
    exact mapping_budget budget tokens hbudget key kn vn
  have hc' := complete_mapping value tokens layout budget hc key kn vn
  have hraw : typeName (16 * (ls.length + 1)) ⟨ls, [], eof⟩ =
      .ok (.mapping key kn value vn, ⟨[], layout.reverse, eof⟩) := by
    have he := hc' _ hf ls [] hp .eof [] eof
    simpa only [List.append_nil] using he
  have ht : (Syn.mapping key kn value vn).toks layout.reverse.reverse = some (ls.map Located.tok) := by
    rw [List.reverse_reverse, mapping_toks value tokens layout hy key kn vn, hp]
  have ha := ParserCheck.checked_category_converse typeName eof ls (.mapping key kn value vn)
    ⟨[], layout.reverse, eof⟩ hraw rfl ht (mapping_prec value hv key kn vn)
  simpa only [List.reverse_reverse] using ha

theorem parseType_mapping (value : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (budget : Nat) (hc : CompleteAt value tokens layout budget)
    (hy : value.toks layout = some tokens) (hv : value.prec = true)
    (hbudget : budget ≤ 16 * (tokens.length + 1))
    (key : MapKey) (kn vn : Option String) (src : Bytes) (ps : List Piece)
    (hlex : lex src = .ok ps) (ht : tokensOf ps = mappingTokens key kn tokens vn) :
    parseType src = .ok (.mapping key kn value vn) := by
  have hl : ((locate .sol 0 ps).map Prod.fst).map Located.tok = mappingTokens key kn tokens vn := by
    rw [List.map_map]
    change (locate .sol 0 ps).map (fun x => x.1.tok) = _
    rw [locate_toks]
    exact ht
  have hp := mapping_checked value tokens layout budget hc hy hv hbudget key kn vn
    ((locate .sol 0 ps).map Prod.fst) src.length hl
  unfold parseType parseCat
  rw [hlex]
  change (parseCatLocated typeName src.length ((locate .sol 0 ps).map Prod.fst)).map Prod.fst = _
  rw [hp]
  rfl

theorem type_prec_node (t : Syn .typeName) : t.precNode = true := by
  cases t <;> rfl

theorem mapping_prec_converse (value : Syn .typeName) (key : MapKey) (kn vn : Option String)
    (h : (Syn.mapping key kn value vn).prec = true) : value.prec = true := by
  change (true && (true && value.all Syn.precNode)) = true at h
  have ha : value.all Syn.precNode = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2
  unfold Syn.prec
  rw [type_prec_node, ha]
  rfl

theorem mapping_yield (value : Syn .typeName) (key : MapKey) (kn vn : Option String)
    (layout : List Choice) :
    (Syn.mapping key kn value vn).yield layout =
      (value.yield layout >>= fun r => some ([mappingTokens key kn r.1.flatten vn], r.2)) := rfl

theorem mapping_toks_decompose (value : Syn .typeName) (key : MapKey) (kn vn : Option String)
    (layout : List Choice) (tokens : List Tok)
    (h : (Syn.mapping key kn value vn).toks layout = some tokens) :
    ∃ values : List Tok, value.toks layout = some values ∧ mappingTokens key kn values vn = tokens := by
  unfold Syn.toks at h
  rw [mapping_yield] at h
  cases hy : value.yield layout with
  | none => rw [hy] at h; cases h
  | some pair =>
    cases pair with
    | mk chunks remaining =>
      rw [hy] at h
      cases remaining with
      | nil =>
        change some (mappingTokens key kn chunks.flatten vn ++ []) = some tokens at h
        have he : some (mappingTokens key kn chunks.flatten vn) = some tokens := by
          simpa only [List.append_nil] using h
        refine ⟨chunks.flatten, ?_, Option.some.inj he⟩
        unfold Syn.toks
        rw [hy]
      | cons choice rest => cases h

/-- The universal-yield proof target for a type, with a separately returned
parser layout and explicit constructive fuel. Constructor preservation below
uses this only for strict children; it is not assumed for its own result. -/
def Certified (t : Syn .typeName) : Prop :=
  ∀ inputLayout : List Choice, ∀ tokens : List Tok,
    t.toks inputLayout = some tokens → t.prec = true →
    ∃ parsedLayout : List Choice, ∃ budget : Nat,
      CompleteAt t tokens parsedLayout budget ∧ t.toks parsedLayout = some tokens ∧
        budget ≤ 16 * (tokens.length + 1)

theorem certified_elem (e : Elem) : Certified (.elem e) := by
  intro input tokens hy _
  cases input with
  | cons choice rest => rw [elem_no_unused_layout] at hy; cases hy
  | nil =>
    rw [elem_toks] at hy
    have he : e.toks = tokens := Option.some.inj hy
    cases he
    refine ⟨[], 2, complete_elem e, elem_toks e, ?_⟩
    exact Nat.le_trans (by decide : 2 ≤ 16) (Nat.le_mul_of_pos_right 16 (Nat.succ_pos e.toks.length))

theorem certified_user (p : IdPath) : Certified (.userType p) := by
  intro input tokens hy _
  cases input with
  | cons choice rest => rw [userType_no_unused_layout] at hy; cases hy
  | nil =>
    rw [userType_toks] at hy
    have he : p.toks = tokens := Option.some.inj hy
    cases he
    refine ⟨[], 2, complete_user p, userType_toks p, ?_⟩
    exact Nat.le_trans (by decide : 2 ≤ 16) (Nat.le_mul_of_pos_right 16 (Nat.succ_pos p.toks.length))

theorem certified_mapping (value : Syn .typeName) (hc : Certified value)
    (key : MapKey) (kn vn : Option String) : Certified (.mapping key kn value vn) := by
  intro input tokens hy hp
  obtain ⟨values, hv, he⟩ := mapping_toks_decompose value key kn vn input tokens hy
  have hvp := mapping_prec_converse value key kn vn hp
  obtain ⟨layout, budget, hc', hy', hb⟩ := hc input values hv hvp
  refine ⟨layout, budget + 2, ?_, ?_, ?_⟩
  · have hm := complete_mapping value values layout budget hc' key kn vn
    rw [he] at hm
    exact hm
  · have hm := mapping_toks value values layout hy' key kn vn
    rw [he] at hm
    exact hm
  · have hm := mapping_budget budget values hb key kn vn
    rw [he] at hm
    exact hm

theorem dynamic_tokens_budget (tokens : List Tok) (k : Nat) :
    k + 2 ≤ 16 * ((tokens ++ dynamicBrackets k).length + 1) := by
  have hk : k ≤ (tokens ++ dynamicBrackets k).length := by
    rw [List.length_append]
    exact Nat.le_trans (brackets_budget k) (Nat.le_add_left _ _)
  exact Nat.le_trans (Nat.add_le_add_right hk 2) (frozen_budget _)

theorem certified_dynamic_elem (e : Elem) (k : Nat) : Certified (dynamicTree (.elem e) k) := by
  intro input tokens hy _
  rw [dynamic_elem_layout] at hy
  cases input with
  | cons choice rest => cases hy
  | nil =>
    have he : e.toks ++ dynamicBrackets k = tokens := Option.some.inj hy
    cases he
    exact ⟨[], k + 2, complete_dynamic_elem e k, dynamic_toks (.elem e) k e.toks rfl, dynamic_tokens_budget e.toks k⟩

theorem certified_dynamic_user (p : IdPath) (k : Nat) : Certified (dynamicTree (.userType p) k) := by
  intro input tokens hy _
  rw [dynamic_user_layout] at hy
  cases input with
  | cons choice rest => cases hy
  | nil =>
    have he : p.toks ++ dynamicBrackets k = tokens := Option.some.inj hy
    cases he
    exact ⟨[], k + 2, complete_dynamic_user p k, dynamic_toks (.userType p) k p.toks rfl, dynamic_tokens_budget p.toks k⟩

/-- Projection of independently constructed certificate evidence to the
actual frozen checked parser; this does not assert all types are certified. -/
theorem certified_checked (t : Syn .typeName) (hc : Certified t)
    (input : List Choice) (tokens : List Tok) (hy : t.toks input = some tokens) (hp : t.prec = true)
    (ls : List Located) (eof : Nat) (hl : ls.map Located.tok = tokens) :
    ∃ layout : List Choice, parseCatLocated typeName eof ls = .ok (t, layout) := by
  obtain ⟨layout, budget, hr, ht, hb⟩ := hc input tokens hy hp
  have hlen : ls.length = tokens.length := by
    have he := congrArg List.length hl
    simpa only [List.length_map] using he
  have hf : budget ≤ 16 * (ls.length + 1) := by rw [hlen]; exact hb
  have hraw : typeName (16 * (ls.length + 1)) ⟨ls, [], eof⟩ = .ok (t, ⟨[], layout.reverse, eof⟩) := by
    have he := hr _ hf ls [] hl .eof [] eof
    simpa only [List.append_nil] using he
  have hyt : t.toks layout.reverse.reverse = some (ls.map Located.tok) := by
    rw [List.reverse_reverse, ht, hl]
  have ha := ParserCheck.checked_category_converse typeName eof ls t ⟨[], layout.reverse, eof⟩ hraw rfl hyt hp
  exact ⟨layout, by simpa only [List.reverse_reverse] using ha⟩

theorem certified_parseType (t : Syn .typeName) (hc : Certified t)
    (input : List Choice) (tokens : List Tok) (hy : t.toks input = some tokens) (hp : t.prec = true)
    (src : Bytes) (ps : List Piece) (hlex : lex src = .ok ps) (ht : tokensOf ps = tokens) :
    parseType src = .ok t := by
  have hl : ((locate .sol 0 ps).map Prod.fst).map Located.tok = tokens := by
    rw [List.map_map]
    change (locate .sol 0 ps).map (fun x => x.1.tok) = _
    rw [locate_toks]
    exact ht
  obtain ⟨layout, ha⟩ := certified_checked t hc input tokens hy hp
    ((locate .sol 0 ps).map Prod.fst) src.length hl
  unfold parseType parseCat
  rw [hlex]
  change (parseCatLocated typeName src.length ((locate .sol 0 ps).map Prod.fst)).map Prod.fst = _
  rw [ha]
  rfl

/-- Identity/layout projection for independently certified trees. Certification
of every original constructor remains a separate obligation. Original input
layout witnesses are never equated. -/
theorem certified_yield_unique (t u : Syn .typeName) (ht : Certified t) (hu : Certified u)
    (left right : List Choice) (tokens : List Tok)
    (hl : t.toks left = some tokens) (hr : u.toks right = some tokens)
    (hpt : t.prec = true) (hpu : u.prec = true) :
    t = u ∧ LayoutEquivalent t left right := by
  let ls := ParserCheck.witnessLocations tokens
  have hm : ls.map Located.tok = tokens := ParserCheck.witness_locations_tokens tokens
  obtain ⟨layout, ha⟩ := certified_checked t ht left tokens hl hpt ls 0 hm
  obtain ⟨layout', hb⟩ := certified_checked u hu right tokens hr hpu ls 0 hm
  have he : t = u := (Prod.mk.inj (Except.ok.inj (ha.symm.trans hb))).1
  refine ⟨he, tokens, hl, ?_⟩
  rw [he]
  exact hr

/-- A control builder over existing intrinsic mapping fields, not a new
operational syntax or producer implementation. Each depth may choose a distinct
key and distinct optional names. -/
def nestedMappings (base : Syn .typeName) : List (MapKey × Option String × Option String) → Syn .typeName
  | [] => base
  | frame :: rest => .mapping frame.1 frame.2.1 (nestedMappings base rest) frame.2.2

theorem certified_nested_mappings (base : Syn .typeName) (hc : Certified base)
    (frames : List (MapKey × Option String × Option String)) : Certified (nestedMappings base frames) := by
  induction frames with
  | nil => exact hc
  | cons frame frames ih => exact certified_mapping (nestedMappings base frames) ih frame.1 frame.2.1 frame.2.2

theorem nested_mappings_prec (base : Syn .typeName) (hp : base.prec = true)
    (frames : List (MapKey × Option String × Option String)) : (nestedMappings base frames).prec = true := by
  induction frames with
  | nil => exact hp
  | cons frame frames ih => exact mapping_prec (nestedMappings base frames) ih frame.1 frame.2.1 frame.2.2

/-- An inhabited arbitrary-depth mapping-family identity theorem: both strict
base certificates and all recursive mapping obligations are discharged here. -/
theorem nested_dynamic_elem_unique (e f : Elem) (k j : Nat)
    (frames frames' : List (MapKey × Option String × Option String))
    (left right : List Choice) (tokens : List Tok)
    (hl : (nestedMappings (dynamicTree (.elem e) k) frames).toks left = some tokens)
    (hr : (nestedMappings (dynamicTree (.elem f) j) frames').toks right = some tokens) :
    nestedMappings (dynamicTree (.elem e) k) frames = nestedMappings (dynamicTree (.elem f) j) frames' ∧
      LayoutEquivalent (nestedMappings (dynamicTree (.elem e) k) frames) left right := by
  exact certified_yield_unique _ _
    (certified_nested_mappings _ (certified_dynamic_elem e k) frames)
    (certified_nested_mappings _ (certified_dynamic_elem f j) frames') left right tokens hl hr
    (nested_mappings_prec _ (dynamic_prec (.elem e) k rfl) frames)
    (nested_mappings_prec _ (dynamic_prec (.elem f) j rfl) frames')

theorem nested_dynamic_user_unique (p q : IdPath) (k j : Nat)
    (frames frames' : List (MapKey × Option String × Option String))
    (left right : List Choice) (tokens : List Tok)
    (hl : (nestedMappings (dynamicTree (.userType p) k) frames).toks left = some tokens)
    (hr : (nestedMappings (dynamicTree (.userType q) j) frames').toks right = some tokens) :
    nestedMappings (dynamicTree (.userType p) k) frames = nestedMappings (dynamicTree (.userType q) j) frames' ∧
      LayoutEquivalent (nestedMappings (dynamicTree (.userType p) k) frames) left right := by
  exact certified_yield_unique _ _
    (certified_nested_mappings _ (certified_dynamic_user p k) frames)
    (certified_nested_mappings _ (certified_dynamic_user q j) frames') left right tokens hl hr
    (nested_mappings_prec _ (dynamic_prec (.userType p) k rfl) frames)
    (nested_mappings_prec _ (dynamic_prec (.userType q) j rfl) frames')

def nestedMappingTokens (base : List Tok) : List (MapKey × Option String × Option String) → List Tok
  | [] => base
  | frame :: rest => mappingTokens frame.1 frame.2.1 (nestedMappingTokens base rest) frame.2.2

theorem nested_mappings_toks (base : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (hy : base.toks layout = some tokens) (frames : List (MapKey × Option String × Option String)) :
    (nestedMappings base frames).toks layout = some (nestedMappingTokens tokens frames) := by
  induction frames with
  | nil => exact hy
  | cons frame frames ih => exact mapping_toks (nestedMappings base frames) _ layout ih frame.1 frame.2.1 frame.2.2

/-- Universal inhabited controls: every frame/depth choice has an actual yield
and an actual checked parse, not merely a conditional equality implication. -/
theorem nested_dynamic_elem_inhabited (e : Elem) (k : Nat)
    (frames : List (MapKey × Option String × Option String)) :
    ∃ tokens : List Tok, (nestedMappings (dynamicTree (.elem e) k) frames).toks [] = some tokens ∧
      ∃ layout : List Choice, parseCatLocated typeName 0 (ParserCheck.witnessLocations tokens) =
        .ok (nestedMappings (dynamicTree (.elem e) k) frames, layout) := by
  let tokens := nestedMappingTokens (e.toks ++ dynamicBrackets k) frames
  have hy : (nestedMappings (dynamicTree (.elem e) k) frames).toks [] = some tokens :=
    nested_mappings_toks _ _ [] (dynamic_toks (.elem e) k e.toks rfl) frames
  have hc := certified_nested_mappings _ (certified_dynamic_elem e k) frames
  have hp := nested_mappings_prec _ (dynamic_prec (.elem e) k rfl) frames
  exact ⟨tokens, hy, certified_checked _ hc [] tokens hy hp _ 0 (ParserCheck.witness_locations_tokens tokens)⟩

theorem nested_dynamic_user_inhabited (p : IdPath) (k : Nat)
    (frames : List (MapKey × Option String × Option String)) :
    ∃ tokens : List Tok, (nestedMappings (dynamicTree (.userType p) k) frames).toks [] = some tokens ∧
      ∃ layout : List Choice, parseCatLocated typeName 0 (ParserCheck.witnessLocations tokens) =
        .ok (nestedMappings (dynamicTree (.userType p) k) frames, layout) := by
  let tokens := nestedMappingTokens (p.toks ++ dynamicBrackets k) frames
  have hy : (nestedMappings (dynamicTree (.userType p) k) frames).toks [] = some tokens :=
    nested_mappings_toks _ _ [] (dynamic_toks (.userType p) k p.toks rfl) frames
  have hc := certified_nested_mappings _ (certified_dynamic_user p k) frames
  have hp := nested_mappings_prec _ (dynamic_prec (.userType p) k rfl) frames
  exact ⟨tokens, hy, certified_checked _ hc [] tokens hy hp _ 0 (ParserCheck.witness_locations_tokens tokens)⟩

/-- Raw artificial token control, distinguished from the real two-token
address-payable spelling in the following theorem. -/
theorem artificial_payable_key_refused (fuel ma mb pa pb ka kb : Nat)
    (rest : List Located) (ch : List Choice) (eof : Nat) :
    mappingType (fuel + 1)
      ⟨⟨.kw .mapping, ma, mb⟩ :: ⟨.punct .lparen, pa, pb⟩ :: ⟨.elem .addressPayable, ka, kb⟩ :: rest, ch, eof⟩ =
      .error ⟨St.pos ⟨rest, ch, eof⟩, "payable mapping key"⟩ := rfl

theorem payable_key_spelling_refused (fuel ma mb pa pb ka kb va vb : Nat)
    (rest : List Located) (ch : List Choice) (eof : Nat) :
    typeName (fuel + 2)
      ⟨⟨.kw .mapping, ma, mb⟩ :: ⟨.punct .lparen, pa, pb⟩ :: ⟨.elem .address, ka, kb⟩ ::
        ⟨.kw .payable, va, vb⟩ :: rest, ch, eof⟩ = .error ⟨va, "expected '=>'"⟩ := rfl

theorem certified_parseType_iff (t : Syn .typeName) (hc : Certified t) (src : Bytes) :
    parseType src = .ok t ↔ ∃ ps : List Piece, lex src = .ok ps ∧
      ∃ layout : List Choice, t.toks layout = some (tokensOf ps) ∧ t.prec = true := by
  constructor
  · intro h
    obtain ⟨ps, hlex, hd, hp⟩ := parseType_derives h
    obtain ⟨layout, hy⟩ := hd
    exact ⟨ps, hlex, layout, hy, hp⟩
  · intro h
    obtain ⟨ps, hlex, layout, hy, hp⟩ := h
    exact certified_parseType t hc layout (tokensOf ps) hy hp src ps hlex rfl

theorem parseType_mapping_iff (value : Syn .typeName) (hc : Certified value)
    (key : MapKey) (kn vn : Option String) (src : Bytes) :
    parseType src = .ok (.mapping key kn value vn) ↔ ∃ ps : List Piece, lex src = .ok ps ∧
      ∃ layout : List Choice, (Syn.mapping key kn value vn).toks layout = some (tokensOf ps) ∧
        (Syn.mapping key kn value vn).prec = true := by
  exact certified_parseType_iff (.mapping key kn value vn) (certified_mapping value hc key kn vn) src

#print axioms opt_ident_complete
#print axioms name_boundary
#print axioms tail_complete
#print axioms mapping_elem_tail
#print axioms mapping_path_tail
#print axioms mapping_tokens_cons
#print axioms key_elem_spelling
#print axioms mapping_body_complete
#print axioms mapping_dispatch
#print axioms mapping_prefix
#print axioms complete_mapping
#print axioms toks_yield_decompose
#print axioms mapping_toks
#print axioms mapping_prec
#print axioms middle_length
#print axioms mapping_length
#print axioms budget_lift
#print axioms mapping_budget
#print axioms mapping_checked
#print axioms parseType_mapping
#print axioms type_prec_node
#print axioms mapping_prec_converse
#print axioms mapping_yield
#print axioms mapping_toks_decompose
#print axioms certified_elem
#print axioms certified_user
#print axioms certified_mapping
#print axioms dynamic_tokens_budget
#print axioms certified_dynamic_elem
#print axioms certified_dynamic_user
#print axioms certified_checked
#print axioms certified_parseType
#print axioms certified_yield_unique
#print axioms certified_nested_mappings
#print axioms nested_mappings_prec
#print axioms nested_dynamic_elem_unique
#print axioms nested_dynamic_user_unique
#print axioms nested_mappings_toks
#print axioms nested_dynamic_elem_inhabited
#print axioms nested_dynamic_user_inhabited
#print axioms artificial_payable_key_refused
#print axioms payable_key_spelling_refused
#print axioms certified_parseType_iff
#print axioms parseType_mapping_iff
end Solidity.Frontend.TypeGrammarH28.ParserMapping
