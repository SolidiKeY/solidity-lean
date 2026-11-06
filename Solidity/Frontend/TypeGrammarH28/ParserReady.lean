import Solidity.Frontend.TypeGrammarH28.ParserDynamicClosure

/-! Strong prefix proof targets for recursive fields and array extension.
Original input layouts may have an arbitrary unconsumed suffix. The constructed
parser/printing layout is independent of that original witness. -/
namespace Solidity.Frontend.TypeGrammarH28.ParserReady
open Solidity.Source Solidity.Frontend.Checked ParserBasic ParserPath ParserArray ParserContext ParserMapping

/-- Safe continuations for the base parser: a known terminal context or another
array suffix. This does not claim that typeName stops before the latter. -/
inductive Continuation : List Located → Prop where
  | finish {rest : List Located} (boundary : ParserContext.Boundary rest) : Continuation rest
  | array (a b : Nat) (rest : List Located) : Continuation (⟨.punct .lbrack, a, b⟩ :: rest)

theorem continuation_no_payable (rest : List Located) (h : Continuation rest)
    (ch : List Choice) (eof : Nat) :
    eat (.kw .payable) ⟨rest, ch, eof⟩ = .ok (false, ⟨rest, ch, eof⟩) := by
  cases h with
  | finish hb => exact boundary_no_payable rest hb ch eof
  | array a b rest => rfl

theorem continuation_no_path (rest : List Located) (h : Continuation rest)
    (ch : List Choice) (eof : Nat) :
    pathStep ⟨rest, ch, eof⟩ = .ok (none, ⟨rest, ch, eof⟩) := by
  cases h with
  | finish hb => exact boundary_no_path rest hb ch eof
  | array a b rest => rfl

theorem continuation_no_attrs (fuel : Nat) (rest : List Located) (h : Continuation rest)
    (vis : Option Visibility) (mu : Option Mutability) (order : List Slot)
    (ch : List Choice) (eof : Nat) :
    fnTypeAttrs fuel vis mu order ⟨rest, ch, eof⟩ = .ok ((vis, mu, order.reverse), ⟨rest, ch, eof⟩) := by
  cases h with
  | finish hb => exact boundary_no_attrs fuel rest hb vis mu order ch eof
  | array a b rest => cases fuel <;> rfl

theorem continuation_no_returns (fuel : Nat) (rest : List Located) (h : Continuation rest)
    (ch : List Choice) (eof : Nat) :
    returnsOpt (fuel + 1) ⟨rest, ch, eof⟩ = .ok (.nil, ⟨rest, ch, eof⟩) := by
  cases h with
  | finish hb => exact boundary_no_returns fuel rest hb ch eof
  | array a b rest => rfl

/-- A suffix-readiness equation, including the actual continuation parser.
No success is assumed for that suffix. cost tracks the typeName dispatch and
already-read array layers; need is sufficient residual suffix fuel. -/
def ReadyAt (t : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (cost need : Nat) : Prop :=
  ∀ residual : Nat, need ≤ residual → ∀ front rest : List Located,
    front.map Located.tok = tokens → Continuation rest → ∀ ch : List Choice, ∀ eof : Nat,
    typeName (residual + cost) ⟨front ++ rest, ch, eof⟩ =
      typeSuffix residual t ⟨rest, layout.reverse ++ ch, eof⟩

theorem ready_completeAt (t : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (cost need : Nat) (hn : 1 ≤ need) (hr : ReadyAt t tokens layout cost need) :
    CompleteAt t tokens layout (need + cost) := by
  intro fuel hf front rest hp hb ch eof
  have hc : cost ≤ fuel := Nat.le_trans (Nat.le_add_left cost need) hf
  have hres : need ≤ fuel - cost := Nat.le_sub_of_add_le hf
  have he : fuel - cost + cost = fuel := Nat.sub_add_cancel hc
  have hready := hr (fuel - cost) hres front rest hp (.finish hb) ch eof
  rw [he] at hready
  have hpos : 1 ≤ fuel - cost := Nat.le_trans hn hres
  have hpred : fuel - cost - 1 + 1 = fuel - cost := Nat.sub_add_cancel hpos
  have hs := suffix_stop (fuel - cost - 1) t ⟨rest, layout.reverse ++ ch, eof⟩
    (boundary_no_suffix rest hb (layout.reverse ++ ch) eof)
  rw [hpred] at hs
  exact hready.trans hs

theorem ready_elem (e : Elem) : ReadyAt (.elem e) e.toks [] 1 1 := by
  intro residual _ front rest hp hb ch eof
  change typeName (residual + 1) ⟨front ++ rest, ch, eof⟩ = typeSuffix residual (.elem e) ⟨rest, ch, eof⟩
  exact elem_then_suffix e residual front rest ch eof hp (continuation_no_payable rest hb ch eof)

theorem ready_user (p : IdPath) : ReadyAt (.userType p) p.toks [] 1 1 := by
  intro residual _ front rest hp hb ch eof
  change typeName (residual + 1) ⟨front ++ rest, ch, eof⟩ = typeSuffix residual (.userType p) ⟨rest, ch, eof⟩
  exact user_then_suffix p residual front rest ch eof hp (continuation_no_path rest hb ch eof)

/-- Strong universal yield target. Exact canonical printing under arbitrary
future layout suffixes is supplied explicitly, so recursive list composition
does not silently assume a producer-interface or whole-type uniqueness fact. -/
def PrefixCertified (t : Syn .typeName) : Prop :=
  ∀ input : List Choice, ∀ chunks : List (List Tok), ∀ remaining : List Choice,
    t.yield input = some (chunks, remaining) → t.prec = true →
    ∃ layout : List Choice, ∃ cost need : Nat,
      1 ≤ need ∧ ReadyAt t chunks.flatten layout cost need ∧
      YieldExact t layout [chunks.flatten] ∧ need + cost ≤ 16 * (chunks.flatten.length + 1)

theorem prefix_to_certified (t : Syn .typeName) (hc : PrefixCertified t) : Certified t := by
  intro input tokens hy hp
  obtain ⟨chunks, hv, ht⟩ := toks_yield_decompose t input tokens hy
  obtain ⟨layout, cost, need, hn, hr, hx, hb⟩ := hc input chunks [] hv hp
  rw [ht] at hr hx hb
  have hcanon := exact_toks t layout [tokens] hx
  have hy' : t.toks layout = some tokens := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hcanon
  exact ⟨layout, need + cost, ready_completeAt t tokens layout cost need hn hr, hy', hb⟩

theorem prefix_elem (e : Elem) : PrefixCertified (.elem e) := by
  intro input chunks remaining hy _
  change some ([e.toks], input) = some (chunks, remaining) at hy
  have he : [e.toks] = chunks := (Prod.mk.inj (Option.some.inj hy)).1
  have ht : chunks.flatten = e.toks := by
    rw [← he]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [ht]
  refine ⟨[], 1, 1, Nat.le_refl 1, ready_elem e, exact_elem e, ?_⟩
  exact Nat.le_trans (by decide : 2 ≤ 16) (Nat.le_mul_of_pos_right 16 (Nat.succ_pos e.toks.length))

theorem prefix_user (p : IdPath) : PrefixCertified (.userType p) := by
  intro input chunks remaining hy _
  change some ([p.toks], input) = some (chunks, remaining) at hy
  have he : [p.toks] = chunks := (Prod.mk.inj (Option.some.inj hy)).1
  have ht : chunks.flatten = p.toks := by
    rw [← he]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [ht]
  refine ⟨[], 1, 1, Nat.le_refl 1, ready_user p, exact_userType p, ?_⟩
  exact Nat.le_trans (by decide : 2 ≤ 16) (Nat.le_mul_of_pos_right 16 (Nat.succ_pos p.toks.length))

theorem ready_mapping (value : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (budget : Nat) (hc : CompleteAt value tokens layout budget)
    (key : MapKey) (kn vn : Option String) :
    ReadyAt (.mapping key kn value vn) (mappingTokens key kn tokens vn) layout 1 (budget + 1) := by
  intro residual hf front rest hp _ ch eof
  have hchild : budget ≤ residual - 1 := Nat.le_sub_of_add_le hf
  have hpos : 1 ≤ residual := Nat.le_trans (Nat.le_add_left 1 budget) hf
  have he : residual - 1 + 1 = residual := Nat.sub_add_cancel hpos
  have hm := mapping_body_complete value tokens layout budget (residual - 1) hc hchild key kn vn front rest hp ch eof
  rw [he] at hm
  rw [mapping_tokens_cons] at hp
  obtain ⟨head, tail, hfront, ht, hr⟩ := located_cons front _ _ hp
  cases hfront
  cases head with
  | mk tok ma mb =>
    cases ht
    have hd := mapping_dispatch (residual - 1) ma mb (tail ++ rest) ch eof
    have hi : residual - 1 + 2 = residual + 1 := congrArg (fun n => n + 1) he
    rw [hi, he] at hd
    simp only [List.cons_append] at hm ⊢
    rw [hd, hm]
    rfl

theorem prefix_mapping (value : Syn .typeName) (hc : PrefixCertified value)
    (key : MapKey) (kn vn : Option String) : PrefixCertified (.mapping key kn value vn) := by
  intro input chunks remaining hy hp
  rw [mapping_yield] at hy
  cases hv : value.yield input with
  | none => rw [hv] at hy; cases hy
  | some pair =>
    cases pair with
    | mk items afterValue =>
      rw [hv] at hy
      change some ([mappingTokens key kn items.flatten vn], afterValue) = some (chunks, remaining) at hy
      have he : [mappingTokens key kn items.flatten vn] = chunks := (Prod.mk.inj (Option.some.inj hy)).1
      have ht : chunks.flatten = mappingTokens key kn items.flatten vn := by
        rw [← he]
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      obtain ⟨layout, cost, need, hn, hr, hx, hb⟩ := hc input items afterValue hv
        (mapping_prec_converse value key kn vn hp)
      have hchild := ready_completeAt value items.flatten layout cost need hn hr
      have hprint := exact_mapping key kn vn value layout [items.flatten] hx
      have hcanon : YieldExact (.mapping key kn value vn) layout [mappingTokens key kn items.flatten vn] := by
        simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using hprint
      rw [ht]
      exact ⟨layout, 1, need + cost + 1, Nat.succ_le_succ (Nat.zero_le _),
        ready_mapping value items.flatten layout (need + cost) hchild key kn vn,
        hcanon, mapping_budget (need + cost) items.flatten hb key kn vn⟩

theorem ready_array_none (base : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (cost need : Nat) (hc : ReadyAt base tokens layout cost need) :
    ReadyAt (.array base .none) (tokens ++ [.punct .lbrack, .punct .rbrack]) layout (cost + 1) (need + 1) := by
  intro residual hf front rest hp hb ch eof
  obtain ⟨body, brackets, he, ht, hbr⟩ := located_append front tokens [.punct .lbrack, .punct .rbrack] hp
  obtain ⟨opening, closing, he', ho, hclose⟩ := located_cons brackets _ _ hbr
  obtain ⟨ra, rb, heclose⟩ := located_one closing _ hclose
  cases he
  cases he'
  cases heclose
  cases opening with
  | mk tok la lb =>
    cases ho
    have hn : need ≤ residual + 1 := Nat.le_trans (Nat.le_trans (Nat.le_succ need) hf) (Nat.le_succ residual)
    have hr := hc (residual + 1) hn body (⟨.punct .lbrack, la, lb⟩ :: ⟨.punct .rbrack, ra, rb⟩ :: rest)
      ht (.array la lb _) ch eof
    have hi : residual + 1 + cost = residual + (cost + 1) :=
      (Nat.add_right_comm residual 1 cost).trans (Nat.add_assoc residual cost 1)
    rw [hi] at hr
    have hs : typeSuffix (residual + 1) base
        ⟨⟨.punct .lbrack, la, lb⟩ :: ⟨.punct .rbrack, ra, rb⟩ :: rest, layout.reverse ++ ch, eof⟩ =
        typeSuffix residual (.array base .none) ⟨rest, layout.reverse ++ ch, eof⟩ := rfl
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hr.trans hs

theorem prefix_array_none (base : Syn .typeName) (hc : PrefixCertified base) : PrefixCertified (.array base .none) := by
  intro input chunks remaining hy hp
  rw [ParserDynamicClosure.array_none_yield] at hy
  cases hv : base.yield input with
  | none => rw [hv] at hy; cases hy
  | some pair =>
    cases pair with
    | mk items afterBase =>
      rw [hv] at hy
      change some ([items.flatten ++ [.punct .lbrack, .punct .rbrack]], afterBase) = some (chunks, remaining) at hy
      have he : [items.flatten ++ [.punct .lbrack, .punct .rbrack]] = chunks := (Prod.mk.inj (Option.some.inj hy)).1
      have ht : chunks.flatten = items.flatten ++ [.punct .lbrack, .punct .rbrack] := by
        rw [← he]
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      obtain ⟨layout, cost, need, hn, hr, hx, hb⟩ := hc input items afterBase hv
        (ParserDynamicClosure.array_none_prec_converse base hp)
      have hprint := exact_array base .none layout [] [items.flatten] [] hx exact_no_length
      have hcanon : YieldExact (.array base .none) layout [items.flatten ++ [.punct .lbrack, .punct .rbrack]] := by
        simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc, List.cons_append, List.nil_append] using hprint
      have hlen : items.flatten.length + 1 ≤ (items.flatten ++ [Tok.punct .lbrack, Tok.punct .rbrack]).length := by
        rw [List.length_append]
        exact Nat.le_succ _
      have hbudget := budget_lift (need + cost) items.flatten.length _ hb hlen
      have htotal : (need + 1) + (cost + 1) = (need + cost) + 2 := by
        calc
          (need + 1) + (cost + 1) = need + (1 + (cost + 1)) := Nat.add_assoc _ _ _
          _ = need + (cost + (1 + 1)) := congrArg (fun n => need + n) (Nat.add_left_comm 1 cost 1)
          _ = (need + cost) + 2 := (Nat.add_assoc need cost 2).symm
      rw [ht]
      refine ⟨layout, cost + 1, need + 1, Nat.succ_le_succ (Nat.zero_le _),
        ready_array_none base items.flatten layout cost need hr, hcanon, ?_⟩
      rw [htotal]
      exact hbudget

theorem prefix_dynamic (base : Syn .typeName) (hc : PrefixCertified base) (depth : Nat) :
    PrefixCertified (dynamicTree base depth) := by
  induction depth with
  | zero => exact hc
  | succ depth ih =>
    rw [ParserDynamicClosure.dynamic_succ]
    exact prefix_array_none (dynamicTree base depth) ih

theorem grammar_prefix (t : Syn .typeName) (h : ParserDynamicClosure.DynamicMappingGrammar t) :
    PrefixCertified t := by
  induction h with
  | elem e depth => exact prefix_dynamic (.elem e) (prefix_elem e) depth
  | user p depth => exact prefix_dynamic (.userType p) (prefix_user p) depth
  | mapping key kn value vn depth child ih =>
    exact prefix_dynamic (.mapping key kn value vn) (prefix_mapping value ih key kn vn) depth

/-- The readiness equation itself also holds at zero residual fuel; its right
side then reports an error. The positive-need field in the completion theorem
is therefore a substantive guard rather than an arbitrary convention. -/
theorem ready_elem_zero (e : Elem) : ReadyAt (.elem e) e.toks [] 1 0 := by
  intro residual _ front rest hp hb ch eof
  change typeName (residual + 1) ⟨front ++ rest, ch, eof⟩ = typeSuffix residual (.elem e) ⟨rest, ch, eof⟩
  exact elem_then_suffix e residual front rest ch eof hp (continuation_no_payable rest hb ch eof)

theorem not_complete_elem_one (e : Elem) : ¬ CompleteAt (.elem e) e.toks [] 1 := by
  intro hc
  let ls := ParserCheck.witnessLocations e.toks
  have hm : ls.map Located.tok = e.toks := ParserCheck.witness_locations_tokens e.toks
  have hs : typeName 1 ⟨ls, [], 0⟩ = .ok (.elem e, ⟨[], [], 0⟩) := by
    have he := hc 1 (Nat.le_refl 1) ls [] hm .eof [] 0
    simpa only [List.append_nil] using he
  have he : typeName 1 ⟨ls, [], 0⟩ = .error ⟨0, "nesting too deep"⟩ := by
    have hr := elem_then_suffix e 0 ls [] [] 0 hm rfl
    simpa only [List.append_nil] using hr
  rw [he] at hs
  cases hs

theorem unconsumed_layout_control (e : Elem) (choice : Choice) (rest : List Choice) :
    (Syn.elem e).yield (choice :: rest) = some ([e.toks], choice :: rest) ∧
      YieldExact (.elem e) [] [e.toks] ∧ ReadyAt (.elem e) e.toks [] 1 1 := by
  exact ⟨rfl, exact_elem e, ready_elem e⟩

#print axioms continuation_no_payable
#print axioms continuation_no_path
#print axioms continuation_no_attrs
#print axioms continuation_no_returns
#print axioms ready_completeAt
#print axioms ready_elem
#print axioms ready_user
#print axioms prefix_to_certified
#print axioms prefix_elem
#print axioms prefix_user
#print axioms ready_mapping
#print axioms prefix_mapping
#print axioms ready_array_none
#print axioms prefix_array_none
#print axioms prefix_dynamic
#print axioms grammar_prefix
#print axioms ready_elem_zero
#print axioms not_complete_elem_one
#print axioms unconsumed_layout_control
end Solidity.Frontend.TypeGrammarH28.ParserReady
