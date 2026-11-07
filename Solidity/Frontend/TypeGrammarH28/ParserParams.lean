import Solidity.Frontend.TypeGrammarH28.ParserReady

/-! Parameter and list constructor proofs for function type fields.
All source locations, optional data locations and names remain arbitrary. -/
namespace Solidity.Frontend.TypeGrammarH28.ParserParams
open Solidity.Source Solidity.Frontend.Checked ParserBasic ParserPath ParserArray ParserContext ParserMapping ParserReady

inductive ListBoundary : List Located → Prop where
  | eof : ListBoundary []
  | comma (a b : Nat) (rest : List Located) : ListBoundary (⟨.punct .comma, a, b⟩ :: rest)
  | rparen (a b : Nat) (rest : List Located) : ListBoundary (⟨.punct .rparen, a, b⟩ :: rest)

theorem list_boundary_type (rest : List Located) (h : ListBoundary rest) : ParserContext.Boundary rest := by
  cases h with
  | eof => exact .eof
  | comma a b rest => exact .comma a b rest
  | rparen a b rest => exact .rparen a b rest

theorem list_boundary_no_ident (rest : List Located) (h : ListBoundary rest)
    (ch : List Choice) (eof : Nat) : optIdent ⟨rest, ch, eof⟩ = .ok (none, ⟨rest, ch, eof⟩) := by
  cases h <;> rfl

/-- A Prop naming the frozen parameter subterm after its type. -/
def ParamTailExact (t : Syn .typeName) (loc : Option DataLoc) (name : Option String)
    (input output : St) : Prop :=
  (show P (Syn .param) from do
    let l ← do match ← peek with
      | some tok => match locOf tok with
        | some location => advance; pure (some location)
        | none => pure none
      | none => pure none
    let nm ← optIdent
    return .param t l nm) input = .ok (.param t loc name, output)

theorem param_tail_complete (t : Syn .typeName) (loc : Option DataLoc) (name : Option String)
    (front rest : List Located) (hp : front.map Located.tok = optToks DataLoc.toks loc ++ optToks idt name)
    (hb : ListBoundary rest) (ch : List Choice) (eof : Nat) :
    ParamTailExact t loc name ⟨front ++ rest, ch, eof⟩ ⟨rest, ch, eof⟩ := by
  obtain ⟨locations, names, he, hl, hn⟩ := located_append front (optToks DataLoc.toks loc) (optToks idt name) hp
  cases he
  cases loc with
  | none =>
    have he := located_nil locations hl
    cases he
    cases name with
    | none =>
      have he := located_nil names hn
      cases he
      cases hb <;> rfl
    | some name =>
      obtain ⟨a, b, he⟩ := located_one names _ hn
      cases he
      rfl
  | some location =>
    have hname := opt_ident_complete name names rest ch eof hn (list_boundary_no_ident rest hb ch eof)
    cases location <;> obtain ⟨a, b, he⟩ := located_one locations _ hl <;> cases he <;>
      unfold ParamTailExact <;>
      change (optIdent ⟨names ++ rest, ch, eof⟩ >>= _) = _ <;>
      rw [hname] <;> rfl

theorem trailer_type_boundary (loc : Option DataLoc) (name : Option String)
    (front rest : List Located) (hp : front.map Located.tok = optToks DataLoc.toks loc ++ optToks idt name)
    (hb : ListBoundary rest) : ParserContext.Boundary (front ++ rest) := by
  obtain ⟨locations, names, he, hl, hn⟩ := located_append front (optToks DataLoc.toks loc) (optToks idt name) hp
  cases he
  rw [List.append_assoc]
  cases loc with
  | none =>
    have he := located_nil locations hl
    cases he
    exact name_boundary name names rest hn (list_boundary_type rest hb)
  | some location =>
    cases location <;> obtain ⟨a, b, he⟩ := located_one locations _ hl <;> cases he <;> first
      | exact .memory a b (names ++ rest)
      | exact .storage a b (names ++ rest)
      | exact .calldata a b (names ++ rest)

def paramTokens (tokens : List Tok) (loc : Option DataLoc) (name : Option String) : List Tok :=
  tokens ++ (optToks DataLoc.toks loc ++ optToks idt name)

def ParamAt (p : Syn .param) (tokens : List Tok) (layout : List Choice) (budget : Nat) : Prop :=
  ∀ fuel : Nat, budget ≤ fuel → ∀ front rest : List Located,
    front.map Located.tok = tokens → ListBoundary rest → ∀ ch : List Choice, ∀ eof : Nat,
    param fuel ⟨front ++ rest, ch, eof⟩ = .ok (p, ⟨rest, layout.reverse ++ ch, eof⟩)

theorem param_prefix (t : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (budget fuel : Nat) (hc : CompleteAt t tokens layout budget) (hf : budget ≤ fuel)
    (loc : Option DataLoc) (name : Option String) (front rest : List Located)
    (hp : front.map Located.tok = paramTokens tokens loc name) (hb : ListBoundary rest)
    (ch : List Choice) (eof : Nat) :
    param (fuel + 1) ⟨front ++ rest, ch, eof⟩ = .ok (.param t loc name, ⟨rest, layout.reverse ++ ch, eof⟩) := by
  obtain ⟨types, trailer, he, ht, htr⟩ := located_append front tokens (optToks DataLoc.toks loc ++ optToks idt name) hp
  cases he
  have hboundary := trailer_type_boundary loc name trailer rest htr hb
  have htype := hc fuel hf types (trailer ++ rest) ht hboundary ch eof
  have htail := param_tail_complete t loc name trailer rest htr hb (layout.reverse ++ ch) eof
  change (typeName fuel ⟨(types ++ trailer) ++ rest, ch, eof⟩ >>= _) = _
  rw [List.append_assoc, htype]
  exact htail

theorem param_complete (t : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (budget : Nat) (hc : CompleteAt t tokens layout budget) (loc : Option DataLoc) (name : Option String) :
    ParamAt (.param t loc name) (paramTokens tokens loc name) layout (budget + 1) := by
  intro fuel hf front rest hp hb ch eof
  have he : fuel - (budget + 1) + budget + 1 = fuel :=
    (Nat.add_assoc _ _ _).trans (Nat.sub_add_cancel hf)
  have hn : budget ≤ fuel - (budget + 1) + budget := Nat.le_add_left _ _
  rw [← he]
  exact param_prefix t tokens layout budget _ hc hn loc name front rest hp hb ch eof

theorem param_yield (t : Syn .typeName) (loc : Option DataLoc) (name : Option String)
    (input : List Choice) :
    (Syn.param t loc name).yield input =
      (t.yield input >>= fun r => some ([paramTokens r.1.flatten loc name], r.2)) := by
  change (t.yield input >>= _) = _
  cases hy : t.yield input with
  | none => rfl
  | some pair =>
    cases pair with
    | mk chunks remaining =>
      change some ([chunks.flatten ++ optToks DataLoc.toks loc ++ optToks idt name], remaining) =
        some ([chunks.flatten ++ (optToks DataLoc.toks loc ++ optToks idt name)], remaining)
      exact congrArg (fun ts => some ([ts], remaining))
        (List.append_assoc chunks.flatten (optToks DataLoc.toks loc) (optToks idt name))

theorem param_prec_converse (t : Syn .typeName) (loc : Option DataLoc) (name : Option String)
    (h : (Syn.param t loc name).prec = true) : t.prec = true := by
  change (true && (true && t.all Syn.precNode)) = true at h
  have ha : t.all Syn.precNode = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2
  unfold Syn.prec
  rw [type_prec_node, ha]
  rfl

theorem param_length (tokens : List Tok) (loc : Option DataLoc) (name : Option String) :
    tokens.length ≤ (paramTokens tokens loc name).length := by
  unfold paramTokens
  rw [List.length_append]
  exact Nat.le_add_right _ _

/-- Parameter prefix evidence includes the one frame above its type budget.
The function's real parentheses/keyword supply the eventual frozen-fuel slack. -/
def ParamCertified (p : Syn .param) : Prop :=
  ∀ input : List Choice, ∀ chunks : List (List Tok), ∀ remaining : List Choice,
    p.yield input = some (chunks, remaining) → p.prec = true →
    ∃ layout : List Choice, ∃ budget : Nat,
      1 ≤ budget ∧ ParamAt p chunks.flatten layout budget ∧ YieldExact p layout [chunks.flatten] ∧
        budget ≤ 16 * (chunks.flatten.length + 1) + 1

theorem param_certified (t : Syn .typeName) (hc : PrefixCertified t)
    (loc : Option DataLoc) (name : Option String) : ParamCertified (.param t loc name) := by
  intro input chunks remaining hy hp
  rw [param_yield] at hy
  cases hv : t.yield input with
  | none => rw [hv] at hy; cases hy
  | some pair =>
    cases pair with
    | mk items afterType =>
      rw [hv] at hy
      change some ([paramTokens items.flatten loc name], afterType) = some (chunks, remaining) at hy
      have he : [paramTokens items.flatten loc name] = chunks := (Prod.mk.inj (Option.some.inj hy)).1
      have ht : chunks.flatten = paramTokens items.flatten loc name := by
        rw [← he]
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      obtain ⟨layout, cost, need, hn, hr, hx, hb⟩ := hc input items afterType hv (param_prec_converse t loc name hp)
      have htype := ready_completeAt t items.flatten layout cost need hn hr
      have hprint := exact_param t loc name layout [items.flatten] hx
      have hcanon : YieldExact (.param t loc name) layout [paramTokens items.flatten loc name] := by
        simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using hprint
      have hlen := param_length items.flatten loc name
      have hbudget : need + cost ≤ 16 * ((paramTokens items.flatten loc name).length + 1) :=
        Nat.le_trans hb (Nat.mul_le_mul_left 16 (Nat.succ_le_succ hlen))
      rw [ht]
      exact ⟨layout, need + cost + 1, Nat.succ_le_succ (Nat.zero_le _),
        param_complete t items.flatten layout (need + cost) htype loc name,
        hcanon, Nat.add_le_add_right hbudget 1⟩

inductive ListEnd : List Located → Prop where
  | eof : ListEnd []
  | rparen (a b : Nat) (rest : List Located) : ListEnd (⟨.punct .rparen, a, b⟩ :: rest)

theorem list_end_boundary (rest : List Located) (h : ListEnd rest) : ListBoundary rest := by
  cases h with
  | eof => exact .eof
  | rparen a b rest => exact .rparen a b rest

theorem list_end_no_comma (rest : List Located) (h : ListEnd rest) (ch : List Choice) (eof : Nat) :
    eat (.punct .comma) ⟨rest, ch, eof⟩ = .ok (false, ⟨rest, ch, eof⟩) := by
  cases h <;> rfl

def tailTokens : List (List Tok) → List Tok
  | [] => []
  | head :: rest => .punct .comma :: (head ++ tailTokens rest)

theorem commaSep_head (head : List Tok) (rest : List (List Tok)) :
    commaSep (head :: rest) = head ++ tailTokens rest := by
  induction rest generalizing head with
  | nil => rfl
  | cons next rest ih =>
    change head ++ (.punct .comma :: commaSep (next :: rest)) =
      head ++ (.punct .comma :: (next ++ tailTokens rest))
    rw [ih next]

def paramValues {c : Cat} (s : Syn c) : List (Syn .param) :=
  match c, s with
  | .list .param, .cons head rest => head :: paramValues rest
  | _, _ => []
termination_by structural s

/-- The indexed-list inverse is unconditional; certificates are not premises. -/
def ParamListInverse {c : Cat} (s : Syn c) : Prop :=
  ∀ h : c = .list .param, toSynList (paramValues s) = h ▸ s

theorem param_list_inverse {c : Cat} (s : Syn c) : ParamListInverse s := by
  induction s <;> intro h <;> cases h
  · simp only [paramValues, toSynList]
  · simp only [paramValues, toSynList]
    apply congrArg (Syn.cons _)
    exact (by assumption : ParamListInverse _) rfl

theorem param_values_to_syn (ps : Syn (.list .param)) : toSynList (paramValues ps) = ps := by
  exact param_list_inverse ps rfl

/-- Intrinsic list evidence: a single common param fuel serves every element;
separator repetition has a separate real-token-derived bound. -/
inductive ListReady : Syn (.list .param) → List (List Tok) → List Choice → Nat → Prop where
  | nil : ListReady .nil [] [] 1
  | cons (p : Syn .param) (ps : Syn (.list .param)) (tokens : List Tok)
      (headLayout : List Choice) (headBudget : Nat) (items : List (List Tok))
      (restLayout : List Choice) (restBudget : Nat)
      (headPositive : 1 ≤ headBudget) (headParser : ParamAt p tokens headLayout headBudget)
      (headPrinter : YieldExact p headLayout [tokens])
      (headBound : headBudget ≤ 16 * (tokens.length + 1) + 1)
      (tail : ListReady ps items restLayout restBudget) :
      ListReady (.cons p ps) (tokens :: items) (headLayout ++ restLayout) (max headBudget restBudget)

theorem list_ready_to_syn (ps : Syn (.list .param)) (items : List (List Tok)) (layout : List Choice)
    (budget : Nat) (h : ListReady ps items layout budget) : toSynList (paramValues ps) = ps := by
  induction h with
  | nil => simp only [paramValues, toSynList]
  | cons p ps tokens hl hb items rl rb hp hparser hprinter hbound tail ih =>
    simp only [paramValues, toSynList]
    exact congrArg (Syn.cons p) ih

theorem list_ready_positive (ps : Syn (.list .param)) (items : List (List Tok)) (layout : List Choice)
    (budget : Nat) (h : ListReady ps items layout budget) : 1 ≤ budget := by
  cases h with
  | nil => exact Nat.le_refl 1
  | cons p ps tokens hl hb items rl rb hp hparser hprinter hbound tail =>
    exact Nat.le_trans hp (Nat.le_max_left _ _)

theorem list_ready_exact (ps : Syn (.list .param)) (items : List (List Tok)) (layout : List Choice)
    (budget : Nat) (h : ListReady ps items layout budget) : YieldExact ps layout items := by
  induction h with
  | nil => exact exact_params_nil
  | cons p ps tokens hl hb items rl rb hp hparser hprinter hbound tail ih =>
    have he := exact_params_cons p ps hl rl [tokens] items hprinter ih
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using he

theorem tail_tokens_boundary (items : List (List Tok)) (front rest : List Located)
    (hp : front.map Located.tok = tailTokens items) (hb : ListEnd rest) : ListBoundary (front ++ rest) := by
  cases items with
  | nil =>
    have he := located_nil front hp
    cases he
    exact list_end_boundary rest hb
  | cons head items =>
    obtain ⟨first, tail, he, ht, hr⟩ := located_cons front _ _ hp
    cases he
    cases first with
    | mk tok a b =>
      cases ht
      exact .comma a b (tail ++ rest)

theorem sep_aux_step (fuel repetition : Nat) (head : Syn .param) (tail : List (Syn .param))
    (a b : Nat) (input : St) (middle output : St)
    (hp : param fuel input = .ok (head, middle))
    (hs : sepByAux (param fuel) repetition middle = .ok (tail, output)) :
    sepByAux (param fuel) (repetition + 1)
      ⟨⟨.punct .comma, a, b⟩ :: input.ts, input.ch, input.eof⟩ = .ok (head :: tail, output) := by
  change (param fuel input >>= _) = _
  rw [hp]
  change (sepByAux (param fuel) repetition middle >>= _) = _
  rw [hs]
  rfl

theorem sep_aux_complete (ps : Syn (.list .param)) (items : List (List Tok)) (layout : List Choice)
    (budget : Nat) (h : ListReady ps items layout budget) (fuel : Nat) (hf : budget ≤ fuel)
    (n : Nat) (front rest : List Located) (hp : front.map Located.tok = tailTokens items)
    (hb : ListEnd rest) (ch : List Choice) (eof : Nat) :
    sepByAux (param fuel) (n + items.length + 1) ⟨front ++ rest, ch, eof⟩ =
      .ok (paramValues ps, ⟨rest, layout.reverse ++ ch, eof⟩) := by
  induction h generalizing front ch with
  | nil =>
    have he := located_nil front hp
    cases he
    change (eat (.punct .comma) ⟨rest, ch, eof⟩ >>= _) = _
    rw [list_end_no_comma rest hb ch eof]
    simp only [paramValues, List.reverse_nil, List.nil_append]
    rfl
  | cons p ps tokens hl pb items rl rb hpos hparser hprinter hbound tail ih =>
    obtain ⟨comma, afterComma, he, ht, hac⟩ := located_cons front _ _ hp
    obtain ⟨heads, tails, he', hh, hs⟩ := located_append afterComma tokens (tailTokens items) hac
    cases he
    cases he'
    cases comma with
    | mk tok a b =>
      cases ht
      have hpbound : pb ≤ fuel := Nat.le_trans (Nat.le_max_left _ _) hf
      have hrbound : rb ≤ fuel := Nat.le_trans (Nat.le_max_right _ _) hf
      have hhead := hparser fuel hpbound heads (tails ++ rest) hh (tail_tokens_boundary items tails rest hs hb) ch eof
      have htail := ih hrbound tails hs (hl.reverse ++ ch)
      have hstep := sep_aux_step fuel (n + items.length + 1) p (paramValues ps) a b
        ⟨heads ++ (tails ++ rest), ch, eof⟩ ⟨tails ++ rest, hl.reverse ++ ch, eof⟩
        ⟨rest, rl.reverse ++ (hl.reverse ++ ch), eof⟩ hhead htail
      simpa only [List.append_assoc, List.cons_append, List.reverse_append, List.length_cons,
        Nat.add_assoc, paramValues] using hstep

theorem sep_aux_complete_ge (ps : Syn (.list .param)) (items : List (List Tok)) (layout : List Choice)
    (budget : Nat) (h : ListReady ps items layout budget) (fuel : Nat) (hf : budget ≤ fuel)
    (repetition : Nat) (hr : items.length + 1 ≤ repetition)
    (front rest : List Located) (hp : front.map Located.tok = tailTokens items)
    (hb : ListEnd rest) (ch : List Choice) (eof : Nat) :
    sepByAux (param fuel) repetition ⟨front ++ rest, ch, eof⟩ =
      .ok (paramValues ps, ⟨rest, layout.reverse ++ ch, eof⟩) := by
  have he : repetition - (items.length + 1) + items.length + 1 = repetition :=
    (Nat.add_assoc _ _ _).trans (Nat.sub_add_cancel hr)
  rw [← he]
  exact sep_aux_complete ps items layout budget h fuel hf _ front rest hp hb ch eof

theorem tail_tokens_count (items : List (List Tok)) : items.length ≤ (tailTokens items).length := by
  induction items with
  | nil => exact Nat.le_refl 0
  | cons head rest ih =>
    change rest.length + 1 ≤ (head ++ tailTokens rest).length + 1
    rw [List.length_append]
    exact Nat.succ_le_succ (Nat.le_trans ih (Nat.le_add_left _ _))

theorem sep_one_complete (p : Syn .param) (ps : Syn (.list .param))
    (tokens : List Tok) (items : List (List Tok)) (hl rl : List Choice) (pb rb : Nat)
    (hp : ParamAt p tokens hl pb) (ht : ListReady ps items rl rb)
    (fuel : Nat) (hf : max pb rb ≤ fuel) (front rest : List Located)
    (hfront : front.map Located.tok = commaSep (tokens :: items))
    (hb : ListEnd rest) (ch : List Choice) (eof : Nat) :
    sepBy1 (param fuel) ⟨front ++ rest, ch, eof⟩ =
      .ok (p :: paramValues ps, ⟨rest, (hl ++ rl).reverse ++ ch, eof⟩) := by
  rw [commaSep_head] at hfront
  obtain ⟨heads, tails, he, hh, hs⟩ := located_append front tokens (tailTokens items) hfront
  cases he
  have hhead := hp fuel (Nat.le_trans (Nat.le_max_left _ _) hf) heads (tails ++ rest) hh
    (tail_tokens_boundary items tails rest hs hb) ch eof
  have hlen : tails.length = (tailTokens items).length := by
    have he := congrArg List.length hs
    simpa only [List.length_map] using he
  have hcount : items.length + 1 ≤ (tails ++ rest).length + 1 := by
    rw [List.length_append, hlen]
    exact Nat.succ_le_succ (Nat.le_trans (tail_tokens_count items) (Nat.le_add_right _ _))
  have htail := sep_aux_complete_ge ps items rl rb ht fuel
    (Nat.le_trans (Nat.le_max_right _ _) hf) ((tails ++ rest).length + 1) hcount
    tails rest hs hb (hl.reverse ++ ch) eof
  rw [List.append_assoc]
  change (param fuel ⟨heads ++ (tails ++ rest), ch, eof⟩ >>= _) = _
  rw [hhead]
  change (sepByAux (param fuel) ((tails ++ rest).length + 1)
    ⟨tails ++ rest, hl.reverse ++ ch, eof⟩ >>= _) = _
  rw [htail]
  simp only [List.reverse_append, List.append_assoc]
  rfl

theorem comma_sep_tail_length (items : List (List Tok)) : (commaSep items).length ≤ (tailTokens items).length := by
  cases items with
  | nil => exact Nat.le_refl 0
  | cons head rest =>
    rw [commaSep_head]
    change (head ++ tailTokens rest).length ≤ (head ++ tailTokens rest).length + 1
    exact Nat.le_succ _

theorem list_ready_budget (ps : Syn (.list .param)) (items : List (List Tok)) (layout : List Choice)
    (budget : Nat) (h : ListReady ps items layout budget) :
    budget ≤ 16 * ((commaSep items).length + 1) + 1 := by
  induction h with
  | nil => exact Nat.le_add_left 1 16
  | cons p ps tokens hl pb items rl rb hpos hparser hprinter hbound tail ih =>
    rw [commaSep_head, List.length_append]
    apply Nat.max_le.mpr
    constructor
    · exact Nat.le_trans hbound (Nat.add_le_add_right
        (Nat.mul_le_mul_left 16 (Nat.succ_le_succ (Nat.le_add_right _ _))) 1)
    · exact Nat.le_trans ih (Nat.add_le_add_right (Nat.mul_le_mul_left 16
        (Nat.succ_le_succ (Nat.le_trans (comma_sep_tail_length items) (Nat.le_add_left _ _)))) 1)

def ParamsCertified (ps : Syn (.list .param)) : Prop :=
  ∀ input : List Choice, ∀ items : List (List Tok), ∀ remaining : List Choice,
    ps.yield input = some (items, remaining) → ps.prec = true →
    ∃ layout : List Choice, ∃ budget : Nat, ListReady ps items layout budget

theorem params_nil_certified : ParamsCertified .nil := by
  intro input items remaining hy hp
  change some ([], input) = some (items, remaining) at hy
  have he : items = [] := (Prod.mk.inj (Option.some.inj hy)).1.symm
  rw [he]
  exact ⟨[], 1, .nil⟩

theorem params_cons_prec (p : Syn .param) (ps : Syn (.list .param))
    (hp : (Syn.cons p ps).prec = true) : p.prec = true ∧ ps.prec = true := by
  change (true && (true && p.all Syn.precNode && ps.all Syn.precNode)) = true at hp
  have hp' := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hp).2
  have hh : p.all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp'.1).2
  constructor
  · cases p
    change (true && _) = true
    rw [hh]
    rfl
  · cases ps <;> change (true && _) = true <;> rw [hp'.2] <;> rfl

theorem params_cons_certified (p : Syn .param) (ps : Syn (.list .param))
    (hc : ParamCertified p) (hr : ParamsCertified ps) : ParamsCertified (.cons p ps) := by
  intro input items remaining hy hp
  obtain ⟨head, tail, middle, hh, ht, he⟩ := params_cons_decompose p ps input remaining items hy
  obtain ⟨pp, pr⟩ := params_cons_prec p ps hp
  obtain ⟨hl, pb, hpos, hparser, hprinter, hbound⟩ := hc input head middle hh pp
  obtain ⟨rl, rb, hrest⟩ := hr middle tail remaining ht pr
  rw [he]
  exact ⟨hl ++ rl, max pb rb, .cons p ps head.flatten hl pb tail rl rb
    hpos hparser hprinter hbound hrest⟩

theorem param_rparen_no_success (fuel a b : Nat) (rest : List Located)
    (ch : List Choice) (eof : Nat) (p : Syn .param) (output : St)
    (hp : param fuel ⟨⟨.punct .rparen, a, b⟩ :: rest, ch, eof⟩ = .ok (p, output)) : False := by
  cases fuel with
  | zero => cases hp
  | succ fuel =>
    cases fuel <;> change (Except.error _ : Except Error _) = .ok _ at hp <;> cases hp

theorem param_success_no_close (fuel : Nat) (s output : St) (p : Syn .param)
    (hp : param fuel s = .ok (p, output)) :
    eat (.punct .rparen) s = .ok (false, s) := by
  cases s with
  | mk ts ch eof =>
    cases ts with
    | nil => rfl
    | cons first rest =>
      cases first with
      | mk tok a b =>
        cases tok <;> try rfl
        case punct punct =>
          cases punct <;> try rfl
          exact False.elim (param_rparen_no_success fuel a b rest ch eof p output hp)

/-- Real closing-parenthesis completeness. EOF is never substituted for ')'. -/
theorem params_paren_complete (ps : Syn (.list .param)) (items : List (List Tok)) (layout : List Choice)
    (budget : Nat) (h : ListReady ps items layout budget) (fuel : Nat) (hf : budget ≤ fuel)
    (a b c d : Nat) (front rest : List Located) (hp : front.map Located.tok = commaSep items)
    (ch : List Choice) (eof : Nat) :
    paramsParen (fuel + 1)
      ⟨⟨.punct .lparen, a, b⟩ :: (front ++ ⟨.punct .rparen, c, d⟩ :: rest), ch, eof⟩ =
      .ok (ps, ⟨rest, layout.reverse ++ ch, eof⟩) := by
  cases h with
  | nil =>
    have he := located_nil front hp
    cases he
    simp only [List.reverse_nil, List.nil_append]
    rfl
  | cons p ps tokens hl pb items rl rb hpos hparser hprinter hbound tail =>
    have hsep := sep_one_complete p ps tokens items hl rl pb rb hparser tail fuel hf
      front (⟨.punct .rparen, c, d⟩ :: rest) hp (.rparen c d rest) ch eof
    have hfirst : ∃ middle : St,
        param fuel ⟨front ++ ⟨.punct .rparen, c, d⟩ :: rest, ch, eof⟩ = .ok (p, middle) := by
      rw [commaSep_head] at hp
      obtain ⟨heads, tails, he, hh, hs⟩ := located_append front tokens (tailTokens items) hp
      cases he
      rw [List.append_assoc]
      exact ⟨_, hparser fuel (Nat.le_trans (Nat.le_max_left _ _) hf) heads
        (tails ++ ⟨.punct .rparen, c, d⟩ :: rest) hh
        (tail_tokens_boundary items tails _ hs (.rparen c d rest)) ch eof⟩
    obtain ⟨middle, hfirst⟩ := hfirst
    have hclose := param_success_no_close fuel _ middle p hfirst
    change (eat (.punct .rparen) ⟨front ++ ⟨.punct .rparen, c, d⟩ :: rest, ch, eof⟩ >>= _) = _
    rw [hclose]
    change (sepBy1 (param fuel) ⟨front ++ ⟨.punct .rparen, c, d⟩ :: rest, ch, eof⟩ >>= _) = _
    rw [hsep]
    have he := list_ready_to_syn (.cons p ps) (tokens :: items) (hl ++ rl) (max pb rb)
      (.cons p ps tokens hl pb items rl rb hpos hparser hprinter hbound tail)
    change (Except.ok (toSynList (p :: paramValues ps), (⟨rest, (hl ++ rl).reverse ++ ch, eof⟩ : St)) : Except Error _) = _
    simp only [paramValues] at he
    rw [he]

/-- Inhabited controls of arbitrary length, covering every elementary family,
all three locations or their absence, and arbitrary optional parameter names. -/
def elemParams : List (Elem × Option DataLoc × Option String) → Syn (.list .param)
  | [] => .nil
  | (e, loc, name) :: rest => .cons (.param (.elem e) loc name) (elemParams rest)

def elemParamItems (frames : List (Elem × Option DataLoc × Option String)) : List (List Tok) :=
  frames.map (fun (e, loc, name) => paramTokens e.toks loc name)

theorem elem_params_certified (frames : List (Elem × Option DataLoc × Option String)) :
    ParamsCertified (elemParams frames) := by
  induction frames with
  | nil => exact params_nil_certified
  | cons frame rest ih =>
    cases frame with
    | mk e pair =>
      cases pair with
      | mk loc name => exact params_cons_certified _ _ (param_certified _ (prefix_elem e) loc name) ih

theorem elem_params_exact (frames : List (Elem × Option DataLoc × Option String)) :
    YieldExact (elemParams frames) [] (elemParamItems frames) := by
  induction frames with
  | nil => exact exact_params_nil
  | cons frame rest ih =>
    cases frame with
    | mk e pair =>
      cases pair with
      | mk loc name =>
        have hh := exact_param (.elem e) loc name [] [e.toks] (exact_elem e)
        have hp : YieldExact (.param (.elem e) loc name) [] [paramTokens e.toks loc name] := by
          simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using hh
        have hl := exact_params_cons (.param (.elem e) loc name) (elemParams rest) [] []
          [paramTokens e.toks loc name] (elemParamItems rest) hp ih
        simpa only [elemParams, elemParamItems, List.map_cons, List.nil_append,
          List.flatten_cons, List.flatten_nil, List.append_nil] using hl

theorem elem_params_prec (frames : List (Elem × Option DataLoc × Option String)) :
    (elemParams frames).prec = true := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
    cases frame with
    | mk e pair =>
      cases pair with
      | mk loc name =>
        have hr : (elemParams rest).all Syn.precNode = true := (Bool.and_eq_true_iff.mp ih).2
        change (true && (true && (true && true) && (elemParams rest).all Syn.precNode)) = true
        rw [hr]
        rfl

theorem elem_params_ready (frames : List (Elem × Option DataLoc × Option String)) :
    ∃ layout : List Choice, ∃ budget : Nat,
      ListReady (elemParams frames) (elemParamItems frames) layout budget := by
  have hy := elem_params_exact frames []
  simp only [List.nil_append] at hy
  exact elem_params_certified frames [] (elemParamItems frames) [] hy (elem_params_prec frames)

theorem elem_params_parse (frames : List (Elem × Option DataLoc × Option String)) :
    ∃ layout : List Choice, ∃ budget : Nat,
      budget ≤ 16 * ((commaSep (elemParamItems frames)).length + 1) + 1 ∧
      ∀ fuel : Nat, budget ≤ fuel → ∀ a b c d : Nat, ∀ front rest : List Located,
        front.map Located.tok = commaSep (elemParamItems frames) → ∀ ch : List Choice, ∀ eof : Nat,
        paramsParen (fuel + 1)
          ⟨⟨.punct .lparen, a, b⟩ :: (front ++ ⟨.punct .rparen, c, d⟩ :: rest), ch, eof⟩ =
          .ok (elemParams frames, ⟨rest, layout.reverse ++ ch, eof⟩) := by
  obtain ⟨layout, budget, hr⟩ := elem_params_ready frames
  exact ⟨layout, budget, list_ready_budget _ _ _ _ hr,
    fun fuel hf a b c d front rest hp ch eof =>
      params_paren_complete _ _ _ _ hr fuel hf a b c d front rest hp ch eof⟩

theorem missing_close_refused (a b c d eof : Nat) (ch : List Choice) :
    paramsParen 6 ⟨[⟨.punct .lparen, a, b⟩, ⟨.elem .bool, c, d⟩], ch, eof⟩ =
      .error ⟨eof, "expected ')'"⟩ := by
  rfl

theorem duplicate_comma_refused (a b c d e f g h : Nat) (rest : List Located)
    (ch : List Choice) (eof : Nat) :
    paramsParen 6 ⟨⟨.punct .lparen, a, b⟩ :: ⟨.elem .bool, c, d⟩ ::
      ⟨.punct .comma, e, f⟩ :: ⟨.punct .comma, g, h⟩ :: rest, ch, eof⟩ =
      .error ⟨g, "expected a type name"⟩ := by
  rfl

#print axioms list_boundary_type
#print axioms list_boundary_no_ident
#print axioms param_tail_complete
#print axioms trailer_type_boundary
#print axioms param_prefix
#print axioms param_complete
#print axioms param_yield
#print axioms param_prec_converse
#print axioms param_length
#print axioms param_certified
#print axioms list_end_boundary
#print axioms list_end_no_comma
#print axioms commaSep_head
#print axioms param_list_inverse
#print axioms param_values_to_syn
#print axioms list_ready_to_syn
#print axioms list_ready_positive
#print axioms list_ready_exact
#print axioms tail_tokens_boundary
#print axioms sep_aux_step
#print axioms sep_aux_complete
#print axioms sep_aux_complete_ge
#print axioms tail_tokens_count
#print axioms sep_one_complete
#print axioms comma_sep_tail_length
#print axioms list_ready_budget
#print axioms params_nil_certified
#print axioms params_cons_prec
#print axioms params_cons_certified
#print axioms param_rparen_no_success
#print axioms param_success_no_close
#print axioms params_paren_complete
#print axioms elem_params_certified
#print axioms elem_params_exact
#print axioms elem_params_prec
#print axioms elem_params_ready
#print axioms elem_params_parse
#print axioms missing_close_refused
#print axioms duplicate_comma_refused
end Solidity.Frontend.TypeGrammarH28.ParserParams
