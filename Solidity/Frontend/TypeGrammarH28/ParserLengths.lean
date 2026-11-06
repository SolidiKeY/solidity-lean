import Solidity.Frontend.TypeGrammarH28.ParserFunctions
import Solidity.Frontend.TypeGrammarH28.TypeRegions

/-! Static array lengths remain read-only expression atoms. The explicit
contract below is about the actual expression parser, not type identity,
constant evaluation, admission or a replacement expression implementation. -/
namespace Solidity.Frontend.TypeGrammarH28.ParserLength
open Solidity.Source Solidity.Frontend.Checked ParserBasic ParserCheck ParserPath ParserArray
  ParserContext ParserMapping ParserReady ParserParams ParserFunction

/-- Actual independent atom parsing, stopping before a real closing bracket
with arbitrary locations, following tokens, choices and EOF. -/
def ExprAt (e : Syn .expr) (tokens : List Tok) (layout : List Choice) (budget : Nat) : Prop :=
  ∀ fuel : Nat, budget ≤ fuel → ∀ front : List Located,
    front.map Located.tok = tokens → ∀ a b : Nat, ∀ rest : List Located,
    ∀ ch : List Choice, ∀ eof : Nat,
    expr fuel ⟨front ++ ⟨.punct .rbrack, a, b⟩ :: rest, ch, eof⟩ =
      .ok (e, ⟨⟨.punct .rbrack, a, b⟩ :: rest, layout.reverse ++ ch, eof⟩)

/-- Dependencies on an expression atom are named explicitly. This is not
assumed for every expression, and assumes no final type-name theorem. -/
def LengthAtom (e : Syn .expr) : Prop :=
  ∀ input : List Choice, ∀ chunks : List (List Tok), ∀ remaining : List Choice,
    e.yield input = some (chunks, remaining) → e.prec = true →
    ∃ layout : List Choice, ∃ budget : Nat,
      1 ≤ budget ∧ ExprAt e chunks.flatten layout budget ∧
      YieldExact e layout [chunks.flatten] ∧ budget ≤ 16 * (chunks.flatten.length + 1) ∧
      Boundary.Balanced chunks.flatten ∧ chunks.flatten ≠ []

theorem balanced_front_no_close (tokens : List Tok) (h : Boundary.Balanced tokens) (hn : tokens ≠ [])
    (front rest : List Located) (hp : front.map Located.tok = tokens) (ch : List Choice) (eof : Nat) :
    eat (.punct .rbrack) ⟨front ++ rest, ch, eof⟩ = .ok (false, ⟨front ++ rest, ch, eof⟩) := by
  cases h with
  | nil => exact False.elim (hn rfl)
  | atom tok tokens hplain hb =>
    obtain ⟨first, tail, he, ht, hr⟩ := located_cons front _ _ hp
    cases he
    cases first with
    | mk t a b =>
      cases ht
      cases t <;> try rfl
      case punct punct =>
        cases punct <;> try rfl
        cases hplain
  | group d inside tokens hi hr =>
    obtain ⟨first, tail, he, ht, hr⟩ := located_cons front _ _ hp
    cases he
    cases first with
    | mk t a b =>
      cases ht
      cases d <;> rfl

theorem expr_ident_before_close (name : String) (n a b c d : Nat) (rest : List Located)
    (ch : List Choice) (eof : Nat) :
    expr (n + 5) ⟨⟨.ident name, a, b⟩ :: ⟨.punct .rbrack, c, d⟩ :: rest, ch, eof⟩ =
      .ok (.ident name, ⟨⟨.punct .rbrack, c, d⟩ :: rest, ch, eof⟩) := by
  rfl

theorem expr_num_before_close (value : NumLit) (n a b c d : Nat) (rest : List Located)
    (ch : List Choice) (eof : Nat) :
    expr (n + 5) ⟨⟨.num value, a, b⟩ :: ⟨.punct .rbrack, c, d⟩ :: rest, ch, eof⟩ =
      .ok (.lit (.num value), ⟨⟨.punct .rbrack, c, d⟩ :: rest, ch, eof⟩) := by
  rfl

theorem ident_expr_at (name : String) : ExprAt (.ident name) [.ident name] [] 5 := by
  intro fuel hf front hp a b rest ch eof
  obtain ⟨c, d, he⟩ := located_one front _ hp
  cases he
  have hs := expr_ident_before_close name (fuel - 5) c d a b rest ch eof
  rw [Nat.sub_add_cancel hf] at hs
  simpa only [List.reverse_nil, List.nil_append] using hs

theorem num_expr_at (value : NumLit) : ExprAt (.lit (.num value)) [.num value] [] 5 := by
  intro fuel hf front hp a b rest ch eof
  obtain ⟨c, d, he⟩ := located_one front _ hp
  cases he
  have hs := expr_num_before_close value (fuel - 5) c d a b rest ch eof
  rw [Nat.sub_add_cancel hf] at hs
  simpa only [List.reverse_nil, List.nil_append] using hs

theorem ident_length_atom (name : String) : LengthAtom (.ident name) := by
  intro input chunks remaining hy hp
  change some ([[.ident name]], input) = some (chunks, remaining) at hy
  have he : chunks = [[.ident name]] := (Prod.mk.inj (Option.some.inj hy)).1.symm
  have hflat : chunks.flatten = [.ident name] := by
    rw [he, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [hflat]
  exact ⟨[], 5, by decide, ident_expr_at name, (fun suffix => rfl), (by decide : 5 ≤ 32),
    .atom _ _ rfl .nil, by intro h; cases h⟩

theorem num_length_atom (value : NumLit) : LengthAtom (.lit (.num value)) := by
  intro input chunks remaining hy hp
  change some ([[.num value]], input) = some (chunks, remaining) at hy
  have he : chunks = [[.num value]] := (Prod.mk.inj (Option.some.inj hy)).1.symm
  have hflat : chunks.flatten = [.num value] := by
    rw [he, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [hflat]
  exact ⟨[], 5, by decide, num_expr_at value, (fun suffix => rfl), (by decide : 5 ≤ 32),
    .atom _ _ rfl .nil, by intro h; cases h⟩

theorem expr_zero_not_complete (name : String) : ¬ ExprAt (.ident name) [.ident name] [] 0 := by
  intro h
  have he := h 0 (Nat.le_refl 0) [⟨.ident name, 0, 1⟩] rfl 1 2 [] [] 2
  cases he

def staticTokens (base atom : List Tok) : List Tok :=
  base ++ pu .lbrack ++ atom ++ pu .rbrack

theorem suffix_static_step (base : Syn .typeName) (e : Syn .expr) (tokens : List Tok)
    (layout : List Choice) (budget : Nat) (he : ExprAt e tokens layout budget)
    (hbal : Boundary.Balanced tokens) (hn : tokens ≠ []) (fuel : Nat) (hf : budget ≤ fuel)
    (a b c d : Nat) (front rest : List Located) (hp : front.map Located.tok = tokens)
    (ch : List Choice) (eof : Nat) :
    typeSuffix (fuel + 1) base
      ⟨⟨.punct .lbrack, a, b⟩ :: (front ++ ⟨.punct .rbrack, c, d⟩ :: rest), ch, eof⟩ =
      typeSuffix fuel (.array base (.some e)) ⟨rest, layout.reverse ++ ch, eof⟩ := by
  have hclose := balanced_front_no_close tokens hbal hn front (⟨.punct .rbrack, c, d⟩ :: rest) hp ch eof
  have hexpr := he fuel hf front hp c d rest ch eof
  change (eat (.punct .rbrack) ⟨front ++ ⟨.punct .rbrack, c, d⟩ :: rest, ch, eof⟩ >>= _) = _
  rw [hclose]
  change (expr fuel ⟨front ++ ⟨.punct .rbrack, c, d⟩ :: rest, ch, eof⟩ >>= _) = _
  rw [hexpr]
  rfl

theorem ready_array_some (base : Syn .typeName) (e : Syn .expr) (bt et : List Tok)
    (bl el : List Choice) (cost need budget : Nat)
    (hb : ReadyAt base bt bl cost need) (he : ExprAt e et el budget)
    (hbal : Boundary.Balanced et) (hn : et ≠ []) :
    ReadyAt (.array base (.some e)) (staticTokens bt et) (bl ++ el) (cost + 1) (need + budget + 1) := by
  intro residual hf front rest hp hr ch eof
  have hbn : need ≤ residual + 1 := Nat.le_trans
    (Nat.le_trans (Nat.le_add_right need (budget + 1)) hf) (Nat.le_succ _)
  have hen : budget ≤ residual := Nat.le_trans
    (Nat.le_trans (Nat.le_add_left budget need) (Nat.le_succ _)) hf
  simp only [staticTokens, List.append_assoc] at hp
  obtain ⟨baseFront, afterBase, hsplit, hbase, hafter⟩ := located_append front bt
    (pu .lbrack ++ (et ++ pu .rbrack)) hp
  obtain ⟨op, afterOpen, hsplit', hop, hafter'⟩ := located_cons afterBase _ _ hafter
  obtain ⟨exprFront, closeFront, hsplit'', hexpr, hclose⟩ := located_append afterOpen et (pu .rbrack) hafter'
  obtain ⟨c, d, hclose'⟩ := located_one closeFront _ hclose
  cases hsplit
  cases hsplit'
  cases hsplit''
  cases hclose'
  cases op with
  | mk tok a b =>
    cases hop
    have hparse := hb (residual + 1) hbn baseFront
      (⟨.punct .lbrack, a, b⟩ :: (exprFront ++ ⟨.punct .rbrack, c, d⟩ :: rest)) hbase
      (.array a b _) ch eof
    have hs := suffix_static_step base e et el budget he hbal hn residual hen a b c d
      exprFront rest hexpr (bl.reverse ++ ch) eof
    simp only [List.append_assoc, List.cons_append, List.nil_append] at *
    have hout := hparse.trans hs
    have hcost : residual + (cost + 1) = residual + 1 + cost := Nat.add_right_comm residual cost 1
    rw [hcost]
    simpa only [List.reverse_append, List.append_assoc] using hout

theorem array_some_yield (base : Syn .typeName) (e : Syn .expr) (input : List Choice) :
    (Syn.array base (.some e)).yield input =
      (base.yield input >>= fun bt => e.yield bt.2 >>= fun et =>
        some ([staticTokens bt.1.flatten et.1.flatten], et.2)) := by
  change (base.yield input >>= fun bt => (Syn.some e).yield bt.2 >>= fun et =>
    some ([staticTokens bt.1.flatten et.1.flatten], et.2)) = _
  cases hb : base.yield input with
  | none => rfl
  | some pair =>
    cases pair with
    | mk bt afterBase =>
      change ((e.yield afterBase >>= fun et => some ([et.1.flatten], et.2)) >>=
        fun et => some ([staticTokens bt.flatten et.1.flatten], et.2)) =
        (e.yield afterBase >>= fun et => some ([staticTokens bt.flatten et.1.flatten], et.2))
      cases he : e.yield afterBase with
      | none => rfl
      | some pair =>
        cases pair with
        | mk et afterExpr =>
          change some ([staticTokens bt.flatten (et.flatten ++ [])], afterExpr) =
            some ([staticTokens bt.flatten et.flatten], afterExpr)
          rw [List.append_nil]

theorem all_node {c : Cat} (t : Syn c) (p : {d : Cat} → Syn d → Bool)
    (h : t.all p = true) : p t = true := by
  cases t <;> first
    | exact h
    | exact (Bool.and_eq_true_iff.mp h).1
    | exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
    | exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).1
    | exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).1).1
    | exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).1).1).1

theorem array_some_prec_converse (base : Syn .typeName) (e : Syn .expr)
    (h : (Syn.array base (.some e)).prec = true) : base.prec = true ∧ e.prec = true := by
  change (true && (true && base.all Syn.precNode && (true && e.all Syn.precNode))) = true at h
  have hb := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2
  have hbase : base.all Syn.precNode = true := (Bool.and_eq_true_iff.mp hb.1).2
  have he : e.all Syn.precNode = true := (Bool.and_eq_true_iff.mp hb.2).2
  constructor
  · unfold Syn.prec; rw [type_prec_node, hbase]; rfl
  · unfold Syn.prec; rw [all_node e Syn.precNode he, he]; rfl

theorem static_tokens_length (bt et : List Tok) :
    (staticTokens bt et).length = bt.length + et.length + 2 := by
  simp only [staticTokens, pu, List.length_append, List.length_cons, List.length_nil,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem static_budget (bt et : List Tok) (need cost budget : Nat)
    (hb : need + cost ≤ 16 * (bt.length + 1)) (he : budget ≤ 16 * (et.length + 1)) :
    need + budget + 1 + (cost + 1) ≤ 16 * ((staticTokens bt et).length + 1) := by
  have hl : need + budget + 1 + (cost + 1) = (need + cost) + budget + 2 := by
    simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  rw [hl]
  have hs := Nat.add_le_add_right (Nat.add_le_add hb he) 2
  have hs' := Nat.le_trans hs (Nat.add_le_add_left (by decide : 2 ≤ 16) _)
  have hr : 16 * (bt.length + 1) + 16 * (et.length + 1) + 16 =
      16 * ((staticTokens bt et).length + 1) := by
    rw [static_tokens_length]
    simp only [Nat.mul_add, Nat.mul_succ,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  rw [hr] at hs'
  exact hs'

theorem array_some_yield_decompose (base : Syn .typeName) (e : Syn .expr)
    (input remaining : List Choice) (chunks : List (List Tok))
    (hy : (Syn.array base (.some e)).yield input = some (chunks, remaining)) :
    ∃ bt et : List (List Tok), ∃ middle : List Choice,
      base.yield input = some (bt, middle) ∧ e.yield middle = some (et, remaining) ∧
      chunks = [staticTokens bt.flatten et.flatten] := by
  rw [array_some_yield] at hy
  cases hb : base.yield input with
  | none => rw [hb] at hy; cases hy
  | some pair =>
    cases pair with
    | mk bt middle =>
      rw [hb] at hy
      change (e.yield middle >>= fun et => some ([staticTokens bt.flatten et.1.flatten], et.2)) =
        some (chunks, remaining) at hy
      cases he : e.yield middle with
      | none => rw [he] at hy; cases hy
      | some pair =>
        cases pair with
        | mk et afterExpr =>
          rw [he] at hy
          change some ([staticTokens bt.flatten et.flatten], afterExpr) = some (chunks, remaining) at hy
          have hh := Prod.mk.inj (Option.some.inj hy)
          cases hh.2
          exact ⟨bt, et, middle, rfl, he, hh.1.symm⟩

/-- Static-array closure depends on the independent strict base and explicit
read-only atom contract, never on the resulting type's completeness/identity. -/
theorem prefix_array_some (base : Syn .typeName) (e : Syn .expr)
    (hb : PrefixCertified base) (he : LengthAtom e) : PrefixCertified (.array base (.some e)) := by
  intro input chunks remaining hy hp
  obtain ⟨bt, et, middle, hby, hey, hc⟩ := array_some_yield_decompose base e input remaining chunks hy
  obtain ⟨hbp, hep⟩ := array_some_prec_converse base e hp
  obtain ⟨bl, cost, need, hn, hready, hprint, hbudget⟩ := hb input bt middle hby hbp
  obtain ⟨el, budget, hepos, hexpr, heprint, hebudget, hebal, hen⟩ := he middle et remaining hey hep
  have hr := ready_array_some base e bt.flatten et.flatten bl el cost need budget hready hexpr hebal hen
  have hs : YieldExact (.some e) el [et.flatten] := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using exact_some_length e el [et.flatten] heprint
  have ht := exact_array base (.some e) bl el [bt.flatten] [et.flatten] hprint hs
  have hcanon : YieldExact (.array base (.some e)) (bl ++ el) [staticTokens bt.flatten et.flatten] := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using ht
  have hflat : chunks.flatten = staticTokens bt.flatten et.flatten := by
    rw [hc, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [hflat]
  exact ⟨bl ++ el, cost + 1, need + budget + 1,
    Nat.succ_le_succ (Nat.zero_le _), hr, hcanon, static_budget _ _ need cost budget hbudget hebudget⟩

theorem certified_array_some (base : Syn .typeName) (e : Syn .expr)
    (hb : PrefixCertified base) (he : LengthAtom e) : Certified (.array base (.some e)) := by
  exact prefix_to_certified _ (prefix_array_some base e hb he)

theorem array_some_parseType_iff (base : Syn .typeName) (e : Syn .expr)
    (hb : PrefixCertified base) (he : LengthAtom e) (src : Bytes) :
    parseType src = .ok (.array base (.some e)) ↔ ∃ pieces : List Piece, lex src = .ok pieces ∧
      ∃ layout : List Choice, (Syn.array base (.some e)).toks layout = some (tokensOf pieces) ∧
        (Syn.array base (.some e)).prec = true := by
  exact certified_parseType_iff _ (certified_array_some base e hb he) src

theorem array_some_prec (base : Syn .typeName) (e : Syn .expr)
    (hb : base.prec = true) (he : e.prec = true) : (Syn.array base (.some e)).prec = true := by
  have hba : base.all Syn.precNode = true := (Bool.and_eq_true_iff.mp hb).2
  have hea : e.all Syn.precNode = true := (Bool.and_eq_true_iff.mp he).2
  change (true && (true && base.all Syn.precNode && (true && e.all Syn.precNode))) = true
  rw [hba, hea]
  rfl

/-- A syntactic control builder only; no evaluation of its atom. -/
def staticTower (base : Syn .typeName) (e : Syn .expr) : Nat → Syn .typeName
  | 0 => base
  | depth + 1 => .array (staticTower base e depth) (.some e)

theorem static_tower_prefix (base : Syn .typeName) (e : Syn .expr)
    (hb : PrefixCertified base) (he : LengthAtom e) (depth : Nat) :
    PrefixCertified (staticTower base e depth) := by
  induction depth with
  | zero => exact hb
  | succ depth ih => exact prefix_array_some _ e ih he

theorem static_tower_prec (base : Syn .typeName) (e : Syn .expr)
    (hb : base.prec = true) (he : e.prec = true) (depth : Nat) :
    (staticTower base e depth).prec = true := by
  induction depth with
  | zero => exact hb
  | succ depth ih => exact array_some_prec _ e ih he

theorem static_tower_exact (base : Syn .typeName) (e : Syn .expr)
    (bl el : List Choice) (bt et : List Tok) (hb : YieldExact base bl [bt])
    (he : YieldExact e el [et]) (depth : Nat) :
    ∃ layout : List Choice, ∃ tokens : List Tok, YieldExact (staticTower base e depth) layout [tokens] := by
  induction depth with
  | zero => exact ⟨bl, bt, hb⟩
  | succ depth ih =>
    obtain ⟨layout, tokens, hx⟩ := ih
    have hs : YieldExact (.some e) el [et] := by
      simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using exact_some_length e el [et] he
    have ha := exact_array (staticTower base e depth) (.some e) layout el [tokens] [et] hx hs
    have hc : YieldExact (.array (staticTower base e depth) (.some e)) (layout ++ el) [staticTokens tokens et] := by
      simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using ha
    exact ⟨layout ++ el, staticTokens tokens et, hc⟩

theorem static_num_checked (e : Elem) (value : NumLit) (depth : Nat) :
    ∃ layout : List Choice, ∃ tokens : List Tok, ∃ parsed : List Choice,
      (staticTower (.elem e) (.lit (.num value)) depth).toks layout = some tokens ∧
      parseCatLocated typeName 0 (witnessLocations tokens) =
        .ok (staticTower (.elem e) (.lit (.num value)) depth, parsed) := by
  obtain ⟨layout, tokens, hx⟩ := static_tower_exact (.elem e) (.lit (.num value)) [] [] e.toks [.num value]
    (exact_elem e) (fun suffix => rfl) depth
  have ht : (staticTower (.elem e) (.lit (.num value)) depth).toks layout = some tokens := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using exact_toks _ _ _ hx
  have hc := static_tower_prefix (.elem e) (.lit (.num value)) (prefix_elem e) (num_length_atom value) depth
  obtain ⟨parsed, hp⟩ := certified_checked _ (prefix_to_certified _ hc) layout tokens ht
    (static_tower_prec (.elem e) (.lit (.num value)) rfl rfl depth) (witnessLocations tokens) 0
    (witness_locations_tokens tokens)
  exact ⟨layout, tokens, parsed, ht, hp⟩

theorem static_ident_checked (e : Elem) (name : String) (depth : Nat) :
    ∃ layout : List Choice, ∃ tokens : List Tok, ∃ parsed : List Choice,
      (staticTower (.elem e) (.ident name) depth).toks layout = some tokens ∧
      parseCatLocated typeName 0 (witnessLocations tokens) =
        .ok (staticTower (.elem e) (.ident name) depth, parsed) := by
  obtain ⟨layout, tokens, hx⟩ := static_tower_exact (.elem e) (.ident name) [] [] e.toks [.ident name]
    (exact_elem e) (fun suffix => rfl) depth
  have ht : (staticTower (.elem e) (.ident name) depth).toks layout = some tokens := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using exact_toks _ _ _ hx
  have hc := static_tower_prefix (.elem e) (.ident name) (prefix_elem e) (ident_length_atom name) depth
  obtain ⟨parsed, hp⟩ := certified_checked _ (prefix_to_certified _ hc) layout tokens ht
    (static_tower_prec (.elem e) (.ident name) rfl rfl depth) (witnessLocations tokens) 0
    (witness_locations_tokens tokens)
  exact ⟨layout, tokens, parsed, ht, hp⟩

theorem ident_expr_four_refused (name : String) (a b c d : Nat) (rest : List Located)
    (ch : List Choice) (eof : Nat) :
    expr 4 ⟨⟨.ident name, a, b⟩ :: ⟨.punct .rbrack, c, d⟩ :: rest, ch, eof⟩ =
      .error ⟨a, "nesting too deep"⟩ := by
  rfl

#print axioms balanced_front_no_close
#print axioms expr_ident_before_close
#print axioms expr_num_before_close
#print axioms ident_expr_at
#print axioms num_expr_at
#print axioms ident_length_atom
#print axioms num_length_atom
#print axioms expr_zero_not_complete
#print axioms suffix_static_step
#print axioms ready_array_some
#print axioms array_some_yield
#print axioms all_node
#print axioms array_some_prec_converse
#print axioms static_tokens_length
#print axioms static_budget
#print axioms array_some_yield_decompose
#print axioms prefix_array_some
#print axioms certified_array_some
#print axioms array_some_parseType_iff
#print axioms array_some_prec
#print axioms static_tower_prefix
#print axioms static_tower_prec
#print axioms static_tower_exact
#print axioms static_num_checked
#print axioms static_ident_checked
#print axioms ident_expr_four_refused
end Solidity.Frontend.TypeGrammarH28.ParserLength
