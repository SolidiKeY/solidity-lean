import Solidity.Frontend.TypeGrammarH28.Layouts

/-! Compositional type-name/list layout contracts. Array expressions enter only
through an explicit suffix-stable yield premise, not a type uniqueness premise.
No whole-expression or whole-unit uniqueness is asserted. -/
namespace Solidity.Frontend.TypeGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- A successful yield consumes exactly its chosen prefix and preserves every
layout suffix. Items retain the actual producer's list-category convention. -/
def YieldExact {c : Cat} (t : Syn c) (choices : List Choice)
    (items : List (List Tok)) : Prop :=
  ∀ suffix : List Choice, t.yield (choices ++ suffix) = some (items, suffix)

theorem exact_elem (e : Elem) : YieldExact (.elem e) [] [e.toks] := by
  intro suffix
  exact elem_yield e suffix

theorem exact_userType (p : IdPath) : YieldExact (.userType p) [] [p.toks] := by
  intro suffix
  exact userType_yield p suffix

theorem exact_params_nil : YieldExact (Syn.nil (c := .param)) [] [] := by
  intro suffix
  rfl

/-- Concatenate the actual item stream of a parameter and the remaining list. -/
theorem exact_params_cons (p : Syn .param) (ps : Syn (.list .param))
    (lp ls : List Choice) (a b : List (List Tok))
    (hp : YieldExact p lp a) (hs : YieldExact ps ls b) :
    YieldExact (.cons p ps) (lp ++ ls) (a.flatten :: b) := by
  intro suffix
  change (p.yield ((lp ++ ls) ++ suffix) >>= fun x =>
    ps.yield x.2 >>= fun y => some (x.1.flatten :: y.1, y.2)) =
      some (a.flatten :: b, suffix)
  rw [List.append_assoc, hp]
  change (ps.yield (ls ++ suffix) >>= fun y => some (a.flatten :: y.1, y.2)) =
    some (a.flatten :: b, suffix)
  rw [hs]
  rfl

/-- The optional dynamic length is a successful empty atom with no layout. -/
theorem exact_no_length : YieldExact (Syn.none (c := .expr)) [] [] := by
  intro suffix
  rfl

/-- A static length's independent suffix contract is lifted unchanged. -/
theorem exact_some_length (e : Syn .expr) (le : List Choice)
    (a : List (List Tok)) (he : YieldExact e le a) :
    YieldExact (.some e) le [a.flatten] := by
  intro suffix
  change (e.yield (le ++ suffix) >>= fun x => some ([x.1.flatten], x.2)) =
    some ([a.flatten], suffix)
  rw [he]
  rfl

/-- Arbitrarily complex types compose with an independently certified length. -/
theorem exact_array (t : Syn .typeName) (len : Syn (.opt .expr))
    (lt ll : List Choice) (a b : List (List Tok))
    (ht : YieldExact t lt a) (hl : YieldExact len ll b) :
    YieldExact (.array t len) (lt ++ ll)
      [a.flatten ++ pu .lbrack ++ b.flatten ++ pu .rbrack] := by
  intro suffix
  change (t.yield ((lt ++ ll) ++ suffix) >>= fun x =>
    len.yield x.2 >>= fun y =>
      some ([x.1.flatten ++ pu .lbrack ++ y.1.flatten ++ pu .rbrack], y.2)) =
    some ([a.flatten ++ pu .lbrack ++ b.flatten ++ pu .rbrack], suffix)
  rw [List.append_assoc, ht]
  change (len.yield (ll ++ suffix) >>= fun y =>
    some ([a.flatten ++ pu .lbrack ++ y.1.flatten ++ pu .rbrack], y.2)) =
    some ([a.flatten ++ pu .lbrack ++ b.flatten ++ pu .rbrack], suffix)
  rw [hl]
  rfl

theorem exact_param (t : Syn .typeName) (loc : Option DataLoc) (name : Option String)
    (lt : List Choice) (a : List (List Tok)) (ht : YieldExact t lt a) :
    YieldExact (.param t loc name) lt
      [a.flatten ++ optToks DataLoc.toks loc ++ optToks idt name] := by
  intro suffix
  change (t.yield (lt ++ suffix) >>= fun x =>
    some ([x.1.flatten ++ optToks DataLoc.toks loc ++ optToks idt name], x.2)) =
    some ([a.flatten ++ optToks DataLoc.toks loc ++ optToks idt name], suffix)
  rw [ht]
  rfl

/-- Mapping keys/names carry no layout; only the value type does. -/
theorem exact_mapping (key : MapKey) (kn vn : Option String) (v : Syn .typeName)
    (lv : List Choice) (a : List (List Tok)) (hv : YieldExact v lv a) :
    YieldExact (.mapping key kn v vn) lv
      [tk .mapping ++ parens ((match key with | .elem e _ => e.toks | .path p => p.toks) ++
        optToks idt kn ++ pu .doubleArrow ++ a.flatten ++ optToks idt vn)] := by
  intro suffix
  change (v.yield (lv ++ suffix) >>= fun x =>
    some ([tk .mapping ++ parens ((match key with | .elem e _ => e.toks | .path p => p.toks) ++
      optToks idt kn ++ pu .doubleArrow ++ x.1.flatten ++ optToks idt vn)], x.2)) = _
  rw [hv]
  rfl

/-- Function layouts preserve pre-order: the attribute choice precedes both
parameter lists, even though their tokens surround the attributes. -/
theorem exact_fnType (ps rs : Syn (.list .param))
    (vis : Option Visibility) (mu : Option Mutability) (order : List Slot)
    (lp lr : List Choice) (p r : List (List Tok)) (attrs : List Tok)
    (hp : YieldExact ps lp p) (hr : YieldExact rs lr r)
    (ha : arrange order (single .vis (optToks Visibility.toks vis) ++
      single .mutab (optToks Mutability.toks mu)) [] = some attrs) :
    YieldExact (.fnType ps vis mu rs) (.attrs order :: (lp ++ lr))
      [tk .function ++ parens (commaSep p) ++ attrs ++
        (if r.isEmpty then [] else tk .returns ++ parens (commaSep r))] := by
  intro suffix
  change (ps.yield ((lp ++ lr) ++ suffix) >>= fun x =>
    attrsP (single .vis (optToks Visibility.toks vis) ++
      single .mutab (optToks Mutability.toks mu)) [] order x.2 >>= fun a =>
    rs.yield a.2 >>= fun y =>
    some ([tk .function ++ parens (commaSep x.1) ++ a.1 ++
      (if y.1.isEmpty then [] else tk .returns ++ parens (commaSep y.1))], y.2)) = _
  rw [List.append_assoc, hp]
  have hat : attrsP (single .vis (optToks Visibility.toks vis) ++
      single .mutab (optToks Mutability.toks mu)) [] order (lr ++ suffix) =
      some (attrs, lr ++ suffix) := by
    change (arrange order (single .vis (optToks Visibility.toks vis) ++
      single .mutab (optToks Mutability.toks mu)) []).map (fun a => (a, lr ++ suffix)) = _
    rw [ha]
    rfl
  change (attrsP (single .vis (optToks Visibility.toks vis) ++
      single .mutab (optToks Mutability.toks mu)) [] order (lr ++ suffix) >>= fun a =>
    rs.yield a.2 >>= fun y =>
    some ([tk .function ++ parens (commaSep p) ++ a.1 ++
      (if y.1.isEmpty then [] else tk .returns ++ parens (commaSep y.1))], y.2)) = _
  rw [hat]
  change (rs.yield (lr ++ suffix) >>= fun y =>
    some ([tk .function ++ parens (commaSep p) ++ attrs ++
      (if y.1.isEmpty then [] else tk .returns ++ parens (commaSep y.1))], y.2)) = _
  rw [hr]
  rfl

/-- Converse decomposition for an actual successful parameter-list yield.
No delimiter, expression-identity or whole-type-uniqueness premise is hidden. -/
theorem params_cons_decompose (p : Syn .param) (ps : Syn (.list .param))
    (input rest : List Choice) (items : List (List Tok))
    (h : (Syn.cons p ps).yield input = some (items, rest)) :
    ∃ a b : List (List Tok), ∃ middle : List Choice,
      p.yield input = some (a, middle) ∧ ps.yield middle = some (b, rest) ∧
      items = a.flatten :: b := by
  change (p.yield input >>= fun x => ps.yield x.2 >>= fun y =>
    some (x.1.flatten :: y.1, y.2)) = some (items, rest) at h
  cases hp : p.yield input with
  | none => rw [hp] at h; cases h
  | some pr =>
    obtain ⟨a, middle⟩ := pr
    rw [hp] at h
    change (ps.yield middle >>= fun y => some (a.flatten :: y.1, y.2)) =
      some (items, rest) at h
    cases hs : ps.yield middle with
    | none => rw [hs] at h; cases h
    | some sr =>
      obtain ⟨b, last⟩ := sr
      rw [hs] at h
      have he : (a.flatten :: b, last) = (items, rest) := Option.some.inj h
      cases he
      exact ⟨a, b, middle, rfl, hs, rfl⟩

/-- An exact suffix contract discharges the producer's whole-layout check. -/
theorem exact_toks {c : Cat} (t : Syn c) (choices : List Choice)
    (items : List (List Tok)) (h : YieldExact t choices items) :
    t.toks choices = some items.flatten := by
  have hy : t.yield choices = some (items, []) := by
    have he : t.yield (choices ++ []) = some (items, []) := h []
    rw [List.append_nil] at he
    exact he
  unfold Syn.toks
  rw [hy]

/-- Successful equivalence follows from equal complete item observations. -/
theorem exact_layout_equivalent {c : Cat} (t : Syn c) (left right : List Choice)
    (items : List (List Tok)) (hl : YieldExact t left items)
    (hr : YieldExact t right items) : LayoutEquivalent t left right := by
  exact ⟨items.flatten, exact_toks t left items hl, exact_toks t right items hr⟩

/-- Unbounded dynamic-array nesting, retained as actual intrinsic syntax. -/
def dynamicType : Nat → Syn .typeName
  | 0 => .elem .bool
  | n + 1 => .array (dynamicType n) .none

def dynamicItems : Nat → List (List Tok)
  | 0 => [Elem.bool.toks]
  | n + 1 => [(dynamicItems n).flatten ++ pu .lbrack ++ ([] : List (List Tok)).flatten ++ pu .rbrack]

/-- A constructive inhabited suffix-stability control at every nesting depth. -/
theorem exact_dynamic_depth (n : Nat) : YieldExact (dynamicType n) [] (dynamicItems n) := by
  induction n with
  | zero => exact exact_elem .bool
  | succ n ih =>
    exact exact_array (dynamicType n) .none [] [] (dynamicItems n) [] ih exact_no_length

/-- An attribute-bearing node is inhabited even without present attributes. -/
theorem exact_empty_function :
    YieldExact (.fnType .nil none none .nil) [.attrs []]
      [[.kw .function, .punct .lparen, .punct .rparen]] := by
  exact exact_fnType .nil .nil none none [] [] [] [] [] []
    exact_params_nil exact_params_nil rfl

/-- Nested mapping/function/array fields exercise actual pre-order layout. -/
def nestedLayoutType : Syn .typeName :=
  .array (.mapping (.elem .bool (by decide)) (some "k")
    (.fnType (.cons (.param (.array (.elem .bool) .none) (some .storage) (some "x")) .nil)
      (some .external) (some .view) (.cons (.param (.elem .bool) none none) .nil))
    (some "v")) .none

theorem exact_nested_layout :
    YieldExact nestedLayoutType [.attrs [.vis, .mutab]]
      [[.kw .mapping, .punct .lparen, .elem .bool, .ident "k", .punct .doubleArrow,
        .kw .function, .punct .lparen, .elem .bool, .punct .lbrack, .punct .rbrack,
        .kw .storage, .ident "x", .punct .rparen, .kw .external, .kw .view,
        .kw .returns, .punct .lparen, .elem .bool, .punct .rparen, .ident "v",
        .punct .rparen, .punct .lbrack, .punct .rbrack]] := by
  intro suffix
  rfl

#print axioms exact_elem
#print axioms exact_userType
#print axioms exact_params_nil
#print axioms exact_params_cons
#print axioms exact_no_length
#print axioms exact_some_length
#print axioms exact_array
#print axioms exact_param
#print axioms exact_mapping
#print axioms exact_fnType
#print axioms params_cons_decompose
#print axioms exact_toks
#print axioms exact_layout_equivalent
#print axioms exact_dynamic_depth
#print axioms exact_empty_function
#print axioms exact_nested_layout
end Solidity.Frontend.TypeGrammarH28
