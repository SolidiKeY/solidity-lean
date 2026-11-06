import Solidity.Frontend.Checked.Parser

/-! Constructive raw-parser contracts. Locations and existing layout suffixes
remain arbitrary. These lemmas do not change parser fuel or source admission. -/
namespace Solidity.Frontend.TypeGrammarH28.ParserBasic
open Solidity.Source Solidity.Frontend.Checked

theorem located_nil (ls : List Located) (h : ls.map Located.tok = []) : ls = [] := by
  cases ls with
  | nil => rfl
  | cons t ts => cases h

theorem located_cons (ls : List Located) (t : Tok) (ts : List Tok)
    (h : ls.map Located.tok = t :: ts) :
    ∃ head : Located, ∃ tail : List Located,
      ls = head :: tail ∧ head.tok = t ∧ tail.map Located.tok = ts := by
  cases ls with
  | nil => cases h
  | cons head tail =>
    have he : head.tok = t ∧ tail.map Located.tok = ts := List.cons.inj h
    exact ⟨head, tail, rfl, he.1, he.2⟩

theorem located_one (ls : List Located) (t : Tok) (h : ls.map Located.tok = [t]) :
    ∃ start stop : Nat, ls = [⟨t, start, stop⟩] := by
  cases ls with
  | nil => cases h
  | cons head tail =>
    cases tail with
    | cons next rest => cases h
    | nil =>
      cases head with
      | mk tok start stop =>
        have he : tok = t := (List.cons.inj h).1
        cases he
        exact ⟨start, stop, rfl⟩

/-- Terminal suffix checking needs one unit of fuel, at every higher fuel. -/
theorem suffix_eof (n : Nat) (t : Syn .typeName) (ch : List Choice) (eof : Nat) :
    typeSuffix (n + 1) t ⟨[], ch, eof⟩ = .ok (t, ⟨[], ch, eof⟩) := by
  rfl

/-- Raw single-element-token behavior, not a lexer or checked-yield claim. -/
theorem elem_token_eof (e : Elem) (n start stop : Nat) (ch : List Choice) (eof : Nat) :
    typeName (n + 2) ⟨[⟨.elem e, start, stop⟩], ch, eof⟩ =
      .ok (.elem e, ⟨[], ch, eof⟩) := by
  cases e <;> rfl

/-- `address payable` uses its actual two-token grammar spelling. -/
theorem payable_eof (n a b c d : Nat) (ch : List Choice) (eof : Nat) :
    typeName (n + 2) ⟨[⟨.elem .address, a, b⟩, ⟨.kw .payable, c, d⟩], ch, eof⟩ =
      .ok (.elem .addressPayable, ⟨[], ch, eof⟩) := by
  rfl

theorem elem_single_projection (e : Elem) (n : Nat) (ls : List Located)
    (ch : List Choice) (eof : Nat) (h : ls.map Located.tok = [.elem e]) :
    typeName (n + 2) ⟨ls, ch, eof⟩ = .ok (.elem e, ⟨[], ch, eof⟩) := by
  obtain ⟨start, stop, he⟩ := located_one ls (.elem e) h
  cases he
  exact elem_token_eof e n start stop ch eof

theorem payable_projection (n : Nat) (ls : List Located) (ch : List Choice) (eof : Nat)
    (h : ls.map Located.tok = Elem.addressPayable.toks) :
    typeName (n + 2) ⟨ls, ch, eof⟩ = .ok (.elem .addressPayable, ⟨[], ch, eof⟩) := by
  obtain ⟨head, tail, he, hh, ht⟩ := located_cons ls (.elem .address) [.kw .payable] h
  cases he
  obtain ⟨c, d, he⟩ := located_one tail (.kw .payable) ht
  cases he
  cases head with
  | mk tok a b =>
    cases hh
    exact payable_eof n a b c d ch eof

/-- Completeness for every actual elementary spelling and every location list,
with explicit sufficient fuel 2 and all greater fuel. -/
theorem elem_yield_eof (e : Elem) (n : Nat) (ls : List Located)
    (ch : List Choice) (eof : Nat) (h : ls.map Located.tok = e.toks) :
    typeName (n + 2) ⟨ls, ch, eof⟩ = .ok (.elem e, ⟨[], ch, eof⟩) := by
  cases e <;> first
    | exact elem_single_projection _ n ls ch eof h
    | exact payable_projection n ls ch eof h

theorem elem_complete_ge (e : Elem) (fuel : Nat) (hf : 2 ≤ fuel) (ls : List Located)
    (ch : List Choice) (eof : Nat) (h : ls.map Located.tok = e.toks) :
    typeName fuel ⟨ls, ch, eof⟩ = .ok (.elem e, ⟨[], ch, eof⟩) := by
  have he : fuel = fuel - 2 + 2 := (Nat.sub_add_cancel hf).symm
  rw [he]
  exact elem_yield_eof e (fuel - 2) ls ch eof h

/-- The unchanged producer refuses exhausted fuel, rather than admitting a tree. -/
theorem type_zero_refused (s : St) :
    typeName 0 s = .error ⟨s.pos, "nesting too deep"⟩ := by
  rfl

theorem suffix_zero_refused (t : Syn .typeName) (s : St) :
    typeSuffix 0 t s = .error ⟨s.pos, "nesting too deep"⟩ := by
  rfl

theorem elementary_one_refused (start stop eof : Nat) (ch : List Choice) :
    typeName 1 ⟨[⟨.elem .bool, start, stop⟩], ch, eof⟩ =
      .error ⟨eof, "nesting too deep"⟩ := by
  rfl

/-- A terminal suffix preserves its exact entire state, not merely its tokens. -/
theorem suffix_stop (n : Nat) (t : Syn .typeName) (s : St)
    (hs : eat (.punct .lbrack) s = .ok (false, s)) :
    typeSuffix (n + 1) t s = .ok (t, s) := by
  change (eat (.punct .lbrack) s >>= _) = .ok (t, s)
  rw [hs]
  rfl

theorem suffix_dynamic_step (n : Nat) (t : Syn .typeName) (a b c d : Nat)
    (tail : List Located) (ch : List Choice) (eof : Nat) :
    typeSuffix (n + 2) t ⟨⟨.punct .lbrack, a, b⟩ :: ⟨.punct .rbrack, c, d⟩ :: tail, ch, eof⟩ =
      typeSuffix (n + 1) (.array t .none) ⟨tail, ch, eof⟩ := by
  rfl

/-- Grammar-only array spine, retaining the intrinsic source type. -/
def dynamicTree (base : Syn .typeName) (k : Nat) : Syn .typeName :=
  match k with
  | 0 => base
  | k + 1 => dynamicTree (.array base .none) k
termination_by structural k

def dynamicBrackets : Nat → List Tok
  | 0 => []
  | k + 1 => .punct .lbrack :: .punct .rbrack :: dynamicBrackets k

/-- Arbitrarily many dynamic suffixes consume exactly their located prefix.
Sufficient fuel is k+1, plus any extra n; no layout choices are changed. -/
theorem suffix_dynamic_complete (k n : Nat) (base : Syn .typeName)
    (front tail : List Located) (ch : List Choice) (eof : Nat)
    (hp : front.map Located.tok = dynamicBrackets k)
    (hs : eat (.punct .lbrack) ⟨tail, ch, eof⟩ = .ok (false, ⟨tail, ch, eof⟩)) :
    typeSuffix (n + k + 1) base ⟨front ++ tail, ch, eof⟩ =
      .ok (dynamicTree base k, ⟨tail, ch, eof⟩) := by
  induction k generalizing base front with
  | zero =>
    have he : front = [] := located_nil front hp
    cases he
    exact suffix_stop n base _ hs
  | succ k ih =>
    obtain ⟨first, more, he, hf, hm⟩ :=
      located_cons front (.punct .lbrack) (.punct .rbrack :: dynamicBrackets k) hp
    cases he
    obtain ⟨second, rest, he, hsecond, hr⟩ := located_cons more (.punct .rbrack) (dynamicBrackets k) hm
    cases he
    cases first with
    | mk ft a b =>
      cases second with
      | mk st c d =>
        cases hf
        cases hsecond
        change typeSuffix ((n + k) + 2) base
          ⟨⟨.punct .lbrack, a, b⟩ :: ⟨.punct .rbrack, c, d⟩ :: (rest ++ tail), ch, eof⟩ =
          .ok (dynamicTree (.array base .none) k, ⟨tail, ch, eof⟩)
        rw [suffix_dynamic_step]
        exact ih (.array base .none) rest hr

/-- Split real located input at a token-prefix boundary without constraining
source ranges or synthesizing replacement positions. -/
theorem located_append (ls : List Located) (front back : List Tok)
    (h : ls.map Located.tok = front ++ back) :
    ∃ a b : List Located, ls = a ++ b ∧ a.map Located.tok = front ∧ b.map Located.tok = back := by
  induction front generalizing ls with
  | nil => exact ⟨[], ls, rfl, rfl, h⟩
  | cons t ts ih =>
    obtain ⟨head, tail, he, hh, ht⟩ := located_cons ls t (ts ++ back) h
    cases he
    obtain ⟨a, b, he, ha, hb⟩ := ih tail ht
    refine ⟨head :: a, b, ?_, ?_, hb⟩
    · rw [he]
      rfl
    · change head.tok :: a.map Located.tok = t :: ts
      rw [hh, ha]

/-- Raw parser success alone need not reproduce the input yield. This
artificial one-token payable value is not the lexer's two-token spelling. -/
theorem raw_payable_no_yield :
    typeName 2 ⟨[⟨.elem .addressPayable, 0, 1⟩], [], 1⟩ =
      .ok (.elem .addressPayable, ⟨[], [], 1⟩) ∧
    (Syn.elem .addressPayable).toks [] ≠ some [.elem .addressPayable] := by
  exact ⟨rfl, by decide +kernel⟩

#print axioms located_nil
#print axioms located_cons
#print axioms located_one
#print axioms suffix_eof
#print axioms elem_token_eof
#print axioms payable_eof
#print axioms elem_single_projection
#print axioms payable_projection
#print axioms elem_yield_eof
#print axioms elem_complete_ge
#print axioms type_zero_refused
#print axioms suffix_zero_refused
#print axioms elementary_one_refused
#print axioms suffix_stop
#print axioms suffix_dynamic_step
#print axioms suffix_dynamic_complete
#print axioms located_append
#print axioms raw_payable_no_yield

end Solidity.Frontend.TypeGrammarH28.ParserBasic
