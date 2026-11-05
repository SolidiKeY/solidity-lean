import Solidity.Frontend.TypeGrammarH28.ParserParams

/-! Exact successful function attribute layouts and the actual frozen parser.
No operational admission or producer interface is changed. -/
namespace Solidity.Frontend.TypeGrammarH28.ParserFnAttrs
open Solidity.Source Solidity.Frontend.Checked ParserBasic ParserCheck ParserPath ParserReady

inductive AttrLayout : Option Visibility → Option Mutability → List Slot → List Tok → Prop where
  | empty : AttrLayout none none [] []
  | vis (v : Visibility) : AttrLayout (some v) none [.vis] v.toks
  | mutab (m : Mutability) : AttrLayout none (some m) [.mutab] m.toks
  | visMut (v : Visibility) (m : Mutability) :
      AttrLayout (some v) (some m) [.vis, .mutab] (v.toks ++ m.toks)
  | mutVis (v : Visibility) (m : Mutability) :
      AttrLayout (some v) (some m) [.mutab, .vis] (m.toks ++ v.toks)

def fnSingles (v : Option Visibility) (m : Option Mutability) : List (Slot × List Tok) :=
  single .vis (optToks Visibility.toks v) ++ single .mutab (optToks Mutability.toks m)

theorem singles_empty : fnSingles none none = [] := rfl

theorem singles_vis (v : Visibility) : fnSingles (some v) none = [(.vis, v.toks)] := by
  cases v <;> rfl

theorem singles_mut (m : Mutability) : fnSingles none (some m) = [(.mutab, m.toks)] := by
  cases m <;> rfl

theorem singles_both (v : Visibility) (m : Mutability) :
    fnSingles (some v) (some m) = [(.vis, v.toks), (.mutab, m.toks)] := by
  cases v <;> cases m <;> rfl

theorem arrange_empty_converse (order : List Slot) (tokens : List Tok)
    (h : arrange order [] [] = some tokens) : order = [] ∧ tokens = [] := by
  cases order with
  | nil => exact ⟨rfl, (Option.some.inj h).symm⟩
  | cons slot rest => cases slot <;> cases h

theorem map_append_converse (value : Option (List Tok)) (leading tokens : List Tok)
    (h : value.map (leading ++ ·) = some tokens) :
    ∃ suffix : List Tok, value = some suffix ∧ tokens = leading ++ suffix := by
  cases value with
  | none => cases h
  | some suffix => exact ⟨suffix, rfl, (Option.some.inj h).symm⟩

theorem arrange_vis_converse (order : List Slot) (head tokens : List Tok)
    (h : arrange order [(.vis, head)] [] = some tokens) : order = [.vis] ∧ tokens = head := by
  cases order with
  | nil => cases h
  | cons slot rest =>
    cases slot <;> try cases h
    case vis =>
      change (arrange rest [] []).map (head ++ ·) = some tokens at h
      obtain ⟨suffix, hs, ht⟩ := map_append_converse _ head tokens h
      obtain ⟨hr, he⟩ := arrange_empty_converse rest suffix hs
      cases hr
      cases he
      exact ⟨rfl, ht.trans (List.append_nil head)⟩

theorem arrange_mut_converse (order : List Slot) (head tokens : List Tok)
    (h : arrange order [(.mutab, head)] [] = some tokens) : order = [.mutab] ∧ tokens = head := by
  cases order with
  | nil => cases h
  | cons slot rest =>
    cases slot <;> try cases h
    case mutab =>
      change (arrange rest [] []).map (head ++ ·) = some tokens at h
      obtain ⟨suffix, hs, ht⟩ := map_append_converse _ head tokens h
      obtain ⟨hr, he⟩ := arrange_empty_converse rest suffix hs
      cases hr
      cases he
      exact ⟨rfl, ht.trans (List.append_nil head)⟩

theorem arrange_both_converse (order : List Slot) (vis mutab tokens : List Tok)
    (h : arrange order [(.vis, vis), (.mutab, mutab)] [] = some tokens) :
    (order = [.vis, .mutab] ∧ tokens = vis ++ mutab) ∨
    (order = [.mutab, .vis] ∧ tokens = mutab ++ vis) := by
  cases order with
  | nil => cases h
  | cons slot rest =>
    cases slot <;> try cases h
    case vis =>
      change (arrange rest [(.mutab, mutab)] []).map (vis ++ ·) = some tokens at h
      obtain ⟨suffix, hs, ht⟩ := map_append_converse _ vis tokens h
      obtain ⟨hr, he⟩ := arrange_mut_converse rest mutab suffix hs
      cases hr
      cases he
      exact .inl ⟨rfl, ht⟩
    case mutab =>
      change (arrange rest [(.vis, vis)] []).map (mutab ++ ·) = some tokens at h
      obtain ⟨suffix, hs, ht⟩ := map_append_converse _ mutab tokens h
      obtain ⟨hr, he⟩ := arrange_vis_converse rest vis suffix hs
      cases hr
      cases he
      exact .inr ⟨rfl, ht⟩

/-- Every successful original arrangement is classified, with no layout filter. -/
theorem arrange_layout (v : Option Visibility) (m : Option Mutability)
    (order : List Slot) (tokens : List Tok)
    (h : arrange order (fnSingles v m) [] = some tokens) : AttrLayout v m order tokens := by
  cases v with
  | none =>
    cases m with
    | none =>
      rw [singles_empty] at h
      obtain ⟨ho, ht⟩ := arrange_empty_converse order tokens h
      cases ho
      cases ht
      exact .empty
    | some m =>
      rw [singles_mut] at h
      obtain ⟨ho, ht⟩ := arrange_mut_converse order m.toks tokens h
      cases ho
      cases ht
      exact .mutab m
  | some v =>
    cases m with
    | none =>
      rw [singles_vis] at h
      obtain ⟨ho, ht⟩ := arrange_vis_converse order v.toks tokens h
      cases ho
      cases ht
      exact .vis v
    | some m =>
      rw [singles_both] at h
      rcases arrange_both_converse order v.toks m.toks tokens h with ⟨ho, ht⟩ | ⟨ho, ht⟩
      · cases ho; cases ht; exact .visMut v m
      · cases ho; cases ht; exact .mutVis v m

theorem layout_arrange (v : Option Visibility) (m : Option Mutability)
    (order : List Slot) (tokens : List Tok) (h : AttrLayout v m order tokens) :
    arrange order (fnSingles v m) [] = some tokens := by
  cases h with
  | empty => rfl
  | vis v => cases v <;> rfl
  | mutab m => cases m <;> rfl
  | visMut v m => cases v <;> cases m <;> rfl
  | mutVis v m => cases v <;> cases m <;> rfl

theorem arrange_layout_iff (v : Option Visibility) (m : Option Mutability)
    (order : List Slot) (tokens : List Tok) :
    arrange order (fnSingles v m) [] = some tokens ↔ AttrLayout v m order tokens := by
  exact ⟨arrange_layout v m order tokens, layout_arrange v m order tokens⟩

/-- The two actual contexts after a function attribute run. -/
inductive AttrBoundary : List Located → Prop where
  | finish (rest : List Located) (h : Continuation rest) : AttrBoundary rest
  | returns (a b : Nat) (rest : List Located) : AttrBoundary (⟨.kw .returns, a, b⟩ :: rest)

theorem attrs_stop (fuel : Nat) (rest : List Located) (hb : AttrBoundary rest)
    (v : Option Visibility) (m : Option Mutability) (order : List Slot)
    (ch : List Choice) (eof : Nat) :
    fnTypeAttrs fuel v m order ⟨rest, ch, eof⟩ = .ok ((v, m, order.reverse), ⟨rest, ch, eof⟩) := by
  cases hb with
  | finish rest hb => exact continuation_no_attrs fuel rest hb v m order ch eof
  | returns a b rest => cases fuel <;> rfl

theorem vis_step (v : Visibility) (m : Option Mutability) (order : List Slot) (fuel : Nat)
    (front rest : List Located) (hp : front.map Located.tok = v.toks)
    (ch : List Choice) (eof : Nat) :
    fnTypeAttrs (fuel + 1) none m order ⟨front ++ rest, ch, eof⟩ =
      fnTypeAttrs fuel (some v) m (.vis :: order) ⟨rest, ch, eof⟩ := by
  cases v <;> obtain ⟨a, b, he⟩ := located_one front _ hp <;> cases he <;> rfl

theorem mut_step (v : Option Visibility) (m : Mutability) (order : List Slot) (fuel : Nat)
    (front rest : List Located) (hp : front.map Located.tok = m.toks)
    (ch : List Choice) (eof : Nat) :
    fnTypeAttrs (fuel + 1) v none order ⟨front ++ rest, ch, eof⟩ =
      fnTypeAttrs fuel v (some m) (.mutab :: order) ⟨rest, ch, eof⟩ := by
  cases m <;> obtain ⟨a, b, he⟩ := located_one front _ hp <;> cases he <;> rfl

/-- Uniform fuel three handles all five layouts, every visibility/mutability,
and arbitrary actual positions, including a following returns keyword. -/
theorem attrs_complete (v : Option Visibility) (m : Option Mutability)
    (order : List Slot) (tokens : List Tok) (h : AttrLayout v m order tokens)
    (front rest : List Located) (hp : front.map Located.tok = tokens)
    (hb : AttrBoundary rest) (ch : List Choice) (eof : Nat) :
    fnTypeAttrs 3 none none [] ⟨front ++ rest, ch, eof⟩ =
      .ok ((v, m, order), ⟨rest, ch, eof⟩) := by
  cases h with
  | empty =>
    have he := located_nil front hp
    cases he
    exact attrs_stop 3 rest hb none none [] ch eof
  | vis v =>
    rw [vis_step v none [] 2 front rest hp ch eof]
    exact attrs_stop 2 rest hb (some v) none [.vis] ch eof
  | mutab m =>
    rw [mut_step none m [] 2 front rest hp ch eof]
    exact attrs_stop 2 rest hb none (some m) [.mutab] ch eof
  | visMut v m =>
    obtain ⟨visFront, mutFront, he, hv, hm⟩ := located_append front v.toks m.toks hp
    cases he
    rw [List.append_assoc, vis_step v none [] 2 visFront (mutFront ++ rest) hv ch eof]
    rw [mut_step (some v) m [.vis] 1 mutFront rest hm ch eof]
    exact attrs_stop 1 rest hb (some v) (some m) [.mutab, .vis] ch eof
  | mutVis v m =>
    obtain ⟨mutFront, visFront, he, hm, hv⟩ := located_append front m.toks v.toks hp
    cases he
    rw [List.append_assoc, mut_step none m [] 2 mutFront (visFront ++ rest) hm ch eof]
    rw [vis_step v (some m) [.mutab] 1 visFront rest hv ch eof]
    exact attrs_stop 1 rest hb (some v) (some m) [.vis, .mutab] ch eof

theorem arranged_attrs_complete (v : Option Visibility) (m : Option Mutability)
    (order : List Slot) (tokens : List Tok)
    (h : arrange order (fnSingles v m) [] = some tokens)
    (front rest : List Located) (hp : front.map Located.tok = tokens)
    (hb : AttrBoundary rest) (ch : List Choice) (eof : Nat) :
    fnTypeAttrs 3 none none [] ⟨front ++ rest, ch, eof⟩ =
      .ok ((v, m, order), ⟨rest, ch, eof⟩) := by
  exact attrs_complete v m order tokens (arrange_layout v m order tokens h) front rest hp hb ch eof

/-- The producer stops before a second visibility; this is not a whole-type
admission of repeated visibility tokens. -/
theorem repeated_vis_stops (v w : Visibility) (first second rest : List Located)
    (hv : first.map Located.tok = v.toks) (hw : second.map Located.tok = w.toks)
    (ch : List Choice) (eof : Nat) :
    fnTypeAttrs 3 none none [] ⟨first ++ (second ++ rest), ch, eof⟩ =
      .ok ((some v, none, [.vis]), ⟨second ++ rest, ch, eof⟩) := by
  rw [vis_step v none [] 2 first (second ++ rest) hv ch eof]
  cases w <;> obtain ⟨a, b, he⟩ := located_one second _ hw <;> cases he <;> rfl

/-- Every mutability pair triggers the actual repeated-attribute error, at
that second token's real start position. -/
theorem repeated_mut_refused (m n : Mutability) (first : List Located)
    (hm : first.map Located.tok = m.toks) (a b : Nat) (rest : List Located)
    (ch : List Choice) (eof : Nat) :
    fnTypeAttrs 3 none none []
      ⟨first ++ (witnessLocations n.toks).map (fun t => {t with start := a, stop := b}) ++ rest, ch, eof⟩ =
      .error ⟨a, "repeated function type attribute"⟩ := by
  rw [List.append_assoc, mut_step none m [] 2 first _ hm ch eof]
  cases n <;> rfl

theorem layout_length (v : Option Visibility) (m : Option Mutability)
    (order : List Slot) (tokens : List Tok) (h : AttrLayout v m order tokens) : order.length ≤ 2 := by
  cases h <;> decide

theorem overlong_order_refused (v : Option Visibility) (m : Option Mutability)
    (order : List Slot) (hl : 3 ≤ order.length) : arrange order (fnSingles v m) [] = none := by
  cases h : arrange order (fnSingles v m) [] with
  | none => rfl
  | some tokens =>
    have hb := layout_length v m order tokens (arrange_layout v m order tokens h)
    exact False.elim (Nat.not_succ_le_self 2 (Nat.le_trans hl hb))

/-- Equal actual attribute yields force the same fields and source order, by
two independently proved parses of the same located tokens. -/
theorem arranged_fields_unique (v w : Option Visibility) (m n : Option Mutability)
    (order other : List Slot) (tokens : List Tok)
    (hv : arrange order (fnSingles v m) [] = some tokens)
    (hw : arrange other (fnSingles w n) [] = some tokens) :
    v = w ∧ m = n ∧ order = other := by
  have ha := arranged_attrs_complete v m order tokens hv (witnessLocations tokens) []
    (witness_locations_tokens tokens) (.finish [] (.finish .eof)) [] 0
  have hb := arranged_attrs_complete w n other tokens hw (witnessLocations tokens) []
    (witness_locations_tokens tokens) (.finish [] (.finish .eof)) [] 0
  have he : (v, m, order) = (w, n, other) := (Prod.mk.inj (Except.ok.inj (ha.symm.trans hb))).1
  exact ⟨congrArg Prod.fst he, congrArg (fun x => x.2.1) he, congrArg (fun x => x.2.2) he⟩

theorem attrs_inhabited (v : Option Visibility) (m : Option Mutability) :
    ∃ order : List Slot, ∃ tokens : List Tok,
      arrange order (fnSingles v m) [] = some tokens ∧
      fnTypeAttrs 3 none none [] ⟨witnessLocations tokens, [], 0⟩ =
        .ok ((v, m, order), ⟨[], [], 0⟩) := by
  have inhabited : ∃ order : List Slot, ∃ tokens : List Tok, AttrLayout v m order tokens := by
    cases v with
    | none =>
      cases m with
      | none => exact ⟨[], [], .empty⟩
      | some m => exact ⟨[.mutab], m.toks, .mutab m⟩
    | some v =>
      cases m with
      | none => exact ⟨[.vis], v.toks, .vis v⟩
      | some m => exact ⟨[.vis, .mutab], v.toks ++ m.toks, .visMut v m⟩
  obtain ⟨order, tokens, hl⟩ := inhabited
  have hp := attrs_complete v m order tokens hl (witnessLocations tokens) []
    (witness_locations_tokens tokens) (.finish [] (.finish .eof)) [] 0
  exact ⟨order, tokens, layout_arrange v m order tokens hl, by simpa only [List.append_nil] using hp⟩

theorem mut_first_inhabited (v : Visibility) (m : Mutability) :
    arrange [.mutab, .vis] (fnSingles (some v) (some m)) [] = some (m.toks ++ v.toks) ∧
    fnTypeAttrs 3 none none [] ⟨witnessLocations (m.toks ++ v.toks), [], 0⟩ =
      .ok ((some v, some m, [.mutab, .vis]), ⟨[], [], 0⟩) := by
  have hl := AttrLayout.mutVis v m
  have hp := attrs_complete _ _ _ _ hl _ [] (witness_locations_tokens _) (.finish [] (.finish .eof)) [] 0
  exact ⟨layout_arrange _ _ _ _ hl, by simpa only [List.append_nil] using hp⟩

#print axioms singles_empty
#print axioms singles_vis
#print axioms singles_mut
#print axioms singles_both
#print axioms arrange_empty_converse
#print axioms map_append_converse
#print axioms arrange_vis_converse
#print axioms arrange_mut_converse
#print axioms arrange_both_converse
#print axioms arrange_layout
#print axioms layout_arrange
#print axioms arrange_layout_iff
#print axioms attrs_stop
#print axioms vis_step
#print axioms mut_step
#print axioms attrs_complete
#print axioms arranged_attrs_complete
#print axioms repeated_vis_stops
#print axioms repeated_mut_refused
#print axioms layout_length
#print axioms overlong_order_refused
#print axioms arranged_fields_unique
#print axioms attrs_inhabited
#print axioms mut_first_inhabited
end Solidity.Frontend.TypeGrammarH28.ParserFnAttrs
