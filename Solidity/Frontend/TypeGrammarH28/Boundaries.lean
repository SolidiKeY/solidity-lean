import Solidity.Frontend.Checked.Token

/-! Token delimiter boundaries. The scanner is a local grammar proof device,
not a replacement parser or a type admission/lowering operation. Its recursion
is on the token list and imposes no nesting bound. -/
namespace Solidity.Frontend.TypeGrammarH28.Boundary
open Solidity.Source Solidity.Frontend.Checked

inductive Delim where
  | paren | bracket | brace
  deriving DecidableEq, Repr

def openToken : Delim → Tok
  | .paren => .punct .lparen
  | .bracket => .punct .lbrack
  | .brace => .punct .lbrace

def closeToken : Delim → Tok
  | .paren => .punct .rparen
  | .bracket => .punct .rbrack
  | .brace => .punct .rbrace

inductive Mark where
  | opening (d : Delim)
  | closing (d : Delim)
  | plain
  deriving DecidableEq, Repr

def mark : Tok → Mark
  | .punct .lparen => .opening .paren
  | .punct .rparen => .closing .paren
  | .punct .lbrack => .opening .bracket
  | .punct .rbrack => .closing .bracket
  | .punct .lbrace => .opening .brace
  | .punct .rbrace => .closing .brace
  | _ => .plain

def prefixResult (front : List Tok) (result : Option (List Tok × List Tok)) :
    Option (List Tok × List Tok) := result.map fun p => (front ++ p.1, p.2)

/-- Cut immediately before the first top-level boundary. Nested delimiters
must match in kind. The returned remainder includes the boundary token. -/
def cut (stop : Tok → Bool) (stack : List Delim) (input : List Tok) :
    Option (List Tok × List Tok) :=
  match input with
  | [] => match stack with | [] => some ([], []) | _ :: _ => none
  | t :: ts =>
    match stack with
    | [] =>
      if stop t then some ([], t :: ts)
      else match mark t with
        | .opening d => prefixResult [t] (cut stop [d] ts)
        | .closing _ => none
        | .plain => prefixResult [t] (cut stop [] ts)
    | d :: ds =>
      match mark t with
      | .opening e => prefixResult [t] (cut stop (e :: d :: ds) ts)
      | .closing e => if e = d then prefixResult [t] (cut stop ds ts) else none
      | .plain => prefixResult [t] (cut stop (d :: ds) ts)
termination_by structural input

/-- Balanced groups, including all three delimiter kinds and arbitrary depth. -/
inductive Balanced : List Tok → Prop where
  | nil : Balanced []
  | atom (t : Tok) (rest : List Tok) (plain : mark t = .plain) :
      Balanced rest → Balanced (t :: rest)
  | group (d : Delim) (inside rest : List Tok) :
      Balanced inside → Balanced rest →
      Balanced (openToken d :: (inside ++ closeToken d :: rest))

/-- A top-level region contains no boundary at its own depth; boundaries
inside a balanced group remain permitted. No expression identity is assumed. -/
inductive Region (stop : Tok → Bool) : List Tok → Prop where
  | nil : Region stop []
  | atom (t : Tok) (rest : List Tok) (plain : mark t = .plain) (pass : stop t = false) :
      Region stop rest → Region stop (t :: rest)
  | group (d : Delim) (inside rest : List Tok) (pass : stop (openToken d) = false) :
      Balanced inside → Region stop rest →
      Region stop (openToken d :: (inside ++ closeToken d :: rest))

theorem mark_open (d : Delim) : mark (openToken d) = .opening d := by
  cases d <;> rfl

theorem mark_close (d : Delim) : mark (closeToken d) = .closing d := by
  cases d <;> rfl

theorem prefix_nil (result : Option (List Tok × List Tok)) : prefixResult [] result = result := by
  cases result <;> rfl

theorem prefix_append (a b : List Tok) (result : Option (List Tok × List Tok)) :
    prefixResult (a ++ b) result = prefixResult a (prefixResult b result) := by
  cases result with
  | none => rfl
  | some p =>
    obtain ⟨xs, ys⟩ := p
    exact congrArg (fun zs : List Tok => some (zs, ys)) (List.append_assoc a b xs)

theorem prefix_cons (t : Tok) (a : List Tok) (result : Option (List Tok × List Tok)) :
    prefixResult (t :: a) result = prefixResult [t] (prefixResult a result) := by
  exact prefix_append [t] a result

theorem cut_empty (stop : Tok → Bool) (t : Tok) (ts : List Tok) :
    cut stop [] (t :: ts) =
      if stop t then some ([], t :: ts)
      else match mark t with
        | .opening d => prefixResult [t] (cut stop [d] ts)
        | .closing _ => none
        | .plain => prefixResult [t] (cut stop [] ts) := rfl

theorem cut_nonempty (stop : Tok → Bool) (d : Delim) (ds : List Delim)
    (t : Tok) (ts : List Tok) :
    cut stop (d :: ds) (t :: ts) =
      match mark t with
      | .opening e => prefixResult [t] (cut stop (e :: d :: ds) ts)
      | .closing e => if e = d then prefixResult [t] (cut stop ds ts) else none
      | .plain => prefixResult [t] (cut stop (d :: ds) ts) := rfl

theorem cut_nonempty_plain (stop : Tok → Bool) (d : Delim) (ds : List Delim)
    (t : Tok) (ts : List Tok) (h : mark t = .plain) :
    cut stop (d :: ds) (t :: ts) = prefixResult [t] (cut stop (d :: ds) ts) := by
  rw [cut_nonempty, h]

theorem cut_nonempty_open (stop : Tok → Bool) (d e : Delim) (ds : List Delim)
    (ts : List Tok) :
    cut stop (d :: ds) (openToken e :: ts) =
      prefixResult [openToken e] (cut stop (e :: d :: ds) ts) := by
  rw [cut_nonempty, mark_open]

theorem cut_close (stop : Tok → Bool) (d : Delim) (ds : List Delim) (ts : List Tok) :
    cut stop (d :: ds) (closeToken d :: ts) =
      prefixResult [closeToken d] (cut stop ds ts) := by
  cases d <;> rfl

theorem cut_empty_plain (stop : Tok → Bool) (t : Tok) (ts : List Tok)
    (hm : mark t = .plain) (hs : stop t = false) :
    cut stop [] (t :: ts) = prefixResult [t] (cut stop [] ts) := by
  rw [cut_empty, hs, hm]
  rfl

theorem cut_empty_open (stop : Tok → Bool) (d : Delim) (ts : List Tok)
    (hs : stop (openToken d) = false) :
    cut stop [] (openToken d :: ts) =
      prefixResult [openToken d] (cut stop [d] ts) := by
  rw [cut_empty, hs, mark_open]
  rfl

/-- No top-level boundary inside a balanced group can interrupt a scan at an
already nonempty stack. The statement quantifies over every continuation. -/
theorem balanced_cut (stop : Tok → Bool) (inside : List Tok) (h : Balanced inside)
    (d : Delim) (ds : List Delim) (suffix : List Tok) :
    cut stop (d :: ds) (inside ++ suffix) =
      prefixResult inside (cut stop (d :: ds) suffix) := by
  induction h generalizing d ds suffix with
  | nil => exact (prefix_nil _).symm
  | atom t rest hp hb ih =>
    change cut stop (d :: ds) (t :: (rest ++ suffix)) = _
    rw [cut_nonempty_plain stop d ds t (rest ++ suffix) hp, ih]
    simp only [← prefix_append, List.cons_append, List.nil_append]
  | group e inside rest hi hr ihi ihr =>
    change cut stop (d :: ds) (openToken e :: ((inside ++ closeToken e :: rest) ++ suffix)) = _
    simp only [List.append_assoc, List.cons_append]
    rw [cut_nonempty_open, ihi, cut_close, ihr]
    simp only [← prefix_append, List.cons_append, List.nil_append]

/-- A boundary-free top-level region composes with every token continuation. -/
theorem region_cut (stop : Tok → Bool) (front : List Tok) (h : Region stop front)
    (suffix : List Tok) :
    cut stop [] (front ++ suffix) = prefixResult front (cut stop [] suffix) := by
  induction h generalizing suffix with
  | nil => exact (prefix_nil _).symm
  | atom t rest hp hs hr ih =>
    change cut stop [] (t :: (rest ++ suffix)) = _
    rw [cut_empty_plain stop t (rest ++ suffix) hp hs, ih]
    simp only [← prefix_append, List.cons_append, List.nil_append]
  | group d inside rest hp hb hr ih =>
    change cut stop [] (openToken d :: ((inside ++ closeToken d :: rest) ++ suffix)) = _
    simp only [List.append_assoc, List.cons_append]
    rw [cut_empty_open stop d _ hp, balanced_cut stop inside hb, cut_close, ih]
    simp only [← prefix_append, List.cons_append, List.nil_append]

/-- A continuation is at EOF or begins with a top-level boundary. -/
def StartsBoundary (stop : Tok → Bool) (suffix : List Tok) : Prop :=
  suffix = [] ∨ ∃ t : Tok, ∃ ts : List Tok, suffix = t :: ts ∧ stop t = true

theorem cut_boundary (stop : Tok → Bool) (suffix : List Tok)
    (h : StartsBoundary stop suffix) : cut stop [] suffix = some ([], suffix) := by
  obtain hnil | ⟨t, ts, he, hs⟩ := h
  · cases hnil
    rfl
  · cases he
    rw [cut_empty, hs]
    rfl

/-- Actual constructive boundary decomposition from the independent group
language. The boundary is retained, not consumed or silently discarded. -/
theorem region_cut_boundary (stop : Tok → Bool) (front suffix : List Tok)
    (hf : Region stop front) (hs : StartsBoundary stop suffix) :
    cut stop [] (front ++ suffix) = some (front, suffix) := by
  have hc : cut stop [] (front ++ suffix) = prefixResult front (cut stop [] suffix) :=
    region_cut stop front hf suffix
  rw [cut_boundary stop suffix hs] at hc
  simp only [prefixResult, Option.map_some, List.append_nil] at hc
  exact hc

/-- Arbitrary-depth boundary uniqueness. Its premises are the independent
balanced-region derivations, not type-name or expression uniqueness. -/
theorem boundary_unique (stop : Tok → Bool) (left right lr rr : List Tok)
    (hl : Region stop left) (hr : Region stop right)
    (hlr : StartsBoundary stop lr) (hrr : StartsBoundary stop rr)
    (same : left ++ lr = right ++ rr) : left = right ∧ lr = rr := by
  have hc : cut stop [] (left ++ lr) = some (left, lr) :=
    region_cut_boundary stop left lr hl hlr
  have hd : cut stop [] (right ++ rr) = some (right, rr) :=
    region_cut_boundary stop right rr hr hrr
  rw [same] at hc
  have he : (left, lr) = (right, rr) := Option.some.inj (hc.symm.trans hd)
  exact Prod.mk.inj he

theorem region_balanced (stop : Tok → Bool) (ts : List Tok) (h : Region stop ts) :
    Balanced ts := by
  induction h with
  | nil => exact .nil
  | atom t rest hp hs hr ih => exact .atom t rest hp ih
  | group d inside rest hp hb hr ih => exact .group d inside rest hb ih

/-- An arbitrary list of delimiter kinds, not a finite nesting test budget. -/
def nest : List Delim → List Tok → List Tok
  | [], body => body
  | d :: ds, body => openToken d :: (nest ds body ++ [closeToken d])

theorem nest_balanced (ds : List Delim) (body : List Tok) (h : Balanced body) :
    Balanced (nest ds body) := by
  induction ds with
  | nil => exact h
  | cons d ds ih => exact .group d (nest ds body) [] ih .nil

theorem nest_region (stop : Tok → Bool) (ds : List Delim) (body : List Tok)
    (h : Region stop body) (hopen : ∀ d : Delim, stop (openToken d) = false) :
    Region stop (nest ds body) := by
  cases ds with
  | nil => exact h
  | cons d ds =>
    exact .group d (nest ds body) [] (hopen d)
      (nest_balanced ds body (region_balanced stop body h)) .nil

/-- Parameter-list separators at the current depth only. -/
def paramStop : Tok → Bool
  | .punct .comma | .punct .rparen => true
  | _ => false

/-- Inhabited constructive control with all delimiter kinds and every depth. -/
theorem arbitrary_nested_boundary (ds : List Delim) (rest : List Tok) :
    cut paramStop [] (nest ds [.elem .bool] ++ .punct .comma :: rest) =
      some (nest ds [.elem .bool], .punct .comma :: rest) := by
  apply region_cut_boundary
  · apply nest_region
    · exact .atom (.elem .bool) [] rfl rfl .nil
    · intro d
      cases d <;> rfl
  · exact Or.inr ⟨.punct .comma, rest, rfl, rfl⟩

/-- A mismatched nested close fails even when it is a top-level stop token. -/
theorem mismatched_close_refused :
    cut paramStop [] [.punct .lbrack, .punct .rparen] = none := rfl

theorem unterminated_group_refused :
    cut paramStop [] [.punct .lbrace, .elem .bool] = none := rfl

/-- Inner commas do not split the outer parameter region. -/
theorem inner_comma_preserved :
    cut paramStop [] [.punct .lparen, .elem .bool, .punct .comma, .elem .bool,
      .punct .rparen, .punct .comma, .ident "tail"] =
    some ([.punct .lparen, .elem .bool, .punct .comma, .elem .bool, .punct .rparen],
      [.punct .comma, .ident "tail"]) := rfl

theorem balanced_append (a b : List Tok) (ha : Balanced a) (hb : Balanced b) :
    Balanced (a ++ b) := by
  induction ha with
  | nil => exact hb
  | atom t rest hp hr ih => exact .atom t (rest ++ b) hp ih
  | group d inside rest hi hr ihi ihr =>
    have hg : Balanced (openToken d :: (inside ++ closeToken d :: (rest ++ b))) :=
      .group d inside (rest ++ b) hi ihr
    simpa only [List.cons_append, List.append_assoc] using hg

theorem region_append (stop : Tok → Bool) (a b : List Tok)
    (ha : Region stop a) (hb : Region stop b) : Region stop (a ++ b) := by
  induction ha with
  | nil => exact hb
  | atom t rest hp hs hr ih => exact .atom t (rest ++ b) hp hs ih
  | group d inside rest hp hi hr ih =>
    have hg : Region stop (openToken d :: (inside ++ closeToken d :: (rest ++ b))) :=
      .group d inside (rest ++ b) hp hi ih
    simpa only [List.cons_append, List.append_assoc] using hg

/-- Decompose a successful prefixed scanner result without assuming the
recursive result was successful. -/
theorem prefix_head_inv (t : Tok) (result : Option (List Tok × List Tok))
    (front rest : List Tok) (h : prefixResult [t] result = some (front, rest)) :
    ∃ tail : List Tok, result = some (tail, rest) ∧ front = t :: tail := by
  cases result with
  | none => cases h
  | some p =>
    obtain ⟨tail, last⟩ := p
    have he : (t :: tail, last) = (front, rest) := Option.some.inj h
    cases he
    exact ⟨tail, rfl, rfl⟩

/-- Every successful scan consumes a prefix and retains exactly its suffix,
for every initial stack. This is independent of the balanced-region premise. -/
theorem cut_suffix (stop : Tok → Bool) (stack : List Delim)
    (input front rest : List Tok) (h : cut stop stack input = some (front, rest)) :
    input = front ++ rest := by
  induction input generalizing stack front rest with
  | nil =>
    cases stack with
    | nil =>
      have he : ([], []) = (front, rest) := Option.some.inj h
      cases he
      rfl
    | cons d ds => cases h
  | cons t ts ih =>
    have consume (next : List Delim)
        (hc : prefixResult [t] (cut stop next ts) = some (front, rest)) :
        t :: ts = front ++ rest := by
      obtain ⟨tail, ht, hf⟩ := prefix_head_inv t (cut stop next ts) front rest hc
      rw [hf]
      exact congrArg (List.cons t) (ih next tail rest ht)
    cases stack with
    | nil =>
      rw [cut_empty] at h
      split at h
      · have he : ([], t :: ts) = (front, rest) := Option.some.inj h
        cases he
        rfl
      · cases hm : mark t with
        | opening d => rw [hm] at h; exact consume [d] h
        | closing d => rw [hm] at h; cases h
        | plain => rw [hm] at h; exact consume [] h
    | cons d ds =>
      rw [cut_nonempty] at h
      cases hm : mark t with
      | opening e => rw [hm] at h; exact consume (e :: d :: ds) h
      | closing e =>
        rw [hm] at h
        change (if e = d then prefixResult [t] (cut stop ds ts) else none) = some (front, rest) at h
        split at h
        · exact consume ds h
        · cases h
      | plain => rw [hm] at h; exact consume (d :: ds) h

#print axioms mark_open
#print axioms mark_close
#print axioms prefix_nil
#print axioms prefix_append
#print axioms prefix_cons
#print axioms cut_empty
#print axioms cut_nonempty
#print axioms cut_nonempty_plain
#print axioms cut_nonempty_open
#print axioms cut_close
#print axioms cut_empty_plain
#print axioms cut_empty_open
#print axioms balanced_cut
#print axioms region_cut
#print axioms cut_boundary
#print axioms region_cut_boundary
#print axioms boundary_unique
#print axioms region_balanced
#print axioms nest_balanced
#print axioms nest_region
#print axioms arbitrary_nested_boundary
#print axioms mismatched_close_refused
#print axioms unterminated_group_refused
#print axioms inner_comma_preserved
#print axioms balanced_append
#print axioms region_append
#print axioms prefix_head_inv
#print axioms cut_suffix

end Solidity.Frontend.TypeGrammarH28.Boundary
