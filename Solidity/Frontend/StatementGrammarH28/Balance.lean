import Solidity.Frontend.Checked.Print

/-!
# Balanced brace boundaries and intrinsic block witnesses

BraceBalanced is a token predicate, not an AST. BlockBoundary remains indexed
by an existing Syn block and its actual yield/layout. Balanced-brace splitting
is independent of expression uniqueness. Deriving these witnesses for all
arbitrary expression atoms is a separate, still-open coverage obligation.
-/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

inductive BraceBalanced : List Tok → Prop where
  | empty : BraceBalanced []
  | token (t : Tok) (ho : t ≠ .punct .lbrace) (hc : t ≠ .punct .rbrace) :
      BraceBalanced [t]
  | append {xs ys : List Tok} : BraceBalanced xs → BraceBalanced ys → BraceBalanced (xs ++ ys)
  | wrap {xs : List Tok} : BraceBalanced xs → BraceBalanced (braces xs)

/-- Return the suffix after the matching closing brace. Zero depth means the
next unmatched closing brace ends this scan. Recursion is on the token list. -/
def closeSuffix : Nat → List Tok → Option (List Tok)
  | _, [] => none
  | d, t :: ts =>
    if t = .punct .lbrace then closeSuffix (d + 1) ts
    else if t = .punct .rbrace then
      match d with | 0 => some ts | n + 1 => closeSuffix n ts
    else closeSuffix d ts

/-- Balanced content does not change which subsequent closing brace ends a
scan, at any enclosing depth and for any suffix. -/
theorem balanced_scan_frame {xs : List Tok} (h : BraceBalanced xs)
    (d : Nat) (tail : List Tok) :
    closeSuffix d (xs ++ tail) = closeSuffix d tail := by
  induction h generalizing d tail with
  | empty => rfl
  | token t ho hc =>
    simp only [List.cons_append, List.nil_append, closeSuffix, ho, hc, ↓reduceIte]
  | append hx hy ihx ihy =>
    rw [List.append_assoc, ihx, ihy]
  | @wrap xs hx ih =>
    simp only [braces, pu, List.cons_append, List.nil_append, List.append_assoc]
    change closeSuffix (d + 1) (xs ++ (.punct .rbrace :: tail)) = closeSuffix d tail
    rw [ih]
    rfl

theorem close_after_balanced {xs : List Tok} (h : BraceBalanced xs) (tail : List Tok) :
    closeSuffix 0 (xs ++ (.punct .rbrace :: tail)) = some tail := by
  rw [balanced_scan_frame h]
  rfl

/-- Arbitrary balanced braced prefixes have a unique content/suffix split.
This concludes token equality, not equality of syntax trees deriving it. -/
theorem balanced_braced_split {xs ys rest tail : List Tok}
    (hx : BraceBalanced xs) (hy : BraceBalanced ys)
    (h : braces xs ++ rest = braces ys ++ tail) : xs = ys ∧ rest = tail := by
  have inner : xs ++ (.punct .rbrace :: rest) = ys ++ (.punct .rbrace :: tail) := by
    have heads : (.punct .lbrace : Tok) :: (xs ++ (.punct .rbrace :: rest)) =
        .punct .lbrace :: (ys ++ (.punct .rbrace :: tail)) := by
      simpa only [braces, pu, List.cons_append, List.nil_append, List.append_assoc] using h
    exact (List.cons.inj heads).2
  have scan := close_after_balanced hx rest
  rw [inner, close_after_balanced hy tail] at scan
  have suffix : tail = rest := Option.some.inj scan
  subst tail
  exact ⟨List.append_cancel_right inner, rfl⟩

theorem balanced_flatten {parts : List (List Tok)} :
    (∀ part ∈ parts, BraceBalanced part) → BraceBalanced parts.flatten := by
  induction parts with
  | nil => intro _; exact .empty
  | cons head rest ih =>
    intro h
    exact .append (h head (.head _)) (ih (fun part hp => h part (.tail _ hp)))

/-- Lists of balanced braced token segments have a unique decomposition.
This is a list-of-block-segments result, not a claim about mixed statement lists. -/
theorem balanced_braced_list_unique (xss : List (List Tok)) :
    ∀ yss : List (List Tok),
      (∀ xs ∈ xss, BraceBalanced xs) → (∀ ys ∈ yss, BraceBalanced ys) →
      (xss.map braces).flatten = (yss.map braces).flatten → xss = yss := by
  induction xss with
  | nil =>
    intro yss hx hy h
    cases yss with
    | nil => rfl
    | cons y ys =>
      change ([] : List Tok) = .punct .lbrace :: _ at h
      cases h
  | cons x xs ih =>
    intro yss hx hy h
    cases yss with
    | nil =>
      change (.punct .lbrace : Tok) :: _ = [] at h
      cases h
    | cons y ys =>
      have split := balanced_braced_split (hx x (.head _)) (hy y (.head _)) h
      have tail_eq : xs = ys := ih ys
        (fun part hp => hx part (.tail _ hp))
        (fun part hp => hy part (.tail _ hp)) split.2
      rw [split.1, tail_eq]

/-- The boundary is attached to existing intrinsic syntax and the actual
state-threaded yield. Balance is explicit, never an assumed parse success. -/
structure BlockBoundary {k : SCtx} (b : Syn (.block k))
    (L M : List Choice) (body : List Tok) : Prop where
  yield_eq : b.yield L = some ([braces body], M)
  balanced : BraceBalanced body

theorem block_boundary_split {k j : SCtx} {b : Syn (.block k)} {c : Syn (.block j)}
    {L M N P : List Choice} {xs ys rest tail : List Tok}
    (hb : BlockBoundary b L M xs) (hc : BlockBoundary c N P ys)
    (h : braces xs ++ rest = braces ys ++ tail) : xs = ys ∧ rest = tail :=
  balanced_braced_split hb.balanced hc.balanced h

theorem empty_block_boundary (k : SCtx) (L : List Choice) :
    BlockBoundary (Syn.block (k := k) .nil) L L [] := ⟨rfl, .empty⟩

theorem unmatched_close_not_balanced : ¬ BraceBalanced [.punct .rbrace] := by
  intro h
  have bad : some ([] : List Tok) = none := balanced_scan_frame h 0 []
  cases bad

#print axioms balanced_scan_frame
#print axioms close_after_balanced
#print axioms balanced_braced_split
#print axioms balanced_flatten
#print axioms balanced_braced_list_unique
#print axioms block_boundary_split
#print axioms empty_block_boundary
#print axioms unmatched_close_not_balanced
end Solidity.Frontend.StatementGrammarH28
