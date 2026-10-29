import Solidity.Frontend.Checked.Lexer
import Solidity.Frontend.Checked.Parser
import Solidity.Frontend.Checked.Prec

/-!
# Whole-source parsing, checked (G11)

`parse : Bytes → Except Error (Syn .unit)` composes the checked lexer (G08)
and the parser (G09–G11) and accepts the parser's tree only if

* its yield under the parser's layout is exactly the token sequence of the
  lexed source (`Syn.toks`, the grammar derivation), and
* it satisfies the precedence predicate (`Syn.prec`).

`parse_sound` states what an accepted source carries.  The parser itself is
not trusted: a wrong tree is refused by the check, never returned.
-/

namespace Solidity.Frontend.Checked

open Solidity.Source

/-- The tokens of a piece list. -/
def tokensOf (ps : List Piece) : List Tok :=
  ps.filterMap fun p => match p.kind with
    | .tok t => some t
    | .trivia _ => none

/-- The certificate of an accepted parse: the yield under the layout is the
token sequence, and the tree is the one precedence selects. -/
def Parsed (ts : List Tok) (t : Syn .unit) (L : List Choice) : Prop :=
  t.toks L = some ts ∧ t.prec = true

instance (ts : List Tok) (t : Syn .unit) (L : List Choice) : Decidable (Parsed ts t L) := by
  unfold Parsed; exact inferInstance

/-- Parse a token list (with the source length for end-of-input errors),
checked. -/
def parseLocated (eof : Nat) (ls : List Located) : Except Error (Syn .unit × List Choice) :=
  match parseTokens eof ls with
  | .error e => .error e
  | .ok (u, L) =>
    if u.toks L ≠ some (ls.map Located.tok) then .error ⟨0, "parser check failed: yield mismatch"⟩
    else if u.prec = false then
      .error ⟨0, "ambiguous expression or statement (precedence, dangling else): parenthesize"⟩
    else .ok (u, L)

/-- **The checked parser** of a source unit, with its layout. -/
def parseWithLayout (src : Bytes) : Except Error (Syn .unit × List Choice) :=
  match lex src with
  | .error e => .error e
  | .ok ps => parseLocated src.length ((locate .sol 0 ps).map Prod.fst)

def parse (src : Bytes) : Except Error (Syn .unit) := (parseWithLayout src).map Prod.fst

theorem locate_toks : ∀ (ps : List Piece) (m : Mode) (o : Nat),
    ((locate m o ps).map fun x => x.1.tok) = tokensOf ps
  | [], _, _ => rfl
  | p :: ps, m, o => by
    have ih := locate_toks ps (m.next p.kind) (o + p.raw.length)
    cases hk : p.kind with
    | tok t =>
      simp only [locate, hk, List.map_cons, tokensOf, List.filterMap_cons] at ih ⊢
      rw [ih]
    | trivia x =>
      simp only [locate, hk, tokensOf, List.filterMap_cons] at ih ⊢
      exact ih

theorem parseLocated_sound {eof : Nat} {ls : List Located} {u : Syn .unit} {L : List Choice}
    (h : parseLocated eof ls = .ok (u, L)) : Parsed (ls.map Located.tok) u L := by
  unfold parseLocated at h
  split at h
  · cases h
  · next u' L' _ =>
    split at h
    · cases h
    · split at h
      · cases h
      · next h1 h2 =>
        cases h
        exact ⟨Decidable.of_not_not h1, by simpa using h2⟩

/-- **Soundness of whole-source parsing**: an accepted source is lexed into
pieces carrying the lexer's certificate (they re-print the source, each is
classified, maximal munch), and the tree derives exactly its tokens under
the returned layout and is the precedence-selected one. -/
theorem parse_sound {src : Bytes} {u : Syn .unit} {L : List Choice}
    (h : parseWithLayout src = .ok (u, L)) :
    ∃ ps, lex src = .ok ps ∧ Lexed src ps ∧ Parsed (tokensOf ps) u L := by
  unfold parseWithLayout at h
  split at h
  · cases h
  · next ps hl =>
    refine ⟨ps, hl, lex_sound hl, ?_⟩
    have hp := parseLocated_sound h
    rw [List.map_map] at hp
    have : (Located.tok ∘ Prod.fst : Located × Mode → Tok) = fun x => x.1.tok := rfl
    rw [this, locate_toks] at hp
    exact hp

/-- The grammar-derivation form: an accepted source's tree derives its
tokens. -/
theorem parse_derives {src : Bytes} {u : Syn .unit} (h : parse src = .ok u) :
    ∃ ps, lex src = .ok ps ∧ u.Derives (tokensOf ps) ∧ u.prec = true := by
  unfold parse at h
  cases hw : parseWithLayout src with
  | error e => rw [hw] at h; cases h
  | ok r =>
    rw [hw] at h
    cases h
    obtain ⟨ps, hl, _, hp⟩ := parse_sound hw
    exact ⟨ps, hl, ⟨r.2, hp.1⟩, hp.2⟩

/-! ## One category

The same check for a single category (a type name, an expression), used by
the G09 and G10 witnesses. -/

/-- Parse all of a token list as one category, checked against the yield
and precedence. -/
def parseCatLocated {c : Cat} (p : Nat → P (Syn c)) (eof : Nat) (ls : List Located) :
    Except Error (Syn c × List Choice) :=
  match p (16 * (ls.length + 1)) ⟨ls, [], eof⟩ with
  | .error e => .error e
  | .ok (t, s) =>
    if !s.ts.isEmpty then .error ⟨s.pos, "unexpected token"⟩
    else if t.toks s.ch.reverse ≠ some (ls.map Located.tok) then
      .error ⟨0, "parser check failed: yield mismatch"⟩
    else if t.prec = false then
      .error ⟨0, "ambiguous expression or statement (precedence, dangling else): parenthesize"⟩
    else .ok (t, s.ch.reverse)

def parseCat {c : Cat} (p : Nat → P (Syn c)) (src : Bytes) : Except Error (Syn c × List Choice) :=
  match lex src with
  | .error e => .error e
  | .ok ps => parseCatLocated p src.length ((locate .sol 0 ps).map Prod.fst)

/-- A checked type name. -/
def parseType (src : Bytes) : Except Error (Syn .typeName) := (parseCat typeName src).map Prod.fst
/-- A checked expression. -/
def parseExpr (src : Bytes) : Except Error (Syn .expr) := (parseCat expr src).map Prod.fst

theorem parseCat_sound {c : Cat} {p : Nat → P (Syn c)} {src : Bytes} {t : Syn c}
    {L : List Choice} (h : parseCat p src = .ok (t, L)) :
    ∃ ps, lex src = .ok ps ∧ t.toks L = some (tokensOf ps) ∧ t.prec = true := by
  unfold parseCat at h
  split at h
  · cases h
  · next ps hl =>
    refine ⟨ps, hl, ?_⟩
    unfold parseCatLocated at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · next h1 h2 =>
            cases h
            have h1' := Decidable.of_not_not h1
            rw [List.map_map] at h1'
            have : (Located.tok ∘ Prod.fst : Located × Mode → Tok) = fun x => x.1.tok := rfl
            rw [this, locate_toks] at h1'
            exact ⟨h1', by simpa using h2⟩

/-- **A checked category derives its tokens** (types: G09; expressions: G10). -/
theorem parseCat_derives {c : Cat} {p : Nat → P (Syn c)} {src : Bytes} {t : Syn c}
    (h : (parseCat p src).map Prod.fst = .ok t) :
    ∃ ps, lex src = .ok ps ∧ t.Derives (tokensOf ps) ∧ t.prec = true := by
  cases hw : parseCat p src with
  | error e => rw [hw] at h; cases h
  | ok r =>
    rw [hw] at h
    cases h
    obtain ⟨ps, hl, hd, hp⟩ := parseCat_sound hw
    exact ⟨ps, hl, ⟨r.2, hd⟩, hp⟩

theorem parseType_derives {src : Bytes} {t : Syn .typeName} (h : parseType src = .ok t) :
    ∃ ps, lex src = .ok ps ∧ t.Derives (tokensOf ps) ∧ t.prec = true := parseCat_derives h

theorem parseExpr_derives {src : Bytes} {e : Syn .expr} (h : parseExpr src = .ok e) :
    ∃ ps, lex src = .ok ps ∧ e.Derives (tokensOf ps) ∧ e.prec = true := parseCat_derives h

end Solidity.Frontend.Checked
