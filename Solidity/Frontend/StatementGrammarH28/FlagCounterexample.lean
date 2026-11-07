import Solidity.Frontend.Checked.Parser
import Solidity.Frontend.Checked.Prec
import Solidity.Source.Ctor

/-!
# A statement-level yield collision independent of expression uniqueness

The existing assembly flag yield uses `ascii`, which narrows Unicode scalar
values to UInt8. This module records an inhabited counterexample and leaves
the universal target open; no input or producer contract is changed.
-/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- U+0141 narrows to the same byte as ASCII A. -/
def flagASCII : String := "A"
def flagUnicode : String := "Ł"

def flagStmtASCII : Syn (.stmt .body) := .assembly false [flagASCII] .nil
def flagStmtUnicode : Syn (.stmt .body) := .assembly false [flagUnicode] .nil

def flagTokens : List Tok :=
  [.kw .assembly, .punct .lparen, .str [65], .punct .rparen,
   .punct .lbrace, .punct .rbrace]

theorem flag_strings_distinct : flagASCII ≠ flagUnicode := by decide

theorem flag_statements_distinct : flagStmtASCII ≠ flagStmtUnicode := by
  intro h
  have bad : flagASCII = flagUnicode := congrArg (fun s : Syn (.stmt .body) =>
    match s with | .assembly _ fs _ => fs.headD "" | _ => "") h
  exact flag_strings_distinct bad

theorem flag_successful_common_yield :
    flagStmtASCII.toks [] = some flagTokens ∧
    flagStmtUnicode.toks [] = some flagTokens := by decide

theorem flag_both_precedence :
    flagStmtASCII.prec = true ∧ flagStmtUnicode.prec = true := by decide

/-- The original broad precedence/yield uniqueness target is false. This
counterexample contains no Solidity expression subtrees. -/
theorem not_universal_statement_yield_unique :
    ¬ (∀ (s t : Syn (.stmt .body)) (L M : List Choice) (ts : List Tok),
      s.prec = true → t.prec = true →
      s.toks L = some ts → t.toks M = some ts → s = t) := by
  intro h
  exact flag_statements_distinct
    (h flagStmtASCII flagStmtUnicode [] [] flagTokens
      flag_both_precedence.1 flag_both_precedence.2
      flag_successful_common_yield.1 flag_successful_common_yield.2)

/-- The existing canonical-rethrow exemption ignores the flag strings. -/
def flagRethrowBody : Syn (.list .yulStmt) :=
  .cons (.yulExprStmt (.yulCall "revert"
    (.cons (.yulCall "add" (.cons (.yulPath "D" [])
      (.cons (.yulLit (.dec 32)) .nil)))
      (.cons (.yulCall "mload" (.cons (.yulPath "D" []) .nil)) .nil)))) .nil

def flagProfileASCII : Syn (.stmt .body) := .assembly false [flagASCII] flagRethrowBody
def flagProfileUnicode : Syn (.stmt .body) := .assembly false [flagUnicode] flagRethrowBody

def flagProfileBodyTokens : List Tok :=
  [.punct .lbrace, .ident "revert", .punct .lparen, .ident "add", .punct .lparen,
   .ident "D", .punct .comma, .yulDec 32, .punct .rparen, .punct .comma,
   .ident "mload", .punct .lparen, .ident "D", .punct .rparen, .punct .rparen,
   .punct .rbrace]

def flagPrefix : List Tok :=
  [.kw .assembly, .punct .lparen, .str [65], .punct .rparen]

def flagProfileTokens : List Tok := flagPrefix ++ flagProfileBodyTokens

theorem flag_profile_successful_yield :
    flagProfileASCII.toks [] = some flagProfileTokens ∧
    flagProfileUnicode.toks [] = some flagProfileTokens := by decide

theorem flag_profile_precedence :
    flagProfileASCII.prec = true ∧ flagProfileUnicode.prec = true := by decide

theorem flag_profile_admitted :
    flagProfileASCII.InProfile ∧ flagProfileUnicode.InProfile := by decide

theorem flag_profile_distinct : flagProfileASCII ≠ flagProfileUnicode := by
  intro h
  have bad : flagASCII = flagUnicode := congrArg (fun s : Syn (.stmt .body) =>
    match s with | .assembly _ fs _ => fs.headD "" | _ => "") h
  exact flag_strings_distinct bad

/-- Even the existing profile restriction does not remove this collision.
No expression subtree or expression uniqueness premise occurs here. -/
theorem not_profile_statement_yield_unique :
    ¬ (∀ (s t : Syn (.stmt .body)) (L M : List Choice) (ts : List Tok),
      s.InProfile → t.InProfile → s.prec = true → t.prec = true →
      s.toks L = some ts → t.toks M = some ts → s = t) := by
  intro h
  exact flag_profile_distinct
    (h flagProfileASCII flagProfileUnicode [] [] flagProfileTokens
      flag_profile_admitted.1 flag_profile_admitted.2
      flag_profile_precedence.1 flag_profile_precedence.2
      flag_profile_successful_yield.1 flag_profile_successful_yield.2)

def flagInput (s : St) : St :=
  { s with ts := flagTokens.map (fun t => ⟨t, 0, 0⟩) ++ s.ts }

/-- Increasing fuel does not recover the original Unicode flag. -/
theorem flag_parse_normalizes (n : Nat) (s : St) :
    stmt (n + 2) .body (flagInput s) = .ok (flagStmtASCII, s) := by rfl

/-- No choice of fuel parses the colliding Unicode tree, even with the empty
suffix state. This refutes an existential-fuel roundtrip target, not just one
chosen bound. -/
theorem flag_unicode_no_fuel (fuel : Nat) (s : St) :
    stmt fuel .body (flagInput s) ≠ .ok (flagStmtUnicode, s) := by
  intro h
  cases fuel with
  | zero => cases h
  | succ n =>
    cases n with
    | zero => cases h
    | succ n =>
      rw [flag_parse_normalizes] at h
      have bad : flagStmtASCII = flagStmtUnicode :=
        congrArg Prod.fst (Except.ok.inj h)
      exact flag_statements_distinct bad

def flagProfileInput (s : St) : St :=
  { s with ts := flagProfileTokens.map (fun t => ⟨t, 0, 0⟩) ++ s.ts }

/-- Factor only the fixed flag prefix, leaving the existing Yul parser
opaque. No successful body parse is assumed. -/
theorem flag_prefix_factor (n : Nat) (bodyTs : List Located) (s : St) :
    stmt (n + 1) .body
      { s with ts := flagPrefix.map (fun t => ⟨t, 0, 0⟩) ++ bodyTs } =
    (yulBody n { s with ts := bodyTs }).bind
      (fun p => .ok (Syn.assembly false [flagASCII] p.1, p.2)) := by
  simp only [stmt]
  rfl

/-- No fuel or output suffix state recovers the Unicode canonical-rethrow
tree from its successful yield. The Yul parser may fail or succeed; it
cannot alter the flag already decoded by strArg. -/
theorem flag_profile_unicode_no_fuel (fuel : Nat) (s out : St) :
    stmt fuel .body (flagProfileInput s) ≠ .ok (flagProfileUnicode, out) := by
  intro h
  cases fuel with
  | zero => cases h
  | succ n =>
    have factor := flag_prefix_factor n
      (flagProfileBodyTokens.map (fun t => ⟨t, 0, 0⟩) ++ s.ts) s
    have input_eq : flagProfileInput s =
        { s with ts := flagPrefix.map (fun t => ⟨t, 0, 0⟩) ++
          (flagProfileBodyTokens.map (fun t => ⟨t, 0, 0⟩) ++ s.ts) } := by
      simp only [flagProfileInput, flagProfileTokens, List.map_append, List.append_assoc]
    rw [input_eq, factor] at h
    cases hb : yulBody n
        { s with ts := flagProfileBodyTokens.map (fun t => ⟨t, 0, 0⟩) ++ s.ts } with
    | error e => rw [hb] at h; cases h
    | ok result =>
      rw [hb] at h
      obtain ⟨body, rest⟩ := result
      have eqTree : Syn.assembly (k := .body) false [flagASCII] body = flagProfileUnicode :=
        congrArg Prod.fst (Except.ok.inj h)
      have bad : flagASCII = flagUnicode := congrArg (fun s : Syn (.stmt .body) =>
        match s with | .assembly _ fs _ => fs.headD "" | _ => "") eqTree
      exact flag_strings_distinct bad

/-- Even existential fuel cannot establish the unrestricted intrinsic
profile roundtrip target. This says nothing about ambiguity of accepted
source bytes: in any successful parse the flag prefix decodes to ASCII. -/
theorem not_profile_statement_parser_complete :
    ¬ (∀ (tree : Syn (.stmt .body)) (L : List Choice) (ts : List Tok),
      tree.InProfile → tree.prec = true → tree.toks L = some ts →
      ∃ fuel out, stmt fuel .body
        ⟨ts.map (fun t => ⟨t, 0, 0⟩), [], 0⟩ = .ok (tree, out)) := by
  intro h
  obtain ⟨fuel, out, hp⟩ := h flagProfileUnicode [] flagProfileTokens
    flag_profile_admitted.2 flag_profile_precedence.2 flag_profile_successful_yield.2
  exact flag_profile_unicode_no_fuel fuel ⟨[], [], 0⟩ out hp

/- A direct proof that the ASCII canonical-rethrow parse succeeds at fuel
n+6 exhausted the unchanged heartbeat budget. That separate normalization
bound remains open; it is not used in the all-fuel impossibility proof. -/

#print axioms not_profile_statement_parser_complete
#print axioms flag_prefix_factor
#print axioms flag_profile_unicode_no_fuel
#print axioms flag_profile_successful_yield
#print axioms flag_profile_precedence
#print axioms flag_profile_admitted
#print axioms flag_profile_distinct
#print axioms not_profile_statement_yield_unique
#print axioms flag_parse_normalizes
#print axioms flag_unicode_no_fuel
#print axioms flag_strings_distinct
#print axioms flag_statements_distinct
#print axioms flag_successful_common_yield
#print axioms flag_both_precedence
#print axioms not_universal_statement_yield_unique
end Solidity.Frontend.StatementGrammarH28
