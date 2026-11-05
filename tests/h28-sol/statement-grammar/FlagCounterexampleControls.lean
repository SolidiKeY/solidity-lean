import Solidity.Frontend.StatementGrammarH28.FlagCounterexample

/-! Inhabited flag collision and retained source-token refusal controls. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def flagSuffix : St := ⟨[⟨.kw .else_, 80, 84⟩], [.attrs [.vis]], 90⟩

example : stmt 2 .body (flagInput flagSuffix) = .ok (flagStmtASCII, flagSuffix) :=
  flag_parse_normalizes 0 flagSuffix

example (fuel : Nat) (out : St) :
    stmt fuel .body (flagProfileInput flagSuffix) ≠ .ok (flagProfileUnicode, out) :=
  flag_profile_unicode_no_fuel fuel flagSuffix out

example : flagProfileASCII.InProfile ∧ flagProfileUnicode.InProfile := flag_profile_admitted

example : flagProfileASCII.toks [] = some flagProfileTokens ∧
    flagProfileUnicode.toks [] = some flagProfileTokens := flag_profile_successful_yield

/-- Existing non-ASCII source-token refusal is retained. The successful
yield collision encodes byte 65; it does not claim this UTF-8 token is accepted. -/
example (s : St) :
    strArg "assembly flag" { s with ts := ⟨.str [197, 129], 3, 7⟩ :: s.ts } =
      .error ⟨3, "non-ASCII assembly flag"⟩ := by rfl

example (s : St) :
    strArg "assembly flag" { s with ts := ⟨.str [], 3, 5⟩ :: s.ts } =
      .error ⟨3, "empty assembly flag"⟩ := by rfl

example (s : St) :
    strArg "assembly flag" { s with ts := ⟨.str [65], 3, 6⟩ :: s.ts } =
      .ok (flagASCII, s) := by rfl

end Solidity.Frontend.StatementGrammarH28
