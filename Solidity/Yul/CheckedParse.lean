import Solidity.Frontend.Checked.Check

/-!
# Checked assembly grammar entry point

This adapter reuses G08–G11 unchanged. It parses an entire Solidity assembly
statement, allowing the existing lexer to enter/leave Yul mode. Successful
results retain the existing yield/precedence certificate. Neither syntax-level
profile admission nor Yul static checking is asserted by this grammar adapter.
-/
namespace Solidity.Yul
open Solidity.Source
open Solidity.Frontend.Checked

/-- Existing statement parser, with exactly its existing token-derived fuel. -/
def assemblyParser (fuel : Nat) : P (Syn (.stmt SCtx.body)) := stmt fuel SCtx.body

/-- A grammar result carries evidence from the existing checked parser. -/
structure AssemblyParse (src : Bytes) where
  evmasm : Bool
  flags : List String
  body : Syn (.list .yulStmt)
  layout : List Choice
  checked : parseCat assemblyParser src = .ok (.assembly evmasm flags body, layout)

private def packAssembly {src : Bytes} (t : Syn (.stmt SCtx.body)) (L : List Choice)
    (h : parseCat assemblyParser src = .ok (t, L)) : Option (AssemblyParse src) := by
  cases t with
  | assembly evmasm flags body => exact some ⟨evmasm, flags, body, L, h⟩
  | _ => exact none

/-- Parse only assembly statements; unrelated statements are not assembly.
Unknown flags are preserved for metadata validation, rather than silently erased. -/
def parseAssembly (src : Bytes) : Option (AssemblyParse src) :=
  match h : parseCat assemblyParser src with
  | .error _ => none
  | .ok (t, L) => packAssembly t L h

/-- Every returned assembly tree is a checked grammar derivation of the exact
source token sequence; this does not imply memory safety or static admission. -/
theorem AssemblyParse.sound {src : Bytes} (p : AssemblyParse src) :
    ∃ ps, lex src = .ok ps ∧ Lexed src ps ∧
      (Syn.assembly (k := SCtx.body) p.evmasm p.flags p.body).toks p.layout = some (tokensOf ps) ∧
      (Syn.assembly (k := SCtx.body) p.evmasm p.flags p.body).prec = true := by
  obtain ⟨ps, hl, ht, hp⟩ := parseCat_sound p.checked
  exact ⟨ps, hl, lex_sound hl, ht, hp⟩

end Solidity.Yul
