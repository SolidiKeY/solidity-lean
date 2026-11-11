import Solidity.SolcValidation.IrParse
import Solidity.SolcValidation.IrEval

/-! Hex strings are byte literals, left aligned in the same EVM word as an
ordinary string containing the identical decoded bytes. Printing preserves the
hex token and the parser checks its existing exact token/scoping certificate.
This is an IR-language extension, not compiler authentication or T02 matching. -/
namespace Solidity.SolcValidation.IrSyntax

/-- Hex payloads reuse the existing byte-to-word semantics and size check. -/
theorem hex_decode (bytes : List (Fin 256)) :
    (LitTok.hex bytes).decode = stringWord bytes := rfl

/-- Hex syntax remains hex syntax in the provenance token stream. -/
theorem hex_tokens (bytes : List (Fin 256)) :
    (LitTok.hex bytes).toks = [.hex bytes] := rfl

/-- Import recognizes the exact byte sequence, without numeric conversion. -/
theorem hex_recognized (bytes : List (Fin 256)) :
    litTok? (.hex bytes) = some (.hex bytes) := rfl

/-- Equal decoded string bytes give equal word values, including rejection. -/
theorem hex_string_decode {raw : String} {bytes : List (Fin 256)}
    (decoded : decodeString raw.toList = some bytes) :
    (LitTok.hex bytes).decode = (LitTok.str raw).decode := by
  simp only [LitTok.decode, decoded, bind, Option.bind]

/-- Oversized hex strings are rejected, rather than truncated to a word. -/
theorem hex_too_long (bytes : List (Fin 256)) (large : 32 < bytes.length) :
    (LitTok.hex bytes).decode = none := by
  simp only [LitTok.decode, stringWord, if_neg (Nat.not_le_of_gt large)]

/-- The actual IR evaluator returns the certified word and preserves every
machine state, independently of the concrete memory/world implementation. -/
theorem eval_hex {σ : Type} (M : Machine σ) (ctx : ObjectCtx)
    {F : List FnSig} {L : List String} (env : FunEnv F) (locals : Vals L)
    (state : σ) (fuel : Nat) (bytes : List (Fin 256)) (word : Word)
    (decoded : stringWord bytes = some word) :
    evalExpr M ctx (fuel + 1) env (.lit ⟨.hex bytes, word, decoded⟩) locals state =
      .ok (state, fun _ => word) := rfl

/-- info: 'Solidity.SolcValidation.IrSyntax.hex_decode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms hex_decode
/-- info: 'Solidity.SolcValidation.IrSyntax.hex_tokens' does not depend on any axioms -/
#guard_msgs in
#print axioms hex_tokens
/-- info: 'Solidity.SolcValidation.IrSyntax.hex_recognized' does not depend on any axioms -/
#guard_msgs in
#print axioms hex_recognized
/-- info: 'Solidity.SolcValidation.IrSyntax.hex_string_decode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms hex_string_decode
/-- info: 'Solidity.SolcValidation.IrSyntax.hex_too_long' depends on axioms: [propext] -/
#guard_msgs in
#print axioms hex_too_long
/-- info: 'Solidity.SolcValidation.IrSyntax.eval_hex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms eval_hex
end Solidity.SolcValidation.IrSyntax
