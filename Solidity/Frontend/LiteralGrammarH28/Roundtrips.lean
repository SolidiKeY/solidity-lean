import Solidity.Frontend.LiteralGrammarH28.Global
import Solidity.Frontend.LiteralGrammarH28.TaggedEncoding

/-! # Constructive round trips in every literal-bearing mode

Assembly's empty decoded value is spelled with a nonempty escaped line end.
These are pinned-model theorems, not compiler flag-name or Unicode validation
claims. No decoded-byte input contract is strengthened.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem encodePlain_sol_classify (q : UInt8) (quote : IsQuote q) (bytes : Bytes) :
    classify .sol (quoteBytes q (encodeBody bytes)) = some (.tok (.str bytes)) :=
  (classify_sol_literal_iff .plain _ _).mpr
    ⟨q, encodeBody bytes, quoteBytes_quoted q quote _, encodeBody_grammar _ _⟩

theorem encodePlain_yul_classify (depth : Nat) (q : UInt8) (quote : IsQuote q) (bytes : Bytes) :
    classify (.yul depth) (quoteBytes q (encodeBody bytes)) = some (.tok (.str bytes)) :=
  (classify_yul_plain_iff depth _ _).mpr
    ⟨q, encodeBody bytes, quoteBytes_quoted q quote _, encodeBody_grammar _ _⟩

theorem encodeHex_sol_classify (q : UInt8) (quote : IsQuote q) (bytes : Bytes) :
    classify .sol (hexPrefix ++ quoteBytes q (encodeHex bytes)) = some (.tok (.hexStr bytes)) :=
  (classify_sol_literal_iff .hex _ _).mpr (encodeHexLiteral_grammar q quote bytes)

theorem encodeHex_yul_classify (depth : Nat) (q : UInt8) (quote : IsQuote q) (bytes : Bytes) :
    classify (.yul depth) (hexPrefix ++ quoteBytes q (encodeHex bytes)) = some (.tok (.hexStr bytes)) :=
  (classify_yul_hex_iff depth _ _).mpr (encodeHexLiteral_grammar q quote bytes)

theorem encodeUnicode_sol_classify (q : UInt8) (quote : IsQuote q) (bytes : Bytes) :
    classify .sol (unicodePrefix ++ quoteBytes q (encodeBody bytes)) = some (.tok (.unicodeStr bytes)) :=
  (classify_sol_literal_iff .unicode _ _).mpr (encodeUnicodeLiteral_grammar q quote bytes)

def encodeAssembly (bytes : Bytes) : Bytes := quoteBytes 34 (92 :: 10 :: encodeBody bytes)

theorem encodeAssembly_grammar (bytes : Bytes) : AssemblyLiteral (encodeAssembly bytes) bytes := by
  have different : (10 : UInt8) ≠ 13 := by decide +kernel
  have body : Body (printable 34) (92 :: 10 :: encodeBody bytes) bytes :=
    .esc .lf (fun eq => False.elim (different eq)) (encodeBody_grammar _ bytes)
  refine ⟨⟨34, 92 :: 10 :: encodeBody bytes, quoteBytes_quoted 34 (Or.inl rfl) _, body⟩, rfl, ?_⟩
  simp only [encodeAssembly, quoteBytes_length, List.length_cons, encodeBody_length]
  omega

theorem encodeAssembly_classify (bytes : Bytes) :
    classify .asm (encodeAssembly bytes) = some (.tok (.str bytes)) :=
  (classify_asm_plain_iff _ _).mpr (encodeAssembly_grammar bytes)

theorem encodeAssembly_length (bytes : Bytes) : (encodeAssembly bytes).length = 4 * bytes.length + 4 := by
  simp only [encodeAssembly, quoteBytes_length, List.length_cons, encodeBody_length]

end Solidity.Frontend.LiteralGrammarH28
