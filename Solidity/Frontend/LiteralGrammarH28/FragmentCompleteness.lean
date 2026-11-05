import Solidity.Frontend.LiteralGrammarH28.Fragments
import Solidity.Frontend.LiteralGrammarH28.Global
import Solidity.Frontend.LiteralGrammarH28.Split
import Solidity.Frontend.LiteralGrammarH28.TaggedEncoding

/-! # All-kind fragment completeness

Unrestricted classification inversions extend to arbitrary fragment lists.
Every admitted literal kind also has an exact next-source-fragment split law.
No raw escape bodies are joined across delimiter boundaries.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem fragments_tagged_iff {α : Type} (literal : Bytes → Bytes → Prop)
    (classifier : Bytes → Option α) (tag : Bytes → α)
    (spec : ∀ raw out, classifier raw = some (tag out) ↔ literal raw out)
    (raws values : List Bytes) :
    raws.mapM classifier = some (values.map tag) ↔ Fragments literal raws values := by
  constructor
  · intro h
    induction raws generalizing values with
    | nil =>
      cases values with
      | nil => exact .nil
      | cons out rest => cases h
    | cons raw raws ih =>
      cases first : classifier raw with
      | none => rw [List.mapM_cons, first] at h; cases h
      | some tok =>
        cases rest : raws.mapM classifier with
        | none => rw [List.mapM_cons, first, rest] at h; cases h
        | some tokens =>
          rw [List.mapM_cons, first, rest] at h
          cases values with
          | nil => cases h
          | cons out values =>
            have pair : tok = tag out ∧ tokens = values.map tag := List.cons.inj (Option.some.inj h)
            have head : classifier raw = some (tag out) := by rw [first, pair.1]
            have tail : raws.mapM classifier = some (values.map tag) := rest.trans (congrArg some pair.2)
            exact .cons ((spec raw out).mp head) (ih values tail)
  · intro h
    induction h with
    | nil => rfl
    | @cons raw out raws values first _ ih =>
      rw [List.mapM_cons, (spec raw out).mpr first, ih]
      rfl

theorem fragments_solTok_iff (flavor : Flavor) (raws values : List Bytes) :
    raws.mapM solTok = some (values.map flavor.tag) ↔ Fragments flavor.Rel raws values :=
  fragments_tagged_iff flavor.Rel solTok flavor.tag (solTok_literal_iff flavor) raws values

theorem fragments_classify_sol_iff (flavor : Flavor) (raws values : List Bytes) :
    raws.mapM (classify .sol) = some (values.map (fun b => Kind.tok (flavor.tag b))) ↔
      Fragments flavor.Rel raws values :=
  fragments_tagged_iff flavor.Rel (classify .sol) (fun b => Kind.tok (flavor.tag b))
    (classify_sol_literal_iff flavor) raws values

theorem fragments_yul_plain_iff (depth : Nat) (raws values : List Bytes) :
    raws.mapM (classify (.yul depth)) = some (values.map (fun b => Kind.tok (.str b))) ↔
      Fragments Plain raws values :=
  fragments_tagged_iff Plain (classify (.yul depth)) (fun b => Kind.tok (.str b))
    (classify_yul_plain_iff depth) raws values

theorem fragments_yul_hex_iff (depth : Nat) (raws values : List Bytes) :
    raws.mapM (classify (.yul depth)) = some (values.map (fun b => Kind.tok (.hexStr b))) ↔
      Fragments HexLiteral raws values :=
  fragments_tagged_iff HexLiteral (classify (.yul depth)) (fun b => Kind.tok (.hexStr b))
    (classify_yul_hex_iff depth) raws values

theorem encoded_hex_fragments (q : UInt8) (quote : IsQuote q) (values : List Bytes) :
    Fragments HexLiteral (values.map (fun b => hexPrefix ++ quoteBytes q (encodeHex b))) values := by
  induction values with
  | nil => exact .nil
  | cons bytes rest ih => exact .cons (encodeHexLiteral_grammar q quote bytes) ih

theorem encoded_unicode_fragments (q : UInt8) (quote : IsQuote q) (values : List Bytes) :
    Fragments UnicodeLiteral (values.map (fun b => unicodePrefix ++ quoteBytes q (encodeBody b))) values := by
  induction values with
  | nil => exact .nil
  | cons bytes rest ih => exact .cons (encodeUnicodeLiteral_grammar q quote bytes) ih

theorem encoded_hex_fragments_roundtrip (q : UInt8) (quote : IsQuote q) (values : List Bytes) :
    (values.map (fun b => hexPrefix ++ quoteBytes q (encodeHex b))).mapM solTok =
      some (values.map Tok.hexStr) :=
  (fragments_solTok_iff .hex _ _).mpr (encoded_hex_fragments q quote values)

theorem encoded_unicode_fragments_roundtrip (q : UInt8) (quote : IsQuote q) (values : List Bytes) :
    (values.map (fun b => unicodePrefix ++ quoteBytes q (encodeBody b))).mapM solTok =
      some (values.map Tok.unicodeStr) :=
  (fragments_solTok_iff .unicode _ _).mpr (encoded_unicode_fragments q quote values)

theorem Fragments.plain_split_head {raw out : Bytes} {raws values : List Bytes}
    (h : Fragments Plain (raw :: raws) (out :: values))
    (mode : Mode) (notPragma : mode ≠ .pragma) (suffix : Bytes) :
    split mode (raw ++ (raws.flatten ++ suffix)) = .ok (raw, raws.flatten ++ suffix) := by
  cases h with
  | cons first _ => exact first.split_mode mode notPragma _

theorem Fragments.hex_split_head {raw out : Bytes} {raws values : List Bytes}
    (h : Fragments HexLiteral (raw :: raws) (out :: values))
    (mode : Mode) (admitted : HexMode mode) (suffix : Bytes) :
    split mode (raw ++ (raws.flatten ++ suffix)) = .ok (raw, raws.flatten ++ suffix) := by
  cases h with
  | cons first _ => exact first.split mode admitted _

theorem Fragments.unicode_split_head {raw out : Bytes} {raws values : List Bytes}
    (h : Fragments UnicodeLiteral (raw :: raws) (out :: values)) (suffix : Bytes) :
    split .sol (raw ++ (raws.flatten ++ suffix)) = .ok (raw, raws.flatten ++ suffix) := by
  cases h with
  | cons first _ => exact first.split _

theorem encoded_hex_fragments_value (q : UInt8) (quote : IsQuote q) (values : List Bytes) :
    FragmentValue HexLiteral (values.map (fun b => hexPrefix ++ quoteBytes q (encodeHex b))) values.flatten :=
  ⟨values, encoded_hex_fragments q quote values, rfl⟩

theorem encoded_unicode_fragments_value (q : UInt8) (quote : IsQuote q) (values : List Bytes) :
    FragmentValue UnicodeLiteral (values.map (fun b => unicodePrefix ++ quoteBytes q (encodeBody b))) values.flatten :=
  ⟨values, encoded_unicode_fragments q quote values, rfl⟩

theorem FragmentValue.byteLength {literal : Bytes → Bytes → Prop} {raws : List Bytes} {out : Bytes}
    (h : FragmentValue literal raws out) :
    ∃ values, Fragments literal raws values ∧ out.length = (values.map List.length).sum := by
  obtain ⟨values, grammar, rfl⟩ := h
  exact ⟨values, grammar, List.length_flatten⟩

end Solidity.Frontend.LiteralGrammarH28

