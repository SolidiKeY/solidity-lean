import Solidity.Frontend.LiteralGrammarH28.Roundtrips
import Solidity.Frontend.LiteralGrammarH28.Split

/-! # Independent all-mode literal and fragment grammar

This is a lexical/value relation. Mixed-kind token sequences are covered; no
claim is made that a parser admits every such sequence as one expression.
No constructor invents a literal class in pragma mode or Unicode in Yul.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

inductive ModeLiteral : Mode → Flavor → Bytes → Bytes → Prop where
  | sol {flavor : Flavor} {raw out : Bytes} : flavor.Rel raw out → ModeLiteral .sol flavor raw out
  | yulPlain {depth : Nat} {raw out : Bytes} : Plain raw out → ModeLiteral (.yul depth) .plain raw out
  | yulHex {depth : Nat} {raw out : Bytes} : HexLiteral raw out → ModeLiteral (.yul depth) .hex raw out
  | assembly {raw out : Bytes} : AssemblyLiteral raw out → ModeLiteral .asm .plain raw out

theorem modeLiteral_iff (mode : Mode) (flavor : Flavor) (raw out : Bytes) :
    classify mode raw = some (.tok (flavor.tag out)) ↔ ModeLiteral mode flavor raw out := by
  constructor
  · intro h
    cases mode with
    | sol => exact .sol ((classify_sol_literal_iff flavor raw out).mp h)
    | pragma => exact False.elim (classify_pragma_literal_impossible flavor raw out h)
    | asm =>
      cases flavor with
      | plain => exact .assembly ((classify_asm_plain_iff raw out).mp h)
      | hex => exact False.elim (classify_asm_nonplain_impossible .hex (by intro e; cases e) raw out h)
      | unicode => exact False.elim (classify_asm_nonplain_impossible .unicode (by intro e; cases e) raw out h)
    | yul depth =>
      cases flavor with
      | plain => exact .yulPlain ((classify_yul_plain_iff depth raw out).mp h)
      | hex => exact .yulHex ((classify_yul_hex_iff depth raw out).mp h)
      | unicode => exact False.elim (classify_yul_unicode_impossible depth raw out h)
  · intro h
    cases h with
    | sol value => exact (classify_sol_literal_iff _ _ _).mpr value
    | yulPlain value => exact (classify_yul_plain_iff _ _ _).mpr value
    | yulHex value => exact (classify_yul_hex_iff _ _ _).mpr value
    | assembly value => exact (classify_asm_plain_iff _ _).mpr value

theorem ModeLiteral.split {mode : Mode} {flavor : Flavor} {raw out : Bytes}
    (h : ModeLiteral mode flavor raw out) (suffix : Bytes) :
    Checked.split mode (raw ++ suffix) = .ok (raw, suffix) := by
  cases h with
  | @sol flavor raw out value =>
    cases flavor with
    | plain => exact Plain.split_mode value .sol (by intro e; cases e) suffix
    | hex => exact HexLiteral.split value .sol (Or.inl rfl) suffix
    | unicode => exact UnicodeLiteral.split value suffix
  | yulPlain value => exact value.split_mode _ (by intro e; cases e) suffix
  | yulHex value => exact value.split _ (Or.inr ⟨_, rfl⟩) suffix
  | assembly value => exact value.1.split_mode _ (by intro e; cases e) suffix

inductive ModeSequence (mode : Mode) : List Bytes → List (Flavor × Bytes) → Prop where
  | nil : ModeSequence mode [] []
  | cons {flavor : Flavor} {raw out : Bytes} {raws : List Bytes} {values : List (Flavor × Bytes)} :
      ModeLiteral mode flavor raw out → ModeSequence mode raws values →
      ModeSequence mode (raw :: raws) ((flavor, out) :: values)

def sequenceTags (values : List (Flavor × Bytes)) : List Kind :=
  values.map (fun pair => Kind.tok (pair.1.tag pair.2))

theorem modeSequence_iff (mode : Mode) (raws : List Bytes) (values : List (Flavor × Bytes)) :
    raws.mapM (classify mode) = some (sequenceTags values) ↔ ModeSequence mode raws values := by
  constructor
  · intro h
    induction raws generalizing values with
    | nil =>
      cases values with
      | nil => exact .nil
      | cons pair rest => cases h
    | cons raw raws ih =>
      cases first : classify mode raw with
      | none => rw [List.mapM_cons, first] at h; cases h
      | some tok =>
        cases rest : raws.mapM (classify mode) with
        | none => rw [List.mapM_cons, first, rest] at h; cases h
        | some tokens =>
          rw [List.mapM_cons, first, rest] at h
          cases values with
          | nil => cases h
          | cons pair values =>
            rcases pair with ⟨flavor, bytes⟩
            have parts : tok = Kind.tok (flavor.tag bytes) ∧ tokens = sequenceTags values :=
              List.cons.inj (Option.some.inj h)
            have head : classify mode raw = some (.tok (flavor.tag bytes)) :=
              first.trans (congrArg some parts.1)
            have tail : raws.mapM (classify mode) = some (sequenceTags values) :=
              rest.trans (congrArg some parts.2)
            exact .cons ((modeLiteral_iff mode flavor raw bytes).mp head) (ih values tail)
  · intro h
    induction h with
    | nil => rfl
    | @cons flavor raw out raws values first _ ih =>
      rw [List.mapM_cons, (modeLiteral_iff mode flavor raw out).mpr first, ih]
      rfl

theorem ModeSequence.append {mode : Mode} {left right : List Bytes}
    {a b : List (Flavor × Bytes)} (ha : ModeSequence mode left a) (hb : ModeSequence mode right b) :
    ModeSequence mode (left ++ right) (a ++ b) := by
  induction ha with
  | nil => exact hb
  | cons first _ ih => exact .cons first ih

def sequenceBytes (values : List (Flavor × Bytes)) : Bytes := (values.map Prod.snd).flatten

theorem sequenceBytes_append (a b : List (Flavor × Bytes)) :
    sequenceBytes (a ++ b) = sequenceBytes a ++ sequenceBytes b := by
  simp only [sequenceBytes, List.map_append, List.flatten_append]

theorem ModeSequence.split_head {mode : Mode} {flavor : Flavor} {raw out : Bytes}
    {raws : List Bytes} {values : List (Flavor × Bytes)}
    (h : ModeSequence mode (raw :: raws) ((flavor, out) :: values)) (suffix : Bytes) :
    Checked.split mode (raw ++ (raws.flatten ++ suffix)) = .ok (raw, raws.flatten ++ suffix) := by
  cases h with
  | cons first _ => exact first.split _

end Solidity.Frontend.LiteralGrammarH28
