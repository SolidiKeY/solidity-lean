import Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip

/-! Checks of the function-signature round trip: its leaf facts, then whole
signatures (nesting, empty lists, widths, locations) and the spellings that do
not come back. Every reading here is a kernel proof (no `#guard`, no native
code). -/
namespace Solidity.Examples.Lowering.Total.FunctionTypeRoundTrip

open Solidity Solidity.Correctness.Lowering.Total
open Solidity.Correctness.Lowering.Total.FunctionTypeDecode
open Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip
open Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws (fnParts?_mk fnTy?_mk partsL Well)
open Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws.Str (startsWith_mk)

def u256 : Source.Elem := .int false 256 (by decide)

/-! ## Core string reading in the kernel -/

example : ("0042" : String).toNat? = some 42 := (toNat?_mk _).trans (by decide)
example : ("4x" : String).toNat? = none := (toNat?_mk _).trans (by decide)
example : narrowTy? "int48" = some (.int, 48) := (narrowTy?_mk _).trans (by decide)
example : bytesTy? "bytes32" = some 32 ∧ bytesTy? "bytes33" = none :=
  ⟨(bytesTy?_mk _).trans (by decide), (bytesTy?_mk _).trans (by decide)⟩

/-! ## Elementary leaves: every width -/

example (s : Bool) (bits : Nat) (h) : leaf (elemName (.int s bits h)) = .elem (.int s bits h) :=
  (spelled_leaf (e := .int s bits h) trivial).1
example (n : Nat) (h) : leaf (elemName (.fixedBytes n h)) = .elem (.fixedBytes n h) ∧
    fnTy? (elemName (.fixedBytes n h)) = false :=
  have l := spelled_leaf (e := .fixedBytes n h) trivial
  ⟨l.1, l.2.1⟩
/-- `address payable` has no spelling of its own. -/
example : ¬ Spelled .addressPayable ∧ elemName .addressPayable = "" := ⟨id, rfl⟩

/-! ## Names: the elementary condition -/

example : ElemFree "S" ∧ ElemFree "uint7" ∧ ElemFree "mapping(uint=>bool)" := by decide +kernel
/-- `uint256` is a name of `uint`. -/
example : ¬ ElemFree "uint256" ∧ leaf "uint256" = .elem u256 :=
  ⟨by decide +kernel, (leaf_mk _).trans (by decide +kernel)⟩
example : ElemFree "Point[]" := elemFree_of_last (by decide) (by decide)

/-! ## Locations: cut at the spelled one -/

example (b : String) (d : Source.DataLoc) : leaf (b ++ locName d) = .located b d := leaf_located b d
/-- The boundary is not recorded: the name `Tmemory` reads as `T` in memory. -/
example : leaf "Tmemory" = .located "T" .memory := leaf_located "T" .memory
example : leaf "Tmemorystorage" = .located "Tmemory" .storage := leaf_located "Tmemory" .storage

/-! ## The leaf conditions are exact -/

/-- A component reads as a name only as itself, and exactly when it reads as
no elementary type and ends in no location word. -/
example {c n : String} (h : leaf c = .named n) : n = c ∧ ElemFree c ∧ locSuffix c = none := by
  cases leaf_named h
  exact ⟨rfl, (leaf_eq_named_iff c).1 h⟩
/-- An elementary spelling reads back exactly when `Spelled`: not `string`. -/
example (e : Source.Elem) (h : leaf (elemName e) = .elem e) : Spelled e ∧ ¬ Spelled .string :=
  ⟨(elem_reads_iff e).1 h, id⟩
/-- The conditions are the erased tree's: annotations play no part. -/
example (t : Part Ann) : t.erase.Canon ↔ t.Canon := Part.canon_erase t

/-! ## Whole signatures: nesting, both flags, ordered lists -/

def u8 : Source.Elem := .int false 8 (by decide)
def one {α : Type} (c : Part α) : Parts α := .cons c .nil
def two {α : Type} (c d : Part α) : Parts α := .cons c (one d)

/-- `function (function (uint8, S memory) external returns (bool), bytes4)
returns (function () returns (uint), address)`, annotated with mutabilities. -/
def nested : Part Ann :=
  .fn false ⟨some .view, true⟩
    (two (.fn true ⟨none, false⟩ (two (.elem u8) (.located "S" .memory)) (one (.elem .bool)))
      (.elem (.fixedBytes 4 (by decide))))
    (two (.fn false ⟨some .pure, false⟩ .nil (one (.elem u256))) (.elem .address))

/-- A written spelling read back: the tree is canonical and spells it (both
decided in the kernel), so `readSig_roundtrip` applies. -/
theorem back (ext : Bool) (ps rs : Parts Unit) {s : String}
    (canon : (Part.fn ext () ps rs).Canon) (spelled : (Part.fn ext () ps rs).spell = s) :
    readSig s = some (.fn ext () ps.erase rs.erase) := spelled ▸ readSig_roundtrip canon

def nestedS : String :=
  "function(function(uint8,Smemory)externalreturns(bool),bytes4)" ++
    "returns(function()returns(uint),address)"

example : nested.Canon := by decide +kernel
example : nested.spell = nestedS := by decide +kernel

/-- The spelling is read back: flags, order and nesting kept, annotations erased. -/
example : readSig nestedS = some nested.erase :=
  (show nested.spell = nestedS by decide +kernel) ▸ readSig_roundtrip (by decide +kernel)

/-- The erased tree, written out: no mutability, no `internal` keyword. -/
example : nested.erase =
    .fn false ()
      (two (.fn true () (two (.elem u8) (.located "S" .memory)) (one (.elem .bool)))
        (.elem (.fixedBytes 4 (by decide))))
      (two (.fn false () .nil (one (.elem u256))) (.elem .address)) := rfl

/-- Exactly the fuels from the depth on: `3` here, far below the budget. -/
example (n : Nat) : part n nestedS = some nested.erase ↔ 3 ≤ n :=
  (show nested.spell = nestedS by decide +kernel) ▸ part_canon_iff (by decide +kernel) n

/-- Any canonical components, at any depth, under either flag. -/
example {ps rs qs : Parts Ann} (e₁ e₂ : Bool) (a b : Ann)
    (hp : ps.Canon) (hr : rs.Canon) (hq : qs.Canon) :
    readSig (Part.fn e₁ a (.cons (.fn e₂ b ps rs) qs) (one (.fn e₁ b qs ps))).spell
      = some (.fn e₁ () (.cons (.fn e₂ () ps.erase rs.erase) qs.erase)
          (one (.fn e₁ () qs.erase ps.erase))) :=
  readSig_roundtrip ⟨⟨⟨hp, hr⟩, hq⟩, ⟨hq, hp⟩, trivial⟩

/-! ## Empty lists -/

example (ext : Bool) (a : Ann) :
    readSig (fnTyStr [] [] ext) = some (.fn ext () .nil .nil) :=
  readSig_fnTyStr ext a (ps := .nil) (rs := .nil) trivial trivial

/-! ## Declarations and marker rows -/

example : ofDecl (.named nestedS) = some nested.erase :=
  (show nested.spell = nestedS by decide +kernel) ▸ ofDecl_roundtrip (by decide +kernel)
example : ofDecl (.array (.named nestedS)) = none := rfl
/-- A state variable `f`'s marker row in the width table, other rows after it. -/
example (rows : List (String × Nat)) :
    ofRows (("f" ++ "#" ++ nested.spell, 0) :: rows) "f" = some nested.erase :=
  ofRows_roundtrip (by decide +kernel) "f" 0 rows
/-- The rows `valueRows?` keeps for a local of the type. -/
example : ∃ rows, valueRows? nested.spell = some (.uint, rows) ∧
    ofRows rows "" = some nested.erase := ofRows_valueRows (by decide +kernel)

/-- One erasure, one spelling, one reading, whatever the mutabilities. -/
example (a b : Ann) (ext : Bool) {ps rs : Parts Ann} (h : (Part.fn ext a ps rs).Canon) :
    (Part.fn ext a ps rs).spell = (Part.fn ext b ps rs).spell ∧
      readSig (Part.fn ext b ps rs).spell = some (Part.fn ext a ps rs).erase :=
  readSig_annotation_free h rfl

/-- A width row before the marker row is passed over. -/
example (rows : List (String × Nat)) :
    ofRows (("f", 8) :: ("f" ++ "#" ++ nested.spell, 0) :: rows) "f" = some nested.erase :=
  (ofRows_skip "f" 8 _ ((startsWith_mk _ _).trans (by decide))).trans
    (ofRows_roundtrip (by decide +kernel) "f" 0 rows)

/-- A leaf alone is no retained signature. -/
example : readSig "uint8" = none :=
  readSig_leaf (t := (.elem u8 : Part Unit)) trivial (by intros; simp)

/-- Canonical trees with one spelling differ at most in their annotations. -/
example {t u : Part Ann} (ht : t.Canon) (hu : u.Canon) (same : t.spell = u.spell) :
    t.erase = u.erase := canon_erase_inj ht hu same

end Solidity.Examples.Lowering.Total.FunctionTypeRoundTrip
