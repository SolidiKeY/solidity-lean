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
example : readSig "function()" = some (.fn false () .nil .nil) :=
  back false .nil .nil (by decide) (by decide)
example : readSig "function()external" = some (.fn true () .nil .nil) :=
  back true .nil .nil (by decide) (by decide)
/-- No parameters, one return; and parameters without returns. -/
example : readSig "function()returns(bool)" = some (.fn false () .nil (one (.elem .bool))) :=
  back false .nil (one (.elem .bool)) (by decide +kernel) (by decide +kernel)
example : readSig "function(bool,address)external"
    = some (.fn true () (two (.elem .bool) (.elem .address)) .nil) :=
  back true (two (.elem .bool) (.elem .address)) .nil (by decide +kernel) (by decide +kernel)

/-! ## Widths -/

/-- Every integer width and sign as a parameter, every `bytesN` as a return
(the conditions are the same in both positions). -/
example (s : Bool) (bits n : Nat) (h h') (ext : Bool) (a : Ann) :
    readSig (Part.fn ext a (one (.elem (.int s bits h))) (one (.elem (.fixedBytes n h')))).spell
      = some (.fn ext () (one (.elem (.int s bits h))) (one (.elem (.fixedBytes n h')))) :=
  readSig_roundtrip ⟨⟨trivial, trivial⟩, trivial, trivial⟩
example : readSig "function(uint8,int128)returns(bytes32,uint)" =
    some (.fn false () (two (.elem u8) (.elem (.int true 128 (by decide))))
      (two (.elem (.fixedBytes 32 (by decide))) (.elem u256))) :=
  back false (two (.elem u8) (.elem (.int true 128 (by decide))))
    (two (.elem (.fixedBytes 32 (by decide))) (.elem u256)) (by decide +kernel) (by decide +kernel)

/-! ## Locations -/

/-- Any located component whose spelling is a `Well` non-function component. -/
example (b : String) (l : Source.DataLoc) (ok : LocatedOk b l) (ext : Bool) :
    readSig (Part.fn ext () (one (.located b l)) .nil).spell
      = some (.fn ext () (one (.located b l)) .nil) :=
  readSig_roundtrip ⟨⟨ok, trivial⟩, trivial⟩
example : readSig "function(uint[]memory,S[2]storage)returns(bytescalldata)" =
    some (.fn false () (two (.located "uint[]" .memory) (.located "S[2]" .storage))
      (one (.located "bytes" .calldata))) :=
  back false (two (.located "uint[]" .memory) (.located "S[2]" .storage))
    (one (.located "bytes" .calldata)) (by decide +kernel) (by decide +kernel)
/-- A named component with no location: a struct, a mapping. -/
example : readSig "function(S,mapping(uint=>bool))" =
    some (.fn false () (two (.named "S") (.named "mapping(uint=>bool)")) .nil) :=
  back false (two (.named "S") (.named "mapping(uint=>bool)")) .nil (by decide +kernel)
    (by decide +kernel)

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

/-! ## What does not come back -/

/-- `address payable` has no spelling: alone, it is read back as no parameter. -/
example : ¬ (Part.fn false () (one (.elem .addressPayable)) .nil).Canon ∧
    readSig (Part.fn false () (one (.elem .addressPayable)) .nil).spell
      = some (.fn false () .nil .nil) :=
  ⟨by decide +kernel, back false .nil .nil (by decide) (by decide +kernel)⟩

/-- A name ending in a location word is read as a located component. -/
example : ¬ NamedOk "Tmemory" ∧
    readSig (Part.fn false () (one (.named "Tmemory")) .nil).spell
      = some (.fn false () (one (.located "T" .memory)) .nil) :=
  ⟨by decide +kernel,
    back false (one (.located "T" .memory)) .nil (by decide +kernel) (by decide +kernel)⟩

/-- An elementary name is read as the elementary type (`uint256` as `uint`):
the spelling is not the canonical one, the reading is by the fuel laws. -/
example : ¬ NamedOk "uint256" ∧
    readSig "function(uint256)" = some (.fn false () (one (.elem u256)) .nil) :=
  ⟨by decide +kernel,
    readSig_of_splits (t := Part.fn false () (one (.elem u256)) .nil)
      ⟨["uint256"], [], (fnParts?_mk _).trans (by decide +kernel),
        ⟨"uint256", [], rfl,
          ⟨(notFn_iff _).2 (by decide), (leaf_mk _).trans (by decide +kernel)⟩, rfl⟩, rfl⟩
      ((fnTy?_mk _).trans (by decide)) (by decide)⟩

/-- A comma at a component's own depth: one name is read as two. -/
example : ¬ NamedOk "a,b" ∧
    readSig (Part.fn true () (one (.named "a,b")) .nil).spell
      = some (.fn true () (two (.named "a") (.named "b")) .nil) :=
  ⟨by decide +kernel,
    back true (two (.named "a") (.named "b")) .nil (by decide +kernel) (by decide +kernel)⟩

/-- An empty name and an unbalanced bracket are not `Well`, so not `NamedOk`. -/
example : ¬ Well "" ∧ ¬ Well "T)" ∧ ¬ Well "T[" ∧
    ¬ NamedOk "" ∧ ¬ NamedOk "T)" ∧ ¬ NamedOk "T[" := by decide +kernel

/-- A function-type suffix: the component starts as a function type, so it is
no named or located leaf, and `fnParts?` refuses it at every fuel. -/
example : ¬ NamedOk "function(uint)[]" ∧ ¬ LocatedOk "function(uint)[]" .memory ∧
    readSig (Part.fn false () (one (.located "function(uint)[]" .memory)) .nil).spell = none :=
  ⟨by decide +kernel, by decide +kernel,
    readSig_refused (.param (c := "function(uint)[]memory") (ps := ["function(uint)[]memory"])
      (rs := []) (ext := false)
      ((fnParts?_mk _).trans (by decide +kernel)) (List.mem_singleton.2 rfl)
      (.malformed ((fnTy?_mk _).trans (by decide)) ((fnParts?_mk _).trans (by decide +kernel))))⟩

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
