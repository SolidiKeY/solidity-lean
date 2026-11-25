import Solidity.Correctness.Lowering.Total.ReferenceDecode

/-! Checks of the reference-type and parameter-location decoder: nested arrays
with their lengths and element width, structs by their one written name,
mappings and the three declared locations, the frame context that merges
`memory` and `calldata`, an error naming each missing piece of metadata, and
the same spellings from types as read. -/
namespace Solidity.Examples.Lowering.Total.ReferenceDecode

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.ReferenceDecode
open Source (Syn STy DataLoc)

/-- `struct Pair { uint a; uint8 b; }`, spelled in the table by its members. -/
def pairs : Contract where
  vars := []
  structs := [("Pair", "Pair{a:uint;b:uint8}")]

def u8 : Source.Elem := .int false 8 (by decide)
def u256 : Source.Elem := .int false 256 (by decide)

/-! ## Nested arrays -/

/-- `function f(uint8[3][] memory xs, uint[][2] calldata ys)`. -/
def nested : FunDecl where
  params := [("xs", .ref (.array (.ref (.fixed .uint 3)))),
    ("ys", .ref (.fixed (.ref (.array .uint)) 2))]
  paramLocs := [("xs", .memory), ("ys", .calldata)]
  widths := [("xs[][]", 8)]
  body := []

/-- Nesting order, both lengths, the element width and each location. -/
theorem nested_signature : signature pairs nested = .ok
    (.cons (.param (.array (.array (.elem u8) (.some (lenLit 3))) .none) (some .memory)
        (some "xs"))
      (.cons (.param (.array (.array (.elem u256) .none) (.some (lenLit 2)))
        (some .calldata) (some "ys")) .nil), .nil) := rfl

/-- The actual Source frame types, in an empty unit: no struct is mentioned. -/
example : (signature pairs nested).toOption.bind (fun s =>
      (Source.Frame.mk? ⟨[]⟩ none s.1 s.2 .nil false false).map (·.ps)) = some
    [.array .memory (.array .memory (.int ⟨false, 8, by decide⟩) (some 3)) none,
      .array .calldata (.array .calldata (.int ⟨false, 256, by decide⟩) none) (some 2)] := rfl

/-! ## Structs -/

/-- `function g(Pair storage p, Token memory t) returns (Pair memory r)`:
a contract struct and a struct of the table. -/
def structs : FunDecl where
  params := [("p", .ref (.struct "Pair{a:uint;b:uint8}")), ("t", .ref (.struct "Token"))]
  paramLocs := [("p", .storage), ("t", .memory)]
  rets := [("r", .ref (.struct "Pair{a:uint;b:uint8}"))]
  retMem := true
  body := []

/-- Each struct by its written name, at its location; the member spelling of
the table name is not written. -/
theorem structs_signature : signature pairs structs = .ok
    (.cons (.param (.userType ⟨"Pair", []⟩) (some .storage) (some "p"))
      (.cons (.param (.userType ⟨"Token", []⟩) (some .memory) (some "t")) .nil),
     .cons (.param (.userType ⟨"Pair", []⟩) (some .memory) (some "r")) .nil) := rfl

/-- The written name elaborates back to the table type, and is the only one. -/
example : pairs.structName? "Pair" = some "Pair{a:uint;b:uint8}" :=
  (written?_sound (C := pairs) (by decide)).1

/-- Under the resolution obligations of `Pair` and `Token`, the frame's types
are the resolved declarations at the declared locations. -/
example (E : Source.Env) (dp dt : Source.DeclName)
    (hp : Resolved E (some "C") "Pair" dp) (ht : Resolved E (some "C") "Token" dt) :
    ∃ f, Source.Frame.mk? E (some "C")
        (.cons (.param (.userType ⟨"Pair", []⟩) (some .storage) (some "p"))
          (.cons (.param (.userType ⟨"Token", []⟩) (some .memory) (some "t")) .nil))
        (.cons (.param (.userType ⟨"Pair", []⟩) (some .memory) (some "r")) .nil)
        .nil false false = some f ∧
      f.ps = [.struct .storage dp, .struct .memory dt] ∧ f.rs = [.struct .memory dp] := by
  simp [Source.Frame.mk?, Source.Syn.tys, hp.userTy, ht.userTy]

/-- Two written names with the same members: which one was written is erased. -/
def twins : Contract where
  vars := []
  structs := [("A", "A{a:uint}"), ("B", "A{a:uint}")]

example : spellType twins [] "p" .memory (.ref (.struct "A{a:uint}")) =
    .error (.ambiguousStruct "p" "A{a:uint}" ["A", "B"]) := rfl

/-- A table type no name of the contract reads as. -/
example : spellType pairs [] "p" .memory (.ref (.struct "Nope")) =
    .error (.unknownStruct "p" "Nope") := rfl

/-! ## Mappings and locations -/

/-- `mapping(address => uint8[]) storage m`. -/
def mapped : FunDecl where
  params := [("m", .ref (.mapping .uint (.ref (.array .uint))))]
  paramLocs := [("m", .storage)]
  widths := [("m{}#address", 20), ("m[][]", 8)]
  body := []

/-- The marked key, the value's nesting and width, in storage. -/
theorem mapped_signature : signature pairs mapped = .ok
    (.cons (.param (.mapping (.elem .address (by decide)) none
        (.array (.elem u8) .none) none) (some .storage) (some "m")) .nil, .nil) := rfl

example : (signature pairs mapped).toOption.bind (fun s =>
      (Source.Frame.mk? ⟨[]⟩ none s.1 s.2 .nil false false).map (·.ps)) = some
    [.mapping (.address false) (.array .storage (.int ⟨false, 8, by decide⟩) none)] := rfl

/-- A mapping declared outside storage has no Source type. -/
example : signature pairs { mapped with paramLocs := [("m", .memory)] } =
    .error (.mappingOutsideStorage "m" .memory) := rfl

/-- `uint[] memory a` and `uint[] calldata a`. -/
def inMemory : FunDecl where
  params := [("a", .ref (.array .uint))]
  paramLocs := [("a", .memory)]
  body := []

def inCalldata : FunDecl := { inMemory with paramLocs := [("a", .calldata)] }

/-- The frame context does not tell them apart; the decoded lists do. -/
example : inMemory.paramCtx = inCalldata.paramCtx := rfl

example : (signature pairs inMemory).map (fun s => declaredLocs s.1) =
    .ok [some .memory] := rfl

example : (signature pairs inCalldata).map (fun s => declaredLocs s.1) =
    .ok [some .calldata] := rfl

/-! ## Missing metadata -/

/-- A reference parameter without a location. -/
example : signature pairs { inMemory with paramLocs := [] } =
    .error (.missingLocation "a") := rfl

/-- A location on a value parameter. -/
example : signature pairs { params := [("n", .uint)], paramLocs := [("n", .memory)], body := [] } =
    .error (.locationOnValue "n" .memory) := rfl

/-- An enum element: its marker row is not read, and not guessed past. -/
example : signature pairs { inMemory with widths := [("a[]#enum", 1)] } =
    .error (.unreadRow "a" "a[]#enum" 1) := rfl

/-- `bytes` and `bytes1[]` leave the same rows. -/
example : signature pairs { inMemory with widths := [("a[]", 8), ("a[]#bytes", 1)] } =
    .error (.erasedBytes "a") := rfl

/-- A width no integer type has, below two arrays. -/
example : spellType pairs [("x[][]", 7)] "x" .memory (.ref (.array (.ref (.array .uint)))) =
    .error (.unrepresentable "x[][]" .uint) := rfl

/-- A zero-length fixed array. -/
example : spellType pairs [] "x" .memory (.ref (.fixed .uint 0)) =
    .error (.zeroLength "x") := rfl

/-- `returns (uint[] r)` with no location flag. -/
def bareReturn : FunDecl where
  params := []
  rets := [("r", .ref (.array .uint))]
  body := []

/-- A reference return whose flags give no location, and one with both. -/
example : signature pairs bareReturn = .error (.missingReturnLocation "r") := rfl

example : signature pairs { bareReturn with retMem := true, retStorage := true } =
    .error (.conflictingReturnLocation "r") := rfl

/-- One flag is the location; a storage return is kept as one. -/
example : (signature pairs { bareReturn with retStorage := true }).map
    (fun s => declaredLocs s.2) = .ok [some .storage] := rfl

/-- Value binders alone: the primitive component's list. -/
example : binders pairs [("n", 8)] (fun _ _ => .ok none) [("n", .uint), ("b", .bool)] = .ok
    (.cons (.param (.elem u8) none (some "n"))
      (.cons (.param (.elem .bool) none (some "b")) .nil)) :=
  binders_primitive rfl (by simp)

/-! ## Types as read

Leaf names are read by string functions the kernel does not unfold, so these
are evaluated checks. -/

-- `uint8[3][]`: the same nesting, length and width from the retained names.
#guard match rawType pairs .memory (.array (.fixed (.named "uint8") 3)) with
  | .ok (.array (.array (.elem (.int false 8 _)) (.some (.lit (.num (.dec 3 0 0))))) .none) =>
    true
  | _ => false

-- `mapping(address => Pair[])` in storage: the struct by its written name.
#guard match rawType pairs .storage (.mapping (.named "address") (.array (.named "Pair"))) with
  | .ok (.mapping (.elem .address _) none (.array (.userType ⟨"Pair", []⟩) .none) none) => true
  | _ => false

/-- Its Source type, under the resolution obligation of `Pair`. -/
example (E : Source.Env) (d : Source.DeclName) (h : Resolved E (some "C") "Pair" d)
    (t : Syn .typeName)
    (ok : rawType pairs .storage (.mapping (.named "address") (.array (.named "Pair"))) = .ok t) :
    ∃ τ, t.tys E (some "C") .storage = some [τ] ∧
      RawRep pairs E (some "C") .storage
        (.mapping (.named "address") (.array (.named "Pair"))) τ :=
  rawType_typed pairs E (some "C") _ .storage t ok (by
    intro s ms _
    have : s = "Pair" := by simpa [rawNames] using ms
    exact ⟨d, this ▸ h⟩)

/-- `bytes`, an enum and a struct key are named, not read as something else. -/
def withEnum : Contract where
  vars := []
  enums := [("Color", ["Red", "Green"])]

#guard match rawType pairs .memory (.named "bytes") with
  | .error (.unsupportedName "bytes") => true
  | _ => false

#guard match rawType withEnum .memory (.array (.named "Color")) with
  | .error (.unsupportedName "Color") => true
  | _ => false

#guard match rawType pairs .storage (.mapping (.named "Pair") (.named "uint")) with
  | .error (.unsupportedKey (.named "Pair")) => true
  | _ => false

#guard match rawType pairs .memory (.mapping (.named "uint") (.named "uint")) with
  | .error (.mappingOutsideStorage .memory) => true
  | _ => false

#guard match rawType pairs .memory (.named "Missing") with
  | .error (.unknownName "Missing") => true
  | _ => false

#guard match rawType pairs .memory (.fixed (.named "bool") 0) with
  | .error .zeroLength => true
  | _ => false

end Solidity.Examples.Lowering.Total.ReferenceDecode
