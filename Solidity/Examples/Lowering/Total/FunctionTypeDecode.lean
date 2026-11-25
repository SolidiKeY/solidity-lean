import Solidity.Correctness.Lowering.Total.FunctionTypeDecode

/-! Checks of the retained function-type signature component. Concrete
spellings are read by `#guard` (compiled code: `fnParts?` does not reduce in
the kernel); everything after the reading is proved on the trees. -/
namespace Solidity.Examples.Lowering.Total.FunctionTypeDecode

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.FunctionTypeDecode
open Solidity.Source (Syn STy DataLoc)

/-- `uint256`, `uint8`, `bool`, `address`, `bytes4` as components. -/
def u256 : Source.Elem := .int false 256 (by decide)
def u8 : Source.Elem := .int false 8 (by decide)
def b4 : Source.Elem := .fixedBytes 4 (by decide)

/-! ## Internal and external -/

/-- `function (uint) returns (uint)`, internal. -/
def unary : Part Unit := .fn false () (.cons (.elem u256) .nil) (.cons (.elem u256) .nil)

#guard readSig "function(uint)returns(uint)" == some unary
#guard ofDecl (.named "function(uint256)returns(uint)") == some unary
#guard unary.spell == "function(uint)returns(uint)"

/-- `function (address) external returns (bool)`: the flag is read, not guessed. -/
def callback : Part Unit := .fn true () (.cons (.elem .address) .nil) (.cons (.elem .bool) .nil)

#guard readSig "function(address)externalreturns(bool)" == some callback
#guard readSig "function(address)returns(bool)" != some callback
#guard callback.spell == "function(address)externalreturns(bool)"

-- No parameters and no returns.
#guard readSig "function()" == some (.fn false () .nil .nil)
#guard readSig "function()external" == some (.fn true () .nil .nil)

-- The marker rows of a local and of a state variable (`fnRow?`).
#guard ofShape [("#function(uint)returns(uint)", 0)] == some unary
#guard ofState [("x", 8), ("f#function(address)externalreturns(bool)", 0)] "f" == some callback
#guard ofState [("x", 8), ("f#function(address)externalreturns(bool)", 0)] "x" == none
#guard valueRows? "function(uint)returns(uint)" ==
  some (.uint, [("#function(uint)returns(uint)", 0)])

/-- An internal `view` function type, the keyword left out: the Source type
name and its exact type, in every environment. -/
example (E : Source.Env) (scope : Option String) (loc : DataLoc) :
    ∃ T, (unary.annotate ⟨some .view, false⟩).typeName Refs.none = some T ∧
      T = .fnType (.cons (.param (.elem u256) none none) .nil) none (some .view)
        (.cons (.param (.elem u256) none none) .nil) ∧
      T.ty E scope loc = some (.fn false [.int ⟨false, 256, by decide⟩]
        [.int ⟨false, 256, by decide⟩] (some .view)) :=
  ⟨_, rfl, rfl, sig_ty (RefsTyped.none E scope ⟨fun _ => none, fun _ _ => none⟩)
    (unary.annotate ⟨some .view, false⟩) loc rfl rfl rfl⟩

/-- An external one is `external` in Source, and of an external type. -/
example (E : Source.Env) (scope : Option String) (loc : DataLoc) :
    ∃ T, (callback.annotate ⟨none, false⟩).typeName Refs.none = some T ∧
      T = .fnType (.cons (.param (.elem .address) none none) .nil) (some .external) none
        (.cons (.param (.elem .bool) none none) .nil) ∧
      T.ty E scope loc = some (.fn true [.address false] [.bool] none) :=
  ⟨_, rfl, rfl, sig_ty (RefsTyped.none E scope ⟨fun _ => none, fun _ _ => none⟩)
    (callback.annotate ⟨none, false⟩) loc rfl rfl rfl⟩

/-! ## Order, nesting and widths -/

/-- `function (function (uint8) returns (bool), bytes4) returns (uint8, uint)`:
a nested signature first, each width kept, returns in order. -/
def nested : Part Unit :=
  .fn false ()
    (.cons (.fn false () (.cons (.elem u8) .nil) (.cons (.elem .bool) .nil))
      (.cons (.elem b4) .nil))
    (.cons (.elem u8) (.cons (.elem u256) .nil))

#guard readSig "function(function(uint8)returns(bool),bytes4)returns(uint8,uint)" == some nested
#guard nested.spell == "function(function(uint8)returns(bool),bytes4)returns(uint8,uint)"
#guard (readSig nested.spell).map Part.spell == some nested.spell

-- Parameter order matters.
#guard readSig "function(bytes4,function(uint8)returns(bool))returns(uint8,uint)" != some nested
-- `uint8` is not `uint`.
#guard readSig "function(uint8)returns(uint)" != some unary
-- A nested external signature keeps its own flag.
#guard readSig "function(function()external)" ==
  some (.fn false () (.cons (.fn true () .nil .nil) .nil) .nil)

/-- The nested type, the outer `pure` and the inner `view` (each function type
has its own mutability): the inner signature is a parameter's function type. -/
def nestedAnn : Part Ann :=
  .fn false ⟨some .pure, false⟩
    (.cons (.fn false ⟨some .view, true⟩ (.cons (.elem u8) .nil) (.cons (.elem .bool) .nil))
      (.cons (.elem b4) .nil))
    (.cons (.elem u8) (.cons (.elem u256) .nil))

example : nestedAnn.erase = nested := rfl

example (E : Source.Env) (scope : Option String) (loc : DataLoc) :
    ∃ T, nestedAnn.typeName Refs.none = some T ∧
      T.ty E scope loc = some (.fn false
        [.fn false [.int ⟨false, 8, by decide⟩] [.bool] (some .view), .fixedBytes 4 (by decide)]
        [.int ⟨false, 8, by decide⟩, .int ⟨false, 256, by decide⟩] (some .pure)) :=
  ⟨_, rfl, sig_ty (RefsTyped.none E scope ⟨fun _ => none, fun _ _ => none⟩) nestedAnn loc rfl
    rfl rfl⟩

/-- The reading of a nested spelling from `fnParts?`'s splits alone: no fuel,
no computation on the strings. -/
example {s inner : String} (bool : fnTy? "bool" = false)
    (parts : fnParts? s = some ([inner], [], true))
    (innerParts : fnParts? inner = some ([], ["bool"], false)) :
    Reads s (.fn true () (.cons (.fn false () .nil (.cons (leaf "bool") .nil)) .nil) .nil) :=
  .fn parts ⟨.fn innerParts trivial ⟨.leaf bool, trivial⟩, trivial⟩ trivial

/-- A narrow component's model width row is the width its Source type has
(`uint8`: the row `("", 8)`, the type `uint8`). -/
example {c : String} {T : Syn .typeName} (notFn : fnTy? c = false) (notAddress : c ≠ "address")
    (narrow : narrowTy? c = some (.uint, 8)) (notBytes : bytesTy? c = none)
    (h : Decode.typeNameB (.named c) = some T) :
    valueRows? c = some (.uint, [("", 8)]) ∧ (T = .elem u8 ∨ c = "bool" ∨ c = "uint" ∨
      c = "uint256" ∨ c = "int" ∨ c = "int256") := by
  refine ⟨valueRows_narrow notFn notAddress narrow, ?_⟩
  rcases typeNameB_named h with ⟨n, _, bytes, _⟩ | ⟨address, _⟩ | ⟨bool, _⟩ | ⟨uint, _⟩ |
    ⟨int, _⟩ | ⟨p, bits, e, narrow', elem, rfl⟩
  · rw [notBytes] at bytes
    cases bytes
  · exact absurd address notAddress
  · exact .inr (.inl bool)
  · exact .inr (.inr (uint.elim .inl fun h => .inr (.inl h)))
  · exact .inr (.inr (.inr (.inr int)))
  · rw [narrow] at narrow'
    cases narrow'
    cases elem
    exact .inl rfl

#guard valueRows? "uint8" == some (.uint, [("", 8)])
#guard leaf "uint8" == .elem u8
#guard leaf "bytes4" == .elem b4

/-! ## Locations -/

/-- `function (uint[] memory, S storage) returns (bytes memory)`: each
reference component with the location recorded for it. -/
def located : Part Unit :=
  .fn false () (.cons (.located "uint[]" .memory) (.cons (.located "S" .storage) .nil))
    (.cons (.located "bytes" .memory) .nil)

#guard readSig "function(uint[]memory,Sstorage)returns(bytesmemory)" == some located
#guard located.spell == "function(uint[]memory,Sstorage)returns(bytesmemory)"
#guard readSig "function(uint[]calldata)" ==
  some (.fn false () (.cons (.located "uint[]" .calldata) .nil) .nil)
-- A location is part of the reading.
#guard readSig "function(uint[]storage,Sstorage)returns(bytesmemory)" != some located

-- The suffix has no separator: a name ending in a location word reads as a located component (as
-- `canonFnTy` reads it).
#guard readSig "function(Tmemory)" == some (.fn false () (.cons (.located "T" .memory) .nil) .nil)

/-- A reference table for `uint[]` and `bytes`, standing in for a reference
decoder. -/
def refs : Refs where
  value _ := none
  located b :=
    if b = "uint[]" then some (.array (.elem u256) .none)
    else if b = "bytes" then some (.elem .bytes) else none

/-- Its component types. -/
def refTys : RefTys where
  value _ := none
  located b l :=
    if b = "uint[]" then some (.array l (.int ⟨false, 256, by decide⟩) none)
    else if b = "bytes" then some (.bytes l) else none

theorem refs_typed (E : Source.Env) (scope : Option String) : RefsTyped E scope refs refTys where
  value h := by cases h
  located {b l T τ} hT hτ := by
    simp only [refs] at hT
    simp only [refTys] at hτ
    split at hT
    · rename_i eq
      rw [if_pos eq] at hτ
      cases hT
      cases hτ
      rfl
    · split at hT
      · rename_i ne eq
        rw [if_neg ne, if_pos eq] at hτ
        cases hT
        cases hτ
        rfl
      · cases hT

/-- `function (uint[] memory) external returns (bytes memory)`, and with the
array in calldata. -/
def refSig (l : DataLoc) : Part Ann :=
  .fn true ⟨some .view, false⟩ (.cons (.located "uint[]" l) .nil)
    (.cons (.located "bytes" .memory) .nil)

/-- The recorded location is the parameter's and the type's. -/
example (E : Source.Env) (scope : Option String) (loc l : DataLoc) :
    ∃ T, (refSig l).typeName refs = some T ∧
      T = .fnType (.cons (.param (.array (.elem u256) .none) (some l) none) .nil)
        (some .external) (some .view) (.cons (.param (.elem .bytes) (some .memory) none) .nil) ∧
      T.ty E scope loc = some (.fn true [.array l (.int ⟨false, 256, by decide⟩) none]
        [.bytes .memory] (some .view)) :=
  ⟨_, rfl, rfl, sig_ty (refs_typed E scope) (refSig l) loc rfl rfl rfl⟩

/-- A component the table does not supply has no type name: `S` here. -/
example : (located.annotate ⟨none, false⟩).typeName refs = none := rfl

/-! ## Malformed markers -/

#guard readSig "uint" == none
#guard readSig "function(uint" == none
#guard readSig "function(uint)junk" == none
#guard readSig "function(uint)returns(uint" == none
#guard readSig "function(function(uint)" == none
#guard ofDecl (.array (.named "function()")) == none
#guard ofShape [("#address", 20)] == none

/-- A marker `fnParts?` refuses has no reading at any fuel, whatever its tail. -/
example {s : String} (isFn : fnTy? s = true) (parts : fnParts? s = none) (t : Part Unit) :
    ¬ Reads s t := Reads.malformed isFn parts t

/-- A nested malformed marker refuses the whole signature. -/
example {s inner : String} {t : Part Unit} (parts : fnParts? s = some ([inner], [], false))
    (innerFn : fnTy? inner = true) (innerParts : fnParts? inner = none) : ¬ Reads s t := by
  intro h
  rcases h.inv with ⟨notFn, _⟩ | ⟨ps, rs, ext, P, R, _, parts', params, _, _⟩
  · rw [fnTy_of_parts parts] at notFn
    cases notFn
  · rw [parts] at parts'
    cases parts'
    cases P with
    | nil => exact params
    | cons t ts => exact Reads.malformed innerFn innerParts t params.1

/-! ## Mutability is not retained -/

/-- `function (uint) pure returns (uint)` and `function (uint) view returns
(uint)`: one retained signature, one spelling, two Source function types. -/
theorem pure_view (E : Source.Env) (scope : Option String) (loc : DataLoc) :
    ∃ T T' : Syn .typeName,
      (unary.annotate (⟨some .pure, false⟩ : Ann)).typeName Refs.none = some T ∧
      (unary.annotate (⟨some .view, false⟩ : Ann)).typeName Refs.none = some T' ∧
      (unary.annotate (⟨some .pure, false⟩ : Ann)).erase = unary ∧
      (unary.annotate (⟨some .view, false⟩ : Ann)).erase = unary ∧
      (unary.annotate (⟨some .pure, false⟩ : Ann)).spell =
        (unary.annotate (⟨some .view, false⟩ : Ann)).spell ∧
      T.ty E scope loc = some (.fn false [.int ⟨false, 256, by decide⟩]
        [.int ⟨false, 256, by decide⟩] (some .pure)) ∧
      T'.ty E scope loc = some (.fn false [.int ⟨false, 256, by decide⟩]
        [.int ⟨false, 256, by decide⟩] (some .view)) ∧
      T.ty E scope loc ≠ T'.ty E scope loc := by
  have typed := RefsTyped.none E scope ⟨fun _ => none, fun _ _ => none⟩
  have p := sig_ty typed (unary.annotate (⟨some .pure, false⟩ : Ann)) loc rfl rfl rfl
  have v := sig_ty typed (unary.annotate (⟨some .view, false⟩ : Ann)) loc rfl rfl rfl
  refine ⟨_, _, rfl, rfl, rfl, rfl, ?_, p, v, ?_⟩
  · exact (mutability_ambiguous ⟨fun _ => none, fun _ _ => none⟩ ⟨some .pure, false⟩
      ⟨some .view, false⟩ (by decide)).2.1
  · rw [p, v]
    intro eq
    injection eq with eq
    injection eq with _ _ _ m
    cases m

#guard readSig ((unary.annotate (⟨some .pure, false⟩ : Ann)).spell) == some unary
#guard readSig ((unary.annotate (⟨some .payable, true⟩ : Ann)).spell) == some unary

/-- The `internal` keyword is not retained either, and changes no type. -/
example (E : Source.Env) (scope : Option String) (loc : DataLoc) :
    ∃ T T' : Syn .typeName,
      (unary.annotate (⟨none, false⟩ : Ann)).typeName Refs.none = some T ∧
      (unary.annotate (⟨none, true⟩ : Ann)).typeName Refs.none = some T' ∧ T ≠ T' ∧
      T.ty E scope loc = T'.ty E scope loc := by
  have typed := RefsTyped.none E scope ⟨fun _ => none, fun _ _ => none⟩
  refine ⟨_, _, rfl, rfl, ?_, ?_⟩
  · intro eq
    injection eq with _ vis
    cases vis
  · rw [sig_ty typed (unary.annotate (⟨none, false⟩ : Ann)) loc rfl rfl rfl,
      sig_ty typed (unary.annotate (⟨none, true⟩ : Ann)) loc rfl rfl rfl]

end Solidity.Examples.Lowering.Total.FunctionTypeDecode
