import Solidity.Correctness.Lowering.Total.FunctionTypeDecode

/-! Checks of the retained function-type signature component: concrete spellings
by `#guard` (`fnParts?` does not reduce in the kernel), the rest proved on trees. -/
namespace Solidity.Examples.Lowering.Total.FunctionTypeDecode

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.FunctionTypeDecode
open Solidity.Source (Syn STy DataLoc)

def u256 : Source.Elem := .int false 256 (by decide)
def u8 : Source.Elem := .int false 8 (by decide)
def b4 : Source.Elem := .fixedBytes 4 (by decide)
def one {α : Type} (c : Part α) : Parts α := .cons c .nil
def U (bits : Nat) (h : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 := by decide) : STy :=
  .int ⟨false, bits, h⟩

/-! ## Internal and external, marker rows -/

#guard readSig "function(uint)returns(uint)" == some (.fn false () (one (.elem u256)) (one (.elem u256)))
#guard ofDecl (.named "function(uint256)returns(uint)") == readSig "function(uint)returns(uint)"
#guard readSig "function(address)externalreturns(bool)" == some (.fn true () (one (.elem .address)) (one (.elem .bool)))
#guard ofRows [("#function()external", 0)] "" == some (.fn true () .nil .nil)
#guard ofRows [("x", 8), ("f#function()external", 0)] "f" == some (.fn true () .nil .nil)
#guard valueRows? "function()external" == some (.uint, [("#function()external", 0)])

/-! ## Order, nesting and widths -/

/-- `function (function (uint8) returns (bool), bytes4) returns (uint8, uint)`. -/
def nestedPs (inner : Ann) : Parts Ann :=
  .cons (.fn false inner (one (.elem u8)) (one (.elem .bool))) (one (.elem b4))
def nestedRs : Parts Ann := .cons (.elem u8) (one (.elem u256))
def nested (inner outer : Ann) : Part Ann := .fn false outer (nestedPs inner) nestedRs

#guard readSig "function(function(uint8)returns(bool),bytes4)returns(uint8,uint)" == some (nested ⟨none, false⟩ ⟨none, false⟩).erase
#guard (nested ⟨some .view, true⟩ ⟨some .pure, false⟩).spell == "function(function(uint8)returns(bool),bytes4)returns(uint8,uint)"
#guard readSig "function(function()external)" == some (.fn false () (one (.fn true () .nil .nil)) .nil)
#guard leaf "uint8" == .elem u8 && leaf "bytes4" == .elem b4 && leaf "uint256" == .elem u256

/-- The reader's equations from `fnParts?`'s split alone: flag, order, marker row. -/
example (n : Nat) {s c : String} (notFn : fnTy? c = false)
    (parts : fnParts? s = some ([c, c], [], true)) :
    part (n + 2) s = some (.fn true () (.cons (leaf c) (one (leaf c))) .nil) ∧
      valueRows? s = some (.uint, [("#" ++ s, 0)]) :=
  ⟨by simp only [part_fn _ parts, part_leaf _ notFn, partsWith, one, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some, Option.map_some], valueRows_fn (fnTy_of_parts parts)⟩
example {s : String} (isFn : fnTy? s = true) (parts : fnParts? s = none) (n : Nat) :
    part n s = none := part_malformed isFn parts n
example {c : String} {e : Source.Elem} (h : leaf c = .elem e) :
    Decode.typeNameB (.named c) = some (.elem e) := leaf_elem h

/-! ## Locations, and a reference table standing in for a reference decoder -/

#guard readSig "function(uint[]memory,Sstorage)returns(bytescalldata)" ==
  some (.fn false () (.cons (.located "uint[]" .memory) (one (.located "S" .storage)))
    (one (.located "bytes" .calldata)))
-- No separator: a name ending in a location word reads as located, the base possibly empty.
#guard leaf "Tmemory" == .located "T" .memory && leaf "memory" == .located "" .memory

def refs : Refs where
  value _ := none
  located b := if b = "uint[]" then some (.array (.elem u256) .none) else none

def refTys : RefTys where
  value _ := none
  located b l := if b = "uint[]" then some (.array l (U 256) none) else none

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
    · cases hT

def arrayPs (l : DataLoc) : Parts Ann := .cons (.located "uint[]" l) (one (.elem u8))
def uints : Parts Ann := one (.elem u256)

/-- `function (uint[] l, uint8) external returns (uint)` at any mutability:
the recorded location is the parameter's and the type's, widths are kept, and
the Source type is exact at every location. -/
theorem located_ty (a : Ann) (l : DataLoc) (E : Source.Env) (scope : Option String)
    (loc : DataLoc) :
    ∃ T, (Part.fn true a (arrayPs l) uints).typeName refs = some T ∧
      T = .fnType (.cons (.param (.array (.elem u256) .none) (some l) none)
        (.cons (.param (.elem u8) none none) .nil)) (some .external) a.mutability
        (.cons (.param (.elem u256) none none) .nil) ∧
      T.ty E scope loc = some (.fn true [.array l (U 256) none, U 8] [U 256] a.mutability) :=
  ⟨_, rfl, rfl, (fnType_ty (refs_typed E scope) true a (arrayPs l) uints loc rfl rfl rfl).2⟩

/-- A nested signature: each function type has its own mutability. -/
example (E : Source.Env) (scope : Option String) (loc : DataLoc) :
    ∃ T, (nested ⟨some .view, true⟩ ⟨some .pure, false⟩).typeName refs = some T ∧
      T.ty E scope loc = some (.fn false [.fn false [U 8] [.bool] (some .view),
        .fixedBytes 4 (by decide)] [U 8, U 256] (some .pure)) :=
  ⟨_, rfl, (fnType_ty (refs_typed E scope) false ⟨some .pure, false⟩ (nestedPs ⟨some .view, true⟩)
    nestedRs loc rfl rfl rfl).2⟩

/-! ## Markers `fnParts?` refuses, and components it does not validate -/

#guard readSig "uint" == none && readSig "function(uint" == none
#guard readSig "function(uint)junk" == none && readSig "function(uint)returns(uint" == none
#guard readSig "function(function(uint)" == none && ofDecl (.array (.named "function()")) == none
-- Refused function-type arrays, empty `returns()`, unvalidated names, `uint256` respelled.
#guard readSig "function(function(uint)[]memory)" == none
#guard readSig "function(uint)returns()" == readSig "function(uint)"
#guard readSig "function(uint[],?)" == some (.fn false () (.cons (.named "uint[]") (one (.named "?"))) .nil)
#guard (readSig "function(uint256)").map Part.spell == some "function(uint)"

/-! ## Mutability is not retained -/

/-- `function (uint) pure returns (uint)` and `function (uint) view returns
(uint)`: one retained signature and spelling, two Source function types. -/
theorem pure_view (E : Source.Env) (scope : Option String) (loc : DataLoc) :
    let t (m : Source.Mutability) : Part Ann := .fn false ⟨some m, false⟩ uints uints
    ∃ T T' : Syn .typeName, (t .pure).typeName refs = some T ∧ (t .view).typeName refs = some T' ∧
      (t .pure).erase = (t .view).erase ∧ (t .pure).spell = (t .view).spell ∧
      T.ty E scope loc = some (.fn false [U 256] [U 256] (some .pure)) ∧
      T'.ty E scope loc = some (.fn false [U 256] [U 256] (some .view)) ∧
      T.ty E scope loc ≠ T'.ty E scope loc := by
  intro t
  have p := (fnType_ty (refs_typed E scope) false ⟨some .pure, false⟩ uints uints loc rfl rfl rfl).2
  have v := (fnType_ty (refs_typed E scope) false ⟨some .view, false⟩ uints uints loc rfl rfl rfl).2
  have amb := mutability_ambiguous refTys false uints uints
    (a := ⟨some .pure, false⟩) (b := ⟨some .view, false⟩) (by decide)
  refine ⟨_, _, rfl, rfl, amb.1, amb.2.1, p, v, ?_⟩
  rw [p, v]
  exact fun eq => amb.2.2 _ _ rfl rfl (Option.some.inj eq)

end Solidity.Examples.Lowering.Total.FunctionTypeDecode
