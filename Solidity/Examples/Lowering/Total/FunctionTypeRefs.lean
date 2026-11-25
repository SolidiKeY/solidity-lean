import Solidity.Correctness.Lowering.Total.FunctionTypeRefs

/-! Checks of the typed reference tables for retained function signatures. Struct and
`bytes` names are read by string functions the kernel does not unfold: lookups reaching
them are evaluated (`#guard`) and are hypotheses of the theorems. -/
namespace Solidity.Examples.Lowering.Total.FunctionTypeRefs

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.FunctionTypeRefs
open Solidity.Correctness.Lowering.Total.FunctionTypeDecode (Part Parts Ann readSig leaf)
open Solidity.Correctness.Lowering.Total.ReferenceDecode (Resolved RawRep rawType)
open Solidity.Source (Syn STy DataLoc)

/-- `struct Pair { uint a; uint8 b; }` of `C`, and its explicit resolution, nothing else. -/
def pairs : Contract := { vars := [], structs := [("Pair", "Pair{a:uint;b:uint8}")] }
def pairD : Source.DeclName := ⟨some "C", "Pair"⟩
def res : Resolution := fun s => if s = "Pair" then some pairD else none
theorem res_sound {E : Source.Env} (h : Resolved E (some "C") "Pair" pairD) :
    ∀ s d, res s = some d → Resolved E (some "C") s d := by
  intro s d eq
  unfold res at eq
  split at eq <;> cases eq
  rename_i hs; exact hs ▸ h
def U (bits : Nat) (h : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 := by decide) : STy :=
  .int ⟨false, bits, h⟩
def u8 : Source.Elem := .int false 8 (by decide)
def uints : RawTy := .array (.named "uint")
def nestedTy : RawTy := .array (.fixed (.named "uint8") 3)
def mapTy : RawTy := .mapping (.named "address") (.array (.named "Pair"))
/-- `uint[]` at two locations, `uint8[3][] calldata`, a storage mapping, `Pair memory`
twice, `Pair` with no location, and `bytes memory`, which `rawType` does not read. -/
def tbl : Table :=
  [⟨uints, some .memory⟩, ⟨uints, some .storage⟩, ⟨nestedTy, some .calldata⟩,
    ⟨mapTy, some .storage⟩, ⟨.named "Pair", some .memory⟩, ⟨.named "Pair", some .memory⟩,
    ⟨.named "Pair", none⟩, ⟨.named "bytes", some .memory⟩]
#guard (tbl.map Entry.key) == ["uint[]memory", "uint[]storage", "uint8[3][]calldata",
  "mapping(address=>Pair[])storage", "Pairmemory", "Pairmemory", "Pair", "bytesmemory"]
-- Every entry is the component the reader produces from its key, location kept.
#guard tbl.all fun e => leaf e.key == e.part.erase
example (e : Entry) : e.part.spell = e.key ∧ e.part.loc = e.loc := e.part_spell
-- One answer for the repeated `Pair memory`; `uint[]` only where it is recorded.
example : tbl.located "uint[]" .memory = some uints ∧ tbl.located "uint[]" .storage = some uints ∧
    tbl.located "uint[]" .calldata = none ∧ tbl.located "Pair" .memory = some (.named "Pair") ∧
    tbl.value "Pair" = some (.named "Pair") ∧ tbl.located "Pair" .storage = none := by decide
-- One base, a different Source type at each recorded location; nesting, length, width.
#guard (refTys pairs res tbl).located "uint[]" .memory == some (.array .memory (U 256) none) &&
  (refTys pairs res tbl).located "uint[]" .storage == some (.array .storage (U 256) none) &&
  (refTys pairs res tbl).located "uint[]" .calldata == none &&
  (refTys pairs res tbl).located "uint8[3][]" .calldata ==
    some (.array .calldata (.array .calldata (U 8) (some 3)) none)
-- A storage mapping with a struct value; the written struct at its location, `memory` with none.
#guard (refTys pairs res tbl).located (spell mapTy) .storage ==
    some (.mapping (.address false) (.array .storage (.struct .storage pairD) none)) &&
  (refTys pairs res tbl).located (spell mapTy) .memory == none &&
  (refTys pairs res tbl).located "Pair" .memory == some (.struct .memory pairD) &&
  (refTys pairs res tbl).value "Pair" == some (.struct .memory pairD)
-- Struct resolution is the caller's: without it the spelling stays, the type does not.
#guard ((refTys pairs (fun _ => none) tbl).located "Pair" .memory).isNone &&
  ((refs pairs tbl).located "Pair").isSome
def withEnum : Contract := { vars := [], enums := [("Color", ["Red", "Green"])] }
def maps : Table := [⟨.mapping (.named "uint") (.named "bool"), some .memory⟩,
  ⟨.mapping (.named "uint") (.named "bool"), some .storage⟩]
#guard match outstanding pairs tbl, outstanding withEnum [⟨.array (.named "Color"), some .memory⟩,
    ⟨.array (.named "function()"), some .memory⟩, ⟨uints, some .memory⟩] with
  | [(⟨.named "bytes", some .memory⟩, .unsupportedName "bytes")],
    [(_, .unsupportedName "Color"), (_, .unsupportedName "function()")] => true
  | _, _ => false
-- A mapping recorded twice: outstanding and untyped in `memory`, typed in `storage`.
#guard ((refs pairs tbl).located "bytes").isNone && (outstanding pairs maps).length == 1 &&
  (refTys pairs res maps).located "mapping(uint=>bool)" .memory == none &&
  (refTys pairs res maps).located "mapping(uint=>bool)" .storage == some (.mapping (U 256) .bool)
example {e : Entry} (m : e ∈ tbl) : (∃ t, rawType pairs (e.loc.getD .memory) e.ty = .ok t) ∨
    ∃ err, (e, err) ∈ outstanding pairs tbl := read_or_outstanding m
example {err} (h : rawType pairs .memory (.named "bytes") = .error err) :
    (refTys pairs res tbl).located "bytes" .memory = none := outstanding_untyped h (by decide)
/-- `uint[]` as an array and as a name so spelled: no answer, in either order. -/
def clash : Table := tbl ++ [⟨.named "uint[]", some .storage⟩]
example : clash.base "uint[]" = none ∧ clash.located "uint[]" .memory = none ∧
    clash.located "uint[]" .storage = none ∧ Table.base clash.reverse "uint[]" = none ∧
    clash.located "Pair" .memory = some (.named "Pair") := by decide
#guard ((refs pairs clash).located "uint[]").isNone &&
  (refTys pairs res clash).located "Pair" .memory == some (.struct .memory pairD)
example : clash.base (spell uints) = none := base_conflict (l := .memory) (l' := .storage)
  (T' := .named "uint[]") (by decide) (by decide) rfl (by decide)
/-- The type/location boundary: beside a name `Tmemory` the base `T` is not answered, at
`memory` or at `storage` (the reader would ask for `T` at `memory`); alone it is. -/
def boundary (l : DataLoc) : Table := [⟨.named "Tmemory", none⟩, ⟨.named "T", some l⟩]
example : (boundary .memory).value "Tmemory" = none ∧ (boundary .memory).base "T" = none ∧
    (boundary .storage).base "T" = none ∧
    Table.located [⟨.named "T", some .memory⟩] "T" .memory = some (.named "T") := by decide
#guard ((refs pairs (boundary .storage)).located "T").isNone
def one {α : Type} (c : Part α) : Parts α := .cons c .nil
def arrayPs : Parts Ann := .cons (.located "uint[]" .memory) (one (.elem u8))
def arrayRs : Parts Ann := one (.located "uint[]" .storage)
/-- `function (uint[] memory, uint8) external returns (uint[] storage)`: proved outright. -/
theorem arrays_ty (a : Ann) (E : Source.Env) (scope : Option String) (loc : DataLoc)
    (sound : ∀ s d, res s = some d → Resolved E scope s d) :
    ∃ T, (Part.fn true a arrayPs arrayRs).typeName (refs pairs tbl) = some T ∧
      T.ty E scope loc = some (.fn true [.array .memory (U 256) none, U 8]
        [.array .storage (U 256) none] a.mutability) :=
  ⟨_, rfl, (fnType_ty (C := pairs) (tbl := tbl) sound true a arrayPs arrayRs loc rfl rfl rfl).2⟩
def mixedPs : Parts Ann := .cons (.located "uint[]" .memory) (.cons (.elem u8)
  (.cons (.located (spell mapTy) .storage) (one (.located "Pair" .memory))))
def mixedRs : Parts Ann :=
  .cons (.located (spell nestedTy) .calldata) (one (.located "uint[]" .storage))
def mixedParamTys : List STy := [.array .memory (U 256) none, U 8,
  .mapping (.address false) (.array .storage (.struct .storage pairD) none), .struct .memory pairD]
def mixedRetTys : List STy :=
  [.array .calldata (.array .calldata (U 8) (some 3)) none, .array .storage (U 256) none]
-- The tree is the one read from the retained spelling; its lookups succeed.
#guard readSig "function(uint[]memory,uint8,mapping(address=>Pair[])storage,Pairmemory)externalreturns(uint8[3][]calldata,uint[]storage)" ==
  some (Part.fn true ⟨some .view, false⟩ mixedPs mixedRs).erase
#guard mixedPs.stys (refTys pairs res tbl) == some mixedParamTys &&
  mixedRs.stys (refTys pairs res tbl) == some mixedRetTys &&
  ((Part.fn true ⟨some .view, false⟩ mixedPs mixedRs).typeName (refs pairs tbl)).isSome
/-- That signature, once `Pair` resolves to `C.Pair`: exactly the function type of its
components at their recorded locations (the evaluated lookups are the hypotheses). -/
theorem mixed_ty {E : Source.Env} (h : Resolved E (some "C") "Pair" pairD) (a : Ann)
    (loc : DataLoc) {T : Syn .typeName} {P : Syn (.list .param)}
    (hT : (Part.fn true a mixedPs mixedRs).typeName (refs pairs tbl) = some T)
    (hP : mixedPs.params (refs pairs tbl) = some P)
    (hπ : mixedPs.stys (refTys pairs res tbl) = some mixedParamTys)
    (hρ : mixedRs.stys (refTys pairs res tbl) = some mixedRetTys) :
    T.ty E (some "C") loc = some (.fn true mixedParamTys mixedRetTys a.mutability) ∧
      P.tys E (some "C") .memory = some mixedParamTys :=
  ⟨(fnType_ty (res_sound h) true a mixedPs mixedRs loc hT hπ hρ).2,
    Parts.params_tys (refsTyped (res_sound h)) mixedPs hP hπ⟩
/-- A typed lookup is the retained entry, at its recorded location, and its represented type. -/
example {E : Source.Env} (h : Resolved E (some "C") "Pair" pairD) {τ τ' : STy}
    (hτ : (refTys pairs res tbl).located (spell mapTy) .storage = some τ)
    (hτ' : (refTys pairs res tbl).value "Pair" = some τ') :
    (∃ T, ⟨T, some .storage⟩ ∈ tbl ∧ RawRep pairs E (some "C") .storage T τ) ∧
      ∃ T, ⟨T, none⟩ ∈ tbl ∧ RawRep pairs E (some "C") .memory T τ' :=
  let ⟨T, _, ⟨m, _⟩, _, _, _, rep⟩ := located_rep (res_sound h) hτ
  let ⟨T', _, ⟨m', _⟩, _, _, _, rep'⟩ := value_rep (res_sound h) hτ'
  ⟨⟨T, m, rep⟩, T', m', rep'⟩

end Solidity.Examples.Lowering.Total.FunctionTypeRefs
