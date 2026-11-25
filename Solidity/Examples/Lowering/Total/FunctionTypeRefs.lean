import Solidity.Correctness.Lowering.Total.FunctionTypeRefs

/-! Checks of the typed reference tables for retained function signatures.
Struct and `bytes` leaf names are read by string functions the kernel does not
unfold, so lookups that reach them are evaluated checks (`#guard`) and the
theorems take them as hypotheses; a primitive-only signature is proved outright. -/
namespace Solidity.Examples.Lowering.Total.FunctionTypeRefs

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.FunctionTypeRefs
open Solidity.Correctness.Lowering.Total.FunctionTypeDecode (Part Parts Ann readSig leaf)
open Solidity.Correctness.Lowering.Total.ReferenceDecode (Resolved RawRep rawType)
open Solidity.Source (Syn STy DataLoc)

/-- `struct Pair { uint a; uint8 b; }` of the contract `C`. -/
def pairs : Contract := { vars := [], structs := [("Pair", "Pair{a:uint;b:uint8}")] }
def pairD : Source.DeclName := ⟨some "C", "Pair"⟩
/-- The explicit struct resolution: `Pair` is `C.Pair`, nothing else is answered. -/
def res : Resolution := fun s => if s = "Pair" then some pairD else none

theorem res_sound {E : Source.Env} (h : Resolved E (some "C") "Pair" pairD) :
    ∀ s d, res s = some d → Resolved E (some "C") s d := by
  intro s d eq
  unfold res at eq
  split at eq
  · rename_i hs
    cases eq
    exact hs ▸ h
  · cases eq

def U (bits : Nat) (h : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 := by decide) : STy :=
  .int ⟨false, bits, h⟩
def u8 : Source.Elem := .int false 8 (by decide)
def uints : RawTy := .array (.named "uint")
def nestedTy : RawTy := .array (.fixed (.named "uint8") 3)
def mapTy : RawTy := .mapping (.named "address") (.array (.named "Pair"))

/-- The retained components: `uint[]` at two locations, `uint8[3][] calldata`,
`mapping(address => Pair[]) storage`, `Pair memory` (twice), `Pair` with no
location, and `bytes memory`, which `rawType` does not read. -/
def tbl : Table :=
  [⟨uints, some .memory⟩, ⟨uints, some .storage⟩, ⟨nestedTy, some .calldata⟩,
    ⟨mapTy, some .storage⟩, ⟨.named "Pair", some .memory⟩, ⟨.named "Pair", some .memory⟩,
    ⟨.named "Pair", none⟩, ⟨.named "bytes", some .memory⟩]

/-! ## Spelling: exactly the reader's components -/

#guard spell nestedTy == "uint8[3][]" && spell mapTy == "mapping(address=>Pair[])"
#guard (tbl.map Entry.key) == ["uint[]memory", "uint[]storage", "uint8[3][]calldata",
  "mapping(address=>Pair[])storage", "Pairmemory", "Pairmemory", "Pair", "bytesmemory"]
-- Every entry is the component the reader produces from its key, location kept.
#guard tbl.all fun e => leaf e.key == e.part.erase
#guard readSig "function(uint[]memory,uint8,mapping(address=>Pair[])storage,Pairmemory)externalreturns(uint8[3][]calldata,uint[]storage)" ==
  some (.fn true ()
    (.cons (.located "uint[]" .memory) (.cons (.elem u8)
      (.cons (.located (spell mapTy) .storage) (.cons (.located "Pair" .memory) .nil))))
    (.cons (.located (spell nestedTy) .calldata) (.cons (.located "uint[]" .storage) .nil)))
example (e : Entry) : e.part.spell = e.key ∧ e.part.loc = e.loc := ⟨e.part_spell, e.part_loc⟩

/-! ## Lookups: retained entries, repeated ones once, locations distinct -/

example : tbl.located "uint[]" .memory = some uints ∧ tbl.located "uint[]" .storage = some uints ∧
    tbl.located "uint[]" .calldata = none := by decide
-- The repeated identical `Pair memory` is one answer; `Pair` without a location is another entry.
example : tbl.located "Pair" .memory = some (.named "Pair") ∧
    tbl.value "Pair" = some (.named "Pair") ∧ tbl.located "Pair" .storage = none := by decide
example : tbl.located (spell mapTy) .storage = some mapTy ∧
    tbl.located (spell nestedTy) .calldata = some nestedTy := by decide

-- One base, one type name, a different Source type at each recorded location.
#guard (refTys pairs res tbl).located "uint[]" .memory == some (.array .memory (U 256) none)
#guard (refTys pairs res tbl).located "uint[]" .storage == some (.array .storage (U 256) none)
#guard (refTys pairs res tbl).located "uint[]" .calldata == none
-- Nested arrays: nesting, length and width; a storage mapping with a struct value.
#guard (refTys pairs res tbl).located "uint8[3][]" .calldata ==
  some (.array .calldata (.array .calldata (U 8) (some 3)) none)
#guard (refTys pairs res tbl).located "mapping(address=>Pair[])" .storage ==
  some (.mapping (.address false) (.array .storage (.struct .storage pairD) none))
#guard (refTys pairs res tbl).located "mapping(address=>Pair[])" .memory == none
-- The written struct name, at its recorded location; in `memory` with none.
#guard (refTys pairs res tbl).located "Pair" .memory == some (.struct .memory pairD)
#guard (refTys pairs res tbl).value "Pair" == some (.struct .memory pairD)
#guard match (refs pairs tbl).located "Pair", (refs pairs tbl).located "mapping(address=>Pair[])" with
  | some (.userType ⟨"Pair", []⟩),
    some (.mapping (.elem .address _) none (.array (.userType ⟨"Pair", []⟩) .none) none) => true
  | _, _ => false
-- Struct resolution is the caller's: without it the spelling stays, the type does not.
#guard ((refTys pairs (fun _ => none) tbl).located "Pair" .memory).isNone &&
  ((refs pairs tbl).located "Pair").isSome &&
  (refTys pairs (fun _ => none) tbl).located "uint[]" .memory == some (.array .memory (U 256) none)

/-! ## Outstanding entries -/

#guard match outstanding pairs tbl with
  | [(⟨.named "bytes", some .memory⟩, .unsupportedName "bytes")] => true
  | _ => false
#guard ((refs pairs tbl).located "bytes").isNone && (tbl.located "bytes" .memory).isSome
-- A mapping recorded in `memory`, an enum and a function-type element: listed, with the reason.
def withEnum : Contract := { vars := [], enums := [("Color", ["Red", "Green"])] }
#guard match outstanding withEnum [⟨.mapping (.named "uint") (.named "uint"), some .memory⟩,
    ⟨.array (.named "Color"), some .memory⟩, ⟨.array (.named "function()"), some .memory⟩,
    ⟨uints, some .memory⟩] with
  | [(_, .mappingOutsideStorage .memory), (_, .unsupportedName "Color"),
      (_, .unsupportedName "function()")] => true
  | _ => false
example {e : Entry} (m : e ∈ tbl) :
    (∃ t, rawType pairs (e.loc.getD .memory) e.ty = .ok t) ∨ ∃ err, (e, err) ∈ outstanding pairs tbl :=
  read_or_outstanding m

/-! ## Conflicting entries are never chosen between -/

/-- `uint[]` as an array and as a name so spelled: no answer at either location. -/
def clash : Table := tbl ++ [⟨.named "uint[]", some .storage⟩]
example : clash.base "uint[]" = none ∧ clash.located "uint[]" .memory = none ∧
    clash.located "uint[]" .storage = none ∧ Table.located clash.reverse "uint[]" .memory = none ∧
    clash.located "Pair" .memory = some (.named "Pair") := by decide
#guard ((refs pairs clash).located "uint[]").isNone && ((refs pairs clash.reverse).located "uint[]").isNone
#guard (refTys pairs res clash).located "uint[]" .memory == none &&
  (refTys pairs res clash).located "Pair" .memory == some (.struct .memory pairD)
example {tbl : Table} {T T' : RawTy} {l l' : DataLoc} (m : ⟨T, some l⟩ ∈ tbl)
    (m' : ⟨T', some l'⟩ ∈ tbl) (sp : spell T' = spell T) (ne : T ≠ T') :
    tbl.base (spell T) = none := base_conflict m m' sp ne

/-- The type/location boundary: a name `Tmemory` and `T` at `memory` are spelled
alike. Each alone is answered; together neither is. -/
def boundary : Table := [⟨.named "Tmemory", none⟩, ⟨.named "T", some .memory⟩]
example : boundary.value "Tmemory" = none ∧ boundary.located "T" .memory = none ∧
    Table.value [⟨.named "Tmemory", none⟩] "Tmemory" = some (.named "Tmemory") ∧
    Table.located [⟨.named "T", some .memory⟩] "T" .memory = some (.named "T") := by decide

/-! ## Exact function types through the existing interfaces -/

def one {α : Type} (c : Part α) : Parts α := .cons c .nil

def arrayPs : Parts Ann := .cons (.located "uint[]" .memory) (one (.elem u8))
def arrayRs : Parts Ann := one (.located "uint[]" .storage)

/-- `function (uint[] memory, uint8) external returns (uint[] storage)`, at any
annotation: proved outright, the two locations of `uint[]` kept apart. -/
theorem arrays_ty (a : Ann) (E : Source.Env) (scope : Option String) (loc : DataLoc)
    (sound : ∀ s d, res s = some d → Resolved E scope s d) :
    ∃ T, (Part.fn true a arrayPs arrayRs).typeName (refs pairs tbl) = some T ∧
      T.ty E scope loc = some (.fn true [.array .memory (U 256) none, U 8]
        [.array .storage (U 256) none] a.mutability) :=
  ⟨_, rfl, (fnType_ty (C := pairs) (tbl := tbl) sound true a arrayPs arrayRs loc rfl rfl rfl).2⟩

def mixedPs : Parts Ann :=
  .cons (.located "uint[]" .memory) (.cons (.elem u8)
    (.cons (.located (spell mapTy) .storage) (one (.located "Pair" .memory))))
def mixedRs : Parts Ann :=
  .cons (.located (spell nestedTy) .calldata) (one (.located "uint[]" .storage))
def mixedParamTys : List STy :=
  [.array .memory (U 256) none, U 8,
    .mapping (.address false) (.array .storage (.struct .storage pairD) none),
    .struct .memory pairD]
def mixedRetTys : List STy :=
  [.array .calldata (.array .calldata (U 8) (some 3)) none, .array .storage (U 256) none]

#guard mixedPs.stys (refTys pairs res tbl) == some mixedParamTys
#guard mixedRs.stys (refTys pairs res tbl) == some mixedRetTys
#guard ((Part.fn true ⟨some .view, false⟩ mixedPs mixedRs).typeName (refs pairs tbl)).isSome

/-- The signature read above, `view`: once `Pair` resolves to `C.Pair`, its
type name denotes exactly the function type of its components, each at its
recorded location (the lookups, evaluated above, are the hypotheses). -/
theorem mixed_ty {E : Source.Env} (h : Resolved E (some "C") "Pair" pairD) (a : Ann)
    (loc : DataLoc) {T : Syn .typeName}
    (hT : (Part.fn true a mixedPs mixedRs).typeName (refs pairs tbl) = some T)
    (hπ : mixedPs.stys (refTys pairs res tbl) = some mixedParamTys)
    (hρ : mixedRs.stys (refTys pairs res tbl) = some mixedRetTys) :
    T.ty E (some "C") loc = some (.fn true mixedParamTys mixedRetTys a.mutability) :=
  (fnType_ty (res_sound h) true a mixedPs mixedRs loc hT hπ hρ).2

/-- A typed lookup is the retained entry, at its recorded location, and its
represented type: here the storage mapping. -/
example {E : Source.Env} (h : Resolved E (some "C") "Pair" pairD) {τ : STy}
    (hτ : (refTys pairs res tbl).located (spell mapTy) .storage = some τ) :
    ∃ T t, ⟨T, some .storage⟩ ∈ tbl ∧ spell T = spell mapTy ∧
      (refs pairs tbl).located (spell mapTy) = some t ∧
      t.tys E (some "C") .storage = some [τ] ∧ RawRep pairs E (some "C") .storage T τ :=
  let ⟨T, t, ⟨m, sp, _⟩, ht, _, typed, rep⟩ := located_rep (res_sound h) hτ
  ⟨T, t, m, sp, ht, typed, rep⟩

/-- Parameters alone, and one component, through the other two interfaces. -/
example {E : Source.Env} (h : Resolved E (some "C") "Pair" pairD) {P : Syn (.list .param)}
    (hP : mixedPs.params (refs pairs tbl) = some P)
    (hπ : mixedPs.stys (refTys pairs res tbl) = some mixedParamTys) :
    P.tys E (some "C") .memory = some mixedParamTys := params_tys (res_sound h) mixedPs hP hπ
example {E : Source.Env} (h : Resolved E (some "C") "Pair" pairD) {T : Syn .typeName} {τ : STy}
    (hT : (Part.located "Pair" .memory : Part Ann).typeName (refs pairs tbl) = some T)
    (hτ : (Part.located "Pair" .memory : Part Ann).sty (refTys pairs res tbl) = some τ) :
    T.tys E (some "C") .memory = some [τ] := part_tys (res_sound h) _ hT hτ

end Solidity.Examples.Lowering.Total.FunctionTypeRefs
