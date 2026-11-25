import Solidity.Correctness.Lowering.Total.RawTypeAgreement

/-! Retained types as read against their model types: nested resolved struct
references, narrow and bytes metadata, arrays and storage mappings; conflicting rows,
ambiguous names, invalid locations, an enum named like an elementary type.

The readers test names with `String` operations the kernel does not reduce, so a
reading of a concrete type is a `#guard` and the hypothesis of the example below it. -/
namespace Solidity.Examples.Lowering.Total.RawTypeAgreement
open Solidity.Correctness.Lowering.Total Source
open RawTypeAgreement
open StructDecode (decode Free)
open StructTableAgreement (Closed Agrees)
open ReferenceDecode (Resolved written? rawType rawElem RawRep Rep readTy spellType lenLit)
open StructRows (Agree)
open Solidity.Semantics (lookupBy)

/-- Contract `K` holding the decoded parts `ps`, after a file-level declaration. -/
def unit (top : Syn (.part true)) (ps : Syn (.list (.part false))) : Syn .unit :=
  .unit (.cons (.topPart top) (.cons (.contract false "K" .none .nil ps) .nil))
def surround (top : Decl) (ps : Syn (.list (.part false))) : List Decl :=
  [top, ⟨.contract, "K", none, true, .contract false "K" .none .nil ps⟩]
/-- The decoded parts, kept opaque to elaboration; facts about them are kernel-checked. -/
@[irreducible] def parts (C : Contract) : Syn (.list (.part false)) :=
  match decode C with | .ok ps => ps | .error _ => .nil
theorem parts_ok {C : Contract} (h : (decode C).toBool = true) : decode C = .ok (parts C) := by
  unfold parts; cases hd : decode C <;> simp_all [Except.toBool]

/-- `struct Inner { uint8 a; address b; }` and `struct Outer { Inner[] xs; }`. -/
def inner : Name := "Inner{a:uint8;b:address}"
def C : Contract :=
  { vars := [], structs := [("Outer", "Outer{xs:Inner{a:uint8;b:address}[]}"), ("Inner", inner)] }
/-- A file-level struct also named `Inner`, shadowed from `K`. -/
def fileInner : Decl :=
  ⟨.struct, "Inner", none, true, .struct "Inner" (.structMember (.elem .bool) "z") .nil⟩
def u : Syn .unit := unit fileInner.node (parts C)
theorem decoded : decode C = .ok (parts C) := parts_ok (by decide +kernel)
theorem hE : u.env.decls = surround fileInner (parts C) ++ (parts C).collect (some "K") ++ [] := rfl
theorem free : Free C "K" (surround fileInner (parts C) ++ []) := by
  intro d md sc
  simp only [surround, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at md
  rcases md with rfl | rfl <;> cases sc
theorem closed : Closed C := by decide +kernel
theorem plain (R : RawTy) : Plain C R := fun _ _ _ => rfl
theorem innerElem : rawElem "Inner" = none :=
  rawElem_none_of_hd (by decide) (by decide) (by decide) (by decide)

/-! ## A storage mapping to nested arrays of a resolved struct -/

/-- `mapping(address => Inner[2][])`. -/
def R1 : RawTy := .mapping (.named "address") (.array (.fixed (.named "Inner") 2))
def T1 : Ty := .ref (.mapping .uint (.ref (.array (.ref (.fixed (.ref (.struct inner)) 2)))))
def t1 : Syn .typeName := .mapping (.elem .address (by decide)) none
  (.array (.array (.userType ⟨"Inner", []⟩) (.some (lenLit 2))) .none) none
theorem tabled1 : Tabled C R1 := fun s ms _ _ => by
  simp only [R1, ReferenceDecode.rawNames, List.mem_singleton] at ms
  subst ms; decide +kernel

#guard (elabTyW C R1).toOption == some (T1, [("{}#address", 20)])
#guard match rawType C .storage R1 with
  | .ok (.mapping (.elem .address _) none
      (.array (.array (.userType ⟨"Inner", []⟩) (.some _)) .none) none) => true
  | _ => false
/-- The binder `m` among the rows of `n` and `z`: the key an `address` from the marker
row `m{}#address`, the value the declaration `K.Inner` generated for the table, not the
file-level `Inner`. -/
example (raw : rawType C .storage R1 = .ok t1) (el : elabTyW C R1 = .ok (T1, [("{}#address", 20)])) :
    Rep C [("n", 8), ("m{}#address", 20), ("z#bytes", 4)] u.env (some "K") "m" .storage T1
      (.mapping (.address false)
        (.array .storage (.array .storage (.struct .storage ⟨some "K", "Inner"⟩) (some 2)) none)) := by
  obtain ⟨τ, typed, -, rep⟩ := rawType_agrees_below decoded hE free closed raw el (plain _) tabled1
    (key := "m") (before := [("n", 8)]) (after := [("z#bytes", 4)]) (by decide +kernel)
  have eq : t1.tys u.env (some "K") .storage = some [.mapping (.address false)
      (.array .storage (.array .storage (.struct .storage ⟨some "K", "Inner"⟩) (some 2)) none)] := by
    decide +kernel
  rw [eq] at typed; cases typed; exact rep
/-- The struct leaf: `elabTyW`'s table, its one written name, and the table agreement
(the generated declaration, its identity, its fields). -/
example (raw : rawType C .storage R1 = .ok t1) :
    ∃ table, C.structName? "Inner" = some table ∧
      elabTyW C (.named "Inner") = .ok (.ref (.struct table), []) ∧
      written? C table = some "Inner" ∧ Agrees C u.env "K" "Inner" table :=
  leaf_agrees decoded hE free closed raw tabled1 (by simp [R1, ReferenceDecode.rawNames]) innerElem
example : u.env.structFields ⟨some "K", "Inner"⟩ .storage =
    some [("a", .int ⟨false, 8, by decide⟩), ("b", .address false)] := by decide +kernel

/-! ## Narrow and bytes metadata -/

theorem tabledElem {R : RawTy} {s : String} (names : ReferenceDecode.rawNames R = [s])
    (no : C.structName? s = none) : Tabled C R := fun s' ms _ st => by
  rw [names, List.mem_singleton] at ms; subst ms; rw [no] at st; cases st

/-- `uint8[]` in memory: the element width from the row `xs[]`. -/
def R2 : RawTy := .array (.named "uint8")
#guard (elabTyW C R2).toOption == some (.ref (.array .uint), [("[]", 8)])
#guard match rawType C .memory R2 with | .ok (.array (.elem (.int false 8 _)) .none) => true | _ => false
example (raw : rawType C .memory R2 = .ok (.array (.elem (.int false 8 (by decide))) .none))
    (el : elabTyW C R2 = .ok (.ref (.array .uint), [("[]", 8)])) :
    Rep C [("xs[]", 8)] u.env (some "K") "xs" .memory (.ref (.array .uint))
      (.array .memory (.int ⟨false, 8, by decide⟩) none) := by
  obtain ⟨τ, typed, -, rep⟩ := rawType_agrees_below decoded hE free closed raw el (plain _)
    (tabledElem rfl (by decide +kernel)) (key := "xs") (before := []) (after := []) (by decide)
  cases typed; exact rep

/-- `mapping(uint8 => bytes4[3])`: the key path `m{}`, the value path `m[][]` with its
width and `#bytes` marker. -/
def R3 : RawTy := .mapping (.named "uint8") (.fixed (.named "bytes4") 3)
def T3 : Ty := .ref (.mapping .uint (.ref (.fixed .uint 3)))
def t3 : Syn .typeName := .mapping (.elem (.int false 8 (by decide)) (by decide)) none
  (.array (.elem (.fixedBytes 4 (by decide))) (.some (lenLit 3))) none
#guard (elabTyW C R3).toOption == some (T3, [("{}", 8), ("[][]", 32), ("[][]#bytes", 4)])
#guard match rawType C .storage R3 with
  | .ok (.mapping (.elem (.int false 8 _) _) none (.array (.elem (.fixedBytes 4 _)) (.some _)) none) =>
    true
  | _ => false
example (raw : rawType C .storage R3 = .ok t3)
    (el : elabTyW C R3 = .ok (T3, [("{}", 8), ("[][]", 32), ("[][]#bytes", 4)])) :
    Rep C [("m{}", 8), ("m[][]", 32), ("m[][]#bytes", 4), ("mm", 16)] u.env (some "K") "m" .storage T3
      (.mapping (.int ⟨false, 8, by decide⟩) (.array .storage (.fixedBytes 4 (by decide)) (some 3))) := by
  obtain ⟨τ, typed, -, rep⟩ := rawType_agrees_below decoded hE free closed raw el (plain _)
    (tabledElem rfl (by decide +kernel)) (key := "m") (before := []) (after := [("mm", 16)])
    (by decide +kernel)
  cases typed; exact rep

/-- `bytes1[]` is represented, though `spellType` cannot spell its model type: the rows
are those of `bytes`, which `rawType` does not read. -/
def R4 : RawTy := .array (.named "bytes1")
#guard (elabTyW C R4).toOption == some (.ref (.array .uint), [("[]", 8), ("[]#bytes", 1)])
#guard (elabTyW C (.named "bytes")).toOption == (elabTyW C R4).toOption
#guard match rawType C .memory (.named "bytes") with | .error (.unsupportedName _) => true | _ => false
example (raw : rawType C .memory R4 = .ok (.array (.elem (.fixedBytes 1 (by decide))) .none))
    (el : elabTyW C R4 = .ok (.ref (.array .uint), [("[]", 8), ("[]#bytes", 1)])) :
    Rep C [("b[]", 8), ("b[]#bytes", 1)] u.env (some "K") "b" .memory (.ref (.array .uint))
      (.array .memory (.fixedBytes 1 (by decide)) none) := by
  obtain ⟨τ, typed, -, rep⟩ := rawType_agrees_below decoded hE free closed raw el (plain _)
    (tabledElem rfl (by decide +kernel)) (key := "b") (before := []) (after := []) (by decide)
  cases typed; exact rep
example : spellType C [("b[]", 8), ("b[]#bytes", 1)] "b" .memory (.ref (.array .uint)) =
    .error (.erasedBytes "b") := rfl

/-! ## Conflicting rows -/

/-- An earlier row at the element key: the rows are not the generated ones there, and
the model type is not represented by `uint8[]` (the table spells `uint16[]`). -/
example : ¬ Agree (readTy "xs" (.ref (.array .uint))) (rebase "xs" [("[]", 8)])
    [("xs[]", 16), ("xs[]", 8)] := fun h => by
  have := h "xs[]" (by decide +kernel); revert this; decide +kernel
example {E : Env} {scope : Option String} : ¬ Rep C [("xs[]", 16), ("xs[]", 8)] E scope "xs" .memory
    (.ref (.array .uint)) (.array .memory (.int ⟨false, 8, by decide⟩) none) := fun r => by
  cases r with
  | array r =>
    obtain ⟨e, he, eq⟩ := Rep.prim_elem r
    have : Decode.elemB [("xs[]", 16), ("xs[]", 8)] ("xs" ++ "[]") .uint =
        some (.int false 16 (by decide)) := by decide +kernel
    rw [this] at he; cases he; cases eq

/-! ## Ambiguous names -/

/-- Two names for one table: no written name, so no struct leaf is `Keyed` and the
table is represented by no Source type. -/
def A : Contract := { vars := [], structs := [("I", inner), ("J", inner)] }
example : written? A inner = none ∧ ¬ Keyed A "I" ∧ ¬ Keyed A "J" :=
  ⟨rfl, by decide +kernel, by decide +kernel⟩
example {E : Env} {scope : Option String} {key : Name} {loc : DataLoc} {τ : STy} :
    ¬ Rep A [] E scope key loc (.ref (.struct inner)) τ := unwritten_no_rep rfl
/-- A name keyed twice is not `Keyed` either; `StructTableAgreement.ambiguous` leaves
it unresolved. -/
def B : Contract := { vars := [], structs := [("I", inner), ("I", "Inner{c:bool}")] }
example : ¬ Keyed B "I" := by decide +kernel

/-! ## Invalid locations -/

-- A mapping in memory: read by `elabTyW`, not spelled.
#guard (elabTyW C R1).toOption.isSome
example : ∃ err, rawType C .memory R1 = .error err := mapping_outside _ _ (by decide)
-- A key that is not an elementary name (`string`) is not spelled either.
#guard (elabTyW C (.mapping (.named "string") (.named "uint"))).toOption.isSome
#guard match rawType C .storage (.mapping (.named "string") (.named "uint")) with
  | .error (.unsupportedKey _) => true | _ => false

/-! ## An enum named like an elementary type -/

/-- `elabTyW` reads the enum (a `uint` marked `#enum`), `rawType` the `bool`: outside
`Plain`, and the generated rows do not represent the enum's `uint` by `bool`. -/
def W : Contract := { vars := [], enums := [("bool", ["Off", "On"])] }
#guard (elabTyW W (.named "bool")).toOption == some (.uint, [("#enum", 1)])
#guard match rawType W .memory (.named "bool") with | .ok (.elem .bool) => true | _ => false
example : ¬ Plain W (.named "bool") := fun p => by
  have := p "bool" (by simp [names]) (by rw [rawElem_bool]; rfl)
  revert this; decide
example {E : Env} {scope : Option String} :
    ¬ Rep W (rebase "x" [("#enum", 1)]) E scope "x" .memory (.prim .uint) .bool := fun r => by
  obtain ⟨e, he, eq⟩ := Rep.prim_elem r
  have : Decode.elemB (rebase "x" [("#enum", 1)]) "x" .uint = some (.int false 256 (by decide)) := by
    decide +kernel
  rw [this] at he; cases he; cases eq

end Solidity.Examples.Lowering.Total.RawTypeAgreement

/-- info: 'Solidity.Correctness.Lowering.Total.RawTypeAgreement.rawType_agrees_below' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Correctness.Lowering.Total.RawTypeAgreement.rawType_agrees_below
/-- info: 'Solidity.Correctness.Lowering.Total.RawTypeAgreement.leaf_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Correctness.Lowering.Total.RawTypeAgreement.leaf_agrees
