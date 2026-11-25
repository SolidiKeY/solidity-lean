import Solidity.Correctness.Lowering.Total.RawTypeAgreement
import Solidity.Examples.Lowering.Total.StructTableAgreement

/-! Retained types as read against their model types, over the contract `C` of the
`StructTableAgreement` examples (`Outer`, `Inner`; the generated `Inner` shadows a file-level
one): a storage mapping to nested arrays of a resolved struct, narrow and bytes metadata;
conflicting rows, ambiguous names, invalid locations, an enum named like an elementary type.
The readers' `String` tests do not reduce in the kernel, so the reading of a concrete type is a
`#guard` and the hypothesis of the example below it. -/
namespace Solidity.Examples.Lowering.Total.RawTypeAgreement
open Solidity.Correctness.Lowering.Total Source RawTypeAgreement
open Solidity.Examples.Lowering.Total.StructTableAgreement (C u decoded hE free closed inner)
open ReferenceDecode (written? rawType rawElem rawNames Rep readTy spellType lenLit)
open Solidity.Semantics (lookupBy)

theorem plain (R : RawTy) : Plain C R := fun _ _ _ => rfl
theorem tabled {R : RawTy} {s : String} (names : rawNames R = [s])
    (ok : (C.structName? s).isSome → Keyed C s) : Tabled C R := fun s' ms _ st => by
  rw [names, List.mem_singleton] at ms; subst ms; exact ok st

/-- `mapping(address => Inner[2][])`. -/
def R1 : RawTy := .mapping (.named "address") (.array (.fixed (.named "Inner") 2))
def T1 : Ty := .ref (.mapping .uint (.ref (.array (.ref (.fixed (.ref (.struct inner)) 2)))))
def t1 : Syn .typeName := .mapping (.elem .address (by decide)) none
  (.array (.array (.userType ⟨"Inner", []⟩) (.some (lenLit 2))) .none) none
theorem tabled1 : Tabled C R1 := tabled rfl fun _ => by decide +kernel
#guard (elabTyW C R1).toOption == some (T1, [("{}#address", 20)])
#guard match rawType C .storage R1 with
  | .ok (.mapping (.elem .address _) none (.array (.array (.userType ⟨"Inner", []⟩) (.some _)) .none)
      none) => true
  | _ => false
/-- The binder `m` among the rows of `n` and `z`: the key an `address` from the row
`m{}#address`, the value the declaration `K.Inner` generated for the table. -/
example (raw : rawType C .storage R1 = .ok t1) (el : elabTyW C R1 = .ok (T1, [("{}#address", 20)])) :
    Rep C [("n", 8), ("m{}#address", 20), ("z#bytes", 4)] u.env (some "K") "m" .storage T1
      (.mapping (.address false)
        (.array .storage (.array .storage (.struct .storage ⟨some "K", "Inner"⟩) (some 2)) none)) := by
  obtain ⟨τ, typed, -, rep⟩ := rawType_agrees decoded hE free closed raw el (plain _) tabled1
    (key := "m") (agree_surround (pre := [("n", 8)]) (post := [("z#bytes", 4)]) (by decide +kernel))
  have eq : t1.tys u.env (some "K") .storage = some [.mapping (.address false) (.array .storage
    (.array .storage (.struct .storage ⟨some "K", "Inner"⟩) (some 2)) none)] := by decide +kernel
  rw [eq] at typed; cases typed; exact rep
/-- The struct leaf: `elabTyW`'s table, its one written name, the table agreement. -/
example (raw : rawType C .storage R1 = .ok t1) (he : rawElem "Inner" = none) :
    ∃ table, C.structName? "Inner" = some table ∧ elabTyW C (.named "Inner") =
      .ok (.ref (.struct table), []) ∧ written? C table = some "Inner" ∧
      StructTableAgreement.Agrees C u.env "K" "Inner" table :=
  leaf_agrees decoded hE free closed raw tabled1 (by simp [R1, rawNames]) he

/-- `mapping(uint8 => bytes1[])`: the key path `m{}`, the value path `m[][]` with its width and
`#bytes` marker. Represented, though `spellType` erases `bytes1[]` (the rows of `bytes`). -/
def R2 : RawTy := .mapping (.named "uint8") (.array (.named "bytes1"))
def T2 : Ty := .ref (.mapping .uint (.ref (.array .uint)))
def t2 : Syn .typeName := .mapping (.elem (.int false 8 (by decide)) (by decide)) none
  (.array (.elem (.fixedBytes 1 (by decide))) .none) none
#guard (elabTyW C R2).toOption == some (T2, [("{}", 8), ("[][]", 8), ("[][]#bytes", 1)])
#guard match rawType C .storage R2 with
  | .ok (.mapping (.elem (.int false 8 _) _) none (.array (.elem (.fixedBytes 1 _)) .none) none) => true
  | _ => false
example (raw : rawType C .storage R2 = .ok t2)
    (el : elabTyW C R2 = .ok (T2, [("{}", 8), ("[][]", 8), ("[][]#bytes", 1)])) :
    Rep C [("m{}", 8), ("m[][]", 8), ("m[][]#bytes", 1), ("mm", 16)] u.env (some "K") "m" .storage T2
      (.mapping (.int ⟨false, 8, by decide⟩) (.array .storage (.fixedBytes 1 (by decide)) none)) := by
  obtain ⟨τ, typed, -, rep⟩ := rawType_agrees decoded hE free closed raw el (plain _)
    (tabled rfl fun st => by revert st; decide +kernel) (key := "m")
    (agree_surround (pre := []) (post := [("mm", 16)]) (by decide +kernel))
  cases typed; exact rep
example : spellType C [("m{}", 8), ("m[][]", 8), ("m[][]#bytes", 1)] "m" .storage T2 =
    .error (.erasedBytes "m[]") := rfl
#guard match rawType C .memory (.named "bytes") with | .error (.unsupportedName _) => true | _ => false

/-- **Conflicting rows**: an earlier row at the element key; the model type is not represented
by `uint8[]` there (the table spells `uint16[]`). -/
example {E : Env} {scope : Option String} : ¬ Rep C [("xs[]", 16), ("xs[]", 8)] E scope "xs" .memory
    (.ref (.array .uint)) (.array .memory (.int ⟨false, 8, by decide⟩) none) := fun r => by
  cases r with
  | array r =>
    generalize hτ : STy.int ⟨false, 8, by decide⟩ = τ at r
    cases r with
    | @prim _ _ _ e he _ =>
      have : Decode.elemB [("xs[]", 16), ("xs[]", 8)] ("xs" ++ "[]") .uint =
        some (.int false 16 (by decide)) := by decide +kernel
      rw [this] at he; cases he; cases hτ

/-- **Ambiguous names**: two names for one table, or one name keyed twice, are not `Keyed`; an
aliased table has no written name and no `Rep`. -/
def A : Contract := { vars := [], structs := [("I", inner), ("J", inner), ("J", "Inner{c:bool}")] }
example : written? A inner = none ∧ ¬ Keyed A "I" ∧ ¬ Keyed A "J" :=
  ⟨rfl, by decide +kernel, by decide +kernel⟩
example {E : Env} {scope : Option String} {key : Name} {loc : DataLoc} {τ : STy} :
    ¬ Rep A [] E scope key loc (.ref (.struct inner)) τ := fun r => by
  cases r with | struct hw _ => cases hw

-- **Invalid locations**: a mapping in memory, or keyed by `string`: read by `elabTyW`, not spelled.
#guard (elabTyW C R1).toOption.isSome && (elabTyW C (.mapping (.named "string") (.named "uint"))).toOption.isSome
example : rawType C .memory R1 = .error (.mappingOutsideStorage .memory) := rfl
#guard match rawType C .storage (.mapping (.named "string") (.named "uint")) with
  | .error (.unsupportedKey _) => true | _ => false

-- An enum named `bool` is outside `Plain`: `elabTyW` reads the enum, `rawType` the `bool`.
def W : Contract := { vars := [], enums := [("bool", ["Off", "On"])] }
#guard (elabTyW W (.named "bool")).toOption == some (.uint, [("#enum", 1)])
#guard match rawType W .memory (.named "bool") with | .ok (.elem .bool) => true | _ => false

/-! ## Leaf names and generated rows -/

-- `bytes4`: a `uint` to `elabTyW`, whose rows spell `bytes4` again.
#guard (elabTyW C (.named "bytes4")).toOption == some (.uint, [("", 32), ("#bytes", 4)])
example {e : Source.Elem} (he : rawElem "bytes4" = some e) : ∃ p ws,
    elabTyW C (.named "bytes4") = .ok (.prim p, ws) ∧ Decode.elemB ws "" p = some e := leaf_elem he rfl
/-- The rows of a `bytes4[]` value below the binder `m`: first lookup and the element type. -/
example : lookupBy "m[]#bytes" (rebase "m" [("[]", 32), ("[]#bytes", 4)]) = some 4 :=
  lookupBy_rebase "m" "[]#bytes" _
example : Decode.elemB (rebase "m[]" [("", 32), ("#bytes", 4)]) "m[]" .uint =
    some (.fixedBytes 4 (by decide)) := (elemB_rebase _ _ _).trans (by decide +kernel)
/-- Rows of other binders around the generated ones are not read; a row at the key is. -/
example : StructRows.Agree (readTy "m" (.ref (.array .uint))) (rebase "m" [("[]", 8)])
    ([("n", 8)] ++ rebase "m" [("[]", 8)] ++ [("mm[]", 16)]) := agree_surround (by decide +kernel)
example : lookupBy "m[]" ([("m[]", 16)] ++ rebase "m" [("[]", 8)]) = some 16 := by decide +kernel
/-- A struct name `rawLeaf` writes is the same struct to `elabTyW`, with no rows. -/
example {s : String} {t : Source.Syn .typeName} (ok : ReferenceDecode.rawLeaf C s = .ok t)
    (he : rawElem s = none) : ∃ table, C.structName? s = some table ∧
      elabTyW C (.named s) = .ok (.ref (.struct table), []) :=
  let ⟨table, name, _, _, el⟩ := leaf_struct ok he; ⟨table, name, el⟩
/-- The rows of `mapping(uint8 => uint16[])` at `m`: nested keys, and the key rows `m{}` and
the value rows `m[]…` read apart out of any table that agrees with them. -/
example : rebase "m" ([("[]", 16)].map fun (k, n) => ("[]" ++ k, n)) = rebase "m[]" [("[]", 16)] :=
  rebase_nest "m" "[]" _
example {widths : List (Name × Nat)} (h : StructRows.Agree
    (ReferenceDecode.readRef "m" (.mapping .uint (.ref (.array .uint))))
    (rebase "m" ([("", 8)].map (fun (k, n) => ("{}" ++ k, n)) ++
      [("[]", 16)].map fun (k, n) => ("[]" ++ k, n))) widths) :
    Decode.elemB widths "m{}" .uint = some (.int false 8 (by decide)) ∧
      StructRows.Agree (readTy "m[]" (.ref (.array .uint))) (rebase "m[]" [("[]", 16)]) widths :=
  ⟨(StructRows.elemB_congr (Agree.keyRows h) .uint).symm.trans
    ((elemB_rebase _ _ _).trans (by decide +kernel)), Agree.valueRows h⟩

end Solidity.Examples.Lowering.Total.RawTypeAgreement

#print axioms Solidity.Correctness.Lowering.Total.RawTypeAgreement.rawType_agrees
#print axioms Solidity.Correctness.Lowering.Total.RawTypeAgreement.leaf_agrees
