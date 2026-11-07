import Solidity.SolcValidation.Dialect

/-!
# Checked object-data references into assembled artifact bytes

This is the label-resolution/data-size boundary of the solc dialect adapter.
References retain their actual byte interval in an assembled artifact. It does
not serialize objects, authenticate assembly output or model memory copying.
-/
namespace Solidity.SolcValidation

abbrev DataByte := Fin 256
abbrev DataWord := Fin (2 ^ 256)

/-- Offsets and sizes are words, and the complete selected interval exists in
this artifact. This is a static label reference, not a dynamic CODECOPY bound. -/
structure DataRef (artifact : List DataByte) where
  offset : DataWord
  size : DataWord
  within : offset.val + size.val ≤ artifact.length

/-- The actual bytes at a checked label's assembled position. -/
def DataRef.bytes {artifact : List DataByte} (ref : DataRef artifact) : List DataByte :=
  (artifact.drop ref.offset.val).take ref.size.val

theorem DataRef.bytes_length {artifact : List DataByte} (ref : DataRef artifact) :
    ref.bytes.length = ref.size.val := by
  have fits : ref.size.val ≤ artifact.length - ref.offset.val := by
    have bound := ref.within
    omega
  simp only [DataRef.bytes, List.length_take, List.length_drop, Nat.min_eq_left fits]

/-- DATASIZE is the actual byte length, with its word bound inherited from
this checked reference rather than a modularly truncated host integer. -/
def DataRef.datasize {artifact : List DataByte} (ref : DataRef artifact) : DataWord :=
  ⟨ref.bytes.length, by rw [ref.bytes_length]; exact ref.size.isLt⟩

def DataRef.dataoffset {artifact : List DataByte} (ref : DataRef artifact) : DataWord :=
  ref.offset

theorem DataRef.datasize_exact {artifact : List DataByte} (ref : DataRef artifact) :
    ref.datasize.val = ref.bytes.length := rfl

theorem DataRef.dataoffset_exact {artifact : List DataByte} (ref : DataRef artifact) :
    ref.dataoffset = ref.offset := rfl

/-- Every byte selected through a label is the byte at its actual assembled
position; no source-side or physical-memory premise is hidden here. -/
theorem DataRef.byte_exact {artifact : List DataByte} (ref : DataRef artifact)
    (i : Nat) (inside : i < ref.bytes.length) :
    ref.bytes[i] = artifact[ref.offset.val + i]'(by
      have bound := ref.within
      have count := ref.bytes_length
      omega) := by
  simp only [DataRef.bytes, List.getElem_take, List.getElem_drop]

/-- A resolved per-object label table cannot contain duplicate label names.
Canonical nested paths and association to parser declarations remain importer work. -/
structure DataTable (artifact : List DataByte) where
  entries : List (String × DataRef artifact)
  unique : (entries.map Prod.fst).Nodup

/-- A lookup result retains membership at the exact requested label. -/
structure DataSelection {artifact : List DataByte}
    (entries : List (String × DataRef artifact)) (label : String) where
  ref : DataRef artifact
  member : (label, ref) ∈ entries

/-- Resolve names without inventing a missing entry. Object-path construction
and global label uniqueness must be checked by the object importer. -/
def selectData {artifact : List DataByte} (label : String) :
    (entries : List (String × DataRef artifact)) → Option (DataSelection entries label)
  | [] => none
  | (name, ref) :: rest =>
      if same : name = label then
        some ⟨ref, by subst name; exact List.Mem.head _⟩
      else
        match selectData label rest with
        | none => none
        | some selected => some ⟨selected.ref, List.Mem.tail _ selected.member⟩

/-- A present label is never discarded by the resolver. This states only
existence of a selection; duplicate lists have no arbitrary equality guarantee. -/
theorem selectData_complete {artifact : List DataByte} {label : String}
    {entries : List (String × DataRef artifact)} (selected : DataSelection entries label) :
    (selectData label entries).isSome = true := by
  induction entries with
  | nil => cases selected.member
  | cons entry rest ih =>
      obtain ⟨name, ref⟩ := entry
      by_cases same : name = label
      · simp only [selectData, dif_pos same, Option.isSome_some]
      · have inRest : (label, selected.ref) ∈ rest := by
          rcases List.mem_cons.mp selected.member with head | tail
          · have names : label = name := congrArg Prod.fst head
            exact False.elim (same names.symm)
          · exact tail
        have found : (selectData label rest).isSome = true := ih ⟨selected.ref, inRest⟩
        simp only [selectData, dif_neg same]
        cases actual : selectData label rest with
        | none => simp only [actual, Option.isSome_none, Bool.false_eq_true] at found
        | some result => rfl

/-- Public table lookup also retains the table's intrinsic uniqueness invariant. -/
def DataTable.select {artifact : List DataByte} (table : DataTable artifact)
    (label : String) : Option (DataSelection table.entries label) :=
  selectData label table.entries

/-- A returned reference belongs to the actual supplied label table. This is
not a claim that a supplied table is a compiler-authenticated object layout. -/
theorem DataSelection.sound {artifact : List DataByte}
    {entries : List (String × DataRef artifact)} {label : String}
    (selected : DataSelection entries label) : (label, selected.ref) ∈ entries :=
  selected.member

end Solidity.SolcValidation
