import Solidity.SolcValidation.DataResolution

namespace Solidity.SolcValidation.MigrationChecks

-- Complete compiler-only operation census, including their arities.
example : (ObjectOp.datasize "").name = "datasize" := rfl
example : (ObjectOp.dataoffset "λ").name = "dataoffset" := rfl
example : (ObjectOp.datacopy : ObjectOp 3 0).name = "datacopy" := rfl
example : (ObjectOp.setimmutable "x" : ObjectOp 2 0).name = "setimmutable" := rfl
example : (ObjectOp.loadimmutable "x" : ObjectOp 0 1).name = "loadimmutable" := rfl
example : (ObjectOp.linkersymbol "L" : ObjectOp 0 1).name = "linkersymbol" := rfl
example : (ObjectOp.memoryguard ⟨0, by decide⟩ : ObjectOp 0 1).name = "memoryguard" := rfl
example (op : ObjectOp 0 1) : (Op.object op).name = op.name := rfl
example : IrMode.unoptimized ≠ IrMode.optimized := Ne.symm mode_distinct
example : (Object.data "" [] : Object Unit) = Object.data "" [] := rfl

-- Empty artifacts and endpoint references remain inhabited without a fallback.
def emptyRef : DataRef [] := ⟨⟨0, by decide⟩, ⟨0, by decide⟩, by decide⟩
example : emptyRef.bytes = [] := rfl
example : (selectData "" ([] : List (String × DataRef []))).isSome = false := rfl

-- Duplicate raw lists choose their first entry; uniqueness is required only
-- by DataTable, so do not silently strengthen selectData semantics.
def bytes : List DataByte := [⟨17, by decide⟩, ⟨34, by decide⟩]
def first : DataRef bytes := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩
def second : DataRef bytes := ⟨⟨1, by decide⟩, ⟨1, by decide⟩, by decide⟩
example : ((selectData "x" [("x", first), ("x", second)]).map
    fun selection => selection.ref.dataoffset.val) = some 0 := rfl
example : ((selectData "x" [("other", first), ("x", second)]).map
    fun selection => selection.ref.bytes) = some [⟨34, by decide⟩] := rfl
example : first.bytes[0] = bytes[first.offset.val + 0] := first.byte_exact 0 (by decide)
example : first.datasize.val = first.size.val := first.bytes_length

-- Generic witness use checks the complete public resolver contract.
example {artifact : List DataByte} (table : DataTable artifact) {label : String}
    (selected : DataSelection table.entries label) :
    table.select label = some selected := table.select_complete selected
example {artifact : List DataByte} (table : DataTable artifact) {label : String}
    (left right : DataSelection table.entries label) : left = right :=
  DataSelection.ext left right (table.selection_unique left right)
example {artifact : List DataByte} (table : DataTable artifact) {label : String}
    (absent : ∀ ref, (label, ref) ∉ table.entries) :
    ¬ (table.select label).isSome = true := by
  intro found
  obtain ⟨ref, member⟩ := (table.select_iff label).mp found
  exact absent ref member

end Solidity.SolcValidation.MigrationChecks
