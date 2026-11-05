import Solidity.SolcValidation.DataResolution
open Solidity.SolcValidation
-- Generated from exact pinned assembled bytes; this file proves byte intervals,
-- not compiler correctness, label association, gas or physical memory copying.
def assembledObject : List DataByte := [⟨96, by decide⟩, ⟨3, by decide⟩, ⟨96, by decide⟩, ⟨11, by decide⟩, ⟨95, by decide⟩, ⟨57, by decide⟩, ⟨96, by decide⟩, ⟨3, by decide⟩, ⟨95, by decide⟩, ⟨243, by decide⟩, ⟨254, by decide⟩, ⟨17, by decide⟩, ⟨34, by decide⟩, ⟨51, by decide⟩]
def payload : DataRef assembledObject :=
  ⟨⟨11, by decide⟩, ⟨3, by decide⟩, by decide⟩
def payloadTable : DataTable assembledObject :=
  ⟨[("payload", payload)], by decide⟩
example : payload.bytes = [⟨17, by decide⟩, ⟨34, by decide⟩, ⟨51, by decide⟩] := rfl
example : payload.datasize.val = 3 := rfl
example : payload.dataoffset.val = 11 := rfl
example : (payloadTable.select "payload").isSome = true := rfl
example : (payloadTable.select "absent").isSome = false := rfl
example : ((⟨⟨14, by decide⟩, ⟨0, by decide⟩, by decide⟩ : DataRef assembledObject).bytes) = [] := rfl
example (ref : DataRef assembledObject)
    (atEnd : ref.offset.val = 12) (size : ref.size.val = 3) : False := by
  have bound := ref.within
  change ref.offset.val + ref.size.val ≤ 14 at bound
  rw [atEnd, size] at bound
  omega
example (table : DataTable assembledObject)
    (duplicate : table.entries = [("payload", payload), ("payload", payload)]) : False := by
  have invalid : ¬ (["payload", "payload"] : List String).Nodup := by decide
  apply invalid
  simpa only [duplicate, List.map_cons, List.map_nil] using table.unique
def endpoint : DataRef assembledObject :=
  ⟨⟨14, by decide⟩, ⟨0, by decide⟩, by decide⟩
def twoLabels : DataTable assembledObject :=
  ⟨[("empty", endpoint), ("payload", payload)], by decide⟩
def tailSelection : DataSelection twoLabels.entries "payload" :=
  ⟨payload, List.Mem.tail _ (List.Mem.head _)⟩
example : twoLabels.select "payload" = some tailSelection :=
  twoLabels.select_complete tailSelection
example (other : DataSelection twoLabels.entries "payload") : other.ref = payload :=
  twoLabels.selection_unique other tailSelection
example : ((twoLabels.select "empty").map fun selected => selected.ref.bytes) = some [] := rfl
example : (twoLabels.select "wrong").isSome = false := rfl
#print axioms DataTable.selection_unique
#print axioms DataSelection.ext
#print axioms DataTable.select_complete
#print axioms DataTable.select_iff
#print axioms DataRef.bytes_length
#print axioms DataRef.datasize_exact
#print axioms DataRef.dataoffset_exact
#print axioms DataRef.byte_exact
#print axioms DataSelection.sound
#print axioms selectData_complete
