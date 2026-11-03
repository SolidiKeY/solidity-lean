import Solidity.Frontend.SolcJson.YulOccurrenceSchema
import Std.Data.DTreeMap.Internal.WF.Lemmas

/-! Actual keyed lookup to actual object-enumeration positions. The forward
fact holds even for arbitrary malformed raw maps. No raw-map well-formedness,
reverse-lookup or uniqueness fact is assumed or claimed. -/
namespace Solidity.Frontend.YulJson.ObjectLookup
open Lean (Json)
open Std.DTreeMap.Internal (Impl)

private theorem impl_lookup_member
    (tree : Impl String (fun _ => Json)) (key : String) (value : Json)
    (found : Impl.Const.get? tree key = some value) :
    (key,value) ∈ tree.toListModel.map (fun entry => (entry.1,entry.2)) := by
  induction tree generalizing key value with
  | leaf => cases found
  | inner size stored storedValue left right leftIH rightIH =>
      cases comparison : compare key stored with
      | lt =>
          have member := leftIH key value (by
            simpa only [Impl.Const.get?,comparison] using found)
          rw [Impl.toListModel_inner,List.map_append,List.map_cons]
          exact List.mem_append_left _ member
      | gt =>
          have member := rightIH key value (by
            simpa only [Impl.Const.get?,comparison] using found)
          rw [Impl.toListModel_inner,List.map_append,List.map_cons]
          exact List.mem_append_right _ (List.mem_cons_of_mem _ member)
      | eq =>
          have same : key = stored := Std.LawfulEqOrd.eq_of_compare comparison
          have valueEq : storedValue = value := Option.some.inj (by
            simpa only [Impl.Const.get?,comparison] using found)
          cases same
          cases valueEq
          rw [Impl.toListModel_inner,List.map_append,List.map_cons]
          exact List.mem_append_right _ List.mem_cons_self

/-- A real lookup hit occurs in actual toList, without a WF premise. -/
theorem lookup_member (fields : Std.TreeMap.Raw String Json) (key : String) (value : Json)
    (found : fields.get? key = some value) : (key,value) ∈ fields.toList := by
  change (key,value) ∈ Impl.Const.toList fields.inner.inner
  rw [Impl.Const.toList_eq_toListModel_map]
  exact impl_lookup_member fields.inner.inner key value found

/-- A lookup hit supplies an actual enumeration ordinal, not a hard-coded key
position or a uniqueness premise. -/
theorem lookup_ordinal (fields : Std.TreeMap.Raw String Json) (key : String) (value : Json)
    (found : fields.get? key = some value) :
    ∃ index : Fin fields.toList.length, fields.toList[index] = (key,value) := by
  exact List.mem_iff_get.mp (lookup_member fields key value found)

theorem field_ordinal {node : Json} {key : String} {value : Json}
    (found : field node key = .ok value) :
    ∃ fields : Std.TreeMap.Raw String Json, node = .obj fields ∧
      ∃ index : Fin fields.toList.length, fields.toList[index] = (key,value) := by
  cases node with
  | null => cases found
  | bool b => cases found
  | num n => cases found
  | str s => cases found
  | arr values => cases found
  | obj fields =>
      refine ⟨fields,rfl,?_⟩
      cases actual : fields.get? key with
      | none => simp only [field,Json.getObjVal?,actual,Except.mapError] at found; cases found
      | some selected =>
          have decoded : field (.obj fields) key = .ok selected := by
            simp only [field,Json.getObjVal?,actual,Except.mapError,pure,Except.pure]
          have same : selected = value := Except.ok.inj (decoded.symm.trans found)
          cases same
          exact lookup_ordinal fields key value actual

/-- Lift through the field that the decoder ACTUALLY selected, using its real
enumeration ordinal. This is forward transport, without a reverse/WF premise. -/
theorem field_occurrence {parent child : Json} {key : String} {start path write node}
    (found : field parent key = .ok child)
    (notIdentifier : Occurrences.isIdentifier parent = false)
    (selected : Occurrences.includeField parent key = true)
    (inside : Occurrences.OccurrenceD child (Occurrences.fieldRole parent key) path write node) :
    ∃ ordinal : Nat,
      Occurrences.OccurrenceD parent start (.field key ordinal::path) write node := by
  obtain ⟨fields,equal,index,pairEq⟩ := field_ordinal found
  cases equal
  have lifted := Occurrences.OccurrenceD.object (start := start) index notIdentifier
    (by simpa only [pairEq] using selected) (by simpa only [pairEq] using inside)
  exact ⟨index.val,by simpa only [pairEq] using lifted⟩

theorem array_occurrence {values : Array Json} {child : Json} {start path write node}
    (member : child ∈ values.toList)
    (inside : Occurrences.OccurrenceD child start path write node) :
    ∃ ordinal : Nat,
      Occurrences.OccurrenceD (.arr values) start (.array ordinal::path) write node := by
  obtain ⟨index,bound,same⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  refine ⟨index,Occurrences.OccurrenceD.array ⟨index,bound⟩ ?_⟩
  change Occurrences.OccurrenceD (values[index]'bound) start path write node
  simpa only [same] using inside

theorem kind_of_string {node : Json} {value : String}
    (found : string node "nodeType" = .ok value) : Occurrences.kind node = value := by
  unfold Occurrences.kind
  rw [found]
  rfl

theorem array_field {node : Json} {key : String} {values : Array Json}
    (parsed : array node key = .ok values) : field node key = .ok (.arr values) := by
  unfold array at parsed
  cases actual : field node key with
  | error reason => rw [actual] at parsed; cases parsed
  | ok child =>
      rw [actual] at parsed
      cases child with
      | null => cases parsed
      | bool b => cases parsed
      | num n => cases parsed
      | str text => cases parsed
      | obj fields => cases parsed
      | arr selected =>
          have same : selected = values := Except.ok.inj parsed
          cases same
          rfl

end Solidity.Frontend.YulJson.ObjectLookup
