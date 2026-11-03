import Solidity.Backend.StorageOps.RecursiveCopy
import Solidity.Backend.StorageOps.CommonPrefix

/-! Actual copies capture reads from each current root, rather than assuming
immutable external snapshots. Disjoint write/read footprints justify freezing
those captures for commutation. No numeric/source/world bridge is claimed. -/
namespace Solidity.Backend.StorageOps
open TypeGraph

def copyEffect {n : Nat} {G : Schema n} {T U : TypeGraph.Ty n}
    (source : Value G T) (dst src : TypeGraph.Path G T U) (target : Value G T) : Option (Value G T) := do
  let snapshot ← source.find src
  let old ← target.find dst
  target.save dst (recursiveCopy old snapshot)

/-- The source is freshly read from the supplied current slots on EVERY call. -/
def copySibling {n : Nat} {G : Schema n} {K : PrimTy} {T U : TypeGraph.Ty n}
    (slots : K.Denote → Slot G T) (dstKey srcKey : K.Denote)
    (dst src : TypeGraph.Path G T U) : Option (K.Denote → Slot G T) :=
  modifySlot slots dstKey (copyEffect ((slots srcKey).getD (Value.dflt T)) dst src)

theorem copySibling_eq_actual {n : Nat} {G : Schema n} {K : PrimTy} {T U : TypeGraph.Ty n}
    (slots : K.Denote → Slot G T) (d s : K.Denote) (dst src : TypeGraph.Path G T U) :
    recursiveCopyAt (.mapping slots) (.cons (.key d) dst) (.cons (.key s) src) =
      (copySibling slots d s dst src).map Value.mapping := by
  simp only [recursiveCopyAt, copySibling, copyEffect, modifySlot, Value.find, Value.save,
    TypeGraph.Path.read, TypeGraph.Path.save, TypeGraph.Step.get, TypeGraph.Step.put,
    Option.bind_eq_bind, Option.bind_some]
  cases rs : src.read Value.dflt ((slots s).getD (Value.dflt T)) with
  | none => rfl
  | some snapshot =>
    simp only [Option.bind_some]
    cases rd : dst.read Value.dflt ((slots d).getD (Value.dflt T)) with
    | none => rfl
    | some old =>
      simp only [Option.bind_some]
      cases dst.save Value.dflt ((slots d).getD (Value.dflt T)) (recursiveCopy old snapshot) <;> rfl

/-- Derived write-frame for source captures, including defaulted absent keys. -/
theorem copySibling_source_frame {n : Nat} {G : Schema n} {K : PrimTy} {T U : TypeGraph.Ty n}
    (slots result : K.Denote → Slot G T) (d s q : K.Denote)
    (dst src : TypeGraph.Path G T U) (outside : q ≠ d)
    (copied : copySibling slots d s dst src = some result) : result q = slots q := by
  unfold copySibling modifySlot at copied
  cases localCopy : copyEffect ((slots s).getD (Value.dflt T)) dst src ((slots d).getD (Value.dflt T)) with
  | none => simp only [localCopy, Option.map_none] at copied; cases copied
  | some value =>
    simp only [localCopy, Option.map_some, Option.some.injEq] at copied
    subst result
    exact Slots.write_other slots d q outside value

/-- Two actual captures commute if destinations differ and neither overwrites
the OTHER source. Sources may be shared; self-copies are permitted. Suffixes
have heterogeneous endpoints and arbitrary finite depth. ALL Option outcomes. -/
theorem copySibling_commute {n : Nat} {G : Schema n} {K : PrimTy} {T U V : TypeGraph.Ty n}
    (slots : K.Denote → Slot G T) (da sa db sb : K.Denote)
    (destinations : da ≠ db) (readB : sb ≠ da) (readA : sa ≠ db)
    (ad asrc : TypeGraph.Path G T U) (bd bsrc : TypeGraph.Path G T V) :
    (copySibling slots da sa ad asrc).bind (fun next => copySibling next db sb bd bsrc) =
    (copySibling slots db sb bd bsrc).bind (fun next => copySibling next da sa ad asrc) := by
  cases left : copyEffect ((slots sa).getD (Value.dflt T)) ad asrc ((slots da).getD (Value.dflt T)) with
  | none =>
    cases right : copyEffect ((slots sb).getD (Value.dflt T)) bd bsrc ((slots db).getD (Value.dflt T)) <;>
      simp only [copySibling, modifySlot, left, right, Option.map_none, Option.map_some,
        Option.bind_none, Option.bind_some, Slots.write_other slots db da destinations,
        Slots.write_other slots db sa readA]
  | some x =>
    cases right : copyEffect ((slots sb).getD (Value.dflt T)) bd bsrc ((slots db).getD (Value.dflt T)) with
    | none =>
      simp only [copySibling, modifySlot, left, right, Option.map_none, Option.map_some,
        Option.bind_none, Option.bind_some, Slots.write_other slots da db (Ne.symm destinations),
        Slots.write_other slots da sb readB]
    | some y =>
      simp only [copySibling, modifySlot, left, right, Option.map_some, Option.bind_some,
        Slots.write_other slots db da destinations, Slots.write_other slots db sa readA,
        Slots.write_other slots da db (Ne.symm destinations), Slots.write_other slots da sb readB]
      exact congrArg some (writes_commute slots da db destinations x y)

/-- The theorem is about actual recursiveCopyAt invocations on successive roots. -/
theorem actual_mapping_copies_commute {n : Nat} {G : Schema n} {K : PrimTy} {T U V : TypeGraph.Ty n}
    (slots : K.Denote → Slot G T) (da sa db sb : K.Denote)
    (destinations : da ≠ db) (readB : sb ≠ da) (readA : sa ≠ db)
    (ad asrc : TypeGraph.Path G T U) (bd bsrc : TypeGraph.Path G T V) :
    (recursiveCopyAt (.mapping slots) (.cons (.key da) ad) (.cons (.key sa) asrc)).bind
      (fun next => recursiveCopyAt next (.cons (.key db) bd) (.cons (.key sb) bsrc)) =
    (recursiveCopyAt (.mapping slots) (.cons (.key db) bd) (.cons (.key sb) bsrc)).bind
      (fun next => recursiveCopyAt next (.cons (.key da) ad) (.cons (.key sa) asrc)) := by
  simp only [copySibling_eq_actual, Option.bind_map]
  have h := congrArg (Option.map Value.mapping)
    (copySibling_commute slots da sa db sb destinations readB readA ad asrc bd bsrc)
  simpa only [Option.map_bind, Function.comp_def, copySibling_eq_actual] using h

/-- BOTH reads and the save factor through the same arbitrary finite prefix,
including unreadable/defaulted/retained prefixes and failed suffixes. -/
theorem recursiveCopyAt_append {n : Nat} {G : Schema n} {A T U : TypeGraph.Ty n}
    (root : Value G A) (pre : TypeGraph.Path G A T) (dst src : TypeGraph.Path G T U) :
    recursiveCopyAt root (pre.append dst) (pre.append src) =
      modifyAt root pre (fun child => recursiveCopyAt child dst src) := by
  simp only [recursiveCopyAt, modifyAt, Value.find, TypeGraph.Path.read_append,
    prefix_save_append, Option.bind_eq_bind]
  cases read : pre.read Value.dflt root with
  | none => rfl
  | some child => simp only [Option.bind_some, Option.bind_assoc]

/-- Concrete mutable-source copy commutation under a common prefix; child
commutation is discharged by constructor-derived source frames above. -/
theorem common_prefix_copies_commute {n : Nat} {G : Schema n} {A T U V : TypeGraph.Ty n}
    {K : PrimTy} (root : Value G A) (pre : TypeGraph.Path G A (.mapping K T))
    (da sa db sb : K.Denote) (destinations : da ≠ db) (readB : sb ≠ da) (readA : sa ≠ db)
    (ad asrc : TypeGraph.Path G T U) (bd bsrc : TypeGraph.Path G T V) :
    (recursiveCopyAt root (pre.append (.cons (.key da) ad)) (pre.append (.cons (.key sa) asrc))).bind
      (fun next => recursiveCopyAt next (pre.append (.cons (.key db) bd)) (pre.append (.cons (.key sb) bsrc))) =
    (recursiveCopyAt root (pre.append (.cons (.key db) bd)) (pre.append (.cons (.key sb) bsrc))).bind
      (fun next => recursiveCopyAt next (pre.append (.cons (.key da) ad)) (pre.append (.cons (.key sa) asrc))) := by
  simp only [recursiveCopyAt_append]
  apply common_prefix_lift
  intro child
  cases child with
  | mapping slots => exact actual_mapping_copies_commute slots da sa db sb destinations readB readA ad asrc bd bsrc

/-- info: 'Solidity.Backend.StorageOps.recursiveCopyAt_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms recursiveCopyAt_append
/-- info: 'Solidity.Backend.StorageOps.common_prefix_copies_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms common_prefix_copies_commute
/-- info: 'Solidity.Backend.StorageOps.copySibling_eq_actual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms copySibling_eq_actual
/-- info: 'Solidity.Backend.StorageOps.copySibling_source_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms copySibling_source_frame
/-- info: 'Solidity.Backend.StorageOps.copySibling_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms copySibling_commute
/-- info: 'Solidity.Backend.StorageOps.actual_mapping_copies_commute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms actual_mapping_copies_commute
end Solidity.Backend.StorageOps
