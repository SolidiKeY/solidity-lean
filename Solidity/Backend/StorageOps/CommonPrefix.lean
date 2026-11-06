import Solidity.Backend.StorageOps.PrefixLaws

/-! Actual operation transport through arbitrary finite intrinsic prefixes.
All Option outcomes and raw retained/defaulted reads are preserved. Effects
read their addressed value and fixed captures; no world rollback is asserted. -/
namespace Solidity.Backend.StorageOps
open TypeGraph

/-- Saving an appended path factors through reading and saving its prefix.
No readability, liveness, extent or successful-save premise is imposed. -/
theorem prefix_save_append {n : Nat} {G : Schema n} {A B C : TypeGraph.Ty n}
    (pre : TypeGraph.Path G A B) (suffix : TypeGraph.Path G B C)
    (root : Value G A) (value : Value G C) :
    root.save (pre.append suffix) value =
      (root.find pre).bind (fun old => (old.save suffix value).bind (fun next => root.save pre next)) := by
  induction pre with
  | nil => simp only [Value.save, Value.find, TypeGraph.Path.append,
      TypeGraph.Path.read, TypeGraph.Path.save, Option.bind_some, Option.bind_fun_some]
  | cons step rest ih =>
    simp only [Value.save, Value.find, TypeGraph.Path.append, TypeGraph.Path.save,
      TypeGraph.Path.read, Option.bind_eq_bind]
    cases first : step.get Value.dflt root with
    | none => rfl
    | some old =>
      simp only [Option.bind_some]
      rw [show (rest.append suffix).save Value.dflt old value =
        (rest.read Value.dflt old).bind (fun child =>
          (suffix.save Value.dflt child value).bind (fun next => rest.save Value.dflt old next)) from ih suffix old]
      simp only [Option.bind_assoc]

/-- Actual find/effect/save factors through every finite common prefix, even
when a path/effect fails. Default materialization is preserved exactly. -/
theorem modifyAt_append {n : Nat} {G : Schema n} {A B C : TypeGraph.Ty n}
    (root : Value G A) (pre : TypeGraph.Path G A B) (suffix : TypeGraph.Path G B C)
    (effect : Value G C → Option (Value G C)) :
    modifyAt root (pre.append suffix) effect =
      modifyAt root pre (fun old => modifyAt old suffix effect) := by
  simp only [modifyAt, Value.find, TypeGraph.Path.read_append, prefix_save_append,
    Option.bind_eq_bind]
  cases first : pre.read Value.dflt root with
  | none => rfl
  | some old => simp only [Option.bind_some, Option.bind_assoc]

/-- Sequential local effects lift through a common prefix, including failure.
Readability guarantees replacement succeeds; overwrite/readback are derived
from constructors in PrefixLaws, not assumed as a desired preservation premise. -/
theorem modifyAt_sequence {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (root : Value G A) (pre : TypeGraph.Path G A B)
    (f g : Value G B → Option (Value G B)) :
    (modifyAt root pre f).bind (fun next => modifyAt next pre g) =
      modifyAt root pre (fun old => (f old).bind g) := by
  simp only [modifyAt, Option.bind_eq_bind]
  cases read : root.find pre with
  | none => rfl
  | some old =>
    simp only [Option.bind_some]
    cases changed : f old with
    | none => rfl
    | some value =>
      simp only [Option.bind_some]
      obtain ⟨next, saved⟩ := prefix_save_exists pre root old value read
      rw [saved]
      simp only [Option.bind_some, Value.find_save root next pre value saved]
      cases second : g value with
      | none => rfl
      | some last =>
        simp only [Option.bind_some]
        exact prefix_save_overwrite pre root next value last saved

/-- Composition transport only: the child commutation premise is explicitly
supplied. The field/key corollaries below discharge it with published lane laws. -/
theorem common_prefix_lift {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (root : Value G A) (pre : TypeGraph.Path G A B)
    (f g : Value G B → Option (Value G B))
    (commute : ∀ child, (f child).bind g = (g child).bind f) :
    (modifyAt root pre f).bind (fun next => modifyAt next pre g) =
      (modifyAt root pre g).bind (fun next => modifyAt next pre f) := by
  rw [modifyAt_sequence, modifyAt_sequence]
  have equal : (fun child => (f child).bind g) = (fun child => (g child).bind f) := funext commute
  rw [equal]

/-- Heterogeneous recursive suffix operations below distinct fields commute
beneath an arbitrary common prefix. The root/prefix need not be readable. -/
theorem common_prefix_fields_commute {n : Nat} {G : Schema n} {A T U B C : TypeGraph.Ty n}
    {i : Fin n} (root : Value G A) (pre : TypeGraph.Path G A (.node i))
    (p : Field (G.fields i) T) (q : Field (G.fields i) U) (different : p.toNat ≠ q.toNat)
    (left : TypeGraph.Path G T B) (right : TypeGraph.Path G U C)
    (f : Value G B → Option (Value G B)) (g : Value G C → Option (Value G C)) :
    (modifyAt root (pre.append (.cons (.field p) left)) f).bind
      (fun next => modifyAt next (pre.append (.cons (.field q) right)) g) =
    (modifyAt root (pre.append (.cons (.field q) right)) g).bind
      (fun next => modifyAt next (pre.append (.cons (.field p) left)) f) := by
  simp only [modifyAt_append]
  apply common_prefix_lift
  intro child
  cases child with
  | node fields => exact recursive_fields_commute fields p q different left right f g

/-- Arbitrary recursive suffixes below distinct mapping keys commute beneath
an arbitrary common prefix, with all defaulted/retained/failing outcomes. -/
theorem common_prefix_keys_commute {n : Nat} {G : Schema n} {A T B C : TypeGraph.Ty n}
    {K : PrimTy} (root : Value G A) (pre : TypeGraph.Path G A (.mapping K T))
    (a b : K.Denote) (different : a ≠ b)
    (left : TypeGraph.Path G T B) (right : TypeGraph.Path G T C)
    (f : Value G B → Option (Value G B)) (g : Value G C → Option (Value G C)) :
    (modifyAt root (pre.append (.cons (.key a) left)) f).bind
      (fun next => modifyAt next (pre.append (.cons (.key b) right)) g) =
    (modifyAt root (pre.append (.cons (.key b) right)) g).bind
      (fun next => modifyAt next (pre.append (.cons (.key a) left)) f) := by
  simp only [modifyAt_append]
  apply common_prefix_lift
  intro child
  cases child with
  | mapping slots => exact recursive_keys_commute slots a b different left right f g

end Solidity.Backend.StorageOps
