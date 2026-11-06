import Solidity.Backend.StorageOps.FieldOperations

/-! Recursive suffix adapters for actual existing graph-path operations.
These are operation identities/commutation, not numeric representation frames.
No new source path syntax, value layer or independent semantics is introduced. -/
namespace Solidity.Backend.StorageOps
open TypeGraph

/-- Updating an arbitrary typed suffix below a node field is exactly a local
member operation whose effect is the existing suffix find/effect/save. -/
theorem modifyAt_field_suffix {n : Nat} {G : Schema n} {i : Fin n}
    {T U : TypeGraph.Ty n} (fields : TypeGraph.Fields G (G.fields i))
    (position : Field (G.fields i) T) (suffix : TypeGraph.Path G T U)
    (effect : Value G U → Option (Value G U)) :
    modifyAt (.node fields) (.cons (.field position) suffix) effect =
      (modifyField fields position (fun value => modifyAt value suffix effect)).map Value.node := by
  simp only [modifyAt, modifyField, Value.find, Value.save, TypeGraph.Path.read,
    TypeGraph.Path.save, TypeGraph.Step.get, TypeGraph.Step.put,
    Option.bind_eq_bind, Option.bind_some]
  cases read : suffix.read Value.dflt (TypeGraph.Fields.get fields position) with
  | none => rfl
  | some old =>
    simp only [Option.bind_some]
    cases changed : effect old with
    | none => rfl
    | some new =>
      simp only [Option.bind_some]
      cases saved : suffix.save Value.dflt (TypeGraph.Fields.get fields position) new <;> rfl

/-- Updating an arbitrary typed suffix below a mapping key is exactly the
keyed operation with the captured suffix update as its local effect. -/
theorem modifyAt_key_suffix {n : Nat} {G : Schema n} {K : PrimTy}
    {T U : TypeGraph.Ty n} (slots : K.Denote → Slot G T) (key : K.Denote)
    (suffix : TypeGraph.Path G T U) (effect : Value G U → Option (Value G U)) :
    modifyAt (.mapping slots) (.cons (.key key) suffix) effect =
      (modifySlot slots key (fun value => modifyAt value suffix effect)).map Value.mapping := by
  simp only [modifyAt, modifySlot, Value.find, Value.save, TypeGraph.Path.read,
    TypeGraph.Path.save, TypeGraph.Step.get, TypeGraph.Step.put,
    Option.bind_eq_bind, Option.bind_some]
  cases read : suffix.read Value.dflt ((slots key).getD (Value.dflt T)) with
  | none => rfl
  | some old =>
    simp only [Option.bind_some]
    cases changed : effect old with
    | none => rfl
    | some new =>
      simp only [Option.bind_some]
      cases saved : suffix.save Value.dflt ((slots key).getD (Value.dflt T)) new <;> rfl

/-- Distinct heterogeneous node members may contain arbitrary-depth recursive
suffix paths; their partial operations commute including every failure branch. -/
theorem recursive_fields_commute {n : Nat} {G : Schema n} {i : Fin n}
    {T U A B : TypeGraph.Ty n} (fields : TypeGraph.Fields G (G.fields i))
    (p : Field (G.fields i) T) (q : Field (G.fields i) U) (different : p.toNat ≠ q.toNat)
    (left : TypeGraph.Path G T A) (right : TypeGraph.Path G U B)
    (f : Value G A → Option (Value G A)) (g : Value G B → Option (Value G B)) :
    (modifyAt (.node fields) (.cons (.field p) left) f).bind
      (fun root => modifyAt root (.cons (.field q) right) g) =
    (modifyAt (.node fields) (.cons (.field q) right) g).bind
      (fun root => modifyAt root (.cons (.field p) left) f) := by
  simp only [modifyAt_field_suffix, Option.bind_map]
  have commute := modifyField_commute fields p q different
    (fun value => modifyAt value left f) (fun value => modifyAt value right g)
  have transported := congrArg (Option.map Value.node) commute
  simpa only [Option.map_bind, Function.comp_def, modifyAt_field_suffix] using transported

/-- Distinct keys may contain arbitrary typed recursive suffixes, without
assuming either source path read/save or either effect succeeds. -/
theorem recursive_keys_commute {n : Nat} {G : Schema n} {K : PrimTy}
    {T A B : TypeGraph.Ty n} (slots : K.Denote → Slot G T) (a b : K.Denote)
    (different : a ≠ b) (left : TypeGraph.Path G T A) (right : TypeGraph.Path G T B)
    (f : Value G A → Option (Value G A)) (g : Value G B → Option (Value G B)) :
    (modifyAt (.mapping slots) (.cons (.key a) left) f).bind
      (fun root => modifyAt root (.cons (.key b) right) g) =
    (modifyAt (.mapping slots) (.cons (.key b) right) g).bind
      (fun root => modifyAt root (.cons (.key a) left) f) := by
  simp only [modifyAt_key_suffix, Option.bind_map]
  have commute := modifySlot_commute slots a b different
    (fun value => modifyAt value left f) (fun value => modifyAt value right g)
  have transported := congrArg (Option.map Value.mapping) commute
  simpa only [Option.map_bind, Function.comp_def, modifyAt_key_suffix] using transported

end Solidity.Backend.StorageOps
