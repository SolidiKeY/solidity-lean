import Solidity.Backend.StorageOps.OperationFamilies

/-! Disjoint heterogeneous member operations on existing intrinsic Fields.
No uniform-value replacement store, representation or EVM frame is introduced. -/

namespace Solidity.Backend.StorageOps

open TypeGraph

/-- Updates to distinct typed field positions commute, even when their value
types differ. The proof uses the existing dependent Fields getter/setter. -/
theorem field_writes_commute {n : Nat} {G : Schema n} {fs : List (Name × TypeGraph.Ty n)}
    {T U : TypeGraph.Ty n} (fields : TypeGraph.Fields G fs)
    (p : Field fs T) (q : Field fs U) (different : p.toNat ≠ q.toNat)
    (x : Value G T) (y : Value G U) :
    @Eq (TypeGraph.Fields G fs)
      (TypeGraph.Fields.set (TypeGraph.Fields.set fields p x) q y)
      (TypeGraph.Fields.set (TypeGraph.Fields.set fields q y) p x) := by
  funext V r
  change TypeGraph.Fields.get (TypeGraph.Fields.set (TypeGraph.Fields.set fields p x) q y) r =
    TypeGraph.Fields.get (TypeGraph.Fields.set (TypeGraph.Fields.set fields q y) p x) r
  by_cases atP : r.toNat = p.toNat
  · have sameType : V = T := Field.type_eq r p atP
    cases sameType
    have same : r = p := Field.eq_of_toNat_eq r p atP
    subst r
    rw [TypeGraph.Fields.get_set_other _ q p y different, TypeGraph.Fields.get_set,
      TypeGraph.Fields.get_set]
  · by_cases atQ : r.toNat = q.toNat
    · have sameType : V = U := Field.type_eq r q atQ
      cases sameType
      have same : r = q := Field.eq_of_toNat_eq r q atQ
      subst r
      rw [TypeGraph.Fields.get_set_other _ p q x (Ne.symm different),
        TypeGraph.Fields.get_set, TypeGraph.Fields.get_set]
    · rw [TypeGraph.Fields.get_set_other _ q r y atQ,
        TypeGraph.Fields.get_set_other _ p r x atP,
        TypeGraph.Fields.get_set_other _ p r x atP,
        TypeGraph.Fields.get_set_other _ q r y atQ]

/-- Apply an existing partial value operation to one typed member. -/
def modifyField {n : Nat} {G : Schema n} {fs : List (Name × TypeGraph.Ty n)}
    {T : TypeGraph.Ty n} (fields : TypeGraph.Fields G fs) (p : Field fs T)
    (effect : Value G T → Option (Value G T)) : Option (TypeGraph.Fields G fs) :=
  (effect (TypeGraph.Fields.get fields p)).map (TypeGraph.Fields.set fields p)

/-- Heterogeneous partial member operations commute, including failure. Each
operation reads only its own value and fixed captured parameters. -/
theorem modifyField_commute {n : Nat} {G : Schema n} {fs : List (Name × TypeGraph.Ty n)}
    {T U : TypeGraph.Ty n} (fields : TypeGraph.Fields G fs)
    (p : Field fs T) (q : Field fs U) (different : p.toNat ≠ q.toNat)
    (f : Value G T → Option (Value G T)) (g : Value G U → Option (Value G U)) :
    (modifyField fields p f).bind (fun next => modifyField next q g) =
      (modifyField fields q g).bind (fun next => modifyField next p f) := by
  cases first : f (TypeGraph.Fields.get fields p) with
  | none =>
    cases second : g (TypeGraph.Fields.get fields q) <;>
      simp only [modifyField, first, second, Option.map_none, Option.map_some,
        Option.bind_none, Option.bind_some,
        TypeGraph.Fields.get_set_other fields q p _ different]
  | some x =>
    cases second : g (TypeGraph.Fields.get fields q) with
    | none =>
      simp only [modifyField, first, second, Option.map_none, Option.map_some,
        Option.bind_none, Option.bind_some,
        TypeGraph.Fields.get_set_other fields p q x (Ne.symm different)]
    | some y =>
      simp only [modifyField, first, second, Option.map_some, Option.bind_some,
        TypeGraph.Fields.get_set_other fields p q x (Ne.symm different),
        TypeGraph.Fields.get_set_other fields q p y different]
      exact congrArg some (field_writes_commute fields p q different x y)

/-- The member scheduler equals the existing typed path find/effect/save
sequence for an actual node field. -/
theorem modifyAt_field {n : Nat} {G : Schema n} {i : Fin n} {T : TypeGraph.Ty n}
    (fields : TypeGraph.Fields G (G.fields i)) (p : Field (G.fields i) T)
    (effect : Value G T → Option (Value G T)) :
    modifyAt (.node fields) (.cons (.field p) .nil) effect =
      (modifyField fields p effect).map Value.node := by
  simp only [modifyAt, modifyField, Value.find, Value.save, TypeGraph.Path.read,
    TypeGraph.Path.save, TypeGraph.Step.get, TypeGraph.Step.put,
    Option.bind_eq_bind, Option.bind_some]
  cases effect (TypeGraph.Fields.get fields p) <;> rfl

end Solidity.Backend.StorageOps
