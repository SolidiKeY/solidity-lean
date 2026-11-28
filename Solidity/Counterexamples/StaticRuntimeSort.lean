import Solidity.Typing.Sorts


namespace Solidity
namespace Counterexamples
namespace StaticRuntimeSort

theorem array_runtime_not_le_static :
    ∃ (T : Ty) (v : SVal T), v.keySort.le (T.keySort false) = false :=
  ⟨Ty.ref (RefTy.array Ty.uint), .array .nil .nil SVal.zero_lt_bound, by decide⟩

example {E : Ty} (v : SVal (.ref (.array E))) :
    v.keySort.le ((Ty.ref (.array E)).keySort false) = false ∧
    ((Ty.ref (.array E)).keySort false).le v.keySort = false := by
  cases v
  constructor <;> rfl


example {E : Ty} {n : Nat} (v : SVal (.ref (.fixed E n))) :
    v.keySort.le ((Ty.ref (.fixed E n)).keySort false) = false ∧
    ((Ty.ref (.fixed E n)).keySort false).le v.keySort = false := by
  cases v
  constructor <;> rfl


theorem mapping_runtime_not_le_static :
    ∃ (T : Ty) (v : SVal T), v.keySort.le (T.keySort false) = false :=
  ⟨Ty.ref (RefTy.mapping .uint Ty.uint), .map .nil (.prim (PrimTy.dflt .uint)), by decide⟩

example {K : PrimTy} {V : Ty} (v : SVal (.ref (.mapping K V))) :
    v.keySort.le ((Ty.ref (.mapping K V)).keySort false) = false ∧
    ((Ty.ref (.mapping K V)).keySort false).le v.keySort = false := by
  cases v
  constructor <;> rfl


example : (KeySort.array KeySort.int).le KeySort.struct = false := by decide
example : (KeySort.mapping KeySort.int KeySort.int).le KeySort.struct = false := by decide

example : (SVal.struct (SFields.dflt (Semantics.structDef "Person"))).keySort =
    (Ty.ref (RefTy.struct "Person")).keySort false := rfl

example {s : Name} (v : SVal (.ref (.struct s))) :
    v.keySort = (Ty.ref (.struct s)).keySort false := by
  cases v
  rfl


theorem prim_runtime_eq_static {T : Ty} (hprim : T.isPrimitive = true) (v : SVal T) :
    v.keySort.le (T.keySort false) = true := by
  rw [SVal.keySort_of_primitive hprim v]
  exact KeySort.le_refl _

example : ((Ty.ref (RefTy.array Ty.uint)).keySort false).le KeySort.prim = false := by decide
example : ((Ty.ref (RefTy.mapping .uint Ty.uint)).keySort false).le KeySort.prim = false := by
  decide

example : ((Ty.ref (RefTy.array Ty.uint)).keySort false).le KeySort.stValue = true := by decide

end StaticRuntimeSort
end Counterexamples
end Solidity
