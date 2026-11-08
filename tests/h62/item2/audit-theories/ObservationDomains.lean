import tests.h62.item2.«audit-theories».PathWitnesses

/-! Joint extensionality inputs with inhabited word and array-length domains.
These are abstract Obs inputs; no storage realization or compiler execution is
claimed. The selected length is one, and both locations are observed as present. -/
namespace H62.AuditTheories
open Solidity

/-- A nonempty array observation supplies both an array root and a word path. -/
def populatedArrayObs : Obs (Path (.ref (.array (.prim .bool)))) where
  word := fun {P} _ => PrimTy.dflt P
  len := fun _ => 1
  has := fun _ => true

/-- All three extensionality hypotheses coexist with concrete locations in
both quantified domains, and actual word/length/presence observations. -/
theorem obs_ext_populated_joint_witness :
    ∃ (L : Ty → Type) (o o' : Obs L) (word : L (.prim .bool))
      (E : Ty) (len : L (.ref (.array E))),
      (∀ {P : PrimTy} (q : L (.prim P)), o.word q = o'.word q) ∧
      (∀ {T : Ty} (q : L (.ref (.array T))), o.len q = o'.len q) ∧
      (∀ {T : Ty} (q : L T), o.has q = o'.has q) ∧
      o.word word = false ∧ o.len len = 1 ∧
      o.has word = true ∧ o.has len = true :=
  ⟨Path (.ref (.array (.prim .bool))), populatedArrayObs, populatedArrayObs,
    .at (uintOfNat 0) .nil, .prim .bool, .nil,
    (fun _ => rfl), (fun _ => rfl), (fun _ => rfl), rfl, rfl, rfl, rfl⟩

#print axioms obs_ext_populated_joint_witness
end H62.AuditTheories
