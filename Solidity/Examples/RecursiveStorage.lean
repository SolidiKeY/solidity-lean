import Solidity.Semantics.RecursiveStorage.Arrays

/-! Kernel examples for the standalone graph storage API. These are not
ordinary Contract/Stmt or solc_import programs; that migration is pending. -/

namespace Solidity.TypeGraph.Examples

private def zero : Fin 1 := ⟨0, by decide⟩
private def uint (n : Nat) : PrimTy.uint.Denote := ⟨(n % 2 ^ 256 : Nat), by
  simp only [PrimTy.inRange, decide_eq_true_eq]
  have h : n % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt n (by decide)
  omega⟩

private def mappingFields : List (Name × Ty 1) :=
  [("value", .prim .uint), ("next", .mapping .uint (.node zero))]

def mappingSchema : Schema 1 where
  origin := "recursive-storage-example"
  declId := fun _ => 1
  declId_injective := by intro i j _; apply Fin.ext; omega
  name := fun _ => "MapNode"
  fields := fun _ => mappingFields
  rank := fun _ => 1
  nonempty := fun _ => rfl
  distinct := fun _ => rfl
  guarded := by
    intro i f hf
    simp only [mappingFields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact Nat.zero_lt_succ 0

private def scalar : Path mappingSchema (.node zero) (.prim .uint) :=
  .cons (.field .here) .nil

def deep : Nat → Path mappingSchema (.node zero) (.prim .uint)
  | 0 => scalar
  | n + 1 => .cons (.field (.there .here)) (.cons (.key (uint 1)) (deep n))

def empty : Value mappingSchema (.node zero) := Value.dflt _

example : empty.observe (deep 64) = some (uint 0) := rfl
theorem empty_deep (n : Nat) : empty.observe (deep n) = some (uint 0) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
example : (empty.save (deep 3) (.prim (uint 7))).map (fun v => v.observe (deep 3)) =
    some (some (uint 7)) := rfl
example : (empty.save (deep 3) (.prim (uint 7))).map (fun v => v.observe (deep 2)) =
    some (some (uint 0)) := rfl
example : (empty.save (deep 3) (.prim (uint 7))).map (fun v => v.clear.observe (deep 3)) =
    some (some (uint 7)) := rfl

private def arrayFields : List (Name × Ty 1) :=
  [("value", .prim .uint), ("children", .array (.node zero))]

def arraySchema : Schema 1 where
  origin := "recursive-array-example"
  declId := fun _ => 2
  declId_injective := by intro i j _; apply Fin.ext; omega
  name := fun _ => "Node"
  fields := fun _ => arrayFields
  rank := fun _ => 1
  nonempty := fun _ => rfl
  distinct := fun _ => rfl
  guarded := by
    intro i f hf
    simp only [arrayFields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact Nat.zero_lt_succ 0

private def idx0 : Index := ⟨0, by decide⟩
private def nodeValue : Path arraySchema (.node zero) (.prim .uint) :=
  .cons (.field .here) .nil
private def atValue : Path arraySchema (.array (.node zero)) (.prim .uint) :=
  .cons (.index idx0) nodeValue
private def start : Value arraySchema (.array (.node zero)) :=
  .array ⟨1, by decide⟩ ⟨1, by decide⟩ (Nat.le_refl 1) (fun _ => .absent)

private def recycled : Option (Value arraySchema (.array (.node zero))) := do
  let v ← start.pop
  let v ← v.save atValue (.prim (uint 7))
  v.push

example : (Value.dflt (.array (.node zero)) : Value arraySchema _).observe atValue = none := rfl
example : start.observe atValue = some (uint 0) := rfl
example : start.pop.map (fun v => v.observe atValue) = some (some (uint 0)) := rfl
example : start.pop.map (fun v => (atValue.readLive Value.dflt v).map Value.head) = some none := rfl
example : recycled.map (fun v => v.observe atValue) = some (some (uint 7)) := rfl
example : recycled.map (fun v => v.observe atValue) ≠ some (some (uint 0)) := by
  change (some (some (uint 7)) : Option (Option PrimTy.uint.Denote)) ≠ some (some (uint 0))
  decide

-- The legal schema certificate rules out source-invalid direct/fixed cycles.
example (G : Schema 1) (f : Name) (h : (f, .node zero) ∈ G.fields zero) : False :=
  G.no_inline_self h .node

private def mutualFields (i : Fin 2) : List (Name × Ty 2) :=
  [("next", .array (.node ⟨1 - i.val, by have hi := i.isLt; omega⟩))]

def mutualSchema : Schema 2 where
  origin := "mutual-array-example"
  declId := Fin.val
  declId_injective := fun _ _ h => Fin.ext h
  name := fun i => if i.val = 0 then "A" else "B"
  fields := mutualFields
  rank := fun _ => 1
  nonempty := fun _ => rfl
  distinct := fun _ => rfl
  guarded := by
    intro i f hf
    simp only [mutualFields, List.mem_singleton] at hf
    subst f
    exact Nat.zero_lt_succ 0

private def rawIndex (i : Index) :
    Path mappingSchema (.array (.prim .uint)) (.prim .uint) := .cons (.index i) .nil
private def idx1 : Index := ⟨1, by decide⟩

private def mutualRoot : Value mutualSchema (.node ⟨0, by decide⟩) :=
  .node (fun p => match p with
    | .here => .array ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide) (fun _ => .present
      (.node (fun p => match p with
        | .here => .array ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide) (fun _ => .present
          (Value.dflt (.node ⟨0, by decide⟩)))))))

private def mutualPath : Path mutualSchema (.node ⟨0, by decide⟩)
    (.array (.node ⟨1, by decide⟩)) :=
  .cons (.field .here) (.cons (.index idx0)
    (.cons (.field .here) (.cons (.index idx0) (.cons (.field .here) .nil))))

example : mutualRoot.observe mutualPath = some (⟨0, by decide⟩, ⟨0, by decide⟩) := rfl
example : (mutualRoot.save mutualPath (.array ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide)
    (fun _ => .absent))).map (fun v => v.observe mutualPath) =
    some (some (⟨1, by decide⟩, ⟨1, by decide⟩)) := rfl

private def withShadow : Value mappingSchema (.array (.prim .uint)) :=
  .array ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide)
    (fun i => .present (.prim (uint (if i.val = 0 then 9 else 7))))

example : withShadow.pop.map (fun v => v.observe (rawIndex idx0)) =
    some (some (uint 0)) := rfl
example : withShadow.pop.map (fun v => v.observe (rawIndex idx1)) =
    some (some (uint 7)) := rfl

private def primitiveReuse : Option (Value mappingSchema (.array (.prim .uint))) := do
  let v ← withShadow.pop
  let v ← v.save (rawIndex idx0) (.prim (uint 7))
  v.push

example : primitiveReuse.map (fun v => v.observe (rawIndex idx0)) =
    some (some (uint 0)) := rfl

private def mkNode (v : Nat) (children : Value arraySchema (.array (.node zero))) :
    Value arraySchema (.node zero) :=
  .node (fun p => match p with
    | .here => .prim (uint v)
    | .there .here => children)

private def populatedTree : Value arraySchema (.node zero) :=
  mkNode 5 (.array ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide) (fun _ => .present
    (mkNode 7 (.array ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide) (fun _ => .present
      (mkNode 9 (Value.dflt _)))))))

private def grandchildValue : Path arraySchema (.node zero) (.prim .uint) :=
  .cons (.field (.there .here)) (.cons (.index idx0)
    (.cons (.field (.there .here)) (.cons (.index idx0) nodeValue)))

example : populatedTree.observe grandchildValue = some (uint 9) := rfl
example : populatedTree.clear.observe nodeValue = some (uint 0) := rfl
example : populatedTree.clear.observe grandchildValue = some (uint 0) := rfl
example : populatedTree.clear.observe (.cons (.field (.there .here)) .nil) =
    some (⟨0, by decide⟩, ⟨1, by decide⟩) := rfl

private def nestedShadow : Value mappingSchema (.array (.array (.prim .uint))) :=
  .array ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide)
    (fun _ => .present (.array ⟨2, by decide⟩ ⟨2, by decide⟩ (by decide) (fun _ => .absent)))

example : nestedShadow.clear.observe (.cons (.index idx0) .nil) =
    some (⟨2, by decide⟩, ⟨2, by decide⟩) := rfl
example : nestedShadow.push.map (fun v => v.observe (.cons (.index idx0) .nil)) =
    some (some (⟨2, by decide⟩, ⟨2, by decide⟩)) := rfl

private def fixedMapPath :
    Path mappingSchema (.fixed (.mapping .uint (.node zero)) ⟨1, by decide⟩) (.prim .uint) :=
  .cons (.fixed idx0) (.cons (.key (uint 1)) scalar)

example : ((Value.dflt _ : Value mappingSchema _).save fixedMapPath (.prim (uint 7))).map
    (fun v => v.clear.observe fixedMapPath) = some (some (uint 7)) := rfl

example : (Slot.absent : Slot mappingSchema (.prim .uint)) ≠
    Slot.present (Value.dflt _) := fun h => Slot.noConfusion h

#print axioms Schema.no_inline_cycle
#print axioms Path.read_save
#print axioms Value.clear_idem
#print axioms Value.clear_dflt

end Solidity.TypeGraph.Examples
