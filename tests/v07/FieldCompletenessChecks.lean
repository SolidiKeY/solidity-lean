import Solidity.Lowering.V07.FieldCompleteness
import Solidity.Lowering.V07.RecursiveGraphControls
namespace Solidity.Lowering.V07.FieldCompletenessChecks
open RecursiveGraph FieldCompleteness

def names : Fin 2 → Source.DeclName := fun i => ⟨none,if i.val = 0 then "Left" else "Right"⟩
def layout : Source.Layout := { (Source.Env.mk []).layout with enumSize := fun _ => 2 }
def nested : Source.STy := .mapping .bool (.array .storage (.struct .storage (names ⟨1,by decide⟩)) (some 3))
def target : TypeGraph.Ty 2 := .mapping .bool (.fixed (.node ⟨1,by decide⟩) ⟨3,by decide⟩)

example : (lowerType layout names nested).isSome = true :=
  complete (by exact (show ∀ i j : Fin 2, names i = names j → i = j by decide)) (by intro d; rfl)
    (.mapping .bool (.fixed .storage ⟨3,by decide⟩ (.node .storage ⟨1,by decide⟩)))
example {T : TypeGraph.Ty 2} (rel : GraphTypeRel layout names nested T) : T = target :=
  functional (by exact (show ∀ i j : Fin 2, names i = names j → i = j by decide)) rel
    (.mapping .bool (.fixed .storage ⟨3,by decide⟩ (.node .storage ⟨1,by decide⟩)))

def sourceFields : List (String × Source.STy) :=
  [("nested",nested),("choice",.enum ⟨none,"Choice"⟩),("flag",.udvt ⟨none,"Flag"⟩)]
def targets : List (Name × TypeGraph.Ty 2) :=
  [("nested",target),("choice",.prim .uint),("flag",.prim .bool)]
example : (lowerFields layout names sourceFields).isSome = true :=
  fields_complete (D := layout) (names := names) (ss := sourceFields) (ts := targets)
    (by exact (show ∀ i j : Fin 2, names i = names j → i = j by decide)) (by intro d; rfl)
    (.cons rfl (.mapping .bool (.fixed .storage ⟨3,by decide⟩ (.node .storage ⟨1,by decide⟩)))
      (.cons rfl (.enum ⟨none,"Choice"⟩ (by decide))
        (.cons rfl (.udvt (.bool)) .nil)))
example : ((lowerFields layout names sourceFields).map Subtype.val) = some targets := by decide
example : ((lowerFields layout names sourceFields).map Subtype.val) ≠ some targets.reverse := by decide

-- Actual published Source environment/ordered fields; no successful compiler run premise.
example : (lowerFields RecursiveGraphControls.chain.layout (PrimitiveGraph.name RecursiveGraphControls.chain)
    (PrimitiveGraph.sourceFields RecursiveGraphControls.chain .memory ⟨0,by decide⟩)).isSome = true :=
  fields_complete (D := RecursiveGraphControls.chain.layout)
    (names := PrimitiveGraph.name RecursiveGraphControls.chain)
    (ts := [("next",.node ⟨1,by decide⟩)])
    (by exact (show PrimitiveGraph.UniqueNames RecursiveGraphControls.chain by decide))
    (by intro d; rfl) (.cons rfl (.node .memory ⟨1,by decide⟩) .nil)

def flagDecl : Source.Decl := ⟨.udvt,"Flag",none,true,.udvt "Flag" .bool⟩
def flagEnv : Source.Env := ⟨[flagDecl]⟩
example : ((lowerType flagEnv.layout names (.udvt ⟨none,"Flag"⟩)).map Subtype.val) =
    some (.prim .bool) := by decide

-- Existing abstract Layout permits more than the primitive UDVT producer.
-- This is a component countermodel, NOT an admitted Source program.
def broader : Source.Layout := { layout with underlying := fun _ => .enum ⟨none,"Choice"⟩ }
example : GraphTypeRel broader names (.udvt ⟨none,"Flag"⟩) (.prim .uint) :=
  .udvt (.enum ⟨none,"Choice"⟩ (by decide))
example : (lowerType broader names (.udvt ⟨none,"Flag"⟩)).isNone = true := by decide
example : ¬ (∀ d, (PrimitiveGraph.lowerType (broader.underlying d)).isSome = true) := by
  intro all
  have bad := all ⟨none,"Flag"⟩
  cases bad
-- Global support is SUFFICIENT, not necessary: unrelated plain fields still lower.
example : (lowerType broader names .bool).isSome = true := by decide

def duplicate : Fin 2 → Source.DeclName := fun _ => ⟨none,"Same"⟩
example : GraphTypeRel layout duplicate (.struct .storage ⟨none,"Same"⟩) (.node ⟨0,by decide⟩) := .node .storage ⟨0,by decide⟩
example : GraphTypeRel layout duplicate (.struct .storage ⟨none,"Same"⟩) (.node ⟨1,by decide⟩) := .node .storage ⟨1,by decide⟩
example : ¬ Function.Injective duplicate := by
  change ¬ (∀ i j : Fin 2, duplicate i = duplicate j → i = j)
  decide
example : (TypeGraph.Ty.node ⟨0,by decide⟩ : TypeGraph.Ty 2) ≠ .node ⟨1,by decide⟩ := by decide

/-- info: [true, true, true, true, true, true, false, false] -/
#guard_msgs in
#eval IO.println (reprStr [(lowerType layout names nested).isSome,
  (lowerFields layout names sourceFields).isSome,
  (lowerType flagEnv.layout names (.udvt ⟨none,"Flag"⟩)).isSome,
  (lowerType broader names (.udvt ⟨none,"Flag"⟩)).isNone,
  (lowerType broader names .bool).isSome,
  decide (((lowerFields layout names sourceFields).map Subtype.val) = some targets),
  decide (((lowerFields layout names sourceFields).map Subtype.val) = some targets.reverse),
  decide (∀ i j : Fin 2, duplicate i = duplicate j → i = j)])
end Solidity.Lowering.V07.FieldCompletenessChecks
