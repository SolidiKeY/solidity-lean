import Solidity.Lowering.V07.LocalFieldSupport
import Solidity.Lowering.V07.RecursiveGraphControls
namespace Solidity.Lowering.V07.LocalFieldSupportChecks
open RecursiveGraph LocalFieldSupport

def names : Fin 1 → Source.DeclName := fun _ => ⟨none,"Node"⟩
def bad : Source.Layout := { (Source.Env.mk []).layout with
  enumSize := fun _ => 2, underlying := fun _ => .enum ⟨none,"Choice"⟩ }
def plain : Source.STy := .array .memory .bool (some 3)
example : (lowerType bad names plain).isSome = true :=
  type_complete (by intro i j h; exact Fin.ext (by omega))
    (.fixed .memory ⟨3,by decide⟩ .bool) True.intro
example : ¬ (∀ d, (PrimitiveGraph.lowerType (bad.underlying d)).isSome = true) := by
  intro all
  have h := all ⟨none,"Unused"⟩
  cases h
example : Supported bad plain := True.intro
example : ¬ Supported bad (.udvt ⟨none,"Used"⟩) := by
  change ¬ (PrimitiveGraph.lowerType (bad.underlying ⟨none,"Used"⟩)).isSome = true
  decide
example : (lowerType bad names (.udvt ⟨none,"Used"⟩)).isNone = true := by decide

def ss : List (String × Source.STy) := [("flag",.bool),("array",plain)]
def ts : List (Name × TypeGraph.Ty 1) := [("flag",.prim .bool),("array",.fixed (.prim .bool) ⟨3,by decide⟩)]
example : (lowerFields bad names ss).isSome = true :=
  fields_complete (ss := ss) (ts := ts)
    (by intro i j h; exact Fin.ext (by omega))
    (.cons rfl .bool (.cons rfl (.fixed .memory ⟨3,by decide⟩ .bool) .nil))
    (by intro s hs; simp only [ss,List.mem_cons,List.not_mem_nil,or_false] at hs
        rcases hs with rfl | rfl <;> exact True.intro)
example : (lowerFields bad names ss).map Subtype.val = some ts := by decide
example : (lowerFields bad names ss).map Subtype.val ≠ some ts.reverse := by decide

-- Referenced UDVTs remain supported when their actual primitive underlying is supported.
def good : Source.Layout := (Source.Env.mk []).layout
example : (lowerType good names (.array .memory (.udvt ⟨none,"Flag"⟩) none)).isSome = true :=
  type_complete (by intro i j h; exact Fin.ext (by omega))
    (.array .memory (.udvt .bool)) rfl
-- This abstract layout witness makes no Source admission claim.
/-- info: [true, true, true, false, true] -/
#guard_msgs in
#eval IO.println (reprStr [(lowerType bad names plain).isSome,(lowerFields bad names ss).isSome,
  (lowerType bad names (.udvt ⟨none,"Used"⟩)).isNone,
  decide ((lowerFields bad names ss).map Subtype.val = some ts.reverse),
  (lowerType good names (.array .memory (.udvt ⟨none,"Flag"⟩) none)).isSome])
end Solidity.Lowering.V07.LocalFieldSupportChecks
