import Solidity.Frontend.OverrideValidation.Memoized

/-! Kernel relational/body witnesses and separate executable graph/pruning arm pins. Runtime output is not a kernel proof of that concrete output. -/
namespace Solidity.Frontend.OverrideValidation.Controls
open Solidity.Source


def synList {c : Cat} (xs : List (Syn c)) : Syn (.list c) := xs.foldr Syn.cons .nil

def inherits (xs : List String) : Syn (.list .inherit) :=
  synList (xs.map fun n => .inherit ⟨n, []⟩ .none)

def body (hasReturn : Bool) : Syn (.opt (.block .body)) :=
  .some (.block (if hasReturn then .cons (.stmtItem (.returnStmt .none)) .nil else .nil))

def fn (vis : Visibility) (ov : Option (List IdPath)) (b : Syn (.opt (.block .body))) : Syn (.part false) :=
  .function (.ident "foo") .nil (some vis) (some .view) .nil true ov .nil b

def tree : Syn .unit := .unit (synList [
  .interface "IBase" .nil (synList [fn .external none .none]),
  .contract false "Base" .none (inherits ["IBase"]) (synList [fn .pub none (body false)]),
  .interface "IExt" (inherits ["IBase"]) .nil,
  .contract false "Ext" .none (inherits ["IExt", "Base"]) .nil,
  .contract false "Impl" .none (inherits ["Ext"])
    (synList [fn .pub (some [⟨"IBase", []⟩, ⟨"Base", []⟩]) (body true)])])

def E : Env := tree.env
def impl : Node E := ⟨6, by decide⟩
def request : Node E := ⟨7, by decide⟩
def ifaceFn : Node E := ⟨1, by decide⟩
def baseFn : Node E := ⟨3, by decide⟩

def ext : Node E := ⟨5, by decide⟩
def iext : Node E := ⟨4, by decide⟩
def ibase : Node E := ⟨0, by decide⟩
def base : Node E := ⟨2, by decide⟩

/-- Inhabited relational witnesses, checked by the kernel. -/
theorem nested_frontiers : Frontier E impl request ifaceFn ∧ Frontier E impl request baseFn := by
  constructor
  · refine ⟨ext, ibase, baseEdgeB_iff.mp (by decide), ownMatchingB_iff.mp (by decide), ?_⟩
    exact .step (next := iext) (by decide) (by decide) (shadowStepB_iff.mp (by decide))
      (.step (next := ibase) (by decide) (by decide) (shadowStepB_iff.mp (by decide)) .done)
  · refine ⟨ext, base, baseEdgeB_iff.mp (by decide), ownMatchingB_iff.mp (by decide), ?_⟩
    exact .step (next := base) (by decide) (by decide) (shadowStepB_iff.mp (by decide)) .done

/-- info: [1, 3] -/
#guard_msgs in
#eval (inherited E impl request).map Fin.val

/-- info: false -/
#guard_msgs in
#eval frontierB E impl request request

def emptyBody (d : Decl) : Bool :=
  match d.kind, d.top, d.node with
  | .function, _, .function _ _ _ _ _ _ _ _ (.some (.block .nil)) => true
  | _, _, _ => false

theorem different_implemented_bodies :
    baseFn.decl.hasBody = true ∧ request.decl.hasBody = true ∧ baseFn.decl ≠ request.decl := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  have hb : emptyBody baseFn.decl = emptyBody request.decl := congrArg emptyBody h
  change true = false at hb
  cases hb

theorem distinct_positions : baseFn ≠ request :=
  distinct_decl_distinct_node different_implemented_bodies.2.2

/-- info: 'Solidity.Frontend.OverrideValidation.Controls.nested_frontiers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nested_frontiers
/-- info: 'Solidity.Frontend.OverrideValidation.Controls.different_implemented_bodies' depends on axioms: [propext] -/
#guard_msgs in
#print axioms different_implemented_bodies
/-- info: 'Solidity.Frontend.OverrideValidation.Controls.distinct_positions' depends on axioms: [propext] -/
#guard_msgs in
#print axioms distinct_positions

end Solidity.Frontend.OverrideValidation.Controls

namespace Solidity.Frontend.OverrideValidation.Controls
open Solidity.Source

/-- Each list position corresponds to a concrete edge/vertex arm. -/
def edgeControls : List Bool :=
  [overrideEdgeB E baseFn ifaceFn, overrideEdgeB E ifaceFn baseFn,
   activeB E impl request baseFn, activeB E impl request ifaceFn, activeB E impl request request]

/-- info: [true, false, true, true, false] -/
#guard_msgs in
#eval edgeControls

def adjacencyControls : List Bool :=
  [adjacentB E impl request (realVertex baseFn) (realVertex ifaceFn),
   adjacentB E impl request (realVertex ifaceFn) (realVertex baseFn),
   adjacentB E impl request (rootVertex E) (realVertex baseFn),
   adjacentB E impl request (realVertex baseFn) (rootVertex E),
   adjacentB E impl request (topVertex E) (realVertex ifaceFn),
   adjacentB E impl request (realVertex ifaceFn) (topVertex E),
   adjacentB E impl request (rootVertex E) (topVertex E),
   adjacentB E impl request (topVertex E) (realVertex baseFn),
   adjacentB E impl request (realVertex request) (realVertex ifaceFn)]

/-- info: [true, true, true, true, true, true, false, false, false] -/
#guard_msgs in
#eval adjacencyControls

def avoidingControls : List Bool :=
  [avoidingB E impl request ifaceFn (realVertex baseFn) (realVertex ifaceFn),
   avoidingB E impl request ifaceFn (realVertex ifaceFn) (realVertex baseFn),
   avoidingB E impl request ifaceFn (rootVertex E) (realVertex baseFn)]

/-- info: [false, false, true] -/
#guard_msgs in
#eval avoidingControls

def pruningControls : List Bool :=
  [cutVertexB E impl request ifaceFn, cutVertexB E impl request baseFn,
   cutVertexB E impl request request, retainedB E impl request ifaceFn,
   retainedB E impl request baseFn, retainedB E impl request request]

/-- info: [true, false, false, false, true, false] -/
#guard_msgs in
#eval pruningControls

def tableAdjacencyControls : List Bool :=
  let adj := tableAdjacentB E (overrideFrontierB E impl request) (activeB E impl request) (overrideEdgeB E)
  [adj (realVertex baseFn) (realVertex ifaceFn),
   adj (realVertex ifaceFn) (realVertex baseFn),
   adj (rootVertex E) (realVertex baseFn),
   adj (realVertex baseFn) (rootVertex E),
   adj (topVertex E) (realVertex ifaceFn),
   adj (realVertex ifaceFn) (topVertex E),
   adj (rootVertex E) (topVertex E),
   adj (topVertex E) (realVertex baseFn),
   adj (realVertex request) (realVertex ifaceFn)]

/-- info: [true, true, true, true, true, true, false, false, false] -/
#guard_msgs in
#eval tableAdjacencyControls

def tableControls : List Bool :=
  [tableAdjacentB E (overrideFrontierB E impl request) (activeB E impl request) (overrideEdgeB E)
      (rootVertex E) (realVertex baseFn),
   tableGet (memoRetainedTable E impl request) ifaceFn,
   tableGet (memoRetainedTable E impl request) baseFn,
   tableGet (memoRetainedTable E impl request) request]

/-- info: [true, false, true, false] -/
#guard_msgs in
#eval tableControls

def zero : Fin 2 := ⟨0, by decide⟩
def one : Fin 2 := ⟨1, by decide⟩
def routeControls : List Bool :=
  [routeB (fun _ _ => false) [] zero zero,
   routeB (fun _ _ => false) [] zero one,
   routeB (fun a b => a == zero && b == one) [zero] zero one,
   routeB (fun _ _ => false) [zero] zero one]

/-- info: [true, false, true, false] -/
#guard_msgs in
#eval routeControls

/-- Deliberately invalid cyclic original Source syntax isolates the defensive
proper-descendant pruning arm. GraphValid refuses it; no Solidity acceptance
claim or additional graph representation is introduced. -/
def cutCycle : Env := (Syn.unit (synList [
  .contract false "V" .none (inherits ["F", "G"]) (synList [fn .pub none (body false)]),
  .contract false "F" .none (inherits ["V"]) (synList [fn .pub none (body false)]),
  .contract false "G" .none .nil (synList [fn .pub none (body false)]),
  .contract false "C" .none (inherits ["V", "F"]) .nil])).env

def cycleV : Node cutCycle := ⟨0, by decide⟩
def cycleVF : Node cutCycle := ⟨1, by decide⟩
def cycleF : Node cutCycle := ⟨2, by decide⟩
def cycleFF : Node cutCycle := ⟨3, by decide⟩
def cycleC : Node cutCycle := ⟨6, by decide⟩

theorem cut_cycle_invalid : ¬ GraphValid cutCycle := by
  intro h
  have he : BaseEdge cutCycle cycleV cycleF := baseEdgeB_iff.mp (by decide)
  have hl : cycleF.val < cycleV.val := h.earlier cycleV cycleF he
  exact (by decide : ¬ cycleF.val < cycleV.val) hl

def strictDescendantControls : List Bool :=
  [overrideFrontierB cutCycle cycleC cycleVF cycleFF,
   cutVertexB cutCycle cycleC cycleVF cycleVF,
   routeB (overrideEdgeB cutCycle) (nodes cutCycle) cycleVF cycleFF,
   retainedB cutCycle cycleC cycleVF cycleFF]

/-- info: [true, true, true, false] -/
#guard_msgs in
#eval strictDescendantControls

end Solidity.Frontend.OverrideValidation.Controls

/-- info: 'Solidity.Frontend.OverrideValidation.Controls.cut_cycle_invalid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.Controls.cut_cycle_invalid
