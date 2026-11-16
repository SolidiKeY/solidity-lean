import Solidity.Yul.Views.NestedMappingLayout
import Solidity.Backend.StorageOps.ProducerInterface

/-! Typed endpoint bridge for ordinary Source recursive uint256-key mappings.

Checked Source declaration/path metadata determines the existing public graph
slot endpoint. This supplies neither Source value adequacy, selected-code
provenance nor a reached execution. It reuses the graph/producer interface;
there is no second state or path syntax. NestedMappingLayout retains its imports.
Solidity.lean includes this separate module in the default full-library build.

H171 accepts the reviewed import cost only, superseding H164 Option A for that
increment. Its recorded fresh bounded matched check used Lean 4.24.0, one thread,
12 GiB/no swap and 300 seconds per file: median 0.38 s baseline versus 0.82 s
candidate (+115.8%), peak VmHWM 458,176 versus 1,089,336 KiB. This is accepted
cost, not speed neutrality or a full-build timing result. Ordinary validation
and integration gates, existing budgets and every adequacy obligation remain.

H189 separately releases the H125 Horizon timing STOP only. It supplies no
successful Source, cache, per-file or full-build validation receipt and changes
no proof/resource budget. No distinct VY2 Horizon failure is asserted here;
any new failure requires its exact source head, command and bounded receipt.
Historical measurement evidence stays private under H145; missing historical
artifacts remain UNVERIFIABLE under H151 and receive no proof credit.
-/
namespace Solidity.Yul.Views

/-- Typed graph image of the existing recursive word-key layout. This adapter
uses the public graph constructors, without introducing a second path syntax. -/
def nestedMappingGraphType (n : Nat) : Nat → TypeGraph.Ty n
  | 0 => .prim .uint
  | depth+1 => .mapping .uint (nestedMappingGraphType n depth)

def nestedMappingGraphKey (key : Roadmap.Word) : PrimTy.uint.Denote :=
  ⟨(key.val : Int), by
    simp only [PrimTy.inRange,decide_eq_true_eq]
    have bound := key.isLt
    omega⟩

theorem nestedMappingGraphKey_word (key : Roadmap.Word) :
    Storage.Representation.keyWord (nestedMappingGraphKey key)=key.val := by rfl

def nestedMappingGraphPath {n : Nat} (G : TypeGraph.Schema n) :
    (keys : List Roadmap.Word) → TypeGraph.Path G
      (nestedMappingGraphType n keys.length) (.prim .uint)
  | [] => .nil
  | key::keys => .cons (.key (nestedMappingGraphKey key)) (nestedMappingGraphPath G keys)

theorem nestedMappingGraphPath_location {n : Nat} (G : TypeGraph.Schema n)
    (keys : List Roadmap.Word) (base : Storage.Loc) :
    Storage.Representation.Graph.pathLoc (nestedMappingGraphPath G keys) base=
      nestedMappingLocation base keys := by
  induction keys generalizing base with
  | nil => rfl
  | cons key keys ih =>
    exact ih (.hash key.val base 0)

theorem nestedMappingGraphPath_supported {n : Nat} (G : TypeGraph.Schema n)
    (keys : List Roadmap.Word) :
    Storage.Representation.Graph.PathSupported (nestedMappingGraphPath G keys) := by
  induction keys with
  | nil => trivial
  | cons key keys ih => exact ⟨True.intro,ih⟩

/-- Checked ordinary Source declaration/path metadata yields the public typed
path endpoint at its existing root0 placement. Slot identity is derived, not
assumed. This does not assert Source liveness, value representation, compiler
selection, numeric-store transport or an actual reached execution. -/
theorem NestedWordMappingRoot.graph_path_endpoint {E root}
    (mapping : NestedWordMappingRoot E root) (fixed : Roadmap.Evm.Fixed)
    (keys : mapping.Keys) {n : Nat} (G : TypeGraph.Schema n) :
    ∃ slot : Evm.Slot,
      Backend.StorageOps.ProducerInterface.PathEndpoint (nestedMappingGraphPath G keys.val)
        (.root 0) slot ∧
      Storage.ofSlot slot=(mapping.entry fixed keys).location := by
  let path := nestedMappingGraphPath G keys.val
  have fits : Backend.StorageOps.TargetOperations.KeysFit (.root 0) := True.intro
  refine ⟨Backend.StorageOps.TargetOperations.toSlot
    (Storage.Representation.Graph.pathLoc path (.root 0))
    (Backend.StorageOps.TargetOperations.path_keysFit path (.root 0) fits),?_,?_⟩
  · exact ⟨nestedMappingGraphPath_supported G keys.val,fits,rfl⟩
  · rw [Backend.StorageOps.TargetOperations.ofSlot_toSlot]
    exact nestedMappingGraphPath_location G keys.val (.root 0)


end Solidity.Yul.Views
