import Solidity.Yul.Views.NestedMappingLayout
import Solidity.Backend.StorageOps.ProducerInterface

/-! Typed endpoint bridge for ordinary Source recursive uint256-key mappings.

Regression boundary: a checked Source path must reach the symbolic slot of the
existing public graph path. This module supplies slot identity only, not Source
value adequacy, selected-code provenance or a reached execution. It instantiates
the existing graph/producer interface without a second state or path syntax.

The bridge is isolated: NestedMappingLayout retains its original imports.
Historical H126 measurements: Lean 4.24.0, serial LEAN_NUM_THREADS=1
on the existing 12 GiB/no-swap VM:
three import-only checks have median 0.54 s, peak VmHWM 1,050,020 KiB.
The existing layout-only import has median 0.18 s (423,856 KiB peak): this
separate producer dependency costs 0.36 s and is not a speed-neutral replacement.
NestedMappingLayout itself is byte-identical; its checks remain 0.40 s median
versus the pre-extraction 0.43 s sample. H171 later accepts the reviewed import
cost only, subject to fresh bounded measurement and ordinary integration gates;
it supersedes Option A for that increment. Fresh matched external copies checked
at median 0.38 s baseline versus 0.82 s with the exact historical import patch
(+115.8%); this is accepted cost, not speed neutrality. NestedMappingLayout
retains its original imports and the separate Horizon STOP is unchanged. Solidity.lean registers
this module in the default full-library build: isolation protects the layout's
import closure, not default-build membership. The import-only comparison does
not measure the full-build delta.
Raw measurements are H44 external VM artifacts at
/workspace/vy2-evidence/source-graph-production/, not repository files.
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
