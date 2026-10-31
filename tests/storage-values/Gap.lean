import Solidity.Storage.HashedSeparation
import Solidity.Semantics.Storage.Ops

/-! A runnable baseline control importing only the exact base interfaces.
The base has no represented-store/value relation; separation alone cannot
state that this independent source read agrees with a store word. -/
namespace Solidity.Storage.RepresentationGap
private def seven : PrimTy.uint.Denote := ⟨7, by decide⟩
private def nine : PrimTy.uint.Denote := ⟨9, by decide⟩
private def mapValue : SVal (.ref (.mapping .bool Ty.uint)) :=
  .map (.cons true (.prim nine) .nil) (.prim seven)
theorem written : mapValue.find (.key true .nil) = some (.prim nine) := by
  simp only [mapValue, SVal.find_key, SVal.find_nil, SMap.toList_cons, SMap.toList_nil,
    Semantics.lookupBy, if_true]
theorem untouched : mapValue.find (.key false .nil) = some (.prim seven) := by
  simp only [mapValue, SVal.find_key, SVal.find_nil, SMap.toList_cons, SMap.toList_nil,
    Semantics.lookupBy, if_neg Bool.false_ne_true]
end Solidity.Storage.RepresentationGap
