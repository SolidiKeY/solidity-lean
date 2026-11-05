import Solidity.Backend.StorageOps.LifecyclePaths

/-! Actual independent push path certificates; published defaults are explicit,
not replaced by emitted code or an allocation/representation assumption. -/
namespace Solidity.Backend.StorageOps
open TypeGraph

theorem pushAt_operational_readback {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E))
    (pushed : pushAt root pre = some result) : ∃ old value,
      root.find pre = some old ∧ operationPush old = some value ∧ root.save pre value = some result ∧
      result.find pre = some value ∧ value.length.val = old.length.val + 1 ∧
      value.extent.val = max old.extent.val (old.length.val + 1) := by
  obtain ⟨old, value, read, changed, saved⟩ := modifyAt_success root result pre operationPush pushed
  exact ⟨old, value, read, changed, saved, root.find_save result pre value saved,
    operationPush_header old value changed⟩

/-- When allocating beyond retained extent, every suffix sees the exact default
observation, including any failing default suffix. -/
theorem pushAt_fresh_suffix {n : Nat} {G : Schema n} {A E B : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (read : root.find pre = some old) (fresh : old.extent.val = old.length.val)
    (pushed : pushAt root pre = some result) (suffix : TypeGraph.Path G E B) :
    result.find (pre.append (.cons (.index old.length) suffix)) = (Value.dflt E).find suffix := by
  obtain ⟨actual, value, found, changed, _, after, _⟩ := pushAt_operational_readback root result pre pushed
  rw [read] at found
  cases found
  simp only [Value.find, TypeGraph.Path.read_append]
  change (result.find pre).bind (fun v => (TypeGraph.Step.get Value.dflt (.index old.length) v).bind (suffix.read Value.dflt)) = _
  simp only [after, Option.bind_some, operationPush_fresh old value fresh changed]

/-- Scalar retained shadows reset, unlike the existing aggregate reuse law. -/
theorem pushAt_reset_suffix {n : Nat} {G : Schema n} {A E B : TypeGraph.Ty n}
    (root result : Value G A) (pre : TypeGraph.Path G A (.array E)) (old : Value G (.array E))
    (read : root.find pre = some old) (primitive : E.isPrimitive = true)
    (pushed : pushAt root pre = some result) (suffix : TypeGraph.Path G E B) :
    result.find (pre.append (.cons (.index old.length) suffix)) = (Value.dflt E).find suffix := by
  obtain ⟨actual, value, found, changed, _, after, _⟩ := pushAt_operational_readback root result pre pushed
  rw [read] at found
  cases found
  simp only [Value.find, TypeGraph.Path.read_append]
  change (result.find pre).bind (fun v => (TypeGraph.Step.get Value.dflt (.index old.length) v).bind (suffix.read Value.dflt)) = _
  simp only [after, Option.bind_some, operationPush_reset old value primitive changed]

/-- info: 'Solidity.Backend.StorageOps.pushAt_operational_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pushAt_operational_readback
/-- info: 'Solidity.Backend.StorageOps.pushAt_fresh_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pushAt_fresh_suffix
/-- info: 'Solidity.Backend.StorageOps.pushAt_reset_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pushAt_reset_suffix
end Solidity.Backend.StorageOps
