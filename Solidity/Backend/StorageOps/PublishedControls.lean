import Solidity.Backend.StorageOps.PublishedOps
import Solidity.Evm.Correct
import Solidity.Typing.Values

/-! Inhabited certificates for the published fragment, plus concrete preserved
fragment refusals. These are kernel examples, not external solc/EVM executions. -/
namespace Solidity.Backend.StorageOps.PublishedControls
open Solidity Evm

private def C : Contract := { vars := [("flag", .prim .bool), ("items", .array (.prim .bool))] }
private def F : Frag [] := Frag.init []
private def flag : Solidity.Loc C [] (.prim .bool) := .root "flag" rfl
private def items : Solidity.SPath C [] (.array (.prim .bool)) := .loc (.root "items" rfl)
private def truth : Solidity.Val C [] .bool := .simple (.bool true)
private def self : Fin W := ⟨0, W_pos⟩
private def sigma : State C [] := freshT C 0 W_pos self
private def machine : Machine := Machine.init (fun _ => 0) self
private theorem initial_sim : Sim C 1 0 F sigma machine :=
  Sim.init C 0 W_pos (fun _ => 0) self rfl

/-- Accepted reads actually load; accepted writes emit an actual SSTORE. -/
theorem read_accepted : Solidity.Backend.StorageOps.Published.read 0 F flag = some (compileLoc 0 flag ++ [.sload]) := rfl
theorem write_accepted : Solidity.Backend.StorageOps.Published.write 0 F flag truth =
    some (compileVal 0 truth ++ compileLoc 0 flag ++ [.sstore]) := rfl

theorem inhabited_read : ValOutT .bool ((Solidity.Val.read flag).evalT sigma)
    (run (compileLoc 0 flag ++ [.sload]) machine) machine :=
  Solidity.Backend.StorageOps.Published.read_sound flag read_accepted initial_sim

theorem inhabited_write : StmtOut C 1 0 F false false false
    (TRun.assign flag (.val truth) sigma)
    (run (compileVal 0 truth ++ compileLoc 0 flag ++ [.sstore]) machine) machine :=
  Solidity.Backend.StorageOps.Published.write_sound flag truth write_accepted initial_sim

/-- The source operation is successful and changes the value, independently of
its compiler evaluation; hence the inhabited write certificate is non-vacuous. -/
theorem source_write_readback : (TRun.assign flag (.val truth) sigma).map
    (fun out => (Solidity.Val.read flag).evalT out.st) = .ok (.ok true) := rfl

theorem primitive_push_accepted : Solidity.Backend.StorageOps.Published.push 0 F items none = some (pushCode 0 none items) := rfl

theorem inhabited_push : StmtOut C 2 0 F false false false (TRun.push items none sigma)
    (run (pushCode 0 none items) machine) machine :=
  Solidity.Backend.StorageOps.Published.push_sound items none primitive_push_accepted initial_sim (by unfold Lmax; decide)

theorem empty_pop_accepted : Solidity.Backend.StorageOps.Published.pop 0 F items = some (compileSPath 0 items ++ popCode) := rfl

theorem source_empty_pop_reverts : TRun.pop items sigma = .error .revert := by
  simp only [TRun.pop, items, SPath.resolveT, Loc.resolveT, bind, Except.bind,
    Storage.pop, Storage.find, sigma, freshT, Storage.init, SFields.dflt_get,
    SRef.ofRoot, SVal.find_nil, SVal.dflt_array, Option.bind_some,
    SVal.view_array, SVec.toList_nil, List.reverse_nil]
  rfl

/-- Accepted syntax can still fail a runtime check. The actual emitted code
reverts on the independently failing source pop, rather than returning success. -/
theorem target_empty_pop_reverts : run (compileSPath 0 items ++ popCode) machine = .revert := by
  have sound := Solidity.Backend.StorageOps.Published.pop_sound items empty_pop_accepted initial_sim
  rw [source_empty_pop_reverts] at sound
  cases sound with
  | inl h => obtain ⟨out, next, impossible, _⟩ := h; cases impossible
  | inr h => exact h.2
  | panic impossible _ => cases impossible
  | refused impossible _ => cases impossible
  | diverge h => cases h.1

private def aliases : Ctx := [.alias (.array (.prim .bool))]
private def rootAlias : Solidity.SPath C aliases (.array (.prim .bool)) := .loc (.root "items" rfl)
private def dead : Frag aliases := ⟨[.dead]⟩
private def fragile : Frag aliases := ⟨[.fragile]⟩
private def aliasPath : Solidity.SPath C aliases (.array (.prim .bool)) := .alias .here

theorem dead_pop_rejected : Solidity.Backend.StorageOps.Published.pop 0 dead aliasPath = none := rfl
theorem fragile_pop_accepted : Solidity.Backend.StorageOps.Published.pop 0 fragile aliasPath =
    some (compileSPath 0 aliasPath ++ popCode) := rfl
theorem invalidated_pop_rejected : Solidity.Backend.StorageOps.Published.pop 0 fragile.dropFragile aliasPath = none := rfl

theorem rebind_revives : Solidity.Backend.StorageOps.Published.rebind 0 dead .here rootAlias =
    some (⟨[.ok]⟩, compileSPath 0 rootAlias ++ [.mstore (cellOf 0 (.here : Idx aliases _))]) := rfl

theorem dynamic_copy_still_rejected : Solidity.Backend.StorageOps.Published.copy 0 F (.root "items" rfl) items = none :=
  Solidity.Backend.StorageOps.Published.dynamic_copy_rejected _ _

private def D : Contract := { vars := [("a", .fixed (.prim .bool) 2), ("b", .fixed (.prim .bool) 2)] }
private def destination : Solidity.Loc D [] (.fixed (.prim .bool) 2) := .root "a" rfl
private def source : Solidity.SPath D [] (.fixed (.prim .bool) 2) := .loc (.root "b" rfl)
private def copyCode := compileSPath 0 source ++ loadLeaves (leaves (.fixed (.prim .bool) 2)) ++
  [.pop] ++ compileLoc 0 destination ++ storeLeaves (leaves (.fixed (.prim .bool) 2)).reverse ++ [.pop]

theorem static_copy_accepted : Solidity.Backend.StorageOps.Published.copy 0 F destination source = some copyCode := rfl

theorem inhabited_static_copy : StmtOut D 1 0 F false false false
    (TRun.assign destination (.copy source (by decide)) (freshT D 0 W_pos self))
    (run copyCode machine) machine :=
  Solidity.Backend.StorageOps.Published.copy_sound destination source (by decide)
    static_copy_accepted (Sim.init D 0 W_pos (fun _ => 0) self rfl)

theorem delete_accepted : Solidity.Backend.StorageOps.Published.delete 0 F flag =
    some (compileLoc 0 flag ++ zeroCode (leaves (.prim .bool)) ++ [.pop]) := rfl

theorem inhabited_delete : StmtOut C 1 0 F.dropFragile true false false
    (TRun.delete flag sigma)
    (run (compileLoc 0 flag ++ zeroCode (leaves (.prim .bool)) ++ [.pop]) machine) machine :=
  Solidity.Backend.StorageOps.Published.delete_sound flag delete_accepted initial_sim

theorem inhabited_rebind : StmtOut C 1 0 (⟨[.ok]⟩ : Frag aliases) false false false
    (TRun.rebind .here (.path rootAlias) (sigma.push (t := .alias (.array (.prim .bool))) none))
    (run (compileSPath 0 rootAlias ++ [.mstore (cellOf 0 (.here : Idx aliases _))]) machine) machine :=
  Solidity.Backend.StorageOps.Published.rebind_sound .here rootAlias _ rebind_revives
    (initial_sim.pushDead (.array (.prim .bool)) none)

private def seededCopy : State D [] :=
  { (freshT D 0 W_pos self) with storage := (
      .cons (.fixed (.cons (.prim false) (.cons (.prim false) .nil)))
        (.cons (.fixed (.cons (.prim true) (.cons (.prim false) .nil))) .nil)) }
private def seedValue : SVal (.fixed (.prim .bool) 2) :=
  .fixed (.cons (.prim true) (.cons (.prim false) .nil))
private def originalValue : SVal (.fixed (.prim .bool) 2) :=
  .fixed (.cons (.prim false) (.cons (.prim false) .nil))

/-- Discriminating copy control: destination [false,false], source [true,false]. -/
theorem seeded_copy_before : seededCopy.storage.find (.ofRoot "a" rfl) = some originalValue ∧
    seededCopy.storage.find (.ofRoot "b" rfl) = some seedValue := ⟨rfl, rfl⟩

theorem seeded_copy_values_differ : originalValue ≠ seedValue := by intro equal; cases equal

private theorem seeded_overlay : originalValue.overlay seedValue = seedValue := by
  simp only [originalValue, seedValue, SVal.overlay_fixed, SVec.toList_cons,
    SVec.toList_nil, SVec.overlayOn_cons_cons, SVal.overlay_prim, SVec.overlayOn_nil]

theorem seeded_copy_readback :
    (TRun.assign destination (.copy source (by decide)) seededCopy).map
      (fun out => out.st.storage.find (.ofRoot "a" rfl)) = .ok (some seedValue) := by
  change (TRes.ofOpt (seededCopy.storage.save (.ofRoot "a" rfl)
      (originalValue.overlay seedValue))).bind
        (fun st => .ok (st.find (.ofRoot "a" rfl))) = .ok (some seedValue)
  rw [seeded_overlay]
  rfl

/-- Delete follows a real write: retaining the old true value would fail. -/
theorem write_delete_readback : (TRun.assign flag (.val truth) sigma).bind
    (fun out => (TRun.delete flag out.st).map
      (fun final => (Solidity.Val.read flag).evalT final.st)) = .ok (.ok false) := by
  simp only [TRun.assign, TRun.delete, Storage.delete, SVal.defaultOf_eq_defaultOfM]
  rfl

/-- A concrete target combination: after actual SSTORE, SLOAD produces a word
representing true. Both source success and simulation are inhabited. -/
theorem compiled_write_read_combination : ∃ (next : Machine) (w : Word),
    run ((compileVal 0 truth ++ compileLoc 0 flag ++ [.sstore]) ++
      (compileLoc 0 flag ++ [.sload])) machine = .ok (next.push w) 0 ∧
    next.stack = machine.stack ∧ ReprV .bool true w := by
  have sourceExists : ∃ out, TRun.assign flag (.val truth) sigma = .ok out ∧
      (Solidity.Val.read flag).evalT out.st = .ok true := by
    cases result : TRun.assign flag (.val truth) sigma with
    | error halt =>
      have impossible := source_write_readback
      rw [result] at impossible
      cases impossible
    | ok out =>
      refine ⟨out, rfl, ?_⟩
      have observed := source_write_readback
      rw [result] at observed
      exact Except.ok.inj observed
  obtain ⟨out, sourceOK, observed⟩ := sourceExists
  have sound := inhabited_write
  rw [sourceOK] at sound
  cases sound with
  | inl h =>
    obtain ⟨actual, next, equal, targetOK, stack, _, sim⟩ := h
    cases equal
    have readSound := Solidity.Backend.StorageOps.Published.read_sound flag read_accepted sim
    rw [observed] at readSound
    rcases readSound with ⟨v, w, equal, repr, loaded⟩ | ⟨impossible, _⟩
    · cases equal
      exact ⟨next, w, by rw [run_append_ok targetOK]; exact loaded, stack, repr⟩
    · cases impossible
  | inr h => cases h.1
  | panic impossible _ => cases impossible
  | refused impossible _ => cases impossible
  | diverge h => cases h.1

/-- info: 'Solidity.Backend.StorageOps.Published.read_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StorageOps.Published.read_sound
/-- info: 'Solidity.Backend.StorageOps.Published.write_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StorageOps.Published.write_sound
/-- info: 'Solidity.Backend.StorageOps.Published.copy_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StorageOps.Published.copy_sound
/-- info: 'Solidity.Backend.StorageOps.Published.push_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StorageOps.Published.push_sound
/-- info: 'Solidity.Backend.StorageOps.Published.pop_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StorageOps.Published.pop_sound
/-- info: 'Solidity.Backend.StorageOps.Published.delete_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StorageOps.Published.delete_sound
/-- info: 'Solidity.Backend.StorageOps.Published.rebind_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StorageOps.Published.rebind_sound
/-- info: 'Solidity.Backend.StorageOps.Published.dynamic_copy_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.StorageOps.Published.dynamic_copy_rejected

end Solidity.Backend.StorageOps.PublishedControls
