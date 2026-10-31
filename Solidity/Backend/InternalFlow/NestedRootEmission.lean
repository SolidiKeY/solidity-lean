import Solidity.Backend.InternalFlow.RootAdapter

/-!
# A nested consumer of the published local emission checkpoints

This composes actual Local.execute/save calls and records their intermediate
projected roots. It is not source catch, whole-State rollback, arbitrary callee
execution, a new world semantics or compiler simulation.
-/
namespace Solidity.Backend.InternalFlow

open Backend.Failure

/-- Execute an inner failure from deep changes, then an outer emission from
its actual restored result. Retaining the intermediate journal makes early
outer restoration distinguishable from correct inner-entry restoration. -/
def nestedRootEmission {C : Contract} {P T : Ty}
    (persistent : Storage.RegionRoot C false P) (transient : Storage.RegionRoot C true T)
    (outer savedPrefix deep : Storage C) (caller middle machine : Slice.Machine)
    (innerOffset outerOffset : Nat) (innerBytes : List UInt8) (outerInput : Input) :
    Option (Local.Journal (SVal P) (SVal T) × Local.Journal (SVal P) (SVal T) ×
      Roadmap.Outcome × Roadmap.Outcome) := do
  let (restored, innerOutcome) ← Local.execute
    (Local.save (rootJournal persistent transient savedPrefix middle))
    innerOffset (.custom innerBytes) (rootJournal persistent transient deep machine)
  let (final, outerOutcome) ← Local.execute
    (Local.save (rootJournal persistent transient outer caller))
    outerOffset outerInput restored
  pure (restored, final, innerOutcome, outerOutcome)

/-- Inner failure restores the caller-prefix snapshot. Actual outer RETURN
then keeps those roots, writes the outer payload into that restored
memory and keeps both exact observed byte lists. No continuation is assumed. -/
theorem nested_root_return {C : Contract} {P T : Ty}
    (persistent : Storage.RegionRoot C false P) (transient : Storage.RegionRoot C true T)
    (outer savedPrefix deep : Storage C) (caller middle machine : Slice.Machine)
    (a b : Nat) (di do' : List UInt8) (hi : Fits a di) (ho : Fits b do')
    (hs : machine.stack.length + 2 ≤ 1024) (hm : middle.stack.length + 2 ≤ 1024) :
    nestedRootEmission persistent transient outer savedPrefix deep caller middle machine a b di (.returned do') =
      some (rootJournal persistent transient savedPrefix middle,
        rootJournal persistent transient savedPrefix
          { middle with memory := Slice.putBytes middle.memory b do' },
        .revert di, .success do') := by
  unfold nestedRootEmission
  rw [root_failure persistent transient savedPrefix deep middle machine a di hi hs]
  change (do
    let (final, outcome) ← Local.execute
      (Local.save (rootJournal persistent transient outer caller)) b (.returned do')
      (rootJournal persistent transient savedPrefix middle)
    pure (rootJournal persistent transient savedPrefix middle, final, Roadmap.Outcome.revert di, outcome)) = _
  rw [root_return persistent transient outer savedPrefix caller middle b do' ho hm]
  rfl

/-- A later actual outer failure restores the outer-entry roots and caller
machine, even though the inner failure first restored the prefix snapshot. -/
theorem nested_root_failure {C : Contract} {P T : Ty}
    (persistent : Storage.RegionRoot C false P) (transient : Storage.RegionRoot C true T)
    (outer savedPrefix deep : Storage C) (caller middle machine : Slice.Machine)
    (a b : Nat) (di do' : List UInt8) (hi : Fits a di) (ho : Fits b do')
    (hs : machine.stack.length + 2 ≤ 1024) (hm : middle.stack.length + 2 ≤ 1024) :
    nestedRootEmission persistent transient outer savedPrefix deep caller middle machine a b di (.custom do') =
      some (rootJournal persistent transient savedPrefix middle,
        rootJournal persistent transient outer caller, .revert di, .revert do') := by
  unfold nestedRootEmission
  rw [root_failure persistent transient savedPrefix deep middle machine a di hi hs]
  change (do
    let (final, outcome) ← Local.execute
      (Local.save (rootJournal persistent transient outer caller)) b (.custom do')
      (rootJournal persistent transient savedPrefix middle)
    pure (rootJournal persistent transient savedPrefix middle, final, Roadmap.Outcome.revert di, outcome)) = _
  rw [root_failure persistent transient outer savedPrefix caller middle b do' ho hm]
  rfl

namespace NestedRootEmission

def contract : Contract :=
  { vars := [("p", .prim .uint), ("t", .prim .int)]
    transientRoots := ["t"] }
def persistent : Storage.RegionRoot contract false (.prim .uint) := ⟨"p", rfl, rfl⟩
def transient : Storage.RegionRoot contract true (.prim .int) := ⟨"t", rfl, rfl⟩
def one : PrimTy.uint.Denote := ⟨1, rfl⟩
def seven : PrimTy.uint.Denote := ⟨7, rfl⟩
def eleven : PrimTy.uint.Denote := ⟨11, rfl⟩
def minusTwo : PrimTy.int.Denote := ⟨-2, by decide +kernel⟩
def minusNine : PrimTy.int.Denote := ⟨-9, by decide +kernel⟩
def minusThirteen : PrimTy.int.Denote := ⟨-13, by decide +kernel⟩

def outer : Storage contract :=
  ((Storage.init contract).set persistent.declared (.prim one)).set transient.declared (.prim minusTwo)
def prefixStore : Storage contract :=
  (outer.set persistent.declared (.prim seven)).set transient.declared (.prim minusNine)
def deep : Storage contract :=
  (prefixStore.set persistent.declared (.prim eleven)).set transient.declared (.prim minusThirteen)

def caller : Slice.Machine := ⟨[Slice.pushed [0x10], Slice.pushed [0x11]], fun _ => 0x11⟩
def middle : Slice.Machine := ⟨[Slice.pushed [0x2a]], fun _ => 0x22⟩
def machine : Slice.Machine :=
  ⟨[Slice.pushed [0x30], Slice.pushed [0x31], Slice.pushed [0x32]], fun _ => 0x33⟩
def innerBytes : List UInt8 := [0xde, 0xad, 0]
def outerBytes : List UInt8 := [0xbe, 0xef, 1, 0xff]

def roots (journal : Local.Journal (SVal (.prim .uint)) (SVal (.prim .int))) : Int × Int :=
  (journal.persistent.view.1, journal.transient.view.1)

theorem three_snapshots :
    roots (rootJournal persistent transient outer caller) = (1, -2) ∧
    roots (rootJournal persistent transient prefixStore middle) = (7, -9) ∧
    roots (rootJournal persistent transient deep machine) = (11, -13) := ⟨rfl, rfl, rfl⟩

def successRun : Option (Local.Journal (SVal (.prim .uint)) (SVal (.prim .int)) ×
    Local.Journal (SVal (.prim .uint)) (SVal (.prim .int)) × Roadmap.Outcome × Roadmap.Outcome) := nestedRootEmission persistent transient outer prefixStore deep
  caller middle machine 5 9 innerBytes (.returned outerBytes)
def failureRun : Option (Local.Journal (SVal (.prim .uint)) (SVal (.prim .int)) ×
    Local.Journal (SVal (.prim .uint)) (SVal (.prim .int)) × Roadmap.Outcome × Roadmap.Outcome) := nestedRootEmission persistent transient outer prefixStore deep
  caller middle machine 5 9 innerBytes (.custom outerBytes)

theorem success_execution : successRun =
    some (rootJournal persistent transient prefixStore middle,
      rootJournal persistent transient prefixStore
        { middle with memory := Slice.putBytes middle.memory 9 outerBytes },
      .revert innerBytes, .success outerBytes) :=
  nested_root_return persistent transient outer prefixStore deep caller middle machine 5 9 innerBytes outerBytes
    (by unfold Fits; decide +kernel) (by unfold Fits; decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem failure_execution : failureRun =
    some (rootJournal persistent transient prefixStore middle,
      rootJournal persistent transient outer caller, .revert innerBytes, .revert outerBytes) :=
  nested_root_failure persistent transient outer prefixStore deep caller middle machine 5 9 innerBytes outerBytes
    (by unfold Fits; decide +kernel) (by unfold Fits; decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem success_roots_and_bytes :
    successRun.map (fun x => (roots x.1, roots x.2.1, x.2.2.1, x.2.2.2)) =
      some ((7, -9), (7, -9), Roadmap.Outcome.revert innerBytes, Roadmap.Outcome.success outerBytes) := by
  rw [success_execution]
  rfl

/-- Inner bytes survive as a value despite deep memory being discarded;
outer bytes are written only into the restored caller-prefix machine. -/
theorem success_memory_and_stack : successRun.map
    (fun x => (x.1.machine.memory 5, x.2.1.machine.memory 5,
      x.2.1.machine.memory 9, x.2.1.machine.memory 13, x.2.1.machine.stack.map Fin.val)) =
      some (0x22, 0x22, 0xbe, 0x22, [42]) := by
  rw [success_execution]
  rfl

theorem failure_roots_and_bytes :
    failureRun.map (fun x => (roots x.1, roots x.2.1, x.2.2.1, x.2.2.2)) =
      some ((7, -9), (1, -2), Roadmap.Outcome.revert innerBytes, Roadmap.Outcome.revert outerBytes) := by
  rw [failure_execution]
  rfl

theorem failure_memory_and_stack : failureRun.map
    (fun x => (x.1.machine.memory 5, x.2.1.machine.memory 5,
      x.2.1.machine.memory 9, x.2.1.machine.stack.map Fin.val)) =
      some (0x22, 0x11, 0x11, [16, 17]) := by
  rw [failure_execution]
  rfl

theorem no_early_outer_restore : successRun.map (fun x => roots x.1) ≠ some (1, -2) := by
  rw [success_execution]
  intro h
  have impossible : (7 : Int) = 1 := congrArg Prod.fst (Option.some.inj h)
  cases impossible

theorem no_deep_transient_commit : successRun.map (fun x => (roots x.2.1).2) ≠ some (-13) := by
  rw [success_execution]
  intro h
  have impossible : (-9 : Int) = -13 := Option.some.inj h
  cases impossible

theorem outer_failure_cannot_keep_prefix : failureRun.map (fun x => roots x.2.1) ≠ some (7, -9) := by
  rw [failure_execution]
  intro h
  have impossible : (1 : Int) = 7 := congrArg Prod.fst (Option.some.inj h)
  cases impossible

theorem return_is_not_revert : successRun.map (fun x => x.2.2.2) ≠ some (.revert outerBytes) := by
  rw [success_execution]
  intro h
  cases Option.some.inj h

theorem inner_bytes_are_not_outer_bytes :
    successRun.map (fun x => x.2.2.1) ≠ some (.revert outerBytes) := by
  rw [success_execution]
  intro h
  exact (by decide +kernel : innerBytes ≠ outerBytes) (Roadmap.Outcome.revert.inj (Option.some.inj h))



/-- info: 'Solidity.Backend.InternalFlow.nested_root_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_root_return
/-- info: 'Solidity.Backend.InternalFlow.nested_root_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nested_root_failure
/-- info: 'Solidity.Backend.InternalFlow.NestedRootEmission.three_snapshots' depends on axioms: [propext] -/
#guard_msgs in
#print axioms three_snapshots
/-- info: 'Solidity.Backend.InternalFlow.NestedRootEmission.success_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_execution
/-- info: 'Solidity.Backend.InternalFlow.NestedRootEmission.failure_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms failure_execution
/-- info: 'Solidity.Backend.InternalFlow.NestedRootEmission.success_roots_and_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_roots_and_bytes
/-- info: 'Solidity.Backend.InternalFlow.NestedRootEmission.success_memory_and_stack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_memory_and_stack
/-- info: 'Solidity.Backend.InternalFlow.NestedRootEmission.failure_roots_and_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms failure_roots_and_bytes
/-- info: 'Solidity.Backend.InternalFlow.NestedRootEmission.failure_memory_and_stack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms failure_memory_and_stack
/-- info: 'Solidity.Backend.InternalFlow.NestedRootEmission.no_early_outer_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms no_early_outer_restore
/-- info: 'Solidity.Backend.InternalFlow.NestedRootEmission.no_deep_transient_commit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms no_deep_transient_commit
/-- info: 'Solidity.Backend.InternalFlow.NestedRootEmission.outer_failure_cannot_keep_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms outer_failure_cannot_keep_prefix
/-- info: 'Solidity.Backend.InternalFlow.NestedRootEmission.return_is_not_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms return_is_not_revert
/-- info: 'Solidity.Backend.InternalFlow.NestedRootEmission.inner_bytes_are_not_outer_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms inner_bytes_are_not_outer_bytes

end NestedRootEmission
end Solidity.Backend.InternalFlow
