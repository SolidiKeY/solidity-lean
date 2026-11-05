import Solidity.Source.Machine
import Solidity.Backend.StorageOps.SourceSelfCopy

/-! Above-core Source/target self-copy correspondence. The StorageOps core
closure forbids Source imports, so this module sits above it and preserves that
boundary and every typed Source fixture/observation. It is not a production
Source lowering, address compiler, static-call/gas or world-refinement bridge. -/
namespace Solidity.Backend.StorageOps.SourceSelfCopy

/-- This is the actual independent published Source operation, at every
positive existing budget. No heap traversal or Source fuel increase is used. -/
theorem source_self {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (budget : Nat) (τ : Source.STy)
    (storage : τ.loc? = some .storage) (path : Source.SPath) :
    Source.storeVal (E := E) (Γ := Γ) frame (budget+1) τ path (Source.Val.storRef storage path) =
      (pure () : Source.EM E Γ Unit) := by
  simp only [Source.storeVal,if_true]

theorem source_self_state {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (budget : Nat) (τ : Source.STy)
    (storage : τ.loc? = some .storage) (path : Source.SPath)
    (initial : Source.Locals E.layout Γ × Source.St E) :
    (Source.storeVal (E := E) (Γ := Γ) frame (budget+1) τ path (Source.Val.storRef storage path)).run initial =
      (.ok (),initial) := by
  rw [source_self]
  rfl

/-- Zero Source budget is not silently identified with successful target
execution. This preserves the original Source timeout and evaluation budget. -/
theorem source_zero_budget {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (τ : Source.STy) (storage : τ.loc? = some .storage)
    (path : Source.SPath) (initial : Source.Locals E.layout Γ × Source.St E) :
    (Source.storeVal (E := E) (Γ := Γ) frame 0 τ path (Source.Val.storRef storage path)).run initial =
      (.error .timeout,initial) := by
  rfl

/-- Two independently proved actual operation results at captured equal
operands. A Source address compiler or argument evaluator is not assumed
correct by this component, nor is a new representation/state layer created. -/
theorem same_path_components {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (budget : Nat) (τ : Source.STy)
    (storage : τ.loc? = some .storage) (path : Source.SPath)
    (initial : Source.Locals E.layout Γ × Source.St E)
    (machine : Evm.Machine) (slot : Evm.Slot) :
    (Source.storeVal (E := E) (Γ := Γ) frame (budget+1) τ path (Source.Val.storRef storage path)).run initial =
      (.ok (),initial) ∧
    Evm.run TargetNestedArrayCopy.code { machine with stack := .slot slot :: .slot slot :: machine.stack } =
      .ok machine 0 := by
  exact ⟨source_self_state frame budget τ storage path initial,run_self machine machine.stack slot⟩

/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopy.source_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_self

/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopy.source_self_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_self_state

/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopy.source_zero_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_zero_budget

/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopy.same_path_components' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms same_path_components
end Solidity.Backend.StorageOps.SourceSelfCopy

namespace Solidity.Backend.StorageOps.SourceSelfCopyControls

private def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))
private def arraySyntax : Source.Syn .typeName := .array (.array uintSyntax .none) .none
private def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar arraySyntax none none none false "items" .none)
    (.cons (.stateVar arraySyntax none none none false "other" .none) .nil))) .nil)
private def env : Source.Env := unit.env
private def ty : Source.STy := .array .storage (.array .storage (.int Source.IntTy.u256) none) none
private def root : Source.SPath := ⟨⟨some "C","items"⟩,[]⟩
private def other : Source.SPath := ⟨⟨some "C","other"⟩,[]⟩
private def row0 := root.go (.index 0)
private def row1 := root.go (.index 1)
private def row2 := root.go (.index 2)
private def elem00 := row0.go (.index 0)
private def elem01 := row0.go (.index 1)
private def elem10 := row1.go (.index 0)
private def elem20 := row2.go (.index 0)
private def address : Roadmap.Address := ⟨7,by decide⟩
private def storage : Source.Storage env.layout env.cellTy :=
  let s0 : Source.Storage env.layout env.cellTy := Source.Storage.empty
  let s1 : Source.Storage env.layout env.cellTy := s0.write root (.int 2 (by decide))
  let s2 : Source.Storage env.layout env.cellTy := s1.write row0 (.int 1 (by decide))
  let s3 : Source.Storage env.layout env.cellTy := s2.write elem00 (.int 7 (by decide))
  let s4 : Source.Storage env.layout env.cellTy := s3.write elem01 (.int 11 (by decide))
  let s5 : Source.Storage env.layout env.cellTy := s4.write row1 (.int 1 (by decide))
  let s6 : Source.Storage env.layout env.cellTy := s5.write elem10 (.int 17 (by decide))
  let s7 : Source.Storage env.layout env.cellTy := s6.write row2 (.int 1 (by decide))
  s7.write elem20 (.int 71 (by decide))
private def state : Source.St env :=
  { ex :=
      { world := ⟨fun a => if a = address then
          { balance := ⟨19,by decide⟩, nonce := 3, code := some 0, storage := storage }
          else Source.Account.empty _⟩
        transient := Source.Transient.empty
        journal := [] }
    heap := Source.Heap.empty
    events := []
    logs := []
    fnLocals := ⟨[],.nil⟩ }
private def initial : Source.Locals env.layout [] × Source.St env := (.nil,state)
private def frame : Source.Fr :=
  { this := address, sender := ⟨13,by decide⟩, value := ⟨0,by decide⟩,
    static := false, contract := "C" }
private def value (i : Int) (h : Source.IntTy.u256.lo ≤ i ∧ i ≤ Source.IntTy.u256.hi) : Source.Val env.layout (.int Source.IntTy.u256) := .int i h
private def sourceView (s : Source.St env) : List (Option (Source.Val env.layout (.int Source.IntTy.u256))) :=
  [(s.ex.world.accounts address).storage.read root,(s.ex.world.accounts address).storage.read row0,
   (s.ex.world.accounts address).storage.read elem00,(s.ex.world.accounts address).storage.read elem01,
   (s.ex.world.accounts address).storage.read row1,(s.ex.world.accounts address).storage.read elem10,
   (s.ex.world.accounts address).storage.read row2,(s.ex.world.accounts address).storage.read elem20,
   (s.ex.world.accounts address).storage.read other]
private def sourceRun := (Source.storeVal (E := env) (Γ := []) frame 1 ty root (Source.Val.storRef (τ := ty) (by rfl) root)).run initial
private def zeroRun := (Source.storeVal (E := env) (Γ := []) frame 0 ty root (Source.Val.storRef (τ := ty) (by rfl) root)).run initial

private def slot : Evm.Slot := .root 0
private def slots : List Evm.Slot := [slot,.data slot 0,.data (.data slot 0) 0,.data (.data slot 0) 1,
  .data slot 1,.data (.data slot 1) 0,.data slot 2,.data (.data slot 2) 0,.root 1,.root 9]
private def targetStore : Evm.WordStore := .ofFn fun s =>
  if s = slot then 2 else if s = .data slot 0 then 1 else if s = .data (.data slot 0) 0 then 7 else
  if s = .data (.data slot 0) 1 then 11 else if s = .data slot 1 then 1 else if s = .data (.data slot 1) 0 then 17 else
  if s = .data slot 2 then 1 else if s = .data (.data slot 2) 0 then 71 else if s = .root 9 then 99 else 0
private def tail : List Evm.Word := [.val ⟨23,by decide⟩,.slot (.root 9)]
private def machine : Evm.Machine :=
  { stack := tail, store := targetStore, mem := fun _ => .val ⟨31,by decide⟩,
    bal := fun _ => 37, bal₀ := fun _ => 41, self := ⟨43,by decide⟩,
    caller := ⟨47,by decide⟩, callvalue := ⟨0,by decide⟩, timestamp := ⟨53,by decide⟩,
    accepts := fun _ _ => false }
private def targetView (m : Evm.Machine) := slots.map (fun s => m.store s)
private def context (m : Evm.Machine) :=
  (m.stack,m.mem 0,m.bal ⟨0,by decide⟩,m.bal₀ ⟨0,by decide⟩,
   m.self,m.caller,m.callvalue,m.timestamp,m.accepts ⟨0,by decide⟩ ⟨0,by decide⟩)

/-- Both references name actual declared nested storage-array roots. -/
theorem typed_roots : env.pathTy root = some ty ∧ env.pathTy other = some ty ∧ root ≠ other := by
  exact ⟨rfl,rfl,by decide⟩

/-- Exact actual Source and target executions at captured equal operands.
Initial storage is populated, including retained shadows, not an empty state. -/
theorem source_target_self :
    sourceRun = (.ok (),initial) ∧
    Evm.run TargetNestedArrayCopy.code { machine with stack := .slot slot :: .slot slot :: tail } = .ok machine 0 := by
  exact SourceSelfCopy.same_path_components frame 0 ty (by rfl) root initial machine slot

/-- Complete selected Source storage and target/context observations before
and after. The operation also preserves the entire typed Source state. -/
theorem ordered_nontrivial :
    (sourceView state,sourceView sourceRun.2.2,targetView machine,
      targetView (TargetNestedArrayRuntime.afterCopy machine tail slot slot),
      context (TargetNestedArrayRuntime.afterCopy machine tail slot slot),
      sourceRun.2.2.heap.next,sourceRun.2.2.ex.journal.length) =
    ([some (value 2 (by decide)),some (value 1 (by decide)),some (value 7 (by decide)),some (value 11 (by decide)),
      some (value 1 (by decide)),some (value 17 (by decide)),some (value 1 (by decide)),some (value 71 (by decide)),some (value 0 (by decide))],
     [some (value 2 (by decide)),some (value 1 (by decide)),some (value 7 (by decide)),some (value 11 (by decide)),
      some (value 1 (by decide)),some (value 17 (by decide)),some (value 1 (by decide)),some (value 71 (by decide)),some (value 0 (by decide))],
     [2,1,7,11,1,17,1,71,0,99],[2,1,7,11,1,17,1,71,0,99],context machine,0,0) := by
  rw [SourceSelfCopy.nested_after_self]
  rfl

/-- The original Source zero-budget timeout is retained, not assumed success. -/
theorem zero_budget_control : zeroRun = (.error .timeout,initial) ∧ zeroRun.1 ≠ .ok () := by
  refine ⟨SourceSelfCopy.source_zero_budget frame ty (by rfl) root initial,?_⟩
  change (Except.error Source.Halt.timeout : Except Source.Halt Unit) ≠ Except.ok ()
  intro impossible
  cases impossible

/-- Distinct captured storage roots do not take the same-path branch at this unchanged budget. -/
theorem different_path_budget_control :
    (Source.storeVal (E := env) (Γ := []) frame 1 ty root
      (Source.Val.storRef (τ := ty) (by rfl) other)).run initial = (.error .timeout,initial) := by
  rfl

/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopyControls.typed_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms typed_roots
/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopyControls.source_target_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_target_self
/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopyControls.ordered_nontrivial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered_nontrivial
/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopyControls.zero_budget_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms zero_budget_control
/-- info: 'Solidity.Backend.StorageOps.SourceSelfCopyControls.different_path_budget_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms different_path_budget_control
end Solidity.Backend.StorageOps.SourceSelfCopyControls
