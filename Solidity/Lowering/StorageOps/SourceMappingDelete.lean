import Solidity.Source.Machine

/-! Upper-layer exact Source mapping-barrier deletion progress. These laws
use the actual Source operations; they do not assert compiler/world closure. -/
namespace Solidity.Backend.StorageOps.SourceMappingDelete

theorem mapping_delete {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (budget : Nat) (key value : Source.STy) (path : Source.SPath) :
    Source.deleteStor (E := E) (Γ := Γ) frame (budget + 1) (.mapping key value) path = pure () := by
  rfl

/-- Every runtime element is visited using the existing Source recursion.
Mapping barriers preserve the entire state, even when fuel is insufficient. -/
theorem mapping_range {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (budget : Nat) (key value : Source.STy)
    (path : Source.SPath) (start count : Nat) :
    Source.deleteRange (E := E) (Γ := Γ) frame budget (.mapping key value) path start count =
      if count < budget then pure () else Source.EM.halt .timeout := by
  induction budget generalizing start count with
  | zero => simp only [Source.deleteRange,Nat.not_lt_zero,if_false]
  | succ budget ih =>
    cases count with
    | zero => simp only [Source.deleteRange,Nat.zero_lt_succ,if_true]
    | succ count =>
      cases budget with
      | zero =>
        simp only [Source.deleteRange,Source.deleteStor,Nat.succ_lt_succ_iff,Nat.not_lt_zero,if_false]
        rfl
      | succ budget =>
        simp only [Source.deleteRange,mapping_delete,pure_bind,ih,Nat.succ_lt_succ_iff]

theorem mapping_range_state {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (budget : Nat) (key value : Source.STy)
    (path : Source.SPath) (start count : Nat)
    (initial : Source.Locals E.layout Γ × Source.St E) :
    (Source.deleteRange frame budget (.mapping key value) path start count).run initial =
      (if count < budget then .ok () else .error .timeout,initial) := by
  rw [mapping_range]
  split <;> rfl

/-- Dynamic deletion visits its actual runtime length, retaining the original
read/type/static behavior and clearing the header only after successful range traversal. -/
theorem mapping_array_delete {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (budget : Nat) (key value : Source.STy) (path : Source.SPath) :
    Source.deleteStor (E := E) (Γ := Γ) frame (budget + 1)
      (.array .storage (.mapping key value) none) path = (do
        let count ← Source.readLen frame path
        (if count < budget then pure () else Source.EM.halt .timeout)
        Source.setCell frame path none) := by
  simp only [Source.deleteStor,mapping_range]

namespace Controls
private def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))
private def mapSyntax : Source.Syn .typeName :=
  .mapping (.elem (.int false 256 (by decide)) (by decide)) none uintSyntax none
private def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.array mapSyntax .none) none none none false "maps" .none)
    (.cons (.stateVar (.array uintSyntax .none) none none none false "values" .none)
      (.cons (.stateVar uintSyntax none none none false "sentinel" .none) .nil)))) .nil)
private def env : Source.Env := unit.env
private def uint : Source.STy := .int Source.IntTy.u256
private def mapTy : Source.STy := .mapping uint uint
private def ty : Source.STy := .array .storage mapTy none
private def root : Source.SPath := ⟨⟨some "C","maps"⟩,[]⟩
private def scalar : Source.SPath := ⟨⟨some "C","values"⟩,[]⟩
private def sentinel : Source.SPath := ⟨⟨some "C","sentinel"⟩,[]⟩
private def key (i : Nat) : Source.SPath := (root.go (.index i)).go (.key (List.replicate 32 0))
private def elem (i : Nat) : Source.SPath := scalar.go (.index i)
private def address : Roadmap.Address := ⟨7,by decide⟩
private def storage : Source.Storage env.layout env.cellTy :=
  let s0 : Source.Storage env.layout env.cellTy := Source.Storage.empty
  let s1 : Source.Storage env.layout env.cellTy := s0.write root (.int 2 (by decide))
  let s2 : Source.Storage env.layout env.cellTy := s1.write (key 0) (.int 7 (by decide))
  let s3 : Source.Storage env.layout env.cellTy := s2.write (key 1) (.int 17 (by decide))
  let s4 : Source.Storage env.layout env.cellTy := s3.write (key 2) (.int 71 (by decide))
  let s5 : Source.Storage env.layout env.cellTy := s4.write sentinel (.int 99 (by decide))
  let s6 : Source.Storage env.layout env.cellTy := s5.write scalar (.int 2 (by decide))
  let s7 : Source.Storage env.layout env.cellTy := s6.write (elem 0) (.int 53 (by decide))
  let s8 : Source.Storage env.layout env.cellTy := s7.write (elem 1) (.int 59 (by decide))
  s8.write (elem 2) (.int 61 (by decide))
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
private def paths : List Source.SPath := [root,key 0,key 1,key 2,sentinel,scalar,elem 0,elem 1,elem 2]
private def view (s : Source.St env) : List (Option (Source.Val env.layout uint)) :=
  [(s.ex.world.accounts address).storage.read root,
   (s.ex.world.accounts address).storage.read (key 0),
   (s.ex.world.accounts address).storage.read (key 1),
   (s.ex.world.accounts address).storage.read (key 2),
   (s.ex.world.accounts address).storage.read sentinel,
   (s.ex.world.accounts address).storage.read scalar,
   (s.ex.world.accounts address).storage.read (elem 0),
   (s.ex.world.accounts address).storage.read (elem 1),
   (s.ex.world.accounts address).storage.read (elem 2)]
private def value (i : Int) (h : Source.IntTy.u256.lo ≤ i ∧ i ≤ Source.IntTy.u256.hi) : Source.Val env.layout uint := .int i h
private def deleted := (Source.deleteStor (E := env) (Γ := []) frame 4 ty root).run initial
private def tooShort := (Source.deleteStor (E := env) (Γ := []) frame 2 ty root).run initial
private def refused := (Source.deleteStor (E := env) (Γ := []) {frame with static := true} 4 ty root).run initial
private def prefixRun := (Source.deleteRange (E := env) (Γ := []) frame 2 uint scalar 0 2).run initial
private def regrown := (Source.writeLen (E := env) (Γ := []) frame root 2).run deleted.2
private def emptyDeleted := (Source.deleteStor (E := env) (Γ := []) frame 4 ty root).run deleted.2
private def erased := (Source.setCell (E := env) (Γ := []) frame (key 0) none).run deleted.2

theorem typed_paths : env.pathTy root = some ty ∧ env.pathTy scalar = some (.array .storage uint none) ∧
    env.pathTy (key 0) = some uint ∧ env.pathTy (key 2) = some uint := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem deletion_result : deleted.1 = .ok () ∧ tooShort = (.error .timeout,initial) ∧
    refused = (.error (.revert []),initial) := by
  exact ⟨rfl,rfl,rfl⟩

/-- Complete ordered storage observations include live mapping cells, a retained
older cell, an unrelated scalar array and a sentinel. -/
theorem ordered_delete :
    (view state,view deleted.2.2,deleted.2.2.ex.journal.length,
     deleted.2.2.heap.next,deleted.2.2.events.length,deleted.2.2.logs.length) =
    ([some (value 2 (by decide)),some (value 7 (by decide)),some (value 17 (by decide)),some (value 71 (by decide)),some (value 99 (by decide)),some (value 2 (by decide)),some (value 53 (by decide)),some (value 59 (by decide)),some (value 61 (by decide))],
     [some (value 0 (by decide)),some (value 7 (by decide)),some (value 17 (by decide)),some (value 71 (by decide)),some (value 99 (by decide)),some (value 2 (by decide)),some (value 53 (by decide)),some (value 59 (by decide)),some (value 61 (by decide))],1,0,0,0) := by
  rfl

/-- Actual Source timeout after one scalar write keeps that prefix; no rollback follows. -/
theorem timeout_prefix :
    (prefixRun.1,view prefixRun.2.2,prefixRun.2.2.ex.journal.length) =
    (.error .timeout,[some (value 2 (by decide)),some (value 7 (by decide)),some (value 17 (by decide)),some (value 71 (by decide)),some (value 99 (by decide)),some (value 2 (by decide)),some (value 0 (by decide)),some (value 59 (by decide)),some (value 61 (by decide))],1) := by
  rfl

/-- A real wrong mapping-cell clear is observable, rather than silently accepted as array deletion. -/
theorem wrong_erasure :
    (view erased.2.2,erased.2.2.ex.journal.length) =
    ([some (value 0 (by decide)),some (value 0 (by decide)),some (value 17 (by decide)),some (value 71 (by decide)),some (value 99 (by decide)),some (value 2 (by decide)),some (value 53 (by decide)),some (value 59 (by decide)),some (value 61 (by decide))],2) := by
  rfl
/-- Deleting an already-empty header preserves retained mapping aliases; regrowth
exposes their old entries again. These are Source retained-path reads, not readLive. -/
theorem reuse_observations :
    (emptyDeleted.1,view emptyDeleted.2.2,emptyDeleted.2.2.ex.journal.length,
      regrown.1,view regrown.2.2,regrown.2.2.ex.journal.length) =
    (.ok (),[some (value 0 (by decide)),some (value 7 (by decide)),some (value 17 (by decide)),some (value 71 (by decide)),some (value 99 (by decide)),some (value 2 (by decide)),some (value 53 (by decide)),some (value 59 (by decide)),some (value 61 (by decide))],2,
     .ok (),[some (value 2 (by decide)),some (value 7 (by decide)),some (value 17 (by decide)),some (value 71 (by decide)),some (value 99 (by decide)),some (value 2 (by decide)),some (value 53 (by decide)),some (value 59 (by decide)),some (value 61 (by decide))],2) := by
  rfl

/-- An actual halted Source computation need not restore its input state. -/
theorem timeout_not_rollback : prefixRun.2 ≠ initial := by
  intro same
  have impossible := congrArg (fun s => ((Source.readLen (E := env) (Γ := []) frame (elem 0)).run s).1) same
  change (Except.ok 0 : Except Source.Halt Nat) = Except.ok 53 at impossible
  cases impossible

/-- Mapping erasure changes an actual typed Source read. -/
theorem wrong_erasure_distinct : erased.2 ≠ deleted.2 := by
  intro same
  have impossible := congrArg (fun s => ((Source.readLen (E := env) (Γ := []) frame (key 0)).run s).1) same
  change (Except.ok 0 : Except Source.Halt Nat) = Except.ok 7 at impossible
  cases impossible

end Controls

/-- info: 'Solidity.Backend.StorageOps.SourceMappingDelete.mapping_delete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_delete

/-- info: 'Solidity.Backend.StorageOps.SourceMappingDelete.mapping_range' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_range

/-- info: 'Solidity.Backend.StorageOps.SourceMappingDelete.mapping_range_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_range_state

/-- info: 'Solidity.Backend.StorageOps.SourceMappingDelete.mapping_array_delete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mapping_array_delete

/-- info: 'Solidity.Backend.StorageOps.SourceMappingDelete.Controls.typed_paths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.typed_paths

/-- info: 'Solidity.Backend.StorageOps.SourceMappingDelete.Controls.deletion_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.deletion_result

/-- info: 'Solidity.Backend.StorageOps.SourceMappingDelete.Controls.ordered_delete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.ordered_delete

/-- info: 'Solidity.Backend.StorageOps.SourceMappingDelete.Controls.timeout_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.timeout_prefix

/-- info: 'Solidity.Backend.StorageOps.SourceMappingDelete.Controls.wrong_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.wrong_erasure

/-- info: 'Solidity.Backend.StorageOps.SourceMappingDelete.Controls.reuse_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.reuse_observations

/-- info: 'Solidity.Backend.StorageOps.SourceMappingDelete.Controls.timeout_not_rollback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.timeout_not_rollback

/-- info: 'Solidity.Backend.StorageOps.SourceMappingDelete.Controls.wrong_erasure_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.wrong_erasure_distinct

end Solidity.Backend.StorageOps.SourceMappingDelete
