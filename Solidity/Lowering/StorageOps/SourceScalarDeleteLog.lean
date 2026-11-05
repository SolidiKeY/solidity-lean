import Solidity.Source.Machine

/-! Actual Source primitive deletion and its existing typed operation journal.
The operation log uses Source.Op, not a replacement evaluator. Restoration
requires explicit application of the existing public frame rollback. -/
namespace Solidity.Backend.StorageOps.SourceScalarDeleteLog

/-- The existing journal operation selected by actual setCell for a clear. -/
def clearOp (E : Source.Env) (frame : Source.Fr) (path : Source.SPath) :
    Source.Op E.layout E.lay E.lay :=
  if E.transientRoot path then
    .transient frame.this (fun storage => storage.set path none)
  else .account frame.this (fun account => { account with storage := account.storage.set path none })

theorem setCell_run {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (path : Source.SPath)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.setCell (E := E) (Γ := Γ) frame path none).run (locals,state) =
      (.ok (), (locals,{state with ex := state.ex.apply (clearOp E frame path)})) := by
  cases branch : E.transientRoot path <;>
    simp only [Source.setCell,clearOp,branch,Source.applyOp,writable,
      Bool.false_eq_true,if_false,if_true] <;> rfl

private theorem bind_run_first {E : Source.Env} {Γ : Source.RCtx} {A B : Type}
    (m : Source.EM E Γ A) (next : A → Source.EM E Γ B)
    (initial middle : Source.Locals E.layout Γ × Source.St E) (value : A)
    (first : m.run initial = (.ok value,middle)) :
    (m >>= next).run initial = (next value).run middle := by
  rw [ExceptT.run_bind]
  simp only [bind,StateT.bind]
  rw [first]

/-- Complete runtime range, with exact existing Source state and journal updates.
No fixed runtime length or depth is admitted as a source restriction. -/
theorem scalar_range_run {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (intTy : Source.IntTy)
    (path : Source.SPath) (start count padding : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.deleteRange (E := E) (Γ := Γ) frame (count + padding + 1)
      (.int intTy) path start count).run (locals,state) =
      (.ok (), (locals,{state with ex := state.ex.run ((List.range' start count).map (fun i => clearOp E frame (path.go (.index i))))})) := by
  induction count generalizing start state with
  | zero =>
    simp only [Source.deleteRange,List.range'_zero,List.map_nil,Source.ExecState.run]
    rfl
  | succ count ih =>
    have budget : count + 1 + padding + 1 = (count + padding + 1) + 1 := by omega
    rw [budget]
    change ((Source.setCell frame (path.go (.index start)) none >>= fun _ =>
      Source.deleteRange frame (count + padding + 1) (.int intTy) path (start + 1) count).run
        (locals,state)) = _
    rw [bind_run_first _ _ _ _ () (setCell_run frame writable _ locals state),ih]
    simp only [List.range'_succ,List.map_cons,Source.ExecState.run]

theorem scalar_range_zero {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (intTy : Source.IntTy) (path : Source.SPath) (start count : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.deleteRange (E := E) (Γ := Γ) frame 0 (.int intTy) path start count).run
      (locals,state) = (.error .timeout,(locals,state)) := by
  simp only [Source.deleteRange]
  rfl

/-- Exact matching prefix at every positive existing fuel, including failure.
At fuel budget+1 exactly min(count,budget) writes occur; timeout is not rollback. -/
theorem scalar_range_prefix {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (intTy : Source.IntTy)
    (path : Source.SPath) (start count budget : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.deleteRange (E := E) (Γ := Γ) frame (budget + 1)
      (.int intTy) path start count).run (locals,state) =
      (if count ≤ budget then .ok () else .error .timeout,
        (locals,{state with ex := state.ex.run ((List.range' start (min count budget)).map
          (fun i => clearOp E frame (path.go (.index i))))})) := by
  induction budget generalizing start count state with
  | zero =>
    cases count with
    | zero =>
      simp only [Source.deleteRange,Nat.le_refl,if_true,Nat.min_zero,
        List.range'_zero,List.map_nil,Source.ExecState.run]
      rfl
    | succ count =>
      simp only [Source.deleteRange,Source.deleteStor,
        Nat.min_zero,List.range'_zero,List.map_nil,Source.ExecState.run]
      rfl
  | succ budget ih =>
    cases count with
    | zero =>
      simp only [Source.deleteRange,Nat.zero_le,if_true,Nat.zero_min,
        List.range'_zero,List.map_nil,Source.ExecState.run]
      rfl
    | succ count =>
      change ((Source.setCell frame (path.go (.index start)) none >>= fun _ =>
        Source.deleteRange frame (budget + 1) (.int intTy) path (start + 1) count).run
          (locals,state)) = _
      rw [bind_run_first _ _ _ _ () (setCell_run frame writable _ locals state),ih]
      simp only [Nat.succ_le_succ_iff,Nat.succ_min_succ,List.range'_succ,
        List.map_cons,Source.ExecState.run]

/-- Explicit existing caller-frame rollback restores the actual generated
range prefix, on success or timeout. No automatic rollback is asserted. -/
theorem scalar_range_explicit_rollback {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (intTy : Source.IntTy)
    (path : Source.SPath) (start count budget : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) (input : Roadmap.Bytes) :
    (state.ex.enter frame.this frame.sender frame.value input frame.static).rollback
      ((Source.deleteRange (E := E) (Γ := Γ) frame (budget + 1)
        (.int intTy) path start count).run (locals,state)).2.2.ex = state.ex := by
  rw [scalar_range_prefix frame writable]
  exact Source.rollback_run state.ex _ frame.this frame.sender frame.value input frame.static

theorem scalar_range_journal {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (intTy : Source.IntTy)
    (path : Source.SPath) (start count budget : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    ((Source.deleteRange (E := E) (Γ := Γ) frame (budget + 1)
      (.int intTy) path start count).run (locals,state)).2.2.ex.journal.length =
      state.ex.journal.length + min count budget := by
  rw [scalar_range_prefix frame writable]
  simp only [Source.ExecState.journal_run,List.length_map,List.length_range']

private theorem set_read_other {D : Source.Layout} {L : Source.SPath → Source.STy}
    (storage : Source.Storage D L) (path query : Source.SPath)
    (different : query ≠ path) :
    (storage.set path none).read query = storage.read query := by
  simp only [Source.Storage.set,Source.Storage.read,different,dif_neg,not_false_eq_true]

/-- Exact logical-cell frames in both persistent and transient storage.
These do not imply numeric/hash or live-path preservation. -/
theorem clearOp_other {E : Source.Env} (frame : Source.Fr)
    (state : Source.ExecState E.layout E.lay E.lay) (path query : Source.SPath)
    (different : query ≠ path) :
    ((state.apply (clearOp E frame path)).world.accounts frame.this).storage.read query =
      (state.world.accounts frame.this).storage.read query ∧
    ((state.apply (clearOp E frame path)).transient.cells frame.this).read query =
      (state.transient.cells frame.this).read query := by
  cases branch : E.transientRoot path <;>
    simp only [clearOp,branch,Bool.false_eq_true,if_false,if_true,
      Source.ExecState.apply,Source.World.set,Source.Transient.set,dif_pos,and_true,true_and]
  · exact set_read_other _ _ _ different
  · exact set_read_other _ _ _ different

/-- Finite touched-path transport uses only actual generated indices. -/
theorem clear_log_other {E : Source.Env} (frame : Source.Fr)
    (state : Source.ExecState E.layout E.lay E.lay) (path query : Source.SPath)
    (indices : List Nat) (untouched : ∀ i ∈ indices, query ≠ path.go (.index i)) :
    ((state.run (indices.map (fun i => clearOp E frame (path.go (.index i))))).world.accounts frame.this).storage.read query =
      (state.world.accounts frame.this).storage.read query ∧
    ((state.run (indices.map (fun i => clearOp E frame (path.go (.index i))))).transient.cells frame.this).read query =
      (state.transient.cells frame.this).read query := by
  induction indices generalizing state with
  | nil => exact ⟨rfl,rfl⟩
  | cons i indices ih =>
    have first := clearOp_other frame state (path.go (.index i)) query (untouched i (by simp only [List.mem_cons, true_or]))
    have rest := ih (state.apply (clearOp E frame (path.go (.index i))))
      (fun j member => untouched j (by simp only [List.mem_cons]; exact Or.inr member))
    exact ⟨rest.1.trans first.1,rest.2.trans first.2⟩

/-- Actual runtime deletion preserves every cell outside its computed prefix. -/
theorem scalar_range_other {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (intTy : Source.IntTy)
    (path query : Source.SPath) (start count budget : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (untouched : ∀ i ∈ List.range' start (min count budget), query ≠ path.go (.index i)) :
    let result := (Source.deleteRange (E := E) (Γ := Γ) frame (budget + 1)
      (.int intTy) path start count).run (locals,state)
    (result.2.2.ex.world.accounts frame.this).storage.read query =
      (state.ex.world.accounts frame.this).storage.read query ∧
    (result.2.2.ex.transient.cells frame.this).read query =
      (state.ex.transient.cells frame.this).read query := by
  dsimp only
  rw [scalar_range_prefix frame writable]
  exact clear_log_other frame state.ex path query _ untouched

/-- Restoring the explicitly marked execution state also restores the full
Source state and locals because this range changes no other state component. -/
theorem scalar_range_restore {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (intTy : Source.IntTy)
    (path : Source.SPath) (start count budget : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) (input : Roadmap.Bytes) :
    let result := (Source.deleteRange (E := E) (Γ := Γ) frame (budget + 1)
      (.int intTy) path start count).run (locals,state)
    (result.2.1,{result.2.2 with ex :=
      (state.ex.enter frame.this frame.sender frame.value input frame.static).rollback result.2.2.ex}) =
      (locals,state) := by
  dsimp only
  rw [scalar_range_prefix frame writable]
  rw [Source.rollback_run]

namespace Controls
private def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))
private def mapSyntax : Source.Syn .typeName :=
  .mapping (.elem (.int false 256 (by decide)) (by decide)) none uintSyntax none
private def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.array mapSyntax .none) none none none false "maps" .none)
    (.cons (.stateVar (.array uintSyntax .none) none none none false "values" .none)
      (.cons (.stateVar uintSyntax none none none false "sentinel" .none)
        (.cons (.stateVar uintSyntax none none none true "scratch" .none) .nil))))) .nil)
private def env : Source.Env := unit.env
private def uint : Source.STy := .int Source.IntTy.u256
private def mapTy : Source.STy := .mapping uint uint
private def ty : Source.STy := .array .storage mapTy none
private def root : Source.SPath := ⟨⟨some "C","maps"⟩,[]⟩
private def scalar : Source.SPath := ⟨⟨some "C","values"⟩,[]⟩
private def sentinel : Source.SPath := ⟨⟨some "C","sentinel"⟩,[]⟩
private def scratch : Source.SPath := ⟨⟨some "C","scratch"⟩,[]⟩
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
private def transientStorage : Source.Storage env.layout env.cellTy :=
  (Source.Storage.empty : Source.Storage env.layout env.cellTy).write scratch (.int 41 (by decide))
private def state : Source.St env :=
  { ex :=
      { world := ⟨fun a => if a = address then
          { balance := ⟨19,by decide⟩, nonce := 3, code := some 0, storage := storage }
          else Source.Account.empty _⟩
        transient := Source.Transient.empty.set address transientStorage
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
   (s.ex.world.accounts address).storage.read (elem 2),
   (s.ex.transient.cells address).read scratch]
private def value (i : Int) (h : Source.IntTy.u256.lo ≤ i ∧ i ≤ Source.IntTy.u256.hi) : Source.Val env.layout uint := .int i h
private def prior := (Source.setCell (E := env) (Γ := []) frame sentinel (some (.int 101 (by decide)))).run initial
private def prefixRun := (Source.deleteRange (E := env) (Γ := []) frame 2 uint scalar 0 2).run prior.2
private def successRun := (Source.deleteRange (E := env) (Γ := []) frame 3 uint scalar 0 2).run prior.2
private def arrayRun := (Source.deleteStor (E := env) (Γ := []) frame 4 (.array .storage uint none) scalar).run prior.2
private def wrongRun := ((do
  Source.deleteRange (E := env) (Γ := []) frame 4 uint scalar 0 3
  Source.setCell frame scalar none) : Source.EM env [] Unit).run prior.2
private def scratchRun := (Source.setCell (E := env) (Γ := []) frame scratch none).run prior.2
private def entry := prior.2.2.ex.enter frame.this frame.sender frame.value [1,2,3] frame.static
private def outerEntry := state.ex.enter frame.this frame.sender frame.value [1,2,3] frame.static
private def restored : Source.St env := {prefixRun.2.2 with ex := entry.rollback prefixRun.2.2.ex}
private def wrongScope : Source.St env := {prefixRun.2.2 with ex := outerEntry.rollback prefixRun.2.2.ex}
private def context (s : Source.St env) :=
  (s.heap.next,s.events.length,s.logs.length,(s.ex.world.accounts address).balance,
    (s.ex.world.accounts address).nonce,(s.ex.world.accounts address).code)

theorem typed_paths : env.pathTy scalar = some (.array .storage uint none) ∧
    env.pathTy (elem 2) = some uint ∧ env.pathTy scratch = some uint ∧
    env.transientRoot scalar = false ∧ env.transientRoot scratch = true := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem generated_prefix : prefixRun =
    (.error .timeout,(prior.2.1,{prior.2.2 with ex := prior.2.2.ex.run [clearOp env frame (elem 0)]})) :=
  scalar_range_prefix frame (by rfl) Source.IntTy.u256 scalar 0 2 1 prior.2.1 prior.2.2

theorem generated_success : successRun =
    (.ok (), (prior.2.1,{prior.2.2 with ex := prior.2.2.ex.run [clearOp env frame (elem 0),clearOp env frame (elem 1)]})) :=
  scalar_range_run frame (by rfl) Source.IntTy.u256 scalar 0 2 0 prior.2.1 prior.2.2

theorem restore_inner : (prefixRun.2.1,restored) = prior.2 :=
  scalar_range_restore frame (by rfl) Source.IntTy.u256 scalar 0 2 1 prior.2.1 prior.2.2 [1,2,3]

theorem ordered_prefix :
    (view state,view prior.2.2,view prefixRun.2.2,view restored,
      prior.2.2.ex.journal.length,prefixRun.2.2.ex.journal.length,restored.ex.journal.length,
      context prefixRun.2.2,context restored) =
    ([some (value 2 (by decide)),some (value 7 (by decide)),some (value 17 (by decide)),some (value 71 (by decide)),some (value 99 (by decide)),some (value 2 (by decide)),some (value 53 (by decide)),some (value 59 (by decide)),some (value 61 (by decide)),some (value 41 (by decide))],[some (value 2 (by decide)),some (value 7 (by decide)),some (value 17 (by decide)),some (value 71 (by decide)),some (value 101 (by decide)),some (value 2 (by decide)),some (value 53 (by decide)),some (value 59 (by decide)),some (value 61 (by decide)),some (value 41 (by decide))],[some (value 2 (by decide)),some (value 7 (by decide)),some (value 17 (by decide)),some (value 71 (by decide)),some (value 101 (by decide)),some (value 2 (by decide)),some (value 0 (by decide)),some (value 59 (by decide)),some (value 61 (by decide)),some (value 41 (by decide))],[some (value 2 (by decide)),some (value 7 (by decide)),some (value 17 (by decide)),some (value 71 (by decide)),some (value 101 (by decide)),some (value 2 (by decide)),some (value 53 (by decide)),some (value 59 (by decide)),some (value 61 (by decide)),some (value 41 (by decide))],1,2,1,context state,context state) := by
  have back := restore_inner
  have backState := congrArg Prod.snd back
  change restored = prior.2.2 at backState
  rw [backState]
  rfl

theorem ordered_success :
    (successRun.1,view successRun.2.2,successRun.2.2.ex.journal.length,
      arrayRun.1,view arrayRun.2.2,arrayRun.2.2.ex.journal.length,
      context successRun.2.2,context arrayRun.2.2) =
    (.ok (),[some (value 2 (by decide)),some (value 7 (by decide)),some (value 17 (by decide)),some (value 71 (by decide)),some (value 101 (by decide)),some (value 2 (by decide)),some (value 0 (by decide)),some (value 0 (by decide)),some (value 61 (by decide)),some (value 41 (by decide))],3,.ok (),[some (value 2 (by decide)),some (value 7 (by decide)),some (value 17 (by decide)),some (value 71 (by decide)),some (value 101 (by decide)),some (value 0 (by decide)),some (value 0 (by decide)),some (value 0 (by decide)),some (value 61 (by decide)),some (value 41 (by decide))],4,context state,context state) := by
  rfl

theorem ordered_wrong_tail :
    (wrongRun.1,view wrongRun.2.2,wrongRun.2.2.ex.journal.length,context wrongRun.2.2) =
    (.ok (),[some (value 2 (by decide)),some (value 7 (by decide)),some (value 17 (by decide)),some (value 71 (by decide)),some (value 101 (by decide)),some (value 0 (by decide)),some (value 0 (by decide)),some (value 0 (by decide)),some (value 0 (by decide)),some (value 41 (by decide))],5,context state) := by
  rfl

theorem wrong_tail_distinct : wrongRun.2 ≠ arrayRun.2 := by
  intro same
  have impossible := congrArg (fun s => ((Source.readLen (E := env) (Γ := []) frame (elem 2)).run s).1) same
  change (Except.ok 0 : Except Source.Halt Nat) = Except.ok 61 at impossible
  cases impossible

theorem wrong_scope : wrongScope = state := by
  have back := Source.rollback_run state.ex
    [Source.Op.account frame.this (fun account => {account with storage := account.storage.set sentinel (some (.int 101 (by decide)))}),
     clearOp env frame (elem 0)] frame.this frame.sender frame.value [1,2,3] frame.static
  change outerEntry.rollback prefixRun.2.2.ex = state.ex at back
  change {state with ex := outerEntry.rollback prefixRun.2.2.ex} = state
  rw [back]

theorem ordered_wrong_scope :
    (view wrongScope,wrongScope.ex.journal.length) = ([some (value 2 (by decide)),some (value 7 (by decide)),some (value 17 (by decide)),some (value 71 (by decide)),some (value 99 (by decide)),some (value 2 (by decide)),some (value 53 (by decide)),some (value 59 (by decide)),some (value 61 (by decide)),some (value 41 (by decide))],0) := by
  rw [wrong_scope]
  rfl

theorem transient_control :
    (scratchRun.1,view scratchRun.2.2,scratchRun.2.2.ex.journal.length,context scratchRun.2.2) =
    (.ok (),[some (value 2 (by decide)),some (value 7 (by decide)),some (value 17 (by decide)),some (value 71 (by decide)),some (value 101 (by decide)),some (value 2 (by decide)),some (value 53 (by decide)),some (value 59 (by decide)),some (value 61 (by decide)),some (value 0 (by decide))],2,context state) := by
  rfl

theorem transient_restore : entry.rollback scratchRun.2.2.ex = prior.2.2.ex := by
  exact Source.rollback_run prior.2.2.ex [clearOp env frame scratch]
    frame.this frame.sender frame.value [1,2,3] frame.static
/-- The writable-frame premise cannot be discarded. -/
theorem static_control :
    (Source.deleteRange (E := env) (Γ := []) {frame with static := true} 3 uint scalar 0 2).run prior.2 =
      (.error (.revert []),prior.2) := by
  rfl

/-- An actual unrelated mapping read applies the finite touched-path theorem. -/
theorem mapping_frame :
    (prefixRun.2.2.ex.world.accounts address).storage.read (key 0) =
      (prior.2.2.ex.world.accounts address).storage.read (key 0) ∧
    (prefixRun.2.2.ex.transient.cells address).read (key 0) =
      (prior.2.2.ex.transient.cells address).read (key 0) := by
  exact scalar_range_other frame (by rfl) Source.IntTy.u256 scalar (key 0) 0 2 1 prior.2.1 prior.2.2
    (by
      intro i member
      have atZero : i = 0 := by
        change i ∈ [0] at member
        simpa only [List.mem_singleton] using member
      subst i
      decide)

end Controls

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.setCell_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms setCell_run

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.scalar_range_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms scalar_range_run

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.scalar_range_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms scalar_range_zero

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.scalar_range_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms scalar_range_prefix

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.scalar_range_explicit_rollback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms scalar_range_explicit_rollback

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.scalar_range_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms scalar_range_journal

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.clearOp_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clearOp_other

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.clear_log_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_log_other

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.scalar_range_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms scalar_range_other

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.scalar_range_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms scalar_range_restore

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.Controls.typed_paths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.typed_paths

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.Controls.generated_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.generated_prefix

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.Controls.generated_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.generated_success

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.Controls.restore_inner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.restore_inner

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.Controls.ordered_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.ordered_prefix

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.Controls.ordered_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.ordered_success

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.Controls.ordered_wrong_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.ordered_wrong_tail

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.Controls.wrong_tail_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.wrong_tail_distinct

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.Controls.wrong_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.wrong_scope

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.Controls.ordered_wrong_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.ordered_wrong_scope

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.Controls.transient_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.transient_control

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.Controls.transient_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.transient_restore

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.Controls.static_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.static_control

/-- info: 'Solidity.Backend.StorageOps.SourceScalarDeleteLog.Controls.mapping_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.mapping_frame

end Solidity.Backend.StorageOps.SourceScalarDeleteLog
