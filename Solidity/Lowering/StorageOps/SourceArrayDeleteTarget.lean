import Solidity.Lowering.StorageOps.SourceScalarDeleteLog
import Solidity.Source.ExprProgress
import Solidity.Backend.StorageOps.TargetArrayClear

/-! Actual captured primitive-array Source deletion and target clearing.
This upper test reuses the exact committed Source log producer. Address/argument
lowering, general packing, call unwinding and target-world composition remain open. -/
namespace Solidity.Backend.StorageOps.SourceArrayDeleteTarget
open SourceScalarDeleteLog

private theorem bind_run_first {E : Source.Env} {Γ : Source.RCtx} {A B : Type}
    (m : Source.EM E Γ A) (next : A → Source.EM E Γ B)
    (initial middle : Source.Locals E.layout Γ × Source.St E) (value : A)
    (first : m.run initial = (.ok value,middle)) :
    (m >>= next).run initial = (next value).run middle := by
  rw [ExceptT.run_bind]
  simp only [bind,StateT.bind]
  rw [first]

/-- Exact existing Op log for actual dynamic Source deletion. readLength is
an input execution fact; no desired output preservation is assumed. -/
theorem source_array_run {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (intTy : Source.IntTy)
    (path : Source.SPath) (count : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (readLength : (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,state) =
      (.ok count,(locals,state))) :
    (Source.deleteStor (E := E) (Γ := Γ) frame (count + 2)
      (.array .storage (.int intTy) none) path).run (locals,state) =
      (.ok (), (locals,{state with ex := state.ex.run (((List.range' 0 count).map (fun i => clearOp E frame (path.go (.index i)))) ++ [clearOp E frame path])})) := by
  change ((Source.readLen frame path >>= fun length => do
    Source.deleteRange frame (count + 1) (.int intTy) path 0 length
    Source.setCell frame path none).run (locals,state)) = _
  rw [bind_run_first _ _ _ _ count readLength]
  rw [bind_run_first _ _ _ _ () (scalar_range_run frame writable intTy path 0 count 0 locals state)]
  rw [setCell_run frame writable]
  simp only [Source.run_append,Source.ExecState.run]

/-- Header clearing follows every element clear, so the journal gains count+1. -/
theorem source_array_journal {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (intTy : Source.IntTy)
    (path : Source.SPath) (count : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (readLength : (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,state) =
      (.ok count,(locals,state))) :
    ((Source.deleteStor (E := E) (Γ := Γ) frame (count + 2)
      (.array .storage (.int intTy) none) path).run (locals,state)).2.2.ex.journal.length =
        state.ex.journal.length + (count + 1) := by
  rw [source_array_run frame writable intTy path count locals state readLength]
  simp only [Source.ExecState.journal_run,List.length_append,List.length_map,
    List.length_range',List.length_singleton]

/-- Explicit public caller-frame rollback restores this actual complete Source
operation, not merely a hypothetical independently supplied operation list. -/
theorem source_array_restore {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (intTy : Source.IntTy)
    (path : Source.SPath) (count : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) (input : Roadmap.Bytes)
    (readLength : (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,state) =
      (.ok count,(locals,state))) :
    let result := (Source.deleteStor (E := E) (Γ := Γ) frame (count + 2)
      (.array .storage (.int intTy) none) path).run (locals,state)
    (result.2.1,{result.2.2 with ex :=
      (state.ex.enter frame.this frame.sender frame.value input frame.static).rollback result.2.2.ex}) =
        (locals,state) := by
  dsimp only
  rw [source_array_run frame writable intTy path count locals state readLength]
  rw [Source.rollback_run]

/-- Canonical published Source ABI-word observation, retaining Option failure. -/
def wordAt {E : Source.Env} (frame : Source.Fr)
    (state : Source.ExecState E.layout E.lay E.lay) (query : Source.SPath) : Option Nat :=
  (((state.world.accounts frame.this).storage.read query).bind Source.Val.word).map Fin.val

private theorem index_ne_header (path : Source.SPath) (i : Nat) :
    path.go (.index i) ≠ path := by
  intro same
  have lengths := congrArg (fun p : Source.SPath => p.steps.length) same
  simp only [Source.SPath.go,List.length_append,List.length_singleton] at lengths
  omega

private theorem index_ne_index (path : Source.SPath) {i j : Nat} (different : i ≠ j) :
    path.go (.index i) ≠ path.go (.index j) := by
  intro same
  have steps := congrArg Source.SPath.steps same
  change path.steps ++ [Source.Step.index i] = path.steps ++ [Source.Step.index j] at steps
  have suffix := List.append_cancel_left steps
  have indices := Source.Step.index.inj (List.cons.inj suffix).1
  exact different indices

theorem array_header_type {E : Source.Env} (path : Source.SPath)
    (typed : E.pathTy path = some (.array .storage (.int Source.IntTy.u256) none)) :
    E.cellTy path = .int Source.IntTy.u256 := by
  simp only [Source.Env.cellTy,typed,Option.map_some,Source.STy.cell,Option.getD_some]

theorem array_index_type {E : Source.Env} (path : Source.SPath)
    (typed : E.pathTy path = some (.array .storage (.int Source.IntTy.u256) none)) (i : Nat) :
    E.cellTy (path.go (.index i)) = .int Source.IntTy.u256 := by
  simp only [Source.Env.cellTy,Source.Env.pathTy_go,typed,Option.bind_some,
    Source.Env.stepTy,Option.map_some,Option.getD_some,Source.STy.cell,Source.STy.isValue,if_true]

theorem clear_word_same {E : Source.Env} (frame : Source.Fr)
    (state : Source.ExecState E.layout E.lay E.lay) (query : Source.SPath)
    (ordinary : E.transientRoot query = false) (uint : E.cellTy query = .int Source.IntTy.u256) :
    wordAt frame (state.apply (clearOp E frame query)) query = some 0 := by
  unfold wordAt clearOp
  simp only [ordinary,Bool.false_eq_true,if_false,Source.ExecState.apply,Source.World.set_get,
    Source.Storage.read,Source.Storage.set,dif_pos]
  change ((Source.Val.default E.layout (E.cellTy query)).bind Source.Val.word).map Fin.val = some 0
  rw [uint]
  rfl

theorem clear_word_other {E : Source.Env} (frame : Source.Fr)
    (state : Source.ExecState E.layout E.lay E.lay) (path query : Source.SPath)
    (different : query ≠ path) :
    wordAt frame (state.apply (clearOp E frame path)) query = wordAt frame state query := by
  unfold wordAt
  rw [(clearOp_other frame state path query different).1]

/-- List membership is actual generated access membership, not a postcondition. -/
theorem clear_words_index {E : Source.Env} (frame : Source.Fr)
    (state : Source.ExecState E.layout E.lay E.lay) (path : Source.SPath)
    (indices : List Nat) (j : Nat)
    (ordinary : E.transientRoot (path.go (.index j)) = false)
    (uint : E.cellTy (path.go (.index j)) = .int Source.IntTy.u256) :
    wordAt frame (state.run (indices.map (fun i => clearOp E frame (path.go (.index i)))))
      (path.go (.index j)) =
        if j ∈ indices then some 0 else wordAt frame state (path.go (.index j)) := by
  induction indices generalizing state with
  | nil => rfl
  | cons i indices ih =>
    simp only [List.map_cons,Source.ExecState.run]
    rw [ih]
    by_cases same : j = i
    · subst i
      rw [clear_word_same frame state _ ordinary uint]
      simp only [List.mem_cons,true_or,if_true,ite_self]
    · rw [clear_word_other frame state _ _ (index_ne_index path same)]
      simp only [List.mem_cons,same,false_or]

theorem clear_range_word {E : Source.Env} (frame : Source.Fr)
    (state : Source.ExecState E.layout E.lay E.lay) (path : Source.SPath) (count j : Nat)
    (ordinary : E.transientRoot (path.go (.index j)) = false)
    (uint : E.cellTy (path.go (.index j)) = .int Source.IntTy.u256) :
    wordAt frame (state.run ((List.range' 0 count).map (fun i => clearOp E frame (path.go (.index i)))))
      (path.go (.index j)) = if j < count then some 0 else wordAt frame state (path.go (.index j)) := by
  rw [clear_words_index frame state path _ j ordinary uint]
  have membership : j ∈ List.range' 0 count ↔ j < count := by
    rw [List.mem_range']
    constructor
    · rintro ⟨i,inside,same⟩
      simp only [Nat.zero_add,Nat.one_mul] at same
      subst j
      exact inside
    · intro inside
      exact ⟨j,inside,by simp only [Nat.zero_add,Nat.one_mul]⟩
  simp only [membership]

theorem source_array_header {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (path : Source.SPath) (count : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (typed : E.pathTy path = some (.array .storage (.int Source.IntTy.u256) none))
    (ordinary : E.transientRoot path = false)
    (readLength : (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,state) =
      (.ok count,(locals,state))) :
    wordAt frame ((Source.deleteStor (E := E) (Γ := Γ) frame (count + 2)
      (.array .storage (.int Source.IntTy.u256) none) path).run (locals,state)).2.2.ex path = some 0 := by
  rw [source_array_run frame writable _ path count locals state readLength,Source.run_append]
  simp only [Source.ExecState.run]
  exact clear_word_same frame _ path ordinary (array_header_type path typed)

/-- Retained word reads stay retained; these are not fresh source index
expressions or a liveness admission rule. No None-to-zero inference occurs. -/
theorem source_array_data {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (path : Source.SPath) (count j : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (typed : E.pathTy path = some (.array .storage (.int Source.IntTy.u256) none))
    (ordinary : E.transientRoot path = false)
    (readLength : (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,state) =
      (.ok count,(locals,state))) :
    wordAt frame ((Source.deleteStor (E := E) (Γ := Γ) frame (count + 2)
      (.array .storage (.int Source.IntTy.u256) none) path).run (locals,state)).2.2.ex (path.go (.index j)) =
      if j < count then some 0 else wordAt frame state.ex (path.go (.index j)) := by
  rw [source_array_run frame writable _ path count locals state readLength,Source.run_append]
  simp only [Source.ExecState.run]
  rw [clear_word_other frame _ path _ (index_ne_header path j)]
  exact clear_range_word frame state.ex path count j ordinary (array_index_type path typed j)

/-- Coupling is an OLD input observation only for an unvisited retained word.
Visited output is derived without assuming its desired representation. -/
theorem data_correspondence {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (path : Source.SPath) (count j : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (typed : E.pathTy path = some (.array .storage (.int Source.IntTy.u256) none))
    (ordinary : E.transientRoot path = false)
    (readLength : (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,state) =
      (.ok count,(locals,state)))
    (target : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (header : target.store slot = count)
    (oldWord : count ≤ j → wordAt frame state.ex (path.go (.index j)) = some (target.store (.data slot j))) :
    wordAt frame ((Source.deleteStor (E := E) (Γ := Γ) frame (count + 2)
      (.array .storage (.int Source.IntTy.u256) none) path).run (locals,state)).2.2.ex (path.go (.index j)) =
      some ((TargetArrayClear.afterClear target tail slot).store (.data slot j)) := by
  rw [source_array_data frame writable path count j locals state typed ordinary readLength,
    TargetArrayClear.after_data,header]
  by_cases live : j < count
  · simp only [if_pos live]
  · simp only [if_neg live,oldWord (by omega)]

/-- Actual Source operation and actual target program with finite selected
canonical word observations. Captured path/slot inputs are explicit; this is
not an address compiler or whole Source/target state relation. -/
theorem delete_components {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (path : Source.SPath) (count : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (typed : E.pathTy path = some (.array .storage (.int Source.IntTy.u256) none))
    (ordinary : E.transientRoot path = false)
    (readLength : (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,state) =
      (.ok count,(locals,state)))
    (target : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot) (indices : List Nat)
    (header : target.store slot = count)
    (oldWords : ∀ j ∈ indices, count ≤ j → wordAt frame state.ex (path.go (.index j)) = some (target.store (.data slot j))) :
    let sourceResult := (Source.deleteStor (E := E) (Γ := Γ) frame (count + 2)
      (.array .storage (.int Source.IntTy.u256) none) path).run (locals,state)
    sourceResult = (.ok (), (locals,{state with ex := state.ex.run (((List.range' 0 count).map
      (fun i => clearOp E frame (path.go (.index i)))) ++ [clearOp E frame path])})) ∧
    Evm.run TargetArrayClear.code {target with stack := .slot slot :: tail} =
      .ok (TargetArrayClear.afterClear target tail slot) 0 ∧
    wordAt frame sourceResult.2.2.ex path = some ((TargetArrayClear.afterClear target tail slot).store slot) ∧
    ∀ j ∈ indices, wordAt frame sourceResult.2.2.ex (path.go (.index j)) =
      some ((TargetArrayClear.afterClear target tail slot).store (.data slot j)) := by
  dsimp only
  refine ⟨source_array_run frame writable _ path count locals state readLength,
    TargetArrayClear.run_current target tail slot,?_,?_⟩
  · rw [source_array_header frame writable path count locals state typed ordinary readLength,
      TargetArrayClear.after_header]
  · intro j member
    exact data_correspondence frame writable path count j locals state typed ordinary readLength
      target tail slot header (oldWords j member)

theorem source_array_other {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (intTy : Source.IntTy)
    (path query : Source.SPath) (count : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (readLength : (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,state) =
      (.ok count,(locals,state)))
    (headerApart : query ≠ path)
    (elementsApart : ∀ i ∈ List.range' 0 count, query ≠ path.go (.index i)) :
    wordAt frame ((Source.deleteStor (E := E) (Γ := Γ) frame (count + 2)
      (.array .storage (.int intTy) none) path).run (locals,state)).2.2.ex query =
        wordAt frame state.ex query := by
  rw [source_array_run frame writable intTy path count locals state readLength,Source.run_append]
  simp only [Source.ExecState.run]
  rw [clear_word_other frame _ path query headerApart]
  unfold wordAt
  rw [(clear_log_other frame state.ex path query (List.range' 0 count) elementsApart).1]

/-- Outside observations require BOTH real logical and target access separation
and OLD observation agreement; None yields no numeric/default inference. -/
theorem outside_correspondence {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (intTy : Source.IntTy)
    (path query : Source.SPath) (count : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (readLength : (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,state) =
      (.ok count,(locals,state)))
    (sourceHeaderApart : query ≠ path)
    (sourceElementsApart : ∀ i ∈ List.range' 0 count, query ≠ path.go (.index i))
    (target : Evm.Machine) (tail : List Evm.Word) (slot observer : Evm.Slot)
    (targetHeaderApart : observer ≠ slot)
    (targetElementsApart : ∀ i, i < target.store slot → observer ≠ .data slot i)
    (oldWord : wordAt frame state.ex query = some (target.store observer)) :
    wordAt frame ((Source.deleteStor (E := E) (Γ := Γ) frame (count + 2)
      (.array .storage (.int intTy) none) path).run (locals,state)).2.2.ex query =
        some ((TargetArrayClear.afterClear target tail slot).store observer) := by
  rw [source_array_other frame writable intTy path query count locals state readLength
      sourceHeaderApart sourceElementsApart,
    TargetArrayClear.after_outside target tail slot observer targetHeaderApart targetElementsApart]
  exact oldWord

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
          { balance := 19, nonce := 3, code := some 0, storage := storage }
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
private def sourceRun := (Source.deleteStor (E := env) (Γ := []) frame 4 (.array .storage uint none) scalar).run prior.2
private def emptyInput := (Source.setCell (E := env) (Γ := []) frame scalar none).run prior.2
private def emptyRun := (Source.deleteStor (E := env) (Γ := []) frame 2 (.array .storage uint none) scalar).run emptyInput.2
private def slot : Evm.Slot := .root 0
private def store : Evm.WordStore := .ofFn fun s =>
  if s = slot then 2 else if s = .data slot 0 then 53 else if s = .data slot 1 then 59 else
  if s = .data slot 2 then 61 else if s = .data slot 4 then 93 else if s = .root 9 then 101 else
  if s = .root 7 then 7 else if s = .root 8 then 17 else if s = .root 6 then 71 else
  if s = .root 77 then 87 else 0
private def tail : List Evm.Word := [.val ⟨23,by decide⟩,.slot (.root 9)]
private def targetAddress : Fin Evm.W := Source.toWord address.val
private def targetCaller : Fin Evm.W := Source.toWord frame.sender.val
private def target : Evm.Machine :=
  { stack := tail, store := store, mem := fun _ => .val ⟨31,by decide⟩,
    bal := fun a => if a = targetAddress then 19 else 0,
    bal₀ := fun a => if a = targetAddress then 19 else 0,
    self := targetAddress,caller := targetCaller,callvalue := frame.value,
    timestamp := ⟨53,by decide⟩,accepts := fun _ _ => false }
private def targetOut := TargetArrayClear.afterClear target tail slot
private def wrongTarget : Evm.Machine := {target with store := Evm.WordStore.write store slot 3}
private def wrongOut := TargetArrayClear.afterClear wrongTarget tail slot
private def emptyTarget : Evm.Machine := {target with store := Evm.WordStore.write store slot 0}
private def emptyOut := TargetArrayClear.afterClear emptyTarget tail slot
private def slots : List Evm.Slot := [slot,.data slot 0,.data slot 1,.data slot 2,.data slot 4,
  .root 9,.root 7,.root 8,.root 6,.root 77]
private def targetView (m : Evm.Machine) := slots.map (fun q => m.store q)
private def targetContext (m : Evm.Machine) :=
  (m.stack,m.mem 0,m.bal targetAddress,m.bal₀ targetAddress,m.self,m.caller,m.callvalue,m.timestamp,
    m.accepts targetAddress ⟨0,by decide⟩)
private def sourceContext (s : Source.St env) :=
  (s.heap.next,s.events.length,s.logs.length,(s.ex.world.accounts address).balance,
    (s.ex.world.accounts address).nonce,(s.ex.world.accounts address).code)
private def wordView (s : Source.St env) :=
  [wordAt frame s.ex root,wordAt frame s.ex (key 0),wordAt frame s.ex (key 1),wordAt frame s.ex (key 2),
   wordAt frame s.ex sentinel,wordAt frame s.ex scalar,wordAt frame s.ex (elem 0),
   wordAt frame s.ex (elem 1),wordAt frame s.ex (elem 2),
   (((s.ex.transient.cells address).read scratch).bind Source.Val.word).map Fin.val]
private def unknown : Source.SPath := ⟨⟨some "C","unknown"⟩,[]⟩

theorem input_facts : env.pathTy scalar = some (.array .storage uint none) ∧
    env.transientRoot scalar = false ∧ target.store slot = 2 ∧
    (Source.readLen (E := env) (Γ := []) frame scalar).run prior.2 = (.ok 2,prior.2) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem coupled_execution :
    sourceRun = (.ok (), (prior.2.1,{prior.2.2 with ex := prior.2.2.ex.run [clearOp env frame (elem 0),clearOp env frame (elem 1),clearOp env frame scalar]})) ∧
    Evm.run TargetArrayClear.code {target with stack := .slot slot :: tail} = .ok targetOut 0 ∧
    wordAt frame sourceRun.2.2.ex scalar = some (targetOut.store slot) ∧
    ∀ j ∈ [2,0,1,2], wordAt frame sourceRun.2.2.ex (elem j) = some (targetOut.store (.data slot j)) := by
  exact delete_components frame (by rfl) scalar 2 prior.2.1 prior.2.2
    input_facts.1 input_facts.2.1 input_facts.2.2.2 target tail slot [2,0,1,2] input_facts.2.2.1
    (by intro j member unvisited; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl | rfl
        · rfl
        · omega
        · omega
        · rfl)

theorem ordered_observations :
    (wordView prior.2.2,wordView sourceRun.2.2,sourceRun.2.2.ex.journal.length,
      targetView target,targetView targetOut,sourceContext sourceRun.2.2,targetContext targetOut) =
    ([some 2,some 7,some 17,some 71,some 101,some 2,some 53,some 59,some 61,some 41],[some 2,some 7,some 17,some 71,some 101,some 0,some 0,some 0,some 61,some 41],4,
     [2,53,59,61,93,101,7,17,71,87],[0,0,0,61,93,101,7,17,71,87],
     sourceContext prior.2.2,targetContext target) := by
  rfl

/-- Actual target code with wrong input length clears retained61, unlike Source. -/
theorem wrong_extent_control :
    Evm.run TargetArrayClear.code {wrongTarget with stack := .slot slot :: tail} = .ok wrongOut 0 ∧
    (targetView wrongOut,targetContext wrongOut) =
      ([0,0,0,0,93,101,7,17,71,87],targetContext target) ∧
    wordAt frame sourceRun.2.2.ex (elem 2) ≠ some (wrongOut.store (.data slot 2)) := by
  refine ⟨TargetArrayClear.run_current wrongTarget tail slot,rfl,?_⟩
  change some 61 ≠ some (0 : Nat)
  decide

/-- Typed but unrepresented old default is not equal to arbitrary raw storage;
untyped Source None is also not a physical zero. -/
theorem observation_boundaries :
    (wordAt frame prior.2.2.ex (elem 4),wordAt frame sourceRun.2.2.ex (elem 4),
      target.store (.data slot 4),targetOut.store (.data slot 4),
      wordAt frame prior.2.2.ex unknown,wordAt frame sourceRun.2.2.ex unknown,
      target.store (.root 77),targetOut.store (.root 77)) =
    (some 0,some 0,93,93,none,none,87,87) ∧
    wordAt frame sourceRun.2.2.ex (elem 4) ≠ some (targetOut.store (.data slot 4)) := by
  refine ⟨rfl,?_⟩
  change some 0 ≠ some (93 : Nat)
  decide

theorem empty_control :
    Evm.run TargetArrayClear.code {emptyTarget with stack := .slot slot :: tail} = .ok emptyOut 0 ∧
    (emptyRun.1,wordView emptyRun.2.2,emptyRun.2.2.ex.journal.length,
      targetView emptyOut,sourceContext emptyRun.2.2,targetContext emptyOut) =
    (.ok (),[some 2,some 7,some 17,some 71,some 101,some 0,some 53,some 59,some 61,some 41],3,[0,53,59,61,93,101,7,17,71,87],sourceContext prior.2.2,targetContext target) := by
  exact ⟨TargetArrayClear.run_current emptyTarget tail slot,rfl⟩

theorem explicit_restore :
    (sourceRun.2.1,{sourceRun.2.2 with ex :=
      (prior.2.2.ex.enter frame.this frame.sender frame.value [1,2,3] frame.static).rollback sourceRun.2.2.ex}) = prior.2 :=
  source_array_restore frame (by rfl) Source.IntTy.u256 scalar 2 prior.2.1 prior.2.2 [1,2,3] input_facts.2.2.2

/-- Static Source refusal is preserved; the legacy target model has no static
flag, so no static-call simulation follows from the captured writable proof. -/
theorem static_control :
    (Source.deleteStor (E := env) (Γ := []) {frame with static := true} 4
      (.array .storage uint none) scalar).run prior.2 = (.error (.revert []),prior.2) ∧
    wordAt frame prior.2.2.ex (elem 0) ≠ some (targetOut.store (.data slot 0)) := by
  refine ⟨rfl,?_⟩
  change some 53 ≠ some (0 : Nat)
  decide
theorem outside_mapping :
    wordAt frame sourceRun.2.2.ex (key 0) = some (targetOut.store (.root 7)) := by
  exact outside_correspondence frame (by rfl) Source.IntTy.u256 scalar (key 0) 2 prior.2.1 prior.2.2
    input_facts.2.2.2 (by decide)
    (by
      intro i member same
      have roots := congrArg Source.SPath.root same
      exact (by decide : (key 0).root ≠ scalar.root) roots)
    target tail slot (.root 7) (by decide)
    (by intro i live same; cases same) rfl

private def longerInput := (Source.writeLen (E := env) (Γ := []) frame scalar 3).run prior.2
private def longerRun := (Source.deleteStor (E := env) (Γ := []) frame 5 (.array .storage uint none) scalar).run longerInput.2

theorem runtime_length_three :
    longerRun = (.ok (), (longerInput.2.1,{longerInput.2.2 with ex := longerInput.2.2.ex.run [clearOp env frame (elem 0),clearOp env frame (elem 1),clearOp env frame (elem 2),clearOp env frame scalar]})) ∧
    Evm.run TargetArrayClear.code {wrongTarget with stack := .slot slot :: tail} = .ok wrongOut 0 ∧
    wordAt frame longerRun.2.2.ex scalar = some (wrongOut.store slot) ∧
    ∀ j ∈ [2,1,0,2], wordAt frame longerRun.2.2.ex (elem j) = some (wrongOut.store (.data slot j)) := by
  exact delete_components frame (by rfl) scalar 3 longerInput.2.1 longerInput.2.2
    input_facts.1 input_facts.2.1 (by rfl) wrongTarget tail slot [2,1,0,2] (by rfl)
    (by
      intro j member unvisited
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> omega)

theorem ordered_runtime_three :
    (wordView longerInput.2.2,wordView longerRun.2.2,longerRun.2.2.ex.journal.length,
      targetView wrongTarget,targetView wrongOut,sourceContext longerRun.2.2,targetContext wrongOut) =
    ([some 2,some 7,some 17,some 71,some 101,some 3,some 53,some 59,some 61,some 41],
     [some 2,some 7,some 17,some 71,some 101,some 0,some 0,some 0,some 0,some 41],6,
     [3,53,59,61,93,101,7,17,71,87],[0,0,0,0,93,101,7,17,71,87],sourceContext prior.2.2,targetContext target) := by
  rfl
private def wrongCode : List Evm.Instr :=
  [.push (.val ⟨3,by decide⟩),.push (.slot slot),.sstore] ++ TargetArrayClear.code

/-- A real wrong program overwrites the length with retained extent3 before
traversal. On the original length2 input it wrongly erases retained61. -/
theorem wrong_program_control :
    Evm.run wrongCode {target with stack := .slot slot :: tail} = .ok wrongOut 0 ∧
    wordAt frame sourceRun.2.2.ex (elem 2) ≠ some (wrongOut.store (.data slot 2)) := by
  have headRun : Evm.run [.push (.val ⟨3,by decide⟩),.push (.slot slot),.sstore]
      {target with stack := .slot slot :: tail} = .ok {wrongTarget with stack := .slot slot :: tail} 0 := rfl
  refine ⟨?_,wrong_extent_control.2.2⟩
  unfold wrongCode
  rw [Evm.run_append_ok headRun]
  exact TargetArrayClear.run_current wrongTarget tail slot
end Controls

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.source_array_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_array_run

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.source_array_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_array_journal

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.source_array_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_array_restore

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.array_header_type' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms array_header_type

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.array_index_type' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms array_index_type

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.clear_word_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_word_same

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.clear_word_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_word_other

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.clear_words_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_words_index

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.clear_range_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms clear_range_word

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.source_array_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_array_header

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.source_array_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_array_data

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.data_correspondence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms data_correspondence

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.delete_components' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms delete_components

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.source_array_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_array_other

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.outside_correspondence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms outside_correspondence

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.Controls.input_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.input_facts

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.Controls.coupled_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.coupled_execution

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.Controls.ordered_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.ordered_observations

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.Controls.wrong_extent_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.wrong_extent_control

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.Controls.observation_boundaries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.observation_boundaries

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.Controls.empty_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.empty_control

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.Controls.explicit_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.explicit_restore

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.Controls.static_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.static_control

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.Controls.outside_mapping' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.outside_mapping

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.Controls.runtime_length_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.runtime_length_three

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.Controls.ordered_runtime_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.ordered_runtime_three

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteTarget.Controls.wrong_program_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.wrong_program_control

end Solidity.Backend.StorageOps.SourceArrayDeleteTarget
