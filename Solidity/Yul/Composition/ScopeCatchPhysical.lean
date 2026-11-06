import Solidity.Yul.Composition.HeapCatchPhysical

/-! Actual typed Source LOCAL scope over a captured allocated bytes reference.
Uses EM.sub/readLoc/bytesOfRV, not a new evaluator/catch selector. Old caller
locals are explicit and separate from the unchanged raw caller companion. -/
namespace Solidity.Yul.Composition.ScopeCatchPhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls LocalPhysicalControls

theorem sub_run {E Γ Δ α} (inside : Source.Locals E.layout Δ) (m : Source.EM E Δ α)
    (outer : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.EM.sub inside m : Source.EM E Γ _).run (outer,state) =
      match m.run (inside,state) with
      | (.ok value,(innerPost,post)) => (.ok (value,innerPost),(outer,post))
      | (.error halt,(_,post)) => (.error halt,(outer,post)) := rfl

/-- Read the actual bound local, then dereference it with the actual evaluator. -/
def readBound {E Γ} (F : Source.Fr) : Source.EM E (.bytes .memory :: Γ) (List UInt8) := do
  let ref ← Source.readLoc F (.local .here)
  Source.bytesOfRV F 32 (.val ref)

def scopedRead {E Γ} (F : Source.Fr) (ref : Source.Val E.layout (.bytes .memory)) :
    Source.EM E Γ (List UInt8 × Source.Locals E.layout (.bytes .memory :: Γ)) := do
  let outer ← Source.EM.locals
  Source.EM.sub (.cons ref outer) (readBound F)

theorem bound_read_run {E : Source.Env} {Γ : Source.RCtx} (F : Source.Fr) (address : Nat) (bytes : List UInt8)
    (outer : Source.Locals E.layout Γ) (state : Source.St E)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (readBound (E:=E) (Γ:=Γ) F).run (.cons (.memRef rfl address) outer,state) =
      (Except.ok bytes,(.cons (.memRef rfl address) outer,state)) := by
  unfold readBound
  rw [Source.Hoare.run_bind]
  have localRead : (Source.readLoc F (.local (.here : Source.Idx (.bytes .memory::Γ) (.bytes .memory)))).run
      (.cons (.memRef rfl address) outer,state) = (Except.ok (.memRef rfl address),(.cons (.memRef rfl address) outer,state)) := rfl
  rw [localRead]
  exact HeapCatchPhysical.bytesOf_ref_run F address bytes _ state found

theorem scoped_read_run {E : Source.Env} {Γ : Source.RCtx} (F : Source.Fr) (address : Nat) (bytes : List UInt8)
    (outer : Source.Locals E.layout Γ) (state : Source.St E)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (scopedRead F (.memRef rfl address)).run (outer,state) =
      (Except.ok (bytes,Source.Locals.cons (.memRef rfl address) outer),(outer,state)) := by
  unfold scopedRead
  rw [Source.Hoare.run_bind]
  have localsRead : (Source.EM.locals : Source.EM E Γ _).run (outer,state) = (Except.ok outer,(outer,state)) := rfl
  rw [localsRead]
  dsimp only
  rw [sub_run,bound_read_run F address bytes outer state found]

abbrev Outer := [Source.STy.bytes .memory]
abbrev Inner := Source.STy.bytes .memory :: Outer

def outer : Source.Locals originEnv.layout Outer := .cons (.memRef rfl 0) .nil

def scopeResult (result : Except Source.Halt ((List UInt8) ⊕ (Source.Val originEnv.layout (.bytes .memory) × List UInt8))) :
    Source.EM originEnv Outer ((List UInt8) ⊕ (Source.Val originEnv.layout (.bytes .memory) × (List UInt8 × Source.Locals originEnv.layout Inner))) :=
  match result with
  | .error halt => Source.EM.halt halt
  | .ok (.inl bytes) => pure (.inl bytes)
  | .ok (.inr (ref,_)) => do let read ← scopedRead packedStepFrame ref; pure (.inr (ref,read))

def afterCaptured (result : Except Source.Halt (Except Source.Halt ((List UInt8) ⊕ (Source.Val originEnv.layout (.bytes .memory) × List UInt8)))) :=
  match result with
  | .ok inner => scopeResult inner
  | .error halt => Source.EM.halt halt

def run (outcome : Except Source.Halt (List UInt8)) :=
  let captured := (HeapCatchPhysical.capture outcome).2
  (captured,AttemptPhysical.companion (afterCaptured captured.1.1) outer captured.2)

theorem input_next : AttemptPhysical.input.2.heap.next = 1 := by
  change CatchFunctionPhysical.completed.state.2.heap.next = 1
  rw [CatchFunctionPhysical.caller_source_retained]
  rfl

/-- Actual captured reference, not a supplied replacement bytes parameter. -/
theorem bound_capture_result (bytes : List UInt8) :
    (run (.error (.revert bytes))).2.1.1 =
      .ok (.ok (.inr (.memRef rfl 1,(bytes,Source.Locals.cons (.memRef rfl 1) outer)))) := by
  unfold run
  dsimp only
  rw [HeapCatchPhysical.capture_revert_result,HeapCatchPhysical.capture_revert_state]
  unfold afterCaptured scopeResult AttemptPhysical.companion
  rw [AttemptPhysical.attempt_run,Source.Hoare.run_bind,scoped_read_run packedStepFrame AttemptPhysical.input.2.heap.next bytes outer _ (HeapCatchPhysical.object_contents bytes)]
  rw [input_next]
  rfl

theorem caller_scope_restored (bytes : List UInt8) : (run (.error (.revert bytes))).2.1.2.1 = outer := by
  unfold run
  dsimp only
  rw [HeapCatchPhysical.capture_revert_result,HeapCatchPhysical.capture_revert_state]
  unfold afterCaptured scopeResult AttemptPhysical.companion
  rw [AttemptPhysical.attempt_run,Source.Hoare.run_bind,scoped_read_run packedStepFrame AttemptPhysical.input.2.heap.next bytes outer _ (HeapCatchPhysical.object_contents bytes)]
  rfl

theorem raw_and_frame_retained (bytes : List UInt8) :
    (run (.error (.revert bytes))).2.2 = (HeapCatchPhysical.allocated bytes).2 := by
  unfold run
  dsimp only
  rw [HeapCatchPhysical.capture_revert_result,HeapCatchPhysical.capture_revert_state]
  unfold afterCaptured scopeResult AttemptPhysical.companion
  rw [AttemptPhysical.attempt_run,Source.Hoare.run_bind,scoped_read_run packedStepFrame AttemptPhysical.input.2.heap.next bytes outer _ (HeapCatchPhysical.object_contents bytes)]
  rfl

theorem success (bytes : List UInt8) : (run (.ok bytes)).2.1.1 = .ok (.ok (.inl bytes)) := rfl

theorem timeout : (run (.error .timeout)).2.1.1 = .ok (.error .timeout) := rfl

theorem stuck (why : String) : (run (.error (.stuck why))).2.1.1 = .ok (.error (.stuck why)) := rfl

theorem panic : (run (Source.panic .assert)).2.1.1 =
    .ok (.ok (.inr (.memRef rfl 1,(Source.panicData .assert,Source.Locals.cons (.memRef rfl 1) outer)))) := bound_capture_result _

/-- Continuation consumes bytes actually read from the bound LOCAL. -/
def continued (outcome : Except Source.Halt (List UInt8)) (fuel : Nat) :=
  let execution := (run outcome).2
  execution.1.1.map fun result => result.map fun branch =>
    match branch with
    | .inl bytes => Sum.inl bytes
    | .inr (ref,(bytes,_)) => Sum.inr (ref,bytes,
        runLocalBlock ctx (AttemptPhysical.continuationCode bytes) (AttemptPhysical.continuationPolicy bytes) fuel execution.2)

def localRun (bytes : List UInt8) (fuel : Nat) :=
  runLocalBlock ctx (AttemptPhysical.continuationCode bytes) (AttemptPhysical.continuationPolicy bytes) fuel
    (run (.error (.revert bytes))).2.2

theorem completes : (localRun [0xde,0xad] 32).isSome := by decide +kernel

def completed : LocalBlockOutcome ctx ⟨false,false⟩ := (localRun [0xde,0xad] 32).get completes

theorem words : snapshot completed.state =
    [2,2^256-1,2309737967,2307,22136,2^256-1,171*2^248] := by decide +kernel

theorem heap_retained : completed.state.2 = (HeapCatchPhysical.allocated [0xde,0xad]).2.2 := by
  have kept : completed.state.2 = (run (.error (.revert [0xde,0xad]))).2.2.2 := runLocalBlock_world ctx _ _ 32 _ (Option.some_get completes).symm
  exact kept.trans (congrArg Prod.snd (raw_and_frame_retained _))

theorem nonword_retained : completed.state.1.get memoryRef.index = (LocalValues.ofClean locals).get memoryRef.index := by
  have kept : completed.state.1.get memoryRef.index = (run (.error (.revert [0xde,0xad]))).2.2.1.get memoryRef.index :=
    runLocalBlock_nonword ctx _ _ 32 _ (Option.some_get completes).symm memoryRef memoryShape rfl
  rw [raw_and_frame_retained] at kept
  exact kept.trans CatchFunctionPhysical.nonword_retained

/-- Mutating inner locals and halting still restores the actual outer context;
post-state effects survive. This is EM.sub, not frame/journal rollback. -/
def mutatedHalt (halt : Source.Halt) : Source.EM originEnv Inner (List UInt8) := do
  Source.EM.setLocals (.cons (.memRef rfl 0) (.cons (.memRef rfl 2) .nil))
  Source.EM.modSt fun state => {state with logs := (account,[0x77])::state.logs}
  Source.EM.halt halt

def inner : Source.Locals originEnv.layout Inner := .cons (.memRef rfl 1) outer

def haltScope (halt : Source.Halt) := AttemptPhysical.companion (Source.EM.sub inner (mutatedHalt halt) : Source.EM originEnv Outer _) outer
  (HeapCatchPhysical.allocated [0xde,0xad]).2

theorem halt_scope_restored (halt : Source.Halt) : (haltScope halt).1.2.1 = outer := rfl

theorem halt_propagated (halt : Source.Halt) : (haltScope halt).1.1 = .ok (.error halt) := rfl

theorem halt_post_kept (halt : Source.Halt) : (haltScope halt).2.2.logs =
    (account,[0x77])::(HeapCatchPhysical.allocated [0xde,0xad]).2.2.logs := rfl

def wrongIndex : Source.EM originEnv Inner (List UInt8) := do
  let ref ← Source.readLoc packedStepFrame (.local (.there .here))
  Source.bytesOfRV packedStepFrame 32 (.val ref)

theorem wrong_index_reads_old_alias : (Source.EM.sub inner wrongIndex : Source.EM originEnv Outer _).run
    (outer,(HeapCatchPhysical.allocated [0xde,0xad]).2.2) =
      (Except.ok ([0xaa,0xbb],inner),(outer,(HeapCatchPhysical.allocated [0xde,0xad]).2.2)) := rfl

theorem no_empty_index {ty : Source.STy} : Source.Idx [] ty → False := by intro index; cases index

def badScopeRead : Source.EM originEnv Inner (Source.Val originEnv.layout .bool) := do
  let values ← Source.EM.locals
  Source.EM.lift (values.getAt 0 .bool)

theorem wrong_type_refused : (Source.EM.sub inner badScopeRead : Source.EM originEnv Outer _).run
    (outer,(HeapCatchPhysical.allocated [0xde,0xad]).2.2) =
      (Except.error (.stuck "local type"),(outer,(HeapCatchPhysical.allocated [0xde,0xad]).2.2)) := rfl

theorem continued_from_bound_local (bytes : List UInt8) (fuel : Nat) :
    continued (.error (.revert bytes)) fuel =
      .ok (.ok (.inr (.memRef rfl 1,bytes,localRun bytes fuel))) := by
  unfold continued
  dsimp only
  rw [bound_capture_result]
  rfl

theorem continued_complete : continued (.error (.revert [0xde,0xad])) 32 =
    .ok (.ok (.inr (.memRef rfl 1,[0xde,0xad],some completed))) := by
  rw [continued_from_bound_local]
  exact congrArg Except.ok (congrArg Except.ok (congrArg Sum.inr
    (congrArg (fun result => ((.memRef rfl 1 : Source.Val originEnv.layout (.bytes .memory)),[0xde,0xad],result))
      (Option.some_get completes).symm)))

theorem raw_retained (outcome : Except Source.Halt (List UInt8)) :
    (run outcome).2.2.1 = (HeapCatchPhysical.capture outcome).2.2.1 := rfl

theorem raw_not_clean : LocalState.clean? completed.state = none :=
  AttemptPhysical.continuation_raw _ 32 _ completed (Option.some_get completes).symm

theorem no_clean_resume (action : Source.EM originEnv ctx.tys Unit) :
    LocalState.runClean action completed.state = none := LocalState.runClean_refuses action _ raw_not_clean

theorem halt_raw_retained (halt : Source.Halt) : (haltScope halt).2.1 =
    (HeapCatchPhysical.allocated [0xde,0xad]).2.1 := rfl

/-- Existing resolved canonical rethrow reads the bound local at positive fuel.
This is the pre-existing exception, not a general try/catch selector. -/
theorem resolved_rethrow {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (address : Nat) (bytes : List UInt8) (outer : Source.Locals E.layout Γ) (state : Source.St E)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execS G F 32 0 none
      (.rethrow (.here : Source.Idx (.bytes .memory::Γ) (.bytes .memory)) : Source.RStmt E [] false ⟨false,false⟩ _ _)
      (.cons (.memRef rfl address) outer)).run (.nil,state) =
        (Except.error (.revert bytes),(.nil,state)) := by
  rw [Source.execS]
  change (do let data ← Source.heapBytes address; Source.EM.halt (.revert data) : Source.EM E [] _).run (.nil,state) = _
  rw [Source.Hoare.run_bind]
  have read : (Source.heapBytes address : Source.EM E [] _).run (.nil,state) = (Except.ok bytes,(.nil,state)) :=
    HeapCatchPhysical.bytesOf_ref_run F address bytes .nil state found
  rw [read]
  rfl

#print axioms sub_run
#print axioms bound_capture_result
#print axioms caller_scope_restored
#print axioms raw_and_frame_retained
#print axioms continued_complete
#print axioms resolved_rethrow
end Solidity.Yul.Composition.ScopeCatchPhysical
