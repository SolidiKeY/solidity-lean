import Solidity.Yul.Composition.RethrowPhysical

/-! Actual Source runtime declaration/block over the captured heap reference.
No Source evaluator, try selector, function/frame or physical layout is replaced. -/
namespace Solidity.Yul.Composition.RuntimeBlockPhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls LocalPhysicalControls

/-- Real typed declaration; initializer reads the already bound bytes local. -/
def aliasDecl {E : Source.Env} {Γ : Source.RCtx} (index : Source.Idx Γ (.bytes .memory)) :
    Source.RStmt E [] false ⟨false,false⟩ Γ (.bytes .memory::Γ) :=
  .declInit (.local index) rfl

def aliasItems {E : Source.Env} {Γ : Source.RCtx} (index : Source.Idx Γ (.bytes .memory)) :
    Source.RItems E [] false ⟨false,false⟩ Γ (.bytes .memory::Γ) :=
  .stmt (aliasDecl index) (.stmt (.rethrow .here) .nil)

def aliasBlock {E : Source.Env} {Γ : Source.RCtx} (index : Source.Idx Γ (.bytes .memory)) :
    Source.RStmt E [] false ⟨false,false⟩ Γ Γ := .block (aliasItems index)

/-- Actual evalE local, convRV identity, getV and runtime local extension. -/
theorem declare_run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS G F (fuel+2) 0 none (aliasDecl index) inside).run (.nil,state) =
      (Except.ok (.normal (.cons (inside.get index) inside)),(.nil,state)) := by
  unfold aliasDecl
  rw [Source.execS]
  rfl

theorem tail_run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel address : Nat)
    (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (state : Source.St E) (reference : inside.get index = .memRef rfl address)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execItems G F (fuel+2) 0 none
      (.stmt (.rethrow index) .nil : Source.RItems E [] false ⟨false,false⟩ _ _) inside).run (.nil,state) =
      (Except.error (.revert bytes),(.nil,state)) := by
  rw [Source.execItems,Source.Hoare.run_bind,RethrowPhysical.exec_rethrow_succ G F fuel address bytes inside index state reference found]

theorem items_run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel address : Nat)
    (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (state : Source.St E) (reference : inside.get index = .memRef rfl address)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execItems G F (fuel+3) 0 none (aliasItems index) inside).run (.nil,state) =
      (Except.error (.revert bytes),(.nil,state)) := by
  unfold aliasItems
  rw [Source.execItems,Source.Hoare.run_bind,declare_run]
  dsimp only
  rw [Source.Hoare.run_bind,tail_run G F fuel address bytes .here _ state reference found]

theorem block_run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel address : Nat)
    (bytes : List UInt8) (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ)
    (state : Source.St E) (reference : inside.get index = .memRef rfl address)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (Source.execS G F (fuel+4) 0 none (aliasBlock index) inside).run (.nil,state) =
      (Except.error (.revert bytes),(.nil,state)) := by
  unfold aliasBlock
  rw [Source.execS,Source.Hoare.run_bind,items_run G F fuel address bytes index inside state reference found]

/-- Existing Source statement runner, with its actual empty evaluator context. -/
def executeBound {E : Source.Env} {Γ Δ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (index : Source.Idx Δ (.bytes .memory)) (inside : Source.Locals E.layout Δ) : Source.EM E Γ (List UInt8) := do
  let _ ← Source.EM.sub .nil (Source.execS G F fuel 0 none (aliasBlock index) inside)
  pure []

theorem execute_bound_run {E : Source.Env} {Γ Δ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel address : Nat)
    (bytes : List UInt8) (index : Source.Idx Δ (.bytes .memory)) (inside : Source.Locals E.layout Δ)
    (outer : Source.Locals E.layout Γ) (state : Source.St E)
    (reference : inside.get index = .memRef rfl address)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes bytes⟩) :
    (executeBound G F (fuel+4) index inside).run (outer,state) =
      (Except.error (.revert bytes),(outer,state)) := by
  unfold executeBound
  rw [Source.Hoare.run_bind,ScopeCatchPhysical.sub_run,block_run G F fuel address bytes index inside state reference found]

/-- Only a name for the ACTUAL Heap.alloc post-state used in allocRef's law. -/
def allocatedState {E : Source.Env} (state : Source.St E) (bytes : List UInt8) : Source.St E :=
  {state with heap := (state.heap.alloc ⟨.bytes .memory,.bytes bytes⟩).1}

def caught {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (result : Except Source.Halt (List UInt8)) : Source.EM E Γ (List UInt8) :=
  match result with
  | .ok bytes => pure bytes
  | .error (.revert bytes) => do
    let (ref,_) ← HeapCatchPhysical.allocateRead F bytes
    let outer ← Source.EM.locals
    executeBound G F fuel .here (.cons ref outer)
  | .error halt => Source.EM.halt halt

/-- Consumer of the actual halt-capture operation. It is NOT Source.tryStmt. -/
def runtime {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (action : Source.EM E Γ (List UInt8)) :
    Source.EM E Γ (List UInt8) := do
  let result ← Source.EM.attempt action
  caught G F fuel result

def fromOutcome {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (outcome : Solidity.Roadmap.Outcome) :
    Source.EM E Γ (List UInt8) := runtime G F fuel (Source.reraise outcome)

/-- No assumed execution oracle: the equation exposes the ACTUAL action run. -/
theorem runtime_actual {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (action : Source.EM E Γ (List UInt8)) (initial : Source.EMState E Γ) :
    (runtime G F fuel action).run initial =
      (caught G F fuel (action.run initial).1).run (action.run initial).2 := by
  unfold runtime
  rw [Source.Hoare.run_bind,AttemptPhysical.attempt_run]

theorem caught_revert {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (bytes : List UInt8)
    (outer : Source.Locals E.layout Γ) (state : Source.St E) :
    (caught G F (fuel+4) (.error (.revert bytes))).run (outer,state) =
      (Except.error (.revert bytes),(outer,allocatedState state bytes)) := by
  unfold caught
  rw [Source.Hoare.run_bind,HeapCatchPhysical.allocateRead_run]
  dsimp only
  change (executeBound G F (fuel+4) .here (.cons (.memRef rfl state.heap.next) outer)).run
    (outer,allocatedState state bytes) = _
  exact execute_bound_run G F fuel state.heap.next bytes .here _ outer _ rfl (Source.Heap.alloc_get _ _)

/-- Actual reraise→attempt→allocRef/readback→declInit/evalE→block rethrow. -/
theorem outcome_revert {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (bytes : List UInt8)
    (outer : Source.Locals E.layout Γ) (state : Source.St E) :
    (fromOutcome G F (fuel+4) (.revert bytes)).run (outer,state) =
      (Except.error (.revert bytes),(outer,allocatedState state bytes)) := by
  unfold fromOutcome
  rw [runtime_actual]
  exact caught_revert G F fuel bytes outer state

theorem outcome_success {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (bytes : List UInt8)
    (outer : Source.Locals E.layout Γ) (state : Source.St E) :
    (fromOutcome G F fuel (.success bytes)).run (outer,state) = (Except.ok bytes,(outer,state)) := rfl

theorem timeout {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (outer : Source.Locals E.layout Γ) (state : Source.St E) :
    (runtime G F fuel (Source.EM.halt .timeout)).run (outer,state) = (Except.error .timeout,(outer,state)) := rfl

theorem stuck {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (why : String)
    (outer : Source.Locals E.layout Γ) (state : Source.St E) :
    (runtime G F fuel (Source.EM.halt (.stuck why))).run (outer,state) = (Except.error (.stuck why),(outer,state)) := rfl

/-- Exact low-horizon controls of the REAL nested Source evaluator. -/
theorem block_small {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (index : Source.Idx Γ (.bytes .memory)) (inside : Source.Locals E.layout Γ) (state : Source.St E) :
    ([0,1,2,3].map fun fuel => (Source.execS G F fuel 0 none (aliasBlock index) inside).run (.nil,state)) =
      List.replicate 4 (Except.error .timeout,(Source.Locals.nil,state)) := rfl

/-- Next existing runtime hook: extReturn must preserve full REVERT data before
any ABI length/decode check, for arbitrary return signature. -/
theorem ext_return_revert {E : Source.Env} {Γ : Source.RCtx} (returns : List Source.STy)
    (bytes : List UInt8) (outer : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.extReturn returns (.revert bytes) : Source.EM E Γ _).run (outer,state) =
      ((Except.error (Source.Halt.revert bytes) : Except Source.Halt (Source.RVal E.layout (Source.STy.ret returns))),(outer,state)) := by
  unfold Source.extReturn
  rw [Source.Hoare.run_bind]
  rfl

/-- Consume a decoded result only AFTER the actual extReturn action; no decoder
or favorable return oracle. Reverts/errors stop before the discarded success. -/
def externalResult {E : Source.Env} {Γ : Source.RCtx} (returns : List Source.STy)
    (outcome : Solidity.Roadmap.Outcome) : Source.EM E Γ (List UInt8) := do
  let _ ← Source.extReturn returns outcome
  pure []

theorem external_revert {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (returns : List Source.STy) (bytes : List UInt8)
    (outer : Source.Locals E.layout Γ) (state : Source.St E) :
    (runtime G F (fuel+4) (externalResult returns (.revert bytes))).run (outer,state) =
      (Except.error (.revert bytes),(outer,allocatedState state bytes)) := by
  rw [runtime_actual]
  unfold externalResult
  rw [Source.Hoare.run_bind,ext_return_revert]
  exact caught_revert G F fuel bytes outer state

theorem short_return {E : Source.Env} {Γ : Source.RCtx}
    (outer : Source.Locals E.layout Γ) (state : Source.St E) :
    (externalResult [.bool] (.success [0xde,0xad])).run (outer,state) =
      ((Except.error (Source.Halt.revert []) : Except Source.Halt (List UInt8)),(outer,state)) := rfl

theorem short_return_caught {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (outer : Source.Locals E.layout Γ) (state : Source.St E) :
    (runtime G F (fuel+4) (externalResult [.bool] (.success [0xde,0xad]))).run (outer,state) =
      (Except.error (.revert []),(outer,allocatedState state [])) := by
  rw [runtime_actual,short_return]
  exact caught_revert G F fuel [] outer state

/-- A real inhabited raw caller/heap/prefix from the existing physical catch
witness. The supplied runtime action is ACTUAL Source.reraise, not an oracle. -/
def sample (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :=
  AttemptPhysical.companion (fromOutcome G packedStepFrame fuel (.revert bytes))
    ScopeCatchPhysical.outer AttemptPhysical.input

theorem sample_run (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    sample G bytes (fuel+4) =
      ((.ok (.error (.revert bytes)),(ScopeCatchPhysical.outer,allocatedState AttemptPhysical.input.2 bytes)),
        (AttemptPhysical.input.1,allocatedState AttemptPhysical.input.2 bytes)) := by
  unfold sample
  rw [AttemptPhysical.companion_actual,outcome_revert]

theorem sample_heap (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (sample G bytes (fuel+4)).2.2.heap.get AttemptPhysical.input.2.heap.next =
      some ⟨.bytes .memory,.bytes bytes⟩ := by
  rw [sample_run]
  exact Source.Heap.alloc_get _ _

theorem sample_prefix (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (sample G bytes (fuel+4)).2.2.logs = AttemptPhysical.input.2.logs := by rw [sample_run]; rfl

theorem sample_raw (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (sample G bytes (fuel+4)).2.1 = AttemptPhysical.input.1 := by rw [sample_run]

theorem sample_nonword (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    (sample G bytes (fuel+4)).2.1.get memoryRef.index = (LocalValues.ofClean locals).get memoryRef.index := by
  rw [sample_raw]
  exact CatchFunctionPhysical.nonword_retained

theorem sample_dead (G : Source.Glob originEnv) :
    (sample G [0xde,0xad] 32).1.1 = .ok (.error (.revert [0xde,0xad])) := by
  rw [show 32=28+4 from rfl,sample_run]

theorem sample_empty (G : Source.Glob originEnv) :
    (sample G [] 4).1.1 = .ok (.error (.revert [])) := by
  rw [show 4=0+4 from rfl,sample_run]

theorem sample_panic (G : Source.Glob originEnv) :
    (sample G (Source.panicData .assert) 32).1.1 = .ok (.error (.revert (Source.panicData .assert))) := by
  rw [show 32=28+4 from rfl,sample_run]

/-- Alias initialization can faithfully pick the WRONG old same-type reference;
complete AABB differs from DEAD despite equal length. -/
theorem wrong_alias (G : Source.Glob originEnv) (fuel : Nat) :
    (executeBound G packedStepFrame (fuel+4) (.there .here) ScopeCatchPhysical.inner).run
      (ScopeCatchPhysical.outer,allocatedState AttemptPhysical.input.2 [0xde,0xad]) =
      (Except.error (.revert [0xaa,0xbb]),(ScopeCatchPhysical.outer,allocatedState AttemptPhysical.input.2 [0xde,0xad])) := by
  apply execute_bound_run G packedStepFrame fuel 0 _ _ _ _ _ rfl
  have other : 0 ≠ AttemptPhysical.input.2.heap.next := by rw [ScopeCatchPhysical.input_next]; decide
  change (AttemptPhysical.input.2.heap.alloc ⟨.bytes .memory,.bytes [0xde,0xad]⟩).1.get 0 = _
  rw [Source.Heap.alloc_other _ _ other]
  change CatchFunctionPhysical.completed.state.2.heap.get 0 = _
  rw [CatchFunctionPhysical.caller_source_retained]
  rfl

theorem sample_raw_not_clean (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat) :
    LocalState.clean? (sample G bytes (fuel+4)).2 = none := by
  rw [sample_run]
  change (LocalValues.clean? ctx.tys CatchFunctionPhysical.completed.state.1).map _ = none
  cases clean : LocalValues.clean? ctx.tys CatchFunctionPhysical.completed.state.1 with
  | none => rfl
  | some values =>
      have bad := CatchFunctionPhysical.raw_not_clean
      unfold LocalState.clean? at bad
      rw [clean] at bad
      cases bad

theorem sample_no_clean_resume (G : Source.Glob originEnv) (bytes : List UInt8) (fuel : Nat)
    (action : Source.EM originEnv ctx.tys Unit) :
    LocalState.runClean action (sample G bytes (fuel+4)).2 = none :=
  LocalState.runClean_refuses action _ (sample_raw_not_clean G bytes fuel)

/-- A stuck runtime action keeps its actual prefix update; attempt is not a
rollback operator. This equation executes modSt and halt, with no oracle. -/
theorem stuck_post {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (why : String)
    (update : Source.St E → Source.St E) (outer : Source.Locals E.layout Γ) (state : Source.St E) :
    (runtime G F fuel (do Source.EM.modSt update; Source.EM.halt (.stuck why))).run (outer,state) =
      (Except.error (.stuck why),(outer,update state)) := rfl

#print axioms declare_run
#print axioms block_run
end Solidity.Yul.Composition.RuntimeBlockPhysical
