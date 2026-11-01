import Solidity.Lowering.V08.SourceEnvironment

namespace Solidity.Lowering.V08.SourceTransient
open Solidity Source

/-- Apply the published source transaction-end operation to the execution
component only. This is not a source transaction interpreter or frame admission. -/
def endExecution {E : Source.Env} (state : Source.St E) : Source.St E :=
  {state with ex:=state.ex.endTx}

def transientUpdate {E : Source.Env} (state : Source.St E) (address : Roadmap.Address)
    (path : Source.SPath) (value : Source.Val E.layout (E.cellTy path)) : Source.St E :=
  {state with ex:=state.ex.apply (.transient address (fun cells => cells.set path (some value)))}

/-- The actual typed source write chooses the transient region and journals it.
Path type and region premises describe the selected declaration, not execution. -/
theorem transient_write {E : Source.Env} {Γ : RCtx} (frame : Fr) (path : Source.SPath)
    (transient : E.transientRoot path = true) (ordinary : frame.static = false)
    (value : Source.Val E.layout (E.cellTy path)) (locals : Source.Locals E.layout Γ)
    (state : Source.St E) :
    (Source.writeAt frame path value : Source.EM E Γ _).run (locals,state) =
      (.ok (),(locals,transientUpdate state frame.this path value)) := by
  simp only [Source.writeAt,dif_pos rfl,Source.setCell,transient,↓reduceIte,
    Source.applyOp,ordinary,Bool.false_eq_true,Source.EM.modSt,transientUpdate]
  rfl

theorem transient_static_revert {E : Source.Env} {Γ : RCtx} (frame : Fr) (path : Source.SPath)
    (transient : E.transientRoot path = true) (static : frame.static = true)
    (value : Source.Val E.layout (E.cellTy path)) (locals : Source.Locals E.layout Γ)
    (state : Source.St E) :
    (Source.writeAt frame path value : Source.EM E Γ _).run (locals,state) =
      (.error (.revert []),(locals,state)) := by
  simp only [Source.writeAt,dif_pos rfl,Source.setCell,transient,↓reduceIte,
    Source.applyOp,static,Source.EM.halt]
  rfl

/-- The actual source read after transaction end sees the declared bool default,
retaining the complete supplied post-end machine and caller locals. -/
theorem transient_bool_read_end {E : Source.Env} {Γ : RCtx} (frame : Fr) (path : Source.SPath)
    (transient : E.transientRoot path = true) (typed : E.cellTy path = .bool)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.readAt frame path .bool : Source.EM E Γ _).run (locals,endExecution state) =
      (.ok (.bool false),(locals,endExecution state)) := by
  have zero (type : Source.STy) (same : type = .bool) :
      Source.Val.default E.layout type = some (same.symm ▸ (.bool false : Source.Val E.layout .bool)) := by
    cases same
    rfl
  have declaredDefault := zero (E.cellTy path) typed
  have cancel (type : Source.STy) (same : type = .bool) :
      same ▸ (same.symm ▸ (.bool false : Source.Val E.layout .bool)) = (.bool false : Source.Val E.layout .bool) := by
    cases same
    rfl
  simp only [Source.readAt,Source.readCell,Source.EM.st,endExecution,Source.ExecState.endTx,
    Source.Transient.empty,Source.Storage.read_empty,Source.Env.lay,typed,transient,
    ↓reduceIte,declaredDefault,dite_true,cancel,Source.EM.lift,bind,pure,ExceptT.bind,ExceptT.pure,
    ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,get,getThe,
    MonadStateOf.get,liftM,monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map]

/-- Typed intrinsic reset at a selected installed owner's transient path.
The exact default lookup and uninstalled failure are preserved, not guessed. -/
theorem target_transient_reset {K : Type} [DecidableEq K] {contracts : K → Contract}
    (world : ContractWorld.World contracts) {kind : K} (handle : ContractWorld.Handle kind)
    (path : SRef (contracts kind) .bool) (transient : path.root ∈ (contracts kind).transientRoots) :
    (world.resetTransient.storage? handle).bind (fun storage => storage.find path) =
      (world.storage? handle).bind (fun _ => (Storage.init (contracts kind)).find path) := by
  rw [ContractWorld.World.resetTransient_storage?]
  cases h : world.storage? handle with
  | none => rfl
  | some storage =>
    change (Storage.resetTransient storage).find path = (Storage.init (contracts kind)).find path
    rw [Storage.resetTransient_find,if_pos transient]

/-- Source rollback uses the actual journal entry, preserving every original
world/transient/journal field. Memory/events/logs/function locals are untouched. -/
theorem transient_undo {E : Source.Env} (state : Source.St E) (address : Roadmap.Address)
    (path : Source.SPath) (value : Source.Val E.layout (E.cellTy path)) :
    {transientUpdate state address path value with
      ex:=(transientUpdate state address path value).ex.undo} = state := by
  simp only [transientUpdate,Source.ExecState.undo_apply]

/-- The source boundary clears the journal and preserves the whole world and
all remaining machine fields; it does not reset internal-call transient cells. -/
theorem end_execution_fields {E : Source.Env} (state : Source.St E) :
    (endExecution state).ex.world = state.ex.world ∧
    (endExecution state).ex.journal = [] ∧
    (endExecution state).heap = state.heap ∧
    (endExecution state).events = state.events ∧
    (endExecution state).logs = state.logs ∧
    (endExecution state).fnLocals = state.fnLocals := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms transient_write
#print axioms transient_static_revert
#print axioms transient_bool_read_end
#print axioms target_transient_reset
#print axioms transient_undo
#print axioms end_execution_fields

end Solidity.Lowering.V08.SourceTransient
