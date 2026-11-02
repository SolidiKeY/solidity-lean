import Solidity.Backend.InternalFlow.RuntimeWorld
import Solidity.Backend.InternalFlow.EvaluatedRevert

/-! A model-level caller result rejection evaluated in an ACTUAL successful
world frame, then consumed by the existing checked emitter/local journal.
Explicit slice/journal hooks are NOT a world/word-memory representation. -/
namespace Solidity.Backend.InternalFlow.WorldResultEmission
open ContractWorld Backend.Failure
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

/-- Use the existing typed revert evaluator as the caller's rejecting result
handler. No payload evaluator, codec or call/world semantics is redefined. -/
def rejectingEntry {C : Contract} {α : Type} (method : Entry C α)
    (parts : List (RevPart C method.locals)) : Entry C Unit :=
  ⟨method.locals,method.body,fun state => (TRun.revertData parts state).map (fun _ => ()),method.payable⟩

theorem same_frame {k : K} {α : Type} (world : World contracts) (self : Handle k)
    (method : Entry (contracts k) α) (parts : List (RevPart (contracts k) method.locals))
    (context : Context) :
    world.callFrame self (rejectingEntry method parts) context = world.callFrame self method context := rfl

/-- Frame execution supplies the real state in which the typed payload parts
are evaluated. The error returns no state or world, and proves no rollback. -/
theorem world_rejection {k : K} {α : Type} (world next : World contracts)
    (self : Handle k) (method : Entry (contracts k) α) (context : Context)
    (state : State (contracts k) method.locals)
    (frame : world.callFrame self method context = .ok (next,state))
    (parts : List (RevPart (contracts k) method.locals)) (chunks : List (List UInt8))
    (evaluated : parts.mapM (·.evalT state) = .ok chunks) :
    world.call self (rejectingEntry method parts) context = .error (THalt.ofData chunks.flatten) := by
  apply RuntimeWorld.decode_failure world next self (rejectingEntry method parts) context state _
  · exact (same_frame world self method parts context).trans frame
  · change (TRun.revertData parts state).map (fun _ => ()) = _
    rw [evaluated_revert_execution state parts chunks evaluated]
    rfl

/-- The ACTUAL world result selects the checked emitted byte payload, including
ordered concatenation and normalized empty/nonempty revert. No panic conversion. -/
theorem checked_rejection {k : K} {α : Type} (world next : World contracts)
    (self : Handle k) (method : Entry (contracts k) α) (context : Context)
    (state : State (contracts k) method.locals)
    (frame : world.callFrame self method context = .ok (next,state))
    (parts : List (RevPart (contracts k) method.locals)) (chunks : List (List UInt8))
    (evaluated : parts.mapM (·.evalT state) = .ok chunks)
    (offset : Nat) (suffix : Program) (machine : Slice.Machine)
    (fits : Fits offset chunks.flatten) (room : machine.stack.length + 2 ≤ 1024) :
    checkedRuntimeRevert (world.call self (rejectingEntry method parts) context) offset suffix machine =
      some ({machine with memory := Slice.putBytes machine.memory offset chunks.flatten},
        some (.revert chunks.flatten)) :=
  checked_runtime_revert _ _ (world_rejection world next self method context state frame parts chunks evaluated)
    offset suffix machine fits room

/-- Live projected roots are taken from the separately witnessed successful
frame state BEFORE rejection. No lost error-valued State is reconstructed.
The saved journal and byte machine remain explicit representation hooks. -/
theorem local_rejection {k : K} {α : Type} {P T : Ty}
    (world next : World contracts) (self : Handle k) (method : Entry (contracts k) α)
    (context : Context) (state : State (contracts k) method.locals)
    (frame : world.callFrame self method context = .ok (next,state))
    (persistent : Storage.RegionRoot (contracts k) false P)
    (transient : Storage.RegionRoot (contracts k) true T)
    (parts : List (RevPart (contracts k) method.locals)) (chunks : List (List UInt8))
    (evaluated : parts.mapM (·.evalT state) = .ok chunks)
    (saved : Storage (contracts k)) (caller machine : Slice.Machine) (offset : Nat)
    (fits : Fits offset chunks.flatten) (room : machine.stack.length + 2 ≤ 1024) :
    localRuntimeRevert (world.call self (rejectingEntry method parts) context)
      (Local.save (rootJournal persistent transient saved caller)) offset
      (rootJournal persistent transient state.storage machine) =
      some (rootJournal persistent transient saved caller,.revert chunks.flatten) :=
  local_runtime_revert _ _ (world_rejection world next self method context state frame parts chunks evaluated)
    _ offset _ fits room
/-- Revert parts evaluated INSIDE a callee after its actual successful body
bodyPrefix. Body-local memory and actual changed roots are still available here. -/
theorem callee_rejection {C : Contract} {Γ Δ ps rs Γf : Ctx}
    (caller : State C Γ) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (bodyPrefix : Prog C (rs ++ ps) Γf) (arguments : TEnv C caller.H ps)
    (evaluatedArgs : args.evalT caller = .ok arguments)
    (out : Out C (ret.enterT (caller.withEnv arguments)).st.H Γf)
    (ran : bodyPrefix.runR (ret.enterT (caller.withEnv arguments)).st = .ok out)
    (parts : List (RevPart C Γf)) (chunks : List (List UInt8))
    (evaluated : parts.mapM (·.evalT out.st) = .ok chunks) :
    let failing := RuntimeWorld.concat bodyPrefix (.cons (.revertData parts) .nil)
    TRun.call args ret failing.ext failing.runR caller = .error (THalt.ofData chunks.flatten) := by
  let failing := RuntimeWorld.concat bodyPrefix (.cons (.revertData parts) .nil)
  have tail : (Prog.cons (Stmt.revertData parts) Prog.nil).runR out.st =
      .error (THalt.ofData chunks.flatten) := by
    change TRun.seq (TRun.revertData parts) TRun.nil out.st = _
    rw [RuntimeWorld.seq_nil]
    exact evaluated_revert_execution out.st parts chunks evaluated
  have failed : failing.runR (ret.enterT (caller.withEnv arguments)).st =
      .error (THalt.ofData chunks.flatten) := by
    rw [RuntimeWorld.concat_runR]
    simp only [TRun.seq,ran]
    rw [tail]
    rfl
  exact (RuntimeCalls.failure_iff args ret failing.ext failing.runR caller _).mpr
    (.inr ⟨arguments,evaluatedArgs,failed⟩)

/-- Forward failure composition for the existing world frame. Only actual
entry/storage/body equations are used; the error carries no successful state. -/
theorem frame_failure {k : K} {α : Type} (world : World contracts) (self : Handle k)
    (method : Entry (contracts k) α) (context : Context)
    (stored : Storage (contracts k)) (initial : State (contracts k) []) (halt : THalt)
    (admitted : (world.isLibrary k || (context.isStatic && !(emptyBody method.body))) = false)
    (lookup : world.storage? self = some stored)
    (entered : world.enter self.address context stored method.payable = .ok initial)
    (failed : method.body.run initial = .error halt) :
    world.callFrame self method context = .error halt := by
  simp only [World.callFrame,admitted,Bool.false_eq_true,↓reduceIte]
  rw [lookup]
  change ((world.enter self.address context stored method.payable).bind fun σ =>
    (method.body.run σ).bind fun o =>
      (world.finish self.address o.st).map fun next => (next,o.st)) = _
  rw [entered]
  change ((method.body.run initial).bind fun o =>
    (world.finish self.address o.st).map fun next => (next,o.st)) = _
  rw [failed]
  rfl

/-- Actual world bodyPrefix, argument evaluation and successful callee body-bodyPrefix
all precede this typed callee revert; the caller decoder is not substituted. -/
theorem world_callee_rejection {k : K} {α : Type} {Γ Δ ps rs Γf : Ctx}
    (world : World contracts) (self : Handle k) (context : Context)
    (before : Prog (contracts k) [] Γ) (name : Name)
    (args : Args (contracts k) Γ ps) (ret : CallRet Γ rs Δ)
    (bodyPrefix : Prog (contracts k) (rs ++ ps) Γf)
    (parts : List (RevPart (contracts k) Γf)) (chunks : List (List UInt8))
    (decode : State (contracts k) Δ → TRes α) (payable : Bool)
    (stored : Storage (contracts k)) (initial : State (contracts k) [])
    (caller : Out (contracts k) initial.H Γ)
    (arguments : TEnv (contracts k) caller.st.H ps)
    (out : Out (contracts k) (ret.enterT (caller.st.withEnv arguments)).st.H Γf)
    (ordinary : world.isLibrary k = false) (dynamic : context.isStatic = false)
    (lookup : world.storage? self = some stored)
    (entered : world.enter self.address context stored payable = .ok initial)
    (beforeRun : before.runR initial = .ok caller)
    (evaluatedArgs : args.evalT caller.st = .ok arguments)
    (prefixRun : bodyPrefix.runR (ret.enterT (caller.st.withEnv arguments)).st = .ok out)
    (evaluated : parts.mapM (·.evalT out.st) = .ok chunks) :
    let failing := RuntimeWorld.concat bodyPrefix (.cons (.revertData parts) .nil)
    world.call self (RuntimeWorld.entry before name args ret failing decode payable) context =
      .error (THalt.ofData chunks.flatten) := by
  let failing := RuntimeWorld.concat bodyPrefix (.cons (.revertData parts) .nil)
  let method := RuntimeWorld.entry before name args ret failing decode payable
  have callFailed : TRun.call args ret failing.ext failing.runR caller.st =
      .error (THalt.ofData chunks.flatten) :=
    callee_rejection caller.st args ret bodyPrefix arguments evaluatedArgs out prefixRun parts chunks evaluated
  have tail : (Prog.cons (Stmt.call name args ret failing) Prog.nil).runR caller.st =
      .error (THalt.ofData chunks.flatten) := by
    change TRun.seq (TRun.call args ret failing.ext failing.runR) TRun.nil caller.st = _
    rw [RuntimeWorld.seq_nil]
    exact callFailed
  have failed : method.body.run initial = .error (THalt.ofData chunks.flatten) := by
    change (RuntimeWorld.concat before (.cons (.call name args ret failing) .nil)).runR initial = _
    rw [RuntimeWorld.concat_runR]
    simp only [TRun.seq,beforeRun]
    rw [tail]
    rfl
  have admitted : (world.isLibrary k || (context.isStatic && !(emptyBody method.body))) = false := by
    rw [ordinary,dynamic]
    rfl
  have frame : world.callFrame self method context = .error (THalt.ofData chunks.flatten) :=
    frame_failure world self method context stored initial _ admitted lookup entered failed
  change world.call self method context = .error (THalt.ofData chunks.flatten)
  unfold World.call
  rw [frame]
  rfl
end Solidity.Backend.InternalFlow.WorldResultEmission
