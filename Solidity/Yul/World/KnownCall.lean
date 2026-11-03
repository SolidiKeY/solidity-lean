import Solidity.Yul.World.InstanceBoundary

/-! Selected source-backed CALL, including actual instance selection and value
transfer. Program input/horizon remain explicit; no deployed-code certificate. -/
namespace Solidity.Yul.World.KnownCall
open Solidity.Source
open Solidity.Roadmap (Bytes Outcome)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.CallbackSuccess (env callerExecution)

def glob (G : Glob env) := CallbackSuccess.callbackGlob G (.success [])
def entryExecution := callerExecution.apply (.account CallerFrameChecks.owner (fun a=>{a with code:=some 0}))
def parentFrame : Fr :=
  ⟨CallerFrameChecks.owner,CallerFrameChecks.sender,0,false,"Finite",true,0⟩
def input : Bytes := [17,34,51,68]
def moved := (entryExecution.apply (.account CallerFrameChecks.owner (fun a=>a.withBalance 4))).apply
  (.account CallerFrameChecks.receiver (fun a=>a.withBalance 30))
def after {Γ} (s : Source.EMState env Γ) : Source.EMState env Γ := ⟨s.1,{s.2 with ex:=moved}⟩

theorem transfer_actual : entryExecution.transfer CallerFrameChecks.owner CallerFrameChecks.receiver 7=some moved := rfl

theorem selected (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution) :
    (Source.instanceAt (glob G) CallerFrameChecks.receiver).run s=(.ok (some "Finite"),s) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  rfl

/-- All independent caller fields are arbitrary; only the actual entry
execution and selected program/context/input/horizon are fixed. -/
theorem source_run (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution) :
    (Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 7 input false).run s =
      (.ok (.success []),after s) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem source_timeout (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution) :
    (Source.callAddr (glob G) parentFrame 6 CallerFrameChecks.receiver 7 input false).run s =
      (.error .timeout,after s) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  cases G with
  | mk program pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

/-- Exact entry bridge to the real child context and pre-transfer mark. -/
theorem entry_exact (G : Glob env) (s : Source.EMState env []) (entry : s.2.ex=entryExecution) :
    (Source.callAddr (glob G) parentFrame 10 CallerFrameChecks.receiver 7 input false).run s =
    (Source.enterInstance (glob G) 9 CallerFrameChecks.receiver CallerFrameChecks.owner 7 input false "Finite" 1
      (s.2.ex.journal.length,s.2.logs.length,s.2.heap)).run (after s) := by
  rcases s with ⟨l,⟨ex,h,events,logs,fn⟩⟩
  change ex=entryExecution at entry
  subst ex
  rfl

theorem other_account (a : Roadmap.Address) (notCaller : a≠CallerFrameChecks.owner)
    (notCallee : a≠CallerFrameChecks.receiver) : moved.world.accounts a=entryExecution.world.accounts a := by
  simp only [moved,Source.ExecState.apply,World.set_other _ notCallee,World.set_other _ notCaller]

theorem transient_unchanged : moved.transient=entryExecution.transient := rfl

theorem enclosing_rollback :
    (entryExecution.enter CallerFrameChecks.receiver CallerFrameChecks.owner 7 input false).rollback moved=entryExecution :=
  Source.rollback_transfer _ _ (by decide) 7 transfer_actual _ _ _ _

/-- Narrow genuine source producer. Guards are adapter-domain checks, not EVM
failure. The actual callAddr result and actual event suffix are retained. -/
def invokeAt (horizon : Nat) (G : Glob env) : Invoke env [] :=
  fun _ frame kind target _ bytes c=>match kind with
    | .call =>
      if decide (target=CallerFrameChecks.receiver) &&
          !(Roadmap.Evm.Precompile.ofAddress? target.val).isSome &&
          decide (frame.source.this=target) && decide (frame.source.caller=CallerFrameChecks.owner) &&
          decide (frame.source.value.val=7) && !frame.source.static &&
          decide ((c.1.1.2.ex.world.accounts target).code=some 0) then
        let run := (Source.callAddr (glob G) parentFrame horizon target frame.source.value bytes false).run c.1.1
        some ((run.1,⟨⟨run.2,c.1.2⟩,c.2⟩),(run.2.2.events.drop c.1.1.2.events.length).map Observation.event)
      else none
    | .staticcall | .delegatecall => none

def invoke (G : Glob env) : Invoke env [] := invokeAt 10 G
def prefixInvoke (G : Glob env) : Invoke env [] := invokeAt 6 G

/-- Empty completed returndata performs no output writes. Ownership, extent,
header/payload and shared-state premises remain those of the actual adapter. -/
theorem empty_output {E Γ} (c : Result E Γ) (same : c.2.effects.execution=c.1.1.1.2.ex)
    (p : Placement c.1.1.1.2.heap) (a : Nat) (string : Bool) (old : Bytes) (found)
    (m : ByteView) (offset capacity : Roadmap.Word) (empty : c.2.effects.returndata=[])
    (inside : offset.val≤old.length) (header : (mload m (p.address a)).val=old.length)
    (reads : readBytes m (p.address a+32) old.length=old) :
    copyOutput c same p a string old found m offset capacity=
      (c,some ((m,c.1.1.1),(c.1.1.2,c.1.2),c.2)) := by
  have fit : offset.val+min capacity.val c.2.effects.returndata.length≤old.length := by
    simpa only [empty,List.length_nil,Nat.min_zero,Nat.add_zero] using inside
  rw [copyOutput_exact c same p a string old found m offset capacity fit header reads]
  simp only [empty,callOutput,List.take_nil,HeapWindow.splice_empty,Solidity.Backend.Environment.writeBytes]
  rw [heap_write_unchanged _ _ _ _ found,withSourceHeap_unchanged]

end Solidity.Yul.World.KnownCall
