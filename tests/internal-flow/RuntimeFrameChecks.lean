import Solidity.Backend.InternalFlow.RuntimeWorld
import Solidity.Backend.InternalFlow.RuntimeGuardedFrame
import Solidity.Backend.InternalFlow.MemoryCallTransport
import Solidity.Backend.InternalFlow.AllocationFrameChecks

namespace Solidity.Backend.InternalFlow.RuntimeFrameChecks
open ContractWorld
open Controls (contract arrayType saved live persistent transient)
private theorem actual {α : Type} (r : TRes α) (h : r.toOption.isSome = true) :
    r = .ok (r.toOption.get h) := by
  cases r with | error e => cases h | ok value => rfl

abbrev Caller : Ctx := [.mem arrayType,.mem arrayType,.val .uint,.val .uint]
abbrev Final : Ctx := .mem arrayType :: Caller
abbrev Input : Ctx := [.mem arrayType,.mem arrayType]
def before : Prog contract [] Caller :=
 .cons (.declLocal .uint (.user "b") (some (.simple (.lit 11 rfl))))
 (.cons (.declLocal .uint (.user "a") (some (.simple (.lit 9 rfl))))
 (.cons (.declMem arrayType (.user "old") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl)
 (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl))) (.val (.simple (.lit 7 rfl))))
 (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 1 rfl))) (.val (.simple (.lit 11 rfl))))
 (.cons (.declMem arrayType (.user "same") (some (.alias (.var .here rfl))) rfl rfl) .nil)))))
def args : Args contract Caller [.mem arrayType] :=
 .snocMemory .nil arrayType (.user "old") (.var .here rfl)
def ret : CallRet Caller [.mem arrayType] Final := .mem arrayType (.user "returned") rfl rfl
def body : Prog contract Input (.mem arrayType :: Input) :=
 .cons (.declMem arrayType (.user "private") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl)
 (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl))) (.val (.simple (.lit 13 rfl))))
 (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 1 rfl))) (.val (.simple (.lit 17 rfl))))
 (.cons (.assign (.root "p" rfl) (.val (.simple (.lit 23 rfl))))
 (.cons (.assign (.root "t" rfl) (.val (.simple (.lit 29 rfl))))
 (.cons (.rebindMem (.there .here) (.alias (.var .here rfl))) .nil)))))
def selfAddress : Address := ⟨⟨1,by decide +kernel⟩,by decide +kernel⟩
def otherAddress : Address := ⟨⟨2,by decide +kernel⟩,by decide +kernel⟩
def catalog (_ : Unit) : Contract := contract
def world : World catalog :=
 { accounts := fun a => if a = selfAddress then some ⟨(),saved⟩ else
     if a = otherAddress then some ⟨(),live⟩ else none
   funds := fun _ => PrimTy.dflt .uint }
def self : Handle () := ⟨selfAddress⟩
def context : Context := ⟨otherAddress,.ordinary (PrimTy.dflt .uint),[]⟩
def decode (σ : State contract Final) : TRes (Option Nat) := .ok (σ.env.1.map HRef.id)
def method := RuntimeWorld.entry before "runtime" args ret body decode false
def initial : State contract [] :=
 (world.enter (k := ()) selfAddress context saved false).toOption.get (by decide +kernel)
def caller : Out contract initial.H Caller :=
 (before.runR initial).toOption.get (by decide +kernel)
def result : Out contract initial.H Final :=
 (method.body.run initial).toOption.get (by decide +kernel)
def next : World catalog :=
 (world.finish (k := ()) selfAddress result.st).toOption.get (by decide +kernel)

theorem stored : world.storage? self = some saved := rfl
theorem entered : world.enter (k := ()) selfAddress context saved false = .ok initial := actual _ _
theorem prefix_run : before.runR initial = .ok caller := actual _ _
theorem body_run : method.body.run initial = .ok result := actual _ _
theorem finished : world.finish (k := ()) selfAddress result.st = .ok next := actual _ _
theorem actual_world : world.callFrame self method context = .ok (next,result.st) := by
 change ((TRes.ofOpt (world.storage? self)).bind fun st =>
   (world.enter (k := ()) selfAddress context st false).bind fun σ =>
   (method.body.run σ).bind fun o =>
   (world.finish (k := ()) selfAddress o.st).map fun w => (w,o.st)) = _
 rw [stored]
 change ((world.enter (k := ()) selfAddress context saved false).bind fun σ =>
   (method.body.run σ).bind fun o => (world.finish (k := ()) selfAddress o.st).map fun w => (w,o.st)) = _
 rw [entered]
 change ((method.body.run initial).bind fun o =>
   (world.finish (k := ()) selfAddress o.st).map fun w => (w,o.st)) = _
 rw [body_run]
 change (world.finish (k := ()) selfAddress result.st).map (fun w => (w,result.st)) = _
 rw [finished]
 rfl

/-- All midpoints/arguments/body executions are DERIVED from actual world run. -/
theorem runtime_frame : ∃ (st : Storage contract) (σ : State contract [])
 (caller : Out contract σ.H Caller),
 world.storage? self = some st ∧ world.enter (k := ()) selfAddress context st false = .ok σ ∧
 before.runR σ = .ok caller ∧
 ∃ a : TEnv contract caller.st.H [.mem arrayType], args.evalT caller.st = .ok a ∧
 ∃ out : Out contract (ret.enterT (caller.st.withEnv a)).st.H (.mem arrayType :: Input),
 body.runR (ret.enterT (caller.st.withEnv a)).st = .ok out ∧
 (RuntimeCalls.returned ret body.ext caller.st a out).st = result.st ∧
 world.finish (k := ()) selfAddress result.st = .ok next ∧
 ∀ other : Address, other ≠ selfAddress → next.accounts other = world.accounts other :=
 RuntimeWorld.callFrame_success world next self context before "runtime" args ret body decode false result.st actual_world

theorem complete_observations :
 (caller.st.H.length,result.st.H.length,result.st.env.1.map HRef.id,
 result.st.env.2.1.map HRef.id,result.st.env.2.2.1.map HRef.id,
 result.st.env.2.2.2.1.1,result.st.env.2.2.2.2.1.1,
 AllocationFrameChecks.contents result.st .here,
 AllocationFrameChecks.contents result.st (.there .here),
 AllocationFrameChecks.contents result.st (.there (.there .here)),
 (result.st.storage.get persistent.declared).view.1,
 (result.st.storage.get transient.declared).view.1) =
 (1,3,some 2,some 0,some 0,9,11,some [13,17],some [7,11],some [7,11],23,29) := by
 simp only [Prod.mk.injEq]
 decide +kernel

theorem other_account : next.accounts otherAddress = world.accounts otherAddress :=
 World.finish_other finished (by decide +kernel)
theorem static_refusal :
 world.callFrame self method {context with mode := .readOnly} = .error .revert :=
 RuntimeWorld.static_refused world self _ before "runtime" args ret body decode false rfl

theorem wrong_alias : result.st.env.1.map HRef.id ≠ some 0 := by
 have actual := congrArg (fun o => o.2.2.1) complete_observations
 change result.st.env.1.map HRef.id = some 2 at actual
 rw [actual]
 decide

/-- Separate admitted readonly client: old-object mutation is NOT accepted by
withinM, and no such guard is imposed on the mixed ordinary-world client. -/
theorem guarded_client : TGFrameM .view MemoryCallTransport.caller
 MemoryCallTransport.returned.st MemoryCallTransport.returned.ext :=
 (RuntimeGuardedFrame.success .view "allocationOnly" MemoryCallTransport.args
  MemoryCallTransport.ret MemoryCallTransport.body rfl rfl
  MemoryCallTransport.caller MemoryCallTransport.returned MemoryCallTransport.actual_call).1

theorem mutating_guard_rejected : Prog.withinM .view body = false := rfl

def failingBody : Prog contract Input (.mem arrayType :: Input) :=
 RuntimeWorld.concat body (.cons (.revertData [.bytes [0xde,0,0xad]]) .nil)
def failingMethod := RuntimeWorld.entry before "failure" args ret failingBody decode false

theorem exact_world_failure : world.callFrame self failingMethod context =
 .error (.revertWith [0xde,0,0xad]) := by
 have halted : (world.callFrame self failingMethod context).halt? =
     some (.revertWith [0xde,0,0xad]) := by decide +kernel
 cases execution : world.callFrame self failingMethod context with
 | ok value =>
   have impossible : none = some (THalt.revertWith [0xde,0,0xad]) := by
     simpa only [execution,TRes.halt?] using halted
   cases impossible
 | error halt =>
   have same : some halt = some (THalt.revertWith [0xde,0,0xad]) := by
     simpa only [execution,TRes.halt?] using halted
   exact congrArg Except.error (Option.some.inj same)

theorem wrong_failure_class : world.callFrame self failingMethod context ≠ .error .revert := by
 rw [exact_world_failure]
 intro eq
 cases eq

theorem wrong_payload : world.callFrame self failingMethod context ≠
 .error (.revertWith [0xde,0xad,0]) := by
 rw [exact_world_failure]
 intro eq
 cases eq

/-- Successful caller-side decoding is checked after the actual mixed frame. -/
theorem actual_call : world.call self method context = .ok (next,some 2) := by
 apply (RuntimeWorld.call_success_iff world next self method context (some 2)).mpr
 refine ⟨result.st,actual_world,?_⟩
 have id := congrArg (fun o => o.2.2.1) complete_observations
 change result.st.env.1.map HRef.id = some 2 at id
 exact congrArg Except.ok id

def failedDecode : Entry contract (Option Nat) :=
 {method with result := fun _ => .error (.revertWith [0x99,0])}

theorem frame_before_bad_decode : world.callFrame self failedDecode context = .ok (next,result.st) :=
 actual_world

theorem decode_after_frame : world.call self failedDecode context = .error (.revertWith [0x99,0]) :=
 RuntimeWorld.decode_failure world next self failedDecode context result.st
  (.revertWith [0x99,0]) frame_before_bad_decode rfl

theorem wrong_protected_scalar : result.st.env.2.2.2.2.1.1 ≠ 9 := by
 have scalar := congrArg (fun o => o.2.2.2.2.2.2.1) complete_observations
 change result.st.env.2.2.2.2.1.1 = 11 at scalar
 rw [scalar]
 decide

#print axioms Solidity.Backend.InternalFlow.RuntimeCalls.success_iff
#print axioms Solidity.Backend.InternalFlow.RuntimeCalls.failure_iff
#print axioms Solidity.Backend.InternalFlow.RuntimeWorld.concat_runR
#print axioms Solidity.Backend.InternalFlow.RuntimeWorld.callFrame_success
#print axioms Solidity.Backend.InternalFlow.RuntimeWorld.static_refused
#print axioms Solidity.Backend.InternalFlow.RuntimeFrameChecks.actual_world
#print axioms Solidity.Backend.InternalFlow.RuntimeFrameChecks.runtime_frame
#print axioms Solidity.Backend.InternalFlow.RuntimeFrameChecks.complete_observations
#print axioms Solidity.Backend.InternalFlow.RuntimeFrameChecks.other_account
#print axioms Solidity.Backend.InternalFlow.RuntimeFrameChecks.static_refusal
#print axioms Solidity.Backend.InternalFlow.RuntimeFrameChecks.wrong_alias
#print axioms Solidity.Backend.InternalFlow.RuntimeGuardedFrame.success
#print axioms Solidity.Backend.InternalFlow.RuntimeFrameChecks.guarded_client
#print axioms Solidity.Backend.InternalFlow.RuntimeFrameChecks.mutating_guard_rejected
#print axioms Solidity.Backend.InternalFlow.RuntimeFrameChecks.exact_world_failure
#print axioms Solidity.Backend.InternalFlow.RuntimeFrameChecks.wrong_failure_class
#print axioms Solidity.Backend.InternalFlow.RuntimeFrameChecks.wrong_payload
#print axioms Solidity.Backend.InternalFlow.RuntimeWorld.call_success_iff
#print axioms Solidity.Backend.InternalFlow.RuntimeWorld.decode_failure
#print axioms Solidity.Backend.InternalFlow.RuntimeFrameChecks.actual_call
#print axioms Solidity.Backend.InternalFlow.RuntimeFrameChecks.frame_before_bad_decode
#print axioms Solidity.Backend.InternalFlow.RuntimeFrameChecks.decode_after_frame
#print axioms Solidity.Backend.InternalFlow.RuntimeFrameChecks.wrong_protected_scalar
end Solidity.Backend.InternalFlow.RuntimeFrameChecks
