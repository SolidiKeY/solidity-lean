import Solidity.Backend.Executable.CreationAttempt
import Solidity.Semantics.CreationTryFrame

/-! Paid-prefix consumers of the published typed creation boundary. The world
and pending caller remain separate: no World.finish or unpaid execute shortcut.
These are intrinsic world/heap executions, not source lowering or EVM CREATE. -/
namespace Solidity.Backend.Executable.CreationFrame
open ContractWorld Semantics
open PaymentCheckpointChecks (contracts sender fresh other)
open WorldPrefixChecks (created paidOne)
open CreationAttempt.Controls (context payPrefix prefix_run successful constructor_success)

abbrev C := contracts ()
abbrev Γ : Ctx := [.mem bytesR, .mem bytesR, .val .uint]
def caller : State C Γ where
  storage := Storage.init C
  H := [bytesR]
  heap := (⟨[⟨7, by decide⟩, ⟨8, by decide⟩], by decide⟩, ())
  env := (some ⟨0, rfl⟩, some ⟨0, rfl⟩, ⟨41, by decide⟩, ())
  selfBalance := ⟨3, by decide⟩
  tx := {selfAddress := sender.1}

def reason : List UInt8 := [0x62, 0x6f, 0x6f, 0x6d]
def payload : List UInt8 := encodeError reason
def failing : Prog C [] [] := .cons (.revertData [.bytes payload]) .nil

def handler : THalt → TStep C Γ (.mem bytesR :: Γ) :=
  fun e => CreationTryFrame.errorData e TRun.nil

def ok (h : Handle ()) : TStep C Γ Γ :=
  TRun.assignLocal (.there (.there .here)) (.simple (.lit h.address.1.1 h.address.1.2))
def successOut (h : Handle ()) : Out C caller.H Γ :=
  ⟨caller.setLocal (.there (.there .here)) h.address.1, List.prefix_refl _⟩

def attempt (args : TRes Unit) (ctor : Prog C [] []) :=
  CreationTryFrame.run paidOne caller args () (fun _ => other) (fun _ => ctor)
    (fun _ => context) Ext.refl ok (Ext.push .refl) handler

def branch : TRes (Out C caller.H Γ) :=
  TRun.block (Ext.push .refl) (handler (.revertWith payload)) caller

private def valueOr {α : Type} (r : TRes α) (fallback : α) : α :=
  match r with | .ok x => x | .error _ => fallback

def caughtOut : Out C caller.H Γ := valueOr branch ⟨caller, List.prefix_refl _⟩

private theorem recover {α : Type} (r : TRes α) (fallback : α)
    (ok : r.toOption.isSome = true) :
    r = .ok (valueOr r fallback) := by
  cases r with | ok x => rfl | error e => cases ok

private def halt {α : Type} : TRes α → Option THalt
  | .ok _ => none | .error e => some e
private theorem failed {α : Type} (r : TRes α) (e : THalt)
    (h : halt r = some e) : r = .error e := by
  cases r with | ok x => cases h | error e' => cases Option.some.inj h; rfl

theorem actual_decode : CatchKind.decode .reason payload = some reason := by decide +kernel

theorem constructor_failure : paidOne.create () other failing context = .error (.revertWith payload) :=
  failed _ _ (by decide +kernel)

theorem branch_allocates : branch = .ok caughtOut :=
  recover branch ⟨caller, List.prefix_refl _⟩ (by decide +kernel)

/-- Exact paid world and exact typed original caller enter the selected catch. -/
theorem caught_run : attempt (.ok ()) failing = .ok (paidOne, caughtOut) := by
  exact (CreationTryFrame.caught paidOne caller () () (fun _ => other) (fun _ => failing)
    (fun _ => context) Ext.refl ok (Ext.push .refl) handler
    (.revertWith payload) rfl constructor_failure rfl).trans
      (congrArg (fun r => r.map (paidOne, ·)) branch_allocates)

/-- Catch-local binding is gone, but its allocated object and both old aliases
remain in the actual grown heap. Pending caller funds are not world funds. -/
theorem caught_heap :
    caughtOut.st.H = [bytesR, bytesR] ∧
    (TEnv.get .here caughtOut.st.env).map HRef.id = some 0 ∧
    (TEnv.get (.there .here) caughtOut.st.env).map HRef.id = some 0 ∧
    (TEnv.get (.there (.there .here)) caughtOut.st.env).val = 41 ∧
    caughtOut.st.selfBalance.val = 3 ∧
    ((paidOne.funds sender).val, (paidOne.funds fresh).val) = (2,1) := by decide +kernel

/-- Read both actual objects through typed references, after catch-local drop. -/
theorem exact_objects :
    (caughtOut.st.heap.get (⟨0, by decide +kernel⟩ : HRef caughtOut.st.H bytesR)).val.map Subtype.val = [7,8] ∧
    (caughtOut.st.heap.get (⟨1, by decide +kernel⟩ : HRef caughtOut.st.H bytesR)).val.map Subtype.val = [98,111,111,109] := by decide +kernel

def oldLength : Val C Γ .uint := .mlen (.var .here rfl) rfl
def resume : TStep C Γ (.val .uint :: Γ) :=
  TRun.declLocal .uint (some oldLength)
def resumed : Out C caughtOut.st.H (.val .uint :: Γ) :=
  ⟨caughtOut.st.push (t := .val .uint) ⟨2, by decide⟩, List.prefix_refl _⟩
private theorem fromOption {α : Type} (r : TRes α) (a : α)
    (h : r.toOption = some a) : r = .ok a := by
  cases r with
  | error e => cases h
  | ok x => cases Option.some.inj h; rfl

theorem old_length_read : oldLength.evalT caughtOut.st = .ok ⟨2, by decide⟩ :=
  fromOption _ _ (by decide +kernel)
theorem tail_runs : resume caughtOut.st = .ok resumed := by
  simp only [resume, TRun.declLocal, old_length_read, bind, Except.bind]
  rfl

/-- The caller tail uses the allocated catch heap, not the pre-catch heap. -/
theorem resumed_run : CreationTryFrame.tail caller (attempt (.ok ()) failing) resume =
    .ok (paidOne, ⟨resumed.st, caughtOut.ext.trans resumed.ext⟩) :=
  CreationTryFrame.tail_success paidOne caller _ caughtOut resume resumed caught_run tail_runs

/-- Actual payment followed by typed catch and tail retains the paid world. -/
theorem paid_prefix_resumes :
    atomic created (payPrefix >>= fun pair =>
      CreationTryFrame.tail caller
        (CreationTryFrame.run pair.1 caller (.ok ()) () (fun _ => other) (fun _ => failing)
          (fun _ => context) Ext.refl ok (Ext.push .refl) handler) resume) =
      (paidOne, .ok (⟨resumed.st, caughtOut.ext.trans resumed.ext⟩ : Out C caller.H (.val .uint :: Γ))) := by
  rw [prefix_run]
  simp only [bind, Except.bind]
  exact (congrArg (atomic created) resumed_run).trans rfl

/-- Even catchable argument bytes bypass the allocating handler. -/
theorem argument_bypasses : attempt (.error (.revertWith [0xab])) failing =
    .error (.revertWith [0xab]) := rfl

def badTail : TStep C Γ Γ := TRun.revertData [.bytes [0x77]]
theorem selected_tail_failure :
    CreationTryFrame.tail caller (attempt (.ok ()) failing) badTail = .error (.revertWith [0x77]) :=
  CreationTryFrame.tail_body_failure paidOne caller _ caughtOut badTail _ caught_run rfl

/-- Outer rollback restores created, not paidOne, if the resumed tail fails. -/
theorem paid_outer_rollback :
    atomic created (payPrefix >>= fun pair =>
      CreationTryFrame.tail caller
        (CreationTryFrame.run pair.1 caller (.ok ()) () (fun _ => other) (fun _ => failing)
          (fun _ => context) Ext.refl ok (Ext.push .refl) handler) badTail) =
      (created, .error (.revertWith [0x77])) := by
  rw [prefix_run]
  simp only [bind, Except.bind]
  exact CreationTryFrame.atomic_tail_failure created paidOne caller _ caughtOut badTail _ caught_run rfl

private theorem success_pair (pair : World contracts × Handle ())
    (ran : paidOne.create () other .nil context = .ok pair) :
    attempt (.ok ()) .nil = .ok (pair.1, successOut pair.2) := by
  rcases pair with ⟨next, reference⟩
  exact (CreationTryFrame.success paidOne next caller () () (fun _ => other)
    (fun _ => .nil) (fun _ => context) Ext.refl ok
    (Ext.push .refl) handler reference rfl ran).trans rfl

/-- Success uses the real returned world/handle; no payload is allocated. -/
theorem success_run : attempt (.ok ()) .nil =
    .ok (successful.1, successOut successful.2) :=
  success_pair successful constructor_success

/-- The success world really installs the returned handle, rather than merely
returning a frame with a manufactured account observation. -/
theorem success_installs : ∃ st : Storage C,
    successful.1.accounts successful.2.address = some ⟨(),st⟩ := by
  cases eq : successful with
  | mk world reference =>
    have ran := constructor_success
    rw [eq] at ran
    exact World.create_installs ran

theorem returned_identity : successful.2.address = other := by decide +kernel

/-- The catch binder is fresh while selected; it is not either old alias. -/
theorem fresh_catch_binding :
    ((handler (.revertWith payload) caller).map fun (out : Out C caller.H (.mem bytesR :: Γ)) =>
      (TEnv.get .here out.st.env).map HRef.id).toOption = some (some 1) := by decide +kernel

/-- The resumed state really retains the grown heap and original aliases. -/
theorem resumed_frame :
    resumed.st.H = [bytesR,bytesR] ∧
    (TEnv.get .here resumed.st.env).val = 2 ∧
    (TEnv.get (.there .here) resumed.st.env).map HRef.id = some 0 ∧
    (TEnv.get (.there (.there .here)) resumed.st.env).map HRef.id = some 0 ∧
    (TEnv.get (.there (.there (.there .here))) resumed.st.env).val = 41 := by decide +kernel

theorem pending_identity : caller.tx.selfAddress = sender.1 ∧ caller.net = [] ∧
    caughtOut.st.tx.selfAddress = sender.1 ∧ caughtOut.st.net = [] := by decide +kernel

theorem success_handle_observed :
    (TEnv.get (.there (.there .here)) (successOut successful.2).st.env).val = other.1.val ∧
    (TEnv.get (.there (.there .here)) (successOut successful.2).st.env).val ≠ fresh.1.val := by decide +kernel

/-- Wrong world, constructor bytes, and alias identity remain observable. -/
theorem wrong_world : (paidOne.funds sender).val ≠ (created.funds sender).val := by decide +kernel
theorem wrong_bytes : payload ≠ [0xca,0xfe] ∧
    CatchKind.decode .reason ([0xca,0xfe] : List UInt8) = none := by decide +kernel
theorem wrong_alias : (TEnv.get .here caughtOut.st.env).map HRef.id ≠ some 1 := by decide +kernel

theorem malformed_not_defaulted :
    (CreationTryFrame.errorData (.revertWith [0xca,0xfe])
      (TRun.nil : TStep C (.mem bytesR :: Γ) (.mem bytesR :: Γ))) caller =
      .error (.revertWith [0xca,0xfe]) :=
  CreationTryFrame.errorData_refused _ _ _ (by decide +kernel)

theorem argument_outer_rollback :
    atomic created (payPrefix >>= fun pair =>
      CreationTryFrame.run pair.1 caller (.error (.revertWith [0xab]) : TRes Unit) ()
        (fun _ => other) (fun _ => failing) (fun _ => context)
        Ext.refl ok (Ext.push .refl) handler) =
      (created, .error (.revertWith [0xab])) := by
  rw [prefix_run]
  rfl

theorem wrong_tail_heap_refused : (TEnv.get .here resumed.st.env).val ≠ 4 := by decide +kernel

/-- info: 'Solidity.Backend.Executable.CreationFrame.actual_decode' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms actual_decode
/-- info: 'Solidity.Backend.Executable.CreationFrame.constructor_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms constructor_failure
/-- info: 'Solidity.Backend.Executable.CreationFrame.branch_allocates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms branch_allocates
/-- info: 'Solidity.Backend.Executable.CreationFrame.caught_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms caught_run
/-- info: 'Solidity.Backend.Executable.CreationFrame.caught_heap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms caught_heap
/-- info: 'Solidity.Backend.Executable.CreationFrame.exact_objects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exact_objects
/-- info: 'Solidity.Backend.Executable.CreationFrame.old_length_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms old_length_read
/-- info: 'Solidity.Backend.Executable.CreationFrame.tail_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_runs
/-- info: 'Solidity.Backend.Executable.CreationFrame.resumed_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resumed_run
/-- info: 'Solidity.Backend.Executable.CreationFrame.paid_prefix_resumes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms paid_prefix_resumes
/-- info: 'Solidity.Backend.Executable.CreationFrame.argument_bypasses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms argument_bypasses
/-- info: 'Solidity.Backend.Executable.CreationFrame.selected_tail_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_tail_failure
/-- info: 'Solidity.Backend.Executable.CreationFrame.paid_outer_rollback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms paid_outer_rollback
/-- info: 'Solidity.Backend.Executable.CreationFrame.success_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms success_run
/-- info: 'Solidity.Backend.Executable.CreationFrame.success_installs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms success_installs
/-- info: 'Solidity.Backend.Executable.CreationFrame.returned_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms returned_identity
/-- info: 'Solidity.Backend.Executable.CreationFrame.fresh_catch_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fresh_catch_binding
/-- info: 'Solidity.Backend.Executable.CreationFrame.resumed_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resumed_frame
/-- info: 'Solidity.Backend.Executable.CreationFrame.pending_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pending_identity
/-- info: 'Solidity.Backend.Executable.CreationFrame.success_handle_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms success_handle_observed
/-- info: 'Solidity.Backend.Executable.CreationFrame.wrong_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_world
/-- info: 'Solidity.Backend.Executable.CreationFrame.wrong_bytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms wrong_bytes
/-- info: 'Solidity.Backend.Executable.CreationFrame.wrong_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_alias
/-- info: 'Solidity.Backend.Executable.CreationFrame.malformed_not_defaulted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_not_defaulted
/-- info: 'Solidity.Backend.Executable.CreationFrame.argument_outer_rollback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms argument_outer_rollback
/-- info: 'Solidity.Backend.Executable.CreationFrame.wrong_tail_heap_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_tail_heap_refused
end Solidity.Backend.Executable.CreationFrame
