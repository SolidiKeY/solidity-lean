import Solidity.Backend.Executable.CreationFrame

/-! Concrete consumers of the published constructor argument closure. Actual
caller reads and failing arithmetic stay outside catch; the constructor's
bound word determines its exact raw failure bytes. Intrinsic semantics only. -/
namespace Solidity.Backend.Executable.CreationArguments
open ContractWorld Semantics CreationFrame
open PaymentCheckpointChecks (contracts sender fresh other)
open WorldPrefixChecks (created paidOne)
open CreationAttempt.Controls (context payPrefix prefix_run)

def argument : Val C Γ .uint := .simple (.local (.there (.there .here)))
def actual : ContractWorld.Word := ⟨41, by decide⟩
def wrong : ContractWorld.Word := ⟨42, by decide⟩
def badArgument : Val C Γ .uint :=
  .binop .div rfl rfl argument (.simple (.lit 0 (by decide)))
def body : Prog C [.val .uint] [.val .uint] :=
  .cons (.revertData [.word (.simple (.local .here))]) .nil
def ctor (a : ContractWorld.Word) : Prog C [] [] := CreationTryFrame.constructorArg body a
def bytes : List UInt8 := wordBytes 41

theorem actual_argument : argument.evalT caller = .ok actual := rfl
theorem no_short_circuit : BinOp.shortT (p := .uint) .div actual = none := rfl
theorem arithmetic_argument_failure : badArgument.evalT caller = .error .revert := rfl

/-- Component binding witness at State.init C; the full creation theorem below
separately executes the actual world-entered frame. The existing closure binds
the evaluated word in a fresh typed constructor frame; this binding is not a substitution into an untyped source body. -/
theorem binding : TRun.declLocal .uint (some (.simple (.lit actual.1 actual.2))) (State.init C) =
    .ok ⟨(State.init C).push (t := .val .uint) actual, List.prefix_refl _⟩ :=
  CreationTryFrame.argument_binding (State.init C) actual

private def halt {α : Type} : TRes α → Option THalt
  | .ok _ => none | .error e => some e
private theorem failed {α : Type} (r : TRes α) (e : THalt)
    (h : halt r = some e) : r = .error e := by
  cases r with | ok x => cases h | error e' => cases Option.some.inj h; rfl

theorem actual_constructor_failure :
    paidOne.create () other (ctor actual) context = .error (.revertWith bytes) :=
  failed _ _ (by decide +kernel)
theorem wrong_constructor_failure :
    paidOne.create () other (ctor wrong) context = .error (.revertWith (wordBytes 42)) :=
  failed _ _ (by decide +kernel)

def rawHandler (e : THalt) : TStep C Γ (.mem bytesR :: Γ) :=
  TRun.litBytesT e.data TRun.nil
/-- Catch would complete normally if invoked on bare revert; thus argument bare revert
cannot be explained by a failing or refusing handler. -/
theorem raw_handler_would_complete : (rawHandler .revert caller).toOption.isSome = true := by decide +kernel

theorem raw_tail_handler_would_complete :
    (rawHandler (.revertWith [0x77]) caller).toOption.isSome = true := by decide +kernel

def attempt (args : TRes ContractWorld.Word) := CreationTryFrame.run paidOne caller args ()
  (fun _ => other) ctor (fun _ => context) Ext.refl ok (Ext.push .refl) rawHandler

def branch : TRes (Out C caller.H Γ) :=
  TRun.block (Ext.push .refl) (rawHandler (.revertWith bytes)) caller
private def valueOr {α : Type} (r : TRes α) (fallback : α) : α :=
  match r with | .ok x => x | .error _ => fallback
def selected : Out C caller.H Γ := valueOr branch ⟨caller, List.prefix_refl _⟩
private theorem recover {α : Type} (r : TRes α) (fallback : α)
    (present : r.toOption.isSome = true) : r = .ok (valueOr r fallback) := by
  cases r with | ok x => rfl | error e => cases present

theorem branch_runs : branch = .ok selected :=
  recover _ _ (by decide +kernel)

/-- The real caller read flows through constructor binding and raw catch,
retaining the paid world and the old typed caller frame after local dropping. -/
theorem argument_to_catch : attempt (argument.evalT caller) = .ok (paidOne, selected) := by
  rw [actual_argument]
  exact (CreationTryFrame.caught paidOne caller actual () (fun _ => other) ctor
    (fun _ => context) Ext.refl ok (Ext.push .refl) rawHandler
    (.revertWith bytes) rfl actual_constructor_failure rfl).trans
      (congrArg (fun r => r.map (paidOne, ·)) branch_runs)

theorem argument_dependent_payload :
    (selected.st.heap.get (⟨1, by decide +kernel⟩ : HRef selected.st.H bytesR)).val.map Subtype.val =
      bytes.map (fun b => (b.toNat : Int)) ∧
    (selected.st.heap.get (⟨0, by decide +kernel⟩ : HRef selected.st.H bytesR)).val.map Subtype.val = [7,8] ∧
    (TEnv.get .here selected.st.env).map HRef.id = some 0 ∧
    (TEnv.get (.there .here) selected.st.env).map HRef.id = some 0 ∧
    (TEnv.get (.there (.there .here)) selected.st.env).val = 41 := by decide +kernel

/-- Positive argument-bearing creation/catch after the real paid prefix. -/
theorem paid_argument_catch : atomic created (payPrefix >>= fun pair =>
    CreationTryFrame.run pair.1 caller (argument.evalT caller) ()
      (fun _ => other) ctor (fun _ => context) Ext.refl ok (Ext.push .refl) rawHandler) =
      (paidOne, .ok selected) := by
  rw [prefix_run]
  simp only [bind, Except.bind]
  exact (congrArg (atomic created) argument_to_catch).trans rfl

theorem selected_wrong_payload_refused :
    (selected.st.heap.get (⟨1, by decide +kernel⟩ : HRef selected.st.H bytesR)).val.map Subtype.val ≠
      (wordBytes 42).map (fun b => (b.toNat : Int)) := by
  rw [argument_dependent_payload.1]
  decide +kernel

/-- A real typed division failure, including its non-short-circuit condition,
never invokes the constructor or the allocating raw catch. -/
theorem evaluated_argument_bypasses : attempt (badArgument.evalT caller) = .error .revert := by
  rw [arithmetic_argument_failure]
  rfl

theorem paid_argument_rollback : atomic created (payPrefix >>= fun pair =>
    CreationTryFrame.run pair.1 caller (badArgument.evalT caller) ()
      (fun _ => other) ctor (fun _ => context) Ext.refl ok (Ext.push .refl) rawHandler) =
      (created, .error .revert) := by
  rw [prefix_run, arithmetic_argument_failure]
  rfl

/-- A raw handler would complete on77, but cannot re-catch this selected-tail
failure. Its exact halt survives after actual argument-dependent creation. -/
theorem argument_tail_failure :
    CreationTryFrame.tail caller (attempt (argument.evalT caller)) badTail =
      .error (.revertWith [0x77]) :=
  CreationTryFrame.tail_body_failure paidOne caller _ selected badTail _ argument_to_catch rfl

theorem paid_tail_rollback : atomic created (payPrefix >>= fun pair =>
    CreationTryFrame.tail caller
      (CreationTryFrame.run pair.1 caller (argument.evalT caller) ()
        (fun _ => other) ctor (fun _ => context) Ext.refl ok (Ext.push .refl) rawHandler) badTail) =
      (created, .error (.revertWith [0x77])) := by
  rw [prefix_run]
  simp only [bind, Except.bind]
  exact CreationTryFrame.atomic_tail_failure created paidOne caller _ selected badTail _ argument_to_catch rfl

theorem wrong_word_refused : bytes ≠ wordBytes 42 ∧ bytes ≠ CreationFrame.payload := by decide +kernel
theorem raw_is_not_error_reason : CatchKind.decode .reason bytes = none := by decide +kernel

/-- info: 'Solidity.Backend.Executable.CreationArguments.actual_argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_argument
/-- info: 'Solidity.Backend.Executable.CreationArguments.no_short_circuit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms no_short_circuit
/-- info: 'Solidity.Backend.Executable.CreationArguments.arithmetic_argument_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms arithmetic_argument_failure
/-- info: 'Solidity.Backend.Executable.CreationArguments.binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms binding
/-- info: 'Solidity.Backend.Executable.CreationArguments.actual_constructor_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_constructor_failure
/-- info: 'Solidity.Backend.Executable.CreationArguments.wrong_constructor_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_constructor_failure
/-- info: 'Solidity.Backend.Executable.CreationArguments.raw_handler_would_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_handler_would_complete
/-- info: 'Solidity.Backend.Executable.CreationArguments.raw_tail_handler_would_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_tail_handler_would_complete
/-- info: 'Solidity.Backend.Executable.CreationArguments.branch_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms branch_runs
/-- info: 'Solidity.Backend.Executable.CreationArguments.argument_to_catch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms argument_to_catch
/-- info: 'Solidity.Backend.Executable.CreationArguments.argument_dependent_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms argument_dependent_payload
/-- info: 'Solidity.Backend.Executable.CreationArguments.paid_argument_catch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms paid_argument_catch
/-- info: 'Solidity.Backend.Executable.CreationArguments.selected_wrong_payload_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_wrong_payload_refused
/-- info: 'Solidity.Backend.Executable.CreationArguments.evaluated_argument_bypasses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evaluated_argument_bypasses
/-- info: 'Solidity.Backend.Executable.CreationArguments.paid_argument_rollback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms paid_argument_rollback
/-- info: 'Solidity.Backend.Executable.CreationArguments.argument_tail_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms argument_tail_failure
/-- info: 'Solidity.Backend.Executable.CreationArguments.paid_tail_rollback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms paid_tail_rollback
/-- info: 'Solidity.Backend.Executable.CreationArguments.wrong_word_refused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms wrong_word_refused
/-- info: 'Solidity.Backend.Executable.CreationArguments.raw_is_not_error_reason' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms raw_is_not_error_reason
end Solidity.Backend.Executable.CreationArguments
