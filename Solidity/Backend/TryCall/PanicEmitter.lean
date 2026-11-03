import Solidity.Backend.TryCall.ProducerInterface
import Solidity.Backend.TryCall.PanicNormalization
import Solidity.Backend.InternalFlow.RuntimeFrameComposition

/-! Checked core emitter for the bounded, known-self H8 Panic source.
This specializes a proved all-outcome source equation; it is not a generic
external-call implementation or the original solc bytecode correspondence. -/
namespace Solidity.Backend.TryCall.PanicEmitter
open Evm Evm.Memory
open Evm.TryPanicSourceControl Evm.TryPanicSourceBody Evm.TryPanicProducer
namespace Comp
export InternalFlow.RuntimeFrame.Composition (Statement Program nil cons branch scalar equivalent)
end Comp
abbrev Γ := Evm.TryPanicSourceControl.Caller
variable {C : Contract}

def site : Site C Γ where
  returns := []
  parameters := Input
  calleeEnd := Input
  panicBinder := [.val .uint]
  okEnd := Γ
  errorEnd := Γ
  panicEnd := Handler
  otherEnd := Γ
  call := Evm.TryPanicCarrier.selfCall
  returnBinders := .nil
  ok := reject
  error := reject
  code := .some (.user "c")
  panic := panicBody
  other := reject
  arguments := Evm.TryPanicCarrier.args36
  callee := body
  self := true

def isZero : Val C Γ .bool :=
  .binop .eqB rfl rfl (.simple (.env .selfAddress rfl)) (.simple (.lit 0 rfl))
def storeCode : Stmt C Γ Γ :=
  .assignLocal .here (.simple (.lit 67 rfl))
def lowered : Stmt C Γ Γ :=
  .ite isZero (.cons .revert .nil) (.cons storeCode .nil)

/-- An actual checked REVERT instruction; no target success is possible. -/
def checkedRevert (b : Nat) (F : Frag Γ) : Comp.Statement (C := C) b F .revert where
  checked := Calls.plainStmt ⟨F,_,.revert F⟩
  safe := by
    intro L frame lo σ base m target repr room boundary capacity actual
    change (Evm.Out.revert : Evm.Out) = .ok target 0 at actual
    contradiction

def checkedLowered (b : Nat) (F : Frag Γ) : Comp.Statement (C := C) b F lowered :=
  Comp.branch isZero ⟨_,.core isZero rfl⟩
    (Comp.cons (checkedRevert b F) (Comp.nil b F))
    (Comp.cons (Comp.scalar F .here (.simple (.lit 67 rfl)) rfl) (Comp.nil b F))

theorem isZero_eval (σ : State C Γ) :
    isZero.evalT σ = .ok (decide (σ.tx.selfAddress.val = 0)) := rfl

/-- Both paths of the emitted branch, before relating it to tryCall. -/
theorem lowered_run (σ : State C Γ) :
    Stmt.run σ lowered = if σ.tx.selfAddress.val = 0 then .error .revert
      else .ok ⟨σ.setLocal .here codeWord, List.prefix_refl _⟩ := by
  change TRun.ite isZero .refl
    (TRun.seq (fun _ => .error .revert) TRun.nil) .refl
    (TRun.seq (TRun.assignLocal .here (.simple (.lit 67 rfl))) TRun.nil) σ = _
  rw [TRun.ite, isZero_eval]
  by_cases active : σ.tx.selfAddress.val = 0
  · simp only [active, decide_true, boolT, if_true]
    rfl
  · simp only [active, decide_false, boolT, if_false]
    rfl

/-- Structural source equality for every caller, not a successful-run premise. -/
theorem expansion (σ : State C Γ) :
    Prog.runSt σ (.cons lowered .nil) = Stmt.runSt σ site.statement := by
  rw [Prog.runSt_cons]
  change ((Stmt.run σ lowered).map (·.st)).bind (fun st => .ok st) =
    (Stmt.run σ (caller body)).map (·.st)
  rw [lowered_run, PanicNormalization.all_outcomes σ
    ⟨0,0,.legacy,105,σ.tx.selfAddress,σ.tx.msgSender,σ.tx.msgValue⟩]
  by_cases active : σ.tx.selfAddress.val = 0
  · rw [if_pos active]
    rfl
  · rw [if_neg active]
    rfl

/-- The SAME derived tryCall, checked code and footprint, at arbitrary entries. -/
def checked (b : Nat) (F : Frag Γ) : Comp.Statement (C := C) b F site.statement :=
  Comp.equivalent (Comp.cons (checkedLowered b F)
    (Comp.nil b (checkedLowered b F).checked.frag)) expansion

/-- Metadata for this exact checked specialization; no admitted profile added. -/
def plan (b lo pointer : Nat) (F : Frag Γ) : RF.Emission C Γ Γ where
  code := (checked (C := C) b F).checked.code
  frag := (checked (C := C) b F).checked.frag
  need := (checked (C := C) b F).checked.need
  localLimit := lo
  pointerCell := pointer
  arenaWords := fun _ => Γ.length + 1
  heapCost := (checked (C := C) b F).checked.cost

/-- Universal return transport consumes actual represented entries. -/
theorem returns (b lo pointer : Nat) (F : Frag Γ) :
    RF.ReturnClaim b F site.statement (plan (C := C) b lo pointer F) := by
  intro L frame caller base machine start entry out source
  have room : b + (checked (C := C) b F).checked.need ≤ frame :=
    Nat.le_trans entry.workspace (Nat.le_trans entry.pointerAbove (Nat.le_of_lt entry.pointerBelow))
  obtain ⟨target,addresses,run,repr,stack,extension,growth⟩ :=
    InternalFlow.RuntimeFrame.statement_endpoint (checked (C := C) b F).checked
      entry.represented room entry.capacity out source
  have footprint : InternalFlow.RuntimeFrame.Footprint.Words lo frame machine target :=
    (checked (C := C) b F).safe entry.represented entry.workspace
      (Nat.le_trans entry.pointerAbove (Nat.le_of_lt entry.pointerBelow)) entry.capacity run
  refine ⟨target,addresses,run,repr,stack,extension,growth,?_,?_⟩
  · exact (footprint pointer entry.pointerAbove entry.pointerBelow).trans entry.cursor
  · intro a lower upper
    exact footprint a lower (Nat.lt_of_lt_of_le upper (by
      have reserve := entry.reserve
      change start + (Γ.length + 1) ≤ frame at reserve
      omega))

/-- The same emitter genuinely reverts for a source bare-revert entry. -/
theorem reverts (b lo pointer : Nat) (F : Frag Γ) :
    RF.BareRevertClaim b F site.statement (plan (C := C) b lo pointer F) := by
  intro L frame caller base machine start entry source
  have room : b + (checked (C := C) b F).checked.need ≤ frame :=
    Nat.le_trans entry.workspace (Nat.le_trans entry.pointerAbove (Nat.le_of_lt entry.pointerBelow))
  rcases (checked (C := C) b F).checked.sound entry.represented room entry.capacity with
    ⟨out,target,addresses,actual,run,repr,stack,extension,growth⟩ | ⟨actual,run⟩
  · rw [source] at actual
    contradiction
  · exact run

end Solidity.Backend.TryCall.PanicEmitter
