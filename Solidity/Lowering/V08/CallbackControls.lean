import Solidity.Lowering.V08.Controls
import Solidity.Semantics.Callback

/-!
# A funded intrinsic callback outcome and its world snapshots

This instantiates the published invariant/havoc callback relation. It does not
execute a concrete callback body or establish a source reentrant history, and
it does not identify relational ExecP with deterministic World.call.
-/
namespace Solidity.Lowering.V08.CallbackControls
open Solidity.ContractWorld
open Solidity.Lowering.V08.Controls

def before : World catalog := setup.toOption.getD initial
def entered : State Cell [] :=
  { storage := Storage.init Cell, H := [], heap := Heap.empty, env := (), selfBalance := ⟨7, by decide +kernel⟩, net := [(sender.1, 7)], tx := paidCtx.tx before self }
def keep : StateInv Cell := ⟨fun _ => True, true⟩
def recipient : Address := ⟨⟨9, by decide +kernel⟩, by decide +kernel⟩
def payment : Stmt Cell [] [] := .transfer (.simple (.lit 9 rfl)) (.simple (.lit 3 rfl))
def body : Prog Cell [] [] := .cons payment .nil
def changed : Storage Cell :=
  let first := ((Storage.init Cell).write (SRef.ofRoot "saved" rfl) (.prim ⟨5, rfl⟩)).getD (Storage.init Cell)
  (first.write (SRef.ofRoot "scratch" rfl) (.prim ⟨17, rfl⟩)).getD first

def resumed : Out Cell entered.H [] :=
  let paid := entered.pay ⟨9, rfl⟩ 3
  ⟨paid.havoc changed paid.net paid.selfBalance, List.prefix_refl _⟩

/-- A nonzero funded transfer admits this actual storage-changing callback
outcome, retaining the transfer's output ledger and live balance. -/
theorem callback_transfer : ExecS keep entered payment (.ok resumed) :=
  .transferResume (J := keep) (σ := entered)
    (r := .simple (.lit 9 rfl)) (a := .simple (.lit 3 rfl))
    (o₁ := ⟨entered.pay ⟨9, rfl⟩ 3, List.prefix_refl _⟩)
    (st := changed) (nt := (entered.pay ⟨9, rfl⟩ 3).net)
    (sb := (entered.pay ⟨9, rfl⟩ 3).selfBalance) rfl rfl trivial trivial

/-- The callback is part of a complete published intrinsic program run. -/
theorem callback_program : ExecP keep entered body (.ok resumed) := by
  exact ExecP.cons callback_transfer ExecP.nil

def after : World catalog := (before.finish (k := ()) self resumed.st).toOption.getD before

/-- The witness ties actual paid entry, relational callback execution and actual
world settlement together; no caller-selected preservation equation is assumed. -/
theorem callback_committed :
    ∃ (state : State Cell []) (out : Out Cell state.H []) (next : World catalog),
      before.storage? (⟨self⟩ : Handle ()) = some (Storage.init Cell) ∧
      before.enter (k := ()) self paidCtx (Storage.init Cell) true = .ok state ∧
      ExecP keep state body (.ok out) ∧
      before.finish (k := ()) self out.st = .ok next ∧
      observe next.resetTransient = some (93, 4, 5, 0) ∧
      (next.balance recipient).1 = 3 := by
  refine ⟨entered, resumed, after, ?_, ?_, callback_program, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · have success : (before.finish (k := ()) self resumed.st).isOk = true := by decide +kernel
    unfold after
    cases h : before.finish (k := ()) self resumed.st with
    | error halt => rw [h] at success; cases success
    | ok next => rfl
  · decide +kernel
  · decide +kernel

def lateFailure : World catalog × TRes Unit := atomic before (do
  let _ ← before.finish (k := ()) self resumed.st
  (.error (.revertWith [0xfa, 0x11]) : TRes (World catalog × Unit)))
def failureView : Option (Int × Int × Int × Int) × Option (List UInt8) :=
  (observe lateFailure.1, match lateFailure.2 with | .error (.revertWith bytes) => some bytes | _ => none)

/-- A later ancestor failure restores the raw atomic entry snapshot after the
same verified callback settlement, retaining the exact failure bytes. -/
theorem callback_after_failure : failureView = (some (100, 0, 0, 0), some [0xfa, 0x11]) := by decide +kernel

/-- The successful callback's snapshot is wrong for the ancestor rollback. -/
theorem callback_wrong_frame : failureView ≠ (some (93, 4, 5, 0), some [0xfa, 0x11]) := by
  rw [callback_after_failure]
  decide +kernel

#print axioms callback_transfer
#print axioms callback_program
#print axioms callback_committed
#print axioms callback_after_failure
#print axioms callback_wrong_frame
end Solidity.Lowering.V08.CallbackControls
