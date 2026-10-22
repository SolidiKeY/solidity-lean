import Solidity.Semantics.DeferredCallback
import Solidity.Syntax.Splice

/-! Callback execution checks for deferred operand capture. A resumed callback
changes the source observed by the push, broken invariants stop execution,
and allocation survives the prefix's scope. These are explicit typed capture
programs; native effectful call receivers remain pending. -/

namespace Solidity.Examples.Tactics.DeferredCallback

open Solidity.DeferredSource Solidity.DeferredSource.Callback

def CallbackContract : Contract := contract!{ uint calls; uint[] values; }

def keep : StateInv CallbackContract := ⟨fun _ => True, true⟩
def broken : StateInv CallbackContract := ⟨fun _ => False, true⟩

def before : State CallbackContract [.alias (.array .uint)] :=
  (State.init CallbackContract).push (some (SRef.ofRoot "values" rfl))

def changed : Storage CallbackContract :=
  ((Storage.init CallbackContract).write (SRef.ofRoot "calls" rfl) (.prim ⟨9, rfl⟩)).getD
    (Storage.init CallbackContract)

def paymentAt (Γ : Ctx) : Operand CallbackContract Γ .uint :=
  ⟨Γ,
    .cons (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 0 rfl))) .nil,
    .val (.read (.root "calls" rfl))⟩

abbrev payment := paymentAt [.alias (.array .uint)]

def observed {H : HTy} {Γ : Ctx} : COut CallbackContract H Γ → Option Int
  | .ok a => (Val.evalT a.st (.read (.index (.arr .dyn) (.loc (.root "values" rfl))
      (.simple (.lit 0 rfl))))).toOption.map (fun n => n.1)
  | _ => none

/-- The ordinary explicit push observes the original store. -/
example : observed (.ofRes ((pushBlock payment .here).run before)) = some 0 := by decide +kernel

/-- `to.transfer(0); values.push(calls);` reads `calls = 9` after callback resume. -/
theorem callback_reads_resumed_storage :
    ∃ o, ExecS keep before (pushBlock payment .here) o ∧ observed o = some 9 := by
  refine ⟨finishPush payment .here
    (.ok ⟨(before.pay ⟨9, rfl⟩ 0).havoc changed [], List.prefix_refl _⟩),
    pushBlock_of_prefix (J := keep) payment .here ?_, ?_⟩
  · exact .cons (.transferResume (J := keep) (σ := before) (st := changed) (nt := []) (sb := before.selfBalance)
      (r := .simple (.lit 9 rfl)) (a := .simple (.lit 0 rfl)) rfl rfl trivial trivial) .nil
  · decide +kernel

/-- `to.transfer(0); values.push(calls);` stops when its callback invariant breaks. -/
theorem callback_violation_propagates :
    ExecS broken before (pushBlock payment .here) .violated :=
  pushBlock_of_prefix (J := broken) payment .here
    (ExecP.violated (.transferViolated (J := broken) rfl rfl (fun h => h)))

def getterBody : Prog CallbackContract [.alias (.array .uint)] [.alias (.array .uint)] :=
  .cons (.rebind .here (.path (.loc (.root "values" rfl)))) .nil

def afterCapture : State CallbackContract [.alias (.array .uint), .alias (.array .uint)] :=
  before.push (some (SRef.ofRoot "values" rfl))

/-- The `to.transfer(0);` prefix resumes with the changed typed storage. -/
private theorem resume_prefix (σ : State CallbackContract Γ)
    (hpay : σ.canPay ⟨9, rfl⟩ ⟨0, rfl⟩ = true) :
    ExecP keep σ (paymentAt Γ).code
      (.ok ⟨(σ.pay ⟨9, rfl⟩ 0).havoc changed [], List.prefix_refl _⟩) :=
  .cons (.transferResume (J := keep) (σ := σ) (o₁ := ⟨σ.pay ⟨9, rfl⟩ 0, List.prefix_refl _⟩)
    (st := changed) (nt := []) (sb := (σ.pay ⟨9, rfl⟩ 0).selfBalance)
    (r := .simple (.lit 9 rfl)) (a := .simple (.lit 0 rfl)) rfl
      (by change (if σ.canPay ⟨9, rfl⟩ ⟨0, rfl⟩ then _ else _) = _; rw [hpay]; rfl)
      trivial trivial) .nil

/-- Explicit `sp = valuesRef(); to.transfer(0); sp.push(calls);` observes resumed storage. -/
theorem complete_capture_reads_resumed_storage :
    ∃ o, ExecP keep (State.init CallbackContract)
      (callProgram "valuesRef" .nil (.user "r") getterBody (paymentAt [])) o ∧
        observed (o.map (Out.drop (.push (.push .refl)))) = some 9 := by
  have hb := pushBlock_of_prefix (J := keep)
    (((paymentAt []).wk (.drop .refl)).wk (.drop .refl)) .here (resume_prefix afterCapture (by decide +kernel))
  have hp := ExecP.cons (s := .declStorage (.array .uint) (.user "sp")
    (some (.path (.alias .here)))) (σ := before) (ExecS.det rfl) (singleton_iff.mpr hb)
  have hc : ExecS keep (State.init CallbackContract)
      (.call "valuesRef" .nil (.storage (.array .uint) (.user "r")) getterBody)
      (.ok ⟨before, List.prefix_refl _⟩) :=
    .callBody (J := keep) (σ := State.init CallbackContract) (f := "valuesRef")
      (args := .nil) (ret := .storage (.array .uint) (.user "r")) (body := getterBody)
      rfl (.cons (.det rfl) .nil)
  refine ⟨_, .cons hc hp, ?_⟩
  decide +kernel

/-- An unset getter result reverts before a callback-bearing operand prefix. -/
example : ExecCall broken (State.init CallbackContract) "unset" .nil (.user "r")
    .nil (paymentAt []) (.halt .revert) :=
  .next (.callBody rfl .nil) (.captureHalt rfl)

/-- A getter that breaks the callback invariant never evaluates its operand. -/
example : ExecCall broken (State.init CallbackContract) "payingGetter" .nil (.user "r")
    (.cons (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 0 rfl))) .nil)
    (paymentAt []) .violated :=
  .violated (.callBody rfl
    (.violated (.transferViolated (J := broken) rfl rfl (fun h => h))))

def trappedPayment : Operand CallbackContract [.alias (.array .uint)] .uint :=
  { payment with value := .val (.binop .div rfl rfl (.simple (.lit 1 rfl)) (.simple (.lit 0 rfl))) }

/-- `to.transfer(0); values.push(1 / 0);`: invariant violation wins over the bad source. -/
example : ExecS broken before (pushBlock trappedPayment .here) .violated :=
  pushBlock_of_prefix (J := broken) trappedPayment .here
    (ExecP.violated (.transferViolated (J := broken) rfl rfl (fun h => h)))

/-- With no broken invariant, the same explicit program reaches its bad source. -/
example : ((pushBlock trappedPayment .here).run before).halt? = some .revert := by decide +kernel

def allocatingPaymentAt (Γ : Ctx) : Operand CallbackContract Γ .uint :=
  ⟨.mem (.array .uint) :: Γ,
    .cons (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 0 rfl)))
      (.cons (.declMem (.array .uint) (.user "tmp") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl) .nil),
    .val (.read (.root "calls" rfl))⟩

def heapLength {H : HTy} {Γ : Ctx} : COut CallbackContract H Γ → Option Nat
  | .ok a => some a.st.H.length
  | _ => none

/-- `to.transfer(0); new uint[](1); values.push(calls);`: resumed storage and grown heap survive. -/
theorem callback_allocation_survives_scope :
    ∃ o, ExecS keep before (pushBlock (allocatingPaymentAt _) .here) o ∧
      observed o = some 9 ∧ heapLength o = some 1 := by
  refine ⟨_, pushBlock_of_prefix (J := keep) (allocatingPaymentAt _) .here
    (ExecP.cons (ExecS.transferResume (J := keep) (σ := before) (st := changed) (nt := []) (sb := before.selfBalance)
      (r := .simple (.lit 9 rfl)) (a := .simple (.lit 0 rfl)) rfl rfl trivial trivial)
      (ExecP.cons (ExecS.det rfl) ExecP.nil)), ?_⟩
  decide +kernel

end Solidity.Examples.Tactics.DeferredCallback
