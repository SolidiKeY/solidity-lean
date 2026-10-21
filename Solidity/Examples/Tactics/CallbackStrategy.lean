import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.CallbackDerive
import Solidity.Calculus.WalkSyntax
import Solidity.Calculus.Spec
import Solidity.Calculus.SolSpec

/-!
# The strategy with callbacks

`sol_prove` and `sol_derive` on a goal read with callbacks (`ValidC`,
`ValidT`; `docs/options.md`, O3): the walk of `ProvesC`
(`Calculus/CallbackDerive.lean`), the derivations
`Examples/Tactics/Callback.lean` and `Examples/Tactics/TryCatch.lean` write
by hand, found.
-/

namespace Solidity.Examples.Tactics.CallbackStrategy

open Semantics

def Vault : Contract := contract!{ uint balance; uint paidOut; uint deposited; bool sent; }

local instance : InContract := ⟨Vault⟩

open scoped Scoped

def vaultInv : Invariant Vault := ⟨dl!{ balance + paidOut == deposited }, rfl⟩

/-- Checks, effects, interactions: the invariant kept with callbacks. -/
theorem withdrawSafe :
    ValidC vaultInv dl!{ balance + paidOut == deposited →
      [ uint amt = balance; balance = 0; paidOut += amt; to.transfer(amt); ]
        balance + paidOut == deposited } := by
  sol_prove

/-! The walk, as `sol_derive?` writes it: `Examples/Tactics/Callback.lean`'s
`withdrawSafe`, rule for rule. -/

/--
info: Try this:
  refine ProvesC.valid ?_
    apply ProvesC.allIntro
    apply ProvesC.intro
    apply ProvesC.bind (.key .localValueDeclInitDrop) rfl rfl
    apply ProvesC.update (.key .storageRootReadSelect) rfl
    apply ProvesC.update (.key .storageRootWriteStore) rfl
    apply ProvesC.update (.key .storageRootOpAssign) rfl
    apply ProvesC.callback .transferWithCallbackBox
    · refine ProvesC.plain ?_ rfl
      refine Proves.updIntro ?_
      refine Proves.updIntro ?_
      sol_leaf
      sol_close
    · refine ProvesC.plain ?_ rfl
      exact Proves.assumeInv
-/
#guard_msgs in
example :
    ValidC vaultInv dl!{ balance + paidOut == deposited →
      [ uint amt = balance; balance = 0; paidOut += amt; to.transfer(amt); ]
        balance + paidOut == deposited } := by
  sol_derive?

/-- A value call: booked, or refused, the callee keeping the invariant. -/
theorem callTo :
    ValidC vaultInv dl!{ balance + paidOut == deposited →
      [ (bool ok, ) = to.call{value: 5}(""); sent = ok; ] balance + paidOut == deposited } := by
  sol_prove

/-! ## `try`, and `noCallback` -/

/-- A pinger: how often a ping went through, and how often it failed. -/
def Pinger : Contract := contract!{ uint pings; uint fails; uint last; }

/-- `fails <= pings`. -/
def pingInv : Invariant Pinger := ⟨dl[Pinger]{ fails <= pings }, rfl⟩

/-- A `try` keeps the invariant with callbacks. -/
theorem pingKeepsInv :
    ValidC pingInv dl[Pinger]{ fails <= pings →
      [ try I(7).ping() { pings += 1; } catch { }; ] fails <= pings } := by
  sol_prove

/-- The same under `transferSemantics:noCallback`: the `try` still calls back. -/
theorem pingKeepsInv_noCallback :
    ValidT (.noCallback pingInv) dl[Pinger]{ fails <= pings →
      [ try I(7).ping() { pings += 1; } catch { }; ] fails <= pings } := by
  sol_prove

/-- A gas-limited send under `noCallback` keeps what it knows: no `{havoc}`
(`ProvesC.sendDet`), then a `try` that does call back. -/
theorem sendThenTry :
    ValidT (.noCallback pingInv) dl[Pinger]{ fails <= pings →
      [ bool ok = to.send(5); if (ok) { pings += 1; }; try I(7).ping() { } catch { }; ]
        fails <= pings } := by
  sol_prove

/-- A transfer under `noCallback` keeps what it knows too
(`transferNoCallbackBox`, no `{havoc}`): `last` is still `3` at the
`assert`, before the `try` calls back. -/
theorem transferThenTry :
    ValidT (.noCallback pingInv) dl[Pinger]{ fails <= pings →
      [ last = 3; to.transfer(1); assert(last == 3); try I(7).ping() { } catch { }; ]
        fails <= pings } := by
  sol_prove

/-! ## Diamonds: a send ends, booked or refused -/

/-- A gas-limited send under the diamond (`sendNoCallbackDiamond`'s goals,
`ProvesC.sendDetD`). -/
theorem sendEnds : ValidT .noCallback dl[Pinger]{ ⟨ bool ok = to.send(5); ⟩ true } := by
  sol_prove

/-! Its walk: `plain`, then `sendNoCallbackDiamond`'s goals, each leaf's
closer in its `sorry`'s place. -/

/--
info: Try this:
  refine ProvesC.validT ?_
    try simp only [TransferSem.inv, TransferSem.pay]
    refine ProvesC.plain ?_ rfl
    refine Proves.allRight ?_
    apply Proves.update (Taclet.step_eq .valueDeclSkip)
    apply Proves.cases (Taclet.step_eq .sendNoCallbackDiamond) rfl <;>
        (try simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]) <;>
      (try and_intros)
    case fml =>
      sol_leaf
      sol_close
    case upd =>
      sol_leaf
      sol_close
    case upd =>
      sol_leaf
      sol_close
-/
#guard_msgs in
example : ValidT .noCallback dl[Pinger]{ ⟨ bool ok = to.send(5); ⟩ true } := by
  sol_derive?

/-- A value call under the diamond, its callee keeping the invariant
(`sendWithCallbackDiamond`, `ProvesC.sendD`). -/
theorem callEnds :
    ValidC pingInv dl[Pinger]{ fails <= pings →
      ⟨ (bool ok, ) = to.call{value: 5}(""); ⟩ fails <= pings } := by
  sol_prove

/-! ## A captured condition, its branch calling back

`if (pings > 0)` is `bool se = pings > 0; if (se)` (`ifElseUnfold`): the
capture declares a value and calls nobody, so it fires though the branch
calls back (`ProvesC.capture`, `Stmt.CapturesAs.ite`). -/

/-- An `if` on a condition that is not a local, its branch a value call. -/
theorem payIfPinged :
    ValidT .noCallback dl[Pinger]{ [ if (pings > 0) { (bool ok, ) = to.call{value: 1}(""); }; ]
      true } := by
  sol_prove

/-- The same, the invariant kept across the callback. -/
theorem payIfPingedInv :
    ValidC pingInv dl[Pinger]{ fails <= pings →
      [ if (pings > fails) { (bool ok, ) = to.call{value: 1}(""); pings += 1; }; ]
        fails <= pings } := by
  sol_prove

/-! Its walk: `ifElseUnfold` by `ProvesC.capture`, then `ifElseSplit`. -/

/--
info: Try this:
  refine ProvesC.validT ?_
    try simp only [TransferSem.inv, TransferSem.pay]
    apply ProvesC.allIntro
    apply ProvesC.capture (.key .ifElseUnfold) .ite
    apply ProvesC.bind (.key .localValueDeclInitDrop) rfl rfl
    apply ProvesC.unfold (.key .binopUnfoldLeft) rfl rfl
    apply ProvesC.bind (.key .localValueDeclInitDrop) rfl rfl
    apply ProvesC.update (.key .storageRootReadSelect) rfl
    apply ProvesC.update (.key .binopAssignment) rfl
    apply ProvesC.updIntro
    apply ProvesC.split (.key .ifElseSplit)
    · apply ProvesC.update (.key .valueDeclSkip) rfl
      apply ProvesC.send .sendWithCallbackBox
      · refine ProvesC.plain ?_ rfl
        refine Proves.updIntro ?_
        refine Proves.updIntro ?_
        exact Proves.closeTrue rfl
      · refine ProvesC.plain ?_ rfl
        refine Proves.updIntro ?_
        refine Proves.updIntro ?_
        exact Proves.closeTrue rfl
      · refine ProvesC.plain ?_ rfl
        refine Proves.updIntro ?_
        refine Proves.updIntro ?_
        exact Proves.closeTrue rfl
    · refine ProvesC.plain ?_ rfl
      refine Proves.updIntro ?_
      refine Proves.updIntro ?_
      exact Proves.closeTrue rfl
-/
#guard_msgs in
example :
    ValidT .noCallback dl[Pinger]{ [ if (pings > 0) { (bool ok, ) = to.call{value: 1}(""); }; ]
      true } := by
  sol_derive?

/-! ## A loop whose body calls back

Unwound (`whileUnwind`, `ProvesC.capture` with `Stmt.CapturesAs.loop`: the
loop runs as its unwinding, or diverges, which the box accepts) to its
bound (`loopExit`, `ProvesC.loopExit`). -/

/-- Two pings, each a value call. -/
theorem pingTwice :
    ValidC pingInv dl[Pinger]{ fails <= pings →
      [ uint i = 0;
        /// @custom:key unwind 2
        while (i < 2) { (bool ok, ) = to.call{value: 1}(""); i = i + 1; }; ]
        fails <= pings } := by
  sol_prove

/-! ## The invariant a specification declares

`invariant[C]` is `C`'s `invariant` clauses as the `Invariant C` a callee
keeps (`specInv`, `Calculus/Spec.lean`), and `spec[C]{f}` the obligation
that assumes and owes it: solkey's specified problem under
`transferSemantics:withCallback`. -/

/-- The vault, its invariant declared. -/
def Bank : Contract := contract!{
  invariant balance + paidOut == deposited;
  uint balance;
  uint paidOut;
  uint deposited;
  function withdraw(address to) public {
    uint amt = balance;
    balance = 0;
    paidOut += amt;
    to.transfer(amt);
  }
}

/-! The invariant compiled: `balance + paidOut == deposited` of the storage. -/

/--
info: dl{ find(storage, balance) + find(storage, paidOut) = find(storage, deposited) } : Fml Bank []
-/
#guard_msgs in #check (cinv[Bank] : Fml Bank [])

/-- `withdraw`'s body under the invariant `Bank` declares, every payment
calling back into a contract that keeps it. -/
theorem withdraw_withCallback :
    ValidC invariant[Bank] dl[Bank]{ balance + paidOut == deposited →
      [ uint amt = balance; balance = 0; paidOut += amt; to.transfer(amt); ]
        balance + paidOut == deposited } := by
  sol_prove

/-- **`withdraw`'s specification under callbacks**: its obligation
(`spec[Bank]{withdraw}`, the invariant assumed on entry and owed on exit),
every payment calling back into a contract that keeps the declared
invariant: solkey's specified problem under `transferSemantics:withCallback`.
The call is inlined under callbacks (`ProvesC.callRets`). -/
theorem withdraw_spec : ValidC invariant[Bank] spec[Bank]{withdraw} := by
  sol_prove

end Solidity.Examples.Tactics.CallbackStrategy
