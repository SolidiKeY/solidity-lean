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
  refine ProvesC.fmlValid ?_
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
      sol_decide
    case upd =>
      sol_leaf
      sol_close
    case upd =>
      sol_leaf
      sol_decide
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

/-! ## A payment's operand captured

`to.transfer(balance)` is `uint se = balance; to.transfer(se)`
(`transfer_unfold_rightSndArgument`), the capture firing though the
transfer calls back (`Stmt.CapturesAs.transferAmt`); a value call's amount
the same (`send_unfold_rightSndArgument`, `Stmt.CapturesAs.sendAmt`). -/

/-- A transfer of a state variable, with callbacks. -/
theorem transferBalance :
    ValidC vaultInv dl!{ balance + paidOut == deposited →
      [ to.transfer(balance); ] balance + paidOut == deposited } := by
  sol_prove

/-- A value call of a state variable's amount. -/
theorem callBalance :
    ValidC vaultInv dl!{ balance + paidOut == deposited →
      [ (bool ok, ) = to.call{value: balance}(""); sent = ok; ]
        balance + paidOut == deposited } := by
  sol_prove

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

/-! ## Calls whose callee calls back

A call forks where its body does (`Stmt.forksIn`): one whose callee pays is
inlined under callbacks, as `internalCallExpand` inlines it, whatever it
returns: one value (`ProvesC.callVal`), a storage reference
(`ProvesC.callStorage`) or a memory one (`ProvesC.callMem`). -/

/-- A pinger whose helpers pay. -/
def Payer : Contract := contract!{
  uint pings;
  uint[] xs;
  function payOne(address t, uint x) returns (uint) {
    (bool ok, ) = t.call{value: 1}("");
    return x + 1;
  }
  function payXs(address t) returns (uint[] storage r) {
    (bool ok, ) = t.call{value: 1}("");
    r = xs;
  }
  function payMem(address t) returns (uint[2] memory r) {
    (bool ok, ) = t.call{value: 1}("");
    r[0] = 3;
  }
}

/-- `uint y = f(x)` where `f` pays: the result survives the callback. -/
theorem payOneReturns :
    ValidT .noCallback dl[Payer]{ [ uint y = payOne(to, 1); assert(y == 2); ] true } := by
  sol_prove

/-- A storage reference returned past a callback. -/
theorem payXsReturns :
    ValidT .noCallback dl[Payer]{ [ uint[] storage s = payXs(to); s.push(1); ] true } := by
  sol_prove

/-- A memory reference returned past a callback: the callee's write is
read back (a callback changes no memory). -/
theorem payMemReturns :
    ValidT .noCallback dl[Payer]{ [ uint[2] memory s = payMem(to); assert(s[0] == 3); ] true } := by
  sol_prove

/-! Its walk: the call inlined (`ProvesC.callVal`), the value call's goals. -/

/--
info: Try this:
  refine ProvesC.validT ?_
    try simp only [TransferSem.inv, TransferSem.pay]
    apply ProvesC.allIntro
    apply ProvesC.update (.key .valueDeclSkip) rfl
    apply ProvesC.callVal
    apply ProvesC.bind (.key .localValueDeclInitDrop) rfl rfl
    apply ProvesC.update (.key .localValueAssign) rfl
    apply ProvesC.bind (.key .localValueDeclInitDrop) rfl rfl
    apply ProvesC.update (.key .localValueAssign) rfl
    apply ProvesC.update (.key .valueDeclSkip) rfl
    apply ProvesC.block
    apply ProvesC.update (.key .valueDeclSkip) rfl
    apply ProvesC.send .sendWithCallbackBox
    · refine ProvesC.plain ?_ rfl
      refine Proves.updIntro ?_
      refine Proves.updIntro ?_
      exact Proves.closeTrue rfl
    · refine ProvesC.plain ?_ rfl
      apply Proves.update (Taclet.step_eq .binopAssignment)
      refine Proves.updIntro ?_
      apply Proves.update (Taclet.step_eq .localValueAssign)
      refine Proves.updIntro ?_
      apply Proves.unfold (Taclet.step_eq .assertConditionCapture)
      apply Proves.bind (Taclet.step_eq .localValueDeclInitDrop)
      apply Proves.update (Taclet.step_eq .binopAssignment)
      apply Proves.check (Taclet.step_eq .assertSimple)
      case thn =>
        refine Proves.updIntro ?_
        exact Proves.closeTrue rfl
      case els =>
        sol_leaf
        sol_close
    · refine ProvesC.plain ?_ rfl
      apply Proves.update (Taclet.step_eq .binopAssignment)
      refine Proves.updIntro ?_
      apply Proves.update (Taclet.step_eq .localValueAssign)
      refine Proves.updIntro ?_
      apply Proves.unfold (Taclet.step_eq .assertConditionCapture)
      apply Proves.bind (Taclet.step_eq .localValueDeclInitDrop)
      apply Proves.update (Taclet.step_eq .binopAssignment)
      apply Proves.check (Taclet.step_eq .assertSimple)
      case thn =>
        refine Proves.updIntro ?_
        exact Proves.closeTrue rfl
      case els =>
        sol_leaf
        sol_decide
-/
#guard_msgs in
example : ValidT .noCallback dl[Payer]{ [ uint y = payOne(to, 1); assert(y == 2); ] true } := by
  sol_derive?

/-! ## A loop by its invariant whose body calls back

`whileInvariantBox` with callbacks (`ProvesC.invBox`): the body's frame
havocs the storage (it pays), and the invariant reads locals only, which a
callback keeps. -/

/-- `n` value calls, the counter at `n` after. -/
theorem pingN :
    ValidT .noCallback dl[Pinger]{ [ uint n = pings; uint i = 0;
      /// @custom:key invariant i <= n
      while (i < n) { (bool ok, ) = to.call{value: 1}(""); i = i + 1; }; assert(i == n); ]
      true } := by
  sol_prove

/--
info: Try this:
  refine ProvesC.validT ?_
    try simp only [TransferSem.inv, TransferSem.pay]
    apply ProvesC.allIntro
    apply ProvesC.bind (.key .localValueDeclInitDrop) rfl rfl
    apply ProvesC.update (.key .storageRootReadSelect) rfl
    apply ProvesC.bind (.key .localValueDeclInitDrop) rfl rfl
    apply ProvesC.update (.key .localValueAssign) rfl
    apply ProvesC.invBox rfl
    · refine ProvesC.plain ?_ rfl
      sol_leaf
      sol_decide
    · apply ProvesC.updIntro
      apply ProvesC.update (.key .valueDeclSkip) rfl
      apply ProvesC.send .sendWithCallbackBox
      · refine ProvesC.plain ?_ rfl
        refine Proves.updIntro ?_
        refine Proves.updIntro ?_
        exact Proves.closeTrue rfl
      · refine ProvesC.plain ?_ rfl
        apply Proves.update (Taclet.step_eq .binopAssignment)
        refine Proves.updIntro ?_
        sol_leaf
        sol_close
      · refine ProvesC.plain ?_ rfl
        apply Proves.update (Taclet.step_eq .binopAssignment)
        refine Proves.updIntro ?_
        sol_leaf
        sol_close
    · refine ProvesC.plain ?_ rfl
      refine Proves.updIntro ?_
      apply Proves.unfold (Taclet.step_eq .assertConditionCapture)
      apply Proves.bind (Taclet.step_eq .localValueDeclInitDrop)
      apply Proves.update (Taclet.step_eq .binopAssignment)
      apply Proves.check (Taclet.step_eq .assertSimple)
      case thn =>
        refine Proves.updIntro ?_
        exact Proves.closeTrue rfl
      case els =>
        sol_leaf
        sol_close
-/
#guard_msgs in
example :
    ValidT .noCallback dl[Pinger]{ [ uint n = pings; uint i = 0;
      /// @custom:key invariant i <= n
      while (i < n) { (bool ok, ) = to.call{value: 1}(""); i = i + 1; }; assert(i == n); ]
      true } := by
  sol_derive?

/-- The contract's invariant kept across every iteration's callback: the
loop's invariant restates it, since the frame havocs the storage. -/
theorem pingNInv :
    ValidC pingInv dl[Pinger]{ fails <= pings → [ uint i = 0;
      /// @custom:key invariant fails <= pings
      while (i < 3) { (bool ok, ) = to.call{value: 1}(""); pings += 1; i = i + 1; }; ]
      fails <= pings } := by
  sol_prove

/-! ## No diamond over a loop that calls back

A loop whose body calls back may diverge (`ExecS.loopDiverge`): the diamond
over it never holds, by its invariant and variant or at its unwinding bound
(`holdsC_diamond_loop`), so `ProvesC` has no diamond loop rule. -/

example {Γ Γb Γ₁ Γ₀ : Ctx} {a : LoopAnn Pinger Γ} {c : Val Pinger Γ .bool}
    {body : Prog Pinger Γ Γb} {ω : Prog Pinger Γ Γ₁} {κ : Frames Pinger Γ₁ Γ₀}
    {φ : Fml Pinger Γ₀} (σ : State Pinger Γ) (hb : body.callsBack true = true) :
    ¬ holdsC pingInv.fml true σ (.modal .diamond (.cons (.loop a c body) ω) κ φ) :=
  holdsC_diamond_loop hb

end Solidity.Examples.Tactics.CallbackStrategy
