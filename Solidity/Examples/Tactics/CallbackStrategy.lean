import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.CallbackDerive
import Solidity.Calculus.WalkSyntax

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

/-! ## Diamonds: a send ends, booked or refused -/

/-- A gas-limited send under the diamond (`sendNoCallbackDiamond`'s goals,
`ProvesC.sendDetD`). -/
theorem sendEnds : ValidT .noCallback dl[Pinger]{ ⟨ bool ok = to.send(5); ⟩ true } := by
  sol_prove

/-- A value call under the diamond, its callee keeping the invariant
(`sendWithCallbackDiamond`, `ProvesC.sendD`). -/
theorem callEnds :
    ValidC pingInv dl[Pinger]{ fails <= pings →
      ⟨ (bool ok, ) = to.call{value: 5}(""); ⟩ fails <= pings } := by
  sol_prove

end Solidity.Examples.Tactics.CallbackStrategy
