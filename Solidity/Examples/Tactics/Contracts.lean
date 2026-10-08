import Solidity.Calculus.Close
import Solidity.Calculus.Contracts
import Solidity.Calculus.Core.Surface
import Solidity.Calculus.Core.Closers
import Solidity.Calculus.Core.Contracts

/-!
# Calls by contract

A call proved by its callee's contract (`useContract`,
`Calculus/Contracts.lean`) instead of its inlined body: the goal `"pre"`
owes `requires` with the parameters bound to the arguments, the goal
`"post"` assumes `ensures` of a result of the return type, after a
`{havoc}` of storage and ledger for a `nonpayable` callee only.  Each
contract is proved once, from its obligation
`requires → {old := storage ‖ oldNet := net} [ T r; body ] (ensures ∧ typed(r))`, by the
strategy.  The callee's locals are the call's fresh names: `se1` the
parameter, `se2` the return variable (`addOne`), `se1` the return variable
(`getTotal`).

The mutability is read off the inlined body (`Prog.within`): `addOne` is
`pure`, `getTotal` reads storage (`view`), `deposit` writes it
(`nonpayable`).

The statements read scoped (`open scoped Solidity.Core.Surface`); the
contract rule is today's, a derived rule over today's run, and a statement
reaches it through its erasure (`sol_erase`, `Calculus/Core/Contracts.lean`):
the formula is plain, so its erasure's validity proves it.  The rule's
arguments, today's formulas, are stated before the switch.
-/
namespace Solidity.Examples.Tactics.Contracts

open Proves

/-- A `pure`, a `view` and a `nonpayable` function. -/
def ContractsExample : Contract := contract!{
  uint total;
  function addOne(uint x) pure returns (uint r) { r = x + 1; }
  function getTotal() view returns (uint r) { r = total; }
  function deposit(uint v) { total += v; }
}

local instance : InContract := ⟨ContractsExample⟩

/-! The contracts and preconditions, today's formulas: the rule's arguments. -/

/-- `x == 4`. -/
def preX4 : Fml ContractsExample := dl!{ x == 4 }
/-- `total == 7`. -/
def preTotal7 : Fml ContractsExample := dl!{ total == 7 }
/-- `total == 3`. -/
def preTotal3 : Fml ContractsExample := dl!{ total == 3 }
/-- `addOne`'s `requires`. -/
def reqAddOne : Fml ContractsExample := dl!{ se1 <= 100 }
/-- `addOne`'s `ensures`. -/
def ensAddOne : Fml ContractsExample := dl!{ se2 == se1 + 1 }
/-- `getTotal`'s `ensures`. -/
def ensGetTotal : Fml ContractsExample := dl!{ se1 == total }
/-- `deposit`'s `requires`. -/
def reqDeposit : Fml ContractsExample := dl!{ total == 3 ∧ se1 == 4 }
/-- `deposit`'s `ensures`. -/
def ensDeposit : Fml ContractsExample := dl!{ total == 7 }

open scoped Solidity.Core.Surface

/-- `y = addOne(x);` by `addOne`'s contract, a `pure` callee: nothing but
the result is forgotten. -/
theorem callAddOne : ⊨ dl!{ x == 4 → [ y = addOne(x); ] y == 5 } := by
  sol_erase
  refine useContract_of_valid (Γ := [.pre preX4]) (μ := .pure)
    (req := reqAddOne) (ens := ensAddOne) ?hc ?pre ?post
  case hc =>
    apply FunContract.ofValid
    simp only [FunContract.obligation, CallRet.typed, CallRet.binders, CallRet.decl, List.map,
      Fml.conj, rangeFml, snapOld]
    sol_symex
    sol_close
  case pre =>
    simp only [Hyp.wrap]
    sol_symex
    sol_close
  case post =>
    simp only [Hyp.wrap, Mutability.anon, Fml.alls, CallRet.binders, CallRet.result, snapOld,
      List.singleton_append]
    sol_symex
    sol_close

/-- `y = getTotal();` by its contract, a `view` callee: `total` is still
`7` after the call, so `ensures` gives `y`. -/
theorem callGetTotal : ⊨ dl!{ total == 7 → [ y = getTotal(); ] y == 7 } := by
  sol_erase
  refine useContract_of_valid (Γ := [.pre preTotal7]) (μ := .view)
    (req := preTotal7) (ens := ensGetTotal) ?hc ?pre ?post
  case hc =>
    apply FunContract.ofValid
    simp only [FunContract.obligation, CallRet.typed, CallRet.binders, CallRet.decl, List.map,
      Fml.conj, rangeFml, snapOld]
    sol_symex
    sol_close
  case pre =>
    simp only [Hyp.wrap]
    sol_symex
    sol_close
  case post =>
    simp only [Hyp.wrap, Mutability.anon, Fml.alls, CallRet.binders, CallRet.result, snapOld,
      List.singleton_append]
    sol_symex
    sol_close

/-- `deposit(4);` by its contract, a `nonpayable` callee: storage is
forgotten (`{havoc}`), and `ensures` is all that is known of it. -/
theorem callDeposit : ⊨ dl!{ total == 3 → [ deposit(4); ] total == 7 } := by
  sol_erase
  refine useContract_of_valid (Γ := [.pre preTotal3]) (μ := .nonpayable)
    (req := reqDeposit) (ens := ensDeposit) ?hc ?pre ?post
  case hc =>
    apply FunContract.ofValid
    simp only [FunContract.obligation, CallRet.typed, CallRet.binders, CallRet.decl, List.map,
      Fml.conj, snapOld]
    sol_symex
    sol_close
  case pre =>
    simp only [Hyp.wrap]
    sol_symex
    sol_close
  case post =>
    -- `{havoc} (total == 7 → [ ] total == 7)`: what the callee leaves is forgotten, and
    -- `ensures` is all that is known of it
    exact fun _ _ => ⟨fun _ _ h => ⟨h, nofun⟩, nofun⟩

/-- `callAddOne`, its two goals derived one rule at a time (`⊢`). -/
theorem callAddOneWalk : ⊨ dl!{ x == 4 → [ y = addOne(x); ] y == 5 } := by
  sol_erase
  refine useContract (R := .all) (Γ := [.pre preX4]) (μ := .pure)
    (req := reqAddOne) (ens := ensAddOne) ?hc ?pre ?post
  case hc =>
    apply FunContract.ofValid
    simp only [FunContract.obligation, CallRet.typed, CallRet.binders, CallRet.decl, List.map,
      Fml.conj, rangeFml, snapOld]
    sol_symex
    sol_close
  case pre =>
    apply unfold .localValueDeclInitDrop
    apply update .localValueAssign
    apply empty
    refine close ?_
    sol_symex
    sol_close
  case post =>
    apply unfold .localValueDeclInitDrop
    apply update .localValueAssign
    apply empty
    apply updIntro
    apply allRight
    apply impRight
    apply update .localValueAssign
    apply empty
    refine close ?_
    sol_symex
    sol_close

/-- The block of a program's first call: its return variables declared,
then its body. -/
def calleeBlock {C : Contract} : Prog C → Prog C
  | .call _ _ _ ret body :: _ => ret.decl ++ body
  | _ :: P => calleeBlock P
  | [] => []

/-- `addOne` is `pure`, `getTotal` `view` only, `deposit` `nonpayable` only. -/
example : [Mutability.pure, .view, .nonpayable].map
    (Prog.within · (calleeBlock sol{ uint y = addOne(1); })) = [true, true, true] := rfl
example : [Mutability.pure, .view, .nonpayable].map
    (Prog.within · (calleeBlock sol{ uint y = getTotal(); })) = [false, true, true] := rfl
example : [Mutability.pure, .view, .nonpayable].map
    (Prog.within · (calleeBlock sol{ deposit(1); })) = [false, false, true] := rfl

/-- The frame fact of a `view` callee: its run leaves storage as it was. -/
example (σ τ : Semantics.State) (h : Prog.run σ (calleeBlock sol{ uint y = getTotal(); }) = .ok τ) :
    τ.storage = σ.storage := (Prog.view_frame rfl h).1

end Solidity.Examples.Tactics.Contracts
