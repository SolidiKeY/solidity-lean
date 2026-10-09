import Solidity.Calculus.Core.Spec
import Solidity.Calculus.Core.Delab

/-!
# Obligations and specifications, scoped

`Calculus/Core/Spec.lean` pinned: a constructor's obligation and a
specification's, read in their parameters' context, print as today's do
(a hidden binder printing as nothing), and erase to today's.
-/

namespace Solidity.Examples.Tactics.CoreSpec

open Solidity

/-- A constructor, a snapshot of the storage and of the ledger, a result. -/
def Ledger : Contract := contract!{
  uint count;
  uint y;
  constructor(uint a) { y = a; }
  requires amount >= 0;
  ensures \result == \old(count) + amount && net(msg.sender) == \old(net(msg.sender)) + msg.value;
  function add(uint amount) public payable returns (uint) {
    count += amount;
    return count;
  }
}

local instance : InContract := ⟨Ledger⟩

/-! A deployment's obligation: the parameter bound by `∀`, at its range. -/

/--
info: dl{
  ∀ uint a;
    { storage := mtSt ‖ net := store(mtSt, at(msg.sender), msg.value) ‖ selfBalance := msg.value }
      ⟨ constructor(a); ⟩ true } : Core.Fml Ledger []
-/
#guard_msgs in #check cproblem!{ constructor }

/-! A specification's: `amount` bound by a hidden binder, `old` and
`oldNet` declared by the update at `LTy.old` and `LTy.oldNet`, `result` by
the program, which the postcondition reads. -/

/--
info: dl{
  ((0 <= amount ∧ amount <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) ∧
        (0 <= find(storage, count) ∧
              find(storage, count) <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) ∧
          msg.value >= 0 ∧ amount >= 0) →
    { old := storage ‖ oldNet := net ‖ net := store(net, at(msg.sender), net(msg.sender) + msg.value) ‖
        selfBalance := selfBalance + msg.value }
      [ uint result; result = add(amount); ]
        (result = find(old, count) + amount ∧
            net(msg.sender) = net(oldNet, msg.sender) + msg.value) } : Core.Fml Ledger []
-/
#guard_msgs in #check cspec!{ add }

/--
info: dl{
  ((0 <= a ∧ a <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) ∧ msg.value = 0) →
    { storage := mtSt ‖ net := store(mtSt, at(msg.sender), msg.value) ‖ selfBalance := msg.value }
      [ constructor(a); ] true } : Core.Fml Ledger []
-/
#guard_msgs in #check cspec!{ constructor }

/-! Declared, so the kernel checks the scoped terms. -/

def addObligation : Core.Fml Ledger [] := cspec!{ add }
def ctorObligation : Core.Fml Ledger [] := cproblem!{ constructor }

/-- The two formulas are the same term (their quotations equal). -/
def sameAs (a b : Except String (Surface.Fml Ledger)) : Bool :=
  match a, b with
  | .ok φ, .ok ψ =>
    Surface.Fml.quote (Lean.mkConst ``Ledger) φ == Surface.Fml.quote (Lean.mkConst ``Ledger) ψ
  | _, _ => false

/-! Each scoped obligation erases to today's. -/

#guard sameAs ((Core.specObligation Ledger "add").map (·.eraseS [])) (Surface.specObligation Ledger "add")
#guard sameAs ((Core.specObligation Ledger "constructor").map (·.eraseS []))
  (Surface.specObligation Ledger "constructor")
#guard sameAs ((Core.Problem.ctor Ledger .diamond).map (·.eraseS [])) (Surface.Problem.ctor Ledger .diamond)

end Solidity.Examples.Tactics.CoreSpec
