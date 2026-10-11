import Solidity.Calculus.Spec
import Solidity.Calculus.Delab

/-!
# Obligations and specifications, scoped

`Calculus/Problem.lean` and `Calculus/Spec.lean` pinned: a constructor's
obligation and a specification's, read in their parameters' context, print
as the closer's formulas do (a hidden binder printing as nothing), and a
specification's erases to the closer's.
-/

namespace Solidity.Examples.Tactics.Spec

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
      ⟨ constructor(a); ⟩ true } : Fml Ledger []
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
        (result = find(old, count) + amount ∧ net(msg.sender) = net(oldNet, msg.sender) + msg.value) } : Fml Ledger []
-/
#guard_msgs in #check cspec!{ add }

/--
info: dl{
  ((0 <= a ∧ a <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) ∧ msg.value = 0) →
    { storage := mtSt ‖ net := store(mtSt, at(msg.sender), msg.value) ‖ selfBalance := msg.value }
      [ constructor(a); ] true } : Fml Ledger []
-/
#guard_msgs in #check cspec!{ constructor }

/-! Declared, so the kernel checks the scoped terms. -/

def addObligation : Fml Ledger [] := cspec!{ add }
def ctorObligation : Fml Ledger [] := cproblem!{ constructor }

/-- The two formulas are the same term (their quotations equal). -/
def sameAs (a b : Except String (Surface.Fml Ledger)) : Bool :=
  match a, b with
  | .ok φ, .ok ψ =>
    Surface.Fml.quote (Lean.mkConst ``Ledger) φ == Surface.Fml.quote (Lean.mkConst ``Ledger) ψ
  | _, _ => false

/-! Each specification's obligation erases to the closer's (`specParts`). -/

#guard sameAs ((specObligation Ledger "add").map (·.eraseS [])) (Surface.specObligation Ledger "add")
#guard sameAs ((specObligation Ledger "constructor").map (·.eraseS []))
  (Surface.specObligation Ledger "constructor")

/-! The deployment's obligation in solkey's problem syntax (`Problem.text`). -/

/--
info: \programVariables {
    int a;
}

\problem {
    {storage := mtSt || net := storeSt(mtSt, at(msgSender), msgValue) || selfBalance := msgValue} \<{ constructor(a)@Ledger; }\>(true)
}
-/
#guard_msgs in
#eval IO.println (Problem.text "Ledger" "constructor" ctorObligation)

end Solidity.Examples.Tactics.Spec
