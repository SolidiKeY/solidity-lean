import Solidity.Calculus.Close
import Solidity.Tools.Run

/-!
# Constructors: a deployment from the empty storage

A contract's `constructor(…) { … }` is not one of its functions
(`Contract.ctor`), and `uint x = 5;` declares a state variable with an
initializer (`Contract.inits`).  A deployment is the program
`constructor(args);`: the elaborator inlines the constructor as any call,
the initializers first, after its parameters are bound, as solkey's
`ExpandFunctionBody` prepends them, and the call returns to no targets, a
`FunctionBodyStatement` (`functionBodyExpand`).

It starts where solkey's constructor obligation starts:
`{storage := mtSt ‖ net := storeSt(mtSt, at(msgSender), msgValue) ‖
selfBalance := msgValue}`, the empty storage, a ledger holding the
deployer's payment, and the value sent as the contract's funds.  In the
interpreter that is `Contract.deployState`, and `Contract.deploy` runs the
elaborated program from it.

`z == 0` below is what needs `mtSt`: the constructor never writes `z`, so
only the empty storage says what it holds.
-/

namespace Solidity.Examples.Tactics.Constructors

/-- One initializer, one parameter, one root nothing writes. -/
def Mini : Contract := contract!{
  uint x = 5;
  uint y;
  uint z;
  constructor(uint a) { y = a; }
}

local instance : InContract := ⟨Mini⟩

/-! ## Deploying it in the interpreter -/

/-- `constructor(7);`: the initializer, then the body, from the empty storage. -/
theorem deploySeven :
    (Mini.deploy sol{ constructor(7); } {}).map (·.storage) =
      .ok [("x", .prim (.int 5)), ("y", .prim (.int 7)), ("z", .prim (.int 0))] := by
  simp only [Contract.deploy, Contract.deployState, Contract.initStorage, Mini, List.map,
    Semantics.defaultForTy]
  rfl

/--
info: ok
balance 0
x = 5
y = 7
z = 0
-/
#guard_msgs in #deploy Mini(7)

/-- The constructor is not `payable`: a deployment with value reverts. -/
theorem deployValue : Mini.deploy sol{ constructor(7); } { msgValue := 1 } = .error .revert := rfl

/-! ## Deploying it in the calculus -/

/-- For every argument, a deployment leaves `x` initialized, `y` the
argument, and `z` as the empty storage has it. -/
theorem deployMini :
    ⊨ dl!{ ∀ uint a;
      { storage := mtSt ‖ net := store(mtSt, at(msg.sender), msg.value) ‖
        selfBalance := msg.value }
      ⟨ constructor(a); ⟩ (x == 5 ∧ y == a ∧ z == 0) } := by
  sol_symex
  sol_close_mt

-- the update prints as solkey writes it
/--
info: dl{
  { storage := mtSt ‖ net := store(mtSt, at(msg.sender), msg.value) ‖ selfBalance := msg.value }
    ⟨ constructor(a); ⟩ find(storage, z) = 0 } : Fml Mini
-/
#guard_msgs in #check dl!{ { storage := mtSt ‖ net := store(mtSt, at(msg.sender), msg.value) ‖
  selfBalance := msg.value } ⟨ constructor(a); ⟩ z == 0 }

/-- Under the box, from any storage: the roots it reads are the ones the
deployment writes, so no `mtSt` is needed. -/
theorem deployMiniBox : ⊨ dl!{ ∀ uint a; [ constructor(a); ] (x == 5 ∧ y == a) } := by
  sol_symex
  sol_close

end Solidity.Examples.Tactics.Constructors
