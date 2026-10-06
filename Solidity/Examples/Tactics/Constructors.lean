import Solidity.Calculus.Problem
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

Its obligation is solkey's: `problem!{constructor}` with no specification
(`Problem.ctor`), `spec!{constructor}` with one, which owes the invariant
without assuming it (solkey's `contracts/Counter.sol`, below).

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

/-! ## Its obligation

solkey's unspecified constructor obligation (`Problem.ctor`): the deployment
update, then the call under the diamond, and no `wt(storage)` premise. -/

/--
info: dl{
  ∀ uint a;
    { storage := mtSt ‖ net := store(mtSt, at(msg.sender), msg.value) ‖ selfBalance := msg.value }
      ⟨ constructor(a); ⟩ true } : Fml Mini
-/
#guard_msgs in #check problem!{ constructor }

/--
info: \programVariables {
    int a;
}

\problem {
    {storage := mtSt || net := storeSt(mtSt, at(msgSender), msgValue) || selfBalance := msgValue} \<{ constructor(a)@Mini; }\>(true)
}
-/
#guard_msgs in #eval IO.println (Problem.text "Mini" "constructor" problem!{ constructor })

/-- The obligation, derived: every argument deploys
(`Problem.deploy_of_valid` reads it at `Contract.deployState`). -/
theorem miniProblem : ⊨ problem!{ constructor } := by
  sol_symex
  sol_close_mt

/-- A derived obligation of no parameters is a theorem about
`Contract.deploy` (`Problem.deploy_of_valid_nil`): `constructor(7);` runs
for every deployer sending no value. -/
example (tx : Semantics.TxEnv) (hv : tx.msgValue = 0) :
    Modality.diamond.afterRun (fun _ => True) (Mini.deploy sol{ constructor(7); } tx) :=
  Problem.deploy_of_valid_nil (by
    show ⊨ dl!{ { storage := mtSt ‖ net := store(mtSt, at(msg.sender), msg.value) ‖
      selfBalance := msg.value } ⟨ constructor(7); ⟩ true }
    sol_symex
    sol_close_mt) tx (.inr hv)

end Solidity.Examples.Tactics.Constructors

/-! ## solkey's `Counter`

`keyext.solidity.examples/contracts/Counter.sol`, solkey's minimal
constructor: the initializer `limit = 5` establishes the invariant, the
body the `ensures`.  Its obligation (`spec!{constructor}`) assumes no
invariant, and owes it with the `ensures`. -/

namespace Solidity.Examples.Tactics.Constructors.SolkeyCounter

/-- `Counter.sol`, with its `@custom:key` clauses. -/
def Counter : Contract := contract!{
  invariant limit == 5;
  uint public limit = 5;
  uint public count;
  ensures count == start;
  constructor(uint start) {
    count = start;
  }
  ensures count == \old(count) + 1;
  function increment() public {
    count = count + 1;
  }
}

local instance : InContract := ⟨Counter⟩

/--
info: dl{
  ((0 <= start ∧ start <= 115792089237316195423570985008687907853269984665640564039457584007913129639935) ∧
        msg.value = 0) →
    { storage := mtSt ‖ net := store(mtSt, at(msg.sender), msg.value) ‖ selfBalance := msg.value }
      [ constructor(start); ] (find(storage, limit) = 5 ∧ find(storage, count) = start) } : Fml Counter
-/
#guard_msgs in #check spec!{ constructor }

/-- The constructor establishes the invariant and its `ensures`. -/
theorem spec_constructor : ⊨ spec!{ constructor } := by
  sol_spec

/-- `increment()` keeps the invariant. -/
theorem spec_increment : ⊨ spec!{ increment } := by
  sol_spec

/-! A `requires` of a constructor that reads the state is refused (Lean
only): solkey reads it before `storage := mtSt`, of a storage the
deployment discards. -/

/-- A constructor whose `requires` reads a state variable. -/
def ReadsState : Contract := contract!{
  uint x;
  requires x == 0;
  constructor() { x = 1; }
}

/--
error: Solidity elaboration failed: constructor: a `requires` reads the state variable x, which a deployment discards
-/
#guard_msgs in #check spec[ReadsState]{ constructor }

end Solidity.Examples.Tactics.Constructors.SolkeyCounter

