import Solidity.Semantics.Run

/-!
# The deployment, typed

A deployment runs `constructor(args);` from the state a contract starts in
when it is created, after the creation code's `CALLVALUE` check.  Here, over
the typed run alone, so that `#deploy` (`Tools/Run.lean`) runs exactly what
the constructor obligation is read at (`Calculus/Deploy.lean`), without
importing the calculus.
-/

namespace Solidity

variable {C : Contract}

/-- The state a deployment starts in: the
empty storage, no memory, a ledger holding the deployer's payment, and the
value sent as the contract's funds. -/
def State.deploy (C : Contract) (tx : TTx) : State C [] :=
  { storage := Storage.init C, H := [], heap := Heap.empty, env := (),
    net := [(tx.msgSender, tx.msgValue.1)], selfBalance := tx.msgValue, tx := tx }

/-- **The typed deployment** (master's `Contract.deploy`, over the typed run): a
constructor that is not `payable`, the implicit one too, refuses value, as
solc's creation code does; otherwise its program runs from
`State.deploy`. -/
def Contract.deployT (C : Contract) {Γ' : Ctx} (P : Prog C [] Γ') (tx : TTx) :
    TRes (State C Γ') :=
  if !((C.ctor.map (·.payable)).getD false) && tx.msgValue.1 != 0 then .error .revert
  else do
    let o ← Prog.run (State.deploy C tx) P
    pure o.st

end Solidity
