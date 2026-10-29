import Solidity.Source.Session
import Solidity.Source.ElaborateExamples

/-!
# Controls of sessions with unfinished transactions (S05 item 2)

```solidity
contract C {
  function spin(address a) public { while (true) { I(a).ping(); } }
}
interface I { function ping() external; }
```

`spin` never completes: each iteration calls the environment, which
answers.  `sessionFrom` ends the prefix at the transaction with none of its
events (only the deployment); `sessionFromEvents` shows the calls and
answers the run made within the horizon, and more at a larger horizon.
Checked by `#guard` (compiled code).
-/

namespace Solidity.Source.SessionExamples

open Solidity.Source Solidity.Source.Examples Solidity.Source.SemanticsExamples
  Solidity.Source.ElaborateExamples
open Solidity.Roadmap (Address Word Bytes Event Outcome SessionEnv)

def pingCall : Syn .expr :=
  .call (.member (.call (.ident "I") (.positional (.cons (.ident "a") .nil))) "ping") (.positional .nil)

def unitSpin : Syn .unit :=
  .unit (.cons (.contract false "C" .none .nil
      (.cons (.function (.ident "spin") pAddr (some .pub) none .nil false none .nil (.some (.block
        (.cons (.stmtItem (.whileStmt (.lit (.bool true))
          (.blockStmt (.block (.cons (.stmtItem (.simpleStmt (.exprStmt pingCall))) .nil))))) .nil)))) .nil))
    (.cons (.interface "I" .nil (.cons (.function (.ident "ping") .nil (some .external) none .nil false none .nil .none)
      .nil)) .nil))

def elabSpin : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } unitSpin)

#guard elabSpin.isSome

def ext : Address := addr 9

/-- One request: `spin(ext)`; the environment answers every call. -/
def envSpin : SessionEnv where
  deployer := SemanticsExamples.user
  deployNonce := ⟨0, by decide⟩
  deployValue := word 0
  deployArgs := []
  balance := fun _ => word 0
  hasCode := fun _ _ => true
  requests := fun _ i => if i = 0 then some (.request ⟨SemanticsExamples.user, addr 0, word 0, word 0,
    selOf "spin(address)" ++ arg 9⟩) else none
  callee := fun _ => .answer (.success [])

def progSpin (el : Elaborated) : SrcProg el.res.env := ⟨el.prog, .legacy, toyFixed, "C"⟩

/-- The number of events at horizon `n`, without and with the unfinished
transaction's events. -/
def counts (n : Nat) : Option (Nat × Nat) :=
  elabSpin.map fun el =>
    ((sessionFrom (progSpin el) envSpin (addr 0) n).events.length,
      (sessionFromEvents (progSpin el) envSpin (addr 0) n).events.length)

-- At horizon 30: `sessionFrom` shows only the deployment; `sessionFromEvents`
-- also shows the transaction's calls and answers so far.
#guard (counts 30).map (·.1) == some 1
#guard ((counts 30).map fun c => decide (c.2 > 1)) == some true
-- A larger horizon shows more of them (consistency, `sessionAtEvents_consistent`).
#guard ((counts 30).bind fun c => (counts 60).map fun d => decide (c.2 < d.2)) == some true
-- Neither session has a final observation: the transaction never completes.
#guard (elabSpin.map fun el => (sessionFromEvents (progSpin el) envSpin (addr 0) 60).final.isNone) == some true

end Solidity.Source.SessionExamples
