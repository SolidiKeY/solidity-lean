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
open Solidity.Roadmap (Address Word Bytes Event Outcome SessionEnv Request Move)

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
-- The session has no final observation: the transaction never completes.
#guard (elabSpin.map fun el => (sessionFromEvents (progSpin el) envSpin (addr 0) 60).final.isNone) == some true

/-! ## Stuck is not divergence

```solidity
contract S { string public s; }
```

The getter of a `string` is not modelled, so `s()` is stuck: halted at
horizon 40 and at 80 (as `stuck_stable` says it must stay), while `spin`
is pending at both.  Two sampled horizons do not show that `spin`
diverges; they show the two fates apart.
-/

def unitS : Syn .unit :=
  .unit (.cons (.contract false "S" .none .nil
      (.cons (.stateVar (.elem .string) (some .pub) none none false "s" .none) .nil)) .nil)

def elabS : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } unitS)

#guard elabS.isSome

/-- The fate of one transaction after deploying `main` at `addr 0`, within
horizon `n`, as a tag: `0` done, `1` stuck at the unmodelled getter, `2`
another halt, `3` pending.  The deployment must succeed. -/
def fateAfterDeploy (el : Elaborated) (main : String) (q : Request) (n : Nat) : Nat :=
  let P : SrcProg el.res.env := ⟨el.prog, .legacy, toyFixed, main⟩
  let G := P.glob envSpin
  let d := runAt (fun f => deploy G f main (addr 0) SemanticsExamples.user (word 0) []) (St.init _) 40
  match d.1 with
  | .ok (.success _) =>
    match txFate G q d.2 n with
    | .done _ => 0
    | .halted (.stuck m) => if m == "getter of this type is not modelled" then 1 else 2
    | .halted _ => 2
    | .pending => 3
  | _ => 4

def reqOf (input : Bytes) : Request := ⟨SemanticsExamples.user, addr 0, word 0, word 0, input⟩

-- `s()` is stuck, at horizon 40 and at 80.
#guard (elabS.map fun el => (fateAfterDeploy el "S" (reqOf (selOf "s()")) 40,
  fateAfterDeploy el "S" (reqOf (selOf "s()")) 80)) == some (1, 1)
-- `spin(ext)` is pending at both.
#guard (elabSpin.map fun el => (fateAfterDeploy el "C" (reqOf (selOf "spin(address)" ++ arg 9)) 40,
  fateAfterDeploy el "C" (reqOf (selOf "spin(address)" ++ arg 9)) 80)) == some (3, 3)

/-! ## Callbacks at the depth limit

The environment frame at depth 1024 cannot call back: its callback fails
as a call from there does (`callAddr`), so `x()` is not entered.  At depth
3 the callback runs the getter.
-/

/-- The environment calls back `x()` on `D` once, then answers. -/
def calleeOnce : List Event → Move := fun evs =>
  if evs.any (fun e => match e with | .reentered _ => true | _ => false) then .answer (.success [])
  else .reenter ElaborateExamples.thisC SemanticsExamples.user (word 0) (selOf "x()") false

/-- The callback's outcome after deploying `D` at `thisC`, with the
environment frame at `depth`. -/
def callbackAt (el : Elaborated) (depth : Nat) : Option Outcome :=
  let G : Glob el.res.env := ⟨el.prog, .legacy, toyFixed, fun _ => word 0, fun _ _ => true, calleeOnce, word 0⟩
  let r := runAt (fun n => do
    let _ ← deploy G n "D" ElaborateExamples.thisC SemanticsExamples.user (word 0) []
    envLoop G n depth false) (St.init _) 40
  r.2.events.findSome? fun e => match e with | .reentered o => some o | _ => none

#guard (elabD.bind fun el => callbackAt el 1024) == some (.revert [])
#guard (elabD.bind fun el => callbackAt el 3) == some (.success (ElaborateExamples.arg 3))

/-! ## An unfinished deployment

```solidity
contract K { constructor(address a) { while (true) { I(a).ping(); } } }
```

The deployment never completes: `sessionFromEvents` shows its calls and
answers (`deploy_events_mono`), more at a larger horizon, and no final
observation.
-/

def unitK : Syn .unit :=
  .unit (.cons (.contract false "K" .none .nil
      (.cons (.constructor pAddr .nil false none (.block
        (.cons (.stmtItem (.whileStmt (.lit (.bool true))
          (.blockStmt (.block (.cons (.stmtItem (.simpleStmt (.exprStmt pingCall))) .nil))))) .nil))) .nil))
    (.cons (.interface "I" .nil (.cons (.function (.ident "ping") .nil (some .external) none .nil false none .nil .none)
      .nil)) .nil))

def elabK : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } unitK)

#guard elabK.isSome

def envK : SessionEnv := { envSpin with deployArgs := ElaborateExamples.arg 9, requests := fun _ _ => none }

/-- The number of events of the session at horizon `n`. -/
def countsK (n : Nat) : Option Nat :=
  elabK.map fun el => (sessionFromEvents ⟨el.prog, .legacy, toyFixed, "K"⟩ envK (addr 0) n).events.length

#guard ((countsK 30).map fun c => decide (c > 0)) == some true
#guard ((countsK 30).bind fun c => (countsK 60).map fun d => decide (c < d)) == some true
#guard (elabK.map fun el => (sessionFromEvents ⟨el.prog, .legacy, toyFixed, "K"⟩ envK (addr 0) 60).final.isNone) ==
  some true

end Solidity.Source.SessionExamples
