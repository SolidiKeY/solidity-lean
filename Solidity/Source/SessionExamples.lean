import Solidity.Source.Session
import Solidity.Source.ElaborateExamples


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

def counts (n : Nat) : Option (Nat × Nat) :=
  elabSpin.map fun el =>
    ((sessionFrom (progSpin el) envSpin (addr 0) n).events.length,
      (sessionFromEvents (progSpin el) envSpin (addr 0) n).events.length)

#guard (counts 30).map (·.1) == some 1
#guard ((counts 30).map fun c => decide (c.2 > 1)) == some true
#guard ((counts 30).bind fun c => (counts 60).map fun d => decide (c.2 < d.2)) == some true
#guard (elabSpin.map fun el => (sessionFromEvents (progSpin el) envSpin (addr 0) 60).final.isNone) == some true


def unitS : Syn .unit :=
  .unit (.cons (.contract false "S" .none .nil
      (.cons (.stateVar (.elem .string) (some .pub) none none false "s" .none) .nil)) .nil)

def elabS : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } unitS)

#guard elabS.isSome

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

example (el : Elaborated) (main : String)
    (q : Request) (n : Nat) (data : Bytes) (post : St el.res.env) :
    let P : SrcProg el.res.env := ⟨el.prog, .legacy, toyFixed, main⟩
    let G := P.glob envSpin
    runAt (fun f => deploy G f main (addr 0) SemanticsExamples.user (word 0) [])
      (St.init _) 40 = (.ok (.success data), post) →
    fateAfterDeploy el main q n =
      match txFate G q post n with
      | .done _ => 0
      | .halted (.stuck message) =>
        if message == "getter of this type is not modelled" then 1 else 2
      | .halted _ => 2
      | .pending => 3 := by
  dsimp only
  intro success
  simp only [fateAfterDeploy, success]

def reqOf (input : Bytes) : Request := ⟨SemanticsExamples.user, addr 0, word 0, word 0, input⟩

#guard (elabS.map fun el => (fateAfterDeploy el "S" (reqOf (selOf "s()")) 40,
  fateAfterDeploy el "S" (reqOf (selOf "s()")) 80)) == some (1, 1)
#guard (elabSpin.map fun el => (fateAfterDeploy el "C" (reqOf (selOf "spin(address)" ++ arg 9)) 40,
  fateAfterDeploy el "C" (reqOf (selOf "spin(address)" ++ arg 9)) 80)) == some (3, 3)


def calleeOnce : List Event → Move := fun evs =>
  if evs.any (fun e => match e with | .reentered _ => true | _ => false) then .answer (.success [])
  else .reenter ElaborateExamples.thisC SemanticsExamples.user (word 0) (selOf "x()") false

def callbackAt (el : Elaborated) (depth : Nat) : Option Outcome :=
  let G : Glob el.res.env := ⟨el.prog, .legacy, toyFixed, fun _ => word 0, fun _ _ => true, calleeOnce, word 0⟩
  let r := runAt (fun n => do
    let _ ← deploy G n "D" ElaborateExamples.thisC SemanticsExamples.user (word 0) []
    envLoop G n depth false) (St.init _) 40
  r.2.events.findSome? fun e => match e with | .reentered o => some o | _ => none

#guard (elabD.bind fun el => callbackAt el 1024) == some (.revert [])
#guard (elabD.bind fun el => callbackAt el 1023) == some (.success (ElaborateExamples.arg 3))
#guard (elabD.bind fun el => callbackAt el 3) == some (.success (ElaborateExamples.arg 3))

def unitP : Syn .unit :=
  .unit (.cons (.contract false "P" .none .nil
      (.cons (.function (.ident "p") .nil (some .pub) (some .payable) .nil false none .nil
        (.some (.block .nil))) .nil)) .nil)

def elabP : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } unitP)

#guard elabP.isSome

def calleePay : List Event → Move := fun evs =>
  if evs.any (fun e => match e with | .reentered _ => true | _ => false) then .answer (.success [])
  else .reenter ElaborateExamples.thisC SemanticsExamples.user (word 1) (selOf "p()") false

def payCallbackIn (el : Elaborated) (pstatic : Bool) : Option Outcome × Nat :=
  let G : Glob el.res.env := ⟨el.prog, .legacy, toyFixed, fun _ => word 0, fun _ _ => true, calleePay, word 0⟩
  let r := runAt (fun n => do
    let _ ← deploy G n "P" ElaborateExamples.thisC SemanticsExamples.user (word 0) []
    envLoop G n 3 pstatic) (St.init _) 40
  (r.2.events.findSome? (fun e => match e with | .reentered o => some o | _ => none),
    (r.2.ex.world.accounts ElaborateExamples.thisC).balance)

#guard (elabP.map fun el => payCallbackIn el true) == some (some (.revert []), 0)
#guard (elabP.map fun el => payCallbackIn el false) == some (some (.success []), 1)


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

def countsK (n : Nat) : Option Nat :=
  elabK.map fun el => (sessionFromEvents ⟨el.prog, .legacy, toyFixed, "K"⟩ envK (addr 0) n).events.length

#guard ((countsK 30).map fun c => decide (c > 0)) == some true
#guard ((countsK 30).bind fun c => (countsK 60).map fun d => decide (c < d)) == some true
#guard (elabK.map fun el => (sessionFromEvents ⟨el.prog, .legacy, toyFixed, "K"⟩ envK (addr 0) 60).final.isNone) ==
  some true

end Solidity.Source.SessionExamples
