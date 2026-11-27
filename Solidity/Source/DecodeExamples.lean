import Solidity.Source.ElaborateExamples
import Solidity.Source.Decode


namespace Solidity.Source.DecodeExamples

open Solidity.Source Solidity.Source.Examples Solidity.Source.SemanticsExamples
open Solidity.Source.ElaborateExamples
open Solidity.Roadmap (Bytes Outcome)

def u8 : Elem := .int false 8 (by decide)
def u256E : Elem := .int false 256 (by decide)

def bParam : Syn (.list .param) := .cons (.param (.elem .bytes) (some .memory) (some "b")) .nil
def ty (el : Elem) (h : el ≠ .addressPayable := by decide) : Syn .expr := .elemType el h
def one (t : Syn .expr) : Syn .expr := .tuple (.some t) .nil
def decodeOf (ts : Syn .expr) : Syn .expr :=
  .call (.member (.ident "abi") "decode") (.positional (.cons (.ident "b") (.cons ts .nil)))
def setX (e : Syn .expr) : Syn (.item .body) := stmt (.assign .assign (.ident "x") e)
def fn (name : String) (body : Syn (.list (.item .body))) : Syn (.part false) :=
  .function (.ident name) bParam (some .pub) none .nil false none .nil (.some (.block body))

def unitDec : Syn .unit :=
  .unit (.cons (.contract false "D" .none .nil
      (.cons (.enum (t := false) "K" "A" ["B"])
      (.cons (.stateVar u256 (some .pub) none none false "x" .none)
      (.cons (fn "f" (.cons (setX (decodeOf (one (ty u8)))) .nil))
      (.cons (fn "g" (.cons (setX (.call (ty u256E) (.positional (.cons (decodeOf (one (.ident "K"))) .nil)))) .nil))
      (.cons (fn "h" (.cons (setX (.member (decodeOf (one (.index (ty u256E) .none))) "length")) .nil))
      (.cons (fn "k" (.cons (setX (.member (decodeOf (one (ty .bytes))) "length")) .nil))
      (.cons (fn "p" (.cons (stmt (decodeOf (.tuple (.some (ty u8)) (.cons (.some (ty .bool)) .nil))))
          (.cons (setX (num 9)) .nil)))
      (.cons (.stateVar (.elem .bytes) none none none false "sb" .none)
      (.cons (.function (.ident "s") .nil (some .pub) none .nil false none .nil (.some (.block
          (.cons (stmt (.assign .assign (.ident "sb") (.lit (.hexStr (List.replicate 31 0 ++ [5])))))
          (.cons (setX (.call (.member (.ident "abi") "decode") (.positional (.cons (.ident "sb")
            (.cons (one (ty u8)) .nil))))) .nil)))))
      (.cons (fn "w" (.cons (.stmtItem (.simpleStmt (.declTuple 0 (.varDecl (.elem u8) none "a")
            (.cons .none .nil) (decodeOf (.tuple (.some (ty u8)) (.cons (.some (ty .bool)) .nil))))))
          (.cons (setX (.ident "a")) .nil)))
      (.cons (fn "v" (.cons (.stmtItem (.simpleStmt (.declTuple 2 (.varDecl (.elem u8) none "z") .nil
            (decodeOf (.tuple (.some (ty .bool)) (.cons (.some (ty .bool)) (.cons (.some (ty u8)) .nil)))))))
          (.cons (setX (.ident "z")) .nil)))
      .nil))))))))))))
    .nil)

def elabDec : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } unitDec)

#guard elabDec.isSome

def argN (k : Nat) : Bytes := Solidity.Source.wordBytes ⟨k % 2 ^ 256, Nat.mod_lt _ (by decide)⟩

def callB (sig : String) (bs : Bytes) : Bytes :=
  selOf sig ++ argN 32 ++ argN bs.length ++ bs ++ List.replicate ((32 - bs.length % 32) % 32) 0

def words (ws : List Nat) : Bytes := (ws.map argN).flatten

#guard (elabDec.map fun el => runD el 0 [callB "f(bytes)" (words [7]), selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 7))]
#guard (elabDec.map fun el => runD el 0 [callB "f(bytes)" (words [300]), selOf "x()"]) ==
  some [some (.success []), some (.revert []), some (.success (arg 0))]
#guard (elabDec.map fun el => runD el 0 [callB "f(bytes)" (List.replicate 31 0), selOf "x()"]) ==
  some [some (.success []), some (.revert []), some (.success (arg 0))]

#guard (elabDec.map fun el => runD el 0 [callB "g(bytes)" (words [1]), selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 1))]
#guard (elabDec.map fun el => runD el 0 [callB "g(bytes)" (words [2]), selOf "x()"]) ==
  some [some (.success []), some (.revert []), some (.success (arg 0))]

#guard (elabDec.map fun el => runD el 0 [callB "h(bytes)" (words [32, 2, 5, 6]), selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 2))]
#guard (elabDec.map fun el => runD el 0 [callB "h(bytes)" (words [32, 2 ^ 64])]) ==
  some [some (.success []), some (.revert (panicData .alloc))]
#guard (elabDec.map fun el => runD el 0 [callB "h(bytes)" (words [32, 3, 5, 6]),
    callB "h(bytes)" (words [64])]) ==
  some [some (.success []), some (.revert []), some (.revert [])]

#guard (elabDec.map fun el => runD el 0 [callB "k(bytes)" (words [32, 2] ++ ([97, 98] ++ List.replicate 30 0)),
    selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 2))]

#guard (elabDec.map fun el => runD el 0 [callB "p(bytes)" (words [1, 1]), selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 9))]
#guard (elabDec.map fun el => runD el 0 [callB "p(bytes)" (words [1, 2]), selOf "x()"]) ==
  some [some (.success []), some (.revert []), some (.success (arg 0))]

def runDF (el : Elaborated) (fuel : Nat) (inputs : List Bytes) : List (Option Outcome) :=
  let G : Glob el.res.env := ⟨el.prog, .legacy, toyFixed, fun _ => word 0, fun _ _ => true,
    fun _ => .answer (.success []), word 0⟩
  let go : Nat → EM el.res.env [] (List Outcome) := fun n => do
    let d ← deploy G n "D" ElaborateExamples.thisC ElaborateExamples.user (word 0) []
    let mut outs := [d]
    for i in inputs do
      outs := outs ++ [← runTx G n ⟨ElaborateExamples.user, ElaborateExamples.thisC, word 0, word 0, i⟩]
    pure outs
  match (runAt go (s0 : St el.res.env) fuel).1 with
  | .ok os => os.map some
  | _ => []

#guard (elabDec.map fun el => runD el 0 [selOf "s()"]) == some []
#guard (elabDec.map fun el => runDF el 200 [selOf "s()", selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 5))]

example : TypingExamples.Γ.decodeTys (one (ty .address)) = some [.address true] := rfl
example : TypingExamples.Γ.decodeTys (one (.index (ty .address) .none)) =
    some [.array .memory (.address false) none] := rfl

#guard (elabDec.map fun el => runD el 0 [callB "w(bytes)" (words [7, 1]), selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 7))]
#guard (elabDec.map fun el => runD el 0 [callB "w(bytes)" (words [7, 2]), selOf "x()"]) ==
  some [some (.success []), some (.revert []), some (.success (arg 0))]
#guard (elabDec.map fun el => runD el 0 [callB "v(bytes)" (words [1, 0, 9]), selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 9))]


def unitRefused (ts : Syn .expr) : Syn .unit :=
  .unit (.cons (.contract false "D" .none .nil
      (.cons (.struct (t := false) "S" (.structMember u256 "a") .nil)
      (.cons (fn "f" (.cons (stmt (decodeOf ts)) .nil))
      .nil)))
    .nil)

#guard (elaborate (resolveUnit { pipeline := .legacy } (unitRefused (one (.ident "S"))))).isNone
#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitRefused (one (.index (ty u256E) (.some (num 2))))))).isNone
#guard (elaborate (resolveUnit { pipeline := .legacy } (unitRefused (one (ty (.fixed false none)))))).isNone
#guard (elaborate (resolveUnit { pipeline := .legacy } (unitRefused (one (ty u256E))))).isSome

end Solidity.Source.DecodeExamples

