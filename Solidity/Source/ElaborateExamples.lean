import Solidity.Source.Elaborate
import Solidity.Source.SemanticsExamples

/-!
# Controls of the elaborator (S02 item 1b)

Units written as syntax, elaborated by `elaborate` (no hand-written
resolved terms), deployed and called through the semantics
(`Solidity/Source/Semantics.lean`).  The runs are checked by `#guard`, which
evaluates compiled code; the elaborator's output is a derivation, so each
run is of the program the typing rules give the unit.

```solidity
contract A {
  uint256 a;
  constructor(uint256 v) { a = v; }
}
contract C is A(7) {
  uint256 x = 3;
  modifier pos(uint256 k) { require(k > 0); _; }
  function g(uint256 k) public pos(k) returns (uint256) { x = x + k; return x + a; }
}
```
-/

namespace Solidity.Source.ElaborateExamples

open Solidity.Source Solidity.Source.Examples Solidity.Source.SemanticsExamples
open Solidity.Roadmap (Address Word Bytes Event Outcome Move Request SessionEnv Pipeline)

def num (k : Nat) : Syn .expr := .lit (.num (.dec k 0 0))
def stmt (e : Syn .expr) : Syn (.item .body) := .stmtItem (.simpleStmt (.exprStmt e))
def pK : Syn (.list .param) := .cons (.param u256 none (some "k")) .nil
def pV : Syn (.list .param) := .cons (.param u256 none (some "v")) .nil
def pRet : Syn (.list .param) := .cons (.param u256 none none) .nil

def ctorA : Syn (.part false) :=
  .constructor pV .nil false none (.block (.cons (stmt (.assign .assign (.ident "a") (.ident "v"))) .nil))

def modPos : Syn (.part false) :=
  .modifier "pos" (.some pK) false none (.some (.block
    (.cons (stmt (.call (.ident "require") (.positional (.cons (.order .gt (.ident "k") (num 0)) .nil))))
    (.cons (stmt (.ident "_")) .nil))))

def fnG : Syn (.part false) :=
  .function (.ident "g") pK (some .pub) none (.cons (.modInv ⟨"pos", []⟩ (.some (.positional (.cons (.ident "k") .nil)))) .nil)
    false none pRet (.some (.block
      (.cons (stmt (.assign .assign (.ident "x") (.addSub .add (.ident "x") (.ident "k"))))
      (.cons (.stmtItem (.returnStmt (.some (.addSub .add (.ident "x") (.ident "a"))))) .nil))))

def unitAC : Syn .unit :=
  .unit (.cons (.contract false "A" .none .nil
      (.cons (.stateVar u256 none none none false "a" .none) (.cons ctorA .nil)))
    (.cons (.contract false "C" .none (.cons (.inherit ⟨"A", []⟩ (.some (.positional (.cons (num 7) .nil)))) .nil)
      (.cons (.stateVar u256 none none none false "x" (.some (num 3))) (.cons modPos (.cons fnG .nil))))
    .nil))

def resAC : Resolution := resolveUnit { pipeline := .legacy } unitAC

def elabAC : Option Elaborated := elaborate resAC

-- The unit elaborates: every body, initializer and base argument has a
-- derivation.
#guard elabAC.isSome

-- The program's parts, read back: `C` has one initializer (`x = 3`) and
-- gives `A` one argument; `A`'s constructor has one local; `g`'s body
-- carries one modifier invocation, `pos`.
#guard (elabAC.map fun el => ((el.prog.inits "C").length, (el.prog.baseArgs "C").length,
  (el.prog.ctorLocals "A").length)) == some (1, 1, 1)
#guard (elabAC.bind fun el => (el.res.env.decls.find? (·.name == "g")).bind fun d =>
  (el.prog.body d).map fun b => b.mods.map (·.modifier.name)) == some ["pos"]

def thisC : Address := addr 1
def user : Address := addr 7

/-- Deploy `C` at `thisC`, then call `g(k)`: the outcome and `x`. -/
def deployCall (el : Elaborated) (k : Nat) (h : k < 2 ^ 256 := by decide) : Option Outcome :=
  let G : Glob el.res.env := ⟨el.prog, .legacy, toyFixed, fun _ => word 0, fun _ _ => true,
    fun _ => .answer (.success []), word 0⟩
  let r := runAt (fun n => do
    let d ← deploy G n "C" thisC user (word 0) []
    match d with
    | .success _ => runTx G n ⟨user, thisC, word 0, word 0, selOf "g(uint256)" ++ wordBytes ⟨k, h⟩⟩
    | o => pure o) (s0 : St el.res.env) 40
  match r.1 with
  | .ok o => some o
  | _ => none

-- **`g(2)` returns `x + a = (3 + 2) + 7`**: the initializer and the base
-- argument through `A`'s constructor ran (without either, `9` or `5`).
#guard (elabAC.bind fun el => deployCall el 2) == some (.success (wordBytes (toWord 12)))

-- `g(0)` reverts in the modifier's `require` (without the modifier, `7`).
#guard (elabAC.bind fun el => deployCall el 0) == some (.revert [])

/-- A unit with an ill-typed body does not elaborate: `x = true` with
`uint256 x`. -/
def unitBad : Syn .unit :=
  .unit (.cons (.contract false "C" .none .nil
      (.cons (.stateVar u256 none none none false "x" .none)
        (.cons (.function (.ident "f") .nil (some .pub) none .nil false none .nil (.some (.block
          (.cons (stmt (.assign .assign (.ident "x") (.lit (.bool true)))) .nil)))) .nil)))
    .nil)

#guard (elaborate (resolveUnit { pipeline := .legacy } unitBad)).isNone

/-! ## Public getters, `emit` in a static frame, value to a constructor

```solidity
contract D {
  uint256 public x = 3;
  mapping(uint256 => uint256) public m;
  event E(uint256);
  function set(uint256 k) public { m[k] = x + k; }
  function e() public { emit E(1); }
}
```
-/

def mapUU : Syn .typeName :=
  .mapping (.elem (.int false 256 (by decide)) (by decide)) none u256 none

def unitD : Syn .unit :=
  .unit (.cons (.contract false "D" .none .nil
      (.cons (.stateVar u256 (some .pub) none none false "x" (.some (num 3)))
      (.cons (.stateVar mapUU (some .pub) none none false "m" .none)
      (.cons (.event "E" (.cons (.eventParam u256 false none) .nil) false)
      (.cons (.function (.ident "set") pK (some .pub) none .nil false none .nil (.some (.block
          (.cons (stmt (.assign .assign (.index (.ident "m") (.some (.ident "k")))
            (.addSub .add (.ident "x") (.ident "k")))) .nil))))
      (.cons (.function (.ident "e") .nil (some .pub) none .nil false none .nil (.some (.block
          (.cons (.stmtItem (.emit (.ident "E") (.positional (.cons (num 1) .nil)))) .nil))))
      .nil))))))
    .nil)

def elabD : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } unitD)

#guard elabD.isSome

def arg (k : Nat) (h : k < 2 ^ 256 := by decide) : Bytes := wordBytes ⟨k, h⟩

/-- Deploy `D` with `value`, then run each call data as a transaction: the
deployment's outcome and each transaction's. -/
def runD (el : Elaborated) (value : Nat) (inputs : List Bytes) (h : value < 2 ^ 256 := by decide) :
    List (Option Outcome) :=
  let G : Glob el.res.env := ⟨el.prog, .legacy, toyFixed, fun _ => word 0, fun _ _ => true,
    fun _ => .answer (.success []), word 0⟩
  let go : Nat → EM el.res.env [] (List Outcome) := fun n => do
    let d ← deploy G n "D" thisC user ⟨value, h⟩ []
    let mut outs := [d]
    for i in inputs do
      outs := outs ++ [← runTx G n ⟨user, thisC, word 0, word 0, i⟩]
    pure outs
  match (runAt go (s0 : St el.res.env) 40).1 with
  | .ok os => os.map some
  | _ => []

-- **Getters**: after `set(2)`, `x()` is `3`, `m(2)` is `3 + 2`, `m(3)` is `0`.
#guard (elabD.map fun el => runD el 0 [selOf "set(uint256)" ++ arg 2, selOf "x()",
    selOf "m(uint256)" ++ arg 2, selOf "m(uint256)" ++ arg 3]) ==
  some [some (.success []), some (.success []), some (.success (arg 3)), some (.success (arg 5)),
    some (.success (arg 0))]

-- **Value to a non-payable constructor** (here the default one) reverts the
-- deployment; no value deploys.
#guard (elabD.map fun el => (runD el 1 []).head?) == some (some (some (.revert [])))
#guard (elabD.map fun el => (runD el 0 []).head?) == some (some (some (.success [])))

/-- `contract D { type W is uint8; uint256 public x; function f(W w) public { x = 1; } }` -/
def unitW : Syn .unit :=
  .unit (.cons (.contract false "D" .none .nil
      (.cons (.udvt (t := false) "W" (.int false 8 (by decide)))
      (.cons (.stateVar u256 (some .pub) none none false "x" .none)
      (.cons (.function (.ident "f") (.cons (.param (.userType ⟨"W", []⟩) none (some "w")) .nil)
          (some .pub) none .nil false none .nil (.some (.block
          (.cons (stmt (.assign .assign (.ident "x") (num 1))) .nil))))
      .nil))))
    .nil)

def elabW : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } unitW)

#guard elabW.isSome

-- **A user-defined value type argument** (lane V04b, a run-time gap
-- closed) is decoded as its underlying type: `f(7)` runs (`x` becomes 1),
-- `f(300)` is not a `uint8` and reverts with no data.
#guard (elabW.map fun el => runD el 0 [selOf "f(uint8)" ++ arg 7, selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 1))]
#guard (elabW.map fun el => runD el 0 [selOf "f(uint8)" ++ arg 300, selOf "x()"]) ==
  some [some (.success []), some (.revert []), some (.success (arg 0))]

/-- `e()` entered in a static frame or not, after deploying `D`. -/
def emitIn (el : Elaborated) (static : Bool) : Option Outcome :=
  let G : Glob el.res.env := ⟨el.prog, .legacy, toyFixed, fun _ => word 0, fun _ _ => true,
    fun _ => .answer (.success []), word 0⟩
  match (runAt (fun n => do
    let _ ← deploy G n "D" thisC user (word 0) []
    let m ← mark
    enterInstance G n thisC user (word 0) (selOf "e()") static "D" 1 m) (s0 : St el.res.env) 40).1 with
  | .ok o => some o
  | _ => none

-- **`emit` in a static frame reverts** (as `LOG` does); outside one it succeeds.
#guard (elabD.bind fun el => emitIn el true) == some (.revert [])
#guard (elabD.bind fun el => emitIn el false) == some (.success [])

/-! ## Dynamic arguments

```solidity
contract L {
  function len(bytes memory b) public returns (uint256) { return b.length; }
  function sum2(uint256[] memory xs) public returns (uint256) { return xs[0] + xs[1]; }
}
```
-/

def unitL : Syn .unit :=
  .unit (.cons (.contract false "L" .none .nil
      (.cons (.function (.ident "len") (.cons (.param (.elem .bytes) (some .memory) (some "b")) .nil)
          (some .pub) none .nil false none pRet (.some (.block
          (.cons (.stmtItem (.returnStmt (.some (.member (.ident "b") "length")))) .nil))))
      (.cons (.function (.ident "sum2") (.cons (.param (.array u256 .none) (some .memory) (some "xs")) .nil)
          (some .pub) none .nil false none pRet (.some (.block
          (.cons (.stmtItem (.returnStmt (.some (.addSub .add (.index (.ident "xs") (.some (num 0)))
            (.index (.ident "xs") (.some (num 1))))))) .nil))))
      .nil)))
    .nil)

def elabL : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } unitL)

#guard elabL.isSome

/-- Deploy `L`, then run one call: its outcome. -/
def callL (el : Elaborated) (input : Bytes) : Option Outcome :=
  let G : Glob el.res.env := ⟨el.prog, .legacy, toyFixed, fun _ => word 0, fun _ _ => true,
    fun _ => .answer (.success []), word 0⟩
  match (runAt (fun n => do
    let _ ← deploy G n "L" thisC user (word 0) []
    runTx G n ⟨user, thisC, word 0, word 0, input⟩) (s0 : St el.res.env) 40).1 with
  | .ok o => some o
  | _ => none

-- **`bytes` decoded from its tail**: `len(0x010203)` is `3`.
#guard (elabL.bind fun el => callL el (selOf "len(bytes)" ++ arg 32 ++ arg 3 ++ pad32 [1, 2, 3])) ==
  some (.success (arg 3))

-- **A dynamic array**: `sum2([5, 7])` is `12`.
#guard (elabL.bind fun el => callL el (selOf "sum2(uint256[])" ++ arg 32 ++ arg 2 ++ arg 5 ++ arg 7)) ==
  some (.success (arg 12))

-- An offset past the data reverts, as solc's decoder does.
#guard (elabL.bind fun el => callL el (selOf "len(bytes)" ++ arg 4096 ++ arg 3)) == some (.revert [])

end Solidity.Source.ElaborateExamples
