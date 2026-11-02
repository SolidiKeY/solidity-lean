import Solidity.Source.InlineExamples

/-!
# Controls of `try`/`catch` (lane FU2-B)

Two contracts written as syntax, elaborated by `elaborate`, deployed and
called through the semantics:

```solidity
contract T {
  function g(uint256 k) external returns (uint256) { require(k < 10); return k + 1; }
}
contract D {
  uint256 public x;
  function f(T t, uint256 k) external {
    try t.g(k) returns (uint256 v) { x = v; } catch { x = 99; }
  }
  function h(T t, uint256 k) external {
    try t.g(k) returns (uint256) { x = 1; } catch (bytes memory r) { x = r.length + 1000; }
  }
}
```

As solc's: a call that returns runs the success block with its returns
bound; a call that reverts runs the `catch` clause (the revert data bound
as `bytes memory`); a call to an address without code reverts the caller,
not caught.
-/

namespace Solidity.Source.TryExamples

open Solidity.Source Solidity.Source.Examples Solidity.Source.SemanticsExamples
open Solidity.Source.ElaborateExamples Solidity.Source.DecodeExamples Solidity.Source.CalldataExamples
open Solidity.Roadmap (Bytes Outcome)

/-- An external function with returns. -/
def extR (name : String) (ps rs : Syn (.list .param)) (body : Syn (.list (.item .body))) : Syn (.part false) :=
  .function (.ident name) ps (some .external) none .nil false none rs (.some (.block body))

def tParam : Syn .param := .param (.userType ⟨"T", []⟩) none (some "t")
def u256R : Syn (.list .param) := .cons (.param u256 none none) .nil

/-- `try t.g(k) returns (rets) { ok } catch … { … }`. -/
def tryG (rets : Syn (.list .param)) (ok : Syn (.list (.item .body))) (cl : Syn (.catchClause .body)) :
    Syn (.item .body) :=
  .stmtItem (.tryStmt (.call (.member (.ident "t") "g") (.positional (.cons (.ident "k") .nil))) rets
    (.block ok) cl .nil)

def unitTry : Syn .unit :=
  .unit (.cons (.contract false "T" .none .nil
      (.cons (extR "g" (.cons (uParam "k") .nil) u256R
          (.cons (stmt (.call (.ident "require") (.positional (.cons (.order .lt (.ident "k") (num 10)) .nil))))
          (.cons (.stmtItem (.returnStmt (.some (.addSub .add (.ident "k") (num 1))))) .nil)))
      .nil))
    (.cons (.contract false "D" .none .nil
      (.cons (.stateVar u256 (some .pub) none none false "x" .none)
      (.cons (ext "f" (.cons tParam (.cons (uParam "k") .nil))
          (.cons (tryG (.cons (.param u256 none (some "v")) .nil) (.cons (setX (.ident "v")) .nil)
            (.catchPlain (.block (.cons (setX (num 99)) .nil)))) .nil))
      (.cons (ext "h" (.cons tParam (.cons (uParam "k") .nil))
          (.cons (tryG u256R (.cons (setX (num 1)) .nil)
            (.catchSig none (.param (.elem .bytes) (some .memory) (some "r")) .nil
              (.block (.cons (setX (.addSub .add (.member (.ident "r") "length") (num 1000))) .nil)))) .nil))
      .nil))))
    .nil))

def elabTry : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } unitTry)

#guard elabTry.isSome

/-- `T`'s address. -/
def tAddr : Solidity.Roadmap.Address := addr 2

/-- Deploy `T` at `tAddr` and `D` at `thisC`, then run each call data on `D`. -/
def runTry (el : Elaborated) (inputs : List Bytes) : List (Option Outcome) :=
  let G : Glob el.res.env := ⟨el.prog, .legacy, toyFixed, fun _ => word 0, fun _ _ => true,
    fun _ => .answer (.success []), word 0⟩
  let go : Nat → EM el.res.env [] (List Outcome) := fun n => do
    let t ← deploy G n "T" tAddr ElaborateExamples.user (word 0) []
    let d ← deploy G n "D" ElaborateExamples.thisC ElaborateExamples.user (word 0) []
    let mut outs := [t, d]
    for i in inputs do
      outs := outs ++ [← runTx G n ⟨ElaborateExamples.user, ElaborateExamples.thisC, word 0, word 0, i⟩]
    pure outs
  match (runAt go (s0 : St el.res.env) 60).1 with
  | .ok os => os.map some
  | _ => []

-- **Success**: `g(4)` returns 5, bound to `v`.
#guard (elabTry.map fun el => runTry el [callW "f(address,uint256)" [2, 4], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success []), some (.success (arg 5))]
-- **Caught revert**: `g(12)` reverts; the plain clause sets 99.
#guard (elabTry.map fun el => runTry el [callW "f(address,uint256)" [2, 12], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success []), some (.success (arg 99))]
-- **The revert data bound**: `require` reverts with no data, `r.length` is 0.
#guard (elabTry.map fun el => runTry el [callW "h(address,uint256)" [2, 12], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success []), some (.success (arg 1000))]
-- **No code at the target**: not caught, the caller reverts.
#guard (elabTry.map fun el => runTry el [callW "f(address,uint256)" [9, 4]]) ==
  some [some (.success []), some (.success []), some (.revert [])]

end Solidity.Source.TryExamples
