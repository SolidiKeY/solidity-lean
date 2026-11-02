import Solidity.Source.CalldataExamples

/-!
# Controls of inline arrays (lane FU2-B)

A unit written as syntax, elaborated by `elaborate`, deployed and called
through the semantics:

```solidity
contract I {
  uint256 public x;
  function f(uint256 i) external { x = [uint8(1), 2, 3][i]; }
  function g() external { x = [1, 256][1]; }
  function h(uint256 a) external { uint256[2] memory c = [a, 1]; x = c[0] + c[1]; }
}
```

As solc's: an inline array is a new `T[n] memory`, `T` the elements'
common type (`[uint8(1), 2, 3]` is `uint8[3]`, `[1, 256]` is `uint16[2]`:
`uint8` converts to `256`'s mobile type), an index past its length panics
with `0x32`. `[1, -1]` has no common type (`uint8` and `int8`) and is
refused, as by solc; `["a", "b"]` (`string memory[2]`) is refused here,
though solc accepts it: only one-word element types are modelled.
-/

namespace Solidity.Source.InlineExamples

open Solidity.Source Solidity.Source.Examples Solidity.Source.SemanticsExamples
open Solidity.Source.ElaborateExamples Solidity.Source.DecodeExamples Solidity.Source.CalldataExamples
open Solidity.Roadmap (Bytes Outcome)

def u256T : Syn .typeName := .elem u256E

def unitInl : Syn .unit :=
  .unit (.cons (.contract false "I" .none .nil
      (.cons (.stateVar u256 (some .pub) none none false "x" .none)
      (.cons (ext "f" (.cons (uParam "i") .nil)
          (.cons (setX (.index (.inlineArray (.call (ty u8) (.positional (.cons (num 1) .nil)))
            (.cons (num 2) (.cons (num 3) .nil))) (.some (.ident "i")))) .nil))
      (.cons (ext "g" .nil
          (.cons (setX (.index (.inlineArray (num 1) (.cons (num 256) .nil)) (.some (num 1)))) .nil))
      (.cons (ext "h" (.cons (uParam "a") .nil)
          (.cons (.stmtItem (.simpleStmt (.declVar (.varDecl (.array u256T (.some (num 2))) (some .memory) "c")
            (.some (.inlineArray (.ident "a") (.cons (num 1) .nil))))))
          (.cons (setX (.addSub .add (.index (.ident "c") (.some (num 0))) (.index (.ident "c") (.some (num 1)))))
            .nil)))
      .nil))))
    .nil)

def elabInl : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } unitInl)

#guard elabInl.isSome

-- **`[uint8(1), 2, 3][i]`**: `i = 1` reads 2; `i = 3` panics `0x32`.
#guard (elabInl.map fun el => runD el 0 [callW "f(uint256)" [1], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 2))]
#guard (elabInl.map fun el => runD el 0 [callW "f(uint256)" [3]]) ==
  some [some (.success []), some (.revert (panicData .index))]

-- **The common type**: `[1, 256]` is `uint16[2]`; its second element is 256.
#guard (elabInl.map fun el => runD el 0 [callW "g()" [], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 256))]

-- **Into a declared `uint256[2] memory`**: `[a, 1]` with `a = 41` sums to 42.
#guard (elabInl.map fun el => runD el 0 [callW "h(uint256)" [41], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 42))]

/-- A one-function unit evaluating `e` as a statement (no conversion of
its value, so a refusal is the inline array's own). -/
def unitOf (e : Syn .expr) : Syn .unit :=
  .unit (.cons (.contract false "J" .none .nil
      (.cons (ext "f" .nil (.cons (stmt e) .nil)) .nil))
    .nil)

-- **Refusals**: `[1, -1]` has no common type (solc refuses it too);
-- `["a", "b"]` has reference elements (not modelled; solc accepts it).
#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitOf (.inlineArray (num 1) (.cons (.unaryPrefix .neg (num 1)) .nil))))).isNone
#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitOf (.inlineArray (.lit (.str [97])) (.cons (.lit (.str [98])) .nil))))).isNone
-- The control unit itself elaborates with a value element.
#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitOf (.inlineArray (num 1) (.cons (num 2) .nil))))).isSome

end Solidity.Source.InlineExamples
