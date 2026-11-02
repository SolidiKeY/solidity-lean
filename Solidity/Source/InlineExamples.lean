import Solidity.Source.CalldataExamples

/-!
# Controls of inline arrays and `new` of memory arrays (lane FU2-B)

A unit written as syntax, elaborated by `elaborate`, deployed and called
through the semantics:

```solidity
contract D {
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
  .unit (.cons (.contract false "D" .none .nil
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
      .nil)))))
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

/-- A one-function unit `f()` with body `body`. -/
def unitBody (body : Syn (.list (.item .body))) : Syn .unit :=
  .unit (.cons (.contract false "D" .none .nil
      (.cons (.stateVar u256 (some .pub) none none false "x" .none)
      (.cons (ext "f" .nil body) .nil)))
    .nil)

-- **The element type is `uint16`, not `uint256`**: `[1, 256][1] * 256`
-- overflows `uint16` and panics `0x11`.
#guard (elaborate (resolveUnit { pipeline := .legacy } (unitBody (.cons (setX (.mulDivMod .mul
    (.index (.inlineArray (num 1) (.cons (num 256) .nil)) (.some (num 1))) (num 256))) .nil)))).map
    (fun el => runD el 0 [callW "f()" []]) ==
  some [some (.success []), some (.revert (panicData .arithmetic))]

-- **No conversion between static array types**: `uint256[2] memory c = [1, 2]`
-- is refused (`uint8[2]` does not convert to `uint256[2]`), as by solc.
#guard (elaborate (resolveUnit { pipeline := .legacy } (unitBody (.cons
    (.stmtItem (.simpleStmt (.declVar (.varDecl (.array u256T (.some (num 2))) (some .memory) "c")
      (.some (.inlineArray (num 1) (.cons (num 2) .nil)))))) .nil)))).isNone

/-! ### `new` of memory arrays

```solidity
contract D {
  uint256 public x;
  function f(uint256 k) external { uint8[] memory a = new uint8[](k); a[1] = 7; x = a[1]; }
  function g(uint256 k) external { x = new bytes(k).length; }
  function h(uint256 k) external { uint256[] memory a = new uint256[](k); x = a[k - 1] + 5; }
}
```

As solc's: `n` zeroed elements; a length of `2^64` or more panics `0x41`
(solc panics already from a lower bound, the free memory pointer passing
`2^64 - 1`; the model's band is the decoder's). -/

def newOf (t : Syn .typeName) (k : Syn .expr) : Syn .expr := .call (.new t) (.positional (.cons k .nil))

def unitNew : Syn .unit :=
  .unit (.cons (.contract false "D" .none .nil
      (.cons (.stateVar u256 (some .pub) none none false "x" .none)
      (.cons (ext "f" (.cons (uParam "k") .nil)
          (.cons (.stmtItem (.simpleStmt (.declVar (.varDecl (.array u8T .none) (some .memory) "a")
            (.some (newOf (.array u8T .none) (.ident "k"))))))
          (.cons (stmt (.assign .assign (.index (.ident "a") (.some (num 1))) (num 7)))
          (.cons (setX (.index (.ident "a") (.some (num 1)))) .nil))))
      (.cons (ext "g" (.cons (uParam "k") .nil)
          (.cons (setX (.member (newOf (.elem .bytes) (.ident "k")) "length")) .nil))
      (.cons (ext "h" (.cons (uParam "k") .nil)
          (.cons (.stmtItem (.simpleStmt (.declVar (.varDecl (.array u256T .none) (some .memory) "a")
            (.some (newOf (.array u256T .none) (.ident "k"))))))
          (.cons (setX (.addSub .add (.index (.ident "a") (.some (.addSub .sub (.ident "k") (num 1)))) (num 5))) .nil)))
      .nil)))))
    .nil)

def elabNew : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } unitNew)

#guard elabNew.isSome

-- **`new uint8[](k)`**: `k = 3` stores and reads 7; `k = 1` has no `a[1]`
-- (panic `0x32`).
#guard (elabNew.map fun el => runD el 0 [callW "f(uint256)" [3], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 7))]
#guard (elabNew.map fun el => runD el 0 [callW "f(uint256)" [1]]) ==
  some [some (.success []), some (.revert (panicData .index))]

-- **`new bytes(k)`**: length 5; a length of `2^64` panics `0x41`.
#guard (elabNew.map fun el => runD el 0 [callW "g(uint256)" [5], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 5))]
#guard (elabNew.map fun el => runD el 0 [callW "g(uint256)" [2 ^ 64]]) ==
  some [some (.success []), some (.revert (panicData .alloc))]

-- **Zeroed**: `new uint256[](2)[1] + 5` is 5.
#guard (elabNew.map fun el => runD el 0 [callW "h(uint256)" [2], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 5))]

-- **Refusals**: `new uint256[2](3)` (a static array; solc refuses it too);
-- `new string[](2)` (reference elements: not modelled; solc accepts it).
#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitOf (newOf (.array u256T (.some (num 2))) (num 3))))).isNone
#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitOf (newOf (.array (.elem .string) .none) (num 2))))).isNone
-- The same frame accepts `new uint256[](3)`.
#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitOf (newOf (.array u256T .none) (num 3))))).isSome

end Solidity.Source.InlineExamples
