import Solidity.Source.DecodeExamples

/-!
# Controls of `calldata` references (lane FU2-B)

A unit written as syntax, elaborated by `elaborate`, deployed and called
through the semantics. Its external functions take `calldata` parameters,
which dispatch keeps as references into the call data (`Val.cdRef`):

```solidity
contract D {
  uint256 public x;
  function f(uint8[] calldata xs, uint256 i) external { x = xs[i]; }
  function g(uint8[] calldata xs) external { x = xs.length; }
  function h(bytes calldata b) external { x = uint8(b[1:3][1]); }
  function k(bytes calldata b, uint256 s, uint256 e) external { x = b[s:e].length; }
  function m(uint8[] calldata xs) external { uint8[] memory c = xs; x = c.length; }
  function p(bytes calldata b) external { x = abi.decode(b[4:], (uint256)); }
}
```

As solc's: at entry the offset, a length below `2^64` and the elements'
extent are checked (each failure reverts with no data); an element is
validated only when read (`xs[1] = 300` is no `uint8`: `f(xs, 0)` runs,
`f(xs, 1)` reverts), an index past the length panics with `0x32`, a slice
whose start passes its end or whose end passes the length reverts with no
data, a copy into memory validates every element.
-/

namespace Solidity.Source.CalldataExamples

open Solidity.Source Solidity.Source.Examples Solidity.Source.SemanticsExamples
open Solidity.Source.ElaborateExamples Solidity.Source.DecodeExamples
open Solidity.Roadmap (Bytes Outcome)

def cdParam (t : Syn .typeName) (x : String) : Syn .param := .param t (some .calldata) (some x)
def uParam (x : String) : Syn .param := .param u256 none (some x)
def u8T : Syn .typeName := .elem u8
def ext (name : String) (ps : Syn (.list .param)) (body : Syn (.list (.item .body))) : Syn (.part false) :=
  .function (.ident name) ps (some .external) none .nil false none .nil (.some (.block body))

def unitCd : Syn .unit :=
  .unit (.cons (.contract false "D" .none .nil
      (.cons (.stateVar u256 (some .pub) none none false "x" .none)
      (.cons (ext "f" (.cons (cdParam (.array u8T .none) "xs") (.cons (uParam "i") .nil))
          (.cons (setX (.index (.ident "xs") (.some (.ident "i")))) .nil))
      (.cons (ext "g" (.cons (cdParam (.array u8T .none) "xs") .nil)
          (.cons (setX (.member (.ident "xs") "length")) .nil))
      (.cons (ext "h" (.cons (cdParam (.elem .bytes) "b") .nil)
          (.cons (setX (.call (ty u8) (.positional (.cons
            (.index (.slice (.ident "b") (.some (num 1)) (.some (num 3))) (.some (num 1))) .nil)))) .nil))
      (.cons (ext "k" (.cons (cdParam (.elem .bytes) "b") (.cons (uParam "s") (.cons (uParam "e") .nil)))
          (.cons (setX (.member (.slice (.ident "b") (.some (.ident "s")) (.some (.ident "e"))) "length")) .nil))
      (.cons (ext "m" (.cons (cdParam (.array u8T .none) "xs") .nil)
          (.cons (.stmtItem (.simpleStmt (.declVar (.varDecl (.array u8T .none) (some .memory) "c")
            (.some (.ident "xs")))))
          (.cons (setX (.member (.ident "c") "length")) .nil)))
      (.cons (ext "p" (.cons (cdParam (.elem .bytes) "b") .nil)
          (.cons (setX (.call (.member (.ident "abi") "decode") (.positional (.cons
            (.slice (.ident "b") (.some (num 4)) .none) (.cons (one (ty u256E)) .nil))))) .nil))
      (.cons (ext "q" (.cons (cdParam (.array u8T .none) "xs") .nil)
          (.cons (setX (.index (.slice (.ident "xs") (.some (num 1)) .none) (.some (num 0)))) .nil))
      (.cons (ext "r" (.cons (cdParam (.elem .bytes) "b") .nil)
          (.cons (setX (.member (.slice (.ident "b") .none (.some (num 2))) "length")) .nil))
      (.cons (ext "t" (.cons (cdParam (.elem .bytes) "b") .nil)
          (.cons (setX (.call (ty (.int false 32 (by decide))) (.positional (.cons
            (.call (ty (.fixedBytes 4 (by decide))) (.positional (.cons (.ident "b") .nil))) .nil)))) .nil))
      (.cons (.stateVar (.elem .bytes) none none none false "sb" .none)
      (.cons (ext "u" (.cons (cdParam (.elem .bytes) "b") .nil)
          (.cons (stmt (.assign .assign (.ident "sb") (.ident "b")))
          (.cons (setX (.member (.ident "sb") "length")) .nil)))
      .nil))))))))))))
    .nil)

def elabCd : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } unitCd)

#guard elabCd.isSome

/-- Call data: the selector, then words. -/
def callW (sig : String) (ws : List Nat) : Bytes := selOf sig ++ words ws

/-- `"abcd"` padded to a word. -/
def abcd : Bytes := [97, 98, 99, 100] ++ List.replicate 28 0

-- **Access-time validation**: `xs = [1, 300]`; `xs[0]` runs, `xs[1]` is no
-- `uint8` and reverts with no data only when read; `xs[2]` panics `0x32`.
#guard (elabCd.map fun el => runD el 0 [callW "f(uint8[],uint256)" [64, 0, 2, 1, 300], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 1))]
#guard (elabCd.map fun el => runD el 0 [callW "f(uint8[],uint256)" [64, 1, 2, 1, 300]]) ==
  some [some (.success []), some (.revert [])]
#guard (elabCd.map fun el => runD el 0 [callW "f(uint8[],uint256)" [64, 2, 2, 1, 300]]) ==
  some [some (.success []), some (.revert (panicData .index))]

-- **Entry checks**: the length of `[1, 300]` is read without its elements;
-- a length of `2^64` reverts with no data (not a panic: calldata is not
-- allocated; this payload also fails the extent check, which reverts the
-- same way), elements past the data and an offset past the data revert.
#guard (elabCd.map fun el => runD el 0 [callW "g(uint8[])" [32, 2, 1, 300], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 2))]
#guard (elabCd.map fun el => runD el 0 [callW "g(uint8[])" [32, 2 ^ 64], callW "g(uint8[])" [32, 3, 1, 2],
    callW "g(uint8[])" [64]]) ==
  some [some (.success []), some (.revert []), some (.revert []), some (.revert [])]

-- **Slices of `bytes`**: `"abcd"[1:3][1]` is `c`; `[1:3]` has length 2, a
-- start past the end and an end past the length revert with no data.
#guard (elabCd.map fun el => runD el 0 [selOf "h(bytes)" ++ words [32, 4] ++ abcd, selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 99))]
#guard (elabCd.map fun el => runD el 0 [selOf "k(bytes,uint256,uint256)" ++ words [96, 1, 3, 4] ++ abcd,
    selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 2))]
#guard (elabCd.map fun el => runD el 0 [selOf "k(bytes,uint256,uint256)" ++ words [96, 3, 1, 4] ++ abcd,
    selOf "k(bytes,uint256,uint256)" ++ words [96, 1, 5, 4] ++ abcd]) ==
  some [some (.success []), some (.revert []), some (.revert [])]

-- **Copies into memory** validate every element: `[1, 2]` copies, `[1, 300]`
-- reverts with no data.
#guard (elabCd.map fun el => runD el 0 [callW "m(uint8[])" [32, 2, 1, 2], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 2))]
#guard (elabCd.map fun el => runD el 0 [callW "m(uint8[])" [32, 2, 1, 300]]) ==
  some [some (.success []), some (.revert [])]

-- **`abi.decode` of a slice**: `b[4:]` past a four-byte prefix decodes 7.
#guard (elabCd.map fun el => runD el 0 [selOf "p(bytes)" ++ words [32, 36] ++ ([1, 2, 3, 4] ++ argN 7 ++
    List.replicate 28 0), selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 7))]

-- **Array slices** move by 32 bytes per element: `[1, 2, 3][1:][0]` is 2;
-- `"abcd"[:2]` has length 2.
#guard (elabCd.map fun el => runD el 0 [callW "q(uint8[])" [32, 3, 1, 2, 3], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 2))]
#guard (elabCd.map fun el => runD el 0 [selOf "r(bytes)" ++ words [32, 4] ++ abcd, selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 2))]

-- **`bytes4(b)` of `calldata` `bytes`**: the first four bytes,
-- `0x61626364`.
#guard (elabCd.map fun el => runD el 0 [selOf "t(bytes)" ++ words [32, 4] ++ abcd, selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 0x61626364))]

-- **A copy of `calldata` into storage**: `sb = b` stores `"abcd"`.
#guard (elabCd.map fun el => runD el 0 [selOf "u(bytes)" ++ words [32, 4] ++ abcd, selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 4))]

end Solidity.Source.CalldataExamples
