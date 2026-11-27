import Solidity.Source.DecodeExamples


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
      .nil)))))))))))))
    .nil)

def elabCd : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } unitCd)

#guard elabCd.isSome

def callW (sig : String) (ws : List Nat) : Bytes := selOf sig ++ words ws

def abcd : Bytes := [97, 98, 99, 100] ++ List.replicate 28 0

#guard (elabCd.map fun el => runD el 0 [callW "f(uint8[],uint256)" [64, 0, 2, 1, 300], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 1))]
#guard (elabCd.map fun el => runD el 0 [callW "f(uint8[],uint256)" [64, 1, 2, 1, 300]]) ==
  some [some (.success []), some (.revert [])]
#guard (elabCd.map fun el => runD el 0 [callW "f(uint8[],uint256)" [64, 2, 2, 1, 300]]) ==
  some [some (.success []), some (.revert (panicData .index))]

#guard (elabCd.map fun el => runD el 0 [callW "g(uint8[])" [32, 2, 1, 300], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 2))]
#guard (elabCd.map fun el => runD el 0 [callW "g(uint8[])" [32, 2 ^ 64], callW "g(uint8[])" [32, 3, 1, 2],
    callW "g(uint8[])" [64]]) ==
  some [some (.success []), some (.revert []), some (.revert []), some (.revert [])]

#guard (elabCd.map fun el => runD el 0 [selOf "h(bytes)" ++ words [32, 4] ++ abcd, selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 99))]
#guard (elabCd.map fun el => runD el 0 [selOf "k(bytes,uint256,uint256)" ++ words [96, 1, 3, 4] ++ abcd,
    selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 2))]
#guard (elabCd.map fun el => runD el 0 [selOf "k(bytes,uint256,uint256)" ++ words [96, 3, 1, 4] ++ abcd,
    selOf "k(bytes,uint256,uint256)" ++ words [96, 1, 5, 4] ++ abcd]) ==
  some [some (.success []), some (.revert []), some (.revert [])]

#guard (elabCd.map fun el => runD el 0 [callW "m(uint8[])" [32, 2, 1, 2], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 2))]
#guard (elabCd.map fun el => runD el 0 [callW "m(uint8[])" [32, 2, 1, 300]]) ==
  some [some (.success []), some (.revert [])]

#guard (elabCd.map fun el => runD el 0 [selOf "p(bytes)" ++ words [32, 36] ++ ([1, 2, 3, 4] ++ argN 7 ++
    List.replicate 28 0), selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 7))]

#guard (elabCd.map fun el => runD el 0 [callW "q(uint8[])" [32, 3, 1, 2, 3], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 2))]
#guard (elabCd.map fun el => runD el 0 [selOf "r(bytes)" ++ words [32, 4] ++ abcd, selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 2))]

#guard (elabCd.map fun el => runD el 0 [selOf "t(bytes)" ++ words [32, 4] ++ abcd, selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 0x61626364))]

#guard (elabCd.map fun el => runD el 0 [selOf "u(bytes)" ++ words [32, 4] ++ abcd, selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 4))]


def unitFb : Syn .unit :=
  .unit (.cons (.contract false "D" .none .nil
      (.cons (.stateVar u256 (some .pub) none none false "x" .none)
      (.cons (.fallback (.fbParams (cdParam (.elem .bytes) "input") .nil
            (.cons (.param (.elem .bytes) (some .memory) none) .nil)) true none .nil false none
          (.some (.block (.cons (setX (.member (.ident "input") "length"))
            (.cons (.stmtItem (.returnStmt (.some (.slice (.ident "input") (.some (num 1)) (.some (num 3))))))
            .nil)))))
      .nil)))
    .nil)

def elabFb : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } unitFb)

#guard elabFb.isSome

#guard (elabFb.map fun el => runD el 0 [[0xaa, 0xbb, 0xcc, 0xdd], selOf "x()"]) ==
  some [some (.success []), some (.success [0xbb, 0xcc]), some (.success (arg 4))]
#guard (elabFb.map fun el => runD el 0 [[0xaa, 0xbb]]) == some [some (.success []), some (.revert [])]

end Solidity.Source.CalldataExamples
