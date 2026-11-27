import Solidity.Source.CalldataExamples


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

#guard (elabInl.map fun el => runD el 0 [callW "f(uint256)" [1], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 2))]
#guard (elabInl.map fun el => runD el 0 [callW "f(uint256)" [3]]) ==
  some [some (.success []), some (.revert (panicData .index))]

#guard (elabInl.map fun el => runD el 0 [callW "g()" [], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 256))]

#guard (elabInl.map fun el => runD el 0 [callW "h(uint256)" [41], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 42))]

def unitOf (e : Syn .expr) : Syn .unit :=
  .unit (.cons (.contract false "J" .none .nil
      (.cons (ext "f" .nil (.cons (stmt e) .nil)) .nil))
    .nil)

#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitOf (.inlineArray (num 1) (.cons (.unaryPrefix .neg (num 1)) .nil))))).isNone
#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitOf (.inlineArray (.lit (.str [97])) (.cons (.lit (.str [98])) .nil))))).isNone
#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitOf (.inlineArray (num 1) (.cons (num 2) .nil))))).isSome

def unitBody (body : Syn (.list (.item .body))) : Syn .unit :=
  .unit (.cons (.contract false "D" .none .nil
      (.cons (.stateVar u256 (some .pub) none none false "x" .none)
      (.cons (ext "f" .nil body) .nil)))
    .nil)

#guard (elaborate (resolveUnit { pipeline := .legacy } (unitBody (.cons (setX (.mulDivMod .mul
    (.index (.inlineArray (num 1) (.cons (num 256) .nil)) (.some (num 1))) (num 256))) .nil)))).map
    (fun el => runD el 0 [callW "f()" []]) ==
  some [some (.success []), some (.revert (panicData .arithmetic))]

#guard (elaborate (resolveUnit { pipeline := .legacy } (unitBody (.cons
    (.stmtItem (.simpleStmt (.declVar (.varDecl (.array u256T (.some (num 2))) (some .memory) "c")
      (.some (.inlineArray (num 1) (.cons (num 2) .nil)))))) .nil)))).isNone


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

#guard (elabNew.map fun el => runD el 0 [callW "f(uint256)" [3], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 7))]
#guard (elabNew.map fun el => runD el 0 [callW "f(uint256)" [1]]) ==
  some [some (.success []), some (.revert (panicData .index))]

#guard (elabNew.map fun el => runD el 0 [callW "g(uint256)" [5], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 5))]
#guard (elabNew.map fun el => runD el 0 [callW "g(uint256)" [2 ^ 64]]) ==
  some [some (.success []), some (.revert (panicData .alloc))]

#guard (elabNew.map fun el => runD el 0 [callW "h(uint256)" [2], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 5))]

#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitOf (newOf (.array u256T (.some (num 2))) (num 3))))).isNone
#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitOf (newOf (.array (.elem .string) .none) (num 2))))).isNone
#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitOf (newOf (.array u256T .none) (.call (ty (.int true 256 (by decide))) (.positional (.cons (num 3) .nil))))))).isNone
#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitOf (newOf (.elem .string) (num 4))))).isSome
#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitOf (newOf (.array u256T .none) (num 3))))).isSome

end Solidity.Source.InlineExamples
