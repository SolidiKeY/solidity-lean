import Lean
import Solidity.Syntax.Checked
import Solidity.Semantics.Run
import Solidity.Tools.Show

/-!
# Bounded typed programs printed for an external solc/EthereumJS oracle

This tool deliberately admits only closed primitive-root programs of `caseContract`.
Every unsupported constructor returns a named refusal; it is never erased.
No compiler or EVM dependency enters Lake. These comparisons are evidence, not
compiler correctness theorems. Checked execution uses the existing withPanics.
-/
namespace Solidity.Tools.SolCases

def caseContract : Contract := { vars := [("x", .prim .uint), ("y", .prim .uint)] }

abbrev Result := Except String

/-- Closed values only; generated names cannot capture a local. -/
def value {Γ : Ctx} : {p : PrimTy} → Val caseContract Γ p → Result String
  | .uint, .simple (.lit n _) => pure s!"uint256({n})"
  | .int, .simple (.lit n _) => pure s!"int256({n})"
  | .bool, .simple (.lit _ _) => throw "solcases.value.numericBool"
  | _, .simple (.bool b) => pure (toString b)
  | _, .read (.root r _) => pure r
  | _, .binop op _ _ a b => do
    unless [BinOp.add, .sub, .mul, .div, .mod, .eqB, .neB, .lt, .le, .gt, .ge,
      .and, .or].contains op do throw "solcases.value.operator"
    return s!"({← value a} {op.sym} {← value b})"
  | _, _ => throw "solcases.value.unsupported"

mutual
/-- A typed statement to source, with explicit refusal outside the fragment. -/
def statement {Γ Δ : Ctx} : Stmt caseContract Γ Δ → Result String
  | .assign (.root r _) (.val v) => return s!"{r} = {← value v};"
  | .delete (.root r _) => pure s!"delete {r};"
  | .require c => return s!"require({← value c});"
  | .assert c => return s!"assert({← value c});"
  | .revert => pure "revert();"
  | .ite c a b => do
    let cond : String ← value c
    let yes : String ← program a
    let no : String ← program b
    return "if (" ++ cond ++ ") { " ++ yes ++ " } else { " ++ no ++ " }"
  | _ => throw "solcases.statement.unsupported"

def program {Γ Δ : Ctx} : Prog caseContract Γ Δ → Result String
  | .nil => pure ""
  | .cons s p => return s!"{← statement s} {← program p}"
end

def literal (n : Nat) : Result (Val caseContract [] .uint) :=
  if h : PrimTy.uint.inRange (n : Int) = true then pure (.simple (.lit n h))
  else throw "solcases.literal.range"

def x : Loc caseContract [] (.prim .uint) := .root "x" (by rfl)
def y : Loc caseContract [] (.prim .uint) := .root "y" (by rfl)

def sequence (ss : List (Stmt caseContract [] [])) : Prog caseContract [] [] :=
  ss.foldr Prog.cons .nil

def setup (a b : Nat) : Result (Prog caseContract [] []) := do
  return sequence [.assign x (.val (← literal a)), .assign y (.val (← literal b))]

/-- Five operation families, plus successful/failing guards and explicit revert.
The first write exposes rollback bugs even when the second statement fails. -/
def candidate (kind : Nat) : Result (Prog caseContract [] []) := do
  let a : Val caseContract [] .uint := .read x
  let b : Val caseContract [] .uint := .read y
  let op := [BinOp.add, .sub, .mul, .div, .mod][kind]?.getD .add
  if h : op.accepts .uint = true then
    if hr : op.ret .uint = .uint then
      let update := Stmt.assign x (.val (.binop op h hr a b))
      if kind < 5 then return sequence [update]
      let write := Stmt.assign x (.val (← literal 7))
      let guard : Val caseContract [] .bool := .binop .lt (by rfl) (by rfl) a b
      if kind == 5 then return sequence [write, .require guard]
      if kind == 6 then return sequence [write, .assert guard]
      if kind == 7 then return sequence [write, .revert]
      if kind == 8 then return sequence [.ite guard (sequence [update]) (sequence [.delete x])]
      if kind == 9 then return sequence [.assign x (.val
        (.binop .div (by rfl) (by rfl) (← literal 5) (← literal 2)))]
      throw "solcases.kind.range"
    else throw "solcases.operator.result"
  else throw "solcases.operator.type"

def bytesHex (bs : List UInt8) : String :=
  "0x" ++ String.mk (bs.flatMap fun b =>
    let digits := "0123456789abcdef".toList
    [digits[b.toNat / 16]!, digits[b.toNat % 16]!])

def storage (s : State caseContract []) : Lean.Json :=
  Lean.Json.arr ((fmtStorage caseContract s.storage).map Lean.toJson).toArray

/-- Rollback is the transaction adapter's observation: failed typed runs expose
no intermediate state. Unknown halts are blocked, never matched as reverts. -/
def observation (start : State caseContract []) (p : Prog caseContract [] []) : Result Lean.Json := do
  match Prog.run start p.withPanics with
  | .ok o => return Lean.Json.mkObj [("failed", Lean.toJson false),
      ("storage", storage o.st), ("revertData", Lean.toJson "0x")]
  | .error h =>
    let data ← match h with
      | .revert => pure "0x"
      | .panic => pure (bytesHex (Semantics.encodePanic 1))
      | .revertWith d => pure (bytesHex d)
      | _ => throw "solcases.halt.unadapted"
    return Lean.Json.mkObj [("failed", Lean.toJson true),
      ("storage", storage start), ("revertData", Lean.toJson data)]

def emit (seed index a b kind : Nat) : Result Lean.Json := do
  let init ← setup a b
  let p ← candidate kind
  let .ok start := Prog.run (State.init caseContract) init | throw "solcases.setup.failed"
  let expected ← observation start.st p
  let source := "pragma solidity 0.8.38; contract Generated { uint256 x; uint256 y; " ++
    "function setUp() external { " ++ (← program init) ++ " } " ++
    "function run() external returns (uint256,uint256) { " ++ (← program p) ++
    " return (x,y); } function observe() external view returns(uint256,uint256) { return(x,y); } }"
  return Lean.Json.mkObj [("schema", Lean.toJson (1 : Nat)), ("seed", Lean.toJson seed),
    ("index", Lean.toJson index), ("a", Lean.toJson (toString a)),
    ("b", Lean.toJson (toString b)), ("kind", Lean.toJson kind),
    ("source", Lean.toJson source), ("expected", expected)]

#guard (program (sequence [.assign x (.val (.read y))])).toOption == some "x = y; "
#guard (statement (Stmt.assumeFalse : Stmt caseContract [] [])).toOption == none
#guard (candidate 10).toOption.isNone

end Solidity.Tools.SolCases
