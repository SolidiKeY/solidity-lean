import Solidity.Semantics

/-!
# Printing states as Solidity

The printers the `Tools/` commands share: a value as Solidity writes it,
read against its type (types as `Ty.toStr` spells them), a storage one
state variable per line (`fmtStorage`) or on one line (`fmtStorageLine`), a
transaction as `#run … with` sets it (`fmtTx`).  They are
for people, not for the kernel: `partial`, and nothing is proved about them.

A mapping prints its entries and then its default, `{7: 5, _: 0}`; an array
its live elements, not the `shadow` a `pop` leaves behind; a `bool` stored
where a `uint` is expected prints as it is, since a printer should show a
badly typed state rather than hide it.
-/

namespace Solidity.Tools

open Semantics

/-- A word: `5`, `-1`, `true`. -/
def Value.fmt : Value → String
  | .int n => toString n
  | .bool b => toString b

/-- A storage value read against its type. -/
partial def SVal.fmt : Ty → SVal → String
  | _, .prim v => Value.fmt v
  | .ref (.struct n), .struct fs =>
    let parts := fs.map fun (f, v) => s!"{f}: {SVal.fmt ((lookupBy f (structDef n)).getD .uint) v}"
    "{" ++ ", ".intercalate parts ++ "}"
  | T, .struct fs =>
    "{" ++ ", ".intercalate (fs.map fun (f, v) => s!"{f}: {SVal.fmt T v}") ++ "}"
  | T, .array es _ _ =>
    let E := match T with
      | .ref (.array E) | .ref (.fixed E _) => E
      | _ => T
    "[" ++ ", ".intercalate (es.map (SVal.fmt E)) ++ "]"
  | T, .map es d =>
    let (K, V) := match T with
      | .ref (.mapping K V) => (K, V)
      | _ => (T, T)
    let key : Int → String := fun k => if K == .bool then toString (k != 0) else toString k
    let parts := es.map (fun (k, v) => s!"{key k}: {SVal.fmt V v}") ++ [s!"_: {SVal.fmt V d}"]
    "{" ++ ", ".intercalate parts ++ "}"

/-- The storage, one state variable per line, in the contract's order;
a root the contract does not declare is printed after, untyped. -/
def fmtStorage (C : Contract) (st : List (Name × SVal)) : List String :=
  let declared := C.vars.filterMap fun (r, T) =>
    (lookupBy r st).map fun v => s!"{r} = {SVal.fmt T v}"
  let extra := st.filterMap fun (r, v) =>
    if (C.vars.find? (·.1 == r)).isSome then none else some s!"{r} = {SVal.fmt .uint v}"
  declared ++ extra

/-- The storage on one line: `count = 1; total = 0`. -/
def fmtStorageLine (C : Contract) (st : List (Name × SVal)) : String :=
  "; ".intercalate (fmtStorage C st)

/-- What a run starts from besides the storage and the arguments, as `#run
… with` sets it: the sender and the value always, the time, the funds and
the ledger where they are not zero. -/
def fmtTx (σ : State) : List String :=
  [s!"msg.sender = {σ.tx.msgSender}", s!"msg.value = {σ.tx.msgValue}"] ++
  (if σ.tx.timestamp = 0 then [] else [s!"block.timestamp = {σ.tx.timestamp}"]) ++
  (if σ.selfBalance = 0 then [] else [s!"balance = {σ.selfBalance}"]) ++
  (if σ.net.isEmpty then [] else
    ["net = " ++ "{" ++ ", ".intercalate (σ.net.map fun (a, b) => s!"{a}: {b}") ++ "}"])

/-- The value the local `x` holds, if it holds a value: what a call
returned, read back from its final state. -/
def _root_.Solidity.Semantics.State.valueOf (σ : State) (x : Var) : Option Value :=
  match lookupBy x σ.env with
  | some (.val v) => some v
  | _ => none

/-- A run's outcome. -/
def fmtHalt : Halt → String
  | .revert => "revert"
  | .stuck => "stuck (the program is outside the interpreter's typing)"
  | .panic => "panic (an `assert` failed)"
  | .diverge => "diverge (a loop that never ends)"

/-- How tightly a clause binds, as `SpecSyntax.lean` parses it: `*` 70,
`+` 65, a comparison 50, `==` 45, `&&` 35, `||` 30, `->` 25, `<->` 20. -/
def SpecExpr.prec : SpecExpr → Nat
  | .binop op _ _ => match op with
    | .mul | .div | .mod => 70
    | .add | .sub => 65
    | .lt | .le | .gt | .ge => 50
    | .eqB | .neB => 45
    | .and => 35
    | .or => 30
    | _ => 60
  | .imp .. => 25
  | .iff .. => 20
  | .all .. | .ex .. => 0
  | .unop .. => 75
  | _ => 100

/-- A clause as written, `count == \old(count) + 1`, parenthesised where
the grammar needs it. -/
partial def SpecExpr.fmt : SpecExpr → String
  | .num n => toString n
  | .bool b => toString b
  | .name x => x
  | .result => "\\result"
  | .old e => s!"\\old({SpecExpr.fmt e})"
  | .net e => s!"net({SpecExpr.fmt e})"
  | .field e f => s!"{SpecExpr.fmt.at 100 e}.{f}"
  | .index e k => s!"{SpecExpr.fmt.at 100 e}[{SpecExpr.fmt k}]"
  | .unop op e => s!"{UnOp.sym op}{SpecExpr.fmt.at 75 e}"
  | e@(.binop op a b) =>
    let p := SpecExpr.prec e
    s!"{SpecExpr.fmt.at p a} {BinOp.sym op} {SpecExpr.fmt.at (p + 1) b}"
  | .imp a b => s!"{SpecExpr.fmt.at 26 a} -> {SpecExpr.fmt.at 25 b}"
  | .iff a b => s!"{SpecExpr.fmt.at 20 a} <-> {SpecExpr.fmt.at 21 b}"
  | .all p x e => s!"\\forall {Ty.toStr (.prim p)} {x}; {SpecExpr.fmt e}"
  | .ex p x e => s!"\\exists {Ty.toStr (.prim p)} {x}; {SpecExpr.fmt e}"
where
  /-- An operand where the grammar expects precedence `p`: parenthesised
  if it binds less tightly. -/
  «at» (p : Nat) (e : SpecExpr) : String :=
    if SpecExpr.prec e < p then s!"({SpecExpr.fmt e})" else SpecExpr.fmt e

/-- An `assignable` location as written: `balances[msg.sender]`, `m[*]`. -/
partial def SpecLoc.fmt : SpecLoc → String
  | .root r => r
  | .field l f => s!"{SpecLoc.fmt l}.{f}"
  | .index l e => s!"{SpecLoc.fmt l}[{SpecExpr.fmt e}]"
  | .all l => s!"{SpecLoc.fmt l}[*]"

end Solidity.Tools
