import Solidity.Tools.Common

/-!
# `#run`: call a contract's function in the interpreter

```
#run CallsExample.addTwo(3)
#run Coin.mint(1, 5) with msg.sender := 7
#run Counter.dec() with count := 2
#run Counter.dec() from { storage := [("count", .int 2)] }
```

The identifier names the contract and the function: its last component is
the function, the rest a `Contract` constant.  The arguments are `sol{ … }`
expressions, typed against the parameters (`-1` at an `int` parameter).
`from σ` gives the state the call starts in (a `State`); without it the
contract starts fresh, every root at its default (`Contract.initStorage`),
with no funds.  `with` sets the transaction, a comma-separated list of
`msg.sender := n`, `msg.value := n`, `block.timestamp := n` and
`balance := n` (`address(this).balance`), over the start state's; and a
state variable of a value type, `count := 41`, over the start storage.

**A call is a program of one statement.**  Nothing at the value level
instantiates a function: the call is written as `sol{ … }` would read it
(`callStmt`) — `uint _r = f(a, b);` when `f` returns a value, `f(a, b);`
otherwise — and elaborated by `elabProg`, which inlines the body
(`Stmt.call`) as for any other call.  The value returned is then the local
`_r` of the final state.  `DiffTest.lean` builds its calls the same way.

The output is `ok`, the value returned, and the storage one root per line
(`fmtStorage`); or `revert`, or `stuck`.
-/

namespace Solidity.Tools

open Semantics

/-- The raw type of a value type, as a declaration spells it. -/
def PrimTy.raw : PrimTy → RawTy
  | .uint => .named "uint"
  | .int => .named "int"
  | .bool => .named "bool"

/-- The local a returning call's value lands in. -/
def retLocal : String := "_r"

/-- The call of `f` as one statement: `uint _r = f(args);` if `f` returns a
value, `f(args);` if it does not. -/
def callStmt (C : Contract) (f : String) (args : List RawExpr) : Except String RawStmt := do
  let some d := lookupBy f C.funs | throw s!"the contract declares no function {f}"
  match d.ret with
  | none => pure (.call (.name f) args)
  | some (_, .prim p) => pure (.decl (PrimTy.raw p) retLocal (some (.call f args)))
  | some (_, T) => throw s!"{f} returns a {Ty.toStr T}, not a value type"

/-- The call of `f`, elaborated: its body inlined. -/
def callProg [FreshNames] (C : Contract) (f : String) (args : List RawExpr) :
    Except String (Prog C) := do
  elabProg C [← callStmt C f args]

/-- The state a contract starts in: every root at its default, no funds, the
transaction `tx`. -/
def freshState (C : Contract) (tx : TxEnv := {}) (balance : Int := 0) : State :=
  { storage := C.initStorage, selfBalance := balance, tx }

/-- `σ` with the transaction fields given replaced. -/
def State.withTx (σ : State) (sender value time balance : Option Int) : State :=
  { σ with
    tx := { msgSender := sender.getD σ.tx.msgSender, msgValue := value.getD σ.tx.msgValue,
            timestamp := time.getD σ.tx.timestamp }
    selfBalance := balance.getD σ.selfBalance }

/-- `σ` with the state variables given replaced. -/
def State.withRoots (σ : State) (roots : List (Name × SVal)) : State :=
  { σ with storage := roots.foldl (fun st (r, v) => setBy r v st) σ.storage }

/-- What `#run` prints: the outcome, the value returned, the storage. -/
def runReport [FreshNames] (C : Contract) (σ : State) (f : String) (args : List RawExpr) :
    Except String (List String) := do
  let P ← callProg C f args
  pure <| match Prog.run σ P with
    | .error h => [fmtHalt h]
    | .ok σ' =>
      let ret := match σ'.valueOf (Var.ofName retLocal) with
        | some v => [s!"returns {Value.fmt v}"]
        | none => []
      ["ok"] ++ ret ++ fmtStorage C σ'.storage

/-- One field of the transaction, `msg.sender := 7`, or a state variable,
`count := 41`. -/
syntax runEnv := ident " := " term:max

/-- `#run C.f(a, b) [from σ] [with msg.sender := n, count := m, …]`: run the
call in the interpreter and print its outcome. -/
syntax (name := runCmd) "#run " ident "(" sol_expr,* ")" (" from " term:max)?
  (" with " runEnv,+)? : command

open Lean Elab Command Term Meta in
@[command_elab runCmd] def elabRun : CommandElab
  | `(#run $callee:ident ( $args:sol_expr,* ) $[from $σ?]? $[with $envs?,*]?) =>
    liftTermElabM do
    let (c, C, f) ← resolveFunction "#run" callee.getId
    let args ← liftMacroM <| args.getElems.mapM expandExpr
    let mut sender : Lean.Term ← `(none)
    let mut value : Lean.Term ← `(none)
    let mut time : Lean.Term ← `(none)
    let mut bal : Lean.Term ← `(none)
    let mut roots : Array Lean.Term := #[]
    for e in (envs?.map (·.getElems)).getD #[] do
      let `(runEnv| $k:ident := $v) := e | throwErrorAt e "#run: expected `name := value`"
      let n := k.getId.toString
      match n with
      | "msg.sender" => sender ← `(some ($v : Int))
      | "msg.value" => value ← `(some ($v : Int))
      | "block.timestamp" => time ← `(some ($v : Int))
      | "balance" => bal ← `(some ($v : Int))
      | _ =>
        match Semantics.lookupBy n C.vars with
        | some (.prim .bool) => roots := roots.push (← `(($(quote n), .prim (.bool ($v : Bool)))))
        | some (.prim _) => roots := roots.push (← `(($(quote n), .prim (.int ($v : Int)))))
        | some T => throwErrorAt k "#run: {n} is a {Ty.toStr T}: give it with `from`"
        | none => throwErrorAt k "#run: {n} is not one of msg.sender, msg.value, \
            block.timestamp, balance, nor a state variable of {c}"
    let Ct := mkCIdent c
    let σ ← match σ? with
      | some σ => `(($σ : Solidity.Semantics.State))
      | none => `(freshState $Ct)
    let t ← `(runReport $Ct (State.withRoots (State.withTx $σ $sender $value $time $bal)
      ([$roots,*] : List (Solidity.Name × Solidity.Semantics.SVal))) $(quote f) [$args,*])
    logInfo (String.intercalate "\n" (← evalLines "#run" t))
  | _ => throwUnsupportedSyntax

end Solidity.Tools
