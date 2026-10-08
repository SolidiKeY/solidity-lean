import Solidity.Tools.Common
import Solidity.Semantics.Core.TypedRun
import Solidity.Semantics.Core.TypedToSem

/-!
# `#run`: call a contract's function in the typed run

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
`_r` of the final state; of several, `(uint _r0, uint _r1) = f(a, b);` and
the locals `_r0`, `_r1`, … (`runStmt`).  The program is resolved to the
scoped syntax (`Core.Prog.resolve`) and run typed (`Core.Prog.trun`,
`Semantics/Core/TypedRun.lean`) from the start state read at the contract's
types (`typedState?`): its storage, ledger, funds and transaction.  A start
state that is not of those types, or that has locals or memory, is an error.
`DiffTest.lean` builds its calls the same way, but a call of several returns
as the bare `f(a, b);`, whose returns the inlined body declares.

The output is `ok`, the value returned, and the storage one root per line
(`fmtStorage`, of the storage erased); or `revert`, or `panic`.  A loop runs
by iterating it (`TLoop.runImpl'`), so a call that never ends does not
return.

```
#deploy Mini(7) with msg.sender := 3
```

`#deploy C(args)` deploys `C` in the typed run (`Core.Contract.deployT`'s
reading): it runs `constructor(args);` (`ctorProg`, the initializers and the
constructor's body) from `Contract.deployState`, whose ledger and funds hold what
`msg.value := n` sends; `with` takes the transaction's fields only.  The
output is `ok`, the funds, and the storage; or how it halted.
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

/-- The call `#run` reports: `callStmt`, but a function of several returns
lands them in `_r0`, `_r1`, …: `(uint _r0, uint _r1) = f(args);`.  (`callProg`
keeps the bare call, whose returns the body declares, for `#difftest`: a call
with targets is outside the compiled fragment.) -/
def runStmt (C : Contract) (f : String) (args : List RawExpr) : Except String RawStmt := do
  let some d := lookupBy f C.funs | throw s!"the contract declares no function {f}"
  if d.rets.length < 2 then callStmt C f args else
  let vs ← d.rets.zipIdx.mapM fun ((_, T), i) => match T with
    | .prim p => pure (some (PrimTy.raw p, s!"{retLocal}{i}"))
    | T => throw s!"{f} returns a {Ty.toStr T}, not a value type"
  pure (.tupleDecl vs (.call f args))

/-- The call of `f`, elaborated: its body inlined. -/
def callProg [FreshNames] (C : Contract) (f : String) (args : List RawExpr) :
    Except String (Surface.Prog C) := do
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

/-- No locals and no memory: what the typed run's start state has
(`Core.TState C []`, its heap empty). -/
def noLocals (σ : State) : Bool :=
  σ.env.isEmpty && σ.heap.isEmpty && σ.nextId == 0

/-- A state of no locals and no memory (`none` for any other), read at the contract's types: the
storage (`SFields.ofU`), the funds and the transaction's words as `uint`s,
the ledger as it is; `none` where one is not of its type. -/
def typedState? (C : Contract) (σ : State) : Option (Core.TState C []) := do
  guard (noLocals σ)
  let st ← Core.SFields.ofU σ.storage C.vars
  let u (n : Int) : Option PrimTy.uint.Denote := PrimTy.ofValue? .uint (.int n)
  let bal ← u σ.selfBalance
  let snd ← u σ.tx.msgSender
  let val ← u σ.tx.msgValue
  let now ← u σ.tx.timestamp
  let addr ← u σ.tx.selfAddress
  let tx : Core.TTx :=
    { msgSender := snd, msgValue := val, timestamp := now, selfAddress := addr, ext := σ.tx.ext }
  pure (Core.TState.mk st [] Core.Heap.empty () σ.net bal tx)

/-- **A block run from an untyped state**, in the typed run: `P` resolved
from no locals (`Core.Prog.resolve`), run by `Core.Prog.trun` from `σ` read
at the contract's types (`typedState?`), and its end state named back
(`Core.TState.toSem`, under the block's names) or its halt erased
(`THalt.erase`); `stuck` where `P` does not resolve or `σ` is not of the
contract's types.  What the examples' `#eval`s run since today's
`Stmt.run` was deleted (W4 `modal`, `docs/intrinsic.md`). -/
def _root_.Solidity.Surface.Prog.runT {C : Contract} (σ : State) (P : Surface.Prog C) : Res State :=
  match Core.Prog.resolve [] P, typedState? C σ with
  | .ok ⟨Γ', Q⟩, some τ =>
    match Core.Prog.trun τ Q with
    | .ok o => .ok (o.st.toSem Γ'.names)
    | .error h => .error h.erase
  | _, _ => .error .stuck

/-- What the local `x` holds after `P` runs from `σ` (`Surface.Prog.runT`). -/
def _root_.Solidity.Surface.Prog.localAfterT {C : Contract} (σ : State) (P : Surface.Prog C)
    (x : String) : Res Binding := do
  (← Surface.Prog.runT σ P).getEnv (.user x)

/-- A deployment in the typed run, its end state named back: `#deploy`'s
(`deployReport`), as a value. -/
def _root_.Solidity.Contract.deployRun (C : Contract) (P : Surface.Prog C)
    (tx : TxEnv) : Res State :=
  if !((C.ctor.map (·.payable)).getD false) && tx.msgValue != 0 then .error .revert
  else Surface.Prog.runT (C.deployState tx) P

/-- The locals of a typed environment, innermost first: each one's level at
base `0` (`Evm.Core.lvl`), and its type and value if it is a value local. -/
def localCells {C : Contract} {H : Core.HTy} : (Γ : Core.Ctx) → Core.TEnv C H Γ →
    List (Nat × Option (PrimTy × Value))
  | [], _ => []
  | t :: Γ, e =>
    (match t, e.1 with
      | .val p, v => (Γ.length, some (p, PrimTy.erase (p := p) v))
      | _, _ => (Γ.length, none)) :: localCells Γ e.2

/-- The value locals of a typed environment, by the names of its context. -/
def localVals {C : Contract} {H : Core.HTy} {Γ : Core.Ctx} (names : List Var)
    (e : Core.TEnv C H Γ) : List (Var × Value) :=
  (names.zip (localCells Γ e)).filterMap fun (x, _, c) => c.map fun (_, v) => (x, v)

/-- What `#run` prints: the outcome, the value returned, the storage. -/
def runReport [FreshNames] (C : Contract) (σ : State) (f : String) (args : List RawExpr) :
    Except String (List String) := do
  let P ← elabProg C [← runStmt C f args]
  let ⟨Γ', Q⟩ ← Core.Prog.resolve [] P
  unless noLocals σ do
    throw "a start state with locals or memory is not supported by the typed run"
  let some τ := typedState? C σ | throw "the start state is not of the contract's types"
  let n : Nat := ((lookupBy f C.funs).map (·.rets.length)).getD 0
  pure <| match Core.Prog.trun τ Q with
    | .error h => [fmtHalt h.erase]
    | .ok o =>
      let vals := localVals Γ'.names o.st.env
      let ret := if n ≥ 2 then
          let vs := (List.range n).filterMap fun i => lookupBy (Var.ofName s!"{retLocal}{i}") vals
          [s!"returns ({", ".intercalate (vs.map Value.fmt)})"]
        else match lookupBy (Var.ofName retLocal) vals with
          | some v => [s!"returns {Value.fmt v}"]
          | none => []
      ["ok"] ++ ret ++ fmtStorage C o.st.storage.erase

/-- One field of the transaction, `msg.sender := 7`, or a state variable,
`count := 41`. -/
syntax runEnv := ident " := " term:max

/-- `#run C.f(a, b) [from σ] [with msg.sender := n, count := m, …]`: run the
call in the typed run and print its outcome. -/
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

/-- What `#deploy` prints: the deployment's outcome in the typed run
(`Core.Contract.deployT`'s: a constructor that is not `payable` refuses
value, else `constructor(args);` runs from `Contract.deployState`), the
contract's funds and its storage. -/
def deployReport [FreshNames] (C : Contract) (args : List RawExpr) (tx : TxEnv) :
    Except String (List String) := do
  let P ← ctorProg C args
  let ⟨_, Q⟩ ← Core.Prog.resolve [] P
  let some τ := typedState? C (C.deployState tx) | throw "the deployment's start is not of the contract's types"
  if !((C.ctor.map (·.payable)).getD false) && tx.msgValue != 0 then return [fmtHalt .revert]
  pure <| match Core.Prog.trun τ Q with
    | .error h => [fmtHalt h.erase]
    | .ok o => ["ok", s!"balance {o.st.selfBalance.1}"] ++ fmtStorage C o.st.storage.erase

/-- `#deploy C(a, b) [with msg.sender := n, msg.value := m, …]`: deploy the
contract `C` in the interpreter and print its outcome. -/
syntax (name := deployCmd) "#deploy " ident "(" sol_expr,* ")" (" with " runEnv,+)? : command

open Lean Elab Command Term Meta in
@[command_elab deployCmd] def elabDeploy : CommandElab
  | `(#deploy $c:ident ( $args:sol_expr,* ) $[with $envs?,*]?) => liftTermElabM do
    let some c ← contractConst? c.getId | throwErrorAt c "#deploy: {c.getId} is not a contract"
    let args ← liftMacroM <| args.getElems.mapM expandExpr
    let mut sender : Lean.Term ← `(0)
    let mut value : Lean.Term ← `(0)
    let mut time : Lean.Term ← `(0)
    for e in (envs?.map (·.getElems)).getD #[] do
      let `(runEnv| $k:ident := $v) := e | throwErrorAt e "#deploy: expected `name := value`"
      match k.getId.toString with
      | "msg.sender" => sender := v
      | "msg.value" => value := v
      | "block.timestamp" => time := v
      | n => throwErrorAt k "#deploy: {n} is not one of msg.sender, msg.value, block.timestamp"
    let t ← `(deployReport $(mkCIdent c) [$args,*]
      { msgSender := ($sender : Int), msgValue := ($value : Int), timestamp := ($time : Int) })
    logInfo (String.intercalate "\n" (← evalLines "#deploy" t))
  | _ => throwUnsupportedSyntax

end Solidity.Tools
