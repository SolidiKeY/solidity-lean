import Solidity.Tools.Common
import Solidity.Semantics.Run
import Solidity.Semantics.ToSem
import Solidity.Semantics.TypedErase

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
otherwise — and elaborated scoped by `elabProgS`, which inlines the body
(`Stmt.call`) as for any other call.  The value returned is then the local
`_r` of the final state; of several, `(uint _r0, uint _r1) = f(a, b);` and
the locals `_r0`, `_r1`, … (`runStmt`).  The program is run typed
(`Prog.run`, `Semantics/Run.lean`) from the start state read at the
contract's types (`typedState?`): its storage, ledger, funds and transaction.  A start
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

`#deploy C(args)` deploys `C` in the typed run (`Contract.deployT`'s
reading): it runs `constructor(args);` (`ctorProgS`, the initializers and the
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

/-- The call of `f`, elaborated scoped (`elabProgS`): its body inlined. -/
def callProg [FreshNames] (C : Contract) (f : String) (args : List RawExpr) :
    Except String (Blk C []) := do
  elabProgS C [← callStmt C f args]

/-- The state a contract starts in: every root at its default, no funds, the
transaction `tx`. -/
def freshState (C : Contract) (tx : TxEnv := {}) (balance : Int := 0) : Semantics.State :=
  { storage := C.initStorage, selfBalance := balance, tx }

/-- `σ` with the transaction fields given replaced. -/
def State.withTx (σ : Semantics.State) (sender value time balance : Option Int) : Semantics.State :=
  { σ with
    tx := { msgSender := sender.getD σ.tx.msgSender, msgValue := value.getD σ.tx.msgValue,
            timestamp := time.getD σ.tx.timestamp }
    selfBalance := balance.getD σ.selfBalance }

/-- `σ` with the state variables given replaced. -/
def State.withRoots (σ : Semantics.State) (roots : List (Name × Semantics.SVal)) : Semantics.State :=
  { σ with storage := roots.foldl (fun st (r, v) => setBy r v st) σ.storage }

/-- No locals and no memory: what the typed run's start state has
(`State C []`, its heap empty). -/
def noLocals (σ : Semantics.State) : Bool :=
  σ.env.isEmpty && σ.heap.isEmpty && σ.nextId == 0

/-- A state of no locals and no memory (`none` for any other), read at the contract's types: the
storage (`SFields.ofU`), the funds and the transaction's words as `uint`s,
the ledger as it is; `none` where one is not of its type. -/
def typedState? (C : Contract) (σ : Semantics.State) : Option (State C []) := do
  guard (noLocals σ)
  let st ← SFields.ofU σ.storage C.vars
  let u (n : Int) : Option PrimTy.uint.Denote := PrimTy.ofValue? .uint (.int n)
  let bal ← u σ.selfBalance
  let snd ← u σ.tx.msgSender
  let val ← u σ.tx.msgValue
  let now ← u σ.tx.timestamp
  let addr ← u σ.tx.selfAddress
  let tx : TTx :=
    { msgSender := snd, msgValue := val, timestamp := now, selfAddress := addr, ext := σ.tx.ext }
  pure (State.mk st [] Heap.empty () σ.net bal tx)

/-- **A scoped block run from an untyped state**, in the typed run: `P`
run by `Prog.run` from `σ` read at the contract's types (`typedState?`), and
its end state named back (`State.toSem`, under the block's names) or its
halt erased (`THalt.erase`); `undef` where `σ` is not of the contract's
types, so that no typed run starts. -/
def _root_.Solidity.Prog.runT {C : Contract} {Γ' : Ctx} (σ : Semantics.State) (P : Prog C [] Γ') :
    Res Semantics.State :=
  match typedState? C σ with
  | some τ =>
    match Prog.run τ P with
    | .ok o => .ok (o.st.toSem (P.outNames []))
    | .error h => .error h.erase
  | none => .error .undef

/-- What the local `x` holds after `P` runs from `σ` (`Prog.runT`). -/
def _root_.Solidity.Prog.localAfterT {C : Contract} {Γ' : Ctx} (σ : Semantics.State)
    (P : Prog C [] Γ') (x : String) : Res Binding := do
  (← Prog.runT σ P).getEnv (.user x)

/-- A deployment in the typed run, its end state named back: `#deploy`'s
(`deployReport`), as a value. -/
def _root_.Solidity.Contract.deployRun (C : Contract) {Γ' : Ctx} (P : Prog C [] Γ')
    (tx : TxEnv) : Res Semantics.State :=
  if !((C.ctor.map (·.payable)).getD false) && tx.msgValue != 0 then .error .revert
  else Prog.runT (C.deployState tx) P

/-- The locals of a typed environment, innermost first: each one's level at
base `0` (`Evm.lvl`), and its type and value if it is a value local. -/
def localCells {C : Contract} {H : HTy} : (Γ : Ctx) → TEnv C H Γ →
    List (Nat × Option (PrimTy × Value))
  | [], _ => []
  | t :: Γ, e =>
    (match t, e.1 with
      | .val p, v => (Γ.length, some (p, PrimTy.erase (p := p) v))
      | _, _ => (Γ.length, none)) :: localCells Γ e.2

/-- The value locals of a typed environment, by the names of its context. -/
def localVals {C : Contract} {H : HTy} {Γ : Ctx} (names : List Var)
    (e : TEnv C H Γ) : List (Var × Value) :=
  (names.zip (localCells Γ e)).filterMap fun (x, _, c) => c.map fun (_, v) => (x, v)

/-- What `#run` prints: the outcome, the value returned, the storage. -/
def runReport [FreshNames] (C : Contract) (σ : Semantics.State) (f : String) (args : List RawExpr) :
    Except String (List String) := do
  let ⟨_, Q⟩ ← elabProgS C [← runStmt C f args]
  unless noLocals σ do
    throw "a start state with locals or memory is not supported by the typed run"
  let some τ := typedState? C σ | throw "the start state is not of the contract's types"
  let n : Nat := ((lookupBy f C.funs).map (·.rets.length)).getD 0
  pure <| match Prog.run τ Q with
    | .error h => [fmtHalt h.erase]
    | .ok o =>
      let vals := localVals (Q.outNames []) o.st.env
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
(`Contract.deployT`'s: a constructor that is not `payable` refuses
value, else `constructor(args);` runs from `Contract.deployState`), the
contract's funds and its storage. -/
def deployReport [FreshNames] (C : Contract) (args : List RawExpr) (tx : TxEnv) :
    Except String (List String) := do
  let ⟨_, Q⟩ ← ctorProgS C args
  let some τ := typedState? C (C.deployState tx) | throw "the deployment's start is not of the contract's types"
  if !((C.ctor.map (·.payable)).getD false) && tx.msgValue != 0 then return [fmtHalt .revert]
  pure <| match Prog.run τ Q with
    | .error h => [fmtHalt h.erase]
    | .ok o => ["ok", s!"balance {o.st.selfBalance.1}"] ++ fmtStorage C o.st.storage.erase

/-- `#deploy C(a, b) [with msg.sender := n, msg.value := m, …]`: deploy the
contract `C` in the typed run and print its outcome. -/
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
