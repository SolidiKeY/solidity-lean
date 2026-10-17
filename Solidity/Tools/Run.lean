import Solidity.Tools.Common
import Solidity.Semantics.Run
import Solidity.Semantics.Deploy

/-!
# `#run`: call a contract's function in the typed run

```
#run CallsExample.addTwo(3)
#run Coin.mint(1, 5) with msg.sender := 7
#run Counter.dec() with count := 2
#run Counter.dec() from (State.init Counter)
```

The identifier names the contract and the function: its last component is
the function, the rest a `Contract` constant.  The arguments are `sol{ … }`
expressions, typed against the parameters (`-1` at an `int` parameter).
`from σ` gives the state the call starts in (a typed `State C []`: its
storage, heap, ledger, funds and transaction); without it the contract
starts fresh, every root at its default (`State.init`), with no funds.  `with` sets the transaction, a comma-separated list of
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
(`Prog.run`, `Semantics/Run.lean`) from the start state; a `with` word out
of its type's range is an error.
`DiffTest.lean` builds its calls the same way, but a call of several returns
as the bare `f(a, b);`, whose returns the inlined body declares.

The output is `ok`, the value returned, and the storage one root per line
(`fmtStorage`, of the typed storage); or `revert`, or `panic`.  A loop runs
by iterating it (`TLoop.runImpl'`), so a call that never ends does not
return.

```
#deploy Mini(7) with msg.sender := 3
```

`#deploy C(args)` deploys `C` by `Contract.deployT` (`Semantics/Deploy.lean`,
what the constructor obligation is read at): it runs `constructor(args);`
(`ctorProgS`, the initializers and the constructor's body) from the
deployment's typed state (`State.deploy`), whose ledger and funds hold what
`msg.value := n` sends; `with` takes the transaction's fields only.  The
output is `ok`, the funds, and the storage; or how it halted.
-/

namespace Solidity.Tools

open Semantics (lookupBy)

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
def freshState (C : Contract) (tx : TTx := {}) (balance : PrimTy.uint.Denote := PrimTy.dflt .uint) :
    State C [] :=
  { State.init C with selfBalance := balance, tx }

/-- `StandardExample` fresh, with funds (`address(this).balance`) for the
examples' transfers to read. -/
def _root_.Solidity.State.exampleStore : State StandardExample [] :=
  freshState StandardExample (balance := PrimTy.ofIntD .uint 1000000000)

/-- `TestSuite` fresh, with funds like `State.exampleStore`. -/
def _root_.Solidity.State.testSuiteStore : State TestSuite [] :=
  freshState TestSuite (balance := PrimTy.ofIntD .uint 1000000000)

/-- An integer read at the type `p`, or the error `#run` reports. -/
def ofIntE (p : PrimTy) (n : Int) : Except String p.Denote :=
  match PrimTy.ofInt? p n with
  | some v => pure v
  | none => throw "the start state is not of the contract's types"

/-- `σ` with the transaction fields given replaced; an error where one is
not a `uint`. -/
def State.withTx {C : Contract} (σ : State C []) (sender value time balance : Option Int) :
    Except String (State C []) := do
  let w (n : Option Int) (d : PrimTy.uint.Denote) := match n with
    | some n => ofIntE .uint n
    | none => pure d
  pure { σ with
    tx := { σ.tx with msgSender := ← w sender σ.tx.msgSender, msgValue := ← w value σ.tx.msgValue,
                      timestamp := ← w time σ.tx.timestamp }
    selfBalance := ← w balance σ.selfBalance }

/-- `σ` with the state variable `r`, of a value type, set to `v`; an error
where `r` is no such variable or `v` not of its type. -/
def State.withRoot {C : Contract} (σ : State C []) (r : Name) (v : Semantics.CallValue) :
    Except String (State C []) :=
  match h : lookupBy r C.vars with
  | some (.prim p) => match v.as? p with
    | some y => pure { σ with storage := SFields.set (σ.storage : SFields C.vars) h (.prim y) }
    | none => throw "the start state is not of the contract's types"
  | some T => throw s!"{r} is a {Ty.toStr T}, not a value type"
  | none => throw s!"{r} is not a state variable"

/-- A state variable's integer given to `#run`, read at its type `p`. -/
def rootInt (r : Name) (p : PrimTy) (n : Int) : Except String (Name × Semantics.CallValue) :=
  return (r, .ofTyped (← ofIntE p n))

/-- `σ` with the state variables given replaced, in order. -/
def State.withRoots {C : Contract} (σ : State C []) (roots : List (Name × Semantics.CallValue)) :
    Except String (State C []) :=
  roots.foldlM (fun σ (r, v) => State.withRoot σ r v) σ

/-- **A scoped block run from a typed state**, in the typed run: `P` run
by `Prog.run` from `σ`, its end state or how it halted. -/
def _root_.Solidity.Prog.runT {C : Contract} {Γ' : Ctx} (σ : State C []) (P : Prog C [] Γ') :
    TRes (State C Γ') :=
  (Prog.run σ P).map (·.st)

/-- The locals of a typed environment, innermost first: each one's level at
base `0` (`Evm.lvl`), and its type and value if it is a value local. -/
def localCells {C : Contract} {H : HTy} : (Γ : Ctx) → TEnv C H Γ →
    List (Nat × Option ((p : PrimTy) × p.Denote))
  | [], _ => []
  | t :: Γ, e =>
    (match t, e.1 with
      | .val p, v => (Γ.length, some ⟨p, v⟩)
      | _, _ => (Γ.length, none)) :: localCells Γ e.2

/-- The value locals of a typed environment, by the names of its context. -/
def localVals {C : Contract} {H : HTy} {Γ : Ctx} (names : List Var)
    (e : TEnv C H Γ) : List (Var × Semantics.CallValue) :=
  (names.zip (localCells Γ e)).filterMap fun (x, _, c) => c.map fun v => (x, .ofTyped v.2)

/-- What the value local `x` holds after `P` runs from `σ` (`Prog.runT`):
`none` where the end state has no value local of that name. -/
def _root_.Solidity.Prog.localAfterT [FreshNames] {C : Contract} {Γ' : Ctx} (σ : State C [])
    (P : Prog C [] Γ') (x : String) : TRes (Option Semantics.CallValue) := do
  let τ ← Prog.runT σ P
  pure (lookupBy (Var.ofName x) (localVals (P.outNames []) τ.env))

/-- What `#run` prints: the outcome, the value returned, the storage. -/
def runReport [FreshNames] (C : Contract) (σ : State C []) (f : String) (args : List RawExpr) :
    Except String (List String) := do
  let ⟨_, Q⟩ ← elabProgS C [← runStmt C f args]
  let n : Nat := ((lookupBy f C.funs).map (·.rets.length)).getD 0
  pure <| match Prog.run σ Q with
    | .error h => [fmtHalt h]
    | .ok o =>
      let vals := localVals (Q.outNames []) o.st.env
      let ret := if n ≥ 2 then
          let vs := (List.range n).filterMap fun i => lookupBy (Var.ofName s!"{retLocal}{i}") vals
          [s!"returns ({", ".intercalate (vs.map CallValue.fmt)})"]
        else match lookupBy (Var.ofName retLocal) vals with
          | some v => [s!"returns {CallValue.fmt v}"]
          | none => []
      ["ok"] ++ ret ++ fmtStorage C o.st.storage

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
        | some (.prim .bool) =>
          roots := roots.push (← `(pure ($(quote n), Solidity.Semantics.CallValue.bool ($v : Bool))))
        | some (.prim .uint) => roots := roots.push (← `(Solidity.Tools.rootInt $(quote n) .uint ($v : Int)))
        | some (.prim .int) => roots := roots.push (← `(Solidity.Tools.rootInt $(quote n) .int ($v : Int)))
        | some T => throwErrorAt k "#run: {n} is a {Ty.toStr T}: give it with `from`"
        | none => throwErrorAt k "#run: {n} is not one of msg.sender, msg.value, \
            block.timestamp, balance, nor a state variable of {c}"
    let Ct := mkCIdent c
    let σ ← match σ? with
      | some σ => `(($σ : Solidity.State $Ct []))
      | none => `(freshState $Ct)
    let t ← `(do
      let σ ← State.withTx $σ $sender $value $time $bal
      let roots ← ([$roots,*] : List (Except String (Solidity.Name × Solidity.Semantics.CallValue))).mapM id
      let σ ← State.withRoots σ roots
      runReport $Ct σ $(quote f) [$args,*])
    logInfo (String.intercalate "\n" (← evalLines "#run" t))
  | _ => throwUnsupportedSyntax

/-- What `#deploy` prints: the outcome of `Contract.deployT` (a
constructor that is not `payable` refuses value, else `constructor(args);`
runs from `State.deploy`), the contract's funds and its storage. -/
def deployReport [FreshNames] (C : Contract) (args : List RawExpr) (sender value time : Int) :
    Except String (List String) := do
  let ⟨_, Q⟩ ← ctorProgS C args
  let some tx := (do
      pure ({ msgSender := ← PrimTy.ofInt? .uint sender, msgValue := ← PrimTy.ofInt? .uint value,
              timestamp := ← PrimTy.ofInt? .uint time } : TTx))
    | throw "the deployment's start is not of the contract's types"
  pure <| match Contract.deployT C Q tx with
    | .error h => [fmtHalt h]
    | .ok σ => ["ok", s!"balance {σ.selfBalance.1}"] ++ fmtStorage C σ.storage

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
    let t ← `(deployReport $(mkCIdent c) [$args,*] ($sender : Int) ($value : Int) ($time : Int))
    logInfo (String.intercalate "\n" (← evalLines "#deploy" t))
  | _ => throwUnsupportedSyntax

end Solidity.Tools
