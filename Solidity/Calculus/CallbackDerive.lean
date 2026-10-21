import Solidity.Calculus.Derive
import Solidity.Calculus.CallbackSound
import Solidity.Calculus.WalkSyntax
import Solidity.Calculus.CapturePayments

/-!
# The strategy with callbacks: `sol_derive` and `sol_prove` on `ValidT`

`docs/options.md`, O3.  On a goal `ValidT ts φ`, `ValidC I φ pay` or a
sequent of `ProvesC`, the strategy is a walk of `ProvesC`'s rules, one
`apply` per rule, as `sol_derive`'s walk of `Proves` (`Calculus/Derive.lean`):

* where nothing in the sequent calls back (`Fml.callsBack pay`), `plain`,
  and `Proves`' walk from there;
* a `transfer`, a `send` or a `try` that hands control to a callee that
  calls back: its callback taclet (`transferWithCallbackBox`,
  `sendWithCallbackBox`, `tryCallWithCallbackBox`; under the diamond
  `sendWithCallbackDiamond`), solkey's goals; a self-call `try`
  `tryCallSelfBox`'s, read with callbacks (`ProvesC.trySelf`, Lean);
* a gas-limited send (`pay` unset): `sendNoCallbackBox`'s or
  `sendNoCallbackDiamond`'s goals (`ProvesC.sendDet`, `ProvesC.sendDetD`); a
  block that calls back: its body (`ProvesC.block`); an internal call with no
  value returned or with a tuple's (`ProvesC.callNone`, `ProvesC.callRets`):
  its body inlined; `assertSimple` (`ProvesC.assert`);
* any other statement: the rule `Stmt.step` fires (`ProofTree.ruleAt?`), as
  `Proves` takes it, when the statement hands control to nobody
  (`Stmt.forksIn`); a gas-limited transfer so (`transferNoCallbackBox`);
  a capture whose rest calls back (`ifElseUnfold`, `whileUnwind`, a
  payment's operand) by `ProvesC.capture`, its side condition one of
  `captureLemmas`; a loop at its bound under the box (`ProvesC.loopExit`).

What is left is a leaf: `sol_prove` closes a `Proves` leaf by `sol_leaf`
and `sol_close`, the invariant assumed opened first where that is needed
(`Proves.openInv`), and leaves the rest as goals.  While something in the
sequent calls back, these shapes have no rule of `ProvesC` and stay leaves:
a loop by its invariant (`Proves.inv` has no counterpart), a loop at its
bound under the diamond, and an internal call that returns one value
(`y = f(x)`) or a memory or storage one (`Stmt.forksIn` counts every call
as forking).

Nothing here is trusted: every step is an `apply` the kernel checks.
-/

namespace Solidity

open Solidity (Modality)

/-- The test runner's reading of `sol_prove` (`Frontend/Testing.lean`): it
reports only whether a leaf is left, so the walk stops at the first. -/
register_option sol.prove.stopAtOpen : Bool := {
  defValue := false
  descr := "sol_prove with callbacks: stop at the first leaf left open"
}

namespace CallbackWalk

open Lean Elab Tactic Meta

/-- A leaf is left and the walk stops there (`sol.prove.stopAtOpen`): the
rest is left unwalked. -/
def stopped (leaves : IO.Ref (Array MVarId)) : TacticM Bool := do
  return sol.prove.stopAtOpen.get (← getOptions) && !(← leaves.get).isEmpty

/-- The `ProvesC` rule of the `Proves` rule `c`, on a statement that hands
control to nobody, and how many `rfl`s its side conditions take. -/
def ctorC? (c : Lean.Name) : Option (Lean.Name × Nat) :=
  [(``Proves.update, (``ProvesC.update, 1)), (``Proves.updates, (``ProvesC.updates, 1)),
   (``Proves.guardedUpdates, (``ProvesC.guardedUpdates, 1)),
   (``Proves.unfold, (``ProvesC.unfold, 2)), (``Proves.bind, (``ProvesC.bind, 2)),
   (``Proves.split, (``ProvesC.split, 0)), (``Proves.done, (``ProvesC.done, 1))].lookup c

/-- The captures whose rest may call back (`Semantics/CallbackCapture.lean`),
each `ProvesC.capture`'s side condition: `Stmt.CapturesAs.<name>`.
Each with the number of `rfl`s its own side conditions take. -/
def captureLemmas : Array (Lean.Name × Nat) :=
  #[(`ite, 0), (`loop, 1), (`transferAmt, 1), (`transferRecv, 1), (`sendAmt, 1), (`sendRecv, 1)]

/-- The steps that may apply at the `ProvesC` goal `g`, in the order tried. -/
def movesAt (g : MVarId) : MetaM (Array (Array (TSyntax `tactic))) := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let_expr ProvesC _ I _ _ _ H φ0 := ty | return #[]
  let ap (n : Lean.Name) : MetaM (TSyntax `tactic) := do
    `(tactic| apply $(← ProofTree.short n))
  let plain ← `(tactic| refine $(← ProofTree.short ``ProvesC.plain) ?_ $(mkIdent `rfl):ident)
  -- not `plain` on a recursive call (no rule of `Proves` steps over it, and
  -- `rfl` would unroll its frames) or a `{havoc}` (`Proves` has no rule for
  -- it): the walk goes on in `ProvesC` (`Calculus/RecursionCallback.lean`)
  let φi ← instantiateMVars φ0
  let noPlain := (φi.find? fun e => e.isConstOf ``Stmt.callRec || e.isConstOf ``Fml.havoc).isSome
  let φ ← whnf φ0
  let rest : Array (Array (TSyntax `tactic)) ← match φ.getAppFn.constName? with
    | some ``Fml.havoc => pure #[#[← ap ``ProvesC.havocIntro]]
    | some ``Fml.imp => pure #[#[← ap ``ProvesC.intro]]
    | some ``Fml.all => pure #[#[← ap ``ProvesC.allIntro]]
    | some ``Fml.upd => pure #[#[← ap ``ProvesC.updIntro]]
    | some ``Fml.bind => pure #[#[← ap ``ProvesC.bindIntro]]
    | some ``Fml.modal =>
      let args := φ.getAppArgs
      let m := args[args.size - 4]!
      let P ← whnf args[args.size - 3]!
      if P.isAppOf ``Prog.nil then pure #[#[← ap ``ProvesC.empty]]
      else
        let s ← whnf (P.getArg! (P.getAppNumArgs - 2))
        let rflT : Lean.Term := ⟨mkIdent `rfl⟩
        -- the callback taclets, a gas-limited send, `assertSimple`, a block
        let own : Array (Array (TSyntax `tactic)) ← match s.getAppFn.constName? with
          | some ``Stmt.send =>
            pure #[#[← `(tactic| apply $(← ProofTree.short ``ProvesC.sendDet) $rflT)],
              #[← `(tactic| apply $(← ProofTree.short ``ProvesC.sendDetD) $rflT)],
              #[← `(tactic| apply $(← ProofTree.short ``ProvesC.send)
                .$(mkIdent `sendWithCallbackBox):ident)],
              #[← `(tactic| apply $(← ProofTree.short ``ProvesC.sendD)
                .$(mkIdent `sendWithCallbackDiamond):ident)]]
          | some ``Stmt.tryCall =>
            -- a self-call (`self = true`): `tryCallSelfBox`'s goals with callbacks
            let selfApp ← `(tactic| apply $(← ProofTree.short ``ProvesC.trySelf)
              .$(mkIdent `tryCallSelfBox):ident)
            let app ← `(tactic| apply $(← ProofTree.short ``ProvesC.tryCall)
              .$(mkIdent `tryCallWithCallbackBox):ident)
            pure #[#[← ProofTree.takeApart selfApp], #[← ProofTree.takeApart app]]
          | some ``Stmt.assert => pure #[#[← ap ``ProvesC.assert]]
          -- a loop at its unwinding bound, under the box (`loopExit`)
          -- a loop by its invariant, under the box (`whileInvariantBox`)
          | some ``Stmt.loop => pure #[#[← ap ``ProvesC.loopExit],
              #[← `(tactic| apply $(← ProofTree.short ``ProvesC.invBox) $rflT)]]
          | some ``Stmt.call => pure #[#[← ap ``ProvesC.callNone], #[← ap ``ProvesC.callRets],
              #[← ap ``ProvesC.callVal], #[← ap ``ProvesC.callStorage], #[← ap ``ProvesC.callMem]]
          | _ => pure #[]
        -- the rule `Stmt.step` fires, on a statement that hands control to nobody
        let k := mkAppN (mkConst ``Hyps.freshC) #[ty.getArg! 0, ty.getArg! 3, ty.getArg! 4, I, H, φ]
        let ordinary : Array (Array (TSyntax `tactic)) ← do
          match ← tryCatchRuntimeEx (ProofTree.ruleAt? k m P) (fun _ => pure none) with
          | some (_, r, _, c) =>
            match ctorC? c with
            | some (cC, n) =>
              let rule := mkIdent (Lean.Name.mkSimple r.getString!)
              -- `whileUnwind`'s mode is read off the loop (`core_while_unwind`)
              let d ← if r == ``Taclet.whileUnwind then
                  `(term| (.$(mkIdent `key):ident (by core_while_unwind)))
                else if r.getPrefix == ``Taclet then `(term| (.$(mkIdent `key):ident .$rule:ident))
                else `(term| (.$(mkIdent `lean):ident .$rule:ident))
              let rfls := (List.replicate n rflT).toArray
              let f ← ProofTree.short cC
              -- a capture whose rest calls back: `ProvesC.capture`, its
              -- side condition the capture's lemma (`Stmt.CapturesAs`)
              let cap ← if c == ``Proves.unfold then
                  captureLemmas.mapM fun (l, k) => do
                    let fc ← ProofTree.short ``ProvesC.capture
                    if k == 0 then pure #[← `(tactic| apply $fc $d .$(mkIdent l):ident)]
                    else
                      let rs := (List.replicate k rflT).toArray
                      pure #[← `(tactic| apply $fc $d (.$(mkIdent l):ident $rs*))]
                else pure #[]
              pure (#[#[← `(tactic| apply $f $d $rfls*)],
                #[← `(tactic| apply $f (by exact $d) $rfls*)]] ++ cap)
            | none => pure #[]
          | none => pure #[]
        -- a transfer calls back only where `pay` is set: `transferNoCallbackBox`
        -- (`ordinary`) first, which fires where it does not
        let after : Array (Array (TSyntax `tactic)) ← match s.getAppFn.constName? with
          | some ``Stmt.transfer =>
            pure #[#[← `(tactic| apply $(← ProofTree.short ``ProvesC.callback)
              .$(mkIdent `transferWithCallbackBox):ident)]]
          | some ``Stmt.block => pure #[#[← ap ``ProvesC.block]]
          | _ => pure #[]
        pure (own ++ ordinary ++ after)
    | _ => pure #[]
  return (if noPlain then #[] else #[#[plain]]) ++ rest

/-- A `Proves` leaf closed as `sol_prove` closes one: `sol_leaf` and
`sol_close` (`sol_spec_close` for a specification's), the invariant opened
first where it is assumed: where the invariant is `true` (`inv` unset),
opening it changes nothing, and a failed try costs a closer's run. -/
def closeLeaf (g : MVarId) (inv : Bool) : TacticM (Option (Array String)) := do
  let openT ← `(tactic| refine $(← ProofTree.short ``Proves.openInv) ?_)
  let leaf ← `(tactic| sol_leaf)
  let close ← `(tactic| sol_close)
  let spec ← `(tactic| sol_spec_close)
  let tries : Array (Array (TSyntax `tactic)) :=
    #[#[leaf, close], #[← `(tactic| exact $(← ProofTree.short ``Proves.assumeInv))]] ++
    (if inv then #[#[openT, leaf, close]] else #[]) ++
    -- a specification's leaf (`spec[C]{f}`): `sol_spec_close`
    #[#[leaf, spec]] ++
    (if inv then #[#[openT, leaf, spec]] else #[])
  for tacs in tries do
    let s ← saveState
    let ok ← tryCatchRuntimeEx
      (withCurrHeartbeats do return (← ProofTree.runOn g tacs).isEmpty) fun _ => pure false
    if ok then return some (← tacs.mapM fun t => (ProofTree.tacLines t : MetaM _)).flatten
    s.restore
  return none

/-- The walk from the `ProvesC` goal `g`: its script and its leaves, as
`Walk.walk` writes them. -/
partial def walk (fuel : IO.Ref Nat) (leaves : IO.Ref (Array MVarId)) (g : MVarId)
    (close : Bool) (inv : Bool := true) : TacticM (Array String) := do
  if ← stopped leaves then leaves.modify (·.push g); return #["sorry"]
  let n ← fuel.get
  if n == 0 then throwError "sol_derive: more than {Derive.fuel} steps"
  fuel.set (n - 1)
  let ty ← instantiateMVars (← g.getType)
  -- a goal of `Proves`, past `plain`: `Proves`' walk
  if ty.isAppOf ``Proves then
    let fuel' ← IO.mkRef (← fuel.get)
    let ls ← IO.mkRef #[]
    let s ← saveState
    -- a step that runs out of heartbeats leaves the goal, as a leaf; the
    -- leaves are closed below, each try on its own heartbeats, not within
    -- the walk's
    let some lines ← tryCatchRuntimeEx (some <$> withCurrHeartbeats (Walk.walk fuel' ls g false))
        fun _ => do s.restore; pure none
      | leaves.modify (·.push g); return #["sorry"]
    fuel.set (← fuel'.get)
    -- each `sorry` (`· sorry` under a bullet) is the next leaf `Proves`'
    -- walk left: closed here where the invariant assumed closes it, its
    -- lines in the `sorry`'s place
    let mut out : Array String := #[]
    let mut rest := (← ls.get).toList
    for line in lines do
      let t := line.trimLeft
      let bullet := t.startsWith "· "
      if (if bullet then (t.drop 2).trimLeft else t) == "sorry" then
        match rest with
        | l :: rs =>
          rest := rs
          if close && !(← stopped leaves) then
            if let some cl ← closeLeaf l inv then
              let pad := "".pushn ' ' (line.length - t.length)
              out := out ++ cl.mapIdx fun i c =>
                pad ++ (if bullet then (if i == 0 then "· " else "  ") else "") ++ c
              continue
          leaves.modify (·.push l)
        | [] => pure ()
      out := out.push line
    return out
  -- `¬X → ψ`, `X` a program's, where something calls back: `X` proved
  -- instead where the walk closes it (`notLeft`), else the premise hidden
  -- (`hideLeft`), as `Walk.walk` does
  if ← tryCatchRuntimeEx (withCurrHeartbeats (Walk.negModalGoal? g)) fun _ => pure false then
    let s ← saveState
    let pl ← `(tactic| refine $(← ProofTree.short ``ProvesC.plain) ?_ $(mkIdent `rfl):ident)
    let viaPlain ← tryCatchRuntimeEx
      (withCurrHeartbeats do return (← ProofTree.runOn g #[pl]).length == 1)
      fun _ => pure false
    s.restore
    unless viaPlain do
      let nl ← `(tactic| refine $(← ProofTree.short ``ProvesC.notLeft) ?_)
      let r ← tryCatchRuntimeEx (do
          let [gx] ← withCurrHeartbeats (ProofTree.runOn g #[nl]) | return none
          let ls ← IO.mkRef #[]
          let lines ← walk fuel ls gx true inv
          return if (← ls.get).isEmpty then some lines else none)
        fun _ => pure none
      if let some lines := r then return (← ProofTree.tacLines nl) ++ lines
      s.restore
      let hl ← `(tactic| refine $(← ProofTree.short ``ProvesC.hideLeft) ?_)
      let [g'] ← withCurrHeartbeats (ProofTree.runOn g #[hl])
        | throwError "sol_derive: hideLeft failed"
      return (← ProofTree.tacLines hl) ++ (← walk fuel leaves g' close inv)
  let mut step := none
  let moves ← tryCatchRuntimeEx (withCurrHeartbeats (movesAt g)) fun _ => pure #[]
  for tacs in moves do
    let s ← saveState
    let r ← tryCatchRuntimeEx (some <$> withCurrHeartbeats (ProofTree.runOn g tacs))
      fun _ => do s.restore; pure none
    if let some gs := r then
      step := some (tacs, gs)
      break
  let some (tacs, gs) := step | leaves.modify (·.push g); return #["sorry"]
  let head := (← tacs.mapM fun t => (ProofTree.tacLines t : MetaM _)).flatten
  match gs with
  | [g'] => return head ++ (← walk fuel leaves g' close inv)
  | gs =>
    let mut out := head
    for g' in gs do
      let body ← walk fuel leaves g' close inv
      out := out ++ body.mapIdx fun i l => (if i == 0 then "· " else "  ") ++ l
    return out

/-- `ValidT ts φ` or `ValidC I φ pay` as a goal of `ProvesC`, the semantics'
invariant and flag read off. -/
def start (g : MVarId) : TacticM (Option (Array String × MVarId)) := do
  let ty ← instantiateMVars (← g.getType)
  let t? : Option (TSyntax `tactic) ←
    if ty.isAppOf ``ValidT then
      some <$> `(tactic| refine $(← ProofTree.short ``ProvesC.validT) ?_)
    else if ty.isAppOf ``ValidC then
      some <$> `(tactic| refine $(← ProofTree.short ``ProvesC.valid) ?_)
    else if ty.isAppOf ``ProvesC then pure none
    else return none
  let (pre, g) ← match t? with
    | some t =>
      let [g'] ← ProofTree.runOn g #[t] | throwError "sol_derive: the start failed"
      pure (← ProofTree.tacLines t, g')
    | none => pure (#[], g)
  -- the transfer semantics' invariant and flag, as the rules read them
  let red ← `(tactic| try simp only
      [$(← ProofTree.short ``TransferSem.inv):ident, $(← ProofTree.short ``TransferSem.pay):ident])
  let [g] ← ProofTree.runOn g #[red]
    | throwError "sol_derive: the transfer semantics did not reduce"
  let redLines ← ProofTree.tacLines red
  let pre := if ty.isAppOf ``ValidT then pre ++ redLines else pre
  return some (pre, g)

/-- The walk from a callback goal: its lines and its leaves, or none for
another goal. -/
def run (g : MVarId) (close : Bool) : TacticM (Option (Array String × List MVarId)) := do
  let some (pre, g) ← start g | return none
  let fuel ← IO.mkRef Derive.fuel
  let leaves ← IO.mkRef #[]
  -- an invariant `true` (`noCallback`'s default): opening it changes nothing
  let ty ← instantiateMVars (← g.getType)
  let inv ← match_expr ty with
    | ProvesC _ I _ _ _ _ _ => pure !(← whnf I).isAppOf ``Fml.tt
    | _ => pure true
  let lines ← walk fuel leaves g close inv
  return some (pre ++ lines, (← leaves.get).toList)

end CallbackWalk

/-- `sol_derive` on a goal with callbacks, the expansion of `sol_derive`
tried first (as `sol_derive_scoped` is, `Calculus/Derive.lean`). -/
syntax (name := solDeriveCallback) "sol_derive_callback" : tactic

macro_rules | `(tactic| sol_derive) => `(tactic| sol_derive_callback)

open Lean Elab Tactic Meta in
/-- `sol_derive` on a goal with callbacks (`ValidT`, `ValidC`, `ProvesC`):
the walk of `ProvesC`, leaving its leaves. -/
@[tactic solDeriveCallback]
def evalSolDeriveCallback : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let rest := (← getUnsolvedGoals).erase g
  let some (_, leaves) ← CallbackWalk.run g false
    | throwError "sol_derive_callback: not a goal with callbacks"
  setGoals (leaves ++ rest)

open Lean Elab Tactic Meta in
/-- `sol_prove` on a goal with callbacks: the walk, each `Proves` leaf
closed where `sol_leaf` and `sol_close` close it. -/
@[tactic Solidity.tacticSol_prove]
def evalSolProveCallback : Tactic := fun stx => withMainContext do
  unless stx[1].isNone do throwUnsupportedSyntax
  let g ← getMainGoal
  let rest := (← getUnsolvedGoals).erase g
  let some (_, leaves) ← CallbackWalk.run g true | throwUnsupportedSyntax
  setGoals (leaves ++ rest)

open Lean Elab Tactic Meta in
/-- `sol_derive?` on a goal with callbacks: the walk, offered as its script. -/
@[tactic Solidity.ProofTree.tacticSol_derive?]
def evalSolDeriveQCallback : Tactic := fun stx => withMainContext do
  let g ← getMainGoal
  let rest := (← getUnsolvedGoals).erase g
  let some (lines, leaves) ← CallbackWalk.run g true | throwUnsupportedSyntax
  setGoals (leaves ++ rest)
  ProofTree.suggest stx[0] lines

end Solidity
