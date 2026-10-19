import Solidity.Calculus.Derive
import Solidity.Calculus.CallbackSound

/-!
# The strategy with callbacks: `sol_derive` and `sol_prove` on `ValidT`

`docs/options.md`, O3.  On a goal `ValidT ts φ`, `ValidC I φ pay` or a
sequent of `ProvesC`, the strategy is a walk of `ProvesC`'s rules, one
`apply` per rule, as `sol_derive`'s walk of `Proves` (`Calculus/Derive.lean`):

* where nothing in the sequent calls back (`Fml.callsBack pay`), `plain`,
  and `Proves`' walk from there;
* a `transfer`, a `send` or a `try` that hands control to a callee that
  calls back: its callback taclet (`transferWithCallbackBox`,
  `sendWithCallbackBox`, `tryCallWithCallbackBox`), solkey's goals;
* a gas-limited send (`pay` unset): `sendNoCallbackBox`'s two goals
  (`ProvesC.sendDet`); a block that calls back: its body (`ProvesC.block`);
  `assertSimple` (`ProvesC.assert`);
* any other statement: the rule `Stmt.step` fires (`ProofTree.ruleAt?`), as
  `Proves` takes it, when the statement hands control to nobody
  (`Stmt.forksIn`).

What is left is a leaf: `sol_prove` closes a `Proves` leaf by `sol_leaf`
and `sol_close`, the invariant assumed opened first where that is needed
(`Proves.openInv`), and leaves the rest as goals.  A loop or an internal call
whose body calls back has no rule of `ProvesC`, and stays a leaf.

Nothing here is trusted: every step is an `apply` the kernel checks.
-/

namespace Solidity

open Solidity (Modality)

namespace CallbackWalk

open Lean Elab Tactic Meta

/-- The `ProvesC` rule of the `Proves` rule `c`, on a statement that hands
control to nobody, and how many `rfl`s its side conditions take. -/
def ctorC? (c : Lean.Name) : Option (Lean.Name × Nat) :=
  [(``Proves.update, (``ProvesC.update, 1)), (``Proves.updates, (``ProvesC.updates, 1)),
   (``Proves.guardedUpdates, (``ProvesC.guardedUpdates, 1)),
   (``Proves.unfold, (``ProvesC.unfold, 2)), (``Proves.bind, (``ProvesC.bind, 2)),
   (``Proves.split, (``ProvesC.split, 0)), (``Proves.done, (``ProvesC.done, 1))].lookup c

/-- The steps that may apply at the `ProvesC` goal `g`, in the order tried. -/
def movesAt (g : MVarId) : MetaM (Array (Array (TSyntax `tactic))) := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let_expr ProvesC _ I _ _ _ H φ0 := ty | return #[]
  let ap (n : Lean.Name) : MetaM (TSyntax `tactic) := do
    `(tactic| apply $(← ProofTree.short n))
  let plain ← `(tactic| refine $(← ProofTree.short ``ProvesC.plain) ?_ $(mkIdent `rfl):ident)
  let φ ← whnf φ0
  let rest : Array (Array (TSyntax `tactic)) ← match φ.getAppFn.constName? with
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
          | some ``Stmt.transfer =>
            pure #[#[← `(tactic| apply $(← ProofTree.short ``ProvesC.callback)
              .$(mkIdent `transferWithCallbackBox):ident)]]
          | some ``Stmt.send =>
            pure #[#[← `(tactic| apply $(← ProofTree.short ``ProvesC.sendDet) $rflT)],
              #[← `(tactic| apply $(← ProofTree.short ``ProvesC.sendDetD) $rflT)],
              #[← `(tactic| apply $(← ProofTree.short ``ProvesC.send)
                .$(mkIdent `sendWithCallbackBox):ident)],
              #[← `(tactic| apply $(← ProofTree.short ``ProvesC.sendD)
                .$(mkIdent `sendWithCallbackDiamond):ident)]]
          | some ``Stmt.tryCall =>
            let app ← `(tactic| apply $(← ProofTree.short ``ProvesC.tryCall)
              .$(mkIdent `tryCallWithCallbackBox):ident)
            pure #[#[← ProofTree.takeApart app]]
          | some ``Stmt.assert => pure #[#[← ap ``ProvesC.assert]]
          | _ => pure #[]
        -- the rule `Stmt.step` fires, on a statement that hands control to nobody
        let k := mkAppN (mkConst ``Hyps.freshC) #[ty.getArg! 0, ty.getArg! 3, ty.getArg! 4, I, H, φ]
        let ordinary : Array (Array (TSyntax `tactic)) ← do
          match ← tryCatchRuntimeEx (ProofTree.ruleAt? k m P) (fun _ => pure none) with
          | some (_, r, _, c) =>
            match ctorC? c with
            | some (cC, n) =>
              let rule := mkIdent (Lean.Name.mkSimple r.getString!)
              let d ← if r.getPrefix == ``Taclet then `(term| (.$(mkIdent `key):ident .$rule:ident))
                else `(term| (.$(mkIdent `lean):ident .$rule:ident))
              let rfls := (List.replicate n rflT).toArray
              let f ← ProofTree.short cC
              pure #[#[← `(tactic| apply $f $d $rfls*)],
                #[← `(tactic| apply $f (by exact $d) $rfls*)]]
            | none => pure #[]
          | none => pure #[]
        let block : Array (Array (TSyntax `tactic)) ←
          if s.isAppOf ``Stmt.block then pure #[#[← ap ``ProvesC.block]] else pure #[]
        pure (own ++ ordinary ++ block)
    | _ => pure #[]
  return #[#[plain]] ++ rest

/-- A `Proves` leaf closed as `sol_prove` closes one: `sol_leaf` and
`sol_close` (`sol_spec_close` for a specification's), the invariant opened
first where it is assumed. -/
def closeLeaf (g : MVarId) : TacticM (Option (Array String)) := do
  let tries : Array (Array (TSyntax `tactic)) := #[
    #[← `(tactic| exact $(← ProofTree.short ``Proves.assumeInv))],
    #[← `(tactic| sol_leaf), ← `(tactic| sol_close)],
    #[← `(tactic| refine $(← ProofTree.short ``Proves.openInv) ?_),
      ← `(tactic| sol_leaf), ← `(tactic| sol_close)],
    -- a specification's leaf (`spec[C]{f}`): `sol_spec_close`
    #[← `(tactic| sol_leaf), ← `(tactic| sol_spec_close)],
    #[← `(tactic| refine $(← ProofTree.short ``Proves.openInv) ?_),
      ← `(tactic| sol_leaf), ← `(tactic| sol_spec_close)]]
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
    (close : Bool) : TacticM (Array String) := do
  let n ← fuel.get
  if n == 0 then throwError "sol_derive: more than {Derive.fuel} steps"
  fuel.set (n - 1)
  let ty ← instantiateMVars (← g.getType)
  -- a goal of `Proves`, past `plain`: `Proves`' walk
  if ty.isAppOf ``Proves then
    let fuel' ← IO.mkRef (← fuel.get)
    let ls ← IO.mkRef #[]
    let lines ← withCurrHeartbeats (Walk.walk fuel' ls g close)
    -- each `sorry` is the next leaf `Proves`' walk left: closed here where
    -- the invariant assumed closes it, its lines in the `sorry`'s place
    let mut out : Array String := #[]
    let mut rest := (← ls.get).toList
    for line in lines do
      if line.trimLeft == "sorry" then
        match rest with
        | l :: rs =>
          rest := rs
          if close then
            if let some cl ← closeLeaf l then
              let pad := "".pushn ' ' (line.length - line.trimLeft.length)
              out := out ++ cl.map (pad ++ ·)
              continue
          leaves.modify (·.push l)
        | [] => pure ()
      out := out.push line
    return out
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
  | [g'] => return head ++ (← walk fuel leaves g' close)
  | gs =>
    let mut out := head
    for g' in gs do
      let body ← walk fuel leaves g' close
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
  let lines ← walk fuel leaves g close
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
