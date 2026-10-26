import Solidity.Calculus.Derive
import Solidity.Calculus.CallbackSound
import Solidity.Calculus.WalkSyntax
import Solidity.Calculus.CapturePayments
import Solidity.Calculus.LeafDerive
import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.RuleExists

/-!
# The strategy with callbacks: `sol_derive` and `sol_prove` on `ValidT`

`docs/options.md`, O3.  On a goal `ValidT ts φ`, `ValidC I φ pay` or a
sequent of `ProvesC`, the strategy is a walk of `ProvesC`'s rules, one
`apply` per rule, as `sol_derive`'s walk of `Proves` (`Calculus/Derive.lean`):

* a new premise refuted by the bounded scoped closer: `closeFalse`,
  with the wrapped contradiction checked to contain no callback;
* where nothing in the sequent calls back (`Fml.callsBack pay`), `plain`,
  and one fixed 128-step compiled `Proves` walk from there when closing,
  each ordinary leaf closed with the same invariant-aware closer; a refused
  compiled attempt keeps the structural walk;
* a `transfer`, a `send` or a `try` that hands control to a callee that
  calls back: its callback taclet (`transferWithCallbackBox`,
  `sendWithCallbackBox`, `tryCallWithCallbackBox`; under the diamond
  `sendWithCallbackDiamond`), solkey's goals; a self-call `try`
  `tryCallSelfBox`'s, read with callbacks (`ProvesC.trySelf`, Lean);
* a gas-limited send (`pay` unset): `sendNoCallbackBox`'s or
  `sendNoCallbackDiamond`'s goals (`ProvesC.sendDet`, `ProvesC.sendDetD`); a
  block that calls back: its body (`ProvesC.block`); an internal call, its
  body inlined whatever it returns (`ProvesC.callNone`, `ProvesC.callRets`,
  `ProvesC.callVal`, `ProvesC.callStorage`, `ProvesC.callMem`);
  `assertSimple` (`ProvesC.assert`); a loop by its invariant under the box
  (`ProvesC.invBox`);
* any other statement: the rule `Stmt.step` fires (`ProofTree.ruleAt?`), as
  `Proves` takes it, when the statement hands control to nobody
  (`Stmt.forksIn`); a gas-limited transfer so (`transferNoCallbackBox`);
  a capture whose rest calls back (`ifElseUnfold`, `whileUnwind`, a
  payment's operand) by `ProvesC.capture`, its side condition one of
  `captureLemmas`; a loop at its bound under the box (`ProvesC.loopExit`).

What is left is a leaf: `sol_prove` closes a `Proves` leaf by `sol_leaf`
and `sol_close`, the invariant assumed opened first where that is needed
(`Proves.openInv`), and leaves the rest as goals.  While something in the
sequent calls back, a loop whose body calls back has no diamond rule: it
may diverge (`holdsC_diamond_loop`), so such a goal stays a leaf.

Nothing here is trusted: every step is an `apply` the kernel checks.
-/

namespace Solidity

open Solidity (Modality)

/-- Reconstruct a named rule at its typed `Rule` goal.  The statement fixes
the typed hole and path arguments before the constructor's side conditions
are checked, just as in the rule-existence replay. -/
syntax (name := solCallbackRule) "sol_callback_rule " ident : tactic

open Lean Elab Tactic Meta in
@[tactic solCallbackRule]
def evalSolCallbackRule : Tactic := fun stx => withMainContext do
  let g ← getMainGoal
  let c := stx[1].getId
  let (some (_, r), _) ← RuleExists.leaf (← g.getType) (some c)
    | throwError "sol_callback_rule: {c} does not match this typed rule goal"
  g.assign r
  replaceMainGoal []

/-- The test runner's reading of `sol_prove` (`Frontend/Testing.lean`): it
reports only whether a leaf is left, so the walk stops at the first. -/
register_option sol.prove.stopAtOpen : Bool := {
  defValue := false
  descr := "sol_prove with callbacks: stop at the first leaf left open"
}

/-- Enable the bounded contradiction check at a newly assumed premise.
This only changes the proof search; each pruned branch has an explicit
`ProvesC.closeFalse` derivation. -/
register_option sol.prove.pruneFalse : Bool := {
  defValue := true
  descr := "sol_prove with callbacks: prune contradictory callback-free contexts"
}

/-- Use one bounded compiled walk on ordinary `Proves` residues reached
through the callback calculus's existing `plain` rule. -/
register_option sol.prove.compiledPlain : Bool := {
  defValue := true
  descr := "sol_prove with callbacks: compile ordinary Proves residues before walking them"
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
  -- it). An explicit try calls back too, so avoid an ordinary-proof
  -- attempt on every capture before it: the walk goes on in `ProvesC` (`Calculus/RecursionCallback.lean`)
  let φi ← instantiateMVars φ0
  let noPlain := (φi.find? fun e => e.isConstOf ``Stmt.callRec || e.isConstOf ``Stmt.tryCall || e.isConstOf ``Fml.havoc ||
    e.isConstOf ``Fml.grow).isSome
  let φ ← whnf φ0
  let rest : Array (Array (TSyntax `tactic)) ← match φ.getAppFn.constName? with
    | some ``Fml.havoc => pure #[#[← ap ``ProvesC.havocIntro]]
    | some ``Fml.grow => pure #[#[← ap ``ProvesC.growIntro]]
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
            -- a `catch` of the raw data: a goal per datum (`flatten`)
            pure #[#[← ProofTree.takeApart selfApp (flatten := true)], #[← ProofTree.takeApart app]]
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
        -- A try's ordinary box rule produces branches, which ctorC? does
        -- not translate; its diamond done rule cannot satisfy forksIn=false.
        -- Avoid reducing that discarded rule before the own callback moves.
        let ordinary : Array (Array (TSyntax `tactic)) ←
          if s.isAppOf ``Stmt.tryCall then pure #[] else do
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
                let typed ← `(term| (by sol_callback_rule $(mkIdent r):ident))
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
                  #[← `(tactic| apply $f $typed $rfls*)]] ++ cap)
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
`sol_decide`, else `sol_close` (`sol_spec_close` for a specification's), as
`sol_prove?` tries them (`Derive.leafTacs`), the invariant opened
first where it is assumed: where the invariant is `true` (`inv` unset),
opening it changes nothing, and a failed try costs a closer's run. -/
def closeLeaf (g : MVarId) (inv : Bool) : TacticM (Option (Array String)) := do
  let openT ← `(tactic| refine $(← ProofTree.short ``Proves.openInv) ?_)
  let leaf ← `(tactic| sol_leaf)
  let close ← `(tactic| sol_close)
  let spec ← `(tactic| sol_spec_close)
  let tries : Array (Array (TSyntax `tactic)) :=
    #[#[leaf, ← `(tactic| sol_decide)], #[leaf, close],
      #[← `(tactic| exact $(← ProofTree.short ``Proves.assumeInv))]] ++
    (if inv then #[#[openT, leaf, close]] else #[]) ++
    -- a specification's leaf (`spec[C]{f}`): `sol_spec_close`
    #[#[leaf, spec]] ++
    (if inv then #[#[openT, leaf, spec]] else #[])
  for tacs in tries do
    let s ← saveState
    -- a failed try leaves no error behind (`withoutRecover`)
    let ok ← tryCatchRuntimeEx
      (withCurrHeartbeats do return (← withoutRecover (ProofTree.runOn g tacs)).isEmpty)
      fun _ => pure false
    if ok then return some (← tacs.mapM fun t => (ProofTree.tacLines t : MetaM _)).flatten
    s.restore
  return none

/-- One fixed compiled attempt on an ordinary `Proves` goal. In
particular, this does not turn a `ProvesC` goal into a deterministic goal:
`plain` has already checked the whole sequent has no callback. The same
sequent, context and rule set are passed to `Seq.prove`. The bound is at
most 128 nodes and at most the callback walk's remaining fuel. On success
the caller charges that entire bound; on failure it keeps the original
state and structural walk.

The fixed bound is recorded in the replay, so `sol_derive?` does not repeat
stage selection. Every resulting leaf remains an ordinary scoped sequent,
closed separately by `closeLeaf`, including invariant-aware fallbacks. -/
def compiledPlain (g : MVarId) (steps : Nat) :
    TacticM (Option (List MVarId)) := do
  unless sol.prove.compiledPlain.get (← getOptions) do return none
  if steps == 0 || 128 < steps then return none
  let saved ← saveState
  let result ← tryCatchRuntimeEx (withCurrHeartbeats <| g.withContext do
      let ty ← instantiateMVars (← g.getType)
      let_expr Proves C R Γ₀ Γ H φ := ty | return none
      unless (← whnfR Γ₀).isAppOf ``List.nil do return none
      -- `some steps` is a single stage, never Seq.prove's increasing search.
      some <$> Seq.prove g C R Γ H φ (some steps) (oneCheck := steps))
    fun _ => pure none
  if result.isNone then saved.restore
  return result

/-- Search at most `fuel` context constructors for a contradictory prefix.
A premise is tested before looking below it; every context constructor consumes
one unit. This can find a contradiction before havoc without dropping any
update, binder or earlier assumption from the prefix being checked. -/
def refutePrefix {C : Contract} : Nat → {Γ : Ctx} → Hyps C [] Γ → Bool
  | 0, _, _ => false
  | _ + 1, _, .nil => false
  | n + 1, _, .pre H c => Seq.refuteS H c || refutePrefix n H
  | n + 1, _, .upd H _ _ | n + 1, _, .havoc H | n + 1, _, .all H _ _
  | n + 1, _, .bind H _ _ _ | n + 1, _, .anon H _
  | n + 1, _, .allocAll H _ _ | n + 1, _, .grow H => refutePrefix n H

/-- A checked contradictory prefix proves every continuation under its entire
context. In particular, a prefix update under the diamond must still land:
only the suffix after the contradiction is replaced, by monotonicity. -/
theorem refutePrefix_valid {C : Contract} (fuel : Nat) :
    {Γ : Ctx} → (H : Hyps C [] Γ) → refutePrefix fuel H = true →
      ∀ φ : Fml C Γ, Fml.Valid (H.wrap φ) := by
  induction fuel with
  | zero =>
    intro Γ H h
    simp only [refutePrefix, Bool.false_eq_true] at h
  | succ n ih =>
    intro Γ H h φ
    cases H with
    | nil => simp only [refutePrefix, Bool.false_eq_true] at h
    | pre before c =>
      change (Seq.refuteS before c || refutePrefix n before) = true at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · intro σ
        exact (before.pre c).wrap_mono
          (fun _ hf => (hf trivial).elim) σ
          (Proves.sound (Seq.refuteS_sound (R := .all) before c h) σ)
      · exact ih before h (.imp c φ)
    | upd before m U => exact ih before h (.upd m U φ)
    | havoc before => exact ih before h (.havoc φ)
    | all before x p => exact ih before h (.all x p φ)
    | bind before m x t => exact ih before h (.bind m x t φ)
    | anon before xs => exact ih before h (.anon xs φ)
    | allocAll before x A => exact ih before h (.allocAll x A φ)
    | grow before => exact ih before h (.grow φ)

/-- The checked prefix certificate closes the original ordinary sequent. Its
whole wrapped formula must still be modal-free; the callback bridge separately
checks that the whole wrapped contradiction contains no callbacks. -/
theorem refutePrefix_sound {C : Contract} {R : RuleSet} {Γ : Ctx}
    (fuel : Nat) (H : Hyps C [] Γ) (h : refutePrefix fuel H = true)
    (hm : (H.wrap .ff).modalFree = true) : Proves C R [] H .ff :=
  Proves.closeHolds (refutePrefix_valid fuel H h .ff) hm

/-- Check one fixed prefix certificate directly in the kernel, as
Seq.leafValid/Seq.prove do. All dependent arguments are supplied explicitly;
no tactic elaboration or dependent-context inference is needed to build it.
Every equality is checked synchronously before assigning the final proof. -/
def closePrefixFalse (g : MVarId) (fuel : Nat) : MetaM Unit := g.withContext do
  unless fuel ≤ 8 do throwError "sol_prefix_false: at most eight context layers"
  let ty ← instantiateMVars (← g.getType)
  let_expr ProvesC C I pay Γ₀ Γ H φ := ty
    | throwError "sol_prefix_false: expected a callback sequent"
  unless (← whnfR Γ₀).isAppOf ``List.nil do
    throwError "sol_prefix_false: expected a closed outer scope"
  let probe := mkAppN (mkConst ``refutePrefix) #[C, mkNatLit fuel, Γ, H]
  if probe.hasFVar || probe.hasMVar then
    throwError "sol_prefix_false: the certificate is not closed"
  let hc ← Decide.trueLemma probe
  let ff := mkApp2 (mkConst ``Fml.ff) C Γ
  let wrapped := mkAppN (mkConst ``Hyps.wrap) #[C, Γ₀, Γ, H, ff]
  let mf := mkApp3 (mkConst ``Fml.modalFree) C Γ₀ wrapped
  let hm ← Decide.trueLemma mf
  let callbacks := mkAppN (mkConst ``Fml.callsBack) #[C, pay, Γ₀, wrapped]
  let hnc ← Derive.kernelLemma
    (← mkEq callbacks (mkConst ``Bool.false))
    (← mkEqRefl (mkConst ``Bool.false))
  let contradiction := mkAppN (mkConst ``refutePrefix_sound)
    #[C, mkConst ``RuleSet.all, Γ, mkNatLit fuel, H, hc, hm]
  g.assign (mkAppN (mkConst ``ProvesC.closeFalse)
    #[C, I, pay, Γ₀, Γ, H, φ, contradiction, hnc])

/-- Deterministic replay of the fixed checked certificate; no arithmetic
fallback or tactic search is performed. -/
syntax "sol_prefix_false " num : tactic

elab_rules : tactic
  | `(tactic| sol_prefix_false $n:num) => do
    closePrefixFalse (← getMainGoal) n.getNat
    replaceMainGoal []

/-- Probe a newly assumed premise with one eight-constructor prefix check.
The fixed checker is replayed by a synchronous kernel certificate, retaining
all preceding updates and diamond landing requirements. A refusal or timeout
restores the original elaboration state. -/
def pruneFalse (g : MVarId) : TacticM (Option (Array String)) := do
  unless sol.prove.pruneFalse.get (← getOptions) do return none
  let saved ← saveState
  let result ← tryCatchRuntimeEx (withCurrHeartbeats <| g.withContext do
      let ty ← instantiateMVars (← g.getType)
      let_expr ProvesC C _ _ Γ₀ Γ H _ := ty | return none
      unless (← whnfR Γ₀).isAppOf ``List.nil do return none
      let H ← whnfR H
      unless H.isAppOf ``Hyps.pre do return none
      let probe := mkAppN (mkConst ``refutePrefix) #[C, mkNatLit 8, Γ, H]
      if probe.hasFVar || probe.hasMVar then return none
      let refuted ← unsafe evalExpr Bool (mkConst ``Bool) probe
      unless refuted do return none
      let replay ← `(tactic| sol_prefix_false 8)
      let closed ← Budget.bounded 16384 do
        closePrefixFalse g 8
        return true
      unless closed == some true do return none
      return some (← ProofTree.tacLines replay))
    fun _ => pure none
  if result.isNone then saved.restore
  return result

/-- A catch continuation beginning with an explicit revert under the box
needs none of its failed-self-call premise. Detect just this head statement;
no callee, argument, update or remainder is reduced to choose the move. -/
def revertingConsequent (g : MVarId) : MetaM Bool := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOf ``ProvesC do return false
  let φ ← whnf ty.getAppArgs.back!
  unless φ.isAppOf ``Fml.imp do return false
  let consequent ← whnf φ.getAppArgs.back!
  unless consequent.isAppOf ``Fml.modal do return false
  let args := consequent.getAppArgs
  unless args[args.size - 4]!.isConstOf ``Modality.box do return false
  let P ← whnf args[args.size - 3]!
  unless P.isAppOf ``Prog.cons do return false
  let s ← whnf (P.getArg! (P.getAppNumArgs - 2))
  return s.isAppOf ``Stmt.revert

/-- The walk from the `ProvesC` goal `g`: its script and its leaves, as
`Walk.walk` writes them. -/
partial def walk (fuel : IO.Ref Nat) (leaves : IO.Ref (Array MVarId)) (g : MVarId)
    (close : Bool) (inv : Bool := true) : TacticM (Array String) := do
  if ← stopped leaves then leaves.modify (·.push g); return #[r"sorry"]
  let n ← fuel.get
  if n == 0 then throwError "sol_derive: more than {Derive.fuel} steps"
  fuel.set (n - 1)
  let ty ← instantiateMVars (← g.getType)
  -- A goal of `Proves`, past `plain`: compile this exact ordinary
  -- residue first, with the original structural walk as the fallback.
  if ty.isAppOf ``Proves then
    if close then
      let steps := min 128 (← fuel.get)
      if let some gs ← compiledPlain g steps then
        fuel.modify (· - steps)
        let mut found : List (Lean.Name × Array String) := []
        for leaf in gs do
          let name ← leaf.getTag
          if !(← stopped leaves) then
            if let some lines ← closeLeaf leaf inv then
              found := found ++ [(name, lines)]
              continue
          leaves.modify (·.push leaf)
          found := found ++ [(name, #[r"sorry"])]
        return Derive.replayLines found (some steps)
    let fuel' ← IO.mkRef (← fuel.get)
    let ls ← IO.mkRef #[]
    let s ← saveState
    -- a step that runs out of heartbeats leaves the goal, as a leaf; the
    -- leaves are closed below, each try on its own heartbeats, not within
    -- the walk's
    let some lines ← tryCatchRuntimeEx (some <$> withCurrHeartbeats (Walk.walk fuel' ls g false))
        fun _ => do s.restore; pure none
      | leaves.modify (·.push g); return #[r"sorry"]
    fuel.set (← fuel'.get)
    -- each `sorry` (`· sorry` under a bullet) is the next leaf `Proves`'
    -- walk left: closed here where the invariant assumed closes it, its
    -- lines in the `sorry`'s place
    let mut out : Array String := #[]
    let mut rest := (← ls.get).toList
    for line in lines do
      let t := line.trimLeft
      let bullet := t.startsWith "· "
      if (if bullet then (t.drop 2).trimLeft else t) == r"sorry" then
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
  -- Refute the new assumption before expanding any remaining calls.
  if close then
    if let some lines ← pruneFalse g then return lines
  -- `¬X → ψ`, `X` a program's, where something calls back: `X` proved
  -- instead where the walk closes it (`notLeft`), else the premise hidden
  -- (`hideLeft`), as `Walk.walk` does
  if ← tryCatchRuntimeEx (withCurrHeartbeats (Walk.negModalGoal? g)) fun _ => pure false then
    -- Ordinary call syntax lowers unhandled catches to revert. Proving the
    -- failed-self-call premise by its diamond duplicates the getter's proof
    -- without helping this branch; hide it by the existing structural rule.
    if ← tryCatchRuntimeEx (withCurrHeartbeats (revertingConsequent g)) fun _ => pure false then
      let saved ← saveState
      let hidden ← `(tactic| refine $(← ProofTree.short ``ProvesC.hideLeft) ?_)
      let result ← tryCatchRuntimeEx (do
          let [child] ← withCurrHeartbeats (ProofTree.runOn g #[hidden]) | return none
          let localLeaves ← IO.mkRef #[]
          let lines ← walk fuel localLeaves child close inv
          unless (← localLeaves.get).isEmpty do return none
          return some ((← ProofTree.tacLines hidden) ++ lines))
        fun _ => pure none
      if let some lines := result then return lines
      saved.restore
    -- Even a callback-free residue needs the full closer on the positive
    -- diamond before falling back to its catch continuation. Deferring this
    -- choice through plain can leave the negative modality in a leaf.
    let s ← saveState
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
    let r ← tryCatchRuntimeEx
      (some <$> withCurrHeartbeats (Walk.withStepDepth (ProofTree.runOn g tacs)))
      fun _ => do s.restore; pure none
    if let some gs := r then
      step := some (tacs, gs)
      break
  let some (tacs, gs) := step | leaves.modify (·.push g); return #[r"sorry"]
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
      some <$> `(tactic| refine $(← ProofTree.short ``ProvesC.fmlValid) ?_)
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
