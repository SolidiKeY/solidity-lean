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

/-- Internal Testing policy: retain exact residue and scoped-closer certificates
as typed proof checkpoints for the final synchronous check. Ordinary callers check now. -/
register_option sol.prove.sharedResidues : Bool := {
  defValue := false
  descr := "Testing: share the final kernel context for exact ordinary certificates"
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
  #[(`ite, 0), (`loopAnnotation, 0), (`loop, 1), (`transferAmt, 1), (`transferRecv, 1), (`sendAmt, 1), (`sendRecv, 1)]

/-- Only an existing normality antecedent for the same simple transfer
bypasses the generic negative-modality fallback. No antecedent is inserted. -/
def isTransferNormality (φ : Expr) : MetaM Bool := do
  let φ ← whnf φ
  unless φ.isAppOf ``Fml.imp do return false
  let a ← whnf (φ.getArg! 2)
  let b ← whnf φ.appArg!
  unless a.isAppOf ``Fml.not && b.isAppOf ``Fml.modal do return false
  let n ← whnf a.appArg!
  unless n.isAppOf ``Fml.modal do return false
  let na := n.getAppArgs
  let ba := b.getAppArgs
  unless na[na.size - 4]!.isConstOf ``Modality.box &&
      ba[ba.size - 4]!.isConstOf ``Modality.diamond do return false
  let np ← whnf na[na.size - 3]!
  let bp ← whnf ba[ba.size - 3]!
  unless np.isAppOf ``Prog.cons && bp.isAppOf ``Prog.cons do return false
  let tail ← whnf np.appArg!
  let frames ← whnf na[na.size - 2]!
  let post ← whnf na.back!
  unless tail.isAppOf ``Prog.nil && frames.isAppOf ``Frames.nil &&
      post.isAppOf ``Fml.not do return false
  unless (← whnf post.appArg!).isAppOf ``Fml.tt do return false
  let ns ← whnf (np.getArg! (np.getAppNumArgs - 2))
  let bs ← whnf (bp.getArg! (bp.getAppNumArgs - 2))
  unless ns.isAppOf ``Stmt.transfer && bs.isAppOf ``Stmt.transfer do return false
  unless (ns.getArg! (ns.getAppNumArgs - 2)).isAppOf ``Val.simple &&
      ns.appArg!.isAppOf ``Val.simple do return false
  isDefEq ns bs

/-- The exact guarded transfer at the current callback sequent. -/
def hasTransferNormality (g : MVarId) : MetaM Bool := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let_expr ProvesC _ _ _ _ _ _ φ := ty | return false
  isTransferNormality φ

/-- Keep the callback judgement through structural prefixes leading to a
normality guard; the ordinary transfer diamond has no unconditional rule. -/
partial def containsTransferNormality (φ : Expr) : MetaM Bool := do
  let φ ← whnf φ
  if ← isTransferNormality φ then return true
  if [``Fml.imp, ``Fml.all, ``Fml.bind, ``Fml.upd, ``Fml.havoc,
      ``Fml.grow, ``Fml.anon, ``Fml.allocAll].any φ.isAppOf then
    containsTransferNormality φ.appArg!
  else return false

/-- `φ` without what it never reads: a loop body's end with no break test,
`Fml.invPost m hu ω κ φ post B` with `B` reducing to `none`, is `post`
alone (`Fml.invPost`), the rest of the program `⟨ ω κ ⟩ φ` after the loop
unread. Only the first such end is looked at; a break test there keeps the
whole formula. -/
partial def liveFml (φ : Expr) : MetaM Expr := do
  let some e := φ.find? fun e => e.isAppOf ``Fml.invPost && e.getAppNumArgs == 12 | return φ
  if e.appArg!.hasLooseBVars then return φ
  unless (← whnf e.appArg!).isAppOf ``Option.none do return φ
  liveFml (φ.replace fun x => if x == e then some e.appFn!.appArg! else none)

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
  -- attempt on every capture before it: the walk goes on in `ProvesC` (`Calculus/RecursionCallback.lean`).
  -- A `try` only in a loop body's unread continuation (`liveFml`) does not count
  let φi ← instantiateMVars φ0
  let containsGuard ← containsTransferNormality φi
  let φs ← liveFml φi
  let noPlain := containsGuard || (φs.find? fun e => e.isConstOf ``Stmt.callRec || e.isConstOf ``Stmt.tryCall || e.isConstOf ``Fml.havoc ||
    e.isConstOf ``Fml.grow).isSome
  let φ ← whnf φ0
  let rest : Array (Array (TSyntax `tactic)) ← match φ.getAppFn.constName? with
    | some ``Fml.havoc => pure #[#[← ap ``ProvesC.havocIntro]]
    | some ``Fml.grow => pure #[#[← ap ``ProvesC.growIntro]]
    | some ``Fml.imp => pure #[
        #[← `(tactic| apply $(← ProofTree.short ``ProvesC.transferDetD) $(mkIdent `rfl):ident)],
        #[← `(tactic| apply $(← ProofTree.short ``ProvesC.transferD) $(mkIdent `rfl):ident)],
        #[← ap ``ProvesC.intro]]
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
  let ordinary := if noPlain then #[] else #[#[plain]]
  return if ← hasTransferNormality g then rest ++ ordinary else ordinary ++ rest

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
      some <$> Seq.prove g C R Γ H φ (some steps) (oneCheck := steps)
        (shareCheck := sol.prove.sharedResidues.get (← getOptions)))
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

/-- Untrusted proposal of the first winning prefix, under the SAME depth
bound as refutePrefix. Every constructor consumes one unit. -/
private def refutingDepth {C : Contract} : Nat → {Γ : Ctx} → Hyps C [] Γ → Option Nat
  | 0, _, _ => none
  | _ + 1, _, .nil => none
  | n + 1, _, .pre H c =>
      if Seq.refuteS H c then some 0 else (refutingDepth n H).map Nat.succ
  | n + 1, _, .upd H _ _ | n + 1, _, .havoc H | n + 1, _, .all H _ _
  | n + 1, _, .bind H _ _ _ | n + 1, _, .anon H _
  | n + 1, _, .allocAll H _ _ | n + 1, _, .grow H =>
      (refutingDepth n H).map Nat.succ

private def prefixProbe {C : Contract} (fuel : Nat) {Γ : Ctx}
    (H : Hyps C [] Γ) : Bool × Option Nat :=
  let eligible := refutePrefix fuel H
  (eligible, if eligible then refutingDepth fuel H else none)

private theorem refutePrefix_head {C : Contract} {Γ : Ctx} (n : Nat)
    (H : Hyps C [] Γ) (c : Fml C Γ) (h : Seq.refuteS H c = true) :
    refutePrefix (n + 1) (H.pre c) = true := by
  simp only [refutePrefix, h, Bool.true_or]

private theorem refutePrefix_tail {C : Contract} {Γ : Ctx} (n : Nat)
    (H : Hyps C [] Γ) (c : Fml C Γ) (h : refutePrefix n H = true) :
    refutePrefix (n + 1) (H.pre c) = true := by
  simp only [refutePrefix, h, Bool.or_true]

open Decide in
private def prefixReduction {C : Contract} (ψ : Fml C []) : Option (LFml C) :=
  ψ.toLS true SymS.init

open Decide in
private def prefixDecision {C : Contract} (ψ : Fml C []) (r : LFml C) : Bool :=
  r.refuteOk && bif ψ.assumesCT then r.decideMemCT || r.decideMem else r.decideMem

open Decide in
private def prefixClose {C : Contract} (ψ : Fml C []) (r : LFml C) : Bool :=
  bif ψ.assumesCT then r.decideMemCT || r.decideMem else r.decideMem

open Decide in
private theorem prefixDecision_parts {C : Contract} (ψ : Fml C []) (r : LFml C)
    (hg : r.refuteOk = true) (hc : prefixClose ψ r = true) :
    prefixDecision ψ r = true := by
  change (r.refuteOk && prefixClose ψ r) = true
  simp only [hg, hc, Bool.true_and]

open Decide in
private def memoryStage {C : Contract} (stage : Nat) (r : LFml C) : LFml C :=
  match stage with
  | 0 => r.nfE
  | 1 => r.elimF {}
  | 2 => r.memRes
  | _ => r.memElim

open Decide in
private def quoteMemoryStage {C : Contract} (c : Expr) (stage : Nat) (r : LFml C) : Expr :=
  ((memoryStage stage r).quote).go c

open Decide in
private theorem memoryStages_checked {C : Contract} (r n e m p : LFml C)
    (hn : memoryStage 0 r = n) (he : memoryStage 1 n = e)
    (hm : memoryStage 2 e = m) (hp : memoryStage 3 m = p)
    (hc : LFml.closeMem.closeTwice p = true) : r.decideMem = true := by
  change r.nfE = n at hn
  change n.elimF {} = e at he
  change e.memRes = m at hm
  change m.memElim = p at hp
  unfold LFml.decideMem
  rw [hn, he]
  unfold LFml.closeMem
  rw [hm, hp]
  exact hc

open Decide in
private theorem prefixClose_mem {C : Contract} (ψ : Fml C []) (r : LFml C)
    (h : r.decideMem = true) : prefixClose ψ r = true := by
  unfold prefixClose
  cases ψ.assumesCT <;> simp only [Bool.cond_false, Bool.cond_true, h, Bool.or_true]

private def rawList (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x tail => mkApp3 (mkConst ``List.cons [0]) ty x tail)
    (mkApp (mkConst ``List.nil [0]) ty)

open Decide in
private def emptyPrefixFacts {C : Contract} : Facts C := {}

open Decide in
private def quotePremises {C : Contract} (c : Expr) (F : Facts C) : Option Expr := do
  unless F.nes.isEmpty && F.rets.isEmpty && F.bnds.isEmpty do none
  let eqs := F.eqs.map fun e =>
    mkAppN (mkConst ``EqF.mk) #[c, toExpr e.p, e.l.quote.go c, e.r.quote.go c]
  let es := rawList (mkApp (mkConst ``EqF) c) eqs
  return mkAppN (mkConst ``Facts.mk) #[c, es,
    rawList (mkApp (mkConst ``EqF) c) [],
    rawList (mkApp2 (mkConst ``Sigma [0, 0]) (mkConst ``Srt)
      (mkLambda `s .default (mkConst ``Srt) (mkApp2 (mkConst ``LTm) c (mkBVar 0)))) [],
    rawList (mkApp (mkConst ``RangeB) c) []]

open Decide in
private theorem elim_not (a a' : LFml C) (F : Facts C) (h : a.elimF F = a') :
    (LFml.not a).elimF F = .not a' := by
  change LFml.not (a.elimF F) = .not a'
  rw [h]

open Decide in
private theorem elim_and (a b a' b' : LFml C) (F : Facts C)
    (ha : a.elimF F = a') (hb : b.elimF F = b') :
    (LFml.and a b).elimF F = .and a' b' := by
  change LFml.and (a.elimF F) (b.elimF F) = .and a' b'
  rw [ha, hb]

open Decide in
private theorem elim_imp (a b a' b' : LFml C) (F F' : Facts C)
    (ha : a.elimF F = a') (hF : F.addEqs a'.factsOf = F')
    (hb : b.elimF F' = b') : (LFml.imp a b).elimF F = .imp a' b' := by
  change LFml.imp (a.elimF F) (b.elimF (F.addEqs (a.elimF F).factsOf)) = .imp a' b'
  rw [ha, hF, hb]

open Decide in
private theorem elim_all (k : Nat) (p : PrimTy) (a a' : LFml C) (F F' : Facts C)
    (hF : F.drop k = F') (ha : a.elimF F' = a') :
    (LFml.all k p a).elimF F = .all k p a' := by
  change LFml.all k p (a.elimF (F.drop k)) = .all k p a'
  rw [hF, ha]

private def retainTyped (ty value : Expr) : MetaM Expr := do
  let name ← mkFreshUserName `prefix_elimination
  addAndCompile <| .defnDecl {
    name, levelParams := [], type := ty, value := ShareCommon.shareCommon value,
    hints := .regular 0, safety := .safe }
  return mkConst name

/-- Untrusted quotations of existing typed LFml/Facts values, used only by
kernel-checked equality reconstruction. Interior nodes need no value quote.
No source semantics or model representation is interpreted over these Exprs. -/
private abbrev PrefixProposal := List Nat × Option Expr × Expr

open Decide in
private partial def buildEliminationProposals {C : Contract} (cn : Expr)
    (r : LFml C) (F : Facts C) (path : List Nat) :
    Option (LFml C × List PrefixProposal) := do
  let fq ← quotePremises cn F
  match r with
  | .not a =>
    let (a', rows) ← buildEliminationProposals cn a F (path ++ [0])
    return (.not a', (path, none, fq) :: rows)
  | .and a b =>
    let (a', left) ← buildEliminationProposals cn a F (path ++ [0])
    let (b', right) ← buildEliminationProposals cn b F (path ++ [1])
    return (.and a' b', (path, none, fq) :: (left ++ right))
  | .imp a b =>
    let (a', left) ← buildEliminationProposals cn a F (path ++ [0])
    let (b', right) ← buildEliminationProposals cn b (F.addEqs a'.factsOf) (path ++ [1])
    return (.imp a' b', (path, none, fq) :: (left ++ right))
  | .all k p a =>
    let (a', rows) ← buildEliminationProposals cn a (F.drop k) (path ++ [0])
    return (.all k p a', (path, none, fq) :: rows)
  | _ =>
    let value := r.elimF F
    return (value, [(path, some (value.quote.go cn), fq)])

open Decide in
private def eliminationProposals {C : Contract} (cn : Expr)
    (r : LFml C) (F : Facts C) (path : List Nat) :
    Option (List PrefixProposal × Expr × Expr) := do
  let (e, plan) ← buildEliminationProposals cn r F path
  let m := e.memRes
  return (plan, m.quote.go cn, m.memElim.quote.go cn)

open Decide in
private theorem elimination_input_eq (r n e : LFml C) (F : Facts C)
    (h : r = n) (he : n.elimF F = e) : r.elimF F = e := by
  rw [h]
  exact he

private def proposalAt (plan : List PrefixProposal) (path : List Nat) : MetaM PrefixProposal := do
  let some row := plan.find? (fun row => row.1 == path)
    | throwError "missing typed elimination proposal"
  return row

private def retainProofInput (ty value : Expr) : MetaM Expr := do
  let name ← mkFreshUserName `prefix_checked_selector
  addDecl <| .defnDecl {
    name, levelParams := [], type := ty, value,
    hints := .regular 0, safety := .safe }
  return mkConst name

/-- Internal equality proposals are checked together at refuteAtom's original
synchronous Boolean certificate. Typed data, terminal decisions, and the atom
and prefix guards remain immediately checked under the original budget. -/
private def prefixStageLemma (type value : Expr) : MetaM Expr := do
  if sol.prove.sharedResidues.get (← getOptions) && !type.hasFVar && !type.hasMVar then
    return mkApp2 (mkConst ``id [0]) type value
  Derive.kernelLemma type value

private def retainPremises (C F value : Expr) : MetaM (Expr × Expr) := do
  let result ← retainProofInput (mkApp (mkConst ``Decide.Facts) C) value
  let cert ← prefixStageLemma (← mkEq F result) (← mkEqRefl result)
  return (result, cert)

private partial def sharePrefixFormula (C : Expr) (value : Expr)
    (cache : IO.Ref (Std.HashMap Expr Expr)) : MetaM Expr := do
  if let some result := (← cache.get)[value]? then return result
  let args := value.getAppArgs
  let node ← if value.isAppOf ``Decide.LFml.not then do
      pure <| mkApp2 (mkConst ``Decide.LFml.not) C (← sharePrefixFormula C args[1]! cache)
    else if value.isAppOf ``Decide.LFml.and || value.isAppOf ``Decide.LFml.imp then do
      pure <| mkApp3 value.getAppFn C
        (← sharePrefixFormula C args[1]! cache) (← sharePrefixFormula C args[2]! cache)
    else if value.isAppOf ``Decide.LFml.all then do
      pure <| mkAppN (mkConst ``Decide.LFml.all)
        #[C, args[1]!, args[2]!, ← sharePrefixFormula C args[3]! cache]
    else pure value
  let result ← retainProofInput (mkApp (mkConst ``Decide.LFml) C) node
  cache.modify (·.insert value result)
  return result

private partial def eliminationCertificate (C cn r : Expr) (path : List Nat) (F : Expr) (plan : List PrefixProposal) : MetaM (Expr × Expr) := do
  let .defnInfo info ← getConstInfo r.constName! | throwError "expected checked formula node"
  let shape := info.value
  let args := shape.getAppArgs
  let lfTy := mkApp (mkConst ``Decide.LFml) C
  let elim := mkAppN (mkConst ``Decide.LFml.elimF) #[C, r, F]
  let (value, proof) ← if shape.isAppOf ``Decide.LFml.not then do
      let left := args[if shape.isAppOf ``Decide.LFml.all then 3 else 1]!
      let (a, ha) ← eliminationCertificate C cn left (path ++ [0]) F plan
      pure (mkApp2 (mkConst ``Decide.LFml.not) C a,
        mkAppN (mkConst ``elim_not) #[C, left, a, F, ha])
    else if shape.isAppOf ``Decide.LFml.and then do
      let left := args[if shape.isAppOf ``Decide.LFml.all then 3 else 1]!
      let (a, ha) ← eliminationCertificate C cn left (path ++ [0]) F plan
      let right := args[2]!
      let (b, hb) ← eliminationCertificate C cn right (path ++ [1]) F plan
      pure (mkApp3 (mkConst ``Decide.LFml.and) C a b,
        mkAppN (mkConst ``elim_and) #[C, left, right, a, b, F, ha, hb])
    else if shape.isAppOf ``Decide.LFml.imp then do
      let left := args[if shape.isAppOf ``Decide.LFml.all then 3 else 1]!
      let (a, ha) ← eliminationCertificate C cn left (path ++ [0]) F plan
      let facts := mkApp2 (mkConst ``Decide.LFml.factsOf) C a
      let (F', hF) ← retainPremises C (mkApp3 (mkConst ``Decide.Facts.addEqs) C F facts) (← proposalAt plan (path ++ [1])).2.2
      let right := args[2]!
      let (b, hb) ← eliminationCertificate C cn right (path ++ [1]) F' plan
      pure (mkApp3 (mkConst ``Decide.LFml.imp) C a b,
        mkAppN (mkConst ``elim_imp) #[C, left, right, a, b, F, F', ha, hF, hb])
    else if shape.isAppOf ``Decide.LFml.all then do
      let (F', hF) ← retainPremises C (mkApp3 (mkConst ``Decide.Facts.drop) C F args[1]!) (← proposalAt plan (path ++ [0])).2.2
      let left := args[if shape.isAppOf ``Decide.LFml.all then 3 else 1]!
      let (a, ha) ← eliminationCertificate C cn left (path ++ [0]) F' plan
      pure (mkAppN (mkConst ``Decide.LFml.all) #[C, args[1]!, args[2]!, a],
        mkAppN (mkConst ``elim_all) #[C, args[1]!, args[2]!, left, a, F, F', hF, ha])
    else do
      let some value := (← proposalAt plan path).2.1
        | throwError "missing terminal formula quotation"
      pure (value, ← mkEqRefl value)
  let result ← retainProofInput lfTy value
  let cert ← prefixStageLemma (← mkEq elim result) proof
  return (result, cert)

private def memoryCertificate (C cn r : Expr) : MetaM Expr := do
  let lfTy := mkApp (mkConst ``Decide.LFml) C
  let mut prev := r
  let mut remainder : Array Expr := #[]
  let mut forms : Array Expr := #[]
  let mut certs : Array Expr := #[]
  for stage in [:4] do
    let (form, eq) ← if stage == 1 then do
        let F ← retainTyped (mkApp (mkConst ``Decide.Facts) C)
          (mkApp (mkConst ``emptyPrefixFacts) C)
        let exprTy := mkConst ``Expr
        let listNatTy := mkApp (mkConst ``List [0]) (mkConst ``Nat)
        let rowTy := mkApp2 (mkConst ``Prod [0, 0]) listNatTy
          (mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``Option [0]) exprTy) exprTy)
        let batchTy := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``List [0]) rowTy)
          (mkApp2 (mkConst ``Prod [0, 0]) exprTy exprTy)
        let planTy := mkApp (mkConst ``Option [0]) batchTy
        let plan ← unsafe evalExpr (Option (List PrefixProposal × Expr × Expr)) planTy
          (mkAppN (mkConst ``eliminationProposals) #[C, cn, prev, F, toExpr ([] : List Nat)])
        let some (plan, qm, qp) := plan | throwError "unsupported typed premise proposal"
        remainder := #[qm, qp]
        let .defnInfo info ← getConstInfo prev.constName!
          | throwError "expected quoted formula root"
        let cache ← IO.mkRef ({} : Std.HashMap Expr Expr)
        let shared ← sharePrefixFormula C info.value cache
        let eqShared ← prefixStageLemma (← mkEq prev shared) (← mkEqRefl shared)
        let (result, cert) ← eliminationCertificate C cn shared [] F plan
        let cert := mkAppN (mkConst ``elimination_input_eq)
          #[C, prev, shared, result, F, eqShared, cert]
        pure (result, cert)
      else do
        let value ← if stage == 0 then
            unsafe evalExpr Expr (mkConst ``Expr)
              (mkAppN (mkConst ``quoteMemoryStage) #[C, cn, toExpr stage, prev])
          else pure remainder[stage - 2]!
        let name ← mkFreshUserName `prefix_memory_stage
        let decl := Declaration.defnDecl {
          name := name, levelParams := [], type := lfTy,
          value := ShareCommon.shareCommon value, hints := .regular 0, safety := .safe }
        addDecl decl
        if stage == 0 then compileDecl decl
        let form := mkConst name
        let eq ← prefixStageLemma
          (← mkEq (mkAppN (mkConst ``memoryStage) #[C, toExpr stage, prev]) form)
          (← mkEqRefl form)
        pure (form, eq)
    forms := forms.push form
    certs := certs.push eq
    prev := form
  let hc ← Decide.trueLemma (mkApp2 (mkConst ``Decide.LFml.closeMem.closeTwice) C prev)
  pure <| mkAppN (mkConst ``memoryStages_checked) (#[C, r] ++ forms ++ certs ++ #[hc])

open Decide in
private def quotePrefixReduction {C : Contract} (c : Expr) (ψ : Fml C []) : Option Expr :=
  (prefixReduction ψ).map fun l => (l.quote).go c

open Decide in
private def prefixForm {C : Contract} (l : LFml C) : LFml C := l.refuteForm

open Decide in
private def quotePrefixForm {C : Contract} (c : Expr) (l : LFml C) : Expr :=
  ((prefixForm l).quote).go c

open Decide in
private theorem refuteCore_reduced {C : Contract} (ψ : Fml C []) (l r : LFml C)
    (hReduce : prefixReduction ψ = some l) (hForm : prefixForm l = r)
    (hCheck : prefixDecision ψ r = true) : Seq.refuteCore ψ = true := by
  change ψ.toLS true SymS.init = some l at hReduce
  change l.refuteForm = r at hForm
  unfold Seq.refuteCore
  rw [hReduce]
  change prefixDecision ψ l.refuteForm = true
  rw [hForm]
  exact hCheck

private theorem refuteS_parts {C : Contract} {Γ : Ctx} (H : Hyps C [] Γ) (c : Fml C Γ)
    (hm : ((H.pre c).wrap .ff).modalFree = true)
    (hr : Seq.refuteCore ((H.pre c).wrap .ff) = true) : Seq.refuteS H c = true := by
  simp only [Seq.refuteS, hm, hr, Bool.true_and]

/-- Retain checked typed normal forms, not Boolean verdicts. Every reduction,
form-selection and final decision remains a synchronous kernel certificate. -/
private def refuteAtom (C Γ H c : Expr) : MetaM Expr := do
  let atom := mkAppN (mkConst ``Seq.refuteS) #[C, Γ, H, c]
  let saved ← saveState
  tryCatchRuntimeEx (do
      let some cn := C.constName? | throwError "prefix reduction needs a named contract"
      let nilCtx := ctxE []
      let hc := mkAppN (mkConst ``Hyps.pre) #[C, nilCtx, Γ, H, c]
      let ff := mkApp2 (mkConst ``Fml.ff) C Γ
      let ψ := mkAppN (mkConst ``Hyps.wrap) #[C, nilCtx, Γ, hc, ff]
      let lfTy := mkApp (mkConst ``Decide.LFml) C
      let optTy := mkApp (mkConst ``Option [0]) lfTy
      let quoted ← unsafe evalExpr (Option Expr) (mkApp (mkConst ``Option [0]) (mkConst ``Expr))
        (mkAppN (mkConst ``quotePrefixReduction) #[C, quoteConstName cn, ψ])
      let some quoted := quoted | throwError "prefix reduction is outside the existing fragment"
      let ln ← mkFreshUserName `prefix_normal
      addAndCompile <| .defnDecl {
        name := ln, levelParams := [], type := lfTy,
        value := ShareCommon.shareCommon quoted, hints := .regular 0, safety := .safe }
      let l := mkConst ln
      let someL := mkApp2 (mkConst ``Option.some [0]) lfTy l
      let hReduce ← Derive.kernelLemma
        (mkApp3 (mkConst ``Eq [1]) optTy (mkAppN (mkConst ``prefixReduction) #[C, ψ]) someL)
        (mkApp2 (mkConst ``Eq.refl [1]) optTy someL)
      let form ← unsafe evalExpr Expr (mkConst ``Expr)
        (mkAppN (mkConst ``quotePrefixForm) #[C, quoteConstName cn, l])
      let rn ← mkFreshUserName `prefix_refute_form
      addAndCompile <| .defnDecl {
        name := rn, levelParams := [], type := lfTy,
        value := ShareCommon.shareCommon form, hints := .regular 0, safety := .safe }
      let r := mkConst rn
      let hForm ← Derive.kernelLemma
        (mkApp3 (mkConst ``Eq [1]) lfTy (mkAppN (mkConst ``prefixForm) #[C, l]) r)
        (mkApp2 (mkConst ``Eq.refl [1]) lfTy r)
      let hGuard ← Decide.trueLemma (mkApp2 (mkConst ``Decide.LFml.refuteOk) C r)
      let hm ← memoryCertificate C (quoteConstName cn) r
      let hClose := mkAppN (mkConst ``prefixClose_mem) #[C, ψ, r, hm]
      let hCheck := mkAppN (mkConst ``prefixDecision_parts) #[C, ψ, r, hGuard, hClose]
      let hr := mkAppN (mkConst ``refuteCore_reduced) #[C, ψ, l, r, hReduce, hForm, hCheck]
      let hm ← Decide.trueLemma (mkApp3 (mkConst ``Fml.modalFree) C nilCtx ψ)
      let proof := mkAppN (mkConst ``refuteS_parts) #[C, Γ, H, c, hm, hr]
      let checked ← Derive.kernelLemma (← mkEq atom (mkConst ``Bool.true)) proof
      pure checked)
    fun _ => do
      saved.restore
      Decide.trueLemma atom

/-- Construct a proof of the unchanged checker statement. Only the winning
atom is evaluated by the kernel; OR introduction skips losing operands. -/
private partial def prefixProof (C : Expr) (fuel : Nat) (Γ H : Expr)
    (depth : Nat) : MetaM Expr := do
  if fuel == 0 then throwError "prefix witness exceeds its original bound"
  let shape ← whnfR H
  if shape.isAppOfArity ``Hyps.pre 5 then
    let before := shape.getArg! 3
    let c := shape.getArg! 4
    if depth == 0 then
      let atom ← refuteAtom C Γ before c
      return mkAppN (mkConst ``refutePrefix_head)
        #[C, Γ, toExpr (fuel - 1), before, c, atom]
    let tail ← prefixProof C (fuel - 1) Γ before (depth - 1)
    return mkAppN (mkConst ``refutePrefix_tail)
      #[C, Γ, toExpr (fuel - 1), before, c, tail]
  if depth == 0 then throwError "prefix witness does not select a premise"
  let before? := if shape.isAppOfArity ``Hyps.upd 7 then some (shape.getArg! 4)
    else if shape.isAppOfArity ``Hyps.havoc 4 || shape.isAppOfArity ``Hyps.all 6 ||
        shape.isAppOfArity ``Hyps.bind 7 || shape.isAppOfArity ``Hyps.anon 5 ||
        shape.isAppOfArity ``Hyps.allocAll 6 || shape.isAppOfArity ``Hyps.grow 4 then
      some (shape.getArg! 3)
    else none
  let some before := before? | throwError "prefix witness has no checked premise"
  prefixProof C (fuel - 1) (shape.getArg! 2) before (depth - 1)

private def refutePrefixLemma (C : Expr) (fuel : Nat) (Γ H : Expr) (depth : Nat) : MetaM Expr := do
  let probe := mkAppN (mkConst ``refutePrefix) #[C, toExpr fuel, Γ, H]
  let saved ← saveState
  tryCatchRuntimeEx (do
      unless depth < fuel do throwError "prefix witness exceeds its original bound"
      let proof ← prefixProof C fuel Γ H depth
      -- This exact original proposition is kernel checked, including the
      -- original fuel, full context and every skipped constructor.
      Derive.kernelLemma (← mkEq probe (mkConst ``Bool.true)) proof)
    fun _ => do
      saved.restore
      Decide.trueLemma probe

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
def closePrefixFalse (g : MVarId) (fuel : Nat) (depth? : Option Nat := none) : MetaM Unit := g.withContext do
  unless fuel ≤ 8 do throwError "sol_prefix_false: at most eight context layers"
  let ty ← instantiateMVars (← g.getType)
  let_expr ProvesC C I pay Γ₀ Γ H φ := ty
    | throwError "sol_prefix_false: expected a callback sequent"
  unless (← whnfR Γ₀).isAppOf ``List.nil do
    throwError "sol_prefix_false: expected a closed outer scope"
  let probe := mkAppN (mkConst ``refutePrefix) #[C, mkNatLit fuel, Γ, H]
  if probe.hasFVar || probe.hasMVar then
    throwError "sol_prefix_false: the certificate is not closed"
  let hc ← match depth? with
    | some depth => refutePrefixLemma C fuel Γ H depth
    | none => Decide.trueLemma probe
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
      let probePair := mkAppN (mkConst ``prefixProbe) #[C, mkNatLit 8, Γ, H]
      let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Bool)
        (mkApp (mkConst ``Option [0]) (mkConst ``Nat))
      let (refuted, depth?) ← unsafe evalExpr (Bool × Option Nat) pairTy probePair
      unless refuted do return none
      let replay ← `(tactic| sol_prefix_false 8)
      let closed ← Budget.bounded 16384 do
        closePrefixFalse g 8 depth?
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
  let guarded ← tryCatchRuntimeEx (withCurrHeartbeats (hasTransferNormality g)) fun _ => pure false
  if !guarded && (← tryCatchRuntimeEx (withCurrHeartbeats (Walk.negModalGoal? g)) fun _ => pure false) then
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
