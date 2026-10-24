import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.Closers

/-!
# `sol_prove (chunk := n)`: the walk in kernel-checked chunks

`sol_prove` checks its whole walk as one kernel evaluation
(`Seq.residueWithin`).  A walk of thousands of steps over a context of
hundreds of updates (an unrolled loop that allocates memory, the nine
binomial rows of `SolcLoopsOpen`) costs more memory in that one check than
a session has.  Here the walk stops after `n` steps and leaves the sequent
it reached as a leaf (`Seq.cutK`, `Seq.runK` with its step budget read as
a checkpoint), whose walk is the next chunk: each chunk is its own kernel
check (`Proves.of_cutWithin`) under its own heartbeat budget, as a step of a
search (`AGENTS.md`, "Writing or fixing a tactic"); the compiled walk that
proposes it heeds no heartbeats, as `sol_prove`'s does not.  A tactic after
a long `sol_prove (chunk := n)` in the same declaration starts past the
declaration's budget, so the leaves are closed here.  A leaf with no modality
left is closed by `sol_leaf; sol_close` under a budget of its own; one it
does not close stays a goal.

Nothing is trusted: every chunk is a theorem the kernel checks, and the
walk it replays is `Seq.runK`'s, step for step (`Seq.cutK_sound`).
-/

namespace Solidity

namespace Seq

variable {C : Contract} {α : Type}

/-- **The walk with a step budget read as a checkpoint**: `runK`, where a
spent budget `b` (or fuel `n`) leaves the sequent reached as a leaf
(`leaf`) in place of failing. -/
def cutK (R : RuleSet) (leaf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List α))
    (rf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Bool) :
    Nat → {Γ : Ctx} → Hyps C [] Γ → Nat → Fml C Γ → Nat → Option (List α × Nat)
  | 0, _, H, _, φ, b => (leaf H φ).map (·, b)
  | _ + 1, _, H, _, φ, 0 => (leaf H φ).map (·, 0)
  | n + 1, _, H, k, φ, b + 1 =>
    Fml.casesOn (motive := fun Γ _ => Hyps C [] Γ → Option (List α × Nat)) φ
      (tt := fun H => cond H.boxOnly (some ([], b)) ((leaf H .tt).map (·, b)))
      (eq := fun t u H => (leaf H (.eq t u)).map (·, b))
      (wellFormed := fun s H => (leaf H (.wellFormed s)).map (·, b))
      (not := fun ψ H => (leaf H (.not ψ)).map (·, b))
      (and := fun ψ χ H => cond (Fml.and ψ χ).modalFree ((leaf H (.and ψ χ)).map (·, b))
        (both (cutK R leaf rf n H k ψ) (cutK R leaf rf n H k χ) b))
      (imp := fun a ψ H => match a.negModal? with
        | some X => match cutK R leaf rf n H k X b with
          | some (ls, b') => cond ls.isEmpty (some ([], b')) (cutK R leaf rf n H k ψ b)
          | none => cutK R leaf rf n H k ψ b
        | none => cutK R leaf rf n (H.pre a) (max k a.maxIdx) ψ b)
      (upd := fun m U ψ H => cutK R leaf rf n (H.upd m U) (max k U.maxIdx) ψ b)
      (modal := fun m P κ ψ H =>
        modal R (fun H k φ b => cutK R leaf rf n H k φ b) rf m H k P κ ψ b)
      (havoc := fun ψ H => (leaf H (.havoc ψ)).map (·, b))
      (all := fun x p ψ H => cutK R leaf rf n (H.all x p) (max k x.idx) ψ b)
      (bind := fun m x t ψ H => cutK R leaf rf n (H.bind m x t) (max k x.idx) ψ b)
      (anon := fun xs ψ H => (leaf H (.anon xs ψ)).map (·, b))
      (allocAll := fun x A ψ H => cutK R leaf rf n (H.allocAll x A) (max k x.idx) ψ b)
      (grow := fun ψ H => (leaf H (.grow ψ)).map (·, b)) H

section Sound

variable {P : α → Prop} {R : RuleSet}
variable {leaf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List α)}
  (hleaf : ∀ {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) ls, leaf H φ = some ls →
    (∀ l ∈ ls, P l) → Proves C R [] H φ)
variable {rf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Bool}
  (hrf : ∀ {Γ : Ctx} (H : Hyps C [] Γ) (c : Fml C Γ), rf H c = true →
    ∀ {a φ : Fml C Γ}, Proves C R [] (H.pre a) φ → Proves C R [] (H.pre c) .ff)
include hleaf hrf

/-- **What the chunk leaves proves the sequent**: `runK_sound`'s walk, a
spent budget a leaf. -/
theorem cutK_sound : ∀ (n : Nat) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) (b : Nat)
    (ls : List α) (b' : Nat), cutK R leaf rf n H H.maxIdxH φ b = some (ls, b') →
    (∀ l ∈ ls, P l) → Proves C R [] H φ
  | 0, _, H, φ, b, _, _, h, hl => leaf_sound hleaf h hl
  | _ + 1, _, H, φ, 0, _, _, h, hl => leaf_sound hleaf h hl
  | n + 1, _, H, φ, b + 1, ls, b', h, hl => by
    have ih : ∀ {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) b ls b',
        cutK R leaf rf n H H.maxIdxH φ b = some (ls, b') → (∀ l ∈ ls, P l) →
          Proves C R [] H φ :=
      fun H φ b ls b' h hl => cutK_sound n H φ b ls b' h hl
    cases φ with
    | tt =>
      cases hb : H.boxOnly
      · exact leaf_sound hleaf (b := b) (by simpa only [cutK, hb, cond_false] using h) hl
      · exact .closeTrue hb
    | eq => exact leaf_sound hleaf h hl
    | wellFormed => exact leaf_sound hleaf h hl
    | not => exact leaf_sound hleaf h hl
    | and ψ χ =>
      cases hm : (Fml.and ψ χ).modalFree
      · simp only [cutK, hm, cond_false] at h
        have := both_sound h hl (ih _ _) (ih _ _)
        exact .andIntro this.1 this.2
      · exact leaf_sound hleaf (b := b) (by simpa only [cutK, hm, cond_true] using h) hl
    | imp a ψ =>
      change (match a.negModal? with
        | some X => match cutK R leaf rf n H H.maxIdxH X b with
          | some (ls, b') => cond ls.isEmpty (some ([], b')) (cutK R leaf rf n H H.maxIdxH ψ b)
          | none => cutK R leaf rf n H H.maxIdxH ψ b
        | none => cutK R leaf rf n (H.pre a) (max H.maxIdxH a.maxIdx) ψ b) = some (ls, b') at h
      cases hn : a.negModal? with
      | none =>
        rw [hn] at h
        exact .intro (ih _ _ _ _ _ h hl)
      | some X =>
        rw [hn] at h
        dsimp only at h
        rw [Fml.negModal?_eq hn]
        cases hX : cutK R leaf rf n H H.maxIdxH X b with
        | none =>
          rw [hX] at h
          exact .hideLeft (ih _ _ _ _ _ h hl)
        | some p =>
          obtain ⟨lx, bx⟩ := p
          rw [hX] at h
          dsimp only at h
          cases he : lx.isEmpty
          · rw [he, cond_false] at h
            exact .hideLeft (ih _ _ _ _ _ h hl)
          · exact .notLeft (ih _ _ _ _ _ hX fun l hlx => by
              rw [List.isEmpty_iff] at he
              rw [he] at hlx
              exact nomatch hlx)
    | upd m U ψ => exact .updIntro (ih _ _ _ _ _ h hl)
    | modal m P κ ψ =>
      cases P with
      | nil => exact .empty (ih _ _ _ _ _ h hl)
      | cons s ω =>
        change (match s.stepIn R (freshK H.maxIdxH (.modal m (.cons s ω) κ ψ)) m with
          | some p => premise (fun H k φ b => cutK R leaf rf n H k φ b) rf H H.maxIdxH m ω κ ψ p b
          | none => none) = some (ls, b') at h
        split at h
        · rename_i p hp
          rw [← Hyps.fresh_eq_freshK] at hp
          exact premise_sound ih hrf H m s ω κ ψ p hp h hl
        · cases h
    | havoc => exact leaf_sound hleaf h hl
    | all x p ψ => exact .allIntro (ih _ _ _ _ _ h hl)
    | bind m x t ψ => exact .bindIntro (ih _ _ _ _ _ h hl)
    | anon => exact leaf_sound hleaf h hl
    | allocAll x A ψ => exact .allocIntro (ih _ _ _ _ _ h hl)
    | grow => exact leaf_sound hleaf h hl

end Sound

/-- The leaves of one chunk of `steps` steps of the sequent `H ⊢ φ`. -/
def cutWithin (steps : Nat) (R : RuleSet) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List (SLeaf C)) :=
  (cutK R leafS refuteLanded steps H H.maxIdxH φ steps).map Prod.fst

/-- `cutWithin`'s leaves, quoted at the contract `c`. -/
def cutQuoteWithin (steps : Nat) (R : RuleSet) (c : Lean.Expr) (np : Option Nat)
    {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) : Option (List Lean.Expr) :=
  (cutWithin steps R H φ).map fun leaves => leaves.map fun l => SLeaf.quote c np l.2.1 l.2.2

end Seq

/-- **A chunk's leaves prove its sequent** (`Seq.cutK_sound`). -/
theorem Proves.of_cutWithin {C : Contract} (steps : Nat) {R : RuleSet} {Γ : Ctx}
    {H : Hyps C [] Γ} {φ : Fml C Γ} {ls : List (Seq.SLeaf C)}
    (h : Seq.cutWithin steps R H φ = some ls)
    (hl : ∀ l ∈ ls, Proves C R [] l.2.1 l.2.2) : Proves C R [] H φ := by
  obtain ⟨⟨ls', b'⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
  cases he
  exact Seq.cutK_sound (P := fun l : Seq.SLeaf C => Proves C R [] l.2.1 l.2.2)
    Seq.leafS_sound
    (fun {_} H c h {_ _} live => Seq.refuteLanded_sound H c h live)
    _ H φ _ _ _ hr hl

namespace Seq

open Lean Elab Tactic Meta

/-- One chunk on the goal `g`, `H ⊢ φ`: `steps` steps of the compiled walk,
then one kernel check of what they leave (`Proves.of_cutWithin`); the
goals left, one per leaf. -/
def chunk (g : MVarId) (C R Γ H φ : Expr) (steps : Nat) : MetaM (List MVarId) := do
  let some n := C.constName? | throwError "sol_prove: the contract is not a named constant"
  if H.hasFVar || H.hasMVar || φ.hasFVar || φ.hasMVar || R.hasFVar || R.hasMVar then
    throwError "sol_prove: the sequent mentions a local hypothesis or a metavariable"
  let φe ← Symex.evaluable φ
  let np := toExpr (← paramCount H φe)
  let leafTy := mkApp (mkConst ``SLeaf) C
  let resTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0]) leafTy)
  let qTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0]) (mkConst ``Expr))
  let some leaves ← unsafe evalExpr (Option (List Expr)) qTy
      (mkAppN (mkConst ``cutQuoteWithin) #[C, toExpr steps, R, quoteConstName n, np, Γ, H, φe])
    | throwError "sol_prove: a step of the walk has no rule"
  let ls ← mkListLit leafTy leaves
  let someLs := mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``List [0]) leafTy) ls
  let h ← try
      Derive.kernelLemma (mkApp3 (mkConst ``Eq [1]) resTy
        (mkAppN (mkConst ``cutWithin) #[C, toExpr steps, R, Γ, H, φ]) someLs)
        (mkApp2 (mkConst ``Eq.refl [1]) resTy someLs)
    catch e => throwError "sol_prove: the kernel rejects the chunk:{indentD e.toMessageData}"
  -- a leaf `⟨Γ', (H', φ')⟩`: its goal `H' ⊢ φ'`
  let parts (l : Expr) : Expr × Expr × Expr :=
    let pr := l.getArg! 3
    (l.getArg! 2, pr.getArg! 2, pr.getArg! 3)
  let nilCtx := ctxE []
  let mut goals : Array MVarId := #[]
  for l in leaves, i in [1:leaves.length + 1] do
    let (Γ', H', φ') := parts l
    let gi ← mkFreshExprSyntheticOpaqueMVar
      (mkAppN (mkConst ``Proves) #[C, R, nilCtx, Γ', H', φ']) (Name.mkSimple s!"leaf{i}")
    goals := goals.push gi.mvarId!
  let mut hl := mkApp2 (mkConst ``SLeaf.nil) C R
  let mut rest := mkApp (mkConst ``List.nil [0]) leafTy
  for l in leaves.reverse, p in goals.reverse do
    let (Γ', H', φ') := parts l
    hl := mkAppN (mkConst ``SLeaf.cons) #[C, R, Γ', H', φ', rest, .mvar p, hl]
    rest := mkAppN (mkConst ``List.cons [0]) #[leafTy, l, rest]
  g.assign (mkAppN (mkConst ``Proves.of_cutWithin) #[C, toExpr steps, R, Γ, H, φ, ls, h, hl])
  return goals.toList

/-- The goal `H ⊢ φ` of the outer scope, its contract, rule set, context,
hypotheses and formula. -/
def sequent? (g : MVarId) : MetaM (Option (Expr × Expr × Expr × Expr × Expr)) := do
  let ty ← instantiateMVars (← g.getType)
  let_expr Proves C R Γ₀ Γ H φ := ty | return none
  unless (← whnfR Γ₀).isAppOf ``List.nil do return none
  return some (C, R, Γ, H, φ)

/-- The recursion depth a chunk runs with: the code generator compiles the
sequent a chunk starts from, a term as deep as the context is long. -/
def chunkRecDepth : Nat := 65536

/-- `x` at `chunkRecDepth`, the context's bound and the option alike. -/
def withChunkDepth {α : Type} (x : TacticM α) : TacticM α :=
  let set (c : Core.Context) : Core.Context :=
    { c with maxRecDepth := chunkRecDepth, options := maxRecDepth.set c.options chunkRecDepth }
  withTheReader Core.Context set x

/-- The most chunks one `sol_prove (chunk := n)` runs. -/
def chunkFuel : Nat := 256

/-- `sol_leaf; sol_close` on the leaf `g`; the goals left. -/
def closeLeaf (g : MVarId) : TacticM (List MVarId) := do
  setGoals [g]
  evalTactic (← `(tactic| (sol_leaf; sol_close)))
  getUnsolvedGoals

/-- **The walk in chunks** from the goal `g`: each sequent with a modality
walked `steps` steps (`chunk`), each without closed by `close`
(`sol_leaf; sol_close`), each under a heartbeat budget of its own; a chunk
or a closer that fails leaves its goal, with a note.  The goals left. -/
def proveChunked (g : MVarId) (steps : Nat)
    (close : MVarId → TacticM (List MVarId) := closeLeaf) : TacticM (List MVarId) := do
  unless 0 < steps && steps ≤ fuel do
    throwError "sol_prove: chunk must be between 1 and {fuel}"
  let mut pending := [g]
  let mut left : List MVarId := []
  for _ in [0:chunkFuel] do
    let some g := pending.head? | break
    pending := pending.tail
    let state ← saveState
    -- every step, the reading of its sequent included, under its own budget:
    -- the declaration's is spent by the chunks before it
    let next ← tryCatchRuntimeEx
      (withChunkDepth <| withCurrHeartbeats do
        let some (C, R, Γ, H, φ) ← sequent? g | return some ([g], true)
        let isLeaf ← unsafe evalExpr Bool (mkConst ``Bool)
          (mkApp3 (mkConst ``Fml.modalFree) C Γ (← Symex.evaluable φ))
        if isLeaf then return some (← close g, true)
        let ty ← instantiateMVars (← g.getType)
        let gs ← chunk g C R Γ H φ steps
        -- a chunk that leaves its own sequent made no step: kept, not retried
        if let [g'] := gs then
          if (← instantiateMVars (← g'.getType)) == ty then
            logInfo m!"sol_prove: a chunk made no step; its sequent is left"
            return some (gs, true)
        return some (gs, false))
      (fun e => do
        let msgs := (← Core.getMessageLog).toList.filter (·.severity == .error)
        state.restore
        let mut why := e.toMessageData
        for m in msgs do why := why ++ m!"\n{((← m.data.toString).take 2000)}"
        logInfo m!"sol_prove: a chunk or a leaf stopped: {why}"
        return none)
    match next with
    | some (gs, true) => left := left ++ gs
    | some (gs, false) => pending := gs ++ pending
    | none => left := left ++ [g]
  unless pending.isEmpty do
    logInfo m!"sol_prove: {chunkFuel} chunks run; {pending.length} sequents left unwalked"
  return left ++ pending

end Seq

/-- `sol_prove (chunk := n)`: `sol_prove`'s walk, `n` steps per kernel
check and per heartbeat budget (`Seq.proveChunked`); each leaf closed by
`sol_leaf; sol_close` where it can be, the rest left as goals. -/
syntax (name := tacticSol_prove_chunk) "sol_prove" "(" &"chunk" ":=" num ")" : tactic

open Lean Elab Tactic Meta in
@[tactic tacticSol_prove_chunk]
def evalSolProveChunk : Tactic := fun stx => withMainContext do
  let `(tactic| sol_prove (chunk := $n:num)) := stx | throwUnsupportedSyntax
  let g ← getMainGoal
  let rest := (← getUnsolvedGoals).erase g
  let g ← match ← Symex.validGoal? g with
    | some (C, φ) =>
      let g' ← mkFreshExprSyntheticOpaqueMVar (ProofTree.provesE C φ) (← g.getTag)
      g.assign (mkAppN (mkConst ``Proves.fmlValid) #[C, mkConst ``RuleSet.all, φ, g'])
      pure g'.mvarId!
    | none =>
      if (← Seq.sequent? g).isNone then
        throwError "sol_prove (chunk := n): expected `⊢ φ` or `⊨ᶠ φ`"
      pure g
  let left ← Seq.proveChunked g n.getNat
  setGoals (left ++ rest)

end Solidity
