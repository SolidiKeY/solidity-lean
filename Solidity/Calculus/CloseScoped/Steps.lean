import Solidity.Calculus.CloseScoped.Leaf

/-!
# Closing a scoped leaf: the steps

The tactic steps on a scoped goal, joined `if`s and joined leaves.

A piece of `Calculus/CloseScoped.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## The steps on a scoped goal -/

open Lean Elab Tactic Meta

/-- **A checked result read as itself** (`CloseS.wp_ite_uintOf`,
`CloseS.wp_ite_intOf`) where its integer reads a variable, before the rest
is read: the rest at `⟨n, _⟩`, not at `uintOf n`, whose integer copies `n`
three times.  An integer that reads no variable value (`1 << 255`, a
local's value read off the state) is left to `Modality.wp_ite`, which
decides its check or reads it as before. -/
simproc ↓ [close_rw_s] CloseS.wpChecked (@Modality.wp _ _ (@ite _ _ _ (Except.ok _) _) _) :=
    fun e => do
  let_expr Modality.wp _ m x P := e | return .continue
  let_expr ite _ _ inst t y := x | return .continue
  let_expr Except.ok _ _ v := t | return .continue
  let lem ← match v.getAppFn.constName? with
    | some ``CloseS.uintOf => pure ``CloseS.wp_ite_uintOf
    | some ``CloseS.intOf => pure ``CloseS.wp_ite_intOf
    | _ => return .continue
  let n := v.appArg!
  -- a value that reads a variable value (a parameter, an earlier result),
  -- not the state's locals, whose reads are read off the state first
  let fs := (collectFVars {} n).fvarIds
  let mut isVar := false
  for f in fs do
    let ty ← instantiateMVars (← f.getType)
    if ty.isConstOf ``Int || ty.isAppOf ``PrimTy.Denote || ty.isAppOf ``Subtype then
      isVar := true
  unless isVar do return .continue
  try
    let pf := mkAppN (mkConst lem) #[m, n, inst, y, P]
    let some (lhs, rhs) := (← inferType pf).iff? | return .continue
    unless ← isDefEq lhs e do return .continue
    return .visit { expr := rhs, proof? := some (mkApp3 (mkConst ``propext) lhs rhs pf) }
  catch _ => return .continue



/-- A Boolean of the formula's terms, evaluated (`Tm.agreeB`, `Tm.totB`,
`Tm.pushFree`); one that does not reduce to a literal (a term with a free
variable) fails, and `sol_close_unwrap` then leaves the leaf as it is. -/
private def evalBoolE (e : Expr) : MetaM Bool := do
  let e' ← whnfD e
  if e'.isConstOf ``Bool.true then return true
  if e'.isConstOf ``Bool.false then return false
  throwError "evalEqsE: {e} does not reduce"

/-- A local, a literal or a value of the transaction, read off the syntax, as
the atom (`Fml.Atom`) whose term it is. -/
private def atomE? (e : Expr) : MetaM (Option Expr) := do
  unless e.isAppOfArity ``Tm.pvV 4 || e.isAppOfArity ``Tm.app0 4 do return none
  let (C, Γ) := (e.getArg! 0, e.getArg! 1)
  if e.isAppOfArity ``Tm.pvV 4 then
    return some (← mkAppOptM ``Fml.Atom.loc #[C, Γ, e.getArg! 2, e.appArg!])
  if e.isAppOfArity ``Tm.app0 4 then
    let o := e.appArg!
    if o.isAppOfArity ``Op0.lit 3 then
      return some (← mkAppOptM ``Fml.Atom.lit #[C, Γ, o.getArg! 1, o.appArg!])
    if o.isAppOfArity ``Op0.env 2 then
      return some (← mkAppOptM ``Fml.Atom.env #[C, Γ, o.appArg!])
  return none

/-- `Fml.evalEqs goal φ` computed on the formula's syntax: each equation's
Booleans evaluated once (`evalBoolE`), the marks' proofs `rfl`.  The result
is definitionally `Fml.evalEqs goal φ`; a formula whose head does not reduce
to a connective is left under `Fml.evalEqs`. -/
private partial def evalEqsE (goal : Bool) (φ : Expr) : MetaM Expr := do
  let heads := [``Fml.tt, ``Fml.eq, ``Fml.wellFormed, ``Fml.not, ``Fml.and, ``Fml.imp, ``Fml.upd,
    ``Fml.modal, ``Fml.havoc, ``Fml.all, ``Fml.bind, ``Fml.anon, ``Fml.allocAll, ``Fml.grow]
  let φ ← whnfR φ
  let φ ← if heads.any φ.isAppOf then pure φ else whnfD φ
  let f := φ.getAppFn
  let args := φ.getAppArgs
  let last (g : Bool) : MetaM Expr := do
    return mkAppN f (args.pop.push (← evalEqsE g args.back!))
  match f.constName?, args.size with
  | some ``Fml.eq, 5 =>
    let (a, b) := (args[3]!, args[4]!)
    let ag ← mkAppM ``Bool.and #[← mkAppM ``Tm.agreeB #[a], ← mkAppM ``Tm.agreeB #[b]]
    let tot ← mkAppM ``Bool.or #[← mkAppM ``Tm.totB #[a], ← mkAppM ``Tm.totB #[b]]
    let rflT := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    -- an equation of atoms, which the closer reads by value as it stands
    -- (`CloseS.holds_eq`, `CloseS.denote_pvV`, …); a capture's own is marked
    -- (`Fml.eqCap`, `CloseS.holds_eqAtom`)
    if (← atomE? a).isSome && (← atomE? b).isSome then return φ
    if ← evalBoolE ag then
      if ← evalBoolE tot then
        let h ← mkExpectedTypeHint rflT (← mkEq (← mkAppM ``Bool.and #[ag, tot]) (mkConst ``Bool.true))
        return ← mkAppM ``Fml.eqT #[a, b, h]
      let h ← mkExpectedTypeHint rflT (← mkEq ag (mkConst ``Bool.true))
      return ← mkAppM ``Fml.eqA #[a, b, h]
    if goal then
      if ← evalBoolE (← mkAppM ``Bool.and #[← mkAppM ``Tm.pushFree #[a], ← mkAppM ``Tm.pushFree #[b]]) then
        let e ← mkAppM ``Fml.eqCap #[mkConst ``Modality.diamond, a, b]
        return (← unfoldDefinition? e).getD e
    return φ
  | some ``Fml.not, 3 => last false
  | some ``Fml.and, 4 =>
    return mkAppN f #[args[0]!, args[1]!, ← evalEqsE goal args[2]!, ← evalEqsE goal args[3]!]
  | some ``Fml.imp, 4 =>
    return mkAppN f #[args[0]!, args[1]!, ← evalEqsE false args[2]!, ← evalEqsE goal args[3]!]
  | some ``Fml.upd, 6 | some ``Fml.all, 5 | some ``Fml.bind, 6 | some ``Fml.havoc, 3
  | some ``Fml.anon, 4 | some ``Fml.allocAll, 5 | some ``Fml.grow, 3 => last goal
  | some ``Fml.tt, _ | some ``Fml.wellFormed, _ | some ``Fml.modal, _ => return φ
  | _, _ => mkAppM ``Fml.evalEqs #[toExpr goal, φ]

/-- `sol_close_unwrap` on a scoped leaf `Fml.Valid ψ`: its equations read by the
interpreter (`Fml.Valid.of_evalEqs`, `Calculus/EvalEqs.lean`, computed by
`evalEqsE`), then `holds` in every typed state (`CloseS.valid_of_holds`). -/
@[tactic Solidity.tacticSol_close_unwrap]
def evalSolCloseUnwrapS : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOf ``Solidity.Fml.Valid do throwUnsupportedSyntax
  let tag ← g.getTag
  -- the pass where every equation's Booleans reduce, else the leaf as it is
  let g₂ ← try
      let φ' ← evalEqsE true ty.appArg!
      let [g₁] ← g.apply (← mkConstWithFreshMVarLevels ``Fml.Valid.of_evalEqs) | failure
      let ty₁ ← instantiateMVars (← g₁.getType)
      g₁.replaceTargetDefEq (mkApp ty₁.appFn! φ')
    catch _ => pure g
  let gs ← g₂.apply (← mkConstWithFreshMVarLevels ``CloseS.valid_of_holds)
  for g' in gs do g'.setTag tag
  replaceMainGoal gs

/-- `sol_close_unwrap_th`: `sol_close_unwrap` with no equation strengthened
(`Fml.Valid.of_evalEqsTh`): one that reads a storage alias stays a Theory
equation, for `sol_close_denote`. -/
@[tactic Solidity.tacticSol_close_unwrap_th]
def evalSolCloseUnwrapThS : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOf ``Solidity.Fml.Valid do throwUnsupportedSyntax
  let tag ← g.getTag
  let g₂ ← try
      let φ' ← evalEqsE false ty.appArg!
      let [g₁] ← g.apply (← mkConstWithFreshMVarLevels ``Fml.Valid.of_evalEqsTh) | failure
      let ty₁ ← instantiateMVars (← g₁.getType)
      g₁.replaceTargetDefEq (mkApp ty₁.appFn! φ')
    catch _ => pure g
  let gs ← g₂.apply (← mkConstWithFreshMVarLevels ``CloseS.valid_of_holds)
  for g' in gs do g'.setTag tag
  replaceMainGoal gs

/-- Run `tac` where the goal is a scoped leaf's, else step aside. -/
def onScoped (tac : TacticM Syntax) : Tactic := fun _ => do
  unless ← Close.scopedGoal do throwUnsupportedSyntax
  evalTactic (← tac)

/-- Whether the goal reads a fresh object (`Fml.allocAll`, or the state it
grew, `State.alloc`): only then are `sol_close`'s lemmas on fresh objects
added to its sets, so a leaf with none takes the same path as without them. -/
def allocInGoal : TacticM Bool := do
  let t ← instantiateMVars (← getMainTarget)
  return (t.find? fun e => e.isConstOf ``Fml.allocAll || e.isConstOf ``State.alloc ||
    e.isConstOf ``Fml.grow || e.isConstOf ``State.adopt).isSome

/-- `sol_close`'s lemmas on a fresh object (`Fml.allocAll`), outside
`close_rw_s`: `allocInGoal` adds them. -/
def allocLemmas : TacticM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  #[``CloseS.holds_allocAll, ``CloseS.alloc_storage, ``CloseS.alloc_net,
    ``CloseS.alloc_selfBalance, ``CloseS.alloc_tx, ``CloseS.locV_alloc, ``CloseS.alloc_snd_id,
    ``CloseS.alloc_lenId, ``CloseS.alloc_readT_index,
    ``CloseS.alloc_readId_index, ``CloseS.holds_grow].mapM fun n =>
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)

/-- The extra lemmas where the goal reads a fresh object, none elsewhere. -/
def allocExtra : TacticM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  if ← allocInGoal then allocLemmas else pure #[]

/-- The steps as `sol_close_facts` and `sol_close_reads` allow: a leaf of
nested landed states (`CloseS.LandedAll`) repeats its captures' terms in each
(`externalValue` of `tests/solc/FunctionTypes.sol` passes the default 100000). -/
@[tactic Solidity.tacticSol_close_eval, tactic Solidity.tacticSol_close_mt_eval]
def evalSolCloseEvalS : Tactic := onScoped do
  let ex ← allocExtra
  if ex.isEmpty then `(tactic| simp (config := { maxSteps := 400000 }) only [close_rw_s])
  else `(tactic| simp (config := { maxSteps := 400000 }) only [close_rw_s, $ex,*])

@[tactic Solidity.tacticSol_close_facts]
def evalSolCloseFactsS : Tactic := onScoped do
  let ex ← allocExtra
  if ex.isEmpty then `(tactic|
    simp (config := { contextual := true, maxSteps := 400000 }) only [close_rw_s])
  else `(tactic|
    simp (config := { contextual := true, maxSteps := 400000 }) only [close_rw_s, $ex,*])

@[tactic Solidity.tacticSol_close_reads]
def evalSolCloseReadsS : Tactic := onScoped do
  let ex ← allocExtra
  if ex.isEmpty then `(tactic|
    simp (config := { contextual := true, maxSteps := 400000 }) only [close_rw_s, close_rw_s_last])
  else `(tactic|
    simp (config := { contextual := true, maxSteps := 400000 }) only
      [close_rw_s, close_rw_s_last, $ex,*])

@[tactic Solidity.tacticSol_close_reads_all]
def evalSolCloseReadsAllS : Tactic := onScoped do
  let ex ← allocExtra
  if ex.isEmpty then `(tactic|
    simp_all (config := { maxSteps := 400000 }) only [close_rw_s, close_rw_s_last])
  else `(tactic|
    simp_all (config := { maxSteps := 400000 }) only [close_rw_s, close_rw_s_last, $ex,*])

/-- Whether the goal or a hypothesis reads a storage alias local inside a
Theory value (`Tm.denote` of a term with `Tm.pvP`). -/
def aliasDenoteLeft : TacticM Bool := withMainContext do
  let hit (e : Expr) : Bool := (e.find? fun x =>
    x.isAppOf ``Tm.denote && (x.find? (·.isConstOf ``Tm.pvP)).isSome).isSome
  if hit (← instantiateMVars (← getMainTarget)) then return true
  for d in ← getLCtx do
    if !d.isImplementationDetail && hit (← instantiateMVars d.type) then return true
  return false

@[tactic Solidity.tacticSol_close_alias_guard]
def evalSolCloseAliasGuard : Tactic := fun _ => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOf ``Solidity.Fml.Valid do throwError "sol_close_alias_guard: not a scoped leaf"
  let hasPvP (e : Expr) : Bool := (e.find? (·.isConstOf ``Tm.pvP)).isSome
  let hit := ty.find? fun x => x.isAppOfArity ``Fml.eq 5 && hasPvP x
  unless hit.isSome do throwError "sol_close_alias_guard: no equation reads a storage alias"

macro_rules
  | `(tactic| sol_close_landed) => `(tactic| simp only [CloseS.landedAll_def])

/-- Select the quantified-premise fallback without charging ordinary leaves. -/
elab "sol_close_all_guard" : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  let rec hasAll (e : Expr) : Bool :=
    e.isAppOf ``Fml.all || (e.isAppOfArity ``Fml.and 4 &&
      (hasAll (e.getArg! 2) || hasAll (e.getArg! 3)))
  unless (ty.find? fun e => e.isAppOfArity ``Fml.imp 4 && hasAll (e.getArg! 2)).isSome do
    throwError "sol_close_quantified: no quantified premise"

/-- Open at most 128 logical constructors, reusing a captured value only
when the goal's equality identifies it. Each checked step has its own budget. -/
elab "sol_close_captures" : tactic => do
  let mut todo ← getGoals
  let mut leaves : List MVarId := []
  for _ in [0:128] do
    let g :: rest := todo | break
    setGoals [g]
    let saved ← saveState
    let ok ← tryCatchRuntimeEx (Budget.within 1000 do
        let step? ← g.withContext do
          let ty ← whnfR (← g.getType)
          if ty.isForall then return some (← `(tactic| intro _))
          if ty.isAppOf ``And then return some (← `(tactic| apply And.intro))
          if ty.isAppOf ``Exists then
            return some (← `(tactic| apply (CloseS.exists_val_eq _ _).2))
          return none
        let some step := step? | return false
        Term.withoutErrToSorry <| withoutRecover <| evalTactic step
        return true) (fun _ => pure false)
    if ok then todo := (← getUnsolvedGoals) ++ rest
    else
      saved.restore
      leaves := leaves ++ [g]
      todo := rest
  setGoals (leaves ++ todo)

/-- `sol_close_save_cases`'s first step: the Theory reads of the goal and of
the premises that read one (a `∀` premise's instances) unfolded alike to
`st.obs.word (.ref r)`; then the storage each landed on after a write
`st.write r v = some st'` read as the write's (`Storage.obs_write`), for at
most 8 writes the goal reads, and a read the leaf knows, `st.find r = some w`,
noted as the Theory's (`Storage.obs_word_ref_some`), at most 16.  Fails where
there is neither. -/
elab "sol_close_save_write" : tactic => withMainContext do
  -- cheap guard first: a write or a read of storage known, at most 256 premises
  let mut known := false
  let mut seen := 0
  for d in ← getLCtx do
    if seen == 256 then break
    seen := seen + 1
    if d.isImplementationDetail then continue
    let_expr Eq _ lhs rhs := (← instantiateMVars d.type) | continue
    if rhs.isAppOfArity ``Option.some 2 &&
        (lhs.isAppOf ``Storage.write || lhs.isAppOfArity ``Storage.find 4) then
      known := true
      break
  unless known do throwError "sol_close_save_cases: no write and no read of storage known"
  let mut hs : Array FVarId := #[]
  for d in ← getLCtx do
    if hs.size == 64 then break
    if d.isImplementationDetail then continue
    if ((← instantiateMVars d.type).find? (·.isAppOf ``Tm.denote)).isSome then
      hs := hs.push d.fvarId
  let (fs, g) ← (← getMainGoal).revert hs
  replaceMainGoal [g]
  evalTactic (← `(tactic| simp (config := { maxSteps := 100000 }) only [CloseS.denote_find,
      CloseS.denote_storage, CloseS.denote_root, CloseS.denote_at, CloseS.denote_pvV,
      Option.getD_some, Option.bind_some, CloseS.push_storage, CloseS.setLocal_storage,
      CloseS.havoc_storage, CloseS.Landed.storage_eq, CloseS.glob_storage,
      CloseS.withStorage_storage, CloseS.globG_val, State.locV_push, CloseS.push_here,
      CloseS.vden_val, Option.some.injEq, Path.index_dyn, Path.index_fixed, Path.index_map,
      CloseS.app_ref]))
  let (_, g) ← (← getMainGoal).introNP fs.size
  let mut g := g
  let mut writes := 0
  let mut reads := 0
  for d in ← g.withContext getLCtx do
    if d.isImplementationDetail then continue
    let_expr Eq _ lhs rhs := (← instantiateMVars d.type) | continue
    unless rhs.isAppOfArity ``Option.some 2 do continue
    if lhs.isAppOf ``Storage.write && writes < 8 then
      let target ← instantiateMVars (← g.getType)
      unless (target.find? fun e => e.isAppOfArity ``Storage.obs 2 &&
        e.appArg! == rhs.appArg!).isSome do continue
      let r ← g.withContext do g.rewrite target (← mkAppM ``Storage.obs_write #[d.toExpr])
      g ← g.replaceTargetEq r.eNew r.eqProof
      writes := writes + 1
    else if lhs.isAppOfArity ``Storage.find 4 && reads < 16 then
      let some pf ← g.withContext (observing? (mkAppM ``Storage.obs_word_ref_some #[d.toExpr]))
        | continue
      let (_, g') ← g.note `read pf
      g := g'
      reads := reads + 1
  if writes + reads == 0 then
    throwError "sol_close_save_cases: no write and no read of storage known"
  replaceMainGoal [g]

/-- **`selectOnSaveCons`** at a symbolic index, solkey's `\if (a1 = a2)`: a
word read after a word written (`sol_close_save_write`) is split on whether
the read goes through the write (`CloseS.copyTo_word_ite`, the paths
compared from their root, `CloseS.strip?_ref_append`): the written word where
the indices agree, the old storage's read, as the premises' instances and
the reads known read it, where they differ.  Each branch is closed as the
leaf's are; with 20000 heartbeats of its own, past which, or where a branch
stays open, it fails with the goal as it was. -/
elab "sol_close_save_cases" : tactic => do
  let saved ← saveState
  let ok ← tryCatchRuntimeEx (Budget.within 20000 do
      Term.withoutErrToSorry <| withoutRecover <| evalTactic (← `(tactic| (
        sol_close_save_write
        try simp only [CloseS.copyTo_word_ite, CloseS.strip?_ref_append, Path.strip?,
          CloseS.obs_word_prim_nil]
        repeat' split
        all_goals try simp only [Option.isSome_some, Option.isSome_none, if_true, if_false,
          Bool.false_eq_true, CloseS.uint_eq_mk, CloseS.int_eq_mk] at *
        all_goals first | decide | omega | grind [CloseS.index_uint_congr])))
      return (← getUnsolvedGoals).isEmpty) (fun _ => pure false)
  unless ok do
    saved.restore
    throwError "sol_close_save_cases: the goal stays open"

macro "sol_close_quantified_core" : tactic => `(tactic| (
    sol_close_all_guard
    sol_close_unwrap_th
    intro σ
    sol_close_eval
    all_goals try sol_close_facts
    all_goals try sol_close_reads
    all_goals try sol_close_landed
    all_goals try (intros; sol_close_reads_all)
    all_goals try (subst_vars; sol_close_reads_all)
    all_goals try intros
    all_goals try simp only [Close.exists_unit, Close.forall_unit, exists_const, forall_const] at *
    all_goals try sol_close_witness
    all_goals (repeat' (first | intro _ | apply And.intro))
    all_goals try sol_close_enrich
    all_goals try sol_close_all
    all_goals try sol_close_enrich
    all_goals try sol_close_reads_all
    sol_close_captures
    all_goals first
      | omega | assumption | rfl | grind [CloseS.index_uint_congr]
      -- a read past a write at a symbolic index (`selectOnSaveCons`)
      | sol_close_save_cases))

elab_rules : tactic
  | `(tactic| sol_close_quantified) => do
    let saved ← saveState
    -- bounded by the declaration's heartbeats, as it always was: its option
    -- of 20000 never bound it (`checkMaxHeartbeats` reads the context's
    -- limit), and the ABI scans of `Examples/Tactics/ArrayScans.lean` use
    -- most of a declaration's
    let ok ← tryCatchRuntimeEx (do
        Term.withoutErrToSorry <| withoutRecover <| evalTactic (← `(tactic| sol_close_quantified_core))
        return (← getUnsolvedGoals).isEmpty) (fun _ => pure false)
    unless ok do
      saved.restore
      throwError "sol_close_quantified: the quantified fallback left the original goal open"

macro_rules
  | `(tactic| sol_close_witness) => `(tactic| (
    (try sol_close_landed)
    intros
    refine ⟨⟨_, by decide⟩, rfl, ?_⟩
    try dsimp only))

macro_rules
  | `(tactic| sol_close_alias) => `(tactic| (
    sol_close_alias_guard
    sol_close_unwrap_th
    intro σ
    sol_close_eval
    all_goals try sol_close_facts
    all_goals try sol_close_reads
    all_goals (try simp only [CloseS.landedAll_def])
    all_goals try (intros; sol_close_reads_all)
    all_goals try (subst_vars; sol_close_reads_all)
    all_goals (try intros)
    all_goals sol_close_denote))

/-! ### A joined `if`'s values (`sol_close_join`) -/

/-- A value read as a fresh `a` and its defining fact: where `X` returns,
`∃ a, X = some a ∧ P a` holds when `P` holds of whatever it returns. -/
theorem CloseS.exists_some_of {α : Type} {X : Option α} {P : α → Prop} (ht : X.isSome = true)
    (h : ∀ a, X = some a → P a) : ∃ a, X = some a ∧ P a := by
  cases hX : X with
  | none => rw [hX] at ht; cases ht
  | some a => exact ⟨a, rfl, h a hX⟩

/-- A conditional's value, as an implication per case: what `omega` reads
with one case split each. -/
theorem CloseS.ite_eq_some_iff {α : Type} {p : Prop} [Decidable p] {x y : Option α} {z : α} :
    (if p then x else y) = some z ↔ (p → x = some z) ∧ (¬p → y = some z) := by
  by_cases h : p <;> simp only [h, if_true, if_false, true_implies, false_implies, and_true,
    true_and, not_true_eq_false, not_false_eq_true]

/-- A checked result: its check a fact, its value the result's. -/
theorem CloseS.ite_some_none_eq {α : Type} {p : Prop} [Decidable p] {y z : α} :
    (if p then some y else none) = some z ↔ p ∧ y = z := by
  by_cases h : p <;> simp only [h, if_true, if_false, Option.some.injEq, true_and, reduceCtorEq,
    false_and]

/-- A value under its own check: the check holds, so the value is the
checked one. -/
theorem CloseS.and_eq_ite_self {α : Type} {p : Prop} [Decidable p] {z a b : α} :
    (p ∧ z = if p then a else b) ↔ (p ∧ z = a) := by
  by_cases h : p <;> simp only [h, if_true, if_false, true_and, false_and]

/-- A conditional's value, as the disjunction of its cases. -/
theorem CloseS.ite_eq_iff' {α : Type} {p : Prop} [Decidable p] {x y : α} {z : α} :
    (if p then x else y) = z ↔ (p ∧ x = z) ∨ (¬p ∧ y = z) := by
  by_cases h : p <;> simp only [h, if_true, if_false, true_and, false_and, or_false,
    false_or, not_true_eq_false, not_false_eq_true]

/-- A value set to a conditional, as the disjunction of its cases. -/
theorem CloseS.eq_ite_iff' {α : Type} {p : Prop} [Decidable p] {x y : α} {z : α} :
    z = (if p then x else y) ↔ (p ∧ z = x) ∨ (¬p ∧ z = y) := by
  by_cases h : p <;> simp only [h, if_true, if_false, true_and, false_and, or_false,
    false_or, not_true_eq_false, not_false_eq_true]

theorem CloseS.uintOf_eq' (n : Int) (a : PrimTy.uint.Denote) :
    CloseS.uintOf n = a ↔ a.val = if 0 ≤ n ∧ n < uintBound then n else 0 :=
  eq_comm.trans (CloseS.eq_uintOf' n a)

theorem CloseS.intOf_eq' (n : Int) (a : PrimTy.int.Denote) :
    CloseS.intOf n = a ↔ a.val = if -intBound ≤ n ∧ n < intBound then n else 0 :=
  eq_comm.trans (CloseS.eq_intOf' n a)

/-- The words' bounds as literals, which `omega` reads. -/
theorem CloseS.uintBound_eq :
    uintBound = 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
  rfl

theorem CloseS.intBound_eq :
    intBound = 57896044618658097711785492504343953926634992332820282019728792003956564819968 :=
  rfl

/-- Whether `e` reads a conditional value (`cond`), or a conditional whose
condition the evaluation has decided away but a checked value's `ite`
remains (`if c then some v else none`, a joined `x + 1` once `brk` is known). -/
def readsCond (e : Expr) : Bool :=
  (e.find? fun x => x.isAppOfArity ``cond 4 || x.isAppOfArity ``ite 5).isSome

/-- Fails unless the goal reads a conditional value. -/
elab "sol_close_has_cond" : tactic => do
  unless readsCond (← instantiateMVars (← getMainTarget)) do
    throwError "sol_close_has_cond: no conditional value"

/-- The landed states and their witnesses cleared from the context, the
arithmetic left for `omega`. -/
elab "sol_close_clear_landed" : tactic => withMainContext do
  let mut g ← getMainGoal
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOf ``CloseS.Landed || t.isAppOf ``Nonempty || t.isAppOf ``State then
      g ← g.tryClear d.fvarId
  replaceMainGoal [g]

/-- A defining fact `h : X = some a` as `omega` reads it: an implication
per condition, a checked value its check and its integer. -/
syntax "sol_close_join_fact " ident : tactic

macro_rules
  | `(tactic| sol_close_join_fact $h:ident) => `(tactic| (
    (try simp only [Bool.cond_eq_ite, decide_eq_true_eq, decide_eq_false_iff_not,
      Bool.not_eq_true] at $h:ident)
    (try simp only [CloseS.ite_some_none_eq, CloseS.ite_eq_some_iff, Option.some.injEq,
      reduceCtorEq, imp_false, Classical.not_not] at $h:ident)
    (try simp only [CloseS.uintOf_eq', CloseS.intOf_eq'] at $h:ident)
    (try simp only [CloseS.uint_eq_iff, CloseS.int_eq_iff, CloseS.uintBound_eq,
      CloseS.intBound_eq] at $h:ident)
    (try simp only [CloseS.and_eq_ite_self, CloseS.eq_ite_iff', and_self, true_and, and_true,
      ite_true, ite_false, if_true, if_false] at $h:ident)
    -- the literal checks decided, a case's own check assumed in it
    (try simp (config := { contextual := true }) only [Int.reduceLT, Int.reduceLE, and_true,
      true_and, and_self, or_false, false_or, not_true_eq_false, false_and, and_false,
      not_false_eq_true, true_implies, implies_true, Classical.not_not] at $h:ident)))

/-- The condition of the first `if` of `e` that tests a Boolean (`b = true`,
a `bif` rewritten) and reads no bound variable. -/
def boolCondOf? (e : Expr) : Option Expr :=
  (e.find? fun x => x.isAppOfArity ``ite 5 && (x.getArg! 1).isAppOfArity ``Eq 3 &&
    ((x.getArg! 1).getArg! 0).isConstOf ``Bool && !(x.getArg! 1).hasLooseBVars &&
    !((x.getArg! 1).getArg! 1).isConstOf ``Bool.true &&
    !((x.getArg! 1).getArg! 1).isConstOf ``Bool.false).map (·.getArg! 1)

/-- The most cases `sol_close_join` splits a leaf into (`splitBoolConds`):
each split adds one, so `n` conditions cost at most this many, not `2^n`. -/
def joinMaxCases : Nat := 64

/-- The goals split on the Boolean conditions they still read, into at most
`joinMaxCases` cases in all; past them it fails. -/
def splitBoolConds : TacticM Unit := do
  let mut todo := ← getGoals
  let mut out : Array MVarId := #[]
  let mut count := todo.length
  for _ in [0:4 * joinMaxCases + 4] do
    let g :: rest := todo | break
    todo := rest
    match boolCondOf? (← instantiateMVars (← g.getType)) with
    | none => out := out.push g
    | some c =>
      setGoals [g]
      g.withContext do
        let cs ← Term.exprToSyntax c
        evalTactic (← `(tactic| by_cases hc : $cs))
        evalTactic (← `(tactic| all_goals (
          (try simp only [hc, ite_true, ite_false, if_true, if_false, Bool.false_eq_true,
            ↓reduceIte])
          (try simp only [decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not] at hc))))
      let gs ← getGoals
      count := count + gs.length - 1
      if count > joinMaxCases then
        throwError "sol_close_join: past {joinMaxCases} cases"
      todo := gs ++ todo
  unless todo.isEmpty do throwError "sol_close_join: past {joinMaxCases} cases"
  setGoals out.toList

/-- `sol_close_join`'s last cases: each Boolean condition the goal still
reads split, into at most `joinMaxCases` cases. -/
elab "sol_close_cond_cases" : tactic => do
  evalTactic (← `(tactic| all_goals (try simp only [Bool.cond_eq_ite])))
  splitBoolConds

macro_rules
  | `(tactic| sol_close_join) => `(tactic| (
    sol_close_has_cond
    repeat' (first
      | intro _
      | apply And.intro
      | (refine CloseS.exists_some_of ?_ (fun _ hX => ?_)
         rotate_left
         sol_close_join_fact hX
         rotate_left
         -- the value returns: a case per condition, the halting one refuted
         focus
           (try simp only [Bool.cond_eq_ite])
           repeat' split
           all_goals first | rfl | (exfalso; sol_close_clear_landed; grind)))
    all_goals sol_close_clear_landed
    -- what is still conditional: a case per condition
    all_goals (try sol_close_cond_cases)
    all_goals (repeat' intro _)
    all_goals first | trivial | omega | (simp_all; done) | grind))

/-! ### A joined leaf one update at a time (`sol_close_join_steps`) -/

/-- A conditional value returns where each case's does. -/
theorem CloseS.isSome_cond {α : Type} {c : Bool} {x y : Option α}
    (h₁ : c = true → x.isSome = true) (h₂ : c = false → y.isSome = true) :
    (bif c then x else y).isSome = true := by
  cases c
  · exact h₂ rfl
  · exact h₁ rfl

/-- A checked value returns where its check holds. -/
theorem CloseS.isSome_ite {α : Type} {p : Prop} [Decidable p] {x y : Option α}
    (h₁ : p → x.isSome = true) (h₂ : ¬p → y.isSome = true) :
    (if p then x else y).isSome = true := by
  by_cases hp : p
  · rw [if_pos hp]; exact h₁ hp
  · rw [if_neg hp]; exact h₂ hp

/-- The box over a value: whatever it returns, read as a fresh value and
its defining fact. -/
theorem CloseS.wp_box_optRes {α : Type} {X : Option α} {P : α → Prop} :
    Modality.box.wp (Close.optRes X) P ↔ ∀ a, X = some a → P a := by
  rw [Modality.wp_box]
  cases X with
  | none => exact ⟨fun _ a h => (nomatch h), fun _ a h => (nomatch h)⟩
  | some b => exact ⟨fun h a e => h a (by cases e; rfl), fun h a e => h a (by cases e; rfl)⟩

namespace CloseJ

/-- The leaves with at least this many joined updates (`countJoins`) take
`sol_close_join_steps` first; those with fewer, and those it does not
close, go on to `sol_close`'s join alternative.  Two: the join alternative
evaluates the leaf whole, which costs about `n³` (`n = 5` near 170 k
heartbeats, past its budget), the steps about `5 k` a join. -/
def stepsMin : Nat := 2

/-- The updates of `e` whose values are conditional (`Op3.ite`: a joined
`if`'s), counted up to `stepsMin`. -/
partial def countJoins (e : Expr) (acc : Nat) (cap : Nat := stepsMin) : Nat :=
  if acc ≥ cap then acc
  else if e.isAppOfArity ``Fml.upd 6 then
    let acc := if ((e.getArg! 4).find? (·.isConstOf ``Op3.ite)).isSome then acc + 1 else acc
    countJoins (e.getArg! 5) acc cap
  else match e with
    | .app f x => countJoins x (countJoins f acc cap) cap
    | .mdata _ b => countJoins b acc cap
    | _ => acc

/-- The most joined updates a leaf may have for `sol_close` to evaluate it
whole (its join alternative, `sol_close_quantified`, its last
alternative) where `sol_close_join_steps` did not close it: whole, each
update's rest is visited again under every rewrite above it, past the
default heartbeats from six (`docs/automation.md`, M6), and a timeout
there is not caught.  Past it, `sol_close` fails where the steps do. -/
def wholeMax : Nat := 5

/-- `tac` on `g` alone; the goals it leaves. -/
def runOn (g : MVarId) (tac : TSyntax `tactic) : TacticM (List MVarId) := do
  let saved ← getGoals
  setGoals [g]
  try
    evalTactic tac
    getGoals
  finally
    setGoals saved

/-- `omega` on `p` in the local context cut down to `keep` and what they
and `p` mention, so that a call costs the same at every step of the leaf. -/
def omegaIn (keep : Array FVarId) (p : Expr) : TacticM (Option Expr) := do
  let lctx ← getLCtx
  let mut need : FVarIdSet := {}
  let mut todo : Array FVarId := keep ++ (collectFVars {} (← instantiateMVars p)).fvarIds
  while !todo.isEmpty do
    let f := todo.back!
    todo := todo.pop
    if need.contains f then continue
    need := need.insert f
    let some d := lctx.find? f | continue
    todo := todo ++ (collectFVars {} (← instantiateMVars d.type)).fvarIds
    if let some v := d.value? then
      todo := todo ++ (collectFVars {} (← instantiateMVars v)).fvarIds
  let lctx' := lctx.foldl (init := lctx) fun l d =>
    if need.contains d.fvarId then l else l.erase d.fvarId
  let insts := (← getLocalInstances).filter fun i => need.contains i.fvar.fvarId!
  let m ← mkFreshExprMVarAt lctx' insts p
  try
    let [] ← runOn m.mvarId! (← `(tactic| omega)) | return none
    return some (← instantiateMVars m)
  catch _ => return none

/-- What is known of a fresh value `a`: `L ≤ a.val ≤ H`, and that fact. -/
abbrev Bounds := Std.HashMap FVarId (Int × Int × FVarId)

/-- `lo ≤ a.val ∧ a.val ≤ hi`. -/
def intervalP (a lo hi : Expr) : MetaM Expr := do
  let av ← mkAppM ``Subtype.val #[a]
  mkAppM ``And #[← mkAppM ``LE.le #[lo, av], ← mkAppM ``LE.le #[av, hi]]

/-- `h : p`, proved by `e`, in front of `g`. -/
def assertH (g : MVarId) (n : Lean.Name) (p e : Expr) : MetaM (FVarId × MVarId) := do
  (← g.assert n p e).intro1P

/-- `t` as a base and an integer offset (`b + k`, `b - k`, a literal `k`,
else `t + 0`). -/
def affine (t : Expr) : Option Expr × Int :=
  let lit? (e : Expr) : Option Int := do
    if e.isAppOfArity ``OfNat.ofNat 3 then
      return ((← (e.getArg! 1).rawNatLit?) : Int)
    if e.isAppOfArity ``Neg.neg 3 && (e.getArg! 2).isAppOfArity ``OfNat.ofNat 3 then
      return -((← ((e.getArg! 2).getArg! 1).rawNatLit?) : Int)
    none
  if let some k := lit? t then (none, k)
  else if t.isAppOfArity ``HAdd.hAdd 6 then
    match lit? (t.getArg! 5) with
    | some k => (some (t.getArg! 4), k)
    | none => (some t, 0)
  else if t.isAppOfArity ``HSub.hSub 6 then
    match lit? (t.getArg! 5) with
    | some k => (some (t.getArg! 4), -k)
    | none => (some t, 0)
  else (some t, 0)

/-- The integer equations of `e`. -/
partial def intEqs (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if e.isAppOfArity ``Eq 3 && (e.getArg! 0).isConstOf ``Int then acc.push e else acc
  match e with
  | .app f x => intEqs x (intEqs f acc)
  | .lam _ t b _ | .forallE _ t b _ => intEqs b (intEqs t acc)
  | .letE _ t v b _ => intEqs b (intEqs v (intEqs t acc))
  | .mdata _ b => intEqs b acc
  | _ => acc

/-- The values `a.val` is equated to in `e`, none of which reads `a`. -/
def valuesOf (a : Expr) (e : Expr) : Array Expr := Id.run do
  let isA (x : Expr) := x.isAppOfArity ``Subtype.val 3 && x.appArg! == a
  let mut out := #[]
  for x in intEqs e #[] do
    if isA (x.getArg! 1) && !(x.getArg! 2).containsFVar a.fvarId! then
      out := out.push (x.getArg! 2)
    else if isA (x.getArg! 2) && !(x.getArg! 1).containsFVar a.fvarId! then
      out := out.push (x.getArg! 1)
  return out

/-- From a defining fact `hX : X = some a`, the interval its cases give
when they are offsets of one base (KeY's join with the conditional's bounds
in the antecedent): relative to the base (`hint`) and, where the base's own
is known, absolute (`hintA`, recorded in `bounds`).  Each by `omega` from
the fact alone.  `none` where reading the fact closed the goal. -/
def addInterval (g : MVarId) (hX : FVarId) (bounds : Bounds) :
    TacticM (Option (MVarId × Bounds)) := g.withContext do
  let ty ← instantiateMVars (← hX.getType)
  unless ty.isAppOfArity ``Eq 3 do return some (g, bounds)
  let rhs := ty.getArg! 2
  unless rhs.isAppOfArity ``Option.some 2 && rhs.appArg!.isFVar do return some (g, bounds)
  let a := rhs.appArg!
  -- a copy of the fact, read as `omega` reads it
  let (_, g₂) ← assertH g `hjoin ty (mkFVar hX)
  let gs ← runOn g₂ (← `(tactic| sol_close_join_fact $(mkIdent `hjoin)))
  let [g₃] := gs | if gs.isEmpty then return none else throwError "sol_close_join_steps: a fact split"
  g₃.withContext do
    let some hkD := (← getLCtx).findFromUserName? `hjoin | return some (g₃, bounds)
    let hk := hkD.fvarId
    let done (g : MVarId) (b : Bounds) : MetaM (Option (MVarId × Bounds)) := do
      return some (← g.tryClear hk, b)
    let vs := valuesOf a (← instantiateMVars hkD.type)
    if vs.isEmpty then return ← done g₃ bounds
    let ps := vs.map affine
    let base := ps[0]!.1
    for q in ps do
      match q.1, base with
      | none, none => pure ()
      | some x, some y => unless ← withReducible (isDefEq x y) do return ← done g₃ bounds
      | _, _ => return ← done g₃ bounds
    let (iLo, iHi) := Id.run do
      let mut lo := 0
      let mut hi := 0
      for i in [0:ps.size] do
        if ps[i]!.2 < ps[lo]!.2 then lo := i
        if ps[i]!.2 > ps[hi]!.2 then hi := i
      return (lo, hi)
    let (cLo, cHi) := (ps[iLo]!.2, ps[iHi]!.2)
    let p ← intervalP a vs[iLo]! vs[iHi]!
    let some e ← omegaIn #[hk] p | return ← done g₃ bounds
    match base with
    | none =>
      let (h, g₄) ← assertH g₃ `hintA p e
      done g₄ (bounds.insert a.fvarId! (cLo, cHi, h))
    | some b =>
      let (h, g₄) ← assertH g₃ `hint p e
      let some (L, H, hb) := (if b.isAppOfArity ``Subtype.val 3 && b.appArg!.isFVar then
          bounds.get? b.appArg!.fvarId! else none) | done g₄ bounds
      g₄.withContext do
        let pA ← intervalP a (toExpr (L + cLo)) (toExpr (H + cHi))
        let some eA ← omegaIn #[h, hb] pA | done g₄ bounds
        let (hA, g₅) ← assertH g₄ `hintA pA eA
        done g₅ (bounds.insert a.fvarId! (L + cLo, H + cHi, hA))

/-- A value that must return (`X.isSome = true`): a case per condition
(`CloseS.isSome_cond`, `CloseS.isSome_ite`), a halting case refuted by
`omega` from its conditions and the absolute intervals of the values they
read. -/
partial def closeSide (g : MVarId) (bounds : Bounds) (hyps : Array FVarId := #[]) :
    TacticM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Eq 3 && (t.getArg! 1).isAppOfArity ``Option.isSome 2 do return false
  let X ← whnfR (t.getArg! 1).appArg!
  let cases (lem : Lean.Name) : TacticM Bool := do
    let gs ← try g.apply (← mkConstWithFreshMVarLevels lem) catch _ => return false
    for g' in gs do
      let (h, g'') ← g'.intro1P
      unless ← closeSide g'' bounds (hyps.push h) do return false
    return true
  if X.isAppOfArity ``cond 4 then return ← cases ``CloseS.isSome_cond
  if X.isAppOfArity ``ite 5 then return ← cases ``CloseS.isSome_ite
  if X.isAppOfArity ``Option.some 2 then return (← observing? g.refl).isSome
  if X.isAppOfArity ``Option.none 1 then
    let mut keep := hyps
    for h in hyps do
      for f in (collectFVars {} (← instantiateMVars (← h.getType))).fvarIds do
        if let some (_, _, hb) := bounds.get? f then keep := keep.push hb
    let some e ← omegaIn keep (mkConst ``False) | return false
    g.assign (← mkFalseElim t e)
    return true
  return false

/-- What one step of evaluation leaves in front, opened: binders, premises,
landed states (`CloseS.LandedAll`), and a value as a fresh `a` and its
defining fact `X = some a`: under the box whatever it returns
(`CloseS.wp_box_optRes`), under the diamond with a goal that it returns
(`CloseS.exists_some_of`).
The goals left, the main one last, and the facts. -/
partial def introFront (g : MVarId) : MetaM (List MVarId × List FVarId) := g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  if t.isForall || t.isAppOfArity ``CloseS.LandedAll 5 then
    let (_, g') ← g.intro1
    return ← introFront g'
  if t.isAppOfArity ``Modality.wp 4 && (t.getArg! 1).isConstOf ``Modality.box &&
      (t.getArg! 2).isAppOfArity ``Close.optRes 2 then
    let [g₁] ← g.apply (← mkAppM ``Iff.mpr #[← mkAppOptM ``CloseS.wp_box_optRes
        #[none, (t.getArg! 2).appArg!, t.getArg! 3]])
      | throwError "sol_close_join_steps: the box's value"
    let (fs, g₂) ← g₁.introN 2
    let (rest, hs) ← introFront g₂
    return (rest, fs[1]! :: hs)
  if t.isAppOfArity ``Exists 2 then
    match ← g.apply (← mkConstWithFreshMVarLevels ``CloseS.exists_some_of) with
    | [gS, gH] =>
      let (fs, gH') ← gH.introN 2
      let (rest, hs) ← introFront gH'
      return (gS :: rest, fs[1]! :: hs)
    | gs => throwError "sol_close_join_steps: {gs.length} goals from an existential"
  return ([g], [])

/-- The facts `introFront` named, each with its interval; the side goals,
each closed or failing.  `none` where the main goal closed. -/
def settle (gs : List MVarId) (hs : List FVarId) (bounds : Bounds) :
    TacticM (Option (MVarId × Bounds)) := do
  let some gMain := gs.getLast? | throwError "sol_close_join_steps: no goal"
  for gS in gs.dropLast do
    unless ← closeSide gS bounds do
      throwError "sol_close_join_steps: a value is not shown to return"
  let mut gM := gMain
  let mut bounds := bounds
  for h in hs do
    let some (g', b') ← addInterval gM h bounds | return none
    (gM, bounds) := (g', b')
  return some (gM, bounds)

/-- The leaf's binders and updates one at a time, the rest of the formula
held opaque (a fresh `ψ` and `rest = ψ`), so that each step evaluates one
update with `close_rw_s` and every value is named once.  Stops at the
first formula that is not a binder or an update; `none` where the goal
closed on the way. -/
partial def peel (g : MVarId) (bounds : Bounds) : TacticM (Option (MVarId × Bounds)) :=
    g.withContext do
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Solidity.holds 4 do return some (g, bounds)
  let φ ← whnfR t.appArg!
  let rest? : Option Expr :=
    if φ.isAppOfArity ``Fml.upd 6 || φ.isAppOfArity ``Fml.bind 6 then some (φ.getArg! 5)
    else if φ.isAppOfArity ``Fml.all 5 then some (φ.getArg! 4)
    else none
  let some rest := rest? | return some (g, bounds)
  -- `∀ ψ, rest = ψ → holds σ (head ψ)`, built in place (no `kabstract`)
  let ty ← withLocalDeclD `ψ (← inferType rest) fun ψ => do
    withLocalDeclD `hψ (← mkEq rest ψ) fun h => do
      mkForallFVars #[ψ, h] (mkApp t.appFn! (mkAppN φ.getAppFn (φ.getAppArgs.pop.push ψ)))
  let g' ← mkFreshExprSyntheticOpaqueMVar ty (← g.getTag)
  g.assign (mkApp2 g' rest (← mkEqRefl rest))
  let (fs, g₁) ← g'.mvarId!.introNP 2
  let (ψ, hψ) := (fs[0]!, fs[1]!)
  let gs ← runOn g₁ (← `(tactic| simp (config := { maxSteps := 400000 }) only [close_rw_s]))
  let [g₂] := gs | if gs.isEmpty then return none else
    throwError "sol_close_join_steps: a step split the goal"
  let (gs, hs) ← introFront g₂
  let some (gM, bounds) ← settle gs hs bounds | return none
  -- the rest back, by its equation
  let gM ← gM.withContext do
    let tgt ← whnfR (← instantiateMVars (← gM.getType))
    unless tgt.isAppOfArity ``Solidity.holds 4 && tgt.appArg! == mkFVar ψ do
      throwError "sol_close_join_steps: a step left {tgt}"
    gM.replaceTargetEq (mkApp tgt.appFn! rest)
      (← mkCongrArg tgt.appFn! (← mkEqSymm (mkFVar hψ)))
  peel gM bounds

/-- The leaf (`Fml.Valid ψ`) closed one update at a time (`peel`), the post
read as the updates were, then `omega` on the intervals, the defining facts'
cases only if it fails (`sol_close_finish`, within 20000 heartbeats of its
own: a false leaf fails in about the cost of a true one).  Fails where a
goal is left. -/
def closeSteps : TacticM Unit := do
  evalTactic (← `(tactic| (sol_close_unwrap; intro σ)))
  let some (g, bounds) ← peel (← getMainGoal) {} | setGoals []; return
  let gs ← runOn g (← `(tactic| sol_close_eval))
  let mut rest : Array MVarId := #[]
  for g in gs do
    let (gs', hs) ← introFront g
    if let some (g', _) ← settle gs' hs bounds then rest := rest.push g'
  setGoals rest.toList
  evalTactic (← `(tactic| all_goals first | omega | sol_skip_after 20000 sol_close_finish))
  unless (← getGoals).isEmpty do throwError "sol_close_join_steps: goals left"

/-- `sol_close_join_steps`'s budget, in thousands of heartbeats, within the
declaration's own. -/
def budget : Nat := 100000

end CloseJ

@[tactic Solidity.tacticSol_close_few_joins]
def evalSolCloseFewJoins : Tactic := fun _ => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  if CloseJ.countJoins ty 0 (CloseJ.wholeMax + 1) > CloseJ.wholeMax then
    throwError "sol_close_few_joins: more than {CloseJ.wholeMax} joined updates"

@[tactic Solidity.tacticSol_close_join_steps]
def evalSolCloseJoinSteps : Tactic := fun _ => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOf ``Solidity.Fml.Valid && CloseJ.countJoins ty 0 ≥ CloseJ.stepsMin do
    throwError "sol_close_join_steps: fewer than {CloseJ.stepsMin} joined updates"
  let saved ← saveState
  let ok ← tryCatchRuntimeEx (Budget.within CloseJ.budget do
      Term.withoutErrToSorry <| withoutRecover CloseJ.closeSteps
      pure true) (fun _ => pure false)
  unless ok do
    saved.restore
    throwError "sol_close_join_steps: the leaf did not close"

@[tactic Solidity.tacticSol_close_denote]
def evalSolCloseDenote : Tactic := fun _ => withMainContext do
  unless ← aliasDenoteLeft do throwError "sol_close_denote: no alias read left as a Theory value"
  -- the equations of Theory values in scope, back into the goal: read alike
  -- with it, nothing else rewritten (the landed states others depend on)
  let mut hs : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isEq && (ty.find? (·.isAppOf ``Tm.denote)).isSome then hs := hs.push d.fvarId
  let (_, g) ← (← getMainGoal).revert hs
  replaceMainGoal [g]
  -- read in the Theory, the alias at the path it holds: an `ensures` the
  -- frame below gave and the frame's own read alike
  evalTactic (← `(tactic| (
    simp (config := { maxSteps := 100000 }) only [CloseS.denote_len, CloseS.denote_find,
      CloseS.denote_storage, CloseS.denote_root, CloseS.denote_pvP, Option.elim_some,
      CloseS.Landed.locV_eq, CloseS.Landed.storage_eq, State.locV_push, CloseS.push_here,
      CloseS.push_there, CloseS.push_storage, CloseS.glob_storage]
    all_goals intros
    all_goals first | rfl | assumption)))

/-- Typed values occurring under projections, including dependent anonymous locals.
Inspect at most 8,192 local declarations/expression nodes and add at most
128 range facts. Unresolved types are left alone. -/
private def addRangeFacts (g : MVarId) : MetaM MVarId := g.withContext do
  let mut todo : Array Expr := #[← g.getType]
  let mut known : Array Expr := #[]
  let mut nodes := 0
  for d in ← getLCtx do
    if nodes ≥ 8192 then break
    nodes := nodes + 1
    unless d.isImplementationDetail do
      todo := todo.push d.type
      known := known.push d.type
  let unsigned ← whnfR (mkApp (mkConst ``PrimTy.Denote) (mkConst ``PrimTy.uint))
  let signed ← whnfR (mkApp (mkConst ``PrimTy.Denote) (mkConst ``PrimTy.int))
  let mut seen : Std.HashSet Expr := {}
  let mut values : Std.HashSet Expr := {}
  let mut goal := g
  let mut facts := 0
  while !todo.isEmpty && nodes < 8192 && facts < 128 do
    let e := todo.back!
    todo := todo.pop
    nodes := nodes + 1
    if seen.contains e then continue
    seen := seen.insert e
    let value? := if e.isAppOfArity ``Subtype.val 3 then some (e.getArg! 2)
      else match e with
        | .proj ``Subtype 0 v => some v
        | _ => none
    if let some v := value? then
      unless v.hasLooseBVars || v.hasMVar || values.contains v do
        values := values.insert v
        let ty ← whnfR (← inferType v)
        if ty.hasMVar then continue
        let lemma? ← if ← isDefEq ty unsigned then pure (some ``CloseS.uintRange)
          else if ← isDefEq ty signed then pure (some ``CloseS.intRange)
          else pure none
        if let some lemma := lemma? then
          let pf ← mkAppM lemma #[v]
          let ty ← inferType pf
          unless known.contains ty do
            let (_, next) ← goal.note `range pf
            goal := next
            known := known.push ty
            facts := facts + 1
    match e with
    | .app f a => todo := (todo.push f).push a
    | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
    | .letE _ t v b _ => todo := ((todo.push t).push v).push b
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return goal

/-- KeY's `exLeft` and `andLeft`, each a single-branch elimination.
Inspect at most 8,192 declarations across all scans and eliminate at most
128 witnesses/conjunctions. -/
private def exposeWitnesses (g : MVarId) : MetaM MVarId := do
  let mut goal := g
  let mut remaining := 8192
  for _ in [0:128] do
    let (selected, left) ← goal.withContext do
      let mut left := remaining
      for d in ← getLCtx do
        if left == 0 then return (none, 0)
        left := left - 1
        unless d.isImplementationDetail do
          if ← isProp d.type then
            let ty ← whnfR d.type
            if ty.isAppOf ``Exists || ty.isAppOf ``And then return (some d.fvarId, left)
      return (none, left)
    remaining := left
    let some h := selected | return goal
    let tag ← goal.getTag
    let branches ← goal.cases h
    let [branch] := branches.toList
      | throwError "sol_close_enrich: expected a single witness branch"
    goal := branch.mvarId
    goal.setTag tag
  return goal

/-- Expose intrinsic range facts and witnesses that become visible after a read.
Each operation constructs ordinary checked proofs; no arithmetic result is assumed. -/
@[tactic Solidity.tacticSol_close_enrich]
def evalSolCloseEnrichS : Tactic := fun _ => focus <| withMainContext do
  unless ← Close.scopedGoal do throwUnsupportedSyntax
  let g ← addRangeFacts (← getMainGoal)
  replaceMainGoal [g]
  evalTactic (← `(tactic| try simp_all only [CloseS.uintRange, CloseS.intRange,
    true_implies, not_true_eq_false, false_implies]))
  let some g := (← getUnsolvedGoals).head? | return
  let g ← exposeWitnesses g
  replaceMainGoal [g]
  evalTactic (← `(tactic| try simp_all only [Option.some.injEq, exists_eq_left', exists_eq',
    forall_eq', Classical.not_not]))
  let some g := (← getUnsolvedGoals).head? | return
  let g ← addRangeFacts g
  replaceMainGoal [g]

end Solidity
