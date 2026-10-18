import Solidity.Calculus.Rules
import Solidity.Calculus.RuleKit

/-!
# Each scoped taclet is the rule `Stmt.step` fires

`Calculus/Rules.lean`'s table, its lines `Rules.lean`'s, against the
strategy of `Calculus/Step.lean`: `Taclet.toStep` says the premise of
every constructor is the one `Stmt.step` builds for its statement, so the
soundness of every rule is `Stmt.Sound`'s (`Calculus/ProvesSound.lean`),
with no proof per rule.

The proof is one lemma per constructor (`Taclet.<rule>.toStep`), each its
own declaration, so that a rule added checks alone.  Most are written by
`to_step_tac`: the hole a rule writes through is taken apart, the side
conditions that compute are settled, the parts a side condition speaks of
taken apart until it does (`core_cases_part`, as today's `Uniqueness`'s
`cases_part`), and what is left closes by `rfl`, or after taking apart a
path, a location or a value the dispatcher reads (`core_brute`, which
searches).  The search runs once, under `#derive_toStep?`, which offers the
plans it found as a `#replay_toStep` table; the file keeps the table, and
its replay tries no `rfl` the search saw fail and undoes no split.  The rules
whose dispatcher branches on what no side condition decides by computing
(an array's element type, a call's arguments, a read through a hole that
is a copy, a conditional written to a member) are proved by hand first.

`RuleKit.lean` is imported for today's `Premise` and holes, which the
printers (`Calculus/Delab.lean`) read.
-/

namespace Solidity

variable {C : Contract}

/-! ## The tactics -/

section Tactics
open Lean Elab Tactic Meta

/-- The predicates a scoped side condition is stated with. -/
def coreSidePreds : List Lean.Name :=
  [``SPath.isSimple, ``Val.isSimple, ``MPath.isSimple, ``Loc.isTarget, ``Loc.isRoot,
    ``MLoc.isTarget, ``MPath.isBindable, ``Val.notTernary, ``SHole.isTarget, ``MHole.isTarget,
    ``VHole.isTarget, ``SPath.elemMapping, ``SPath.elemPrim, ``CallRet.isRets,
    ``Args.firstNonSimple, ``BinOp.accepts, ``BinOp.shortCircuits, ``Val.complexStorageRead,
    ``Src.isMemory]

/-- Settle the side conditions that compute: drop the true ones, close the
goal on a false one. -/
elab "core_settle_side" : tactic => do
  let g ← getMainGoal
  g.withContext do
  let mut g := g
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, lhs, rhs) := (← instantiateMVars d.type).eq? | continue
    unless coreSidePreds.any lhs.isAppOf do continue
    let v ← whnfD lhs
    let r ← whnfD rhs
    unless v.isConstOf ``Bool.true || v.isConstOf ``Bool.false do continue
    if v == r then
      g ← g.tryClear d.fvarId
    else
      let g' ← g.replaceLocalDeclDefEq d.fvarId (← mkEq v r)
      g'.contradiction
      replaceMainGoal []
      return
  replaceMainGoal [g]

/-- Case on the local `fv` of the main goal. -/
def coreCasesLocal (fv : FVarId) : TacticM Unit := do
  let gs ← (← getMainGoal).cases fv
  replaceMainGoal (gs.map (·.mvarId)).toList

/-- Case on the first local whose type is one of `heads`; whether there was one. -/
def coreCasesFirst (heads : List Lean.Name) : TacticM Bool := withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← whnfR (← instantiateMVars d.type)
    if heads.any t.isAppOf then
      coreCasesLocal d.fvarId
      return true
  return false

/-- Case on the hole a rule writes through. -/
elab "core_cases_hole" : tactic => do
  unless ← coreCasesFirst [``SHole, ``MHole, ``VHole] do throwError "core_cases_hole: no hole"

/-- Case on a part a side condition speaks of. -/
elab "core_cases_part" : tactic => withMainContext do
  let parts := [``Val, ``SPath, ``Loc, ``MPath, ``MLoc, ``BinOp, ``CallRet, ``Args]
  let isPart (e : Expr) : MetaM Bool := do
    let t ← whnfR (← instantiateMVars (← inferType e))
    return parts.any t.isAppOf
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, lhs, _) := (← instantiateMVars d.type).eq? | continue
    unless coreSidePreds.any lhs.isAppOf do continue
    for fv in (Lean.collectFVars {} lhs).fvarIds do
      if ← isPart (.fvar fv) then
        coreCasesLocal fv
        return
  throwError "core_cases_part: no part to case on"

/-- The parts `core_brute` splits, in the order it tries them, by the letter
a replay plan names them with. -/
def coreBruteHeads : List (Char × Lean.Name) :=
  [('S', ``SPath), ('M', ``MPath), ('L', ``Loc), ('m', ``MLoc), ('R', ``MSrc), ('V', ``Val),
   ('Z', ``ReceiverValue), ('Y', ``LoopUnwind)]

/-- The plans of consecutive goals, a run of one plan written once after
its length (`58.`: fifty-eight goals, each by `rfl`). -/
def corePlans (ps : List String) : String :=
  let runs := ps.foldl (init := ([] : List (Nat × String))) fun
    | (n, q) :: rs, p => if p == q then (n + 1, q) :: rs else (1, p) :: (n, q) :: rs
    | [], p => [(1, p)]
  String.join (runs.reverse.map fun (n, p) => if n == 1 then p else s!"{n}{p}")

/-- `rfl`, or a case split on a part the dispatcher reads (a path, a
location, a memory source, a value), `n` deep.  Returns the plan that
closed the goal: `.` for `rfl`, `S(…)` for a split on an `SPath` and the
plans of its cases (`corePlans`). -/
partial def coreBrute : Nat → TacticM String
  | 0 => do evalTactic (← `(tactic| rfl)); return "."
  | n + 1 => do
    try evalTactic (← `(tactic| rfl)); return "."
    catch _ =>
      for (c, h) in coreBruteHeads do
        let s ← saveState
        try
          unless ← coreCasesFirst [h] do continue
          let mut plans := #[]
          for g in ← getGoals do
            setGoals [g]
            plans := plans.push (← coreBrute n)
          setGoals []
          return s!"{c}({corePlans plans.toList})"
        catch _ => s.restore
      throwError "core_brute: no split closes the goal"

/-- The plan of one goal at the head of `cs`, and what follows it. -/
partial def corePlanSpan (cs : List Char) : List Char × List Char :=
  let rec go : Nat → List Char → List Char → List Char × List Char
    | 0, acc, '.' :: rest => ((acc ++ ['.']), rest)
    | d, acc, '(' :: rest => go (d + 1) (acc ++ ['(']) rest
    | 1, acc, ')' :: rest => ((acc ++ [')']), rest)
    | d + 1, acc, ')' :: rest => go d (acc ++ [')']) rest
    | d, acc, c :: rest => go d (acc ++ [c]) rest
    | _, acc, [] => (acc, [])
  go 0 [] cs

mutual
/-- `coreBrute`'s plan replayed on one goal: no `rfl` tried that the search
saw fail, no split undone. -/
partial def coreReplay : List Char → TacticM Unit
  | ['.'] => do evalTactic (← `(tactic| rfl))
  | c :: '(' :: rest => do
    let some (_, h) := coreBruteHeads.find? (·.1 == c) | throwError "core_replay: no part `{c}`"
    unless ← coreCasesFirst [h] do throwError "core_replay: no `{h}` to split"
    let left ← coreReplayGoals (← getGoals) rest
    unless left == [')'] do throwError "core_replay: `)` expected"
  | p => throwError "core_replay: no plan `{String.mk p}`"

/-- The plans of `gs`, read off the head of a plan (`corePlans`); what follows
them. -/
partial def coreReplayGoals : List MVarId → List Char → TacticM (List Char)
  | [], cs => do setGoals []; return cs
  | gs, cs => do
    let digits := cs.takeWhile Char.isDigit
    let n := if digits.isEmpty then 1 else (String.mk digits).toNat!
    let (p, rest) := corePlanSpan (cs.drop digits.length)
    if p.isEmpty then throwError "core_replay: the plan ended"
    if gs.length < n then throwError "core_replay: the plan has more goals than the proof"
    for g in gs.take n do
      setGoals [g]
      coreReplay p
    coreReplayGoals (gs.drop n) rest
end

/-- What `to_step_tac` does before it searches: the hole taken apart, the
side conditions settled, the parts they speak of taken apart until they do. -/
def toStepPrefix : TacticM Unit := do
  evalTactic (← `(tactic| (intros; (try core_cases_hole) <;> core_settle_side <;>
    (repeat' (core_cases_part <;> core_settle_side)))))

/-- A constructor's premise is `Stmt.step`'s, by a search; its plan. -/
def toStepSearch : TacticM String := do
  toStepPrefix
  let mut plans := #[]
  for g in ← getGoals do
    setGoals [g]
    plans := plans.push (← coreBrute 2)
  setGoals []
  return corePlans plans.toList

/-- A constructor's premise is `Stmt.step`'s, by the plan a search found. -/
def toStepReplay (plan : String) : TacticM Unit := do
  toStepPrefix
  let rest ← coreReplayGoals (← getGoals) plan.toList
  unless rest.isEmpty do throwError "core_replay: the plan has more goals than the proof"

elab "core_brute" : tactic => discard <| coreBrute 2

/-- A constructor's premise is `Stmt.step`'s (searches; `to_step_replay`
replays). -/
elab "to_step_tac" : tactic => discard toStepSearch

elab "to_step_replay " plan:str : tactic => toStepReplay plan.getString

/-- `Taclet.<rule>.toStep`'s statement: the constructor's statement, `Stmt.step`
of the statement the premise, the side conditions hypotheses. -/
def toStepType (c : Lean.Name) : MetaM Expr := do
  let ty ← forallTelescope (← getConstInfo c).type fun xs body => do
    let args := body.getAppArgs
    let concl ← mkEq (← mkAppM ``Stmt.step #[args[1]!, args[2]!, args[5]!]) args[6]!
    mkForallFVars xs concl
  return ty.dropAutoParams

/-- Add the lemma `c ++ suffix` of the constructor `c`, of the type `ty`,
proved by `tac` in its own heartbeat budget; what `tac` returned.  A failure
is logged (`msg`); `strict` then throws `err`, otherwise it is `none` and the
caller goes on with the next constructor. -/
def addCtorLemma {α} (c suffix : Lean.Name) (ty : TermElabM Expr) (tac : TacticM α)
    (err : MessageData) (strict : Bool := true)
    (msg : Exception → TermElabM MessageData := fun ex => pure ex.toMessageData) :
    Command.CommandElabM (Option α) :=
  Command.liftTermElabM <| withCurrHeartbeats do
    let ty ← ty
    let mvar ← mkFreshExprMVar ty
    let r ← tryCatchRuntimeEx (do
        let out ← IO.mkRef none
        let gs ← Term.withoutErrToSorry <|
          Tactic.run mvar.mvarId! do out.set (some (← tac))
        let a ← out.get
        pure (if gs.isEmpty && !(← instantiateMVars mvar).hasSorry then a else none))
      (fun ex => do logError m!"{c}: {← msg ex}"; pure none)
    let some a := r | if strict then throwError err else pure none
    addDecl (Declaration.thmDecl
      { name := c ++ suffix, levelParams := [], type := ty, value := ← instantiateMVars mvar })
    return some a

/-- The constructors of `J` without their lemma `c ++ suffix`. -/
def ctorsMissing (J suffix : Lean.Name) : Command.CommandElabM (Array Lean.Name) := do
  let some (.inductInfo ii) := (← getEnv).find? J | throwError "no inductive `{J}`"
  let env ← getEnv
  return ii.ctors.toArray.filter fun c => !env.contains (c ++ suffix)

/-- Add `c.toStep`, proved by `tac` (`addCtorLemma`). -/
def addToStep {α} (c : Lean.Name) (tac : TacticM α) (strict : Bool := true) :
    Command.CommandElabM (Option α) :=
  addCtorLemma c `toStep (toStepType c) tac m!"no proof that `{c}` is `Stmt.step`'s rule" strict

/-- `#derive_toStep? J` searches a `Taclet.<rule>.toStep` for every
constructor of `J` without one (`to_step_tac`), and offers the
`#replay_toStep` table that replays the plans it found.  Run it once, after
a rule is added; the file keeps the table. -/
elab tk:"#derive_toStep? " j:ident : command => do
  let J ← Command.liftCoreM <| realizeGlobalConstNoOverload j
  let t0 ← IO.monoMsNow
  let mut rows : Array String := #[]
  for c in ← ctorsMissing J `toStep do
    let some plan ← addToStep c toStepSearch (strict := false) | pure ()
    rows := rows.push s!"\n  {c.replacePrefix J .anonymous} \"{plan}\""
  let text := s!"#replay_toStep {j.getId}" ++ String.join rows.toList
  Command.liftTermElabM do
    logInfoAt tk m!"searched in {(← IO.monoMsNow) - t0} ms"
    Lean.Meta.Tactic.TryThis.addSuggestion tk { suggestion := .string text }

/-- `#replay_toStep J  r₁ "plan₁" …` proves `J.rᵢ.toStep` by
`to_step_replay "planᵢ"`, the plan `#derive_toStep?` found, and fails if a
constructor of `J` is then left without its lemma. -/
syntax (name := replayToStep) "#replay_toStep " ident (ppLine ident ppSpace str)* : command

elab_rules : command
  | `(#replay_toStep $j $[$cs $ps]*) => do
    let J ← Command.liftCoreM <| realizeGlobalConstNoOverload j
    for c in cs, p in ps do
      discard <| addToStep (J ++ c.getId) (toStepReplay p.getString)
    let left ← ctorsMissing J `toStep
    unless left.isEmpty do
      throwError "#replay_toStep: no lemma for {left.toList}; run `#derive_toStep? {J}`"

/-- Close `s.step k m = p` for the case of `cases h` it is, by its
constructor's lemma. -/
elab "apply_toStep " j:ident : tactic => do
  let J ← realizeGlobalConstNoOverload j
  let tag ← getMainTag
  let n := J ++ tag ++ `toStep
  evalTactic (← `(tactic| (apply $(mkIdent n) <;> assumption)))

end Tactics

/-! ## The rules proved by hand -/

section Hand

variable {k : Nat} {m : Modality} {Γ : Ctx}

theorem Taclet.storageIndexRead_unfold_rightSndIndex.toStep {x : Ty} {lhs : SHole C Γ x}
    {R : RefTy} {kp : PrimTy} {it : IndexTy R kp x} {sp : SPath C Γ (Ty.ref R)} {nse : Val C Γ kp}
    (h1 : sp.isSimple = true) (h2 : nse.isSimple = false) (h3 : lhs.isTarget = true) :
    Stmt.step k m (lhs.fill (SPath.loc (Loc.index it sp nse))) =
      Premise.unfold (Prog.cons (Stmt.declLocal kp (Var.fresh "ie" k) (some nse))
        (Prog.cons (lhs.up.fill (SPath.loc (Loc.index it sp.up (Val.simple (Simple.local Idx.here)))))
          Prog.nil)) Ext.refl.push := by
  cases lhs with
  | «local» i =>
    cases nse <;> (try contradiction) <;>
      (dsimp only [Stmt.step, SHole.fill]; simp only [localStep, SHole.readStep, h1, if_true]) <;> rfl
  | rebind i =>
    cases nse <;> (try contradiction) <;>
      (dsimp only [Stmt.step, SHole.fill]; simp only [rebindStep, SHole.readStep, h1, if_true]) <;> rfl
  | copy l hm =>
    cases l with
    | root => cases nse <;> (try contradiction) <;>
        (dsimp only [Stmt.step, SHole.fill]; simp only [assignStep, SHole.readStep, h1, if_true]) <;> rfl
    | field b f hf =>
      simp only [SHole.isTarget, Loc.isTarget] at h3
      cases nse <;> (try contradiction) <;>
        (dsimp only [Stmt.step, SHole.fill]
         simp only [assignStep, copyStep, SHole.readStep, h1, h3, if_true]) <;> rfl
    | index it' b i =>
      simp only [SHole.isTarget, Loc.isTarget, Bool.and_eq_true] at h3
      obtain ⟨hb, hi⟩ := h3
      cases i <;> (try contradiction) <;> cases nse <;> (try contradiction) <;>
        (dsimp only [Stmt.step, SHole.fill]
         simp only [assignStep, copyStep, SHole.readStep, h1, hb, if_true]) <;> rfl

theorem Taclet.ternaryToIf.toStep {p : PrimTy} {lhs : VHole C Γ p} {se : Simple C Γ .bool}
    {thenExpr elseExpr : Val C Γ p} (h : lhs.isTarget = true) :
    Stmt.step k m (lhs.fill ((Val.simple se).ternary thenExpr elseExpr)) =
      Premise.unfold (Prog.cons (Stmt.ite (Val.simple se) (Prog.cons (lhs.fill thenExpr) Prog.nil)
        (Prog.cons (lhs.fill elseExpr) Prog.nil)) Prog.nil) Ext.refl := by
  cases lhs with
  | «local» => rfl
  | store l => cases l with
    | root => rfl
    | field b =>
      cases hb : b.isSimple <;> dsimp only [Stmt.step, VHole.fill] <;> simp only [assignStep, hb] <;> rfl
    | index _ b i =>
      cases hb : b.isSimple <;> dsimp only [Stmt.step, VHole.fill] <;> simp only [assignStep, hb] <;>
        (try cases i) <;> rfl
  | mem l =>
    simp only [VHole.isTarget] at h
    cases l with
    | field b f hf => cases b <;> (try contradiction) <;> rfl
    | index a b i =>
      cases b <;> cases i <;> first | rfl | (simp only [MLoc.isTarget, MPath.isSimple, Val.isSimple, Bool.and_false, Bool.false_and,
          Bool.false_eq_true] at h)

theorem Taclet.ternaryCaptureCond.toStep {p : PrimTy} {lhs : VHole C Γ p} {nse : Val C Γ .bool}
    {thenExpr elseExpr : Val C Γ p} (h1 : nse.isSimple = false) (h : lhs.isTarget = true) :
    Stmt.step k m (lhs.fill (nse.ternary thenExpr elseExpr)) =
      Premise.unfold (Prog.cons (Stmt.declLocal .bool (Var.fresh "se" k) (some nse))
        (Prog.cons (lhs.up.fill ((Val.simple (Simple.local Idx.here)).ternary thenExpr.up elseExpr.up))
          Prog.nil)) Ext.refl.push := by
  cases lhs with
  | «local» => cases nse <;> (try contradiction) <;> rfl
  | store l => cases l with
    | root => cases nse <;> (try contradiction) <;> rfl
    | field b =>
      cases hb : b.isSimple <;> cases nse <;> (try contradiction) <;>
        dsimp only [Stmt.step, VHole.fill] <;> simp only [assignStep, hb] <;> rfl
    | index _ b i =>
      cases hb : b.isSimple <;> cases nse <;> (try contradiction) <;>
        dsimp only [Stmt.step, VHole.fill] <;> simp only [assignStep, hb] <;> (try cases i) <;> rfl
  | mem l =>
    simp only [VHole.isTarget] at h
    cases l with
    | field b f hf => cases b <;> (try contradiction) <;> cases nse <;> (try contradiction) <;> rfl
    | index a b i =>
      cases b <;> cases i <;>
        first
          | (simp only [MLoc.isTarget, MPath.isSimple, Val.isSimple, Bool.and_false, Bool.false_and,
          Bool.false_eq_true] at h; done)
          | (cases nse <;> (try contradiction) <;> rfl)

theorem Taclet.memoryFieldWrite_unfold_leftFst.toStep {s : Name} {nmp : MPath C Γ (Ty.struct s)}
    {fld : Name} {T : Ty} {hfld : C.fieldType s fld = some T} {msrc : MSrc C Γ T}
    (h : nmp.isSimple = false) :
    Stmt.step k m (Stmt.assignMem (MLoc.field nmp fld hfld) msrc) =
      Premise.unfold
        (Prog.cons (Stmt.declMem (RefTy.struct s) (Var.fresh "mv" k) (some (MRhs.alias nmp)) rfl
          (MRhs.alias nmp).mapFree)
          (Prog.cons (Stmt.assignMem (MLoc.field (MPath.var Idx.here (MRhs.alias nmp).mapFree) fld hfld)
            msrc.up) Prog.nil)) Ext.refl.push := by
  cases nmp <;> (try contradiction) <;> cases msrc <;> rfl

theorem Taclet.storagePushLengthSave.toStep {E : Ty} {parr : SPath C Γ E.array}
    {hd : ((none : Option (Src C Γ E)).isSome || E.defaultOkS) = true}
    (h1 : parr.isSimple = true) (h2 : parr.elemPrim = true) :
    Stmt.step k m (Stmt.push parr none hd) =
      Premise.update (Upd.nil.snoc (UpdElem.storage
        (Tms.STerm.pushSlot Tms.STerm.storage parr.lower E))) := by
  show pushStep k parr none hd = _
  simp only [pushStep, h1, h2]
  rfl

theorem Taclet.storagePushLengthSaveReferenceElement.toStep {E : Ty} {rarr : SPath C Γ E.array}
    {hd : ((none : Option (Src C Γ E)).isSome || E.defaultOkS) = true}
    (h1 : rarr.isSimple = true) (h2 : rarr.elemPrim = false) (h3 : rarr.elemMapping = false) :
    Stmt.step k m (Stmt.push rarr none hd) =
      Premise.update (Upd.nil.snoc (UpdElem.storage
        (Tms.STerm.pushSlot Tms.STerm.storage rarr.lower E))) := by
  show pushStep k rarr none hd = _
  simp only [pushStep, h1, h2, h3]
  rfl

theorem Taclet.storagePushLengthSaveMappingElement.toStep {E : Ty} {marr : SPath C Γ E.array}
    {hd : ((none : Option (Src C Γ E)).isSome || E.defaultOkS) = true}
    (h1 : marr.isSimple = true) (h2 : marr.elemMapping = true) :
    Stmt.step k m (Stmt.push marr none hd) =
      Premise.update (Upd.nil.snoc (UpdElem.storage
        (Tms.STerm.pushSlot Tms.STerm.storage marr.lower E))) := by
  have hp : marr.elemPrim = false := by
    cases E with
    | prim p => cases h2
    | ref R => rfl
  show pushStep k marr none hd = _
  simp only [pushStep, h1, hp, h2]
  rfl

theorem Taclet.storageLocalRootPushBind.toStep {R : RefTy} {lsv : Idx Γ (.alias R)}
    {darr : SPath C Γ (.array (.ref R))} {hd : (Ty.ref R).defaultOkS = true}
    (h1 : darr.isSimple = true) (h2 : darr.elemMapping = false) :
    Stmt.step k m (.rebind lsv (.push darr hd)) = .update (Upd.pushBind lsv darr) := by
  show rebindStep k lsv (.push darr hd) = _
  simp only [rebindStep, h1, h2]
  rfl

theorem Taclet.storageLocalRootPushBindMappingElement.toStep {R : RefTy} {lsv : Idx Γ (.alias R)}
    {marr : SPath C Γ (.array (.ref R))} {hd : (Ty.ref R).defaultOkS = true}
    (h1 : marr.isSimple = true) (h2 : marr.elemMapping = true) :
    Stmt.step k m (.rebind lsv (.push marr hd)) = .update (Upd.pushBindMapping lsv marr) := by
  show rebindStep k lsv (.push marr hd) = _
  simp only [rebindStep, h1, h2]
  rfl

/-- `sp1.push(sp2)` copies directly when both storage paths are simple. -/
theorem Taclet.storagePushValueCopySource.toStep {R : RefTy}
    {sp1 : SPath C Γ (.array (.ref R))} {sp2 : SPath C Γ (.ref R)}
    {hm : (Ty.ref R).mapFree = true} (h1 : sp1.isSimple = true) (h2 : sp2.isSimple = true) :
    Stmt.step k m (.push sp1 (some (.copy sp2 hm)) rfl) =
      .upd1 (UpdElem.push sp1 (.copy sp2 hm)) := by
  show pushStep k sp1 (some (.copy sp2 hm)) rfl = _
  simp only [pushStep, h1, h2, if_pos]

/-- `sp.push(mv)` copies a memory variable's value at the old array length. -/
theorem Taclet.storagePushMemoryCopySource.toStep {R : RefTy}
    {sp : SPath C Γ (.array (.ref R))} {mv : Idx Γ (.mem R)}
    {hmv : (Ty.ref R).mapFree = true} (hsp : sp.isSimple = true) :
    Stmt.step k m (.push sp (some (.copyMem (.var mv hmv))) rfl) =
      .upd1 (UpdElem.push sp (.copyMem (.var mv hmv))) := by
  show pushStep k sp (some (.copyMem (.var mv hmv))) rfl = _
  simp only [pushStep, hsp, MPath.isSimple, if_true]

/-- `sp.push(nsp)` binds a complex reference source to its fresh alias. -/
theorem Taclet.storagePushValue_unfold_rightFstReferenceArgument.toStep {R : RefTy}
    {sp : SPath C Γ (.array (.ref R))} {nsp : SPath C Γ (.ref R)}
    {hm : (Ty.ref R).mapFree = true} (h1 : sp.isSimple = true) (h2 : nsp.isSimple = false) :
    Stmt.step k m (.push sp (some (.copy nsp hm)) rfl) =
      .captureSP (.fresh "source" k) nsp
        (.push sp.up (some (.copy (.alias .here) hm)) rfl) := by
  show pushStep k sp (some (.copy nsp hm)) rfl = _
  simp only [pushStep, h1, h2, Bool.false_eq_true, if_true, if_false]

/-- `sp.push(nsp)` reads its complex primitive source once into `source`. -/
theorem Taclet.storagePushValue_unfold_rightFstPrimitiveArgument.toStep {p : PrimTy}
    {sp : SPath C Γ (.array (.prim p))} {nsp : SPath C Γ (.prim p)}
    (h1 : sp.isSimple = true) (h2 : nsp.isSimple = false) :
    Stmt.step k m (.push sp (some (.val nsp.primitiveRead)) rfl) =
      .capture p (.fresh "source" k) nsp.primitiveRead
        (.push sp.up (some (.val (.simple (.local .here)))) rfl) := by
  cases nsp with
  | loc l =>
    show pushStep k sp (some (.val (.read l))) rfl = _
    simp only [pushStep, h1, SPath.primitiveRead, Val.complexStorageRead, h2,
      Bool.not_false, if_true]

/-- `sp.push(nse)` captures an ordinary expression rather than a complex storage path. -/
theorem Taclet.storagePushValue_unfold_rightSndArgument.toStep {p : PrimTy}
    {sp : SPath C Γ (.array (.prim p))} {nse : Val C Γ p}
    (h1 : sp.isSimple = true) (h2 : nse.isSimple = false)
    (h3 : nse.complexStorageRead = false) :
    Stmt.step k m (.push sp (some (.val nse)) rfl) =
      .capture p (fse k) nse (.push sp.up (some (.val (.simple (.local .here)))) rfl) := by
  cases nse <;> (try contradiction) <;>
    (show pushStep k sp (some (.val _)) rfl = _
     simp only [pushStep, h1, h3, Bool.false_eq_true, if_true, if_false])

/-- `v = sp.push()` updates directly only when its receiver is simple. -/
theorem Taclet.storageLocalPrimitivePushBind.toStep {p : PrimTy} {v : Idx Γ (.val p)}
    {sp : SPath C Γ (.array (.prim p))} (h : sp.isSimple = true) :
    Stmt.step k m (.assignLocalPush v sp) = .update (Upd.pushBindPrim v sp) := by
  show assignLocalPushStep k v sp = _
  simp only [assignLocalPushStep, h, if_pos]

/-- `v = nsp.push()` first binds the complex receiver to a fresh alias. -/
theorem Taclet.localValuePush_unfold_leftFstReceiver.toStep {p : PrimTy}
    {v : Idx Γ (.val p)} {nsp : SPath C Γ (.array (.prim p))} (h : nsp.isSimple = false) :
    Stmt.step k m (.assignLocalPush v nsp) =
      .captureSP (fsp k) nsp (.assignLocalPush v.there (.alias .here)) := by
  show assignLocalPushStep k v nsp = _
  simp only [assignLocalPushStep, h, Bool.false_eq_true, if_false]

theorem Taclet.storagePopSave.toStep {E : Ty} {darr : SPath C Γ E.array}
    (h1 : darr.isSimple = true) (h2 : darr.elemMapping = false) :
    Stmt.step k m (Stmt.pop darr) =
      Premise.update (Upd.nil.snoc (UpdElem.storage
        (Tms.STerm.pop Tms.STerm.storage darr.lower))) := by
  show popStep k darr = _
  simp only [popStep, h1, h2]
  rfl

theorem Taclet.storagePopSaveMappingElement.toStep {E : Ty} {marr : SPath C Γ E.array}
    (h1 : marr.isSimple = true) (h2 : marr.elemMapping = true) :
    Stmt.step k m (Stmt.pop marr) =
      Premise.update (Upd.nil.snoc (UpdElem.storage
        (Tms.STerm.shrink Tms.STerm.storage marr.lower))) := by
  show popStep k marr = _
  simp only [popStep, h1, h2]
  rfl

/-- A call whose arguments are all simple is inlined, whatever it returns. -/
theorem Premise.expandCall_step {f : Name} {ps : Ctx} {args : Args C Γ ps} {rs Γ' : Ctx}
    {ret : CallRet Γ rs Γ'} {Γf : Ctx} {body : Prog C (rs ++ ps) Γf}
    (h1 : args.firstNonSimple = none) :
    Stmt.step k m (Stmt.call f args ret body) = Premise.expandCall k args ret body := by
  simp only [Args.firstNonSimple, Option.map_eq_none_iff] at h1
  cases ret <;> (dsimp only [Stmt.step]; simp only [callStep, h1]) <;> rfl

theorem Taclet.functionBodyExpand.toStep {f : Name} {ps : Ctx} {args : Args C Γ ps} {rs Γ' : Ctx}
    {ret : CallRet Γ rs Γ'} {Γf : Ctx} {body : Prog C (rs ++ ps) Γf}
    (h1 : args.firstNonSimple = none) (_ : ret.isRets = true) :
    Stmt.step k m (Stmt.call f args ret body) = Premise.expandCall k args ret body :=
  Premise.expandCall_step h1

theorem Taclet.internalCallExpand.toStep {f : Name} {ps : Ctx} {args : Args C Γ ps} {rs Γ' : Ctx}
    {ret : CallRet Γ rs Γ'} {Γf : Ctx} {body : Prog C (rs ++ ps) Γf}
    (h1 : args.firstNonSimple = none) (_ : ret.isRets = false) :
    Stmt.step k m (Stmt.call f args ret body) = Premise.expandCall k args ret body :=
  Premise.expandCall_step h1

theorem Taclet.whileInvariantBox.toStep {Γ₁ : Ctx} {body : Prog C Γ Γ₁}
    {xs : List ((t : LTy) × Idx Γ t)} {hv : Bool} {dec : Option (Val C Γ .uint)}
    {cond inv : Val C Γ .bool} {brk : Bool} {qs : List (LoopQ C Γ)}
    (hf : body.frame = some (xs, hv)) :
    Stmt.step k .box (Stmt.loop (LoopAnn.inv inv dec brk qs) cond body) =
      Premise.inv (invFml inv qs) (loopBreak brk cond) xs hv
        (Upd.nil.decl (Var.fresh "se" k) (Rhs.val cond.lower))
        (Fml.eqD (Tms.Term.pv (p := .bool) Idx.here) (Tms.Term.litB true))
        (Fml.eqD (Tms.Term.pv (p := .bool) Idx.here) (Tms.Term.litB false)) Ext.refl
        Ext.refl.push body (invFml inv qs) := by
  dsimp only [Stmt.step]
  simp only [loopStep, hf]

theorem Taclet.whileInvariantDiamond.toStep {Γ₁ : Ctx} {body : Prog C Γ Γ₁}
    {xs : List ((t : LTy) × Idx Γ t)} {hv : Bool} {cond inv : Val C Γ .bool} {dec : Val C Γ .uint}
    {brk : Bool} {qs : List (LoopQ C Γ)} (hf : body.frame = some (xs, hv)) (hq : qs = []) :
    Stmt.step k .diamond (Stmt.loop (LoopAnn.inv inv (some dec) brk qs) cond body) =
      Premise.inv (invFml inv qs) none xs hv
        ((Upd.nil.decl (Var.fresh "ie" k) (Rhs.val (p := .uint) dec.lower)).decl (Var.fresh "se" k)
          (Rhs.val (p := .bool) cond.lower))
        (Fml.eqD (Tms.Term.pv (p := .bool) Idx.here) (Tms.Term.litB true))
        (Fml.eqD (Tms.Term.pv (p := .bool) Idx.here) (Tms.Term.litB false)) Ext.refl.push
        Ext.refl.push body.up
        ((invFml inv.up (List.map LoopQ.up qs)).and
          (Fml.upd .diamond (Upd.nil.decl (Var.fresh "se" k) (Rhs.val (p := .bool) cond.up.lower))
            ((Fml.eqD (Tms.Term.pv (p := .bool) Idx.here) (Tms.Term.litB true)).imp
              ((Fml.eqD (Tms.Term.binop .le .uint (Tms.Term.nat 0) dec.up.up.lower)
                  (Tms.Term.litB true)).and
                (Fml.eqD (Tms.Term.binop .lt .uint dec.up.up.lower (Tms.Term.pv (p := .uint) Idx.here.there))
                  (Tms.Term.litB true)))))) := by
  subst hq
  dsimp only [Stmt.step]
  simp only [loopStep, hf]
  rfl

theorem LeanTaclet.whileClose.toStep {Γ₁ : Ctx} {body : Prog C Γ Γ₁} {inv : Val C Γ .bool}
    {dec : Option (Val C Γ .uint)} {cond : Val C Γ .bool} {brk : Bool} {qs : List (LoopQ C Γ)}
    (hf : body.frame = none) :
    Stmt.step k m (Stmt.loop (LoopAnn.inv inv dec brk qs) cond body) = Premise.done false := by
  dsimp only [Stmt.step]
  simp only [loopStep, hf]

theorem LeanTaclet.whileNoVariantDiamond.toStep {Γ₁ : Ctx} {body : Prog C Γ Γ₁}
    {inv cond : Val C Γ .bool} {dec : Option (Val C Γ .uint)} {brk : Bool} {qs : List (LoopQ C Γ)}
    (hf : body.frame.isSome = true) (hd : (dec.isNone || !qs.isEmpty) = true) :
    Stmt.step k .diamond (Stmt.loop (LoopAnn.inv inv dec brk qs) cond body) = Premise.done false := by
  obtain ⟨⟨xs, hv⟩, hfr⟩ := Option.isSome_iff_exists.mp hf
  dsimp only [Stmt.step]
  cases dec with
  | none => cases qs <;> simp only [loopStep, hfr]
  | some =>
    cases qs with
    | nil => simp only [Option.isNone_some, List.isEmpty_nil, Bool.not_true, Bool.or_self,
        Bool.false_eq_true] at hd
    | cons => simp only [loopStep, hfr]

theorem LeanTaclet.functionCallArgCapture.toStep {f : Name} {ps : Ctx} {args : Args C Γ ps}
    {rs Γ' : Ctx} {ret : CallRet Γ rs Γ'} {Γf : Ctx} {body : Prog C (rs ++ ps) Γf} {p : PrimTy}
    {v : Val C Γ p} {as' : Args C (.val p :: Γ) ps} (hcap : Args.capture args = some ⟨p, v, as'⟩) :
    Stmt.step k m (Stmt.call f args ret body) = Premise.argCapture k f p v as' ret body := by
  cases ret <;> (dsimp only [Stmt.step]; simp only [callStep, hcap]) <;> rfl

end Hand

/-! The plans `#derive_toStep? Taclet` and `#derive_toStep? LeanTaclet` found:
a count of goals the prefix leaves, each closed by `rfl`. -/

#replay_toStep Taclet
  storageFieldRead_unfold_rightFst "14."
  storageIndexRead_unfold_rightFst "14."
  storageFieldRead_unfold_rightSndResult "8."
  storageIndexRead_unfold_rightSndResult "8."
  storageFieldWrite_unfold_leftFst "60."
  storageFieldWriteStorageRef_unfold_leftFst "2."
  storageIndexWriteCaptureAllComplexRecv "60."
  storageIndexWriteStorageRefCaptureAllComplexRecv "2."
  storageIndexWriteCaptureAllNonSimpleIndex "1800."
  storageIndexWriteStorageRefCaptureAllNonSimpleIndex "60."
  storageRootWriteValueRhsCapture "29."
  fieldWriteValueRhsCapture "58."
  indexWriteValueRhsCapture "58."
  storageFieldDelete_unfold_leftFst "2."
  storageIndexDelete_unfold_leftFst "2."
  storageIndexDeleteNonSimpleIndexCapture "60."
  localValueDeclInitDrop "."
  valueDeclSkip "."
  storageLocalDeclInitDrop "."
  storageLocalDeclSkip "."
  memoryLocalDeclInitDrop "."
  memoryReferenceDeclFreshAlloc "."
  localValueAssign "."
  storageRootReadSelect "."
  storageFieldReadFind "2."
  storageIndexReadMappingFind "2."
  storageIndexReadArrayFind "2."
  storageRootWriteStore "."
  storageRootWriteCopySource "2."
  storageFieldReadStoreRoot "2."
  storageIndexReadMappingStoreRoot "2."
  storageIndexReadArrayStoreRoot "2."
  storageFieldWriteSave "2."
  storageFieldWriteCopySource "4."
  storageIndexWriteMappingSave "2."
  storageIndexWriteArraySave "2."
  storageIndexWriteMappingCopySource "4."
  storageIndexWriteArrayCopySource "4."
  storageLocalRootRebind "2."
  storageFieldReadBindLocalRoot "2."
  storageIndexReadMappingBindLocalRoot "2."
  storageIndexReadArrayBindLocalRoot "2."
  storageIndexReadArrayBindLocalRootMappingElement "2."
  storageRootDelete "."
  storageFieldDelete "2."
  storageIndexDelete "2."
  storageIndexArrayDelete "2."
  storageLengthRead "2."
  storageLengthRead_unfold_rightFst "2."
  memoryLengthRead "."
  memoryLengthRead_unfold_rightFst "."
  binopAssignment "23."
  binopUnfoldLeft "688."
  binopUnfoldRight "630."
  logicalAndShortCircuitRhs "29."
  logicalOrShortCircuitRhs "29."
  unopAssignment "."
  unopCapture "30."
  localOpAssign "."
  storageRootOpAssign "."
  storageFieldOpAssign "2."
  storageIndexMappingOpAssign "2."
  storageIndexArrayOpAssign "2."
  memoryFieldOpAssign "."
  memoryIndexArrayOpAssign "."
  storageFieldOpAssignUnfoldLeftFst "2."
  storageIndexOpAssignUnfoldLeftFst "2."
  memoryFieldOpAssignUnfoldLeftFst "."
  memoryIndexOpAssignUnfoldLeftFst "."
  compoundAssignValueRhsCapture "30."
  localIncrement "."
  storageRootIncrement "."
  storageFieldIncrement "2."
  storageIndexIncrement "2."
  memoryFieldIncrement "."
  memoryIndexArrayIncrement "."
  storageFieldIncrementUnfoldLeftFst "2."
  storageIndexIncrementUnfoldLeftFst "2."
  memoryFieldIncrementUnfoldLeftFst "."
  memoryIndexIncrementUnfoldLeftFst "."
  localAssignIncrement "."
  storageRootIncrementAssignment "."
  storageFieldIncrementAssignment "2."
  storageIndexIncrementAssignment "2."
  memoryFieldIncrementAssignment "."
  memoryIndexArrayIncrementAssignment "."
  storagePushAddAssign "2."
  storagePushSubAssign "2."
  storagePushMulAssign "2."
  storagePushDivAssign "2."
  storagePushModAssign "2."
  storagePushPreincrement "2."
  storagePushPostincrement "2."
  storagePushPredecrement "2."
  storagePushPostdecrement "2."
  pushCompoundAssignValueRhsCapture "30."
  storagePushValueSave "2."
  storagePushValue_unfold_leftFstReceiver "2."
  storagePush_unfold_leftFstReceiver "2."
  storagePop_unfold_leftFstReceiver "2."
  storagePushValue_unfold_leftCallReceiver "Z(2.)"
  storagePush_unfold_leftCallReceiver "."
  storagePop_unfold_leftCallReceiver "."
  storageLocalRootPush_unfold_leftFstReceiver "2."
  transfer_unfold_leftFstReceiver "30."
  transfer_unfold_rightSndArgument "30."
  transferNoCallbackBox "."
  send_unfold_leftFstReceiver "30."
  send_unfold_rightSndArgument "30."
  sendNoCallbackBox "."
  sendNoCallbackDiamond "."
  memoryFieldRead_unfold_rightFst "4."
  memoryIndexRead_unfold_rightFst "4."
  memoryIndexRead_unfold_rightSndIndex "120."
  memoryFieldRead "."
  memoryIndexReadArrayValue "."
  memoryRootRebind "."
  memoryFieldReadAliasRoot "."
  memoryIndexReadArrayMemory "."
  memoryFieldWrite "."
  memoryIndexWriteArray "."
  memoryFieldWriteCopy "3."
  memoryIndexWriteCopy "3."
  memoryIndexWriteCaptureAllComplexRecv "."
  memoryIndexWriteMemRefCaptureAllComplexRecv "."
  memoryIndexWriteCaptureAllNonSimpleIndex "30."
  memoryIndexWriteMemRefCaptureAllNonSimpleIndex "30."
  memoryFieldWriteUnfoldSource "29."
  memoryIndexWriteUnfoldSource "29."
  memoryRootDeleteFreshRebind "."
  memoryFieldDeletePrimitive "."
  memoryFieldDeleteReference "."
  memoryIndexDeletePrimitive "."
  memoryIndexDeleteReference "."
  memoryFieldDelete_unfold_leftFst "."
  memoryIndexDelete_unfold_leftFst "."
  memoryIndexDeleteNonSimpleIndexCapture "30."
  memoryArrayFreshAlloc "."
  newArrayCapture "."
  memoryStorageCopy "2."
  memoryStorageCopyUnfold "2."
  memoryToStorageStoreRoot "."
  memoryToStorageFieldCopyRoot "2."
  memoryToStorageIndexMappingCopyRoot "2."
  memoryToStorageIndexArrayCopyRoot "2."
  memoryToStorageField_unfold_leftFst "2."
  memoryToStorageIndexCaptureAllComplexRecv "2."
  memoryToStorageIndexCaptureAllNonSimpleIndex "60."
  ifElseUnfold "29."
  ifElseSplit "."
  requireConditionCapture "29."
  requireSimple "."
  assertConditionCapture "29."
  assertSimple "."
  revertBox "."
  revertDiamond "."
  tryCallNoCallbackBox "."
  blockEmpty "."
  whileUnwind "V(8Y(2.))"

/-- A memory snapshot source writes through the same typed save update. -/
theorem LeanTaclet.storageMemorySourceSave.toStep {T : Ty} {loc : Loc C Γ T}
    {src : Src C Γ T} (hmem : src.isMemory = true) :
    Stmt.step k m (.assign loc src) = .save loc src := by
  cases src with
  | val v => cases hmem
  | copy p hm => cases hmem
  | fixedCopy p shape hm => cases hmem
  | copyMem p => cases loc <;> rfl

/-- A compatible fixed-array source uses the native typed save update. -/
theorem LeanTaclet.storageFixedCopySave.toStep {T : Ty} {loc : Loc C Γ T}
    {src : Src C Γ T} (hshape : src.isFixedCopy = true) :
    Stmt.step k m (.assign loc src) = .save loc src := by
  cases src with
  | val | copy | copyMem => cases hshape
  | fixedCopy => cases loc <;> rfl

/-- A converted fixed-array snapshot is pushed by the ordinary push symbol. -/
theorem LeanTaclet.pushFixedCopySave.toStep {E : Ty} {sp : SPath C Γ (.array E)}
    {src : Src C Γ E} (hshape : src.isFixedCopy = true) (hsp : sp.isSimple = true) :
    Stmt.step k m (.push sp (some src) rfl) = .upd1 (UpdElem.push sp src) := by
  cases src with
  | val | copy | copyMem => cases hshape
  | fixedCopy => simp only [Stmt.step, pushStep, hsp, ↓reduceIte]

#replay_toStep LeanTaclet
  addmodAssignment "."
  mulmodAssignment "."
  pushMemorySourceCapture "2."
  pushCompoundUnfoldReceiver "2."
  pushIncrementUnfoldReceiver "2."
  tryCallDiamond "."
  transferDiamond "."
  loopExit "."

/-! ## The rule `Stmt.step` fires -/

/-- **Each taclet is the rule the strategy fires on its statement**: its
premise is `Stmt.step`'s, so it is sound by `Stmt.Sound`. -/
theorem Taclet.toStep {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (h : Taclet C k m s p) : s.step k m = p := by
  cases h <;> apply_toStep Taclet

/-- The rules solkey does not have are `Stmt.step`'s too. -/
theorem LeanTaclet.toStep {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (h : LeanTaclet C k m s p) : s.step k m = p := by
  cases h <;> apply_toStep LeanTaclet

/-- **Every rule of the calculus is the one `Stmt.step` fires**: at most one
premise per statement, the dispatcher's. -/
theorem Rule.toStep {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} : Rule C k m s p → s.step k m = p
  | .key d => d.toStep
  | .lean d => d.toStep

/-- Two rules on one statement leave the same premise. -/
theorem Rule.premise_unique {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p p' : Premise C Γ Γ'} (d : Rule C k m s p) (d' : Rule C k m s p') : p = p' :=
  d.toStep.symm.trans d'.toStep

/-- `Taclet.toStep`, under its first name. -/
theorem Taclet.step_eq {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (h : Taclet C k m s p) : s.step k m = p := h.toStep

end Solidity
