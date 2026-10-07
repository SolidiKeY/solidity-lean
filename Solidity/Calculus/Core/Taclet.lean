import Solidity.Calculus.Core.Rules
import Solidity.Calculus.Rules

/-!
# Each scoped taclet is the rule `Stmt.step` fires

`Calculus/Core/Rules.lean`'s table, its lines `Rules.lean`'s, against the
strategy of `Calculus/Core/Step.lean`: `Taclet.toStep` says the premise of
every constructor is the one `Stmt.step` builds for its statement, so the
soundness of every rule is `Stmt.Sound`'s (`Calculus/Core/ProvesSound.lean`),
with no proof per rule.

The proof is one lemma per constructor (`Taclet.<rule>.toStep`), each its
own declaration, so that a rule added checks alone.  Most are written by
`#derive_toStep`: the hole a rule writes through is taken apart, the side
conditions that compute are settled, the parts a side condition speaks of
taken apart until it does (`core_cases_part`, as `Uniqueness.lean`'s
`cases_part`), and what is left closes by `rfl`, or after taking apart a
path, a location or a value the dispatcher reads (`core_brute`).  The rules
whose dispatcher branches on what no side condition decides by computing
(an array's element type, a call's arguments, a read through a hole that
is a copy, a conditional written to a member) are proved by hand first.

`Rules.lean` is imported for the printers (`Calculus/Core/Delab.lean`) and
`Premise.erase`, the premise's erasure to today's.
-/

namespace Solidity.Core

variable {C : Contract}

/-! ## The tactics -/

section Tactics
open Lean Elab Tactic Meta

/-- The predicates a scoped side condition is stated with. -/
def coreSidePreds : List Lean.Name :=
  [``SPath.isSimple, ``Val.isSimple, ``MPath.isSimple, ``Loc.isTarget, ``Loc.isRoot,
    ``MLoc.isTarget, ``MPath.isBindable, ``Val.notTernary, ``SHole.isTarget, ``MHole.isTarget,
    ``VHole.isTarget, ``SPath.elemMapping, ``SPath.elemPrim, ``CallRet.isRets,
    ``Args.firstNonSimple, ``BinOp.accepts, ``BinOp.shortCircuits]

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

/-- `rfl`, or a case split on a part the dispatcher reads (a path, a
location, a memory source, a value), `n` deep. -/
partial def coreBrute : Nat → TacticM Unit
  | 0 => do evalTactic (← `(tactic| rfl))
  | n + 1 => do
    try evalTactic (← `(tactic| rfl))
    catch _ =>
      for heads in [[``SPath], [``MPath], [``Loc], [``MLoc], [``MSrc], [``Val]] do
        let s ← saveState
        try
          unless ← coreCasesFirst heads do continue
          for g in ← getGoals do
            setGoals [g]
            coreBrute n
          setGoals []
          return
        catch _ => s.restore
      throwError "core_brute: no split closes the goal"

elab "core_brute" : tactic => coreBrute 2

/-- A constructor's premise is `Stmt.step`'s. -/
macro "to_step_tac" : tactic => `(tactic| (
  (try core_cases_hole) <;> core_settle_side <;>
  (repeat' (core_cases_part <;> core_settle_side)) <;> core_brute))

/-- `Taclet.<rule>.toStep` for every constructor without one, by
`to_step_tac`: its statement the constructor's, `Stmt.step` of the
statement the premise, the side conditions hypotheses. -/
elab "#derive_toStep " j:ident : command => do
  let J ← Command.liftCoreM <| realizeGlobalConstNoOverload j
  let some (.inductInfo ii) := (← getEnv).find? J | throwError "no inductive `{J}`"
  for c in ii.ctors do
    let n := c ++ `toStep
    if (← getEnv).contains n then continue
    Command.liftTermElabM <| withCurrHeartbeats do
      let ty ← forallTelescope (← getConstInfo c).type fun xs body => do
        let args := body.getAppArgs
        let concl ← mkEq (← mkAppM ``Stmt.step #[args[1]!, args[2]!, args[5]!])
          (← mkAppM ``Option.some #[args[6]!])
        mkForallFVars xs concl
      let ty := ty.replace fun e =>
        if e.isAppOfArity ``autoParam 2 then some (e.getArg! 0) else none
      let mvar ← mkFreshExprMVar ty
      let ok ← tryCatchRuntimeEx (do
          let gs ← Term.withoutErrToSorry <|
            Tactic.run mvar.mvarId! (evalTactic (← `(tactic| (intros; to_step_tac))))
          pure (gs.isEmpty && !(← instantiateMVars mvar).hasSorry))
        (fun ex => do logError m!"{c}: {ex.toMessageData}"; pure false)
      unless ok do throwError "#derive_toStep: no proof that `{c}` is `Stmt.step`'s rule"
      let val ← instantiateMVars mvar
      addDecl (Declaration.thmDecl { name := n, levelParams := [], type := ty, value := val })

/-- Close `s.step k m = some p` for the case of `cases h` it is, by its
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
      some (Premise.unfold (Prog.cons (Stmt.declLocal kp (Var.fresh "ie" k) (some nse))
        (Prog.cons (lhs.up.fill (SPath.loc (Loc.index it sp.up (Val.simple (Simple.local Idx.here)))))
          Prog.nil)) Ext.refl.push) := by
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
      some (Premise.unfold (Prog.cons (Stmt.ite (Val.simple se) (Prog.cons (lhs.fill thenExpr) Prog.nil)
        (Prog.cons (lhs.fill elseExpr) Prog.nil)) Prog.nil) Ext.refl) := by
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
      some (Premise.unfold (Prog.cons (Stmt.declLocal .bool (Var.fresh "se" k) (some nse))
        (Prog.cons (lhs.up.fill ((Val.simple (Simple.local Idx.here)).ternary thenExpr.up elseExpr.up))
          Prog.nil)) Ext.refl.push) := by
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
      some (Premise.unfold
        (Prog.cons (Stmt.declMem (RefTy.struct s) (Var.fresh "mv" k) (some (MRhs.alias nmp)) rfl
          (MRhs.alias nmp).mapFree)
          (Prog.cons (Stmt.assignMem (MLoc.field (MPath.var Idx.here (MRhs.alias nmp).mapFree) fld hfld)
            msrc.up) Prog.nil)) Ext.refl.push) := by
  cases nmp <;> (try contradiction) <;> cases msrc <;> rfl

theorem Taclet.storagePushLengthSave.toStep {E : Ty} {parr : SPath C Γ E.array}
    {hd : ((none : Option (Src C Γ E)).isSome || E.defaultOkS) = true}
    (h1 : parr.isSimple = true) (h2 : parr.elemPrim = true) :
    Stmt.step k m (Stmt.push parr none hd) =
      some (Premise.update (Upd.nil.snoc (UpdElem.storage
        (Tms.STerm.pushSlot Tms.STerm.storage parr.lower E)))) := by
  show pushStep k parr none hd = _
  simp only [pushStep, h1, h2]
  rfl

theorem Taclet.storagePushLengthSaveReferenceElement.toStep {E : Ty} {rarr : SPath C Γ E.array}
    {hd : ((none : Option (Src C Γ E)).isSome || E.defaultOkS) = true}
    (h1 : rarr.isSimple = true) (h2 : rarr.elemPrim = false) :
    Stmt.step k m (Stmt.push rarr none hd) =
      some (Premise.update (Upd.nil.snoc (UpdElem.storage
        (Tms.STerm.extend Tms.STerm.storage rarr.lower E)))) := by
  show pushStep k rarr none hd = _
  simp only [pushStep, h1, h2]
  rfl

theorem Taclet.storagePopSave.toStep {E : Ty} {darr : SPath C Γ E.array}
    (h1 : darr.isSimple = true) (h2 : darr.elemMapping = false) :
    Stmt.step k m (Stmt.pop darr) =
      some (Premise.update (Upd.nil.snoc (UpdElem.storage
        (Tms.STerm.pop Tms.STerm.storage darr.lower)))) := by
  show popStep k darr = _
  simp only [popStep, h1, h2]
  rfl

theorem Taclet.storagePopSaveMappingElement.toStep {E : Ty} {marr : SPath C Γ E.array}
    (h1 : marr.isSimple = true) (h2 : marr.elemMapping = true) :
    Stmt.step k m (Stmt.pop marr) =
      some (Premise.update (Upd.nil.snoc (UpdElem.storage
        (Tms.STerm.shrink Tms.STerm.storage marr.lower)))) := by
  show popStep k marr = _
  simp only [popStep, h1, h2]
  rfl

/-- A call whose arguments are all simple is inlined, whatever it returns. -/
theorem Premise.expandCall_step {f : Name} {ps : Ctx} {args : Args C Γ ps} {rs Γ' : Ctx}
    {ret : CallRet Γ rs Γ'} {Γf : Ctx} {body : Prog C (rs ++ ps) Γf}
    (h1 : args.firstNonSimple = none) :
    Stmt.step k m (Stmt.call f args ret body) = some (Premise.expandCall k args ret body) := by
  simp only [Args.firstNonSimple, Option.map_eq_none_iff] at h1
  cases ret <;> (dsimp only [Stmt.step]; simp only [callStep, h1]) <;> rfl

theorem Taclet.functionBodyExpand.toStep {f : Name} {ps : Ctx} {args : Args C Γ ps} {rs Γ' : Ctx}
    {ret : CallRet Γ rs Γ'} {Γf : Ctx} {body : Prog C (rs ++ ps) Γf}
    (h1 : args.firstNonSimple = none) (_ : ret.isRets = true) :
    Stmt.step k m (Stmt.call f args ret body) = some (Premise.expandCall k args ret body) :=
  Premise.expandCall_step h1

theorem Taclet.internalCallExpand.toStep {f : Name} {ps : Ctx} {args : Args C Γ ps} {rs Γ' : Ctx}
    {ret : CallRet Γ rs Γ'} {Γf : Ctx} {body : Prog C (rs ++ ps) Γf}
    (h1 : args.firstNonSimple = none) (_ : ret.isRets = false) :
    Stmt.step k m (Stmt.call f args ret body) = some (Premise.expandCall k args ret body) :=
  Premise.expandCall_step h1

theorem LeanTaclet.whileInvariantBox.toStep {Γ₁ : Ctx} {body : Prog C Γ Γ₁}
    {xs : List ((t : LTy) × Idx Γ t)} {hv : Bool} {dec : Option (Val C Γ .uint)}
    {cond inv : Val C Γ .bool} (hf : body.frame = some (xs, hv)) :
    Stmt.step k .box (Stmt.loop (LoopAnn.inv inv dec) cond body) =
      some (Premise.inv (Fml.eqD inv.lower (Tms.Term.lit (.bool true))) xs hv
        (Upd.nil.decl (Var.fresh "se" k) (Rhs.val cond.lower))
        (Fml.eqD (Tms.Term.pv (p := .bool) Idx.here) (Tms.Term.lit (.bool true)))
        (Fml.eqD (Tms.Term.pv (p := .bool) Idx.here) (Tms.Term.lit (.bool false))) Ext.refl
        Ext.refl.push body (Fml.eqD inv.lower (Tms.Term.lit (.bool true)))) := by
  dsimp only [Stmt.step]
  simp only [loopStep, hf]

theorem LeanTaclet.whileInvariantDiamond.toStep {Γ₁ : Ctx} {body : Prog C Γ Γ₁}
    {xs : List ((t : LTy) × Idx Γ t)} {hv : Bool} {cond inv : Val C Γ .bool} {dec : Val C Γ .uint}
    (hf : body.frame = some (xs, hv)) :
    Stmt.step k .diamond (Stmt.loop (LoopAnn.inv inv (some dec)) cond body) =
      some (Premise.inv (Fml.eqD inv.lower (Tms.Term.lit (.bool true))) xs hv
        ((Upd.nil.decl (Var.fresh "ie" k) (Rhs.val (p := .uint) dec.lower)).decl (Var.fresh "se" k)
          (Rhs.val (p := .bool) cond.lower))
        (Fml.eqD (Tms.Term.pv (p := .bool) Idx.here) (Tms.Term.lit (.bool true)))
        (Fml.eqD (Tms.Term.pv (p := .bool) Idx.here) (Tms.Term.lit (.bool false))) Ext.refl.push
        Ext.refl.push body.up
        ((Fml.eqD inv.up.lower (Tms.Term.lit (.bool true))).and
          (Fml.upd .diamond (Upd.nil.decl (Var.fresh "se" k) (Rhs.val (p := .bool) cond.up.lower))
            ((Fml.eqD (Tms.Term.pv (p := .bool) Idx.here) (Tms.Term.lit (.bool true))).imp
              ((Fml.eqD (Tms.Term.binop .le .uint (Tms.Term.lit (.int 0)) dec.up.up.lower)
                  (Tms.Term.lit (.bool true))).and
                (Fml.eqD (Tms.Term.binop .lt .uint dec.up.up.lower (Tms.Term.pv (p := .uint) Idx.here.there))
                  (Tms.Term.lit (.bool true)))))))) := by
  dsimp only [Stmt.step]
  simp only [loopStep, hf]

theorem LeanTaclet.whileClose.toStep {Γ₁ : Ctx} {body : Prog C Γ Γ₁} {inv : Val C Γ .bool}
    {dec : Option (Val C Γ .uint)} {cond : Val C Γ .bool} (hf : body.frame = none) :
    Stmt.step k m (Stmt.loop (LoopAnn.inv inv dec) cond body) = some (Premise.done false) := by
  dsimp only [Stmt.step]
  simp only [loopStep, hf]

theorem LeanTaclet.whileNoVariantDiamond.toStep {Γ₁ : Ctx} {body : Prog C Γ Γ₁}
    {inv cond : Val C Γ .bool} {dec : Option (Val C Γ .uint)} (hf : body.frame.isSome = true)
    (hd : dec.isNone = true) :
    Stmt.step k .diamond (Stmt.loop (LoopAnn.inv inv dec) cond body) = some (Premise.done false) := by
  cases dec with
  | some => simp only [Option.isNone_some, Bool.false_eq_true] at hd
  | none =>
    obtain ⟨⟨xs, hv⟩, hfr⟩ := Option.isSome_iff_exists.mp hf
    dsimp only [Stmt.step]
    simp only [loopStep, hfr]

theorem LeanTaclet.functionCallArgCapture.toStep {f : Name} {ps : Ctx} {args : Args C Γ ps}
    {rs Γ' : Ctx} {ret : CallRet Γ rs Γ'} {Γf : Ctx} {body : Prog C (rs ++ ps) Γf} {p : PrimTy}
    {v : Val C Γ p} {as' : Args C (.val p :: Γ) ps} (hcap : Args.capture args = some ⟨p, v, as'⟩) :
    Stmt.step k m (Stmt.call f args ret body) = some (Premise.argCapture k f p v as' ret body) := by
  cases ret <;> (dsimp only [Stmt.step]; simp only [callStep, hcap]) <;> rfl

end Hand

#derive_toStep Taclet
#derive_toStep LeanTaclet

/-! ## The rule `Stmt.step` fires -/

/-- **Each taclet is the rule the strategy fires on its statement**: its
premise is `Stmt.step`'s, so it is sound by `Stmt.Sound`. -/
theorem Taclet.toStep {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (h : Taclet C k m s p) : s.step k m = some p := by
  cases h <;> apply_toStep Taclet

/-- The rules solkey does not have are `Stmt.step`'s too. -/
theorem LeanTaclet.toStep {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (h : LeanTaclet C k m s p) : s.step k m = some p := by
  cases h <;> apply_toStep LeanTaclet

/-- **Every rule of the calculus is the one `Stmt.step` fires**: at most one
premise per statement, the dispatcher's. -/
theorem Rule.toStep {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} : Rule C k m s p → s.step k m = some p
  | .key d => d.toStep
  | .lean d => d.toStep

/-- Two rules on one statement leave the same premise. -/
theorem Rule.premise_unique {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p p' : Premise C Γ Γ'} (d : Rule C k m s p) (d' : Rule C k m s p') : p = p' :=
  Option.some.inj (d.toStep.symm.trans d'.toStep)

/-- `Taclet.toStep`, under its first name. -/
theorem Taclet.step_eq {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (h : Taclet C k m s p) : s.step k m = some p := h.toStep

/-! ## Erasure: today's premise -/

/-- `Rules.lean`'s premise, the positions named by `ns`: a capture's scope
and a hidden binder are erased, a branch's block is its statements. -/
def Premise.erase {Γ Γ' : Ctx} (ns : List Var) : Premise C Γ Γ' → Solidity.Premise C
  | .update U => .update (U.erase ns)
  | .unfold P _ => .unfold (P.erase ns)
  | .bind x _ P => .unfold (P.erase (x :: ns))
  | .split _ c c' P Q => .split (c.erase ns) (c'.erase ns) (P.erase ns) (Q.erase ns)
  | .check c => .check (c.erase ns) []
  | .done b => .done b
  | .branches bs => .branches (bs.map fun b => (b.bs.toList, b.P.erase (b.bs.names ++ ns)))
  | .cases fs us => .cases (fs.map (·.erase ns)) (us.map (·.erase ns))
  | .inv I _ _ U c c' _ hb P post =>
    let ms := (U.names ns).drop hb.depth
    .inv (I.erase ns) (U.erase ns) (c.erase (U.names ns)) (c'.erase (U.names ns)) (P.erase ms)
      (post.erase ms)
  | .inline P _ => .unfold (P.erase ns)

end Solidity.Core
