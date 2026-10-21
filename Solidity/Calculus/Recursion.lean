import Solidity.Calculus.FunContract
import Solidity.Calculus.Symex
import Solidity.Calculus.Spec
import Solidity.Calculus.SurfaceSpec

/-!
# Recursive calls by contract

A call of a recursive function is `Stmt.callRec` (`Syntax/Scoped.lean`): the
call of its body unrolled to `recDepth` frames (`recUnroll`), the bottom one
exhausted.  The strategy unfolds it frame by frame (`recursiveCallUnfold`),
which ends where the arguments are concrete; with a symbolic argument it
does not.  This module is KeY's way instead: the call proved by its callee's
contract (`useRecContract`, `useContract` at a recursive call), the contract
proved once for every frame of the unrolling by induction over it
(`RecContract.unroll`, `recUnroll_induct`): the bottom frame meets every
contract (it is exhausted, which the box accepts), and a frame meets it
where the frame below does.  The step is the body's obligation whose recursive
calls are calls of an unknown body `t ()` that meets the contract: the
strategy runs up to each of them (`sol_symex_rec`), where `rec_contract`
uses the hypothesis.  No `decreases` is needed, under either modality:
both accept the exhausted bottom frame (decision 15), and the unrolling is
finite, so the induction is over its frames, not over a measure.

`RecContract` is the hypothesis: the contract at every call that returns
`rs` (`FunContract`, whatever the call does with them), the mutability the
contract's frame needs (`Prog.within`), and the parameters left as they were
(`writesRets`).
-/

namespace Solidity

open Solidity (Modality Mutability)

variable {C : Contract}

section Contract

variable {ps rs : Ctx} {m : Modality}

/-- **A recursive function's contract**, at one body: the contract at every
call returning `rs`, the body within `μ`, the parameters unwritten. -/
def RecContract (μ : Mutability) (b : Prog C (rs ++ ps) (rs ++ ps)) (req : Fml C ps)
    (ens : Fml C (rs ++ (Olds ++ ps))) (m : Modality := .box) : Prop :=
  (∀ {Γ Γ' : Ctx} (ret : CallRet Γ rs Γ'), FunContract ret b req ens m) ∧
    Prog.within μ b = true ∧ writesRets rs.length b = true

/-- A formula of the locals `ps` closed by `∀` over each (a value) or a
hidden binder (a reference), the outermost first, named by `ns`, innermost
first: a callee's frame's obligation, its parameters bound. -/
def Fml.allCtx : (ps : Ctx) → List Var → Fml C ps → Fml C []
  | [], _, φ => φ
  | .val p :: ps, ns, φ => Fml.allCtx ps ns.tail (.all (ns.headD (.user "p")) p φ)
  | t :: ps, ns, φ => Fml.allCtx ps ns.tail (.bind .box (ns.headD (.user "p")) t φ)

theorem holds_allCtx : (ps : Ctx) → (ns : List Var) → {φ : Fml C ps} →
    Valid (Fml.allCtx ps ns φ) → ∀ σ : State C ps, holds σ φ
  | [], _, _, h, σ => h σ
  | .val p :: ps, ns, φ, h, σ =>
    holds_allCtx ps ns.tail (φ := .all (ns.headD (.user "p")) p φ) h (σ.withEnv σ.env.2) σ.env.1
  | .alias R :: ps, ns, φ, h, σ =>
    holds_allCtx ps ns.tail (φ := .bind .box (ns.headD (.user "p")) (.alias R) φ) h
      (σ.withEnv σ.env.2) σ.env.1
  | .mem R :: ps, ns, φ, h, σ =>
    holds_allCtx ps ns.tail (φ := .bind .box (ns.headD (.user "p")) (.mem R) φ) h
      (σ.withEnv σ.env.2) σ.env.1
  | .old :: ps, ns, φ, h, σ =>
    holds_allCtx ps ns.tail (φ := .bind .box (ns.headD (.user "p")) .old φ) h
      (σ.withEnv σ.env.2) σ.env.1
  | .oldNet :: ps, ns, φ, h, σ =>
    holds_allCtx ps ns.tail (φ := .bind .box (ns.headD (.user "p")) .oldNet φ) h
      (σ.withEnv σ.env.2) σ.env.1
  | .kint :: ps, ns, φ, h, σ =>
    holds_allCtx ps ns.tail (φ := .bind .box (ns.headD (.user "p")) .kint φ) h
      (σ.withEnv σ.env.2) σ.env.1

/-- A contract from a proof of its obligation, the frame's parameters bound
(`Fml.allCtx`, named by `ns`, innermost first). -/
theorem FunContract.ofValidCtx {Γ Γ' Γf : Ctx} (ns : List Var) {ret : CallRet Γ rs Γ'}
    {body : Prog C (rs ++ ps) Γf} {req : Fml C ps} {ens : Fml C (rs ++ (Olds ++ ps))}
    (h : Valid (Fml.allCtx ps ns (FunContract.obligation ret body req ens m))) :
    FunContract ret body req ens m :=
  FunContract.ofValid (holds_allCtx ps ns h)

/-- A contract at a call that returns nothing is one at every such call:
each enters the body alike (`CallRet.enterT`). -/
theorem FunContract.forall_none {Γf : Ctx} {b : Prog C ([] ++ ps) Γf} {req : Fml C ps}
    {ens : Fml C ([] ++ (Olds ++ ps))} (h : FunContract (Γ := []) CallRet.none b req ens m) :
    ∀ {Γ Γ' : Ctx} (ret : CallRet Γ [] Γ'), FunContract ret b req ens m := by
  intro Γ Γ' ret
  cases ret with
  | none => exact h
  | rets bs => cases bs; exact h

/-- A contract at a call that returns one value is one at every such call:
each enters the body with the return variable at its default. -/
theorem FunContract.forall_val {Γf : Ctx} {p : PrimTy} {b : Prog C ([.val p] ++ ps) Γf}
    {req : Fml C ps} {ens : Fml C ([.val p] ++ (Olds ++ ps))}
    (h : FunContract (Γ := []) (CallRet.val p (.user "r") Option.none) b req ens m) :
    ∀ {Γ Γ' : Ctx} (ret : CallRet Γ [.val p] Γ'), FunContract ret b req ens m := by
  intro Γ Γ' ret
  cases ret with
  | val => exact h
  | rets bs =>
    cases bs with
    | snoc bs q x => cases bs; exact h

/-- A contract at a call that returns a storage alias is one at every such
call: each enters the body with the alias unset, whatever its name. -/
theorem FunContract.forall_storage {Γf : Ctx} {R : RefTy} {b : Prog C ([.alias R] ++ ps) Γf}
    {req : Fml C ps} {ens : Fml C ([.alias R] ++ (Olds ++ ps))}
    (h : FunContract (Γ := []) (CallRet.storage R (.user "r")) b req ens m) :
    ∀ {Γ Γ' : Ctx} (ret : CallRet Γ [.alias R] Γ'), FunContract ret b req ens m := by
  intro Γ Γ' ret
  cases ret with
  | storage => exact h
  | rets bs => cases bs

theorem Binders.defaultsT_eq {H : HTy} : {ρ : Ctx} → (bs bs' : Binders ρ) →
    (Binders.defaultsT (C := C) (H := H) bs) = Binders.defaultsT bs'
  | _, .nil, .nil => rfl
  | _, .snoc bs _ _, .snoc bs' _ _ => by
    show (_, _) = (_, _)
    rw [Binders.defaultsT_eq bs bs']

/-- A contract at a call that returns several values to its targets is one
at every such call: each enters the body with the return variables at their
defaults, whatever the targets' names. -/
theorem FunContract.forall_rets {Γf : Ctx} {b : Prog C (rs ++ ps) Γf} {req : Fml C ps}
    {ens : Fml C (rs ++ (Olds ++ ps))} (bs : Binders rs) (h2 : 2 ≤ rs.length)
    (h : FunContract (Γ := []) (CallRet.rets bs) b req ens m) :
    ∀ {Γ Γ' : Ctx} (ret : CallRet Γ rs Γ'), FunContract ret b req ens m := by
  intro Γ Γ' ret
  cases ret with
  | none => simp at h2
  | val => simp at h2
  | mem => simp at h2
  | storage => simp at h2
  | rets bs' =>
    intro σ hσ
    have := h σ hσ
    simp only [CallRet.enterT] at this ⊢
    rw [Binders.defaultsT_eq bs bs'] at this
    exact this

theorem Prog.within_nil {μ : Mutability} {Γ : Ctx} : Prog.within μ (.nil : Prog C Γ Γ) = true :=
  rfl

theorem Prog.within_cons {μ : Mutability} {Γ Γ₁ Γ₂ : Ctx} (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) :
    Prog.within μ (.cons s P) = (Stmt.within μ s && Prog.within μ P) :=
  rfl

/-- Every frame of an unrolling is within `μ` where each frame is from the
one below. -/
theorem Prog.within_recUnroll {μ : Mutability} {F : Ctx}
    {step : Nat → (Unit → Prog C F F) → Prog C F F}
    (hs : ∀ n (t : Unit → Prog C F F), Prog.within μ (t ()) = true →
      Prog.within μ (step n t) = true) (d : Nat) :
    Prog.within μ (recUnroll Prog.recBase step d) = true :=
  recUnroll_induct (fun b => Prog.within μ b = true) rfl hs d

/-- The bottom frame meets every contract: it is exhausted. -/
theorem RecContract.base (μ : Mutability) (req : Fml C ps) (ens : Fml C (rs ++ (Olds ++ ps)))
    (m : Modality) :
    RecContract μ (Prog.recBase : Prog C (rs ++ ps) (rs ++ ps)) req ens m :=
  ⟨fun _ _ _ => ⟨by cases m <;> first | trivial | rfl, nofun⟩, rfl, rfl⟩

/-- **Induction over the unrolling**: a contract every frame meets where the
frame below does holds of the recursive call's body. -/
theorem RecContract.unroll {μ : Mutability} {req : Fml C ps} {ens : Fml C (rs ++ (Olds ++ ps))}
    {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (hs : ∀ n (t : Unit → Prog C (rs ++ ps) (rs ++ ps)),
      RecContract μ (t ()) req ens m → RecContract μ (step n t) req ens m) (d : Nat) :
    RecContract μ (recUnroll Prog.recBase step d) req ens m :=
  recUnroll_induct (fun b => RecContract μ b req ens m) (RecContract.base μ req ens m) hs d

end Contract

section Rule

variable {Γ ps rs Γ' Γ₂ Γ₀ : Ctx} {m : Modality}

/-- **A recursive call by its callee's contract** (`useContract` at a
`Stmt.callRec`, which runs as the call of its body): the goals "pre" and
"post". -/
theorem useRecContract {H : Hyps C [] Γ} {μ : Mutability} {f : Name} {d : Nat}
    {args : Args C Γ ps} {ret : CallRet Γ rs Γ'} {body : Unit → Prog C (rs ++ ps) (rs ++ ps)}
    {ω : Prog C Γ' Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {req : Fml C ps}
    {ens : Fml C (rs ++ (Olds ++ ps))} (hc : RecContract μ (body ()) req ens m)
    («pre» : Valid (H.wrap (Fml.callPre args req m)))
    («post» : Valid (H.wrap (Fml.callPost μ args ret ens ω κ φ m)))
    (hn : ret.nVals = rs.length) :
    Valid (H.wrap (.modal m (.cons (.callRec f d args ret body) ω) κ φ)) := fun σ =>
  H.wrap_mono (φ := .modal m (.cons (.call f args ret (body ())) ω) κ φ)
    (ψ := .modal m (.cons (.callRec f d args ret body) ω) κ φ) (fun _ h => h) σ
    (useContractC_of_valid (f := f) (hc.1 ret) «pre» «post» hc.2.1 (hn ▸ hc.2.2) σ)

/-- A conjunction behind a context, from each conjunct behind it. -/
theorem valid_wrap_and {H : Hyps C [] Γ} {φ ψ : Fml C Γ} (h₁ : Valid (H.wrap φ))
    (h₂ : Valid (H.wrap ψ)) : Valid (H.wrap (.and φ ψ)) :=
  fun σ => H.wrap_and (χ := .and φ ψ) (fun _ a b => ⟨a, b⟩) σ (h₁ σ) (h₂ σ)

end Rule

/-! ## A contract from the source

A recursive function's `/// @custom:key requires …` and `ensures …`
(`FunDecl.spec`, read as `spec!{f}` reads them, `Calculus/SurfaceSpec.lean`)
are its `RecContract`'s `req` and `ens`: `requires` over the parameters,
`ensures` over the return variables (`\result`, or `result_<name>` of
several), the snapshots `old` and `oldNet` (`\old`) and the parameters.
Unlike `spec!{f}`'s obligation, the contract assumes no layout, range or
invariant (a contract holds from any typed state of the frame). -/

section SpecContract

variable [FreshNames]

/-- The contract `requires`/`ensures` of the function `f` of `C`, at its
frame. -/
def recSpecContract (C : Contract) (f : String) :
    Except String ((ps : Ctx) × (rs : Ctx) × Fml C ps × Fml C (rs ++ (Olds ++ ps))) := do
  let some d := Semantics.lookupBy f C.funs | throw s!"{f} is not a function of the contract"
  if d.spec.requires.isEmpty && d.spec.ensures.isEmpty then
    throw s!"{f} has no `requires` or `ensures`"
  let Γ ← d.paramCtx
  let ps := d.params.filterMap fun (n, T) => match T with
    | .prim p => some (n, p)
    | _ => none
  let rets ← d.rets.mapM fun (n, T) => match T with
    | .prim p => pure (n, if d.rets.length == 1 then "result" else s!"result_{n}", p)
    | T => throw (refReturnMsg f T)
  let res := match rets with
    | [(_, _, p)] => some p
    | _ => none
  let pre : SpecCtx C := {
    storage := .storage
    ensures := false
    locals := ps
    refs := Γ.filter (fun (_, t) => t matches .alias _ | .mem _)
    result := none }
  let post : SpecCtx C := { pre with ensures := true, result := res, rets := rets }
  let reqs ← d.spec.requires.mapM (SpecExpr.fml C pre)
  let enss ← d.spec.ensures.mapM (SpecExpr.fml C post)
  let Δ : NCtx := ECtx.toNCtx Γ
  -- the last return innermost (`Binders.ofList`)
  let R : NCtx := (rets.map fun (_, v, p) => (Var.ofName v, LTy.val p)).reverse
  let O : NCtx := [(oldNetVar, .oldNet), (oldVar, .old)]
  let req ← NRead.conj reqs Δ
  let ens ← NRead.conj enss (R ++ (O ++ Δ))
  have h : NCtx.ctx (R ++ (O ++ Δ)) = R.ctx ++ (Olds ++ Δ.ctx) := by
    simp only [NCtx.ctx, List.map_append]; rfl
  pure ⟨Δ.ctx, R.ctx, req, h ▸ ens⟩

/-- `recSpecContract`, quoted at the contract `c`. -/
def recSpecContractQ (C : Contract) (c : Lean.Expr) (f : String) :
    Except String (Lean.Expr × Lean.Expr) := do
  let ⟨_, _, req, ens⟩ ← recSpecContract C f
  pure (Fml.quote c req, Fml.quote c ens)

end SpecContract

/-! ## Tactics

`sol_symex_rec` runs the strategy (`sol_step`) on each goal `⊨ φ`, a
conjunction behind the context split in two goals (`valid_wrap_and`), and
stops where the first statement of the box at the head of a goal is a
recursive call (`Stmt.callRec`), or where no modality is left.
`rec_contract h` proves the recursive call at the head of the goal by the
contract `h : RecContract μ (t ()) req ens`, leaving "pre" and "post". -/

namespace Recursion

open Lean Elab Tactic Meta

/-- Whether `φ` has a modality, read off its constructors. -/
partial def hasModal (φ : Expr) : MetaM Bool := do
  let φ ← whnfD (← instantiateMVars φ)
  if φ.isAppOf ``Fml.modal then return true
  for a in φ.getAppArgs do
    if (← inferType a).isAppOf ``Fml then
      if ← hasModal a then return true
  return false

/-- The context and formula of a goal `⊨ φ`: `φ` peeled (`Contract.peel`). -/
def goalParts (g : MVarId) : MetaM (Option (Expr × Expr × Expr)) := do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let_expr Valid C φ := ty | return none
  let nil := ctxE []
  let mut (H, Γ, χ) ← Contract.peel C (mkApp2 (mkConst ``Hyps.nil) C nil) nil (← whnfD φ)
  -- a definition under the context (`FunContract.obligation`) unfolded, and peeled
  for _ in [0:8] do
    let χ' ← whnfD χ
    if [``Fml.all, ``Fml.imp, ``Fml.bind, ``Fml.upd, ``Fml.havoc, ``Fml.grow].any χ'.isAppOf then
      (H, Γ, χ) ← Contract.peel C H Γ χ'
    else
      χ := χ'
      break
  return some (C, H, χ)

/-- Whether `χ` is a box whose first statement is a recursive call. -/
def headRecCall (χ : Expr) : MetaM Bool := do
  unless χ.isAppOfArity ``Fml.modal 8 do return false
  let P ← whnfR (χ.getArg! 5)
  unless P.isAppOfArity ``Prog.cons 6 do return false
  let s ← whnfR (P.getArg! 4)
  return s.isAppOf ``Stmt.callRec

/-- The formula under `φ`'s leading preconditions, updates, `∀`s, hidden
binders and `havoc`s, and `φ` with another formula in its place. -/
partial def splitPrefix (φ : Expr) : MetaM (Expr × (Expr → Expr)) := do
  let φ ← whnfR (← instantiateMVars φ)
  let a := φ.getAppArgs
  let f := φ.getAppFn
  let under (i : Nat) : MetaM (Expr × (Expr → Expr)) := do
    let (χ, k) ← splitPrefix a[i]!
    return (χ, fun x => mkAppN f (a.set! i (k x)))
  if φ.isAppOfArity ``Fml.imp 4 then under 3
  else if φ.isAppOfArity ``Fml.upd 6 then under 5
  else if φ.isAppOfArity ``Fml.all 5 then under 4
  else if φ.isAppOfArity ``Fml.bind 6 then under 5
  else if φ.isAppOfArity ``Fml.havoc 3 then under 2
  else if φ.isAppOfArity ``Fml.grow 3 then under 2
  else return (φ, id)

/-- `sol_symex_rec` on one goal, with fuel. -/
partial def loop (g : MVarId) (fuel : Nat) : TacticM (List MVarId) := g.withContext do
  if fuel == 0 then return [g]
  let some (C, H, χ) ← goalParts g | return [g]
  if χ.isAppOfArity ``Fml.and 4 then
    let a := χ.getAppArgs
    let gs ← g.apply (mkAppN (mkConst ``valid_wrap_and) #[C, a[1]!, H, a[2]!, a[3]!])
    -- each goal written out, its context's `wrap` unfolded
    let ty ← whnfR (← instantiateMVars (← g.getType))
    let (_, k) ← splitPrefix (← whnfD ty.appArg!)
    let mut out := []
    for (g', ψ) in gs.zip [a[2]!, a[3]!] do
      let g'' ← g'.replaceTargetDefEq (mkApp2 (mkConst ``Valid) C (k ψ))
      out := out ++ (← loop g'' fuel)
    return out
  if ← headRecCall χ then return [g]
  unless ← hasModal χ do return [g]
  setGoals [g]
  evalTactic (← `(tactic| sol_step))
  let [g'] ← getGoals | throwError "sol_symex_rec: unexpected goals"
  loop g' (fuel - 1)

end Recursion

open Lean Elab Tactic Meta in
/-- `sol_symex_rec`: the strategy up to each recursive call, conjunctions
split. -/
elab "sol_symex_rec" : tactic => do
  let gs ← getGoals
  let mut out := []
  for g in gs do
    if ← g.isAssigned then continue
    out := out ++ (← Recursion.loop g 5000)
  setGoals out

open Lean Elab Tactic Meta in
/-- `rec_contract h`: the recursive call at the head of the goal's box by
the contract `h` (`useRecContract`), the goals "pre" and "post" left. -/
elab "rec_contract " h:term : tactic => withMainContext do
  let g ← getMainGoal
  let some (_, H, χ) ← Recursion.goalParts g | throwError "rec_contract: expected a goal `⊨ φ`"
  unless ← Recursion.headRecCall χ do
    throwError "rec_contract: no recursive call at the head of the box{indentExpr χ}"
  let HS ← Term.exprToSyntax H
  evalTactic (← `(tactic| refine useRecContract (H := $HS) $h ?pre ?post ?hn))
  evalTactic (← `(tactic| case hn => rfl))

open Lean Elab Tactic Meta in
/-- `rec_contract_by μ req ens`: the recursive call at the head of the goal's
box by the contract `req`/`ens` of mutability `μ`, the goals `hc` (the
contract, `RecContract.unroll`), "pre" and "post" left. -/
elab "rec_contract_by " μ:term:max ppSpace req:term:max ppSpace ens:term:max : tactic =>
  withMainContext do
  let g ← getMainGoal
  let some (_, H, χ) ← Recursion.goalParts g | throwError "rec_contract_by: expected a goal `⊨ φ`"
  unless ← Recursion.headRecCall χ do
    throwError "rec_contract_by: no recursive call at the head of the box{indentExpr χ}"
  let HS ← Term.exprToSyntax H
  evalTactic (← `(tactic| refine useRecContract (H := $HS) (μ := $μ) (req := ?req) (ens := ?ens)
    ?hc ?pre ?post ?hn))
  evalTactic (← `(tactic| case hn => rfl))
  evalTactic (← `(tactic| case req => exact $req))
  evalTactic (← `(tactic| case ens => exact $ens))

open Lean Elab Tactic Meta in
/-- `rec_head`: fails unless the head of the goal's box is a recursive call. -/
elab "rec_head" : tactic => withMainContext do
  let some (_, _, χ) ← Recursion.goalParts (← getMainGoal) | throwError "rec_head: not `⊨ φ`"
  unless ← Recursion.headRecCall χ do throwError "rec_head: no recursive call at the head"

/-- `rec_step ih`: an induction step's obligation, its recursive calls by the
hypothesis `ih` and everything else by the closer. -/
macro "rec_step " ih:ident : tactic => `(tactic| (
  sol_symex_rec
  all_goals first
    | (rec_head
       rec_contract $ih
       all_goals (sol_symex; sol_close))
    | sol_close))

/-- `rec_induct`: a `RecContract` of a recursive call's body by
induction over its frames (`RecContract.unroll`), each step by `rec_step`:
a function of no return or of one value return. -/
macro "rec_induct" : tactic => `(tactic| (
  apply RecContract.unroll
  intro n t ih
  refine ⟨?c, ?w, rfl⟩
  case c =>
    first
      | apply FunContract.forall_none
      | apply FunContract.forall_val
      | apply FunContract.forall_storage
    apply FunContract.ofValidCtx []
    rec_step ih
  case w =>
    simp only [Prog.within, Stmt.within, ih.2.1, Bool.and_true]
    first | rfl | decide))

open Lean Meta in
/-- The goals of `g` with every local of type `bool` split in its two values. -/
partial def Recursion.boolCases (g : MVarId) (fuel : Nat := 8) : MetaM (List MVarId) :=
  g.withContext do
  if fuel == 0 then return [g]
  for d in (← getLCtx).decls.toList.filterMap id do
    if d.isImplementationDetail then continue
    let ty ← whnfD (← instantiateMVars d.type)
    unless ty.isConstOf ``Bool do continue
    let some subs ← observing? (g.cases d.fvarId) | continue
    return (← subs.toList.mapM fun s => Recursion.boolCases s.mvarId (fuel - 1)).flatten
  return [g]

open Lean Elab Tactic Meta in
/-- `rec_bool_cases`: every local of type `bool` split in its two values. -/
elab "rec_bool_cases" : tactic => do
  replaceMainGoal (← Recursion.boolCases (← getMainGoal))

namespace Recursion

open Lean Elab Tactic Meta

/-- `tac` on the goal `g` alone, with no error recovery: the goals it
leaves, or `none` (the state restored) where it fails. -/
def tryOn (g : MVarId) (tac : TacticM Unit) : TacticM (Option (List MVarId)) := do
  let s ← saveState
  tryCatchRuntimeEx (do
      setGoals [g]
      -- each step its own heartbeats, as a search's steps (`rec_auto`'s
      -- driver is bounded by its fuel instead)
      let max := Core.getMaxHeartbeats (← getOptions)
      withTheReader Core.Context (fun c => { c with maxHeartbeats := max })
        <| withCurrHeartbeats <| Term.withoutErrToSorry <| withoutRecover tac
      return some (← getUnsolvedGoals))
    fun _ => do s.restore; return none

/-- The recursive call at the head of `χ`'s box: the callee's name and the
statement. -/
def headCall? (χ : Expr) : MetaM (Option (String × Expr)) := do
  unless χ.isAppOfArity ``Fml.modal 8 do return none
  let P ← whnfR (χ.getArg! 5)
  unless P.isAppOfArity ``Prog.cons 6 do return none
  let s ← whnfR (P.getArg! 4)
  unless s.isAppOfArity ``Stmt.callRec 10 do return none
  let .lit (.strVal f) := (← whnfD (s.getArg! 5)).consumeMData | return none
  return some (f, s)

/-- The contract the source gives `f` (`recSpecContract`), quoted; `none`
where it gives none. -/
def specContract? (C : Expr) (f : String) : TacticM (Option (Expr × Expr)) := do
  let C ← withTransparency .instances <| whnf C
  let some n := C.constName? | return none
  let stx ← `(recSpecContractQ $(mkCIdent n) (Lean.mkConst $(quote n)) $(quote f))
  let exprE := mkConst ``Lean.Expr
  let ty := mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String)
    (mkApp2 (mkConst ``Prod [0, 0]) exprE exprE)
  let e ← Term.elabTermEnsuringType stx ty
  Term.synthesizeSyntheticMVarsNoPostponing
  match ← unsafe evalExpr (Except String (Expr × Expr)) ty (← instantiateMVars e) with
  | .ok r => return some r
  | .error _ => return none

/-- The hypotheses of the context that are a `RecContract`. -/
def recHyps : MetaM (List LocalDecl) := do
  (← getLCtx).decls.toList.filterMapM fun d? => do
    let some d := d? | return none
    if d.isImplementationDetail then return none
    let ty ← instantiateMVars d.type
    return if ty.isAppOf ``RecContract then some d else none

/-- A leaf: `sol_close`, else a specification's closer. -/
def closeLeaf (g : MVarId) : TacticM Bool := do
  if let some [] ← tryOn g (evalTactic (← `(tactic| sol_close))) then return true
  if let some [] ← tryOn g (evalTactic (← `(tactic| (sol_spec_prep; all_goals sol_spec_finish))))
  then return true
  -- a remainder (`%`) is `Int.tmod`, which `omega` reads at a nonnegative
  -- dividend only; a `bool` result split
  if let some [] ← tryOn g (evalTactic (← `(tactic| (
      sol_spec_prep
      all_goals (try simp (disch := omega) only [Int.tmod_eq_emod_of_nonneg] at *)
      all_goals rec_bool_cases
      all_goals (first | omega | (simp_all <;> omega) | grind (gen := 3))))))
  then return true
  return false

/-- How an induction over the frames ended. -/
inductive Induct where
  | proved
  /-- the body is not within the mutability: a more permissive one may be -/
  | notWithin
  | failed

mutual

/-- `rec_auto` on the goal `g`: the strategy up to each recursive call, each
call by a contract (`autoCall`), the closer at the leaves.  The goals left
(`[]` where it is proved). -/
partial def autoGoal (g : MVarId) (fuel : Nat) : TacticM (List MVarId) := g.withContext do
  let some gs ← tryOn g (evalTactic (← `(tactic| sol_symex_rec))) | return [g]
  let mut rest := gs
  while !rest.isEmpty do
    let g' :: more := rest | break
    rest := more
    let call ← withCurrHeartbeats <| g'.withContext do
      let some (_, _, χ) ← goalParts g' | pure none
      headCall? χ
    let ok ← match call with
      | some (f, s) => do pure (← autoCall g' f s fuel).isEmpty
      | none => closeLeaf g'
    -- one goal left open: the others are not tried
    unless ok do return g' :: rest
  return []

/-- The recursive call `s` of `f` at the head of `g`'s box: by a hypothesis
of the context about its body (an induction's), else by the source's
contract of `f`, else by `true`/`true`; the contract proved by induction
over the frames (`induct`), at the first mutability its body is within. -/
partial def autoCall (g : MVarId) (f : String) (s : Expr) (fuel : Nat) :
    TacticM (List MVarId) := g.withContext do
  if fuel == 0 then return [g]
  let some (C, H, _) ← withCurrHeartbeats <| goalParts g | return [g]
  let body := s.getArg! 9
  -- a hypothesis about the frame below
  for d in ← recHyps do
    let b := (← instantiateMVars d.type).getArg! 4
    unless ← withCurrHeartbeats <| withReducible (isDefEq b (mkApp body (mkConst ``Unit.unit)))
    do continue
    let st ← saveState
    let hS ← Term.exprToSyntax d.toExpr
    let HS ← Term.exprToSyntax H
    let some gs ← tryOn g (evalTactic (← `(tactic|
        refine useRecContract (H := $HS) $hS ?_ ?_ (by rfl))))
      | continue
    if ← allProved gs (fuel - 1) then return []
    st.restore
  let HS ← Term.exprToSyntax H
  let spec ← withCurrHeartbeats <| specContract? C f
  let cands : List (Option (Expr × Expr)) := (spec.map some).toList ++ [none]
  for c in cands do
    let (reqS, ensS) ← match c with
      | some (req, ens) => pure ((← Term.exprToSyntax req), (← Term.exprToSyntax ens))
      | none => pure ((← `(.tt)), (← `(.tt)))
    for μ in [← `(Mutability.pure), ← `(Mutability.view), ← `(Mutability.nonpayable)] do
      let st ← saveState
      let some gs ← tryOn g (evalTactic (← `(tactic|
          refine useRecContract (H := $HS) (μ := $μ) (req := $reqS) (ens := $ensS)
            ?_ ?_ ?_ (by rfl))))
        | continue
      let some hc := ← gs.findM? fun g' => do
          return (← instantiateMVars (← g'.getType)).isAppOf ``RecContract
        | st.restore; continue
      match ← induct hc (s.getArg! 8) (fuel - 1) with
      | .notWithin => st.restore; continue
      | .failed => st.restore; break
      | .proved =>
        if ← allProved (gs.erase hc) (fuel - 1) then return []
        st.restore; break
  return [g]

/-- Every goal of `gs` proved by `autoGoal`. -/
partial def allProved (gs : List MVarId) (fuel : Nat) : TacticM Bool := do
  for g in gs do
    if ← g.isAssigned then continue
    unless (← autoGoal g fuel).isEmpty do return false
  return true

/-- A `RecContract` of a recursive call's body (`g`) by induction over its
frames (`RecContract.unroll`): the step's body within the mutability, it
writes its return variables only, and its obligation by `autoGoal`, the
frame below's calls by the hypothesis.  `ret` is the call's, whose binders
name a contract at several returns. -/
partial def induct (g : MVarId) (ret : Expr) (fuel : Nat) : TacticM Induct := g.withContext do
  let some [g₁] ← tryOn g (evalTactic (← `(tactic| (apply RecContract.unroll; intro n t ih))))
    | return .failed
  g₁.withContext do
  -- the frame's own within facts, for `simp`
  let mut g₂ := g₁
  for d in ← recHyps do
    let hS ← Term.exprToSyntax d.toExpr
    let some [g'] ← tryOn g₂ (evalTactic (← `(tactic| have := ($hS).2.1))) | return .failed
    g₂ := g'
  let some gs ← tryOn g₂ (evalTactic (← `(tactic| refine ⟨?_, ?_, ?_⟩))) | return .failed
  let [gc, gw, gr] := gs | return .failed
  unless ← proveWithin gw do return .notWithin
  let some [] ← tryOn gr (evalTactic (← `(tactic| first | rfl | decide))) | return .failed
  let rets := ret.isAppOf ``CallRet.rets
  let tac ← if rets then do
      let bs ← Term.exprToSyntax ret.appArg!
      `(tactic| (
        (first | apply FunContract.forall_rets $bs (by decide) | apply FunContract.forall_val)
        apply FunContract.ofValidCtx []))
    else `(tactic| (
        (first
          | apply FunContract.forall_none
          | apply FunContract.forall_val
          | apply FunContract.forall_storage)
        apply FunContract.ofValidCtx []))
  let some [gc'] ← tryOn gc (evalTactic tac) | return .failed
  return if (← autoGoal gc' fuel).isEmpty then .proved else .failed

/-- `Prog.within μ b = true`, `b` a frame: its statements by `simp`, the
frame below by the hypotheses, a nested unrolling (a mutually recursive
callee) frame by frame (`Prog.within_recUnroll`). -/
partial def proveWithin (g : MVarId) : TacticM Bool := g.withContext do
  let some gs ← tryOn g (evalTactic (← `(tactic|
      simp only [Prog.within_nil, Prog.within_cons, Stmt.within, Bool.and_true, Bool.true_and,
        Bool.and_self, *])))
    | return false
  for g' in gs do
    if let some [] ← tryOn g' (evalTactic (← `(tactic| first | rfl | decide))) then continue
    -- a nested unrolling: true where each of its frames is
    let some gs' ← tryOn g' (evalTactic (← `(tactic| rw [Prog.within_recUnroll])))
      | return false
    for g'' in gs' do
      let ty ← instantiateMVars (← g''.getType)
      let g'' ← if ty.isForall then do
          let some [g₃] ← tryOn g'' (evalTactic (← `(tactic| intro n t ih))) | return false
          pure g₃
        else pure g''
      unless ← proveWithin g'' do return false
  return true

end

end Recursion

open Lean Elab Tactic Meta in
/-- `rec_auto`: a goal `⊨ φ` whose recursive calls are proved by their
contracts (`docs/kernel-port.md`, "Recursion"): the strategy up to each
recursive call (`sol_symex_rec`), the closer everywhere else.  A call is
proved by a hypothesis about its body (in an induction step, the frame
below), else by its callee's `requires`/`ensures` (`recSpecContract`, the
source's `/// @custom:key` clauses), else by `true`/`true` (no panic, the
box's); a contract by induction over the frames, at the first of `pure`,
`view` and `nonpayable` the body is within.  Fails, the goal unchanged,
where it does not close. -/
elab "rec_auto" : tactic => do
  let g ← getMainGoal
  let rest := (← getGoals).erase g
  -- each step has its own heartbeats (`Recursion.tryOn`); the driver, which
  -- spans at most `fuel` of them, the same budget `fuel` times over, so a
  -- runaway fails within a bound (AGENTS.md: bound every search)
  let fuel := 32
  let open_ ← withTheReader Core.Context
      (fun c => { c with maxHeartbeats := c.maxHeartbeats * fuel }) <|
    withCurrHeartbeats <| Recursion.autoGoal g fuel
  unless open_.isEmpty do
    throwError "rec_auto: a goal is left open{indentExpr (← open_.head!.getType)}"
  setGoals rest

end Solidity
