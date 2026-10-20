import Solidity.Calculus.FunContract
import Solidity.Calculus.Symex

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
where the frame below does.  The step is a box obligation whose recursive
calls are calls of an unknown body `t ()` that meets the contract: the
strategy runs up to each of them (`sol_symex_rec`), where `rec_contract`
uses the hypothesis.  No `decreases` is needed: the box of KeY's partial
correctness accepts a run that does not end, as it accepts the exhausted
bottom frame.

`RecContract` is the hypothesis: the contract at every call that returns
`rs` (`FunContract`, whatever the call does with them), the mutability the
contract's frame needs (`Prog.within`), and the parameters left as they were
(`writesRets`).
-/

namespace Solidity

open Solidity (Modality Mutability)

variable {C : Contract}

section Contract

variable {ps rs : Ctx}

/-- **A recursive function's contract**, at one body: the contract at every
call returning `rs`, the body within `μ`, the parameters unwritten. -/
def RecContract (μ : Mutability) (b : Prog C (rs ++ ps) (rs ++ ps)) (req : Fml C ps)
    (ens : Fml C (rs ++ (Olds ++ ps))) : Prop :=
  (∀ {Γ Γ' : Ctx} (ret : CallRet Γ rs Γ'), FunContract ret b req ens) ∧
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
    (h : Valid (Fml.allCtx ps ns (FunContract.obligation ret body req ens))) :
    FunContract ret body req ens :=
  FunContract.ofValid (holds_allCtx ps ns h)

/-- A contract at a call that returns nothing is one at every such call:
each enters the body alike (`CallRet.enterT`). -/
theorem FunContract.forall_none {Γf : Ctx} {b : Prog C ([] ++ ps) Γf} {req : Fml C ps}
    {ens : Fml C ([] ++ (Olds ++ ps))} (h : FunContract (Γ := []) CallRet.none b req ens) :
    ∀ {Γ Γ' : Ctx} (ret : CallRet Γ [] Γ'), FunContract ret b req ens := by
  intro Γ Γ' ret
  cases ret with
  | none => exact h
  | rets bs => cases bs; exact h

/-- A contract at a call that returns one value is one at every such call:
each enters the body with the return variable at its default. -/
theorem FunContract.forall_val {Γf : Ctx} {p : PrimTy} {b : Prog C ([.val p] ++ ps) Γf}
    {req : Fml C ps} {ens : Fml C ([.val p] ++ (Olds ++ ps))}
    (h : FunContract (Γ := []) (CallRet.val p (.user "r") Option.none) b req ens) :
    ∀ {Γ Γ' : Ctx} (ret : CallRet Γ [.val p] Γ'), FunContract ret b req ens := by
  intro Γ Γ' ret
  cases ret with
  | val => exact h
  | rets bs =>
    cases bs with
    | snoc bs q x => cases bs; exact h

/-- The bottom frame meets every contract: it is exhausted. -/
theorem RecContract.base (μ : Mutability) (req : Fml C ps) (ens : Fml C (rs ++ (Olds ++ ps))) :
    RecContract μ (Prog.recBase : Prog C (rs ++ ps) (rs ++ ps)) req ens :=
  ⟨fun _ _ hr => ⟨trivial, nofun⟩, rfl, rfl⟩

/-- **Induction over the unrolling**: a contract every frame meets where the
frame below does holds of the recursive call's body. -/
theorem RecContract.unroll {μ : Mutability} {req : Fml C ps} {ens : Fml C (rs ++ (Olds ++ ps))}
    {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (hs : ∀ n (t : Unit → Prog C (rs ++ ps) (rs ++ ps)),
      RecContract μ (t ()) req ens → RecContract μ (step n t) req ens) (d : Nat) :
    RecContract μ (recUnroll Prog.recBase step d) req ens :=
  recUnroll_induct (fun b => RecContract μ b req ens) (RecContract.base μ req ens) hs d

end Contract

section Rule

variable {Γ ps rs Γ' Γ₂ Γ₀ : Ctx}

/-- **A recursive call by its callee's contract** (`useContract` at a
`Stmt.callRec`, which runs as the call of its body): the goals "pre" and
"post". -/
theorem useRecContract {H : Hyps C [] Γ} {μ : Mutability} {f : Name} {d : Nat}
    {args : Args C Γ ps} {ret : CallRet Γ rs Γ'} {body : Unit → Prog C (rs ++ ps) (rs ++ ps)}
    {ω : Prog C Γ' Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {req : Fml C ps}
    {ens : Fml C (rs ++ (Olds ++ ps))} (hc : RecContract μ (body ()) req ens)
    («pre» : Valid (H.wrap (Fml.callPre args req)))
    («post» : Valid (H.wrap (Fml.callPost μ args ret ens ω κ φ)))
    (hn : ret.nVals = rs.length := by rfl) :
    Valid (H.wrap (.modal .box (.cons (.callRec f d args ret body) ω) κ φ)) := fun σ =>
  H.wrap_mono (φ := .modal .box (.cons (.call f args ret (body ())) ω) κ φ)
    (ψ := .modal .box (.cons (.callRec f d args ret body) ω) κ φ) (fun _ h => h) σ
    (useContractC_of_valid (f := f) (hc.1 ret) «pre» «post» hc.2.1 (hn ▸ hc.2.2) σ)

/-- A conjunction behind a context, from each conjunct behind it. -/
theorem valid_wrap_and {H : Hyps C [] Γ} {φ ψ : Fml C Γ} (h₁ : Valid (H.wrap φ))
    (h₂ : Valid (H.wrap ψ)) : Valid (H.wrap (.and φ ψ)) :=
  fun σ => H.wrap_and (χ := .and φ ψ) (fun _ a b => ⟨a, b⟩) σ (h₁ σ) (h₂ σ)

end Rule

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
    if [``Fml.all, ``Fml.imp, ``Fml.bind, ``Fml.upd, ``Fml.havoc].any χ'.isAppOf then
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
  evalTactic (← `(tactic| refine useRecContract (H := $HS) $h ?pre ?post))

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
    ?hc ?pre ?post))
  evalTactic (← `(tactic| case req => exact $req))
  evalTactic (← `(tactic| case ens => exact $ens))

/-- `rec_step ih`: an induction step's obligation, its recursive calls by the
hypothesis `ih` and everything else by the closer. -/
macro "rec_step " ih:ident : tactic => `(tactic| (
  sol_symex_rec
  all_goals first
    | sol_close
    | (rec_contract $ih
       all_goals (sol_symex; sol_close))))

/-- `rec_induct μ`: a `RecContract μ` of a recursive call's body by
induction over its frames (`RecContract.unroll`), each step by `rec_step`:
a function of no return or of one value return. -/
macro "rec_induct" : tactic => `(tactic| (
  apply RecContract.unroll
  intro n t ih
  refine ⟨?c, ?w, rfl⟩
  case c =>
    first | apply FunContract.forall_none | apply FunContract.forall_val
    apply FunContract.ofValidCtx []
    rec_step ih
  case w =>
    simp only [Prog.within, Stmt.within, ih.2.1, Bool.and_true]
    first | rfl | decide))

/-- `rec_auto`: a goal `⊨ φ` whose recursive calls are proved by the
contract `true`/`true` (no panic, the box's) at the most permissive
mutability (`nonpayable`: storage and ledger forgotten past the call), each
by induction over its frames: the strategy up to each call
(`sol_symex_rec`), the closer everywhere else.  The obligation as its own
contract (`docs/kernel-port.md`, "Recursion"): it closes where nothing past
a recursive call needs what the call did. -/
macro "rec_auto" : tactic => `(tactic| (
  sol_symex_rec
  all_goals first
    | sol_close
    | (rec_contract_by .nonpayable .tt .tt
       case hc => rec_induct
       all_goals (sol_symex; sol_close))))

end Solidity
