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
  let φ ← whnfR (← instantiateMVars φ)
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
  let (H, _, χ) ← Contract.peel C (mkApp2 (mkConst ``Hyps.nil) C nil) nil φ
  return some (C, H, ← whnfR χ)

/-- Whether `χ` is a box whose first statement is a recursive call. -/
def headRecCall (χ : Expr) : MetaM Bool := do
  unless χ.isAppOfArity ``Fml.modal 7 do return false
  let P ← whnfR (χ.getArg! 4)
  unless P.isAppOfArity ``Prog.cons 6 do return false
  let s ← whnfR (P.getArg! 4)
  return s.isAppOf ``Stmt.callRec

/-- `sol_symex_rec` on one goal, with fuel. -/
partial def loop (g : MVarId) (fuel : Nat) : TacticM (List MVarId) := do
  if fuel == 0 then return [g]
  let some (_, H, χ) ← goalParts g | return [g]
  if χ.isAppOfArity ``Fml.and 4 then
    let gs ← g.apply (← mkAppOptM ``valid_wrap_and #[none, none, some H, none, none])
    let mut out := []
    for g' in gs do out := out ++ (← loop g' fuel)
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

end Solidity
