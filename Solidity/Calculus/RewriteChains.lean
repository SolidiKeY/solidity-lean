import Solidity.Calculus.TacticSyntax
import Solidity.Calculus.TreeData
import Solidity.Calculus.TermLaws

/-!
# The chain arrows, and the rewrites they name

The syntax of a chain (`~>`, `~*>`, `~[r]~>`, `~=>`), which
`Calculus/Chains.lean` reads on scoped lines, and what an arrow `~[r]~>`
names past the strategy: an update rule of the table (`rwTable`), a term
taclet (`TermTaclet`), a law of a memory read (`EvalLaw`) or a literal law
(`LitLaw`) (`rwArrow?`, `Calculus/TermLaws.lean`), and the instances of a
law in a scoped line (`lawInstances`), which the rewrites of
`Calculus/RewriteScoped.lean` and `Calculus/RewriteLaws.lean` take their
law's two sides from.  `~=>` tries the arrows of `rwAnyArrows` in order.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## The notation

The arrows are the scoped chains' too (`Calculus/Chains.lean`), which
read a chain whose first line is scoped and hand any other here. -/


declare_syntax_cat chain_arrow
syntax "~> " : chain_arrow
syntax "~*> " : chain_arrow
syntax "~[" ident "]~> " : chain_arrow
syntax "~=> " : chain_arrow
/-- `φ ~~> ψ`: to prove `φ`, prove `ψ` — wherever `ψ` holds, `φ` does; on
scoped lines (`Calculus/Chains.lean`'s `leads%`). -/
syntax:50 term:51 " ~~> " term:51 : term

/-- `a ~> b`, `a ~*> b`, `a ~[r]~> b`, and chains of them: `a ~*> b ~[r]~> c ~*> d`. -/
syntax:50 (name := chainStx) term:51 (ppIndent(ppLine chain_arrow term:51))+ : term

open Lean in
/-- A chain whose first line is no scoped formula: refused, a chain's lines
are scoped (`Calculus/Chains.lean`). -/
def expandChainStx : Macro := fun stx =>
  Macro.throwErrorAt stx[0] "a chain's first line is a scoped formula: write it `dl!{ … }` under \
    `open scoped Solidity.Scoped`"

namespace Chain
section Print
open Lean Meta PrettyPrinter Delaborator SubExpr

/-- A chain's syntax, its first line and its links. -/
def chainNode (a : Lean.Term) (arrows : Array (TSyntax `chain_arrow × Lean.Term)) : Lean.Term :=
  ⟨mkNode ``chainStx #[a, mkNullNode (arrows.map fun (l, b) => mkNode groupKind #[l, b])]⟩

end Print
end Chain

namespace Chain
section Tactic
open Lean Elab Tactic Meta


/-! ### Rewrite links

`~[n]~>` names a rewrite when `n` is no rule of the strategy: an update rule
of the table (`rwTable`), or a law (`Calculus/TermLaws.lean`): a term taclet
(`TermTaclet`), a law of a memory read (`EvalLaw`), a literal law
(`LitLaw`), or a constant whose statement is one.  The name stands for
several rewrites, which the line before tells apart: the position on the
update spine, and for a law its instance, found in the scoped line as `rw`
finds one (`lawInstances`).  They are tried in a fixed order, and the label
is the first that gives the line after — or, with the line after left `_`,
the first that applies.  So the next line is computed, as for a step, and
the kernel checks `r.apply φ = some ψ` by `rfl`. -/

/-- What `~[n]~>` names past the strategy. -/
inductive RwArrow where
  /-- An update rule of the table (`rwTable`). -/
  | table (n : Lean.Name)
  /-- A law: a term taclet, or a constant whose statement is one. -/
  | law (c : Lean.Name)
  /-- A law of a memory read (`EvalLaw`), or a constant whose statement is one. -/
  | evalLaw (c : Lean.Name)
  /-- A literal law (`LitLaw`), or a constant whose statement is one. -/
  | litLaw (c : Lean.Name)

/-- The update rules an arrow names, KeY's names: `sequentialToParallel`
merges, `simplifyUpdate` drops, `applySkip` and the `applyOnRigid…` apply,
`concrete` folds the literal connectives. -/
def rwTable : List Lean.Name :=
  [`sequentialToParallel, `simplifyUpdate, `applySkip, `applyOnRigid, `applyOnRigidBox,
    `applyStorageBox, `applyOnPV, `concrete]

/-- The kind of law the constant `c` states under its arguments:
`TermTaclet`, `EvalLaw`, `LitLaw`, or none. -/
def lawKind? (c : Lean.Name) : MetaM (Option Lean.Name) := do
  let some info := (← getEnv).find? c | return none
  forallTelescope info.type fun _ ty => do
    let ty ← whnfR ty
    if ty.isAppOf ``TermTaclet then return some ``TermTaclet
    if ty.isAppOf ``EvalLaw then return some ``EvalLaw
    if ty.isAppOf ``LitLaw then return some ``LitLaw
    return none

/-- Whether the constant `c` states a law, under its arguments. -/
def isLaw (c : Lean.Name) : MetaM Bool := return (← lawKind? c).isSome

/-- The two sides of a law's statement, its last two arguments:
`TermTaclet t t'`, `EvalLaw t t'`, `LitLaw t t'`. -/
def lawSides? (ty : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if ty.isAppOf ``TermTaclet || ty.isAppOf ``EvalLaw || ty.isAppOf ``LitLaw then
    let args := ty.getAppArgs
    if args.size ≥ 2 then some (args[args.size - 2]!, args[args.size - 1]!) else none
  else none

/-- The arrow for the law `c` of kind `k`. -/
def RwArrow.ofLaw (k c : Lean.Name) : RwArrow :=
  if k == ``EvalLaw then .evalLaw c else if k == ``LitLaw then .litLaw c else .law c

/-- What `~[r]~>` names: `none` for a rule of the strategy (a constructor of
the scoped `Taclet` or `LeanTaclet`, `emptyModality`), else a
rewrite; any other name is an error, and so is a name that resolves to more
than one constant. -/
def rwArrow? (r : Ident) : MetaM (Option RwArrow) := do
  let n := r.getId
  let env ← getEnv
  if n == `emptyModality || env.contains (`Solidity.Taclet ++ n) ||
      env.contains (`Solidity.LeanTaclet ++ n) then
    return none
  if rwTable.contains n then return some (.table n)
  if env.contains (``TermTaclet ++ n) then return some (.law (``TermTaclet ++ n))
  if env.contains (``EvalLaw ++ n) then return some (.evalLaw (``EvalLaw ++ n))
  if env.contains (``LitLaw ++ n) then return some (.litLaw (``LitLaw ++ n))
  let cs := ((← resolveGlobalName n).filterMap fun (c, fs) =>
    if fs.isEmpty then some c else none).eraseDups
  match cs with
  | [c] => if let some k ← lawKind? c then return some (.ofLaw k c)
  | [] => pure ()
  | cs => throwError "~[{r}]~>: ambiguous, {r} may be {", ".intercalate (cs.map toString)}"
  throwError "~[{r}]~>: {r} is no rule: not a `Taclet` or `LeanTaclet` constructor, not an \
    update rule ({", ".intercalate (rwTable.map toString)}), not a term taclet (`TermTaclet`), \
    not a law of a memory read (`EvalLaw`), not a literal law (`LitLaw`)"

/-- The symbol of a term `Tm.appN … o …`: its constructor's name, where it
has one. -/
def tmSymbolHead? (e : Lean.Expr) : Option Lean.Name :=
  let k? : Option Nat :=
    if e.isAppOfArity ``Tm.app0 4 then some 3
    else if e.isAppOfArity ``Tm.app1 6 then some 4
    else if e.isAppOfArity ``Tm.app2 8 then some 5
    else if e.isAppOfArity ``Tm.app3 10 then some 6
    else none
  k?.bind fun k => (e.getArg! k).getAppFn.constName?

/-- The subterms of `e` with the head of `p`, outermost and leftmost first,
each once;
for a term, with its symbol too, where `p` names one (a typed term's
symbols are compared before any unification). -/
partial def subtermsLike (p e : Lean.Expr) : Array Lean.Expr :=
  let ps := tmSymbolHead? p
  -- each shared subterm once: a line's terms share their storages
  let rec go (e : Lean.Expr) (st : Array Lean.Expr × Std.HashSet Lean.Expr) :
      Array Lean.Expr × Std.HashSet Lean.Expr :=
    if st.2.contains e then st else
    let (acc, seen) := st
    let seen := seen.insert e
    let acc := if !e.hasLooseBVars && e.toHeadIndex == p.toHeadIndex &&
        e.headNumArgs == p.headNumArgs &&
        (match ps, tmSymbolHead? e with
          | some a, some b => a == b
          | _, _ => true) then acc.push e else acc
    match e with
    | .app f x => go x (go f (acc, seen))
    | .mdata _ e => go e (acc, seen)
    | _ => (acc, seen)
  (go e (#[], {})).1

/-- The positions on the spine of the scoped storage of members `S`: each
storage of members reached through the first argument of a `saveIn`, a
`delAtIn` or a `selectIn`, with the context (`SCtxS`) a hole there stands
in. -/
partial def spinePositions (S : Lean.Expr) (mk : Lean.Expr → MetaM Lean.Expr) :
    MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let ty ← whnfR (← inferType S)
  unless ty.isAppOfArity ``Tm 3 do return #[]
  let srt ← whnfR (ty.getArg! 2)
  unless srt.isAppOfArity ``Srt.sts 1 do return #[]
  let here := (S, ← mk (mkApp3 (mkConst ``SCtxS.hole) (ty.getArg! 0) (ty.getArg! 1) srt.appArg!))
  let args := S.getAppArgs
  if S.isAppOfArity ``Tm.app3 10 && args[6]!.isAppOf ``Op3.saveIn then
    let (S', p, v) := (args[7]!, args[8]!, args[9]!)
    return #[here] ++ (← spinePositions S' fun K => do mk (← mkAppM ``SCtxS.save #[K, p, v]))
  else if S.isAppOfArity ``Tm.app2 8 && args[5]!.isAppOf ``Op2.delAtIn then
    let (S', p) := (args[6]!, args[7]!)
    return #[here] ++ (← spinePositions S' fun K => do mk (← mkAppM ``SCtxS.delAt #[K, p]))
  else if S.isAppOfArity ``Tm.app1 6 && args[4]!.isAppOfArity ``Op1.selectIn 5 then
    -- the member's names from the symbol: its proof may be a computed line's
    -- `rfl`, whose type the unifier cannot read the names off
    let oa := args[4]!.getAppArgs
    let (sn, sn', f, hf, S') := (oa[1]!, oa[2]!, oa[3]!, oa[4]!, args[5]!)
    return #[here] ++ (← spinePositions S' fun K => do
      mk (← mkAppOptM ``SCtxS.select #[none, none, none, sn, sn', f, K, hf]))
  else return #[here]

/-- `lhs` matched against `e`: by unification, or, for a law in a context of
storages of members (`findIn(K[X], q)` with `K` to find), `X` against a
position on the spine of `e`'s storage and `K` the context there. -/
def matchLaw (lhs e : Lean.Expr) : MetaM Bool := do
  let la := lhs.getAppArgs
  if lhs.isAppOfArity ``Tm.app2 8 && la[5]!.isAppOf ``Op2.findIn then
    let st := la[6]!
    if st.isAppOfArity ``SCtxS.fill 6 then
      let K := st.getArg! 4
      let X := st.getArg! 5
      if (← instantiateMVars K).isMVar then
        let ea := e.getAppArgs
        unless e.isAppOfArity ``Tm.app2 8 && ea[5]!.isAppOf ``Op2.findIn do return false
        for (T, Kpos) in ← spinePositions ea[6]! pure do
          let s ← saveState
          if (← isDefEq X T) && (← isDefEq K Kpos) && (← isDefEq la[7]! ea[7]!) then return true
          s.restore
        return false
  if ← isDefEq lhs e then return true
  -- again, the arguments right to left: a proof in an earlier argument
  -- (`copySt`'s) may type only once a later one fixed its indices
  let ea := e.getAppArgs
  unless lhs.getAppFn == e.getAppFn && la.size == ea.size do return false
  let s ← saveState
  for k in (List.range la.size).reverse do
    unless ← isDefEq la[k]! ea[k]! do
      s.restore
      return false
  return true

/-- The law `c` at the subterm `e`: `(t, t', h)` when `e` is its left side,
its arguments found there by unification and its side conditions
(`hp : p.hasSeg = true`, …) closed by `rfl` or `decide`, as `sol_rw` closes
them, or by a hypothesis of the chain (`findOnDelAtBelow`'s `hk`), matched
up to reducible unfolding only: a hypothesis about another node would
otherwise be compared by unfolding the semantics, a second wasted per
instance tried; else why not, if a side condition is why. -/
def lawAt (c : Lean.Name) (e : Lean.Expr) :
    TermElabM (Except (Option MessageData) (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let pf ← mkConstWithFreshMVarLevels c
  let (args, _, ty) ← forallMetaTelescope (← inferType pf)
  let ty ← whnfR (← instantiateMVars ty)
  let some (lhs, rhs) := lawSides? ty | return .error none
  let lhs ← whnfR (← instantiateMVars lhs)
  unless ← matchLaw lhs e do return .error none
  -- the side conditions, in passes: one closed by `rfl` may fix the arguments
  -- another needs (`findMemberCons`' `h : p.shift? = some ⟨r, sn, hr, p'⟩`
  -- fixes the `hr` before it)
  let mut pending := args.toList.reverse
  let mut progress := true
  while progress do
    progress := false
    let mut rest := []
    for a in pending do
      let g := a.mvarId!
      if (← g.isAssigned) || !(← isProp (← g.getType)) then continue
      let s ← saveState
      let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
      let g ← g.replaceTargetDefEq ty
      -- by its shape: a chain's premise (`KindFreeAt`) by a hypothesis, a
      -- closed `Bool` or `Option` test by `rfl` alone (where `rfl` fails,
      -- `decide` evaluates the same test, at the price of an instance search
      -- over the whole term), anything else by `rfl` or `decide`
      let tac ← if ty.isAppOf ``Tm.KindFreeAt then
          `(tactic| first | with_reducible assumption |
              exact Tm.KindFreeAt.ofNil (by with_reducible assumption) rfl rfl)
        else if ty.isAppOfArity ``Eq 3 && !ty.hasExprMVar &&
            ((ty.getArg! 0).isConstOf ``Bool || (ty.getArg! 0).isAppOfArity ``Option 1) then
          `(tactic| rfl)
        else `(tactic| first | rfl | decide | with_reducible assumption)
      let closed ← try
          pure (← Term.withoutErrToSorry <| Tactic.run g (evalTactic tac)).isEmpty
        catch _ => pure false
      if closed then progress := true
      else
        s.restore
        rest := rest ++ [a]
    pending := rest
  for a in pending do
    let g := a.mvarId!
    if (← g.isAssigned) || !(← isProp (← g.getType)) then continue
    let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
    -- an argument the condition fixes, not yet known, prints as `?_`
    let fmt ← withOptions (fun o => o.setBool `pp.mvars false) (ppExpr ty)
    return .error (some m!"the side condition{indentD fmt}\nof {lastName c} closes by neither \
      `rfl`, `decide` nor a hypothesis")
  let pf ← instantiateMVars (mkAppN pf args)
  let t' ← instantiateMVars rhs
  if pf.hasExprMVar || t'.hasExprMVar then return .error none
  return .ok (← instantiateMVars lhs, t', pf)

/-- The instances `(t, t', h)` of the law `c` in `φ` (a scoped line, or a
list of its terms), outermost and leftmost first (`lawAt`), and the first
side condition that did not close.  The law's left side, written by `Tms`'
reducible symbols, is read by its constructor (`Tm.app2`, …), as the line's
terms are. -/
def lawInstances (c : Lean.Name) (φ : Lean.Expr) :
    TermElabM (Array (Lean.Expr × Lean.Expr × Lean.Expr) × Option MessageData) := do
  let lhs0 ← withoutModifyingState do
    let (_, _, ty) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels c))
    let ty ← whnfR (← instantiateMVars ty)
    let some (lhs, _) := lawSides? ty | throwError "not a law: {c}"
    whnfR (← instantiateMVars lhs)
  let mut out := #[]
  let mut failed := none
  for e in subtermsLike lhs0 φ do
    let s ← saveState
    let r ← try lawAt c e catch _ => pure (.error none)
    s.restore
    match r with
    | .ok i => unless out.any (·.2.2 == i.2.2) do out := out.push i
    | .error m => if failed.isNone then failed := m
  return (out, failed)

/-- The law `c` and its twins in a storage of members (`findOnSave` and
`findOnSaveIn`; `selectOnSaveMember`, `selectOnSaveMemberIn` and
`selectOnSaveMemberAt`, …): a link names each by the first. -/
def lawTwins (env : Environment) (c : Lean.Name) : List Lean.Name :=
  c :: ([c.appendAfter "In", c.appendAfter "At"].filter env.contains)

/-- The term taclets `~=>` tries, after the update rules of `rwTable`: the
named rules of `TermTaclet`, and `findOnDelAtSave`. -/
def rwLaws : List Lean.Name :=
  [``TermTaclet.findOnSave, ``TermTaclet.findOnSaveIn, ``TermTaclet.findOnSaveFrame,
    ``TermTaclet.findMemberCons, ``TermTaclet.findMemberConsIn,
    ``TermTaclet.selectOnSaveMember, ``TermTaclet.selectOnSaveFrame,
    ``TermTaclet.selectOnDelAtMember, ``TermTaclet.selectOnDelAtFrame,
    ``TermTaclet.selectOnSaveMemberIn, ``TermTaclet.selectOnSaveFrameIn,
    ``TermTaclet.selectOnDelAtMemberIn, ``TermTaclet.selectOnDelAtFrameIn,
    ``TermTaclet.selectOnSaveMemberAt, ``TermTaclet.selectOnSaveFrameAt,
    ``TermTaclet.selectOnDelAtMemberAt, ``TermTaclet.selectOnDelAtFrameAt,
    ``TermTaclet.findOnDelAt, ``TermTaclet.findOnDelAtSave, ``TermTaclet.findOnDelAtValue,
    ``TermTaclet.delValueLit, ``TermTaclet.findOnDelAtBelow,
    ``TermTaclet.findOnDelAtBelowIn, ``TermTaclet.findOnDelAtFrame,
    ``TermTaclet.findOnPushFrame, ``TermTaclet.findOnPopFrame, ``TermTaclet.lenOnSaveFrame,
    ``TermTaclet.lenOnDelAtFrame]

/-- The laws of memory reads `~=>` tries, after the term taclets. -/
def rwEvalLaws : List Lean.Name :=
  [``EvalLaw.readOnWrite, ``EvalLaw.findCopyMem, ``EvalLaw.findCopyMemIn, ``EvalLaw.readCopySt,
    ``EvalLaw.readAddEqual, ``EvalLaw.readAddDifferent,
    ``EvalLaw.readAddDifferentIdentity, ``EvalLaw.readWriteDifferent,
    ``EvalLaw.readWriteDifferentIdentity, ``EvalLaw.readOnWriteIdentity]

/-- The literal laws `~=>` tries, after the laws of memory reads. -/
def rwLitLaws : List Lean.Name :=
  [``LitLaw.add_literals, ``LitLaw.sub_literals, ``LitLaw.div_literals, ``LitLaw.leq_literals,
    ``LitLaw.less_literals, ``LitLaw.greater_literals, ``LitLaw.geq_literals]

/-- What `~=>` tries, in order: the update rules, then the laws in scope. -/
def rwAnyArrows : MetaM (List (String × RwArrow)) := do
  let env ← getEnv
  let laws ← rwLaws.filterM fun c => if env.contains c then isLaw c else pure false
  let evalLaws := rwEvalLaws.filter env.contains
  let litLaws := rwLitLaws.filter env.contains
  return rwTable.map (fun n => (n.toString, .table n)) ++
    laws.map (fun c => ((lastName c).toString, .law c)) ++
    evalLaws.map (fun c => ((lastName c).toString, .evalLaw c)) ++
    litLaws.map fun c => ((lastName c).toString, .litLaw c)

/-- `sol_chain`: a chain proved link by link, by the kernel
(`Calculus/Chains.lean`). -/
syntax "sol_chain" : tactic

/-- `sol_chain` on a goal no chain elaborator takes: a statement whose own
elaboration failed is left with its error, any other goal refused. -/
elab_rules : tactic
  | `(tactic| sol_chain) => do
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    if ty.hasSyntheticSorry then
      g.admit
      replaceMainGoal []
    else throwError "sol_chain: the goal is no chain on scoped lines{indentExpr ty}"

syntax "#derivation " term : command

end Tactic

end Chain

end Solidity
