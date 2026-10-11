import Solidity.Calculus.SurfaceNotation
import Solidity.Calculus.TacticSyntax
import Solidity.Calculus.TreeData
import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.ChainBranches
import Solidity.Calculus.Literals

/-!
# The chain arrows, and the rewrites they name

The syntax of a chain (`~>`, `~*>`, `~[r]~>`, `~=>`), which
`Calculus/Chains.lean` reads on scoped lines, and what an arrow `~[r]~>`
names past the strategy: an update rule of the table (`rwTable`), a term
taclet (`TermTaclet`), a law of a memory read (`EvalLaw`) or a literal law
(`LitLaw`) (`rwArrow?`), and the instances of a law in a line's erasure
(`lawInstances`), which the scoped rewrites read their law's two sides
from (`Calculus/RewriteLaws.lean`).  `~=>` tries the arrows of
`rwAnyArrows` in order.  The chains themselves, past the program too, are
scoped (`Fml.Via`, W9.4).
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## An abstract postcondition

A chain is stated for any postcondition `φ`, a `Post C`, written by its
name in a line (`dl![m]{ … φ }`, printed back so).  A rewrite that asks it
which fresh variables it reads (`LineRw.simplifyFresh`) is proved from
`Post.noFresh` (`proveRw`). -/

/-- A postcondition `φ`: a formula that names no fresh variable
(`se1`, `sp1`, …), so that the rules' fresh names avoid it whatever it is.

Example: `⟨dl!{ alice.account.balance == 10 }, by decide⟩`, which
`{ fml := dl!{ alice.account.balance == 10 } }` abbreviates. -/
structure NFml.Post (C : Contract) where
  fml : NFml C
  noFresh : maxIdx fml.vars = 0 := by decide

attribute [coe] NFml.Post.fml

/-- A postcondition names no fresh variable: `simplifyUpdate` over it drops
a capture of the rules (`LineRw.simplifyFresh`). -/
theorem NFml.Post.freshVars_eq_nil (φ : NFml.Post C) : φ.fml.freshVars = [] := by
  rw [NFml.freshVars_eq, List.filter_eq_nil_iff]
  intro x hx
  have : x.idx ≤ 0 := φ.noFresh ▸ le_maxIdx hx
  simp only [bne_iff_ne, ne_eq, Decidable.not_not]
  omega

instance : Coe (NFml.Post C) (NFml C) := ⟨NFml.Post.fml⟩

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

namespace NFml.Chain
section Print
open Lean Meta PrettyPrinter Delaborator SubExpr

/-- A line of a chain: `dl{ φ }`, or Lean's own printing. -/
def ppLine (e : Lean.Expr) : MetaM Lean.Term := do
  let φ ← ppFml e
  if isEscape φ then escapeTerm e else `(dl{ $φ:dl_fml })

def chainNode (a : Lean.Term) (arrows : Array (TSyntax `chain_arrow × Lean.Term)) : Lean.Term :=
  ⟨mkNode ``chainStx #[a, mkNullNode (arrows.map fun (l, b) => mkNode groupKind #[l, b])]⟩

end Print
end NFml.Chain

namespace NFml.Chain
section Tactic
open Lean Elab Tactic Meta


/-- The Lean terms of a line (`fillSlots`): its modality, a variable, and
its postconditions `↑φ` by slot, each with its `Post.noFresh`. -/
structure Splice where
  modality : Option Lean.Expr := none
  fmls : Array Lean.Expr := #[]
  noFresh : Array Lean.Expr := #[]

/-- The line with each open postcondition `↑φ` in its slot. -/
partial def punch (C : Lean.Expr) : Lean.Expr → StateT Splice MetaM Lean.Expr
  | e@(.app f x) => do
    unless e.isAppOfArity ``Post.fml 2 && e.hasFVar do
      return .app (← punch C f) (← punch C x)
    let sp ← get
    if let some i := sp.fmls.findIdx? (· == e) then return slotExpr C i
    set { sp with fmls := sp.fmls.push e,
                  noFresh := sp.noFresh.push (mkApp2 (mkConst ``Post.noFresh) (e.getArg! 0) x) }
    return slotExpr C sp.fmls.size
  | .mdata _ e => punch C e
  | e => return e

/-- The modality of a line with its postconditions in their slots, when it
is a variable; no other variable may be left. -/
def modalityOf? (φ : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let fvs := (collectFVars {} φ).fvarIds
  if fvs.isEmpty then return none
  for x in fvs do
    let ty ← instantiateMVars (← x.getType)
    if ty.isConstOf ``Modality && fvs.size == 1 then return some (.fvar x)
    if ty.isAppOfArity ``NFml 1 then
      throwError "sol_chain: {mkFVar x} may name a fresh variable or have a modality: \
        take it as a postcondition, `{mkFVar x} : Post {ty.appArg!}`"
    unless ty.isConstOf ``Modality do
      throwError "sol_chain: {mkFVar x} is free in the line: only a modality `m` and \
        postconditions `φ : Post C` may be{indentExpr φ}"
  throwError "sol_chain: the line is under two modalities: take `cases` on one{indentExpr φ}"

/-- `some ψ = some ψ`, the proof of `φ.step = some ψ` and `φ.run n = some ψ`. -/
def someRefl (C ψ : Lean.Expr) : Lean.Expr :=
  let ty := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``NFml) C)
  mkApp2 (mkConst ``Eq.refl [1]) ty (mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``NFml) C) ψ)

/-- `a ≡ b` by the kernel's definitional equality: the check a `rfl` meets
when the declaration is added, made now instead of by the elaborator's
reduction (`Meta.whnf`), which on a whole line is two orders of magnitude
slower (`docs/kernel-port.md`).  `false` where either side has a
metavariable, which the kernel does not take. -/
def kernelDefEq (a b : Lean.Expr) : MetaM Bool := do
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  if a.hasMVar || b.hasMVar then return false
  return Kernel.isDefEqGuarded (← getEnv) (← getLCtx) a b

/-! ### Rewrite links

`~[n]~>` names a rewrite when `n` is no rule of the strategy: an update rule
of `Calculus/ChainRewrites.lean`'s table, or a law: a term taclet
(`TermTaclet`, `Calculus/TermTaclets.lean`), a law of a memory read
(`EvalLaw`, `Calculus/ChainRewrites.lean`), or a constant whose statement is
one.  The name stands for several rewrites, which the
line before tells apart: the position on the update spine, and for a law its
instance, found in the line as `rw` finds one.  They are tried in a fixed
order (`rwCandidates`), and the label is the first that gives the line after
— or, with the line after left `_`, the first that applies.  So the next
line is computed, as for a step, and the kernel checks `r.apply φ = some ψ`
by `rfl` — or, where the rewrite asks a postcondition `φ : Post C` what it
reads (`LineRw.simplifyFresh`), `sol_chain` proves it from `Post.noFresh`
(`proveRw`), as it proves a step's fresh index (`proveFresh`). -/

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

/-- Whether the constant `c` states a `TermTaclet`, an `EvalLaw` or a
`LitLaw`, under its arguments. -/
def isLaw (c : Lean.Name) : MetaM Bool := return (← lawKind? c).isSome

/-- The two sides of a law's statement, `TermTaclet C t t'`, `EvalLaw C u t t'`
or `LitLaw C t t'`. -/
def lawSides? (ty : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if ty.isAppOfArity ``TermTaclet 3 || ty.isAppOfArity ``LitLaw 3 then
    let args := ty.getAppArgs
    some (args[1]!, args[2]!)
  else if ty.isAppOfArity ``EvalLaw 4 || ty.isAppOfArity `Solidity.TermTacletS 4 then
    let args := ty.getAppArgs
    some (args[2]!, args[3]!)
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

/-- The formula below `n` updates of the line `e`. -/
partial def bodyBelow (e : Lean.Expr) : Nat → MetaM Lean.Expr
  | 0 => pure e
  | n + 1 => do
    let e ← whnf e
    if e.isAppOfArity ``NFml.upd 4 then bodyBelow e.appArg! n else pure e

/-- What a part of a line folds to under `NFml.concrete`, as far as the
elaborator can tell: `true`, `false`, a formula it must not look at (a
postcondition variable, or a fold that returns one), or anything else. -/
inductive LitStatus where
  | tt | ff | opaque | other
  deriving DecidableEq

/-- The skeleton of a formula (`Skel`), read off the line: the connectives,
the literal leaves, the updates; a postcondition variable, a program, a
quantifier and a `havoc` are opaque, and so is a connective's part whose
fold may return an opaque formula (`LitStatus`), which the folds then do
not test.  The status mirrors `NFml.concrete`'s folds so the flags are exact. -/
partial def skelOf (e : Lean.Expr) : MetaM (Skel × LitStatus) := do
  let e ← instantiateMVars e
  let isLit (t : Lean.Expr) : MetaM Bool := do
    return (← whnfTm t).isAppOfArity ``Term.lit 2
  match e.getAppFnArgs with
  | (``NFml.tt, #[_]) => return (.lit, .tt)
  | (``NFml.eq, #[_, a, b]) =>
    if (← isLit a) && (← isLit b) then
      let va := (← whnfTm a).appArg!
      let vb := (← whnfTm b).appArg!
      return (.lit, if ← isDefEq va vb then .tt else .ff)
    return (.lit, .other)
  | (``NFml.defined, #[_, t]) => return (.lit, if ← isLit t then .tt else .other)
  | (``NFml.not, #[_, a]) =>
    let (sa, ta) ← skelOf a
    let st := match ta with
      | .ff => .tt
      | .tt => .ff
      | .opaque => .opaque
      | .other => .other
    return (.not (ta == .opaque) sa, st)
  | (``NFml.and, #[_, a, b]) =>
    let (sa, ta) ← skelOf a
    let (sb, tb) ← skelOf b
    let st := if ta == .tt then tb else if ta == .ff then .ff
      else if tb == .tt then ta else if tb == .ff then .ff else .other
    return (.and (ta == .opaque) (tb == .opaque) sa sb, st)
  | (``NFml.imp, #[_, a, b]) =>
    let (sa, ta) ← skelOf a
    let (sb, tb) ← skelOf b
    let st := if ta == .tt then tb else if ta == .ff then .tt
      else if tb == .tt then .tt else if tb == .ff then (if ta == .opaque then .opaque else .other)
      else .other
    return (.imp (ta == .opaque) (tb == .opaque) sa sb, st)
  | (``NFml.upd, #[_, _, _, ψ]) => return (.upd (← skelOf ψ).1, .opaque)
  | _ => return (.opaque, .opaque)

/-- The skeleton of the formula below `n` updates of the line `e`, quoted. -/
def skelBelow (e : Lean.Expr) (n : Nat) : MetaM Lean.Expr := do
  return toExpr (← skelOf (← bodyBelow e n)).1

/-- The number of updates in front of a line. -/
partial def spineLen (e : Lean.Expr) : MetaM Nat := do
  let e ← whnf e
  if e.isAppOfArity ``NFml.upd 4 then return (← spineLen e.appArg!) + 1 else return 0

/-- The subterms of `e` with the head of `p`, outermost and leftmost first. -/
partial def subtermsLike (p e : Lean.Expr) : Array Lean.Expr :=
  let rec go (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
    let acc := if !e.hasLooseBVars && e.toHeadIndex == p.toHeadIndex &&
        e.headNumArgs == p.headNumArgs then acc.push e else acc
    match e with
    | .app f x => go x (go f acc)
    | .mdata _ e => go e acc
    | _ => acc
  go e #[]

/-- The positions on the spine of the storage term `S`: each storage subterm
reached through the storage argument of a save, a delete or a select, with
the context (`SCtx`) a hole there stands in. -/
partial def spinePositions (C S : Lean.Expr) (mk : Lean.Expr → Lean.Expr := id) :
    MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let here := (S, mk (mkApp (mkConst ``SCtx.hole) C))
  if S.isAppOfArity ``STerm.save 4 then
    let #[_, S', p, v] := S.getAppArgs | return #[here]
    return #[here] ++ (← spinePositions C S' fun K => mk (mkAppN (mkConst ``SCtx.save) #[C, K, p, v]))
  else if S.isAppOfArity ``STerm.delAt 3 then
    let #[_, S', p] := S.getAppArgs | return #[here]
    return #[here] ++ (← spinePositions C S' fun K => mk (mkAppN (mkConst ``SCtx.delAt) #[C, K, p]))
  else if S.isAppOfArity ``STerm.select 3 then
    let #[_, S', r] := S.getAppArgs | return #[here]
    return #[here] ++ (← spinePositions C S' fun K => mk (mkAppN (mkConst ``SCtx.select) #[C, K, r]))
  else return #[here]

/-- `lhs` matched against `e`: by unification, or, for a law in a storage
context (`find(K[X], q)` with `K` to find), `X` against a position on the
spine of `e`'s storage and `K` the context there. -/
def matchLaw (lhs e : Lean.Expr) : MetaM Bool := do
  if lhs.isAppOfArity ``Term.find 3 then
    let #[C, st, q] := lhs.getAppArgs | return ← isDefEq lhs e
    if st.isAppOfArity ``SCtx.fill 3 then
      let #[_, K, X] := st.getAppArgs | return ← isDefEq lhs e
      if (← instantiateMVars K).isMVar then
        unless e.isAppOfArity ``Term.find 3 do return false
        let #[_, S, q'] := e.getAppArgs | return false
        for (T, Kpos) in ← spinePositions C S do
          let s ← saveState
          if (← isDefEq X T) && (← isDefEq K Kpos) && (← isDefEq q q') then return true
          s.restore
        return false
  isDefEq lhs e

/-- The law `c` at the subterm `e`: `(t, t', h)` when `e` is its left side,
its arguments found there and its side conditions (`hp : p.hasSeg = true`,
…) closed by `rfl` or `decide`, as `sol_rw` closes them (`solRwSide`), or by
a hypothesis of the chain (`findOnDelAtBelow`'s `hk`), matched up to
reducible unfolding only: a hypothesis about another node would otherwise be
compared by unfolding the semantics, a second wasted per instance tried;
else why not, if a side condition is why. -/
def lawAt (c : Lean.Name) (e : Lean.Expr) :
    TermElabM (Except (Option MessageData) (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let pf ← mkConstWithFreshMVarLevels c
  let (args, _, ty) ← forallMetaTelescope (← inferType pf)
  let ty ← whnfR (← instantiateMVars ty)
  let some (lhs, rhs) := lawSides? ty | return .error none
  unless ← matchLaw lhs e do return .error none
  for a in args do
    let g := a.mvarId!
    if (← g.isAssigned) || !(← isProp (← g.getType)) then continue
    let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
    let g ← g.replaceTargetDefEq ty
    let closed ← try
        pure (← Term.withoutErrToSorry <|
          Tactic.run g (evalTactic (← `(tactic| first | rfl | decide | with_reducible assumption)))).isEmpty
      catch _ => pure false
    unless closed do
      return .error (some m!"the side condition{indentExpr ty}\nof {lastName c} closes by neither \
        `rfl`, `decide` nor a hypothesis")
  let pf ← instantiateMVars (mkAppN pf args)
  let t' ← instantiateMVars rhs
  if pf.hasExprMVar || t'.hasExprMVar then return .error none
  return .ok (← instantiateMVars lhs, t', pf)

/-- The instances `(t, t', h)` of the law `c` in the line `φ`, outermost and
leftmost first (`lawAt`), and the first side condition that did not close. -/
def lawInstances (c : Lean.Name) (φ : Lean.Expr) :
    TermElabM (Array (Lean.Expr × Lean.Expr × Lean.Expr) × Option MessageData) := do
  let lhs0 ← withoutModifyingState do
    let (_, _, ty) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels c))
    let ty ← whnfR (← instantiateMVars ty)
    let some (lhs, _) := lawSides? ty | throwError "not a law: {c}"
    -- a scoped law's side, written by `Tms`' reducible symbols, by its
    -- constructor (`Tm.app2`, …), as the line's terms are
    if ty.isAppOf `Solidity.TermTacletS then whnfR (← instantiateMVars lhs)
    else instantiateMVars lhs
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

/-- The term taclets `~=>` tries, after the update rules of `rwTable`: the
named rules of `TermTaclet`, and `findOnDelAtSave`. -/
def rwLaws : List Lean.Name :=
  [``TermTaclet.findOnSave, ``TermTaclet.findOnSaveFrame, ``TermTaclet.findMemberCons,
    ``TermTaclet.selectOnSaveMember, ``TermTaclet.selectOnSaveFrame, ``TermTaclet.selectOnDelAtMember,
    ``TermTaclet.selectOnDelAtFrame, ``TermTaclet.selectOnSaveMemberIn, ``TermTaclet.selectOnSaveFrameIn,
    ``TermTaclet.selectOnDelAtMemberIn, ``TermTaclet.selectOnDelAtFrameIn,
    ``TermTaclet.findOnDelAt, ``TermTaclet.findOnDelAtSave, ``TermTaclet.findOnDelAtValue,
    ``TermTaclet.delValueLit, ``TermTaclet.findOnDelAtBelow, ``TermTaclet.findOnDelAtFrame,
    ``TermTaclet.findOnPushFrame, ``TermTaclet.findOnPopFrame, ``TermTaclet.lenOnSaveFrame,
    ``TermTaclet.lenOnDelAtFrame]

/-- The laws of memory reads `~=>` tries, after the term taclets. -/
def rwEvalLaws : List Lean.Name :=
  [``EvalLaw.readOnWrite, ``EvalLaw.findCopyMem, ``EvalLaw.readCopySt, ``EvalLaw.readAddEqual,
    ``EvalLaw.readAddDifferent, ``EvalLaw.readAddDifferentIdentity, ``EvalLaw.readWriteDifferent,
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

syntax "#derivation " term : command

end Tactic

end NFml.Chain

end Solidity
