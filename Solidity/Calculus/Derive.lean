import Solidity.Calculus.Symex
import Solidity.Calculus.Completeness
import Solidity.Calculus.ProofTree
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.TreeData
import Solidity.Calculus.CloseFrame

/-!
# The scoped strategy as a walk: `sol_derive`, and `sol_close` on a leaf

`sol_prove` on a goal `Valid φ` is the walk of `⊢` (`Proves.valid`, then
`Calculus/ProvesDerive.lean`'s `Seq.prove`, decision 89 extended): the
strategy and the closer as one kernel evaluation, the leaves it leaves
the walk's own sequents.  This module has what that walk shares with
the tactics that write it out: `Derive.fuel`, the steps `sol_derive`'s
walk is given (`sol_prove`'s walk is bounded by `Seq.fuel`,
`Derive.budget`), the leaf search of `sol_prove?` (`Derive.searchLeaf`), and
`sol_derive`/`sol_derive?`, the strategy as one `apply` per rule.
`sol_close` reads a scoped leaf without the erasure
(`Calculus/CloseScoped.lean`).
-/

namespace Solidity

open Solidity (Modality)

variable {C : Contract}

namespace Derive

/-- The steps `sol_derive`'s walk is given. -/
def fuel : Nat := 5000

end Derive

/-! ## The leaf search: `sol_prove?`'s tries

`sol_prove?` runs the scoped `sol_prove` (`Calculus/ProvesDerive.lean`) and
then tries each leaf it leaves, a scoped sequent, with the scoped leaf
tactics (`leafTacs`), each try with its own heartbeats; the replay is
`sol_prove` and each leaf's lines (`replayLines`). -/

namespace Derive

open Lean Elab Tactic Meta

/-- The steps `sol_prove`'s walk is given, down a path and in all. -/
def budget : Nat := 20000

/-- The tactics `sol_prove?` tries on a leaf, in order, each a sequence of
lines: `sol_leaf` (the sequent as `⊨ ψ`, `Calculus/ProvesDerive.lean`), then
`sol_decide` on the scoped leaf, then
`sol_close` and `sol_spec_close` (`Calculus/CloseScoped.lean`).  A leaf past
the closer's bounds (`small = false`) gets no step that reduces it, only
`sol_close` and `sol_spec_close`, whose `simp`, `omega` and `grind` heed
heartbeats. -/
def leafTacs (small : Bool := true) : Array (Array String) :=
  (if small then #[#["sol_leaf", "sol_decide"]] else #[]) ++
    #[#["sol_leaf", "sol_close"], #["sol_leaf", "sol_spec_close"]]

/-- The first of `leafTacs` that closes the leaf `l`, with the raw
heartbeats it used; `none` when none does.  Each try runs with its own
heartbeats and its state rolled back when it fails.  A leaf past the
closer's bounds (`fits`, the scoped leaf's `Seq.goalFits`,
`Calculus/ProvesDerive.lean`) is not reduced. -/
def searchLeaf (l : MVarId) (fits : MVarId → MetaM Bool) :
    TacticM (Option (Array String × Nat)) := do
  let env ← getEnv
  for src in leafTacs (← fits l) do
    let t ← src.mapM fun line =>
      match Parser.runParserCategory env `tactic line with
      | .ok stx => pure (⟨stx⟩ : TSyntax `tactic)
      | .error e => throwError "sol_prove?: {e}"
    let s ← saveState
    let h0 ← IO.getNumHeartbeats
    let ok ← tryCatchRuntimeEx
      (withCurrHeartbeats do
        setGoals [l]
        for x in t do Term.withoutErrToSorry (withoutRecover (evalTactic x))
        pure (← getUnsolvedGoals).isEmpty)
      fun _ => pure false
    if ok then return some (src, (← IO.getNumHeartbeats) - h0)
    s.restore
  return none

/-- What `proveSearch` found: each leaf's name and lines (`sorry` for one
no try closes), the leaves no try closes, and the raw heartbeats the replay
needs, the walk's and the closing tries' (the failed tries are not
replayed). -/
structure Search where
  found : List (Lean.Name × Array String)
  open_ : List MVarId
  heartbeats : Nat
  steps : Option Nat := none

/-- Recover the bounded walk certified by the generated proof, without rerunning it. -/
partial def replaySteps (e : Expr) : Option Nat :=
  if e.isAppOfArity `Solidity.Proves.of_residueWithin 9 then
    let n := e.getArg! 1
    let n := if n.isAppOfArity ``OfNat.ofNat 3 then n.getArg! 1 else n
    match n with
    | .lit (.natVal n) => some n
    | _ => none
  else match e with
    | .app f a => replaySteps f <|> replaySteps a
    | .lam _ _ b _ | .forallE _ _ b _ | .mdata _ b => replaySteps b
    | .letE _ _ v b _ => replaySteps v <|> replaySteps b
    | _ => none

/-- The walk `prove` on `g`, then `searchLeaf` on each leaf it leaves, the
open ones left as goals; with `stopAtOpen`, the search ends at the first
open leaf.  The one loop of `#solkey_derive?`. -/
def proveSearch (g : MVarId) (prove : MVarId → MetaM (List MVarId))
    (fits : MVarId → MetaM Bool) (stopAtOpen : Bool := false) : TacticM Search := do
  let h0 ← IO.getNumHeartbeats
  let leaves ← prove g
  let steps := replaySteps (← instantiateMVars (.mvar g))
  let mut hb : Nat := (← IO.getNumHeartbeats) - h0
  let mut found : List (Lean.Name × Array String) := []
  let mut open_ : List MVarId := []
  for l in leaves do
    let name ← l.getTag
    match ← searchLeaf l fits with
    | some (t, h) =>
      found := found ++ [(name, t)]
      hb := hb + h
    | none =>
      open_ := open_ ++ [l]
      found := found ++ [(name, #["sorry"])]
      if stopAtOpen then break
  return { found, open_, heartbeats := hb, steps }

/-- Whether a replay of `hb` raw heartbeats fits in one declaration's
`maxHeartbeats`.  Each try ran with heartbeats of its own; the replay runs
them all in one declaration, so their sum is what it needs, up to the
elaboration of the statement and the `case` lines. -/
def replayFits (hb : Nat) : CoreM Bool := do
  let max := (← read).maxHeartbeats
  return max == 0 || hb ≤ max

/-- The replay of a `sol_prove` whose leaves are closed by `found`:
`sol_prove`, then each leaf's lines, under `case leafᵢ =>` when there are
several. -/
def replayLines (found : List (Lean.Name × Array String)) (steps : Option Nat := none) : Array String :=
  let first := steps.map (fun n => s!"sol_prove (steps := {n})") |>.getD "sol_prove"
  match found with
  | [(_, body)] => #[first] ++ body
  | _ => found.foldl (fun ls (n, body) =>
      (ls.push s!"case {n} =>") ++ body.map ("  " ++ ·)) #[first]

end Derive

/-! ## `sol_derive`: the strategy as a walk

On a scoped sequent `H ⊢ φ` (`Proves`), one `refine` per step: a
precondition, a quantifier, an update or a hidden binder into the context,
an empty modality through its frames (the first, the second and this by
solkey's names, `impRight`, `allRight`, `emptyModality`,
`Calculus/ProofTree.lean`), `closeTrue`, or the rule the
statement fires, named as solkey names it (`ruleOf?`,
`Calculus/Completeness.lean`) and cited by its taclet
(`Taclet.step_eq .rule`, `LeanTaclet.toStep .rule`).  A goal with no
modality is a leaf: `sol_derive` leaves it, `sol_derive?` closes it where
it can (`sol_leaf`, then the scoped `sol_close`, as the tree's leaves
close).

Under `open scoped Solidity.Scoped` (`Walk.surfaceOn`) `sol_derive?`
writes today's short walk instead, which the scope's macros read
(`Calculus/WalkSyntax.lean`): `apply Proves.valid`, solkey's aliases
(`apply impRight`, `apply allRight`, `apply emptyModality`), one `apply
update .r` (`unfold`, `splitBox`, `split`, `done`, `Proves.check`, `cases`,
`branches`, `invBox`, the `…Lean` forms) per rule, `sol_leaf; sol_close` at
a leaf (`true` too), and nothing for the steps KeY does not show
(`core_silent`: a scope's end, a hidden binder, the parameters' `∀`).  The
walk runs those very lines, so the suggestion is what was checked; where a
short line fails, the explicit `refine` stands in. -/

namespace Walk

open Lean Elab Tactic Meta

/-- The explicit arguments of the constructor `c` after the rule `d`, but
those a default proves (`hR`). -/
def ctorArgs (c : Lean.Name) : MetaM (Array Lean.Name) := do
  let some info := (← getEnv).find? c | throwError "unknown constant {c}"
  forallTelescope info.type fun xs _ => do
    let mut out : Array Lean.Name := #[]
    let mut seen := false
    for x in xs do
      let ld ← x.fvarId!.getDecl
      unless ld.binderInfo.isExplicit do continue
      -- the rule set's admission (`hR`) is proved by its default
      if ld.type.isAppOf ``autoParam then continue
      if !seen then seen := true; continue
      out := out.push ld.userName
    return out

/-- The rule `d` by the constructor `c`, two ways: `apply c d`, its goals
tagged by the constructor's arguments (`thn`, `els`), with `rfl` for a
non-emptiness check (`hne`); and `refine c d ?_ … ?_`, where a side
condition of the rule needs the goal to be elaborated.  A rule of labelled
goals (`cases`, `branches`) is the `apply` with its goals taken apart. -/
def ctorTacs (c : Lean.Name) (d : Lean.Term) : MetaM (Array (Array (TSyntax `tactic))) := do
  let names ← ctorArgs c
  let f ← ProofTree.short c
  let rflId := mkIdent `rfl
  let pre := names.toList.takeWhile (· == `hne) |>.length
  let rfls : Array Lean.Term := (List.replicate pre (⟨rflId⟩ : Lean.Term)).toArray
  let args ← names.mapM fun n => do
    if n == `hne then `(term| $rflId:ident) else `(term| ?_)
  let app ← `(tactic| apply $f $d $rfls*)
  -- a rule of labelled goals (`∀ f ∈ fs, …`): taken apart on its `apply`
  -- line, one goal per outcome, as today's walk writes it
  if c == ``Proves.cases || c == ``Proves.branches then
    return #[#[← ProofTree.takeApart app],
      #[← `(tactic| refine $f $d $args*)]]
  return #[#[app], #[← `(tactic| refine $f $d $args*)]]

/-- Whether today's walk text reads here: `open scoped Solidity.Scoped`
is in effect (its `core_surface%` reads `true`, `surfaceOn`, read
without importing the switch) and the walk's macros are loaded
(`Calculus/WalkSyntax.lean`). -/
def surfaceOn : MetaM Bool := do
  unless (← getEnv).contains `Solidity.evalCoreSilent do return false
  let stx := mkNode `Solidity.coreSurfaceFlag #[mkAtom "core_surface%"]
  let some out ← (liftMacroM (expandMacro? stx) : TermElabM _).run' | return false
  return out.isIdent && out.getId.eraseMacroScopes == `true

/-- Today's walk line for the scoped rule `c` firing the taclet `.r`
(`lean`: a Lean taclet; `box`: under the box), as the scope's macros read
it (`Calculus/WalkSyntax.lean`). -/
def shortTac (c : Lean.Name) (r : Lean.Name) (lean box : Bool) :
    MetaM (Option (TSyntax `tactic)) := do
  let rule := ProofTree.dotIdent r
  let kind? : Option Lean.Name :=
    if c == ``Proves.update || c == ``Proves.updates then some `update
    else if c == ``Proves.unfold || c == ``Proves.bind || c == ``Proves.inline then
      some (if lean then `unfoldLean else `unfold)
    else if c == ``Proves.split || c == ``Proves.guardedUpdates then some (if box then `splitBox else `split)
    else if c == ``Proves.check then some (if lean then `checkLean else `Proves.check)
    else if c == ``Proves.done then some (if lean then `doneLean else `done)
    else if c == ``Proves.cases then some `cases
    else if c == ``Proves.branches then some `branches
    else if c == ``Proves.inv then some (if box then `invBox else `invLean)
    else none
  let some kind := kind? | return none
  let app ← `(tactic| apply $(mkIdent kind) $rule)
  -- a rule of labelled goals (`∀ f ∈ fs, …`): taken apart on its `apply`
  -- line, one goal per outcome, as today's walk writes it
  if c == ``Proves.cases || c == ``Proves.branches then
    return some (← ProofTree.takeApart app)
  return some app

/-- The steps that may apply at the goal `g`, each as tactics, in the order
tried; none at a leaf.  `short`: today's walk line first (`shortTac`), the
explicit `refine` after it; `true` is then a leaf, closed as today's.  A
step's note, where it has one, is the solkey name of a rule its lines do not
write (`-- storageFieldReadFind` after a premise proved by `rfl`). -/
def movesAt (g : MVarId) (short : Bool := false) :
    MetaM (Array (Array (TSyntax `tactic) × Option String)) := g.withContext do
  let plain (ms : Array (Array (TSyntax `tactic))) := ms.map (·, (none : Option String))
  let ty ← instantiateMVars (← g.getType)
  let_expr Proves C _ Γ₀ Γ H φ0 := ty | return #[]
  let φ ← whnf φ0
  let one (c : Lean.Name) : MetaM (Array (Array (TSyntax `tactic))) := do
    return #[#[← `(tactic| refine $(← ProofTree.short c) ?_)]]
  let alias (n : Lean.Name) (c : Lean.Name) : MetaM (Array (Array (TSyntax `tactic))) := do
    if short then return #[#[← `(tactic| apply $(mkIdent n))]] ++ (← one c)
    one c
  match φ.getAppFn.constName? with
  | some ``Fml.imp => plain <$> alias `impRight ``Proves.impRight
  | some ``Fml.all => plain <$> alias `allRight ``Proves.allRight
  | some ``Fml.and =>
    let mf ← whnfD (← mkAppM ``Fml.modalFree #[φ])
    if mf.isConstOf ``Bool.true then return #[]
    let both ← `(tactic| refine $(← ProofTree.short ``Proves.andRight) ?_ ?_)
    if short then return plain #[#[← `(tactic| apply $(mkIdent `andRight))], #[both]]
    return plain #[#[both]]
  | some ``Fml.upd => plain <$> alias `updIntro ``Proves.updIntro
  | some ``Fml.bind => plain <$> one ``Proves.bindIntro
  | some ``Fml.tt =>
    if short then return #[]
    return plain
      #[#[← `(tactic| exact $(← ProofTree.short ``Proves.closeTrue) $(mkIdent `rfl):ident)]]
  | some ``Fml.modal =>
    let args := φ.getAppArgs
    let m := args[args.size - 4]!
    let P ← whnf args[args.size - 3]!
    if P.isAppOf ``Prog.nil then return plain (← alias `emptyModality ``Proves.emptyModality)
    let k := mkAppN (mkConst ``Hyps.fresh) #[C, Γ₀, Γ, H, φ]
    let some (_, r, _, c) ← ProofTree.ruleAt? k m P | return #[]
    let rName := Lean.Name.mkSimple r.getString!
    let rule := mkIdent rName
    let lean := r.getPrefix != ``Taclet
    let d ← if !lean then
        `(term| ($(← ProofTree.short ``Taclet.step_eq) .$rule:ident))
      else `(term| ($(← ProofTree.short ``LeanTaclet.toStep) .$rule:ident))
    -- a rule whose line `apply` cannot match (a read into a hole, whose
    -- `fill` does not reduce while unifying): the taclet elaborated after
    -- the goal (`by exact`), as `core_rule` does, so the line keeps its name
    let late ← ctorTacs c (← `(term| (by exact $d)))
    -- and where the taclet's side conditions are decided before its schema
    -- variables are read off the goal (a read into a hole after a hidden
    -- binder), the premise `Stmt.step` computes, by `rfl`; the line names
    -- no rule, so the rule's solkey name follows it as a comment
    let byStep ← ctorTacs c (← `(term| $(mkIdent `rfl):ident))
    let explicit := plain ((← ctorTacs c d) ++ late.extract (late.size - 1) late.size) ++
      (byStep.extract (byStep.size - 1) byStep.size).map (·, some rName.toString)
    if short then
      let box := (← whnf m).isConstOf ``Modality.box
      if let some t ← shortTac c rName lean box then return plain #[#[t]] ++ explicit
    return explicit
  | _ => return #[]

/-- A leaf closed as a walk ends, at the empty outer scope: `sol_leaf` and
the scoped `sol_close`, its lines, or none where the closer does not close
it (the state rolled back). -/
def closeLeaf (g : MVarId) : TacticM (Option (Array String)) := do
  let ty ← instantiateMVars (← g.getType)
  let_expr Proves _ _ Γ₀ _ _ _ := ty | return none
  unless (← whnfR Γ₀).isAppOf ``List.nil do return none
  let tacs := #[← `(tactic| sol_leaf), ← `(tactic| sol_close)]
  let s ← saveState
  let ok ← tryCatchRuntimeEx
    (withCurrHeartbeats do return (← ProofTree.runOn g tacs).isEmpty) fun _ => pure false
  unless ok do s.restore; return none
  return some (← tacs.mapM fun t => (ProofTree.tacLines t : MetaM _)).flatten

/-- Whether the goal `g` is `¬X → ψ` with `X` a program's (a self-call's
`catch` goal, `ExtCall.selfFails`): the context cannot keep `¬X` for the
closer, so the walk proves `X` instead (`notLeft`) or hides it
(`hideLeft`). -/
def negModalGoal? (g : MVarId) : MetaM Bool := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some φ0 := (if ty.isAppOf ``Proves || ty.isAppOf `Solidity.ProvesC then ty.getAppArgs.back?
    else none) | return false
  let φ ← whnf φ0
  unless φ.isAppOf ``Fml.imp do return false
  let a ← whnf (φ.getArg! (φ.getAppNumArgs - 2))
  unless a.isAppOf ``Fml.not do return false
  let mf ← whnfD (← mkAppM ``Fml.modalFree #[a.appArg!])
  return mf.isConstOf ``Bool.false

/-- The walk from `g`: its script, lines indented relative to the first, a
`case` per goal of a step with several, `sorry` for a leaf; the leaves are
collected in `open`. -/
partial def walk (fuel : IO.Ref Nat) (leaves : IO.Ref (Array MVarId)) (g : MVarId)
    (close : Bool := false) (short : Bool := false) : TacticM (Array String) := do
  let n ← fuel.get
  if n == 0 then throwError "sol_derive: more than {Derive.fuel} steps"
  fuel.set (n - 1)
  -- today's text: the steps KeY does not show are taken unwritten, as each
  -- of the scope's lines takes them first (`core_silent`)
  let g ← if short then
      match ← ProofTree.runOn g #[⟨mkNode `Solidity.coreSilent #[mkAtom "core_silent"]⟩] with
      | [g'] => pure g'
      | _ => pure g
    else pure g
  -- `¬X → ψ`, `X` a program's: `X` proved instead where the walk closes
  -- it (`notLeft`), else the premise hidden (`hideLeft`)
  if ← tryCatchRuntimeEx (withCurrHeartbeats (negModalGoal? g)) fun _ => pure false then
    let s ← saveState
    let nl ← `(tactic| refine $(← ProofTree.short ``Proves.notLeft) ?_)
    let r ← tryCatchRuntimeEx (do
        let [gx] ← withCurrHeartbeats (ProofTree.runOn g #[nl]) | return none
        let ls ← IO.mkRef #[]
        let lines ← walk fuel ls gx (close := true) short
        return if (← ls.get).isEmpty then some lines else none)
      fun _ => pure none
    if let some lines := r then return (← ProofTree.tacLines nl) ++ lines
    s.restore
    let hl ← `(tactic| refine $(← ProofTree.short ``Proves.hideLeft) ?_)
    let [g'] ← withCurrHeartbeats (ProofTree.runOn g #[hl])
      | throwError "sol_derive: hideLeft failed"
    return (← ProofTree.tacLines hl) ++ (← walk fuel leaves g' close short)
  let mut step := none
  for (tacs, note) in ← movesAt g short do
    let s ← saveState
    -- each try with its own heartbeats, a timeout a failed try
    let r ← tryCatchRuntimeEx (some <$> withCurrHeartbeats (ProofTree.runOn g tacs))
      fun _ => do s.restore; pure none
    if let some gs := r then
      step := some (tacs, note, gs)
      break
  let some (tacs, note, gs) := step
    | if close then
        if let some lines ← closeLeaf g then return lines
      leaves.modify (·.push g); return #["sorry"]
  let head := (← tacs.mapM fun t => (ProofTree.tacLines t : MetaM _)).flatten
  let head := match note with
    | some n => head.modify (head.size - 1) (· ++ s!" -- {n}")
    | none => head
  match gs with
  | [g'] => return head ++ (← walk fuel leaves g' close short)
  | gs =>
    -- a goal's name is its tag's first part past the step's goal's (`els`
    -- under `thn`, past a silent step's `els.h`); `and_intros`' goals
    -- (`refine_1`, …) have none to cite
    let parent := (← g.getTag).components
    let tags ← gs.mapM fun g' => do
      let cs := (← g'.getTag).components
      let cs := if parent.isPrefixOf cs then cs.drop parent.length else cs
      match cs.head? with
      | some (.str _ l) => return if l.startsWith "refine_" then none else some l
      | _ => return none
    -- cited by name when every goal of the step has one (`thn`, `els`); else
    -- bullets, in order, as today's walk takes a rule's goals apart (`cases`'
    -- formula goal is `fml`, its updates' goals have no name)
    let cite := tags.all Option.isSome
    let mut out := head
    for g' in gs, tag in tags do
      let body ← walk fuel leaves g' close short
      match cite, tag with
      | true, some l =>
        out := out.push s!"case {l} =>"
        out := out ++ body.map ("  " ++ ·)
      | _, _ => out := out ++ body.mapIdx fun i l => (if i == 0 then "· " else "  ") ++ l
    return out

/-- The walk from the goal `g` (`Valid φ` starts with `Proves.valid`):
its lines, and the leaves it leaves. -/
def run (g : MVarId) (close : Bool := false) (short : Bool := false) :
    TacticM (Array String × List MVarId) := do
  let (pre, g) ← match ← Symex.validGoal? g with
    | some _ =>
      let t ← if short then `(tactic| apply $(mkIdent `Proves.valid))
        else `(tactic| refine $(← ProofTree.short ``Proves.valid)
          ($(mkIdent `R) := $(← ProofTree.short ``RuleSet.all)) ?_)
      let [g'] ← ProofTree.runOn g #[t] | throwError "sol_derive: `refine Proves.valid ?_` failed"
      pure ((← ProofTree.tacLines t), g')
    | none => pure (#[], g)
  let fuel ← IO.mkRef Derive.fuel
  let leaves ← IO.mkRef #[]
  let lines ← walk fuel leaves g close short
  return (pre ++ lines, (← leaves.get).toList)

/-- A scoped goal: `Valid φ` or `H ⊢ φ` over `Proves`. -/
def isCoreGoal (g : MVarId) : MetaM Bool := do
  let ty ← instantiateMVars (← g.getType)
  return ty.isAppOf ``Valid || ty.isAppOf ``Proves

end Walk

/-- `sol_derive` on a scoped goal, the expansion of `sol_derive` tried
before today's (below): today's is a macro that never fails, so an
elaborator of the same syntax would never run. -/
syntax (name := solDeriveScoped) "sol_derive_scoped" : tactic

/-- `sol_derive` is first `sol_derive_scoped`, which fails on a goal that is
not scoped; Lean then expands today's macro. -/
macro_rules | `(tactic| sol_derive) => `(tactic| sol_derive_scoped)

open Lean Elab Tactic Meta in
/-- `sol_derive` on a scoped goal: the strategy as a walk of `Proves`
rules, leaving the leaves (`Walk.run`). -/
@[tactic solDeriveScoped]
def evalSolDeriveCore : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  unless ← Walk.isCoreGoal g do throwError "sol_derive_scoped: not a scoped goal"
  let rest := (← getUnsolvedGoals).erase g
  Symex.reporting g do
    let (_, leaves) ← Walk.run g
    setGoals (leaves ++ rest)

open Lean Elab Tactic Meta in
/-- `sol_derive?` on a scoped goal: the walk, offered as its script, one
`refine` per rule (today's short walk under the scope, `Walk.surfaceOn`); a leaf closed by `sol_leaf` and the scoped
`sol_close` where it can be (`Walk.closeLeaf`), else left as a goal
(`sorry` in the script). -/
@[tactic Solidity.ProofTree.tacticSol_derive?]
def evalSolDeriveQCore : Tactic := fun stx => withMainContext do
  let g ← getMainGoal
  unless ← Walk.isCoreGoal g do throwUnsupportedSyntax
  let rest := (← getUnsolvedGoals).erase g
  Symex.reporting g do
    let (lines, leaves) ← Walk.run g (close := true) (short := ← Walk.surfaceOn)
    setGoals (leaves ++ rest)
    ProofTree.suggest stx[0] lines

end Solidity
