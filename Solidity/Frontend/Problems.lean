import Solidity.Frontend.Import
import Solidity.Calculus.Problem
import Solidity.Calculus.Spec
import Solidity.Calculus.ProvesDerive

/-!
# The obligations of an imported contract

`Frontend/Testing.lean` runs these obligations and specifications from Solidity
files through the machine-readable test API.

`solc_scoped_problems N`, after `solc_import … as N`, states for each
function `f` that elaborated its obligation as solkey states it,
`N.f.problem : Fml N []` (`Problem.fml`, `Calculus/Problem.lean`): the
modality is the function's tag, the binders its parameters (`∀`, the first
outermost), the program `N.f`'s, read in their context (`obligation`).  The
constructor's, `N.constructor.problem`, is a deployment's (as
`Problem.ctorFml` computes it): the program `constructor(x̄);` from
solkey's deployment update, with no `wt(storage)` premise.

The statements are one declaration, the list `N.problems`, which the
kernel checks once, each `N.f.problem` a constant naming its entry
(`List.getD`, read back by `Symex.evaluable`; 437 statements: 0.4 s
against 3.4 s as constants of their own), so `sol_prove` names it and the
elaborator never unfolds it.  With `decl` the table is not compiled: the
scoped `sol_prove` reads an obligation by its value.  An info names how
many.

An obligation is proved by a theorem named `N.f.proved : ⊢ N.f.problem`,
the scoped sequent `Proves N .all [] .nil N.f.problem`, in a module of its
own (`Solidity/TestSuite/`); one not yet proved is no theorem at all.
`#solkey_obligations N` reads the environment and reports each function as
derived (its theorem exists, states `⊢ N.f.problem` syntactically, and
uses no axiom but Lean's three, so no `sorry` that a pasted suggestion of
`sol_prove?` would leave), pending (its statement exists, its theorem not
yet), or what the import made of it.  A theorem `N.f.proved` of another
type or with another axiom, or an elaborated function with no statement,
is listed apart, never derived.

A parameter is bound at its type's 256-bit range (`PrimTy`), not at its
width, and the body is elaborated at the width (`paramCtx`).  What the
call's dispatcher checks before the body is a premise (`Problem.callPre`):
a narrow integer or an enum parameter in its range, which solc's ABI
decoder enforces, and `msg.value = 0` where the function is not `payable`
and reads `msg.value`.  Each is stated only where it says something, so an
obligation without them is unchanged.

* `#solkey_problem N.f` prints the statement in solkey's problem syntax
  (`Problem.text`), to compare with `--print-problem`: `N.f.problem`, or the
  statement `solc_scoped_problems` would declare where it has not run.
* `#solkey_scan N` runs `sol_prove`'s walk on every statement with
  compiled code and lists what it leaves, with times: a search, to choose the
  theorems to state.  It is not used in a checked file.  `#solkey_scan N
  walk` lists the leaves without closing them; the closer skips a leaf
  past its bounds (`Seq.leafFitsOn`: the leaf's nodes and its
  reduction's, which grows faster).
* `#solkey_derive? N` searches `⊢ N.f.problem` (`scopedSearch`) and prints
  the theorems that close.
-/

namespace Solidity.Frontend

open Lean Elab Command Meta

/-- The rows of `N.report`. -/
def reportRows (N : Lean.Name) : CommandElabM (List ImportRow) :=
  liftTermElabM <| unsafe evalConst (List ImportRow) (N ++ `report)

/-- **What the call guarantees before the body runs**, as a premise read
at the parameters `Γ`: `msg.value = 0` when `noValue` (a function that is
not `payable` reverts on value in its dispatcher, as the specified
obligation assumes, `Calculus/SurfaceSpec.lean`), and each bounded
parameter in its range (the ABI decoder reverts on a narrow integer or an
enum out of range).  An argument out of range never reaches the body, so
the obligation holds of every call that does.  A premise that does not read
is `true`: the obligation is then stronger, never weaker. -/
def Problem.callPre (C : Contract) (Γ : NCtx) (noValue : Bool)
    (ranges : List (Var × Int × Int)) : Fml C Γ.ctx :=
  let value : List (NRead C) := if noValue then [NRead.eq (.env .msgValue) (.num 0)] else []
  let bounds : List (NRead C) := ranges.map fun (x, lo, hi) =>
    NRead.and (NRead.cmp .le (.num lo) (.pv x)) (NRead.cmp .le (.pv x) (.num hi))
  match NRead.conj (value ++ bounds) Γ with
  | .ok φ => φ
  | .error _ => .tt

/-- The modality of a tag's plain obligation, if solkey states that one. -/
def Tag.modality? : Tag → Option Modality
  | .diamond => some .diamond
  | .box => some .box
  | .skip | .specified | .internal | .malformed => none

/-- **The statement of `N.f`** (the row `r`), written on the program
`N.f : Prog N Γ Γ'` (its type and value read off the environment):
`∀x̄. wt(storage) → [m] N.f`, or a deployment's `∀x̄. {deployUpd} [m] N.f`,
its binders (`Fml.all`, the first parameter outermost), the premise and
the modality as constructors, what `Problem.fml` and `Problem.ctorFml`
compute.  The program is `N.f`'s value, the literal the import declared:
the import does not compile it, and `sol_prove` evaluates the statement
with compiled code (`Symex.evaluable`).  `none`
where solkey states no plain obligation (the tag) or a parameter is of no
value type. -/
def obligation (env : Environment) (N : Lean.Name) (r : ImportRow) :
    Except String (Option Expr) := do
  let some m := r.tag.modality? | return none
  unless r.params.length == r.paramTypes.length do
    throw s!"{r.name}: its parameter types are missing"
  let Γ : NCtx := (r.params.reverse.map fun (x, _) => Var.ofName x).zip r.paramTypes
  let xs := Γ.reverse
  let n := r.declName N
  let some ci := env.find? n | throw s!"{r.name}: no program {n}"
  let ty := ci.type.consumeMData
  let some v := ci.value? | throw s!"{r.name}: {n} is not a scoped program"
  unless ty.isAppOfArity ``Prog 3 do throw s!"{r.name}: {n} is not a scoped program"
  let Γe := ty.appFn!.appArg!
  let Γ'e := ty.appArg!
  unless Γe == ctxE Γ.ctx do
    throw s!"{r.name}: {n} is not read in its parameters' context"
  let c := mkConst N
  let modal := mkAppN (mkConst ``Fml.modal) #[c, Γe, Γ'e, Γ'e, toExpr m, v,
    mkApp2 (mkConst ``Frames.nil) c Γ'e, mkApp2 (mkConst ``Fml.tt) c Γ'e]
  let body := if r.name == "constructor" then
      mkAppN (mkConst ``Fml.upd) #[c, Γe, Γe, toExpr m, mkApp2 (mkConst ``Problem.deployUpd) c Γe, modal]
    else mkAppN (mkConst ``Fml.imp) #[c, Γe, mkApp2 (mkConst ``Fml.wt) c Γe, modal]
  -- the call's premise, only where it says something: a function that is
  -- not `payable` and reads `msg.value`, a parameter the decoder bounds
  let noValue := !r.payable && r.name != "constructor" &&
    (v.find? (·.isConstOf ``EnvKey.msgValue)).isSome
  let ranges : List (Var × Int × Int) := r.paramRanges.map fun (x, b) => (Var.ofName x, b)
  let body := if noValue || !ranges.isEmpty then
      mkAppN (mkConst ``Fml.imp) #[c, Γe,
        mkAppN (mkConst ``Problem.callPre) #[c, toExpr Γ, toExpr noValue, toExpr ranges], body]
    else body
  let body := if r.paramTypes.any (fun t => t matches .alias _ | .mem _) then
      mkAppN (mkConst ``Fml.imp) #[c, Γe, mkApp2 (mkConst ``Fml.refInputs) c Γe, body]
    else body
  -- the binders, the last parameter innermost
  let φ := xs.zipIdx.foldr (init := body) fun ((x, t), i) φ =>
    let ctx := ctxE ((xs.take i).reverse.map (·.2))
    match t with
    | .val p => mkAppN (mkConst ``Fml.all) #[c, ctx, toExpr x, toExpr p, φ]
    | _ => mkAppN (mkConst ``Fml.bind) #[c, ctx, toExpr m, toExpr x, toExpr t, φ]
  return some φ

/-- Declare each obligation of the import `N`, `N.f.problem : Fml N []`
(`obligation`), as the entries of one declaration `N.problems`; compiled
when `compile`.  How many. -/
def declareObligations (N : Lean.Name) (compile : Bool) : CommandElabM Nat := do
  let rows ← reportRows N
  let nilCtx := ctxE []
  let fmlTy := mkApp2 (mkConst ``Fml) (mkConst N) nilCtx
  let env ← getEnv
  let mut errs0 : Array String := #[]
  let mut entries : Array (Lean.Name × Expr) := #[]
  for r in rows do
    unless r.status == .elaborated do continue
    match obligation env N r with
    | .error e => errs0 := errs0.push e
    | .ok none => pure ()
    | .ok (some φ) => entries := entries.push (r.declName N ++ `problem, φ)
  let errs ← liftTermElabM do
    let mut errs := errs0
    let mut defined : Array Lean.Name := #[]
    try
      -- one declaration holds every statement, so the kernel checks the
      -- contract's types and contexts once rather than once an obligation
      -- (437: 0.4 s against 3.4 s); each `N.f.problem` is its entry,
      -- which `Symex.evaluable` reads back
      let tn := N ++ `problems
      let tt := mkApp2 (mkConst ``Fml.tt) (mkConst N) nilCtx
      let value := Lean.ShareCommon.shareCommon (← mkListLit fmlTy (entries.toList.map (·.2)))
      addDecl <| Declaration.defnDecl {
        name := tn, levelParams := [], type := mkApp (mkConst ``List [0]) fmlTy,
        value, hints := .abbrev, safety := .safe }
      defined := defined.push tn
      for (dn, _) in entries, i in [0:entries.size] do
        addDecl <| Declaration.defnDecl {
          name := dn, levelParams := [], type := fmlTy,
          value := mkApp4 (mkConst ``List.getD [0]) fmlTy (mkConst tn) (mkRawNatLit i) tt,
          hints := .abbrev, safety := .safe }
        defined := defined.push dn
      if compile then compileDecls defined
    catch ex => errs := errs.push s!"the kernel rejects them: {← ex.toMessageData.toString}"
    pure errs
  unless errs.isEmpty do
    throwError "solc_scoped_problems: {errs.size} obligations are not stated:\n{"\n".intercalate errs.toList}"
  return entries.size

/-- `solc_scoped_problems N`: each obligation `N.f.problem : Fml N []`
(`obligation`), an entry of one table `N.problems`, compiled, or with
`decl` not compiled (the scoped `sol_prove` reads an obligation by its
value, `Symex.evaluable`); an info names how many. -/
syntax (name := solcScopedProblems) "solc_scoped_problems " ident (&" decl")? : command

@[command_elab solcScopedProblems]
def elabSolcScopedProblems : CommandElab := fun stx => do
  let N ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let k ← declareObligations N stx[2].isNone
  logInfo m!"{k} obligation{if k == 1 then "" else "s"} declared scoped"

/-- `N.f`'s statement, as compiled code evaluates it: `N.f.problem` (its
value, where it has no code: `Symex.evaluable`), else the one
`solc_scoped_problems` would declare (`obligation`). -/
def statement? (N f : Lean.Name) : CommandElabM (Option Expr) := do
  let env ← getEnv
  if env.contains (f ++ `problem) then
    return some (← liftTermElabM <| Symex.evaluable (mkConst (f ++ `problem)))
  let some r := (← reportRows N).find? (fun r => r.declName N == f)
    | return none
  match obligation env N r with
  | .ok φ => return φ
  | .error _ => return none

syntax (name := solkeyProblem) "#solkey_problem " ident : command

/-- `#solkey_problem N.f`: the statement of `N.f` in solkey's syntax. -/
@[command_elab solkeyProblem]
def elabSolkeyProblem : CommandElab := fun stx => do
  let f := stx[1].getId
  let N := f.getPrefix
  let some φ ← statement? N f | throwError "#solkey_problem: {f} has no statement"
  let e := mkAppN (mkConst ``Problem.text) #[mkConst N, toExpr N.getString!,
    toExpr f.getString!, φ]
  let s ← liftTermElabM <| unsafe evalExpr String (mkConst ``String) e
  logInfo s

syntax (name := solkeyScan) "#solkey_scan " ident (&" walk")? : command

/-- `#solkey_scan N`: per statement, the leaves `sol_prove` leaves on it
(`Seq.scanLeaves`) and the time; with `walk`, the leaves of the walk
before any is closed. -/
@[command_elab solkeyScan]
def elabSolkeyScan : CommandElab := fun stx => do
  let N := stx[1].getId
  let walk := !stx[2].isNone
  let rows ← reportRows N
  let C := mkConst N
  let mut out : Array String := #[]
  for r in rows do
    unless r.status == .elaborated do continue
    let f := r.declName N
    let some φ ← statement? N f | continue
    let e := mkAppN (mkConst ``Seq.scanLeaves) #[C, toExpr walk, φ]
    let t0 ← IO.monoMsNow
    let k ← liftTermElabM <| unsafe evalExpr (Option (Nat × Nat)) (mkApp (mkConst ``Option [0])
      (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat))) e
    let t1 ← IO.monoMsNow
    let res := match k with
      | none => "budget"
      | some (n, w) => s!"{n} leaves, {w} storage writes"
    out := out.push s!"{r.name} {r.tag.toStr}: {res}, {t1 - t0} ms"
  logInfo ("\n".intercalate out.toList)

open Tactic in
/-- `Derive.proveSearch` (`stopAtOpen`) on a scoped goal `⊢ N.f.problem`:
`sol_prove` (the scoped walk, `Calculus/ProvesDerive.lean`), then
`Derive.searchLeaf` on each leaf it leaves (`Seq.goalFits`). -/
def scopedSearch (g : MVarId) : TacticM Derive.Search := do
  let_expr Proves C R _ Γ H φ := ← g.getType | throwError "expected a scoped `⊢ φ`"
  Derive.proveSearch g (fun g => Seq.prove g C R Γ H φ) (stopAtOpen := true)
    (fits := Seq.goalFits)

syntax (name := solkeyDerive) "#solkey_derive? " ident (&" only " ident)? (&" from " num)?
  (&" count " num)? (&" timed")? (&" pending")? : command

/-- `#solkey_derive? N from i count k`: `sol_prove?`'s search on the scoped
`⊢ N.f.problem` (`scopedSearch`) for the statements `i … i+k-1` (all of them by
default), or with `only f` on `N.f` alone; each one whose leaves all close,
and whose replay fits one declaration's `maxHeartbeats`
(`Derive.replayFits`), is printed as the theorem to paste, `N.f.proved`
with its replay; the others are named with the leaf that stays open, or
as past `maxHeartbeats`.  With `timed`, each note says how long it took,
and how many heartbeats a replay too long needs; without, the output is
fixed, to pin.  With `pending`, only the statements no `N.f.proved`
derives yet. -/
@[command_elab solkeyDerive]
def elabSolkeyDerive : CommandElab := fun stx => do
  let N := stx[1].getId
  let only? := if stx[2].isNone then none else some stx[2][1].getId
  let start := if stx[3].isNone then 0 else stx[3][1].isNatLit?.getD 0
  let count := if stx[4].isNone then 100000 else stx[4][1].isNatLit?.getD 0
  let timed := !stx[5].isNone
  let pendingOnly := !stx[6].isNone
  let env ← getEnv
  let rows := ((← reportRows N).filter fun r => r.status == .elaborated &&
    only?.all (· == Lean.Name.mkSimple r.name) &&
    (!pendingOnly || !env.contains (r.declName N ++ `proved))).drop start
    |>.take count
  if rows.isEmpty then throwError "#solkey_derive?: no statement of {N} selected"
  let C := mkConst N
  let mut thms : Array String := #[]
  let mut notes : Array String := #[]
  for r in rows do
    let f := r.declName N
    let t0 ← IO.monoMsNow
    -- the tactics' names resolve as in a `Derived` module
    let res : Except String (Array String) ← withScope (fun sc =>
        { sc with openDecls := .simple `Solidity [] :: sc.openDecls }) <| liftTermElabM do
      -- the scoped `⊢ N.f.problem` (`Calculus/Surface.lean`)
      unless env.contains (f ++ `problem) do return .error "no statement"
      let g ← mkFreshExprSyntheticOpaqueMVar (ProofTree.provesE C (mkConst (f ++ `problem)))
      tryCatchRuntimeEx (do
          let out ← IO.mkRef (none : Option Derive.Search)
          let _ ← Tactic.run g.mvarId! do
            out.set (some (← scopedSearch g.mvarId!))
          let some s ← out.get | return .error "the search did not run"
          if let some l := s.open_.head? then return .error s!"{← l.getTag} stays open"
          unless ← Derive.replayFits s.heartbeats do
            let hb := if timed then s!" ({s.heartbeats / 1000} heartbeats)" else ""
            return .error s!"its replay is past maxHeartbeats as one declaration{hb}"
          return .ok (Derive.replayLines s.found s.steps))
        fun e => do return .error (← e.toMessageData.toString)
    let t1 ← IO.monoMsNow
    let ms := if timed then s!", {t1 - t0} ms" else ""
    match res with
    | .ok lines =>
      thms := thms.push (s!"theorem {f}.proved : ⊢ {f}.problem := by\n" ++
        "\n".intercalate (lines.toList.map ("  " ++ ·)))
      notes := notes.push s!"{r.name}: derived{ms}"
    | .error m => notes := notes.push s!"{r.name}: pending, {m}{ms}"
  logInfo ("\n\n".intercalate (thms.toList ++ ["\n".intercalate notes.toList]))

/-- The axioms a derived theorem may use: Lean's three, so no `sorryAx`
and no `Lean.ofReduceBool`. -/
def standardAxioms : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]

syntax (name := solkeyObligations) "#solkey_obligations " ident : command

/-- Whether `ty` is the scoped `⊢ φ`, `Proves C .all [] .nil φ`
(`Calculus/Surface.lean`). -/
def provesScoped (C φ ty : Expr) : Bool :=
  match ty.consumeMData.getAppFnArgs with
  | (`Solidity.Proves, #[C', R, Γ₀, _, H, φ']) =>
    C' == C && R.isConstOf ``RuleSet.all && Γ₀.isAppOfArity ``List.nil 1 &&
      H.isAppOf `Solidity.Hyps.nil && φ' == φ
  | _ => false

/-- `#solkey_obligations N`: each function derived, pending, or what the
import made of it, counted; the pending ones named.  Derived means a
theorem `N.f.proved` whose type is `⊢ N.f.problem`, the scoped
`Proves N .all [] .nil N.f.problem` (`provesScoped`), compared as an
expression, and whose proof uses no axiom but Lean's three (`standardAxioms`): a theorem of another statement,
or of a sequent with hypotheses, is "mismatched"; one that uses `sorry` or
`native_decide` is "unsound".  The axioms are collected once for all the
theorems, and per theorem only when that union is not standard. -/
@[command_elab solkeyObligations]
def elabSolkeyObligations : CommandElab := fun stx => do
  let N := stx[1].getId
  let rows ← reportRows N
  let env ← getEnv
  let C := mkConst N
  let mut matched : Array (String × Lean.Name) := #[]
  let mut pending : Array String := #[]
  let mut other : Array String := #[]
  for r in rows do
    if r.status == .elaborated then
      let f := r.declName N
      if !env.contains (f ++ `problem) then
        let why := if r.tag.modality?.isNone then r.tag.toStr else "unstated"
        other := other.push s!"{why} {r.name}"
        continue
      match env.find? (f ++ `proved) with
      | some (.thmInfo t) =>
        if provesScoped C (mkConst (f ++ `problem)) t.type then matched := matched.push (r.name, f ++ `proved)
        else other := other.push s!"mismatched {r.name}"
      | some _ => other := other.push s!"mismatched {r.name}"
      | none => pending := pending.push r.name
    else other := other.push s!"{r.status.toStr} {r.name}"
  let std (n : Lean.Name) : Bool := standardAxioms.contains n
  let union := (((matched.forM fun (p : String × Lean.Name) => CollectAxioms.collect p.2).run env).run {}).2.axioms
  let mut derived : Array String := #[]
  for (name, t) in matched do
    -- not `union.all std || (← collectAxioms t).all std`: `do` hoists the `←`
    -- out of the `||`, and each theorem's traversal then runs whatever the union
    if union.all std then derived := derived.push name
    else if (← collectAxioms t).all std then derived := derived.push name
    else other := other.push s!"unsound {name}"
  let mut lines : Array String := #[]
  for x in pending, i in [0:pending.size] do
    lines := if i % 6 == 0 then lines.push x else lines.modify (lines.size - 1) (· ++ " " ++ x)
  logInfo m!"{rows.length} functions: {derived.size} derived, {pending.size} pending, \
    {other.size} other\n{"\n".intercalate other.toList}\npending:\n\
    {"\n".intercalate lines.toList}"

end Solidity.Frontend
