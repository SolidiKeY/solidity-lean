import Solidity.Frontend.Import
import Solidity.Calculus.Problem
import Solidity.Calculus.Core.Spec
import Solidity.Calculus.Core.ProvesDerive

/-!
# The obligations of an imported contract

`solc_problems N`, after `solc_import … as N`, defines for each function
`f` that elaborated its obligation as solkey states it,
`N.f.problem : Surface.Fml N` (`Problem.fml`, `Calculus/Problem.lean`): the
modality is the function's tag, the binders its parameters, the program
`N.f`.  The constructor's, `N.constructor.problem`, is a deployment's
(`Problem.ctorFml`): the program `constructor(x̄);` from solkey's
deployment update, with no `wt(storage)` premise.  A statement is a constant, so `sol_prove` names it and the
elaborator never unfolds it; it is compiled, since `sol_prove` evaluates
its sequent with compiled code.

An obligation is proved by a theorem named `N.f.proved : ⊢ N.f.problem`,
in a module of its own (`Solidity/TestSuite/`); one not yet proved is no
theorem at all.  `#solkey_obligations N` reads the environment and reports
each function as derived (its theorem exists, states `⊢ N.f.problem`
syntactically, and uses no axiom but Lean's three, so no `sorry` that a
pasted suggestion of `sol_prove?` would leave), pending (its statement
exists, its theorem not yet), or what the import made of it.  A theorem
`N.f.proved` of another type or with another axiom, or an elaborated
function with no statement, is listed apart, never derived.

A parameter is bound at its type's 256-bit range (`PrimTy`), not at its
width: an `int8` binder admits values solc's ABI decoder rejects.  The
obligation is then stronger than Solidity's, never weaker, since the body
is elaborated at the width (`paramCtx`).

`solc_scoped_problems N` (`docs/intrinsic.md`, M6b) states each of them
scoped, `N.f.problem.core : Core.Fml N []` (`Core.Problem.fml`,
`Core.Problem.ctorFml`, `Calculus/Core/Spec.lean`): the program resolved in
the context of its parameters, which `∀` binds.  They are one declaration,
the list `N.problems.core`, which the kernel checks once, and each
`N.f.problem.core` is its entry (`List.getD`, read back by
`Core.Symex.evaluable`); each is checked to erase to its legacy statement
(`Fml.eraseS`, compared as quoted expressions).  The flip
(`docs/intrinsic.md`, W3) is `solc_problems N legacy`
(`N.f.problem.legacy`, not compiled) then `solc_scoped_problems N main`
(`N.f.problem`, the table `N.problems`); `#solkey_problem` reads the
legacy statement wherever it is (`legacyStatement`), `#solkey_scan` the
scoped one (`scopedStatement?`; today's walk on the legacy statement went
with today's rule table), `#solkey_derive?` searches the scoped `⊢` once
there is one, and `#solkey_obligations` counts a theorem of either `⊢`.

* `#solkey_problem N.f` prints the statement in solkey's problem syntax
  (`Problem.text`), to compare with `--print-problem`.
* `#solkey_scan N` runs `sol_prove`'s walk on every scoped statement with
  compiled code and lists what it leaves, with times: a search, to choose the
  theorems to state.  It is not used in a checked file.  `#solkey_scan N
  walk` lists the leaves without closing them; the closer skips a leaf
  past its bounds (`Derive.fitsClose`: the leaf's nodes and its
  reduction's, which grows faster).
-/

namespace Solidity.Frontend

open Lean Elab Command Meta

/-- The rows of `N.report`. -/
def reportRows (N : Lean.Name) : CommandElabM (List ImportRow) :=
  liftTermElabM <| unsafe evalConst (List ImportRow) (N ++ `report)

/-- The modality of a tag's plain obligation, if solkey states that one. -/
def Tag.modality? : Tag → Option Modality
  | .diamond => some .diamond
  | .box => some .box
  | .skip | .specified | .internal | .malformed => none

/-- The name of `N.f`'s statement in `Update.lean`'s formulas: `N.f.problem.legacy`
once the scoped one is `N.f.problem` (`solc_scoped_problems N main`),
`N.f.problem` before. -/
def legacyProblem (env : Environment) (f : Lean.Name) : Lean.Name :=
  if env.contains (f ++ `problem ++ `legacy) then f ++ `problem ++ `legacy else f ++ `problem

/-- `N.f`'s statement in `Update.lean`'s formulas, as compiled code
evaluates it: `N.f.problem`, or the value of `N.f.problem.legacy`, which is
not compiled (`Problem.fml N m xs N.f`, every part of it compiled). -/
def legacyStatement (env : Environment) (f : Lean.Name) : Expr :=
  let n := legacyProblem env f
  match env.find? n, IR.findEnvDecl env n with
  | some (.defnInfo d), none => d.value
  | _, _ => mkConst n

/-- `solc_problems N`, or `solc_problems N legacy` to declare each as
`N.f.problem.legacy`, beside a scoped `N.f.problem`, and not compiled: no
tactic proves a legacy statement, and the commands below read its value
(`legacyStatement`). -/
syntax (name := solcProblems) "solc_problems " ident (&" legacy")? : command

@[command_elab solcProblems]
def elabSolcProblems : CommandElab := fun stx => do
  let N := stx[1].getId
  let suffix := if stx[2].isNone then `problem else `problem ++ `legacy
  let rows ← reportRows N
  let fmlTy := mkApp (mkConst ``Surface.Fml) (mkConst N)
  let mut defined : Array Lean.Name := #[]
  for r in rows do
    unless r.status == .elaborated do continue
    let some m := r.tag.modality? | continue
    let some xs := r.params.mapM (fun (x, t) =>
      (paramTy? t).map fun (pn : PrimTy × Nat) => (pn.1, Var.ofName x))
      | logWarning m!"solc_problems: {r.name} has a parameter of no value type, so no \
          statement"
        continue
    let n := N ++ Lean.Name.mkSimple r.name ++ suffix
    -- the constructor's is a deployment's, from the empty storage
    let stmt := if r.name == "constructor" then ``Problem.ctorFml else ``Problem.fml
    let value := mkAppN (mkConst stmt) #[mkConst N, toExpr m, toExpr xs,
      mkConst (N ++ Lean.Name.mkSimple r.name)]
    liftCoreM <| addDecl <| .defnDecl {
      name := n, levelParams := [], type := fmlTy, value, hints := .abbrev, safety := .safe }
    defined := defined.push n
  if stx[2].isNone then liftCoreM <| compileDecls defined

/-- `solc_scoped_problems N`: each obligation `solc_problems` states,
scoped, `N.f.problem.core`, an entry of the table `N.problems.core`,
compiled; with `main`, `N.f.problem` and `N.problems` (the flip:
`solc_problems N legacy` first); with `decl`, not compiled (the scoped
`sol_prove` reads an obligation by its value, `Core.Symex.evaluable`).
Each is checked to erase to its legacy statement (`legacyProblem`;
`N.f.problem.legacy` with `main`), as expressions; a missing legacy
statement or a mismatch is an error. -/
syntax (name := solcScopedProblems) "solc_scoped_problems " ident (&" main")? (&" decl")? :
  command

@[command_elab solcScopedProblems]
def elabSolcScopedProblems : CommandElab := fun stx => do
  let N ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let suffix := if stx[2].isNone then `problem ++ `core else `problem
  let compile := stx[3].isNone
  let rows ← reportRows N
  let nilCtx := mkApp (mkConst ``List.nil [0]) (mkConst ``Core.LTy)
  let fmlTy := mkApp2 (mkConst ``Core.Fml) (mkConst N) nilCtx
  let errs ← liftTermElabM do
    let C ← unsafe evalConst Contract N
    let mut errs : Array String := #[]
    let mut entries : Array (Lean.Name × Expr) := #[]
    let mut defined : Array Lean.Name := #[]
    for r in rows do
      unless r.status == .elaborated do continue
      let some m := r.tag.modality? | continue
      let some xs := r.params.mapM (fun (x, t) =>
        (paramTy? t).map fun (pn : PrimTy × Nat) => (pn.1, Var.ofName x)) | continue
      let n := N ++ Lean.Name.mkSimple r.name
      let P ← unsafe evalConst (Surface.Prog C) n
      match Core.Problem.resolve (r.name == "constructor") m xs P with
      | .error e => errs := errs.push s!"{r.name}: {e}"
      | .ok φ =>
        -- the guard: the scoped statement erases to the legacy one
        let env ← getEnv
        let ln := if stx[2].isNone then legacyProblem env n else n ++ `problem ++ `legacy
        match env.find? ln with
        | some (.defnInfo d) =>
          -- the legacy statement is `solc_problems`' application to `N.f`, and that
          -- is computed here from `P`: an `evalConst` of it would run the
          -- interpreter on the contract again, 9 ms an obligation
          let ctor := r.name == "constructor"
          let want := mkAppN (mkConst (if ctor then ``Problem.ctorFml else ``Problem.fml))
            #[mkConst N, toExpr m, toExpr xs, mkConst n]
          let legacy := if ctor then Problem.ctorFml m xs P else Problem.fml m xs P
          unless d.value == want &&
              Solidity.Surface.Fml.quote (mkConst N) (φ.eraseS []) ==
                Solidity.Surface.Fml.quote (mkConst N) legacy do
            errs := errs.push s!"{r.name}: it does not erase to {ln}"
        | _ => errs := errs.push s!"{r.name}: no legacy statement {ln}"
        -- written out here and shared once, across the statements, below
        entries := entries.push (n ++ suffix, (Core.Quote.qFml [] φ).run (mkConst N))
    -- one declaration holds every statement, so the kernel checks the
    -- contract's types, contexts and side conditions once rather than once
    -- an obligation (437: 0.4 s against 3.4 s); each `N.f.problem` is its
    -- entry, which `Core.Symex.evaluable` reads back
    let table := N ++ (if stx[2].isNone then `problems ++ `core else `problems)
    let tt := mkApp2 (mkConst ``Core.Fml.tt) (mkConst N) nilCtx
    let value := Lean.ShareCommon.shareCommon (← mkListLit fmlTy (entries.toList.map (·.2)))
    try
      addDecl <| Declaration.defnDecl {
        name := table, levelParams := [], type := mkApp (mkConst ``List [0]) fmlTy,
        value, hints := .abbrev, safety := .safe }
      for (dn, _) in entries, i in [0:entries.size] do
        addDecl <| Declaration.defnDecl {
          name := dn, levelParams := [], type := fmlTy,
          value := mkApp4 (mkConst ``List.getD [0]) fmlTy (mkConst table) (mkRawNatLit i) tt,
          hints := .abbrev, safety := .safe }
        defined := defined.push dn
    catch ex => errs := errs.push s!"the kernel rejects them: {← ex.toMessageData.toString}"
    -- compiled, as `N.f.problem` is, for compiled consumers
    if compile then compileDecls (#[table] ++ defined)
    if errs.isEmpty then
      let k := defined.size
      logInfo m!"{k} obligation{if k == 1 then "" else "s"} declared scoped"
    pure errs
  unless errs.isEmpty do
    throwError "solc_scoped_problems: {errs.size} obligations are not scoped:\n{"\n".intercalate errs.toList}"

syntax (name := solkeyProblem) "#solkey_problem " ident : command

/-- `#solkey_problem N.f`: the statement of `N.f.problem` in solkey's
syntax. -/
@[command_elab solkeyProblem]
def elabSolkeyProblem : CommandElab := fun stx => do
  let f := stx[1].getId
  let N := f.getPrefix
  let e := mkAppN (mkConst ``Problem.text) #[mkConst N, toExpr N.getString!,
    toExpr f.getString!, legacyStatement (← getEnv) f]
  let s ← liftTermElabM <| unsafe evalExpr String (mkConst ``String) e
  logInfo s

/-- `N.f`'s scoped statement, if there is one: `N.f.problem.core`, or
`N.f.problem` once it is the scoped one (`solc_scoped_problems N main`,
beside `N.f.problem.legacy`). -/
def scopedStatement? (env : Environment) (f : Lean.Name) : Option Expr :=
  if env.contains (f ++ `problem ++ `core) then some (mkConst (f ++ `problem ++ `core))
  else if env.contains (f ++ `problem ++ `legacy) then some (mkConst (f ++ `problem))
  else none

syntax (name := solkeyScan) "#solkey_scan " ident (&" walk")? : command

/-- `#solkey_scan N`: per statement, the leaves `sol_prove` leaves on its
scoped statement (`Core.Seq.scanLeaves`) and the time; with `walk`, the
leaves of the walk before any is closed. -/
@[command_elab solkeyScan]
def elabSolkeyScan : CommandElab := fun stx => do
  let N := stx[1].getId
  let walk := !stx[2].isNone
  let rows ← reportRows N
  let C := mkConst N
  let mut out : Array String := #[]
  for r in rows do
    unless r.status == .elaborated do continue
    let f := N ++ Lean.Name.mkSimple r.name
    let env ← getEnv
    let some φ := scopedStatement? env f
      | throwError "#solkey_scan: {f} has no scoped statement (`solc_scoped_problems {N}`)"
    let e := mkAppN (mkConst ``Core.Seq.scanLeaves) #[C, toExpr walk, φ]
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
`sol_prove` (the scoped walk, `Calculus/Core/ProvesDerive.lean`), then
`Derive.searchLeaf` on each leaf of today's calculus it leaves. -/
def scopedSearch (g : MVarId) : TacticM Derive.Search := do
  let_expr Core.Proves C R _ Γ H φ := ← g.getType | throwError "expected a scoped `⊢ φ`"
  Derive.proveSearch g (stopAtOpen := true) (prove := fun g => Core.Seq.prove g C R Γ H φ)

syntax (name := solkeyDerive) "#solkey_derive? " ident (&" only " ident)? (&" from " num)?
  (&" count " num)? (&" timed")? (&" pending")? : command

/-- `#solkey_derive? N from i count k`: `sol_prove?`'s search
(`Derive.proveSearch`, or `scopedSearch` once `N.f.problem` is scoped) on the statements `i … i+k-1` (all of them by
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
    (!pendingOnly || !env.contains (N ++ Lean.Name.mkSimple r.name ++ `proved))).drop start
    |>.take count
  if rows.isEmpty then throwError "#solkey_derive?: no statement of {N} selected"
  let C := mkConst N
  let mut thms : Array String := #[]
  let mut notes : Array String := #[]
  for r in rows do
    let f := N ++ Lean.Name.mkSimple r.name
    let t0 ← IO.monoMsNow
    -- the tactics' names (`Proves.close_dropWt`) resolve as in a `Derived` module
    let res : Except String (Array String) ← withScope (fun sc =>
        { sc with openDecls := .simple `Solidity [] :: sc.openDecls }) <| liftTermElabM do
      -- once `N.f.problem` is scoped, its `⊢` (`Calculus/Core/Surface.lean`)
      let isScoped := env.contains (f ++ `problem ++ `legacy)
      let nilCtx := mkApp (mkConst ``List.nil [0]) (mkConst ``Core.LTy)
      let ty := if isScoped then
          mkAppN (mkConst ``Core.Proves) #[C, mkConst ``RuleSet.all, nilCtx, nilCtx,
            mkApp2 (mkConst ``Core.Hyps.nil) C nilCtx, mkConst (f ++ `problem)]
        else Derive.provesNil C (legacyStatement env f)
      let g ← mkFreshExprSyntheticOpaqueMVar ty
      tryCatchRuntimeEx (do
          let out ← IO.mkRef (none : Option Derive.Search)
          let _ ← Tactic.run g.mvarId! do
            out.set (some (← if isScoped then scopedSearch g.mvarId!
              else Derive.proveSearch g.mvarId! (stopAtOpen := true)))
          let some s ← out.get | return .error "the search did not run"
          if let some l := s.open_.head? then return .error s!"{← l.getTag} stays open"
          unless ← Derive.replayFits s.heartbeats do
            let hb := if timed then s!" ({s.heartbeats / 1000} heartbeats)" else ""
            return .error s!"its replay is past maxHeartbeats as one declaration{hb}"
          return .ok (Derive.replayLines s.found))
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

/-- Whether `ty` is the scoped `⊢ φ`, `Core.Proves C .all [] .nil φ`
(`Calculus/Core/Surface.lean`). -/
def provesScoped (C φ ty : Expr) : Bool :=
  match ty.consumeMData.getAppFnArgs with
  | (`Solidity.Core.Proves, #[C', R, Γ₀, _, H, φ']) =>
    C' == C && R.isConstOf ``RuleSet.all && Γ₀.isAppOfArity ``List.nil 1 &&
      H.isAppOf `Solidity.Core.Hyps.nil && φ' == φ
  | _ => false

/-- `#solkey_obligations N`: each function derived, pending, or what the
import made of it, counted; the pending ones named.  Derived means a
theorem `N.f.proved` whose type is `⊢ N.f.problem` as `⊢` writes it
(`Derive.provesNil`, or the scoped `Core.Proves N .all [] .nil N.f.problem`
once `N.f.problem` is scoped: `provesScoped`), compared as an expression, and
whose proof uses no
axiom but Lean's three (`standardAxioms`): a theorem of another statement,
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
      let f := N ++ Lean.Name.mkSimple r.name
      if !env.contains (f ++ `problem) then
        let why := if r.tag.modality?.isNone then r.tag.toStr else "unstated"
        other := other.push s!"{why} {r.name}"
        continue
      let want := Derive.provesNil C (mkConst (f ++ `problem))
      match env.find? (f ++ `proved) with
      | some (.thmInfo t) =>
        if t.type.consumeMData == want || provesScoped C (mkConst (f ++ `problem)) t.type then matched := matched.push (r.name, f ++ `proved)
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
