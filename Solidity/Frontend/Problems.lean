import Solidity.Frontend.Import
import Solidity.Calculus.Problem

/-!
# The obligations of an imported contract

`solc_problems N`, after `solc_import … as N`, defines for each function
`f` that elaborated its obligation as solkey states it,
`N.f.problem : Fml N` (`Problem.fml`, `Calculus/Problem.lean`): the
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

* `#solkey_problem N.f` prints the statement in solkey's problem syntax
  (`Problem.text`), to compare with `--print-problem`.
* `#solkey_scan N` runs `sol_prove`'s walk on every statement with compiled
  code and lists what it leaves, with times: a search, to choose the
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

syntax (name := solcProblems) "solc_problems " ident : command

@[command_elab solcProblems]
def elabSolcProblems : CommandElab := fun stx => do
  let N := stx[1].getId
  let rows ← reportRows N
  let fmlTy := mkApp (mkConst ``Fml) (mkConst N)
  let mut defined : Array Lean.Name := #[]
  for r in rows do
    unless r.status == .elaborated do continue
    let some m := r.tag.modality? | continue
    let some xs := r.params.mapM (fun (x, t) =>
      (paramTy? t).map fun (pn : PrimTy × Nat) => (pn.1, Var.ofName x))
      | logWarning m!"solc_problems: {r.name} has a parameter of no value type, so no \
          statement"
        continue
    let n := N ++ Lean.Name.mkSimple r.name ++ `problem
    -- the constructor's is a deployment's, from the empty storage
    let stmt := if r.name == "constructor" then ``Problem.ctorFml else ``Problem.fml
    let value := mkAppN (mkConst stmt) #[mkConst N, toExpr m, toExpr xs,
      mkConst (N ++ Lean.Name.mkSimple r.name)]
    liftCoreM <| addDecl <| .defnDecl {
      name := n, levelParams := [], type := fmlTy, value, hints := .abbrev, safety := .safe }
    defined := defined.push n
  liftCoreM <| compileDecls defined

syntax (name := solkeyProblem) "#solkey_problem " ident : command

/-- `#solkey_problem N.f`: the statement of `N.f.problem` in solkey's
syntax. -/
@[command_elab solkeyProblem]
def elabSolkeyProblem : CommandElab := fun stx => do
  let f := stx[1].getId
  let N := f.getPrefix
  let e := mkAppN (mkConst ``Problem.text) #[mkConst N, toExpr N.getString!,
    toExpr f.getString!, mkConst (f ++ `problem)]
  let s ← liftTermElabM <| unsafe evalExpr String (mkConst ``String) e
  logInfo s

syntax (name := solkeyScan) "#solkey_scan " ident (&" walk")? : command

/-- `#solkey_scan N`: per statement, the leaves `sol_prove` leaves and the
time; with `walk`, the leaves of the walk before any is closed. -/
@[command_elab solkeyScan]
def elabSolkeyScan : CommandElab := fun stx => do
  let N := stx[1].getId
  let walk := !stx[2].isNone
  let rows ← reportRows N
  let C := mkConst N
  let mut out : Array String := #[]
  for r in rows do
    unless r.status == .elaborated do continue
    let φ := mkConst (N ++ Lean.Name.mkSimple r.name ++ `problem)
    let e := mkAppN (mkConst ``Derive.scanLeaves) #[C, toExpr walk, φ]
    let t0 ← IO.monoMsNow
    let k ← liftTermElabM <| unsafe evalExpr (Option (Nat × Nat)) (mkApp (mkConst ``Option [0])
      (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Nat))) e
    let t1 ← IO.monoMsNow
    let res := match k with
      | none => "budget"
      | some (n, w) => s!"{n} leaves, {w} storage writes"
    out := out.push s!"{r.name} {r.tag.toStr}: {res}, {t1 - t0} ms"
  logInfo ("\n".intercalate out.toList)

syntax (name := solkeyDerive) "#solkey_derive? " ident (&" only " ident)? (&" from " num)?
  (&" count " num)? (&" timed")? (&" pending")? : command

/-- `#solkey_derive? N from i count k`: `sol_prove?`'s search
(`Derive.proveSearch`) on the statements `i … i+k-1` (all of them by
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
      let g ← mkFreshExprSyntheticOpaqueMVar (Derive.provesNil C (mkConst (f ++ `problem)))
      tryCatchRuntimeEx (do
          let out ← IO.mkRef (none : Option Derive.Search)
          let _ ← Tactic.run g.mvarId! do
            out.set (some (← Derive.proveSearch g.mvarId! (stopAtOpen := true)))
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

/-- `#solkey_obligations N`: each function derived, pending, or what the
import made of it, counted; the pending ones named.  Derived means a
theorem `N.f.proved` whose type is `⊢ N.f.problem` as `⊢` writes it
(`Derive.provesNil`), compared as an expression, and whose proof uses no
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
        if t.type.consumeMData == want then matched := matched.push (r.name, f ++ `proved)
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
