import Solidity

/-!
# Axiom audit of every declaration under `Solidity`

CI's audit (`.github/workflows/lean.yml`, step "Audit every declaration's
axioms"): `lake env lean --tstack=131072 scripts/AxiomAudit.lean`, after the
build. It replaces lean-action's `axiom-audit`, which applies one allow list
to every constant, `unsafe` ones included, and so fails on the compiled twins
behind `@[implemented_by]` memo helpers: `unsafeCast` and `unsafeBaseIO` are
defined through `lcProof`, and putting `lcProof` on the global allow list would
let a safe theorem use it.

The audit, over every constant declared in a module `Solidity` or
`Solidity.*` that `import Solidity` reaches (the default library CI builds,
as lean-action's `axiom-audit-root: Solidity` read it; the `SolidityCorpus`
and `SolkeyTestSuite` libraries' `Solidity.Corpus.*`/`Solidity.TestSuite.*`
modules are not imported, so not audited here):

* a **safe** constant (theorem, definition, opaque, inductive, …) may reach
  only the `allowed` axioms, transitively through the kernel terms of its type
  and value (an inductive through its whole mutual block's constructor types,
  a constructor or recursor through its block);
* an **`unsafe`** (or `partial`-safety auxiliary) constant may additionally reach `lcProof` only if it is named
  in `exemptUnsafe`, the compiled implementations listed below; any other
  `unsafe` constant reaching a disallowed axiom fails, and an exemption whose
  constant is gone or no longer reaches `lcProof` fails as stale.

`unsafe` constants are not part of the logic: no safe constant can mention
one (the kernel refuses it), and `@[implemented_by]` is a compiler attribute,
not a kernel edge, so the exemption cannot leak into a theorem.
-/

open Lean

namespace AxiomAudit

/-- The axioms any constant may use: CI's allow list. -/
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The axiom the exempt compiled implementations use (`unsafeCast`,
`unsafeBaseIO`). -/
def unsafeOnly : List Name := [``lcProof]

/-- The `unsafe` implementations behind `@[implemented_by]` that reach
`lcProof`, by (user-facing) name. Each is a compiled memo/cache twin whose
logical declaration is a pure `pure none` / `pure ()` / thunk-returning
definition (see each one's docstring); they exist for elaboration speed. -/
def exemptUnsafe : List Name := [
  -- `Calculus/MemoryLoopReplay.lean`: the replay's proposal pass.
  `Solidity.Seq.MemoryReplay.gather,
  `Solidity.Seq.MemoryReplay.propose,
  -- `Syntax/Elab/Values.lean`: a shared callee's body, read back.
  `Solidity.CallMemo.bodyImpl?,
  `Solidity.CallMemo.setBodyImpl,
  -- `Syntax/Quote.lean`: a body's `Expr`, recorded.
  `Solidity.QMemo.addImpl,
  -- `Syntax/Elab/Context.lean` (private): a recursive frame's thunk.
  `Solidity.RecThunk.getImpl ]

/-- The name a declaration is listed under: private names by their user name. -/
def userName (n : Name) : Name := (privateToUserName? n).getD n

/-- Whether module `m` is `Solidity` or below it. -/
def inScope (m : Name) : Bool := (`Solidity).isPrefixOf m

structure State where
  /-- The disallowed axioms each finished safe constant reaches. -/
  done : Std.HashMap Name (Array Name) := {}
  /-- Constants on the current path (a cycle among safe constants is an error). -/
  active : NameSet := {}
  /-- Safe constants met on a cycle. -/
  cycles : Array Name := #[]

abbrev M := ReaderT Environment (StateM State)

def union (xs ys : Array Name) : Array Name :=
  ys.foldl (fun acc y => if acc.contains y then acc else acc.push y) xs

/-- An `unsafe` or `partial` definition (or opaque): one whose value may
mention itself, directly or not. -/
def loose (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ | .opaqueInfo _ | .thmInfo _ => ci.isUnsafe || ci.isPartial
  | _ => false

/-- The marker a constant missing from the environment is reported as (the
audit fails closed: it never passes a constant it cannot read). -/
def missing (c : Name) : Name := .str c "<missing from the environment>"

/-- The constants an expression mentions. -/
def refs (e : Expr) : Array Name := e.getUsedConstants

mutual
/-- The disallowed axioms a safe constant reaches, memoised. -/
partial def reach (c : Name) : M (Array Name) := do
  if let some r := (← get).done[c]? then return r
  if (← get).active.contains c then
    modify fun s => { s with cycles := s.cycles.push c }
    return #[]
  modify fun s => { s with active := s.active.insert c }
  let env ← read
  let r ← match env.find? c with
    -- a constant missing from the environment cannot be audited: a finding
    | none => pure #[missing c]
    | some ci@(.defnInfo _) | some ci@(.opaqueInfo _) | some ci@(.thmInfo _) =>
      if loose ci then outside c else do
        let mut acc ← reachAll (refs ci.type) []
        if let some v := ci.value? (allowOpaque := true) then acc := union acc (← reachAll (refs v) [])
        pure acc
    | some (.axiomInfo _) => pure (if allowed.contains c then #[] else #[c])
    | some (.inductInfo v) => block v.all
    | some (.ctorInfo v) => do pure (union (← reachAll (refs v.type) [v.induct]) (← reach v.induct))
    | some (.recInfo v) => do
      -- Its rules are built from the block's constructors and recursors.
      let mut acc ← reachAll (refs v.type) v.all
      for i in v.all do acc := union acc (← reach i)
      pure acc
    | some ci => reachAll (refs ci.type) []
  modify fun s => { s with done := s.done.insert c r, active := s.active.erase c }
  return r

/-- The disallowed axioms of the constants `cs`, skipping those in `skip`. -/
partial def reachAll (cs : Array Name) (skip : List Name) : M (Array Name) := do
  let mut acc := #[]
  for d in cs do
    unless skip.contains d do acc := union acc (← reach d)
  return acc

/-- The disallowed axioms an `unsafe` or `partial` constant reaches. Such
constants may be (mutually) recursive, so their own part of the graph is walked
with a visited set, and every safe constant met is `reach`ed (memoised). -/
partial def outside (c : Name) : M (Array Name) := do
  let env ← read
  let mut seen : NameSet := {}
  let mut todo := #[c]
  let mut acc := #[]
  while h : todo.size > 0 do
    let d := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains d then continue
    seen := seen.insert d
    match env.find? d with
    | some ci =>
      if loose ci then
        todo := todo ++ refs ci.type
        if let some v := ci.value? (allowOpaque := true) then todo := todo ++ refs v
      else acc := union acc (← reach d)
    | none => acc := union acc #[missing d]
  return acc

/-- A mutual inductive block: every type's type and constructors' types,
references into the block itself skipped (the block is one declaration). -/
partial def block (all : List Name) : M (Array Name) := do
  let env ← read
  let mut acc := #[]
  for i in all do
    let some (.inductInfo v) := env.find? i | continue
    acc := union acc (← reachAll (refs v.type) all)
    for k in v.ctors do
      let some ci := env.find? k | continue
      acc := union acc (← reachAll (refs ci.type) all)
  return acc
end

/-- The audit's findings, and how many constants it read. -/
def run (env : Environment) : Array String × Nat × Nat := Id.run do
  let modules := env.header.moduleNames
  let roots := env.constants.fold (init := #[]) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some i => if inScope (modules[i.toNat]!) then acc.push (n, ci) else acc
    | none => acc
  let mut st : State := {}
  let mut errors := #[]
  let mut unsafeSeen : List Name := []
  for (n, ci) in roots do
    if loose ci || ci.isUnsafe then
      let (bad, st') := (outside n |>.run env).run st
      st := st'
      if bad.isEmpty then continue
      if exemptUnsafe.contains (userName n) && bad.all unsafeOnly.contains then
        unsafeSeen := userName n :: unsafeSeen
      else
        errors := errors.push s!"unsafe {n} uses {bad.toList}{if exemptUnsafe.contains (userName n) then "" else " (not in exemptUnsafe)"}"
    else
      let (bad, st') := (reach n |>.run env).run st
      st := st'
      unless bad.isEmpty do errors := errors.push s!"{n} uses {bad.toList}"
  for c in st.cycles do errors := errors.push s!"cycle through safe constant {c}"
  for e in exemptUnsafe do
    unless unsafeSeen.contains e do
      errors := errors.push s!"stale exemption {e}: no unsafe constant of that name reaches {unsafeOnly}"
  return (errors, roots.size, unsafeSeen.length)

end AxiomAudit

open Lean Elab Command in
run_cmd do
  let (errors, n, exempt) := AxiomAudit.run (← getEnv)
  for e in errors do logError e
  logInfo m!"axiom audit: {n} declarations under Solidity, {exempt} exempt unsafe implementations, {errors.size} findings"
