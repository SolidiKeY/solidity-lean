import Lean

/-!
Registers the `rule_simp_set` simp attribute used by the step-case navigation
tactics in `Examples/Common.lean`. Lives in its own module because a simp
attribute must be initialized in a module imported by its users.

(4.24 note: the former `rule_simp` macro passed ~100 lemmas literally to
`simp only`, and each invocation re-elaborated the whole set — ~3s per call on
Lean 4.24, × ~190 skip proofs per `single_step`. A registered set is built
once per module instead.)
-/

register_simp_attr rule_simp_set

/-- Trace the rules `steps!` picks, one line per step plus a pasteable
`steps [...]` summary:

```
set_option trace.solidity.steps true in
sol_runs deepFieldWrite { alice.account.balance = amount }
```

Registered here for the same reason the simp set is: a trace class must be
initialized in a module imported by its users. -/
initialize Lean.registerTraceClass `solidity.steps

open Lean Elab Command Meta in
/-- Put a *name-keyed table* -- `rootExpr`, `fieldForName`, `funDef`: a
`match` on a `String` with a `_` default -- into `rule_simp_set` one arm at a
time, tagging the unconditional equations and leaving the default one out.

The def itself must not be in the set.  Unfolding it makes `simp` reduce the
match, and reducing a match on a string literal means deciding `String.decEq`
against every earlier pattern: the kernel expands both literals to their
character lists, so one `rule_simp` over one small statement spent ~2s and
unfolded `String.decEq` a thousand times.  The arm equations say the same
thing with the literal in the head, so `simp` finds them by one
discrimination-tree hit and never reduces the match at all -- the string work
is done once, by the kernel, when the equation is generated.  Measured on the
shortest worked derivation (`Paper/Storage.lean`'s `fieldWriteSimple`): 23.4s
to 1.25s.

A name the table has no arm for still reaches its default through
`rule_simp_tables`, the slow alternative `rule_cond` falls back to. -/
elab "name_table_simp " fns:ident,+ : command => do
  for fn in fns.getElems do
    let n ← liftCoreM <| realizeGlobalConstNoOverload fn
    let some eqs ← liftTermElabM (getEqnsFor? n)
      | throwErrorAt fn "name_table_simp: `{n}` has no equation lemmas"
    let mut arms : Array Ident := #[]
    for eq in eqs do
      -- The default arm is the conditional one: `∀ name, (name = "…" → False)
      -- → … → f name = …`.  Every other equation has the literal in its head.
      unless (← liftTermElabM do inferType (← mkConstWithLevelParams eq)).isForall do
        arms := arms.push (mkIdent eq)
    if arms.isEmpty then
      throwErrorAt fn "name_table_simp: `{n}` has no unconditional arm"
    elabCommand (← `(command| attribute [rule_simp_set] $arms:ident*))

open Lean Elab Command Meta in
/-- Give a name-keyed table an arm equation for a name it reaches through its
`_` default, and put that in `rule_simp_set` too.

`name_table_simp` covers the names a table lists.  An identifier a worked
example introduces — `ageVal`, `newBal`, `mv2` — is not one of them, and the
default arm is the *worst* case to reduce: its equation is conditional on the
name differing from every listed one, so `simp` decides forty string
disequalities to use it, every time.  This states the instance the example
needs and proves it by `rfl`, which pays that once.

Adding the name to the table in `AST.lean` instead is the other way, and is
the wrong way for these: the explicit-arms list there is for scratch names
that appear in *residuals*, and giving the worked-example identifiers arms
overflowed Lean's stack (`.claude/rules/derivations.md`). A lemma here does
not grow the match at all. -/
elab "name_table_arms " fns:ident,+ " for " names:str,+ : command => do
  for fn in fns.getElems do
    let tbl ← liftCoreM <| realizeGlobalConstNoOverload fn
    let some eqs ← liftTermElabM (getEqnsFor? tbl)
      | throwErrorAt fn "name_table_arms: `{tbl}` has no equation lemmas"
    let mut listed : Array String := #[]
    let mut dflt? : Option Name := none
    for eq in eqs do
      let ty ← liftTermElabM do inferType (← mkConstWithLevelParams eq)
      if ty.isForall then dflt? := some eq
      else if let some (_, lhs, _) := ty.eq? then
        if let .lit (.strVal s) := lhs.appArg! then listed := listed.push s
    let some dflt := dflt?
      | throwErrorAt fn "name_table_arms: `{tbl}` has no default arm"
    for nameStx in names.getElems do
      let s := nameStx.getString
      if listed.contains s then continue
      let declName := tbl ++ `arm ++ Name.mkSimple s
      if (← getEnv).contains declName then continue
      liftTermElabM do
        let dty ← inferType (← mkConstWithLevelParams dflt)
        let (type, value) ← forallTelescope dty fun xs body => do
          let some (_, lhs, rhs) := body.eq?
            | throwErrorAt fn "name_table_arms: `{dflt}` is not an equation"
          let lit := mkStrLit s
          let lhs := lhs.replaceFVar xs[0]! lit
          let rhs := rhs.replaceFVar xs[0]! lit
          pure (← mkEq lhs rhs, ← mkEqRefl lhs)
        addDecl (.thmDecl { name := declName, levelParams := [], type, value })
      elabCommand (← `(command| attribute [rule_simp_set] $(mkIdent declName)))
