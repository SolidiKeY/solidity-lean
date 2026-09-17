import Solidity.Semantics

/-!
# The interpreter-evaluation battery

`sol_eval_battery` and `sol_exec_eval`, the two tactics that normalize a
concrete interpreter term. They depend on nothing but the interpreter:
`Semantics`, the `SoliditySyntax` smart constructors, and the type-level
helpers those compute with — no wp layer, no rule table.

Both take an optional `location`, so the *same* list serves the goal
(`sol_eval_battery`) and the hypotheses (`sol_eval_battery at *`). A
hypothesis can carry a stalled `evalValue`, and reducing it there is the
difference between `omega` seeing an arithmetic fact and seeing an opaque
`match`; writing the list twice to get that would be the obvious way and
the wrong one.

Their only reader is now `Wp/Verifier.lean`, which reaches them through
the wp algebra. The separate module survives because the dependency is
genuinely one-directional, not because a second client needs it.
-/

namespace Solidity

/-! ## The evaluation battery

`sol_exec_eval` and `sol_wp_post` both normalize interpreter terms and
need *the same* definitions unfolded: the interpreter, the state algebra,
the `SoliditySyntax` smart constructors the `sol!` macro expands into,
and the type-level helpers those constructors compute with. The list
lives in one tactic so it stays in one place — a missing entry is a quiet
failure, not a loud one: `sol_exec_eval`'s `rfl` cannot assign the
verdict metavariable, so `sol_wp_step`'s `rw` fails, `repeat` gives up,
and `sol_wp` leaves an unsolved goal that reads like a calculus gap.

(It is a `simp` *call*, not a registered simp set: an attribute adds only
a definition's equation lemmas, which is weaker than what `simp [f]` does
for the plain non-matching definitions here, and memory reads stop
reducing.) -/

syntax "sol_eval_battery" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| sol_eval_battery $[$loc]?) =>
  `(tactic|
    simp [Semantics.execStmt, Semantics.execAssign, Semantics.execBlock,
          Semantics.evalValue, Semantics.evalInt, Semantics.writeValue,
          Semantics.resolveLoc, Semantics.resolveS, Semantics.resolveMBase,
          Semantics.readM,
          -- Single-resolution l-values and the assignment RHS readers.
          Semantics.readLoc, Semantics.writeLoc, Semantics.execAssignNested,
          Semantics.rhsToSVal, Semantics.rhsToMVal,
          -- Checked arithmetic (solc ≥ 0.8) and the solc mapping-copy
          -- rejection.
          Semantics.checkArith, Semantics.uintBound, Semantics.intBound,
          Semantics.tyHasMapping, Semantics.fieldsHaveMapping,
          Semantics.State.getEnv, Semantics.State.setEnv,
          Semantics.State.getObj, Semantics.State.setObj,
          Semantics.State.alloc, Semantics.State.getNet,
          Semantics.State.setNet, Semantics.State.findStorage,
          Semantics.State.saveStorage, Semantics.State.exampleStore,
          Semantics.State.testSuiteStore,
          Semantics.State.solcExpressionsStore,
          Semantics.State.solcStructsStore, Semantics.State.solcArraysStore,
          Semantics.State.solcMemoryStore, Semantics.State.solcMappingsStore,
          Semantics.State.solcControlFlowStore,
          Semantics.lookupBy, Semantics.setBy,
          Semantics.SVal.find, Semantics.SVal.save,
          Semantics.SVal.asValue, Semantics.SVal.defaultOf,
          -- `defaultOf` recurses into struct members through this `where`
          -- helper, which simp does not reach via `defaultOf` alone; every
          -- `delete` on a struct stalls without it.
          Semantics.SVal.defaultOf.defaultOfFields,
          Semantics.MVal.asValue,
          Semantics.Value.asInt, Semantics.Value.asBool,
          Semantics.Value.toSVal, Semantics.Value.toMVal,
          Semantics.applyBinOp, Semantics.applyUnOp,
          Semantics.defaultForTy, Semantics.defaultForFields,
          Semantics.defaultForRef, Semantics.structDef,
          Semantics.copyStToM, Semantics.copyStFields,
          Semantics.copyStElems, Semantics.copyMem,
          Semantics.copyMToSt, Semantics.copyMFields,
          Semantics.copyMElems, Semantics.allocDefault,
          bind, Except.bind, pure, Except.pure,
          SoliditySyntax.intLitExpr, SoliditySyntax.varExpr,
          SoliditySyntax.varPlace, SoliditySyntax.rootExpr,
          SoliditySyntax.rootPlace, SoliditySyntax.fieldExpr,
          SoliditySyntax.fieldPlace, SoliditySyntax.indexExpr,
          SoliditySyntax.indexPlace, SoliditySyntax.fieldFor,
          SoliditySyntax.fieldForName, SoliditySyntax.fieldTy,
          SoliditySyntax.originFor, SoliditySyntax.storageOriginFor,
          SoliditySyntax.globalExpr, SoliditySyntax.globalPlace,
          SoliditySyntax.aliasExpr, SoliditySyntax.aliasPlace,
          SoliditySyntax.aliasKind,
          SoliditySyntax.localStorageTyFor,
          SoliditySyntax.aliasExpr, SoliditySyntax.aliasPlace,
          SoliditySyntax.aliasKind, SoliditySyntax.declTy,
          SoliditySyntax.typedVarTy, SoliditySyntax.typedKind,
          SoliditySyntax.binopExpr, SoliditySyntax.unopExpr,
          SoliditySyntax.incDecExpr, SoliditySyntax.andExpr,
          -- The `sol!` macro expands `c ? t : e` and `a.push()` through
          -- these; without them a ternary or a push receiver is opaque to
          -- the interpreter-evaluation simp set and `sol_wp` stalls on the
          -- first such statement.
          SoliditySyntax.ternaryExpr,
          SoliditySyntax.pushPlaceExpr, SoliditySyntax.pushPlace,
          SoliditySyntax.callExpr, SoliditySyntax.stackCallExpr,
          StandardExample.stackUint, StandardExample.stackUintPlace,
          StandardExample.stackBool, StandardExample.stackBoolPlace,
          StandardExample.memoryPerson, StandardExample.memoryPersonPlace,
          StandardExample.personTy, StandardExample.accountTy,
          StandardExample.tokenTy, StandardExample.personRef,
          StandardExample.accountRef, StandardExample.tokenRef,
          StandardExample.accountField, StandardExample.tokenField,
          StandardExample.ageField, StandardExample.balanceField,
          StandardExample.valueField,
          -- `PlaceExpr.expr` is how `Stmt.push`/`Stmt.pop` reach the
          -- receiver, and `pushPlace` is the place a `push` assigns to;
          -- without them every push/pop statement is opaque.  `pushSlot`
          -- is the slot a bare `push` lands on — the one a `pop` cleared
          -- and gave back — so a push stalls without it.
          PlaceExpr.var, PlaceExpr.field, PlaceExpr.index,
          PlaceExpr.expr, PlaceExpr.pushPlace, Semantics.pushSlot,
          WrappedExpr.kind, WrappedExpr.ty,
          Typed.WrappedExpr.kind, Typed.WrappedExpr.ty,
          Ty.isPrimitive, Field.name, Field.primitive, Field.identity,
          -- The result types the typed smart constructors compute with:
          -- without these `(mkBinop op lhs rhs).ty = op.retTy lhs.ty`
          -- stays stuck, the primitiveness `if` in `execAssign` never
          -- reduces, and every judgment assigning a *binop* to a storage
          -- or memory place — as opposed to a stack variable — stops
          -- mid-block.
          BinOp.retTy, BinOp.isArith, UnOp.retTy,
          -- `evalValue` on a `mkIncDec` branches on these; without them
          -- the `if` never reduces and `x++` in any position stalls.
          IncDec.isIncrement, IncDec.isPre, IncDec.binOp] $[$loc]?)

/-- Compute a concrete interpreter equation
(`Semantics.execStmt s stmt = .ok ?s'` or `= .error ?h`, for concrete `s`
and `stmt`): simp with the interpreter-evaluation battery normalizes the
left-hand side, `rfl` assigns the result metavariable. -/
macro "sol_exec_eval" : tactic =>
  `(tactic| (sol_eval_battery; try rfl))

end Solidity
