import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Quote

/-!
# Typed source compiler operational controls

Guards changed evaluation order, refusal text, sorting and binding during
removal of opaque partial recursion. The same fixed cases run against the
retained old compiled artifact and the new total artifact. Quoted formulas are
operational observations, not kernel certificates or source-span evidence.
-/
open Solidity Lean
-- Helper declarations, as well as generated case certificates, are checked synchronously.
set_option debug.skipKernelTC false
set_option Elab.async false
namespace TypedSpecCompilerProbe

def C : Contract := { vars := [("count", .uint), ("items", .ref (.array (.prim .uint)))] }
def ctx : SpecCtx C := {
 storage := .storage, ensures := true, result := some .uint,
 locals := [("from", .uint), ("flag", .bool)], refs := [("memory", .mem (.array (.prim .uint)))] }
def names : NCtx := [(.ofName "from", .val .uint), (.ofName "flag", .val .bool),
 (.ofName "result", .val .uint), (.ofName "memory", .mem (.array (.prim .uint)))]
/-- Guards the existing structural string-parser equations at each byte position. -/
theorem flagTakeWhileV1 :
    Substring.takeWhileAux "flag" ⟨4⟩ (!·.isDigit) ⟨0⟩ = ⟨4⟩ := by
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_neg (by decide)]
  rfl

theorem flagEndV1 : "flag".endPos = ⟨4⟩ := rfl

/-- Guards exact source-name resolution, without native proof reduction. -/
theorem flagNameV1 : Var.ofName "flag" = Var.user "flag" := by
  simp only [Var.ofName, FreshNames.parse, instFreshNames, FreshNames.ofPrefixes,
    String.takeWhile, Substring.takeWhile, String.toSubstring, flagEndV1, flagTakeWhileV1]
  rfl

/-- Guards the first, distinct local name through the unchanged parser. -/
theorem fromTakeWhileV1 :
    Substring.takeWhileAux "from" ⟨4⟩ (!·.isDigit) ⟨0⟩ = ⟨4⟩ := by
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_neg (by decide)]
  rfl

theorem fromEndV1 : "from".endPos = ⟨4⟩ := rfl

theorem fromNameV1 : Var.ofName "from" = Var.user "from" := by
  simp only [Var.ofName, FreshNames.parse, instFreshNames, FreshNames.ofPrefixes,
    String.takeWhile, Substring.takeWhile, String.toSubstring, fromEndV1, fromTakeWhileV1]
  rfl

/-- Guards the real four-entry named context's Boolean local lookup. -/
theorem flagReadV1 (D : Contract) :
    NRead.bool (C := D) (NTerm.pv (Var.ofName "flag")) names =
      .ok (.eq (.pvV (.there .here)) (.app0 (.lit (p := .bool) true))) := by
  simp only [NRead.bool, NRead.eq, NTm.resolvePairV, NTm.resolveV,
    NTerm.pv, NTerm.bool, NTerm.lit, NTm.pvV, NTm.app0, NTm.syn,
    NTm.check, NTm.widen, NCtx.findAny,
    names, flagNameV1, fromNameV1, Var.user.injEq, String.reduceEq, if_true, if_false,
    Bool.false_eq_true, NTm.VSort.srt,
    pure_bind, Option.isSome, Option.isNone, Bool.false_and]
  rfl

/-- Guards a Boolean local after one distinct unsigned local, including dependent indices. -/
theorem boolSecondReadV1 (D : Contract) (x y : Var) (tail : NCtx) (hne : y ≠ x) :
    NRead.bool (C := D) (NTerm.pv x) ((y, .val .uint) :: (x, .val .bool) :: tail) =
      .ok (.eq (.pvV (.there .here)) (.app0 (.lit (p := .bool) true))) := by
  simp only [NRead.bool, NRead.eq, NTm.resolvePairV, NTm.resolveV,
    NTerm.pv, NTerm.bool, NTerm.lit, NTm.pvV, NTm.app0, NTm.syn,
    NTm.check, NTm.widen, NCtx.findAny, if_neg hne, if_true, if_false,
    Bool.false_eq_true, NTm.VSort.srt, pure_bind, Option.isSome, Option.isNone, Bool.false_and]
  rfl

/-- Guards the exact malformed-field refusal through existing compiler equations. -/
theorem malformedReadV1 (D : Contract) (context : SpecCtx D) :
    SpecExpr.read D context (.field (.num 1) "x") =
      .error "not a storage path: a state variable, `e.f` or `e[k]`" := by
  unfold SpecExpr.read
  split
  · rename_i e h
    simp only [SpecExpr.field.injEq, String.reduceEq, and_false] at h
  · simp only [SpecExpr.memPath, SpecExpr.path]
    rfl

/-- Guards the existing non-reserved binder decision, not a new admission rule. -/
theorem xNotReservedV1 : reservedSpecName "x" = false := by decide

theorem xPrefixV1 : "x".startsWith "result_" = false := by decide

/-- Guards the one-byte binder through the actual default source-name parser. -/
theorem xTakeWhileV1 :
    Substring.takeWhileAux "x" ⟨1⟩ (!·.isDigit) ⟨0⟩ = ⟨1⟩ := by
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_neg (by decide)]
  rfl

theorem xEndV1 : "x".endPos = ⟨1⟩ := rfl

theorem xNameV1 : Var.ofName "x" = Var.user "x" := by
  simp only [Var.ofName, FreshNames.parse, instFreshNames, FreshNames.ofPrefixes,
    String.takeWhile, Substring.takeWhile, String.toSubstring, xEndV1, xTakeWhileV1]
  rfl

/-- Guards dependent lookup at the freshly introduced Boolean binder. -/
theorem boolHeadReadV1 (D : Contract) (x : Var) (tail : NCtx) :
    NRead.bool (C := D) (NTerm.pv x) ((x, .val .bool) :: tail) =
      .ok (.eq (.pvV .here) (.app0 (.lit (p := .bool) true))) := by
  simp only [NRead.bool, NRead.eq, NTm.resolvePairV, NTm.resolveV,
    NTerm.pv, NTerm.bool, NTerm.lit, NTm.pvV, NTm.app0, NTm.syn,
    NTm.check, NTm.widen, NCtx.findAny, if_true, if_false,
    Bool.false_eq_true, NTm.VSort.srt, pure_bind, Option.isSome, Option.isNone, Bool.false_and]
  rfl

/-- Guards the concrete value-sort distinction used by source equality compilation. -/
theorem uintNotBoolV1 : NTm.VSort.prim .uint ≠ NTm.VSort.prim .bool := by
  intro h
  cases h

/-- Guards source return-name parsing at all six actual byte positions. -/
theorem resultTakeWhileV1 :
    Substring.takeWhileAux "result" ⟨6⟩ (!·.isDigit) ⟨0⟩ = ⟨6⟩ := by
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_neg (by decide)]
  rfl

theorem resultEndV1 : "result".endPos = ⟨6⟩ := rfl

theorem resultNameV1 : Var.ofName "result" = Var.user "result" := by
  simp only [Var.ofName, FreshNames.parse, instFreshNames, FreshNames.ofPrefixes,
    String.takeWhile, Substring.takeWhile, String.toSubstring, resultEndV1, resultTakeWhileV1]
  rfl

/-- Guards exact first/third local indices in the original four-entry context. -/
theorem fromResultReadV1 (D : Contract) :
    NRead.eq (C := D) (NTerm.pv (Var.ofName "from")) (NTerm.pv resultVar) names =
      .ok (.eq (.pvV .here) (.pvV (.there (.there .here)))) := by
  simp only [NRead.eq, NTm.resolvePairV, NTm.resolveV, NTerm.pv, NTm.pvV,
    NTm.check, NTm.widen, NCtx.findAny, names, resultVar,
    fromNameV1, flagNameV1, resultNameV1, Var.user.injEq, String.reduceEq,
    if_true, if_false, Bool.false_eq_true, NTm.VSort.srt,
    pure_bind, Option.isSome, Option.isNone, Bool.false_and]
  rfl

/-- Guards typed source equality under a new unsigned binder without changing its context. -/
theorem uintHeadEqReadV1 (D : Contract) (x : Var) (tail : NCtx) :
    NRead.eq (C := D) (NTerm.pv x) (NTerm.pv x) ((x, .val .uint) :: tail) =
      .ok (.eq (.pvV .here) (.pvV .here)) := by
  simp only [NRead.eq, NTm.resolvePairV, NTm.resolveV, NTerm.pv, NTm.pvV,
    NTm.check, NTm.widen, NCtx.findAny, if_true, if_false,
    Bool.false_eq_true, NTm.VSort.srt, pure_bind, Option.isSome, Option.isNone, Bool.false_and]
  rfl

/-- Guards the original numeric admission facts, without changing the bounds. -/
theorem zeroInRangeV1 : PrimTy.uint.inRange ((0 : Nat) : Int) = true := by decide
theorem oneInRangeV1 : PrimTy.uint.inRange ((1 : Nat) : Int) = true := by decide

theorem numZeroCheckV1 (D : Contract) (scope : NCtx) :
    NTm.check (C := D) (NTerm.num ((0 : Nat) : Int)) (.val .uint) scope =
      .ok (.app0 (.lit (PrimTy.ofLit .uint 0 zeroInRangeV1))) := by
  simp only [NTm.check, NTerm.num, numLit, zeroInRangeV1, dif_pos]
  rfl

theorem numOneCheckV1 (D : Contract) (scope : NCtx) :
    NTm.check (C := D) (NTerm.num ((1 : Nat) : Int)) (.val .uint) scope =
      .ok (.app0 (.lit (PrimTy.ofLit .uint 1 oneInRangeV1))) := by
  simp only [NTm.check, NTerm.num, numLit, oneInRangeV1, dif_pos]
  rfl

/-- Guards the actual filtered predicate's typed binder/literal equality. -/
theorem uintHeadEqOneReadV1 (D : Contract) (x : Var) (tail : NCtx) :
    NRead.eq (C := D) (NTerm.pv x) (NTerm.num ((1 : Nat) : Int)) ((x, .val .uint) :: tail) =
      .ok (.eq (.pvV .here) (.app0 (.lit (PrimTy.ofLit .uint 1 oneInRangeV1)))) := by
  simp only [NRead.eq, NTm.resolvePairV, NTm.resolveV, NTerm.pv, NTm.pvV,
    NTerm.num, NTm.check, NTm.widen, NCtx.findAny, numLit, oneInRangeV1,
    if_true, if_false, Bool.false_eq_true, NTm.VSort.srt,
    pure_bind, Option.isSome, Option.isNone, Bool.false_and]
  rfl

/-- Guards the actual `memory` source-name parser path used by old-state refusal. -/
theorem memoryTakeWhileV1 :
    Substring.takeWhileAux "memory" ⟨6⟩ (!·.isDigit) ⟨0⟩ = ⟨6⟩ := by
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_neg (by decide)]
  rfl

theorem memoryEndV1 : "memory".endPos = ⟨6⟩ := rfl

theorem memoryNameV1 : Var.ofName "memory" = Var.user "memory" := by
  simp only [Var.ofName, FreshNames.parse, instFreshNames, FreshNames.ofPrefixes,
    String.takeWhile, Substring.takeWhile, String.toSubstring, memoryEndV1, memoryTakeWhileV1]
  rfl

/-- Guards the actual `old` source-name parser path used by old-state refusal. -/
theorem oldTakeWhileV1 :
    Substring.takeWhileAux "old" ⟨3⟩ (!·.isDigit) ⟨0⟩ = ⟨3⟩ := by
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_neg (by decide)]
  rfl

theorem oldEndV1 : "old".endPos = ⟨3⟩ := rfl

theorem oldNameV1 : Var.ofName "old" = Var.user "old" := by
  simp only [Var.ofName, FreshNames.parse, instFreshNames, FreshNames.ofPrefixes,
    String.takeWhile, Substring.takeWhile, String.toSubstring, oldEndV1, oldTakeWhileV1]
  rfl

/-- Guards the actual `oldNet` source-name parser path used by old-state refusal. -/
theorem oldNetTakeWhileV1 :
    Substring.takeWhileAux "oldNet" ⟨6⟩ (!·.isDigit) ⟨0⟩ = ⟨6⟩ := by
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_pos (by decide), if_pos (by decide)]
  rw [Substring.takeWhileAux, dif_neg (by decide)]
  rfl

theorem oldNetEndV1 : "oldNet".endPos = ⟨6⟩ := rfl

theorem oldNetNameV1 : Var.ofName "oldNet" = Var.user "oldNet" := by
  simp only [Var.ofName, FreshNames.parse, instFreshNames, FreshNames.ofPrefixes,
    String.takeWhile, Substring.takeWhile, String.toSubstring, oldNetEndV1, oldNetTakeWhileV1]
  rfl

/-- Guards refusal of an absent old storage snapshot binding before reading any path. -/
theorem oldStorageReadV1 (D : Contract) (path : NPTerm D) :
    NRead.not (NRead.eq (NTerm.find (NSTerm.pv oldVar) path)
      (NTerm.num ((0 : Nat) : Int))) names = .error "unknown name old" := by
  simp only [NRead.not, NRead.eq, NTm.resolvePairV, NTm.resolveV,
    NTerm.find, NSTerm.pv, NTm.pvS, NTm.syn, NTerm.num, NCtx.findAny,
    names, oldVar, oldNameV1, fromNameV1, flagNameV1, resultNameV1, memoryNameV1,
    Var.user.injEq, String.reduceEq, if_true, if_false, Bool.false_eq_true,
    NTm.VSort.srt, pure_bind, Option.isSome, Option.isNone, Bool.false_and]
  rfl

/-- Guards that a valid key cannot invent a missing old ledger binding. -/
theorem oldNetReadV1 (D : Contract) :
    NRead.eq (C := D) (NTerm.netOf oldNetVar (NTerm.num ((0 : Nat) : Int)))
      (NTerm.num ((0 : Nat) : Int)) names = .error "unknown name oldNet" := by
  simp only [NRead.eq, NTm.resolvePairV, NTm.resolveV, NTerm.netOf, NTm.netOf,
    NTerm.num, NTm.check, numLit, zeroInRangeV1, NCtx.findAny,
    names, oldNetVar, oldNetNameV1, fromNameV1, flagNameV1, resultNameV1, memoryNameV1,
    Var.user.injEq, String.reduceEq, if_true, if_false, Bool.false_eq_true,
    NTm.VSort.srt, pure_bind, Option.isSome, Option.isNone, Bool.false_and]
  rfl

def cases : List (String × SpecExpr) := [
 ("num", .num 0), ("uintLit", .uintLit 1), ("true", .bool true), ("false", .bool false),
 ("local", .name "flag"), ("missing", .name "missing"), ("storage", .name "count"),
 ("result", .result), ("old", .old (.bool false)), ("old-nested", .old (.old (.bool true))),
 ("net", .net (.num 0)), ("env", .field (.name "msg") "sender"),
 ("balance", .field (.name "this") "balance"), ("unknown-field", .field (.name "missing") "x"),
 ("storage-index", .index (.name "items") (.num 0)),
 ("memory-index", .index (.name "memory") (.num 0)),
 ("storage-length", .field (.name "items") "length"),
 ("memory-length", .field (.name "memory") "length"),
 ("not", .unop .not (.bool true)), ("negative", .unop .neg (.num 1)),
 ("and", .binop .and (.bool true) (.bool false)), ("or", .binop .or (.bool false) (.bool true)),
 ("add", .binop .add (.num 1) (.num 2)), ("eq-bool", .binop .eqB (.bool true) (.bool false)),
 ("eq-local", .binop .eqB (.name "from") (.result)),
 ("ne-storage", .binop .neB (.name "count") (.num 0)),
 ("ledger-cmp", .binop .eqB (.net (.num 0)) (.num 0)),
 ("imp", .imp (.bool true) (.bool false)), ("iff", .iff (.bool false) (.bool true)),
 ("all", .all .uint "x" (.binop .eqB (.name "x") (.name "x"))),
 ("exists", .ex .bool "x" (.name "x")),
 ("reserved", .all .uint "result" (.bool true)),
 ("member", .member .uint (.num 1) [.num 0, .num 1]),
 ("empty-member", .member .uint (.bool true) []),
 ("filter", .memberFilter .uint (.num 1) "x" [.num 0, .num 1] (.binop .eqB (.name "x") (.num 1))),
 ("reserved-filter", .memberFilter .uint (.num 1) "old" [] (.bool true)),
 ("bad-filter-literal", .memberFilter .uint (.num 1) "x" [.name "from"] (.bool true)),
 ("error-order", .binop .eqB (.name "firstMissing") (.name "secondMissing")),
 ("malformed-path", .field (.num 1) "x")]

def contexts : List (String × SpecCtx C) := [("post", ctx), ("pre", {ctx with ensures := false}), ("old", ctx.old)]

def compileAt (modeIndex caseIndex : Nat) : Except String (Fml C names.ctx) := do
 let some (_, context) := contexts[modeIndex]? | throw "missing fixed mode"
 let some (_, expression) := cases[caseIndex]? | throw "missing fixed case"
 let read ← expression.fml C context
 read names

def output : Json := toJson <| (contexts.flatMap fun (mode, context) =>
 cases.map fun (id, expression) =>
  let value := match expression.fml C context with
   | .error error => Json.mkObj [("error", toJson error)]
   | .ok read => match read names with
     | .error error => Json.mkObj [("readError", toJson error)]
     | .ok formula => Json.mkObj [("formula", toJson (reprStr (formula.quote (mkConst `TypedSpecCompilerProbe.C))))]
  Json.mkObj [("mode", toJson mode), ("case", toJson id), ("observation", value)])

#eval (show IO Unit from do
 let some file ← IO.getEnv "TYPED_SPEC_PROBE_OUTPUT" | throw (IO.userError "missing owned probe output")
 IO.FS.writeFile file (output.pretty ++ "\n")
 IO.println s!"TYPED_SPEC_COMPILER_CASES:{cases.length * 3}")
end TypedSpecCompilerProbe

/- Native evaluation below proposes data only. Every proposed output is checked
by a closed equation proof in the kernel under the existing100000 heartbeat ceiling. No native
proof reduction, proof axiom or unchecked declaration may certify a case. -/
open Lean Elab Command Meta
syntax "#typed_spec_kernel_case " num num str : command
elab_rules : command
 | `(#typed_spec_kernel_case $mode:num $index:num $file:str) => liftTermElabM do
  let m := mode.getNat
  let i := index.getNat
  unless m < TypedSpecCompilerProbe.contexts.length && i < TypedSpecCompilerProbe.cases.length do
   throwError "outside fixed compiler corpus"
  let cE := mkConst `TypedSpecCompilerProbe.C
  let C ← unsafe evalExpr Solidity.Contract (mkConst ``Solidity.Contract) cE
  let nE := mkConst `TypedSpecCompilerProbe.names
  let names ← unsafe evalExpr Solidity.NCtx (mkConst ``Solidity.NCtx) nE
  let input ← mkAppM ``TypedSpecCompilerProbe.compileAt #[toExpr m, toExpr i]
  let type ← inferType input
  let value ← unsafe evalExpr (Except String (Solidity.Fml C names.ctx)) type input
  let (``Except, #[errorType, successType]) := type.getAppFnArgs | throwError "unexpected compiler result type"
  let expected := match value with
   | .error message => mkAppN (mkConst ``Except.error [.zero, .zero]) #[errorType, successType, toExpr message]
   | .ok formula => mkAppN (mkConst ``Except.ok [.zero, .zero]) #[errorType, successType, formula.quote cE]
  let proposedType ← mkEq input expected
  let name ← if m == 0 && i == 3 then pure `TypedSpecCompilerProbe.literalFalseKernelV1
    else mkFreshUserName `TypedSpecCompilerProbe.kernelCaseV1
  let options := Elab.async.set (← getOptions) false
  let current := maxHeartbeats.get options
  let limit := if current == 0 then 100000 else min current 100000
  let result ← try
   let proposedProof ← Term.withoutErrToSorry <| Term.elabTerm (← `(by
    simp only [TypedSpecCompilerProbe.flagReadV1, TypedSpecCompilerProbe.xNotReservedV1, TypedSpecCompilerProbe.uintNotBoolV1, reduceCtorEq,
      Except.pure, Except.bind, map_pure, pure_bind, bind_pure_comp, decide_true, decide_false, Bool.true_or,
      String.reduceEq, String.reduceBEq, if_true, if_false,
      Solidity.Semantics.lookupBy, Solidity.reservedSpecName,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.mapM_cons, List.mapM_nil,
      TypedSpecCompilerProbe.compileAt, TypedSpecCompilerProbe.contexts,
      TypedSpecCompilerProbe.cases, TypedSpecCompilerProbe.ctx, TypedSpecCompilerProbe.names,
      TypedSpecCompilerProbe.C, Solidity.SpecCtx.old, Solidity.SpecExpr.fml,
      Solidity.SpecExpr.fml.iff, Solidity.SpecExpr.fml.cond, Solidity.SpecExpr.term,
      Solidity.SpecExpr.termPair, Solidity.SpecExpr.read, Solidity.SpecExpr.memPath,
      Solidity.SpecExpr.path]
    -- Resolve the equation at the original named context before rewriting names.
    all_goals
      first
      | exact TypedSpecCompilerProbe.flagReadV1 _
      | exact TypedSpecCompilerProbe.fromResultReadV1 _
      | exact TypedSpecCompilerProbe.oldStorageReadV1 _ _
      | exact TypedSpecCompilerProbe.oldNetReadV1 _
      | skip
    all_goals simp (config := { failIfUnchanged := false }) only [
      TypedSpecCompilerProbe.boolSecondReadV1, Solidity.Var.user.injEq, String.reduceEq,
      TypedSpecCompilerProbe.flagReadV1, TypedSpecCompilerProbe.malformedReadV1,
      TypedSpecCompilerProbe.xNotReservedV1, TypedSpecCompilerProbe.xPrefixV1,
      TypedSpecCompilerProbe.uintNotBoolV1, Bool.false_or, Bool.false_and,
      Bool.false_eq_true, decide_false, if_false,
      List.mapM_cons, List.mapM_nil,
      TypedSpecCompilerProbe.numZeroCheckV1, TypedSpecCompilerProbe.numOneCheckV1,
      TypedSpecCompilerProbe.zeroInRangeV1, TypedSpecCompilerProbe.oneInRangeV1,
      TypedSpecCompilerProbe.uintHeadEqOneReadV1,
      Solidity.Fml.finiteMember, Solidity.Fml.filteredMember, Solidity.SpecExpr.domainLiteral, Solidity.numLit,
      TypedSpecCompilerProbe.boolHeadReadV1, TypedSpecCompilerProbe.uintHeadEqReadV1,
      Solidity.NRead.not, Solidity.NRead.all,
      Except.pure, Except.bind, map_pure, pure_bind]
    all_goals simp (config := { failIfUnchanged := false }) only [TypedSpecCompilerProbe.xNameV1]
    all_goals with_unfolding_all rfl)) (some proposedType)
   Term.synthesizeSyntheticMVarsNoPostponing
   let proposedProof ← instantiateMVars proposedProof
   let proposedType ← instantiateMVars proposedType
   if [proposedProof, proposedType].any (fun e => e.hasMVar || e.hasFVar || e.hasSorry || e.hasLevelMVar) then
    throwError "compiler correspondence proof is not closed and sorry-free"
   let declaration := Declaration.thmDecl {name, levelParams := [], type := proposedType, value := proposedProof}
   let checkedOptions := debug.skipKernelTC.set (maxHeartbeats.set options limit) false
   let _ ← ofExceptKernelException (Kernel.Environment.addDecl (← getEnv).toKernelEnv checkedOptions declaration)
   withOptions (fun _ => debug.skipKernelTC.set (maxHeartbeats.set options limit) false) (addDecl declaration)
   let axioms ← collectAxioms name
   unless axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do throwError "nonstandard compiler correspondence axiom: {axioms}"
   pure (Json.mkObj [("status", toJson "kernel-checked"), ("declaration", toJson name.toString),
    ("axioms", toJson (axioms.map Name.toString))])
  catch error => pure (Json.mkObj [("status", toJson "failed"), ("error", toJson (← error.toMessageData.toString))])
  let path := System.FilePath.mk file.getString
  let prior ← if ← path.pathExists then do
   let text ← IO.FS.readFile path
   let .ok json := Json.parse text | throwError "malformed prior case observations"
   let .ok rows := json.getArr? | throwError "prior observations are not an array"
   pure rows
   else pure #[]
  let result := result.setObjVal! "modeIndex" (toJson m) |>.setObjVal! "caseIndex" (toJson i)
  IO.FS.writeFile path (Json.pretty (toJson (prior.push result)) ++ "\n")
  unless (result.getObjValAs? String "status").toOption == some "kernel-checked" do
   throwError "actual typed compiler output failed kernel correspondence at mode={m} case={i}: {result.compress}"
  logInfo m!"TYPED_SPEC_KERNEL_CASE {m}/{i}"

syntax "#typed_spec_wrong_literal " str : command
elab_rules : command
 | `(#typed_spec_wrong_literal $file:str) => liftTermElabM do
  let input ← mkAppM ``TypedSpecCompilerProbe.compileAt #[toExpr (0 : Nat), toExpr (3 : Nat)]
  let type ← inferType input
  let (``Except, #[errorType, successType]) := type.getAppFnArgs | throwError "wrong literal result type"
  let (``Solidity.Fml, arguments) := successType.getAppFnArgs | throwError "wrong typed formula"
  let wrong := mkAppN (mkConst ``Solidity.Fml.tt) arguments
  let expected := mkAppN (mkConst ``Except.ok [.zero, .zero]) #[errorType, successType, wrong]
  let name ← mkFreshUserName `TypedSpecCompilerProbe.wrongLiteralV1
  let proof := mkConst `TypedSpecCompilerProbe.literalFalseKernelV1
  let falseFormula := mkAppN (mkConst ``Solidity.Fml.not) (arguments.push (mkAppN (mkConst ``Solidity.Fml.tt) arguments))
  let falseExpected := mkAppN (mkConst ``Except.ok [.zero, .zero]) #[errorType, successType, falseFormula]
  unless ← isDefEq (← inferType proof) (← mkEq input falseExpected) do throwError "missing actual checked false-clause proof"
  let declaration := Declaration.thmDecl {name, levelParams := [], type := ← mkEq input expected, value := proof}
  let saved ← Term.saveState
  let options := Elab.async.set (← getOptions) false
  let current := maxHeartbeats.get options
  let limit := if current == 0 then 100000 else min current 100000
  let message ← try
   let checkedOptions := debug.skipKernelTC.set (maxHeartbeats.set options limit) false
   let _ ← ofExceptKernelException (Kernel.Environment.addDecl (← getEnv).toKernelEnv checkedOptions declaration)
   pure none
  catch error => pure (some (← error.toMessageData.toString))
  saved.restore
  IO.FS.writeFile file.getString ((Json.mkObj [("rejected", toJson message.isSome), ("error", toJson message),
   ("boundary", toJson "Wrong typed output for actual compiler literal, not a source-span control")]).pretty ++ "\n")
  let some message := message | throwError "wrong literal compiler output was accepted"
  unless (message.toLower.splitOn "mismatch").length > 1 do throwError "wrong literal rejected for an unexpected reason: {message}"
  logInfo "TYPED_SPEC_WRONG_LITERAL_REFUSED"
