import Solidity.Frontend.Testing
import Solidity.Calculus.Close
import Solidity.Calculus.Closers

/-!
# Resolved source operator aliases

The fixtures use custom meanings rather than builtin arithmetic, including
unary/binary `-`, all six comparisons, lazy branches, failure order, nominal
identity and checked/unchecked callee scope. Both compiler pipelines lower
operator operands in source order. This module is a patch validation target;
its proof scripts must be kernel-checked by the integrator.
-/
solc_import "../../../tests/operators-0.8.38/OperatorAliases.ast.json" hash 0xe874faaf62a86a04
  as Imported.OperatorAliases testing
solc_import "../../../tests/operators-0.8.38/OperatorAliasesIR.ast.json" hash 0xdf9f437f53eb8a8b
  as Imported.IR.OperatorAliases testing

namespace Solidity.Examples.Tactics.OperatorAliasesImport
open Lean Solidity.Frontend

private def positive : List String :=
  ["numeric", "comparisons", "unary", "nominal", "order", "nested", "customZero", "lazy", "wrappingBody"]

#guard positive.all fun name =>
  (Imported.OperatorAliases.report.find? (·.name == name)).any fun r =>
    r.admissionChecked && r.status == .elaborated && r.sourceDiagnostic.isNone &&
      r.sourceFeatures.contains .operatorAliases
#guard positive.all fun name =>
  (Imported.IR.OperatorAliases.report.find? (·.name == name)).any fun r =>
    r.admissionChecked && r.status == .elaborated && r.sourceDiagnostic.isNone &&
      r.sourceFeatures.contains .operatorAliases
#guard (Imported.OperatorAliases.report.find? (·.name == "excludedAlias")).any fun r =>
  r.status == .excluded && (r.sourceDiagnostic.map (·.name)) == some `solidity.creationCode
#guard (Imported.IR.OperatorAliases.report.find? (·.name == "excludedAlias")).any fun r =>
  r.status == .excluded && (r.sourceDiagnostic.map (·.name)) == some `solidity.creationCode

/-- `numeric()` uses the source alias bodies in the legacy pipeline. -/
theorem legacy_numeric :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.numeric).isOk = true := by
  decide +kernel

/-- `comparisons()` uses the source alias bodies in the legacy pipeline. -/
theorem legacy_comparisons :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.comparisons).isOk = true := by
  decide +kernel

/-- `unary()` uses the source alias bodies in the legacy pipeline. -/
theorem legacy_unary :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.unary).isOk = true := by
  decide +kernel

/-- `nominal()` uses the source alias bodies in the legacy pipeline. -/
theorem legacy_nominal :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.nominal).isOk = true := by
  decide +kernel

/-- `order()` uses the source alias bodies in the legacy pipeline. -/
theorem legacy_order :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.order).isOk = true := by
  decide +kernel

/-- `nested()` uses the source alias bodies in the legacy pipeline. -/
theorem legacy_nested :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.nested).isOk = true := by
  decide +kernel

/-- `customZero()` uses the source alias bodies in the legacy pipeline. -/
theorem legacy_customZero :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.customZero).isOk = true := by
  decide +kernel

/-- `lazy()` uses the source alias bodies in the legacy pipeline. -/
theorem legacy_lazy :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.lazy).isOk = true := by
  decide +kernel

/-- `wrappingBody()` uses the source alias bodies in the legacy pipeline. -/
theorem legacy_wrappingBody :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.wrappingBody).isOk = true := by
  decide +kernel

/-- `checkedBody()` fails in the legacy pipeline, rather than returning a builtin value. -/
theorem legacy_checkedBody :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.checkedBody).isOk = false := by
  decide +kernel

/-- `discardedUnary()` fails in the legacy pipeline, rather than returning a builtin value. -/
theorem legacy_discardedUnary :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.discardedUnary).isOk = false := by
  decide +kernel

/-- `falseBuiltin()` fails in the legacy pipeline, rather than returning a builtin value. -/
theorem legacy_falseBuiltin :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.falseBuiltin).isOk = false := by
  decide +kernel

/-- `failureOrderRevert()` observes the left operand's failure before evaluating the right. -/
theorem legacy_failureOrderRevert :
    (match Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.failureOrderRevert with
      | .error .revert => true
      | _ => false) = true := by
  decide +kernel

/-- `failureOrderPanic()` observes the left operand's failure before evaluating the right. -/
theorem legacy_failureOrderPanic :
    (match Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.failureOrderPanic with
      | .error .panic => true
      | _ => false) = true := by
  decide +kernel

/-- `numeric()` uses the source alias bodies in the viaIR pipeline. -/
theorem viaIR_numeric :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.numeric).isOk = true := by
  decide +kernel

/-- `comparisons()` uses the source alias bodies in the viaIR pipeline. -/
theorem viaIR_comparisons :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.comparisons).isOk = true := by
  decide +kernel

/-- `unary()` uses the source alias bodies in the viaIR pipeline. -/
theorem viaIR_unary :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.unary).isOk = true := by
  decide +kernel

/-- `nominal()` uses the source alias bodies in the viaIR pipeline. -/
theorem viaIR_nominal :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.nominal).isOk = true := by
  decide +kernel

/-- `order()` uses the source alias bodies in the viaIR pipeline. -/
theorem viaIR_order :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.order).isOk = true := by
  decide +kernel

/-- `nested()` uses the source alias bodies in the viaIR pipeline. -/
theorem viaIR_nested :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.nested).isOk = true := by
  decide +kernel

/-- `customZero()` uses the source alias bodies in the viaIR pipeline. -/
theorem viaIR_customZero :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.customZero).isOk = true := by
  decide +kernel

/-- `lazy()` uses the source alias bodies in the viaIR pipeline. -/
theorem viaIR_lazy :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.lazy).isOk = true := by
  decide +kernel

/-- `wrappingBody()` uses the source alias bodies in the viaIR pipeline. -/
theorem viaIR_wrappingBody :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.wrappingBody).isOk = true := by
  decide +kernel

/-- `checkedBody()` fails in the viaIR pipeline, rather than returning a builtin value. -/
theorem viaIR_checkedBody :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.checkedBody).isOk = false := by
  decide +kernel

/-- `discardedUnary()` fails in the viaIR pipeline, rather than returning a builtin value. -/
theorem viaIR_discardedUnary :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.discardedUnary).isOk = false := by
  decide +kernel

/-- `falseBuiltin()` fails in the viaIR pipeline, rather than returning a builtin value. -/
theorem viaIR_falseBuiltin :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.falseBuiltin).isOk = false := by
  decide +kernel

/-- `failureOrderRevert()` observes the left operand's failure before evaluating the right. -/
theorem viaIR_failureOrderRevert :
    (match Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.failureOrderRevert with
      | .error .revert => true
      | _ => false) = true := by
  decide +kernel

/-- `failureOrderPanic()` observes the left operand's failure before evaluating the right. -/
theorem viaIR_failureOrderPanic :
    (match Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.failureOrderPanic with
      | .error .panic => true
      | _ => false) = true := by
  decide +kernel

/-- The source `castOrderBounds()` fails in the legacy pipeline; its precise EVM code
is pinned by the independent reference, while checked call tests below pin order. -/
theorem legacy_castOrderBounds :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.castOrderBounds).isOk = false := by
  decide +kernel

/-- The source `castOrderDivision()` fails in the legacy pipeline; its precise EVM code
is pinned by the independent reference, while checked call tests below pin order. -/
theorem legacy_castOrderDivision :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.castOrderDivision).isOk = false := by
  decide +kernel

/-- The source `lengthOrderDivision()` fails in the legacy pipeline; its precise EVM code
is pinned by the independent reference, while checked call tests below pin order. -/
theorem legacy_lengthOrderDivision :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.lengthOrderDivision).isOk = false := by
  decide +kernel

/-- The source `modularOrderDivision()` fails in the legacy pipeline; its precise EVM code
is pinned by the independent reference, while checked call tests below pin order. -/
theorem legacy_modularOrderDivision :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.modularOrderDivision).isOk = false := by
  decide +kernel

/-- The source `castOrderBounds()` fails in the viaIR pipeline; its precise EVM code
is pinned by the independent reference, while checked call tests below pin order. -/
theorem viaIR_castOrderBounds :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.castOrderBounds).isOk = false := by
  decide +kernel

/-- The source `castOrderDivision()` fails in the viaIR pipeline; its precise EVM code
is pinned by the independent reference, while checked call tests below pin order. -/
theorem viaIR_castOrderDivision :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.castOrderDivision).isOk = false := by
  decide +kernel

/-- The source `lengthOrderDivision()` fails in the viaIR pipeline; its precise EVM code
is pinned by the independent reference, while checked call tests below pin order. -/
theorem viaIR_lengthOrderDivision :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.lengthOrderDivision).isOk = false := by
  decide +kernel

/-- The source `modularOrderDivision()` fails in the viaIR pipeline; its precise EVM code
is pinned by the independent reference, while checked call tests below pin order. -/
theorem viaIR_modularOrderDivision :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.modularOrderDivision).isOk = false := by
  decide +kernel

/-- Native checked call tests distinguish arithmetic-overflow assertion panic from a later
ordinary bounds revert. These use exactly the argument-hoist path of aliases. -/
def CaptureOrder : Contract := contract!{
  struct Padded { bytes4 b; uint n; }
  function takeBool(bool a, bool b) returns (bool r) { r = a && b; }
  function takeNumber(uint a, uint b) returns (uint r) { r = a + b; }
}

def CaptureOrderIR : Contract := { CaptureOrder with evalOrder := EvalOrder.viaIR }

/-- The legacy call evaluates its earlier bounds operand before every later prefix. -/
theorem checked_legacy_bounds :
    (match Prog.run (State.init CaptureOrder)
      (sol[CaptureOrder]{ checked { uint[] memory xs = new uint[](0); uint top = type(uint).max;
      uint x = takeNumber(xs[0], uint(top + 1)); }; }) with
      | .error .revert => true
      | _ => false) = true := by
  decide +kernel

/-- The legacy call evaluates its earlier overflow operand before every later prefix. -/
theorem checked_legacy_overflow :
    (match Prog.run (State.init CaptureOrder)
      (sol[CaptureOrder]{ checked { uint[] memory xs = new uint[](0); uint top = type(uint).max;
      bool x = takeBool(top + 1 > 0, uint(xs[0]) > 0); }; }) with
      | .error .panic => true
      | _ => false) = true := by
  decide +kernel

/-- The legacy call evaluates its earlier length operand before every later prefix. -/
theorem checked_legacy_length :
    (match Prog.run (State.init CaptureOrder)
      (sol[CaptureOrder]{ checked { uint[2][] memory rows = new uint[2][](0); uint top = type(uint).max;
      bool x = takeBool(top + 1 > 0, rows[0].length > 0); }; }) with
      | .error .panic => true
      | _ => false) = true := by
  decide +kernel

/-- The legacy call evaluates its earlier modular operand before every later prefix. -/
theorem checked_legacy_modular :
    (match Prog.run (State.init CaptureOrder)
      (sol[CaptureOrder]{ checked { uint top = type(uint).max; uint modulus = 0;
      bool x = takeBool(top + 1 > 0, addmod(1, 2, modulus) > 0); }; }) with
      | .error .panic => true
      | _ => false) = true := by
  decide +kernel

/-- The viaIR call evaluates its earlier bounds operand before every later prefix. -/
theorem checked_viaIR_bounds :
    (match Prog.run (State.init CaptureOrderIR)
      (sol[CaptureOrderIR]{ checked { uint[] memory xs = new uint[](0); uint top = type(uint).max;
      uint x = takeNumber(xs[0], uint(top + 1)); }; }) with
      | .error .revert => true
      | _ => false) = true := by
  decide +kernel

/-- The viaIR call evaluates its earlier overflow operand before every later prefix. -/
theorem checked_viaIR_overflow :
    (match Prog.run (State.init CaptureOrderIR)
      (sol[CaptureOrderIR]{ checked { uint[] memory xs = new uint[](0); uint top = type(uint).max;
      bool x = takeBool(top + 1 > 0, uint(xs[0]) > 0); }; }) with
      | .error .panic => true
      | _ => false) = true := by
  decide +kernel

/-- The viaIR call evaluates its earlier length operand before every later prefix. -/
theorem checked_viaIR_length :
    (match Prog.run (State.init CaptureOrderIR)
      (sol[CaptureOrderIR]{ checked { uint[2][] memory rows = new uint[2][](0); uint top = type(uint).max;
      bool x = takeBool(top + 1 > 0, rows[0].length > 0); }; }) with
      | .error .panic => true
      | _ => false) = true := by
  decide +kernel

/-- The viaIR call evaluates its earlier modular operand before every later prefix. -/
theorem checked_viaIR_modular :
    (match Prog.run (State.init CaptureOrderIR)
      (sol[CaptureOrderIR]{ checked { uint top = type(uint).max; uint modulus = 0;
      bool x = takeBool(top + 1 > 0, addmod(1, 2, modulus) > 0); }; }) with
      | .error .panic => true
      | _ => false) = true := by
  decide +kernel

/-- A captured bytes2 array element keeps its byte kind when widened to bytes4. -/
theorem legacy_paddingCapture :
    (Prog.run (State.init Imported.OperatorAliases) Imported.OperatorAliases.paddingCapture).isOk = true := by
  decide +kernel

/-- The ordinary struct-constructor path keeps the same source kind after capture. -/
theorem native_legacy_paddingCapture :
    (Prog.run (State.init CaptureOrder) (sol[CaptureOrder]{
      bytes2[] memory bs = new bytes2[](1); bs[0] = hex"1234";
      Padded memory p = Padded(bs[0], 0);
      assert(p.b == bytes4(hex"12340000"));
    })).isOk = true := by
  decide +kernel

/-- A captured bytes2 array element keeps its byte kind when widened to bytes4. -/
theorem viaIR_paddingCapture :
    (Prog.run (State.init Imported.IR.OperatorAliases) Imported.IR.OperatorAliases.paddingCapture).isOk = true := by
  decide +kernel

/-- The ordinary struct-constructor path keeps the same source kind after capture. -/
theorem native_viaIR_paddingCapture :
    (Prog.run (State.init CaptureOrderIR) (sol[CaptureOrderIR]{
      bytes2[] memory bs = new bytes2[](1); bs[0] = hex"1234";
      Padded memory p = Padded(bs[0], 0);
      assert(p.b == bytes4(hex"12340000"));
    })).isOk = true := by
  decide +kernel

open scoped Scoped
local instance : InContract := ⟨Imported.OperatorAliases⟩

/-- The custom division and remainder bodies accept zero operands and establish
these source assertions in every typed state. No builtin nonzero guard applies. -/
theorem custom_zero_valid : ⊨ᶠ spec!{customZero} := by
  sol_symex
  sol_decide

/-- A builtin interpretation would prove this false assertion; the source alias
body computes 62, and the actual source box is refuted by a concrete panic. -/
theorem false_builtin_invalid : ¬ (⊨ᶠ spec!{falseBuiltin}) :=
  fun h => Modality.afterRunTR_not_panic
    ((h (State.init _)) rfl) (by decide +kernel)

private def put (j : Json) (key : String) (value : Json) : Json :=
  Json.mkObj ((key, value) :: ((j.getObj?.toOption.map (·.toList)).getD []).filter (·.1 != key))

private def erase (j : Json) (key : String) : Json :=
  Json.mkObj (((j.getObj?.toOption.map (·.toList)).getD []).filter (·.1 != key))

private partial def replaceDeclaration (id : Int) (replacement : Json) : Json → Json
  | j@(.obj fields) =>
    if J.id? j == some id then replacement else
      Json.mkObj (fields.toList.map fun (key, value) =>
        (key, replaceDeclaration id replacement value))
  | .arr values => .arr (values.map (replaceDeclaration id replacement))
  | j => j

run_cmd do
  let fixture ← ofExcept (Json.parse (← IO.FS.readFile "tests/operators-0.8.38/OperatorAliases.ast.json"))
  let ast ← ofExcept (fixture.getObjVal? "ast")
  let provenance ← ofExcept (Source.read fixture ast)
  let declarations := (J.nodes ast).filter (J.id? · |>.isSome)
  let operators := (J.nodes ast).filter J.hasOperatorFunction
  unless !operators.isEmpty && operators.all (fun op => (operatorAlias? declarations op).isOk) do
    throwError "a genuine source alias did not validate"
  unless operators.all (fun op => !pureExpr op) do
    throwError "an aliased call was classified as a call-free expression"
  let some binary := operators.find? (fun op => J.kind op == "BinaryOperation" &&
      J.str? op "operator" == some "+") | throwError "missing binary fixture"
  let some unary := operators.find? (fun op => J.kind op == "UnaryOperation" &&
      J.str? op "operator" == some "-") | throwError "missing unary fixture"
  let some id := J.operatorFunction? binary | throwError "missing alias target"
  let some target := declarations.find? (J.id? · == some id) | throwError "missing target declaration"
  let check (ast node : Json) := do
    let ds := (J.nodes ast).filter (J.id? · |>.isSome)
    if (operatorAlias? ds node).isOk then throwError "accepted malformed operator: {node.compress}"
    let result := Admission.scan ast provenance { entry := node, evaluatedRoots := [node] }
    unless (result.diagnostic?.map (·.name)) == some `solidity.operatorAliases &&
        (result.diagnostic?.map (·.kind)) == some .invalidAst do
      throwError "admission did not reject the same malformed operator: {repr result.diagnostic?}"
  for annotation in [Json.null, .str "bad", toJson (0 : Int), toJson (-1 : Int), toJson (99999999 : Int)] do
    check ast (put binary "function" annotation)
  check ast (erase binary "function")
  check ast (put binary "operator" (.str "&&"))
  check ast (put unary "prefix" (.bool false))
  let some unaryId := J.operatorFunction? unary | throwError "missing unary identity"
  check ast (put binary "function" (toJson unaryId))
  let left ← ofExcept (binary.getObjVal? "leftExpression")
  let desc ← ofExcept (left.getObjVal? "typeDescriptions")
  check ast (put binary "leftExpression" (put left "typeDescriptions" (erase desc "typeIdentifier")))
  let some other := declarations.find? (fun d => J.kind d == "FunctionDefinition" &&
      J.str? d "name" == some "mixOther") | throwError "missing distinct nominal type"
  let otherParams ← ofExcept ((← ofExcept (other.getObjVal? "parameters")).getObjValAs? (Array Json) "parameters")
  let some otherFirst := otherParams[0]? | throwError "missing nominal parameter"
  let otherDescription : Json ← Lean.ofExcept (ε := String) (otherFirst.getObjVal? "typeDescriptions")
  check ast (put binary "leftExpression" (put left "typeDescriptions" otherDescription))
  -- Change the return's nominal type without copying another declaration's
  -- IDs: duplicate declarations would mask the intended operator diagnostic.
  let targetReturns : Json ← Lean.ofExcept (ε := String) (target.getObjVal? "returnParameters")
  let targetReturnParams : Array Json ← Lean.ofExcept (ε := String)
    (targetReturns.getObjValAs? (Array Json) "parameters")
  let some targetReturn := targetReturnParams[0]? | throwError "missing target return"
  let targetReturnType : Json ← Lean.ofExcept (ε := String) (targetReturn.getObjVal? "typeName")
  let otherType : Json ← Lean.ofExcept (ε := String) (otherFirst.getObjVal? "typeName")
  let some otherTypeId := J.typeRef? otherType | throwError "missing other nominal identity"
  let wrongReturnType := put (put targetReturnType "typeDescriptions" otherDescription)
    "referencedDeclaration" (toJson otherTypeId)
  let wrongReturnType := match J.opt targetReturnType "pathNode" with
    | some path => put wrongReturnType "pathNode"
        (put (put path "referencedDeclaration" (toJson otherTypeId)) "name" (.str (J.tyStr otherFirst)))
    | none => wrongReturnType
  let wrongReturn := put (put targetReturn "typeDescriptions" otherDescription) "typeName" wrongReturnType
  let wrongReturns := put targetReturns "parameters" (.arr (targetReturnParams.set! 0 wrongReturn))
  for badTarget in [put target "stateMutability" (.str "view"),
      put target "kind" (.str "function"), put target "body" .null,
      put target "returnParameters" wrongReturns] do
    check (replaceDeclaration id badTarget ast) binary

end Solidity.Examples.Tactics.OperatorAliasesImport
