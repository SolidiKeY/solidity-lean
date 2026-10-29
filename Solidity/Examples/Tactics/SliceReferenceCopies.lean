import Solidity.Frontend.Import
import Solidity.Examples.Tactics.SliceCopies

/-! Source-to-typed-run certificates for fixed primitive calldata slice rows.
Compiler agreement is checked separately; these proofs certify emitted runs. -/
solc_import "../../../tests/solc/SliceReferenceCopies.ast.json" hash 0xc21a01ff899d97c
  as Legacy.SliceReferenceCopies testing
solc_import "../../../tests/solc/SliceReferenceCopies.viaIR.ast.json" hash 0x6db2cdeb5efe2177
  as ViaIR.SliceReferenceCopies testing

namespace Solidity.Examples.Tactics.SliceReferenceCopies
open Semantics
open Solidity.Examples.Tactics.SliceCopies (observe_run_of_fuel)

/-- Both modern nested identifiers and historical source leaf names refuse
nominal slices before a primitive type erasure can hide the declaration. -/
private def nominalSliceRefused (leaf : String) (identifier : Option String) : Bool :=
  let desc := [("typeString", Lean.Json.str leaf)] ++
    identifier.toList.map (fun id => ("typeIdentifier", Lean.Json.str id))
  let node := Lean.Json.mkObj [("nodeType", .str "IndexRangeAccess"),
    ("typeDescriptions", Lean.Json.mkObj desc)]
  let decl := Lean.Json.mkObj [("nodeType", .str "UserDefinedValueTypeDefinition"),
    ("name", .str "Token"), ("canonicalName", .str "Token")]
  match (Frontend.expr node).run { declarations := [decl] } with
  | .error (.unsupported msg _) => (msg.splitOn "nominal").length > 1
  | _ => false
#guard nominalSliceRefused "Token[2] calldata[] calldata slice" none
#guard nominalSliceRefused "uint8[2] calldata[] calldata slice"
  (some "t_array$_t_array$_t_userDefinedValueType$_Token_$3_$2_calldata_ptr_$dyn_calldata_ptr_slice")

namespace legacy

#guard ["nominal", "enums", "structs"].all fun name =>
  (Legacy.SliceReferenceCopies.report.find? (·.name == name)).any (·.status == .unsupported)

private def copiesInput := sol[Legacy.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  copies(a);
}
/-- `copies` retains its source assertions and exact model halt class. -/
theorem copies_run : (Prog.run (State.init Legacy.SliceReferenceCopies) copiesInput).isOk = true := by
  apply observe_run_of_fuel copiesInput (State.init Legacy.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def independentInput := sol[Legacy.SliceReferenceCopies]{
  uint8[2] memory row = [uint8(5), 6];
  uint8[2][] memory a = new uint8[2][](2); a[0] = row; a[1] = row;
  independent(a);
}
/-- `independent` retains its source assertions and exact model halt class. -/
theorem independent_run : (Prog.run (State.init Legacy.SliceReferenceCopies) independentInput).isOk = true := by
  apply observe_run_of_fuel independentInput (State.init Legacy.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def reboundInput := sol[Legacy.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  uint8[2][] memory ys = new uint8[2][](1); ys[0] = [uint8(3), 4];
  rebound(a, ys);
}
/-- `rebound` retains its source assertions and exact model halt class. -/
theorem rebound_run : (Prog.run (State.init Legacy.SliceReferenceCopies) reboundInput).isOk = true := by
  apply observe_run_of_fuel reboundInput (State.init Legacy.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def endpointsInput := sol[Legacy.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  endpoints(a);
}
/-- `endpoints` retains its source assertions and exact model halt class. -/
theorem endpoints_run : (Prog.run (State.init Legacy.SliceReferenceCopies) endpointsInput).isOk = true := by
  apply observe_run_of_fuel endpointsInput (State.init Legacy.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def passingInput := sol[Legacy.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  passing(a);
}
/-- `passing` retains its source assertions and exact model halt class. -/
theorem passing_run : (Prog.run (State.init Legacy.SliceReferenceCopies) passingInput).isOk = true := by
  apply observe_run_of_fuel passingInput (State.init Legacy.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def returnedInput := sol[Legacy.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  returned(a);
}
/-- `returned` retains its source assertions and exact model halt class. -/
theorem returned_run : (Prog.run (State.init Legacy.SliceReferenceCopies) returnedInput).isOk = true := by
  apply observe_run_of_fuel returnedInput (State.init Legacy.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def storageCopyInput := sol[Legacy.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  storageCopy(a);
}
/-- `storageCopy` retains its source assertions and exact model halt class. -/
theorem storageCopy_run : (Prog.run (State.init Legacy.SliceReferenceCopies) storageCopyInput).isOk = true := by
  apply observe_run_of_fuel storageCopyInput (State.init Legacy.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def emptyInput := sol[Legacy.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  empty(a);
}
/-- `empty` retains its source assertions and exact model halt class. -/
theorem empty_run : (Prog.run (State.init Legacy.SliceReferenceCopies) emptyInput).isOk = true := by
  apply observe_run_of_fuel emptyInput (State.init Legacy.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def signedInput := sol[Legacy.SliceReferenceCopies]{
  int8[2][] memory a = new int8[2][](1); a[0] = [int8(-128), 127];
  signed(a);
}
/-- `signed` retains its source assertions and exact model halt class. -/
theorem signed_run : (Prog.run (State.init Legacy.SliceReferenceCopies) signedInput).isOk = true := by
  apply observe_run_of_fuel signedInput (State.init Legacy.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def kindsInput := sol[Legacy.SliceReferenceCopies]{
  bool[2][] memory f = new bool[2][](1); f[0] = [true, false];
  bytes2[2][] memory b = new bytes2[2][](1); b[0] = [bytes2(0x1234), bytes2(0xabcd)];
  address[2][] memory a = new address[2][](1); a[0] = [address(17), address(18)];
  kinds(f, b, a);
}
/-- `kinds` retains its source assertions and exact model halt class. -/
theorem kinds_run : (Prog.run (State.init Legacy.SliceReferenceCopies) kindsInput).isOk = true := by
  apply observe_run_of_fuel kindsInput (State.init Legacy.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def invalidRangeInput := sol[Legacy.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  invalidRange(a);
}
/-- `invalidRange` retains its source assertions and exact model halt class. -/
theorem invalidRange_run : (match Prog.run (State.init Legacy.SliceReferenceCopies) invalidRangeInput with | .error .revert => true | _ => false) = true := by
  apply observe_run_of_fuel invalidRangeInput (State.init Legacy.SliceReferenceCopies) 8
    (fun r => match r with | .error .revert => true | _ => false) rfl
  decide +kernel

private def rowBoundsInput := sol[Legacy.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  uint8 r = rowBounds(a);
}
/-- `rowBounds` retains its source assertions and exact model halt class. -/
theorem rowBounds_run : (match Prog.run (State.init Legacy.SliceReferenceCopies) rowBoundsInput with | .error .revert => true | _ => false) = true := by
  apply observe_run_of_fuel rowBoundsInput (State.init Legacy.SliceReferenceCopies) 8
    (fun r => match r with | .error .revert => true | _ => false) rfl
  decide +kernel

private def falsePostInput := sol[Legacy.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  falsePost(a);
}
/-- `falsePost` retains its source assertions and exact model halt class. -/
theorem falsePost_run : (match Prog.run (State.init Legacy.SliceReferenceCopies) falsePostInput with | .error .panic => true | _ => false) = true := by
  apply observe_run_of_fuel falsePostInput (State.init Legacy.SliceReferenceCopies) 8
    (fun r => match r with | .error .panic => true | _ => false) rfl
  decide +kernel

private def narrowFailureInput := sol[Legacy.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](1); a[0] = [uint8(255), 0];
  narrowFailure(a);
}
/-- `narrowFailure` retains its source assertions and exact model halt class. -/
theorem narrowFailure_run : (match Prog.run (State.init Legacy.SliceReferenceCopies) narrowFailureInput with | .error .revert => true | _ => false) = true := by
  apply observe_run_of_fuel narrowFailureInput (State.init Legacy.SliceReferenceCopies) 8
    (fun r => match r with | .error .revert => true | _ => false) rfl
  decide +kernel

private def inlineCopyInput := sol[Legacy.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  inlineCopy(a);
}
/-- Inline arrays preserve direct and named slice-copy types and lazy effects. -/
theorem inlineCopy_run : (Prog.run (State.init Legacy.SliceReferenceCopies) inlineCopyInput).isOk = true := by
  apply observe_run_of_fuel inlineCopyInput (State.init Legacy.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

#print axioms inlineCopy_run
#print axioms copies_run
#print axioms independent_run
#print axioms rebound_run
#print axioms kinds_run
#print axioms invalidRange_run
#print axioms rowBounds_run
#print axioms falsePost_run
#print axioms narrowFailure_run
#print axioms endpoints_run
#print axioms passing_run
#print axioms returned_run
#print axioms storageCopy_run
#print axioms empty_run
#print axioms signed_run

end legacy

namespace viaIR

#guard ["nominal", "enums", "structs"].all fun name =>
  (ViaIR.SliceReferenceCopies.report.find? (·.name == name)).any (·.status == .unsupported)

private def copiesInput := sol[ViaIR.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  copies(a);
}
/-- `copies` retains its source assertions and exact model halt class. -/
theorem copies_run : (Prog.run (State.init ViaIR.SliceReferenceCopies) copiesInput).isOk = true := by
  apply observe_run_of_fuel copiesInput (State.init ViaIR.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def independentInput := sol[ViaIR.SliceReferenceCopies]{
  uint8[2] memory row = [uint8(5), 6];
  uint8[2][] memory a = new uint8[2][](2); a[0] = row; a[1] = row;
  independent(a);
}
/-- `independent` retains its source assertions and exact model halt class. -/
theorem independent_run : (Prog.run (State.init ViaIR.SliceReferenceCopies) independentInput).isOk = true := by
  apply observe_run_of_fuel independentInput (State.init ViaIR.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def reboundInput := sol[ViaIR.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  uint8[2][] memory ys = new uint8[2][](1); ys[0] = [uint8(3), 4];
  rebound(a, ys);
}
/-- `rebound` retains its source assertions and exact model halt class. -/
theorem rebound_run : (Prog.run (State.init ViaIR.SliceReferenceCopies) reboundInput).isOk = true := by
  apply observe_run_of_fuel reboundInput (State.init ViaIR.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def endpointsInput := sol[ViaIR.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  endpoints(a);
}
/-- `endpoints` retains its source assertions and exact model halt class. -/
theorem endpoints_run : (Prog.run (State.init ViaIR.SliceReferenceCopies) endpointsInput).isOk = true := by
  apply observe_run_of_fuel endpointsInput (State.init ViaIR.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def passingInput := sol[ViaIR.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  passing(a);
}
/-- `passing` retains its source assertions and exact model halt class. -/
theorem passing_run : (Prog.run (State.init ViaIR.SliceReferenceCopies) passingInput).isOk = true := by
  apply observe_run_of_fuel passingInput (State.init ViaIR.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def returnedInput := sol[ViaIR.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  returned(a);
}
/-- `returned` retains its source assertions and exact model halt class. -/
theorem returned_run : (Prog.run (State.init ViaIR.SliceReferenceCopies) returnedInput).isOk = true := by
  apply observe_run_of_fuel returnedInput (State.init ViaIR.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def storageCopyInput := sol[ViaIR.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  storageCopy(a);
}
/-- `storageCopy` retains its source assertions and exact model halt class. -/
theorem storageCopy_run : (Prog.run (State.init ViaIR.SliceReferenceCopies) storageCopyInput).isOk = true := by
  apply observe_run_of_fuel storageCopyInput (State.init ViaIR.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def emptyInput := sol[ViaIR.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  empty(a);
}
/-- `empty` retains its source assertions and exact model halt class. -/
theorem empty_run : (Prog.run (State.init ViaIR.SliceReferenceCopies) emptyInput).isOk = true := by
  apply observe_run_of_fuel emptyInput (State.init ViaIR.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def signedInput := sol[ViaIR.SliceReferenceCopies]{
  int8[2][] memory a = new int8[2][](1); a[0] = [int8(-128), 127];
  signed(a);
}
/-- `signed` retains its source assertions and exact model halt class. -/
theorem signed_run : (Prog.run (State.init ViaIR.SliceReferenceCopies) signedInput).isOk = true := by
  apply observe_run_of_fuel signedInput (State.init ViaIR.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def kindsInput := sol[ViaIR.SliceReferenceCopies]{
  bool[2][] memory f = new bool[2][](1); f[0] = [true, false];
  bytes2[2][] memory b = new bytes2[2][](1); b[0] = [bytes2(0x1234), bytes2(0xabcd)];
  address[2][] memory a = new address[2][](1); a[0] = [address(17), address(18)];
  kinds(f, b, a);
}
/-- `kinds` retains its source assertions and exact model halt class. -/
theorem kinds_run : (Prog.run (State.init ViaIR.SliceReferenceCopies) kindsInput).isOk = true := by
  apply observe_run_of_fuel kindsInput (State.init ViaIR.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

private def invalidRangeInput := sol[ViaIR.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  invalidRange(a);
}
/-- `invalidRange` retains its source assertions and exact model halt class. -/
theorem invalidRange_run : (match Prog.run (State.init ViaIR.SliceReferenceCopies) invalidRangeInput with | .error .revert => true | _ => false) = true := by
  apply observe_run_of_fuel invalidRangeInput (State.init ViaIR.SliceReferenceCopies) 8
    (fun r => match r with | .error .revert => true | _ => false) rfl
  decide +kernel

private def rowBoundsInput := sol[ViaIR.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  uint8 r = rowBounds(a);
}
/-- `rowBounds` retains its source assertions and exact model halt class. -/
theorem rowBounds_run : (match Prog.run (State.init ViaIR.SliceReferenceCopies) rowBoundsInput with | .error .revert => true | _ => false) = true := by
  apply observe_run_of_fuel rowBoundsInput (State.init ViaIR.SliceReferenceCopies) 8
    (fun r => match r with | .error .revert => true | _ => false) rfl
  decide +kernel

private def falsePostInput := sol[ViaIR.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  falsePost(a);
}
/-- `falsePost` retains its source assertions and exact model halt class. -/
theorem falsePost_run : (match Prog.run (State.init ViaIR.SliceReferenceCopies) falsePostInput with | .error .panic => true | _ => false) = true := by
  apply observe_run_of_fuel falsePostInput (State.init ViaIR.SliceReferenceCopies) 8
    (fun r => match r with | .error .panic => true | _ => false) rfl
  decide +kernel

private def narrowFailureInput := sol[ViaIR.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](1); a[0] = [uint8(255), 0];
  narrowFailure(a);
}
/-- `narrowFailure` retains its source assertions and exact model halt class. -/
theorem narrowFailure_run : (match Prog.run (State.init ViaIR.SliceReferenceCopies) narrowFailureInput with | .error .revert => true | _ => false) = true := by
  apply observe_run_of_fuel narrowFailureInput (State.init ViaIR.SliceReferenceCopies) 8
    (fun r => match r with | .error .revert => true | _ => false) rfl
  decide +kernel

private def inlineCopyInput := sol[ViaIR.SliceReferenceCopies]{
  uint8[2][] memory a = new uint8[2][](3);
  a[0] = [uint8(3), 4]; a[1] = [uint8(5), 6]; a[2] = [uint8(9), 10];
  inlineCopy(a);
}
/-- Inline arrays preserve direct and named slice-copy types and lazy effects. -/
theorem inlineCopy_run : (Prog.run (State.init ViaIR.SliceReferenceCopies) inlineCopyInput).isOk = true := by
  apply observe_run_of_fuel inlineCopyInput (State.init ViaIR.SliceReferenceCopies) 8
    (fun r => r.isOk) rfl
  decide +kernel

#print axioms inlineCopy_run
#print axioms copies_run
#print axioms independent_run
#print axioms rebound_run
#print axioms kinds_run
#print axioms invalidRange_run
#print axioms rowBounds_run
#print axioms falsePost_run
#print axioms narrowFailure_run
#print axioms endpoints_run
#print axioms passing_run
#print axioms returned_run
#print axioms storageCopy_run
#print axioms empty_run
#print axioms signed_run

end viaIR

-- No shallow fallback is available for other reference shapes or nominal leaves.
#guard (elabProgS Legacy.SliceReferenceCopies (sol_raw!{
  uint[][] memory a = new uint[][](2); uint[][] memory b = a[:];
})).isOk == false
#guard (elabProgS Legacy.SliceReferenceCopies (sol_raw!{
  uint8[2][] memory a = new uint8[2][](2); uint[2][] memory b = a[:];
})).isOk == false
#guard (elabProgS Legacy.SliceReferenceCopies (sol_raw!{
  uint8[2][] memory a = new uint8[2][](2); uint8[2][] calldata v = a[:]; v[0][0] = 1;
})).isOk == false

-- Existing stable duplicate primitive targets stay admitted. Effectful and
-- dependent nonlocal tuple targets are explicitly outside this slice increment.
#guard (elabProgS Legacy.SliceReferenceCopies (sol_raw!{
  uint[2] memory a; (a[0], a[0]) = (1, 2);
})).isOk
#guard (elabProgS Legacy.SliceReferenceCopies (sol_raw!{
  uint[2] memory a; uint i = 0; (a[i++], a[0]) = (1, 2);
})).isOk == false
#guard (elabProgS Legacy.SliceReferenceCopies (sol_raw!{
  uint[2] memory a; uint i = 0; (a[i], i) = (1, 2);
})).isOk == false

-- The assignment check accepts the same source width; it is not a blanket refusal.
#guard (elabProgS Legacy.SliceReferenceCopies (sol_raw!{
  uint8[2][] memory a = new uint8[2][](2); uint8[2][] memory b; b = [a[:]][0];
})).isOk
-- Deferring only the pre-hoist projection check must not erase source widths.
#guard (elabProgS Legacy.SliceReferenceCopies (sol_raw!{
  uint8[2][] memory a = new uint8[2][](2); uint[2][] memory b = [a[:]][0];
})).isOk == false
#guard (elabProgS Legacy.SliceReferenceCopies (sol_raw!{
  uint8[2][] memory a = new uint8[2][](2); uint[2][] memory b; b = [a[:]][0];
})).isOk == false

-- Call argument projections are checked before formal-typed capture.
private def ExactRows : Contract := contract!{
  function takeRows(uint8[2][] memory xs) returns (uint r) { r = xs.length; }
}
#guard (elabProgS ExactRows (sol_raw!{
  uint8[2][] memory a = new uint8[2][](1); uint r = takeRows([a[:]][0]);
})).isOk
#guard (elabProgS ExactRows (sol_raw!{
  uint[2][] memory a = new uint[2][](1); uint r = takeRows([a[:]][0]);
})).isOk == false

end Solidity.Examples.Tactics.SliceReferenceCopies
