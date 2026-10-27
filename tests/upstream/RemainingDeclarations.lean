import Solidity.Tools.Upstream

solc_import "../solc/RemainingDeclarations.ast.json" hash 0x5d429fa78f336311 as Imported.Remaining.StaticCodeConstants testing
solc_import "../solc/RemainingDeclarations.ast.json" hash 0x5d429fa78f336311 as Imported.Remaining.EnumStructFields testing
solc_import "../solc/RemainingDeclarations.ast.json" hash 0x5d429fa78f336311 as Imported.Remaining.MixedStorageResults testing
solc_import "../solc/RemainingDeclarations.ast.json" hash 0x5d429fa78f336311 as Imported.Remaining.MixedReturnRefusal testing
solc_import "../solc/RemainingDeclarationsIR.ast.json" hash 0xf689acee6521ec52 as Imported.RemainingIR.StaticCodeConstants testing
solc_import "../solc/RemainingDeclarationsIR.ast.json" hash 0xf689acee6521ec52 as Imported.RemainingIR.EnumStructFields testing
solc_import "../solc/RemainingDeclarationsIR.ast.json" hash 0xf689acee6521ec52 as Imported.RemainingIR.MixedStorageResults testing
solc_import "../solc/RemainingDeclarationsIR.ast.json" hash 0xf689acee6521ec52 as Imported.RemainingIR.MixedReturnRefusal testing

solc_import "../solc/RemainingDeclarations.ast.json" hash 0x5d429fa78f336311 as Imported.Remaining.EnumIdentity testing
solc_import "../solc/RemainingDeclarationsIR.ast.json" hash 0xf689acee6521ec52 as Imported.RemainingIR.EnumIdentity testing

solc_import "../solc/RemainingDeclarations.ast.json" hash 0x5d429fa78f336311 as Imported.Remaining.EnumDecodeRefusal testing
solc_import "../solc/RemainingDeclarationsIR.ast.json" hash 0xf689acee6521ec52 as Imported.RemainingIR.EnumDecodeRefusal testing

solc_import "../solc/RemainingDeclarations.ast.json" hash 0x5d429fa78f336311 as Imported.Remaining.EnumInputRefusal testing

solc_import "../solc/RemainingDeclarationsIR.ast.json" hash 0xf689acee6521ec52 as Imported.RemainingIR.EnumInputRefusal testing

namespace Solidity.Upstream.RemainingDeclarations
open Solidity Solidity.Frontend Lean

/-- Binding a scalar co-result cannot change the captured storage alias,
for every intrinsic caller context, heap and state. -/
theorem scalar_projection_keeps_alias {C : Contract} {Γ : Ctx} {R : RefTy} {p : PrimTy}
    (state : State C (.alias R :: Γ)) (value : Val C (.alias R :: Γ) p)
    (literal : p.Denote) (evaluates : value.evalT state = .ok literal) :
    (TRun.declLocal p (some value) state).toOption.map (fun out =>
      (TEnv.get (H := out.st.H) (.there .here) out.st.env : Option (SRef C (.ref R)))) =
      some (TEnv.get (H := state.H) .here state.env : Option (SRef C (.ref R))) := by
  simp only [TRun.declLocal, evaluates]
  rfl

/-- info: 'Solidity.Upstream.RemainingDeclarations.scalar_projection_keeps_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms scalar_projection_keeps_alias
/-- info: 'Solidity.Frontend.staticCompilerLength_agrees' depends on axioms: [propext] -/
#guard_msgs in #print axioms staticCompilerLength_agrees

/-- The scalar co-result is exactly the value supplied to the checked
primitive declaration, independent of the captured reference and caller state. -/
theorem scalar_projection_value {C : Contract} {Γ : Ctx} {p : PrimTy}
    (state : State C Γ) (value : Val C Γ p) (literal : p.Denote)
    (evaluates : value.evalT state = .ok literal) :
    (TRun.declLocal p (some value) state).toOption.map (fun out =>
      (TEnv.get (H := out.st.H) .here out.st.env : p.Denote)) = some literal := by
  simp only [TRun.declLocal, evaluates]
  rfl
/-- info: 'Solidity.Upstream.RemainingDeclarations.scalar_projection_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms scalar_projection_value

def replaceField (object : Json) (key : String) (value : Json) : Json :=
  match object with
  | .obj fields => Json.mkObj (fields.toList.filter (·.1 != key) ++ [(key, value)])
  | _ => object

def hexNat (text : String) : Nat := text.toList.foldl (fun n c =>
  n * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10)) 0

def fixture (ir : Bool) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile (if ir then
    "tests/solc/RemainingDeclarationsIR.ast.json" else "tests/solc/RemainingDeclarations.ast.json")))

def checkArtifact (ir : Bool) : IO Unit := do
  let input ← fixture ir
  let ast ← IO.ofExcept (input.getObjVal? "ast")
  let provenance ← IO.ofExcept (Source.read input ast)
  let code ← IO.ofExcept (Source.readCompilerCode input ast provenance)
  unless code.length == 1 do throw (IO.userError "missing target code")
  let artifact ← IO.ofExcept (input.getObjVal? "compilerCode")
  let settings ← IO.ofExcept (artifact.getObjVal? "settings")
  for bad in [replaceField artifact "compilerSha256" (toJson "bad"),
      replaceField artifact "sourceSha256" (toJson "bad"),
      replaceField artifact "settings" (replaceField settings "viaIR" (toJson (!ir)))] do
    if (Source.readCompilerCode (replaceField input "compilerCode" bad) ast provenance).isOk then
      throw (IO.userError "mismatched static artifact accepted")
  let contracts ← IO.ofExcept (artifact.getObjValAs? (Array Json) "contracts")
  let unitSelection ← IO.ofExcept (settings.getObjVal? "outputSelection")
  let .obj units := unitSelection | throw (IO.userError "missing output unit")
  let unit := units.toList.head!.2
  for bad in [replaceField artifact "contracts" (toJson #[contracts[0]!, contracts[0]!]),
      replaceField artifact "settings" (replaceField settings "outputSelection"
        (Json.mkObj [("wrong-unit.sol", unit)]))] do
    if (Source.readCompilerCode (replaceField input "compilerCode" bad) ast provenance).isOk then
      throw (IO.userError "artifact identity/unit mismatch accepted")
  for bad in [replaceField contracts[0]! "creationCode" (toJson "__link__"),
      replaceField contracts[0]! "id" (toJson (999999 : Nat)),
      replaceField contracts[0]! "runtimeCode" (toJson "f")] do
    let altered := replaceField artifact "contracts" (toJson #[bad])
    if (Source.readCompilerCode (replaceField input "compilerCode" altered) ast provenance).isOk then
      throw (IO.userError "invalid static artifact accepted")

def checkEnumDeclarations (ir : Bool) : IO Unit := do
  let input ← fixture ir
  let ast ← IO.ofExcept (input.getObjVal? "ast")
  let nodes ← IO.ofExcept (ast.getObjValAs? (Array Json) "nodes")
  let some owner := nodes.toList.find? (fun n => Frontend.J.str? n "name" == some "EnumStructFields")
    | throw (IO.userError "missing enum owner")
  let members ← IO.ofExcept (owner.getObjValAs? (Array Json) "nodes")
  let some declaration := members.toList.find? (fun n => Frontend.J.kind n == "EnumDefinition")
    | throw (IO.userError "missing enum declaration")
  let values ← IO.ofExcept (declaration.getObjValAs? (Array Json) "members")
  unless (readContract ast "EnumStructFields" [] true).isOk do
    throw (IO.userError "valid enum context refused")
  let withoutId := match values[0]! with
    | .obj fields => Json.mkObj (fields.toList.filter (·.1 != "id"))
    | value => value
  let tooMany := (List.range 257).map fun index => Json.mkObj
    [("nodeType", toJson "EnumValue"), ("id", toJson (100000 + index)),
      ("name", toJson ("V" ++ toString index))]
  for badValues in [#[], #[values[0]!, values[0]!], #[withoutId],
      #[replaceField values[0]! "name" (toJson "")],
      #[values[0]!, replaceField values[1]! "id" (toJson (Frontend.J.id? values[0]!).get!)],
      #[values[0]!, replaceField values[1]! "name" (toJson (Frontend.J.str? values[0]! "name").get!)],
      tooMany.toArray] do
    let bad := replaceField declaration "members" (toJson badValues)
    let changed := replaceField owner "nodes" (toJson (members.map fun n =>
      if Frontend.J.id? n == Frontend.J.id? declaration then bad else n))
    let altered := replaceField ast "nodes" (toJson (nodes.map fun n =>
      if Frontend.J.id? n == Frontend.J.id? owner then changed else n))
    if (readContract altered "EnumStructFields" [] true).isOk then
      throw (IO.userError "malformed enum declaration accepted")

#eval checkEnumDeclarations false
#eval checkEnumDeclarations true
#eval checkArtifact false
#eval checkArtifact true

def check (ir wrong : Bool) : IO Unit := do
  let input ← fixture ir
  let artifact ← IO.ofExcept (input.getObjVal? "compilerCode")
  let contracts ← IO.ofExcept (artifact.getObjValAs? (Array Json) "contracts")
  let creation ← IO.ofExcept (contracts[0]!.getObjValAs? String "creationCode")
  let runtime ← IO.ofExcept (contracts[0]!.getObjValAs? String "runtimeCode")
  let vector (signature : String) (args expected : List String) (failure := false) := Json.mkObj
    [("signature", toJson signature), ("args", toJson args), ("expected", toJson expected), ("failure", toJson failure)]
  let replay (C : Contract) (rows : List ImportRow) (vectors : List Json) :=
    Tools.Upstream.replay C rows (Json.mkObj [("vectors", toJson vectors)])
  let staticVectors := [vector "nonempty()" [] [if wrong then "0" else "1"],
    vector "firstCreation()" [] [toString (hexNat (creation.take 2))],
    vector "firstRuntime()" [] [toString (hexNat (runtime.take 2))],
    vector "lastRuntime()" [] [toString (hexNat (runtime.drop (runtime.length - 2)))],
    vector "same()" [] ["1"], vector "storedLength()" [] [toString (runtime.length / 2)]]
  let enumVectors := [vector "initial()" [] ["1"], vector "set()" [] [], vector "packed()" [] [if wrong then "32" else "1"],
    vector "values()" [] ["42"], vector "localPacked()" [] ["1"],
    vector "arrayPacked()" [] ["1"], vector "wholeArrayPacked()" [] ["64"],
    vector "saved()" [] ["7"]]
  let mixedVectors := [vector "all()" [] [if wrong then "0" else "1"],
    vector "referenceFailureDespiteHole()" [] [] true,
    vector "saved()" [] ["4"], vector "unitsValue()" [] ["1000000000000000120"],
    vector "saved()" [] ["5"]]
  let identityVectors := [vector "good()" [] [if wrong then "0" else "1"],
    vector "packed()" [] ["1"], vector "own()" [] ["3"]]
  let results := if ir then [
    replay Imported.RemainingIR.StaticCodeConstants Imported.RemainingIR.StaticCodeConstants.report staticVectors,
    replay Imported.RemainingIR.EnumStructFields Imported.RemainingIR.EnumStructFields.report enumVectors,
    replay Imported.RemainingIR.MixedStorageResults Imported.RemainingIR.MixedStorageResults.report mixedVectors,
    replay Imported.RemainingIR.EnumIdentity Imported.RemainingIR.EnumIdentity.report identityVectors]
    else [
    replay Imported.Remaining.StaticCodeConstants Imported.Remaining.StaticCodeConstants.report staticVectors,
    replay Imported.Remaining.EnumStructFields Imported.Remaining.EnumStructFields.report enumVectors,
    replay Imported.Remaining.MixedStorageResults Imported.Remaining.MixedStorageResults.report mixedVectors,
    replay Imported.Remaining.EnumIdentity Imported.Remaining.EnumIdentity.report identityVectors]
  for (result, label) in results.zip ["static", "enum", "mixed", "enumIdentity"] do
    unless (result.getObjValAs? String "status").toOption == some (if wrong then "broken" else "working") do
      throw (IO.userError (label ++ ": " ++ result.pretty))

#eval check false false
#eval check true false
#eval check false true
#eval check true true

/-- Native panic controls do not claim the ABI panic code, which the upstream
replay adapter correctly refuses to infer from a generic model panic. -/
private def identityP := sol[Imported.Remaining.EnumIdentity]{ good(); invalidGlobal(); }
private def identityIRP := sol[Imported.RemainingIR.EnumIdentity]{ good(); invalidGlobal(); }
private def enumP := sol[Imported.Remaining.EnumStructFields]{ set(); invalid(9); }
private def enumIRP := sol[Imported.RemainingIR.EnumStructFields]{ set(); invalid(9); }
private def mixedP := sol[Imported.Remaining.MixedStorageResults]{ referenceFailureDespiteHole(); }
private def mixedIRP := sol[Imported.RemainingIR.MixedStorageResults]{ referenceFailureDespiteHole(); }

def isPanic {α : Type} : TRes α → Bool
  | .error .panic => true
  | _ => false

example : isPanic (identityP.run (State.init Imported.Remaining.EnumIdentity)) = true := by decide +kernel
example : isPanic (identityIRP.run (State.init Imported.RemainingIR.EnumIdentity)) = true := by decide +kernel
example : isPanic (enumP.run (State.init Imported.Remaining.EnumStructFields)) = true := by decide +kernel
example : isPanic (enumIRP.run (State.init Imported.RemainingIR.EnumStructFields)) = true := by decide +kernel
def isRevert {α : Type} : TRes α → Bool
  | .error .revert => true
  | _ => false

example : isRevert (Prog.runF 1000 mixedP (State.init Imported.Remaining.MixedStorageResults)) = true := by decide +kernel
example : isRevert (Prog.runF 1000 mixedIRP (State.init Imported.RemainingIR.MixedStorageResults)) = true := by decide +kernel

#guard (Semantics.structWidths ((Imported.Remaining.EnumStructFields.structName? "Record").getD "")).contains ("small", 8)
#guard (Semantics.structWidths ((Imported.RemainingIR.EnumStructFields.structName? "Record").getD "")).contains ("small", 8)
#guard Imported.Remaining.EnumDecodeRefusal.report.any fun row =>
  row.sourceName == "decode" && row.status == .unsupported &&
    (row.reason.splitOn "nominal cardinality checks").length > 1
#guard Imported.RemainingIR.EnumDecodeRefusal.report.any fun row =>
  row.sourceName == "decode" && row.status == .unsupported &&
    (row.reason.splitOn "nominal cardinality checks").length > 1

#guard Imported.Remaining.MixedReturnRefusal.report.any fun row =>
  row.sourceName == "selected" && row.status != .elaborated
#guard Imported.RemainingIR.MixedReturnRefusal.report.any fun row =>
  row.sourceName == "selected" && row.status != .elaborated

#guard [Imported.Remaining.EnumInputRefusal.report, Imported.RemainingIR.EnumInputRefusal.report].all fun rows =>
  ["direct", "records", "nested"].all fun name => rows.any fun row =>
    row.sourceName == name && row.status == .unsupported &&
      (row.reason.splitOn "recursive enum cardinality checks").length > 1
#guard [Imported.Remaining.EnumInputRefusal.report, Imported.RemainingIR.EnumInputRefusal.report].all fun rows =>
  ["scalar", "array"].all fun name => rows.any fun row =>
    row.sourceName == name && row.status == .elaborated
#guard Imported.Remaining.EnumInputRefusal.report.any fun row =>
  row.sourceName == "scalar" && row.paramRanges.contains ("value", 0, 1)
#guard Imported.Remaining.EnumInputRefusal.report.any fun row =>
  row.sourceName == "array" && row.elemRanges.contains ("values", 0, 1, none)

end Solidity.Upstream.RemainingDeclarations

