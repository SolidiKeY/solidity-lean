import Lean
import Solidity.Frontend.NumericLiteralProofs.Controls

/-! # Typed observations for every fixed differential spelling fixture -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

structure FixtureObservation where
  id : String
  mode : String
  spelling : String
  lexOk : Bool
  numeric : Option NumLit
  numbers : List NumLit
  yul : Option Tok
  deriving Repr, DecidableEq

def fixture_row_control : FixtureObservation :=
  ⟨"witness", "sol", "0", true, some (.dec 0 0 0), [.dec 0 0 0], none⟩

-- BEGIN_FIXTURE_CASES
def fixtureCases : List (String × String × String) := [
  ("S00","sol","0"),
  ("S01","sol","1"),
  ("S02","sol","123456789012345678901234567890"),
  ("S03","sol","1_2_3"),
  ("S04","sol","0_1"),
  ("S05","sol","01"),
  ("S06","sol",".1"),
  ("S07","sol","1."),
  ("S08","sol","1.0"),
  ("S09","sol","1.0_2"),
  ("S10","sol","1e2"),
  ("S11","sol","1E2"),
  ("S12","sol","1e-2"),
  ("S13","sol","1e+2"),
  ("S14","sol","1e"),
  ("S15","sol","1e-"),
  ("S16","sol","1__2"),
  ("S17","sol","1_"),
  ("S18","sol","_1"),
  ("S19","sol","0x"),
  ("S20","sol","0X1"),
  ("S21","sol","0x1_2"),
  ("S22","sol","0x_1"),
  ("S23","sol","0x1__2"),
  ("S24","sol","0x1_"),
  ("S25","sol","0xAb"),
  ("S26","sol","0x0000000000000000000000000000000000000000"),
  ("S27","sol","1wei"),
  ("S28","sol","1 wei"),
  ("S29","sol","1/*x*/wei"),
  ("S30","sol","1uint8"),
  ("S31","sol","1 uint8"),
  ("Y00","yul","0"),
  ("Y01","yul","01"),
  ("Y02","yul","1_2"),
  ("Y03","yul","0x12"),
  ("Y04","yul","0x1_2"),
  ("Y05","yul","0x"),
  ("Y06","yul",".1"),
  ("Y07","yul","1e2"),
  ("S32","sol","0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAed"),
  ("S33","sol","0x5aaeb6053F3E94C9b9A09f33669435E7Ef1BeAed")
]
-- END_FIXTURE_CASES

def fixtureObservations : List FixtureObservation := fixtureCases.map fun (id, mode, spelling) =>
  let raw := ascii spelling
  let source := if mode == "yul" then "assembly { let x := " ++ spelling ++ " }" else spelling
  let out := tokens (ascii source)
  let numbers := match out with
    | .ok ls => ls.filterMap fun l => match l.tok with | .num n => some n | _ => none
    | .error _ => []
  ⟨id, mode, spelling, out.toOption.isSome,
    if mode == "sol" then (hexNumber raw).orElse (fun _ => decNumber raw) else none,
    numbers, if mode == "yul" then yulNumber raw else none⟩

def numericFixtureJson : Option NumLit → Lean.Json
  | none => .null
  | some (.dec m f e) => Lean.Json.mkObj [
      ("tag", Lean.toJson "dec"), ("mantissa", Lean.toJson m),
      ("fraction", Lean.toJson f), ("exponent", Lean.toJson e)]
  | some (.hex ds flag) => Lean.Json.mkObj [
      ("tag", Lean.toJson "hex"), ("digits", Lean.toJson (ds.map Fin.val)),
      ("flag", Lean.toJson flag)]

def yulFixtureJson : Option Tok → Lean.Json
  | none => .null
  | some (.yulDec n) => Lean.Json.mkObj [("tag", Lean.toJson "dec"), ("value", Lean.toJson n)]
  | some (.yulHex n) => Lean.Json.mkObj [("tag", Lean.toJson "hex"), ("value", Lean.toJson n)]
  | some t => Lean.Json.mkObj [("tag", Lean.toJson "unexpected"), ("token", Lean.toJson (reprStr t))]

def observationJson (row : FixtureObservation) : Lean.Json := Lean.Json.mkObj [
  ("id", Lean.toJson row.id), ("mode", Lean.toJson row.mode),
  ("spelling", Lean.toJson row.spelling), ("lexOk", Lean.toJson row.lexOk),
  ("numeric", numericFixtureJson row.numeric),
  ("numbers", Lean.Json.arr ((row.numbers.map (fun n => numericFixtureJson (some n))).toArray)),
  ("yul", yulFixtureJson row.yul)]

-- BEGIN_EXPECTED_FIXTURE_ROWS
def fixtureExpected : List FixtureObservation := [
  ⟨"S00", "sol", "0", true, some (.dec 0 0 (0)), [(.dec 0 0 (0))], none⟩,
  ⟨"S01", "sol", "1", true, some (.dec 1 0 (0)), [(.dec 1 0 (0))], none⟩,
  ⟨"S02", "sol", "123456789012345678901234567890", true, some (.dec 123456789012345678901234567890 0 (0)), [(.dec 123456789012345678901234567890 0 (0))], none⟩,
  ⟨"S03", "sol", "1_2_3", true, some (.dec 123 0 (0)), [(.dec 123 0 (0))], none⟩,
  ⟨"S04", "sol", "0_1", false, none, [], none⟩,
  ⟨"S05", "sol", "01", false, none, [], none⟩,
  ⟨"S06", "sol", ".1", true, some (.dec 1 1 (0)), [(.dec 1 1 (0))], none⟩,
  ⟨"S07", "sol", "1.", true, none, [(.dec 1 0 (0))], none⟩,
  ⟨"S08", "sol", "1.0", true, some (.dec 10 1 (0)), [(.dec 10 1 (0))], none⟩,
  ⟨"S09", "sol", "1.0_2", true, some (.dec 102 2 (0)), [(.dec 102 2 (0))], none⟩,
  ⟨"S10", "sol", "1e2", true, some (.dec 1 0 (2)), [(.dec 1 0 (2))], none⟩,
  ⟨"S11", "sol", "1E2", true, some (.dec 1 0 (2)), [(.dec 1 0 (2))], none⟩,
  ⟨"S12", "sol", "1e-2", true, some (.dec 1 0 (-2)), [(.dec 1 0 (-2))], none⟩,
  ⟨"S13", "sol", "1e+2", false, none, [], none⟩,
  ⟨"S14", "sol", "1e", false, none, [], none⟩,
  ⟨"S15", "sol", "1e-", false, none, [], none⟩,
  ⟨"S16", "sol", "1__2", false, none, [], none⟩,
  ⟨"S17", "sol", "1_", false, none, [], none⟩,
  ⟨"S18", "sol", "_1", true, none, [], none⟩,
  ⟨"S19", "sol", "0x", false, none, [], none⟩,
  ⟨"S20", "sol", "0X1", false, none, [], none⟩,
  ⟨"S21", "sol", "0x1_2", true, some (.hex [⟨1, by decide⟩, ⟨2, by decide⟩] false), [(.hex [⟨1, by decide⟩, ⟨2, by decide⟩] false)], none⟩,
  ⟨"S22", "sol", "0x_1", false, none, [], none⟩,
  ⟨"S23", "sol", "0x1__2", false, none, [], none⟩,
  ⟨"S24", "sol", "0x1_", false, none, [], none⟩,
  ⟨"S25", "sol", "0xAb", true, some (.hex [⟨10, by decide⟩, ⟨11, by decide⟩] false), [(.hex [⟨10, by decide⟩, ⟨11, by decide⟩] false)], none⟩,
  ⟨"S26", "sol", "0x0000000000000000000000000000000000000000", true, some (.hex [⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩] true), [(.hex [⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩] true)], none⟩,
  ⟨"S27", "sol", "1wei", false, none, [], none⟩,
  ⟨"S28", "sol", "1 wei", true, none, [(.dec 1 0 (0))], none⟩,
  ⟨"S29", "sol", "1/*x*/wei", true, none, [(.dec 1 0 (0))], none⟩,
  ⟨"S30", "sol", "1uint8", false, none, [], none⟩,
  ⟨"S31", "sol", "1 uint8", true, none, [(.dec 1 0 (0))], none⟩,
  ⟨"Y00", "yul", "0", true, none, [], some (.yulDec 0)⟩,
  ⟨"Y01", "yul", "01", false, none, [], none⟩,
  ⟨"Y02", "yul", "1_2", false, none, [], none⟩,
  ⟨"Y03", "yul", "0x12", true, none, [], some (.yulHex 18)⟩,
  ⟨"Y04", "yul", "0x1_2", false, none, [], none⟩,
  ⟨"Y05", "yul", "0x", false, none, [], none⟩,
  ⟨"Y06", "yul", ".1", true, none, [], none⟩,
  ⟨"Y07", "yul", "1e2", false, none, [], none⟩,
  ⟨"S32", "sol", "0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAed", true, some (.hex [⟨5, by decide⟩, ⟨10, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩, ⟨11, by decide⟩, ⟨6, by decide⟩, ⟨0, by decide⟩, ⟨5, by decide⟩, ⟨3, by decide⟩, ⟨15, by decide⟩, ⟨3, by decide⟩, ⟨14, by decide⟩, ⟨9, by decide⟩, ⟨4, by decide⟩, ⟨12, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨0, by decide⟩, ⟨9, by decide⟩, ⟨15, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨6, by decide⟩, ⟨9, by decide⟩, ⟨4, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨14, by decide⟩, ⟨7, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨1, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩, ⟨13, by decide⟩] true), [(.hex [⟨5, by decide⟩, ⟨10, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩, ⟨11, by decide⟩, ⟨6, by decide⟩, ⟨0, by decide⟩, ⟨5, by decide⟩, ⟨3, by decide⟩, ⟨15, by decide⟩, ⟨3, by decide⟩, ⟨14, by decide⟩, ⟨9, by decide⟩, ⟨4, by decide⟩, ⟨12, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨0, by decide⟩, ⟨9, by decide⟩, ⟨15, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨6, by decide⟩, ⟨9, by decide⟩, ⟨4, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨14, by decide⟩, ⟨7, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨1, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩, ⟨13, by decide⟩] true)], none⟩,
  ⟨"S33", "sol", "0x5aaeb6053F3E94C9b9A09f33669435E7Ef1BeAed", true, some (.hex [⟨5, by decide⟩, ⟨10, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩, ⟨11, by decide⟩, ⟨6, by decide⟩, ⟨0, by decide⟩, ⟨5, by decide⟩, ⟨3, by decide⟩, ⟨15, by decide⟩, ⟨3, by decide⟩, ⟨14, by decide⟩, ⟨9, by decide⟩, ⟨4, by decide⟩, ⟨12, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨0, by decide⟩, ⟨9, by decide⟩, ⟨15, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨6, by decide⟩, ⟨9, by decide⟩, ⟨4, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨14, by decide⟩, ⟨7, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨1, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩, ⟨13, by decide⟩] false), [(.hex [⟨5, by decide⟩, ⟨10, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩, ⟨11, by decide⟩, ⟨6, by decide⟩, ⟨0, by decide⟩, ⟨5, by decide⟩, ⟨3, by decide⟩, ⟨15, by decide⟩, ⟨3, by decide⟩, ⟨14, by decide⟩, ⟨9, by decide⟩, ⟨4, by decide⟩, ⟨12, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨0, by decide⟩, ⟨9, by decide⟩, ⟨15, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩, ⟨6, by decide⟩, ⟨9, by decide⟩, ⟨4, by decide⟩, ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨14, by decide⟩, ⟨7, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨1, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨10, by decide⟩, ⟨14, by decide⟩, ⟨13, by decide⟩] false)], none⟩
]

theorem fixture_observations_pass : fixtureObservations = fixtureExpected := by decide +kernel
-- END_EXPECTED_FIXTURE_ROWS

end Solidity.Frontend.NumericLiteralProofs

open Lean Elab Command in
run_cmd do
  let mut root := System.FilePath.mk (← getFileName)
  for _ in [:4] do root := root.parent.getD "."
  liftIO <| IO.FS.writeFile (root / "tests/sol-numeric-literals/evidence/lean-fixtures.actual.json")
    (Json.pretty (Json.arr ((Solidity.Frontend.NumericLiteralProofs.fixtureObservations.map
      Solidity.Frontend.NumericLiteralProofs.observationJson).toArray)))
  logInfo "numeric literal fixture observations exported"
