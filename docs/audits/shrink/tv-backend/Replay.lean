import Lean

/-! Explicit kernel timing, independent of root import timing. Every theorem
emitted by a selected module is checked again with its ORIGINAL type and proof
under a fresh name. Dependencies are the imported baseline environment, not
recursively rebuilt here. No proof search, evaluator shortcut or changed budget.
Usage: lake env lean -j1 -M12288 --run Replay.lean IMPORTS SELECTED OUTPUT EXPECTED_COUNT -/
open Lean

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let [importsFile, selectedFile, output, expectedText] := args | return 2
  let some expected := expectedText.toNat? | return 2
  let imports := (← IO.FS.lines importsFile).filter (· != "")
  let selected := (← IO.FS.lines selectedFile).foldl (fun (s : NameSet) n => s.insert n.toName) {}
  let env ← importModules (imports.map fun n => { module := n.toName }) {} 0
  let mut checked := 0
  let mut kernelNanos : Nat := 0
  let budget := (Core.getMaxHeartbeats {}).toUSize
  if env.contains `ShrinkPilotReplay.invalid then
    IO.eprintln "KERNEL_NEGATIVE_CONTROL_NAME_COLLISION"
    return 1
  let invalid : Declaration := .thmDecl {
    name := `ShrinkPilotReplay.invalid
    levelParams := []
    type := mkConst ``False
    value := mkConst ``True.intro }
  match env.addDeclCore budget invalid none true with
  | .ok _ =>
    IO.eprintln "KERNEL_NEGATIVE_CONTROL_FAIL"
    return 1
  | .error _ => pure ()
  let moduleNames := env.header.moduleNames
  let started ← IO.monoNanosNow
  if moduleNames.any selected.contains then
    for (name, ci) in env.constants.toList do
      let some index := env.getModuleIdxFor? name | continue
      unless selected.contains moduleNames[index]! do continue
      let .thmInfo theoremVal := ci | continue
      let fresh := Name.num `ShrinkPilotReplay checked
      let decl := Declaration.thmDecl { theoremVal with name := fresh }
      let before ← IO.monoNanosNow
      let result := env.addDeclCore budget decl none true
      match result with
      | .error ex =>
        IO.eprintln s!"KERNEL_REPLAY_FAIL {name}: {← ex.toMessageData {} |>.toString}"
        return 1
      | .ok _ => pure ()
      let after ← IO.monoNanosNow
      kernelNanos := kernelNanos + (after - before)
      checked := checked + 1
  let stopped ← IO.monoNanosNow
  unless checked == expected do
    IO.eprintln s!"KERNEL_REPLAY_COUNT_FAIL expected={expected} actual={checked}"
    return 1
  let record := Json.mkObj [("negative_control_rejected", toJson true), ("checked_theorems", toJson checked),
    ("kernel_call_nanoseconds", toJson kernelNanos),
    ("replay_loop_nanoseconds", toJson (stopped - started)),
    ("default_kernel_heartbeat_budget", toJson budget.toNat)]
  IO.FS.writeFile output (record.pretty ++ "\n")
  IO.println s!"KERNEL_REPLAY_PASS {checked} {kernelNanos}ns"
  return 0
