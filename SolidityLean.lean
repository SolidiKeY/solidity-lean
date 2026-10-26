import Lean

/-! Native entry point. The source compiler and orchestration live beside the
checkout; proof search still runs through Lean's kernel-checked frontend. -/

private def findRoot (start : System.FilePath) : IO (Option System.FilePath) := do
  let mut dir := start
  for _ in [:10] do
    if ← (dir / "scripts" / "solidity-lean.mjs").pathExists then return some dir
    let some parent := dir.parent | return none
    dir := parent
  return none

def main (args : List String) : IO UInt32 := do
  try
    let root ← match ← IO.getEnv "SOLIDITY_LEAN_ROOT" with
      | some path => pure (System.FilePath.mk path)
      | none =>
        match ← findRoot ((← IO.appPath).parent.getD ".") with
        | some root => pure root
        | none =>
          let some root ← findRoot (← IO.currentDir)
            | throw <| IO.userError "runtime files not found; set SOLIDITY_LEAN_ROOT to the checkout"
          pure root
    let script := root / "scripts" / "solidity-lean.mjs"
    unless ← script.pathExists do
      throw <| IO.userError s!"runtime files not found at {root}"
    -- Inherit the caller's directory, so relative source paths keep their meaning.
    let child ← IO.Process.spawn { cmd := "node", args := #[script.toString] ++ args.toArray }
    return ← child.wait
  catch e =>
    IO.eprintln s!"solidity-lean: {e}"
    return (2 : UInt32)
