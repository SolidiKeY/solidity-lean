import SolidityBridge.PropertyChecks

private def parseArgs : List String → Plausible.Configuration → Except String Plausible.Configuration
  | [], cfg => .ok cfg
  | "--seed" :: n :: args, cfg => do
    let seed ← match n.toNat? with
      | some seed => .ok seed
      | none => .error "--seed needs a natural number"
    parseArgs args {cfg with randomSeed := some seed}
  | "--samples" :: n :: args, cfg => do
    let count ← match n.toNat? with
      | some count => .ok count
      | none => .error "--samples needs a positive natural number"
    if count = 0 then .error "--samples must be positive"
    else parseArgs args {cfg with numInst := count}
  | _, _ => .error "Usage: lake exe rulecheck [--seed N] [--samples N]"

def main (args : List String) : IO UInt32 := do
  match parseArgs args { numInst := 200, randomSeed := some 20261025 } with
  | .error msg => IO.eprintln msg; return 2
  | .ok cfg =>
    try
      Solidity.Bridge.PropertyChecks.runChecks cfg
      return 0
    catch e =>
      IO.eprintln s!"Plausible failed (seed {cfg.randomSeed}): {e}"
      return 1
