import SolidityBridge.ExternalEvm.Assembly.Control
import SolidityBridge.ExternalEvm.Assembly.Loop

/-! Actual fetched upstream observations for inhabited, assembled inputs.
The number of dispatcher steps is the exact emitted path length. This is
neither an increased semantic fuel budget nor a driver-halting theorem. -/
namespace Solidity.Evm.External.Assembly

private def initial (bytes : List UInt8) : EvmYul.EVM.State :=
  { (default : EvmYul.EVM.State) with
    pc := .ofNat 0
    stack := []
    executionEnv := {(default : EvmYul.ExecutionEnv .EVM) with code := ⟨bytes.toArray⟩} }

private def steps : Nat → EvmYul.EVM.State →
    Except EvmYul.EVM.ExecutionException EvmYul.EVM.State
  | 0, s => .ok s
  | n + 1, s => do
    let t ← EvmYul.EVM.step 1 0 none s
    steps n t

private def observe : Except EvmYul.EVM.ExecutionException EvmYul.EVM.State →
    Option (Nat × List Nat)
  | .ok s => some (s.pc.toNat, s.stack.map EvmYul.UInt256.toNat)
  | .error _ => none

private def assembledRun (code : List Instr) (n : Nat) : Option (Nat × List Nat) := do
  let image ← assemble code 0
  observe (steps n (initial image.bytes))

#guard assembledRun [.push w[1], .jumpi 1, .push w[7], .push w[9]] 8 = some (138, [9])
#guard assembledRun [.push w[0], .jumpi 1, .push w[7], .push w[9]] 10 = some (138, [9, 7])
#guard assembledRun [.jump 1, .push w[7], .push w[9]] 6 = some (104, [9])
#guard assembledRun [.loop [.push w[0]] []] 8 = some (107, [])
#guard assembledRun [.push (.val wMax)] 3 = some (35, [W - 1])
-- One real back edge, not termination: the PC and stack return to the header.
#guard assembledRun [.loop [.push w[1]] []] 10 = some (0, [])
#guard assembledRun [.jumpi 0] 3 = none
#guard assembledRun [.jump 1] 3 = none

-- An inhabited instance of the general fetched-code theorem, rather than
-- only sampled agreement. The final byte really decodes as JUMPDEST.
private def jumpBytes : List UInt8 := push32 ⟨34, by decide⟩ ++ [0x56, 0x5b]

example : FetchedTrace 0 (initial jumpBytes)
    (jumpState (initial jumpBytes) (.ofNat 34)) := by
  apply fetched_jump_trace
  · rfl
  · rfl

example : EvmYul.EVM.decode ⟨jumpBytes.toArray⟩ (.ofNat 34) =
    some (.JUMPDEST, none) := rfl

private def isBadJump : Except EvmYul.EVM.ExecutionException
    (EvmYul.EVM.ExecutionResult EvmYul.EVM.State) → Bool
  | .error .BadJumpDestination => true
  | _ => false

private def isSuccess : Except EvmYul.EVM.ExecutionException
    (EvmYul.EVM.ExecutionResult EvmYul.EVM.State) → Bool
  | .ok (.success _ _) => true
  | _ => false

-- Actual driver controls: invalid targets reject only taken jumps.
#guard isBadJump (EvmYul.EVM.X 2 #[]
  {(initial [0x56]) with stack := [.ofNat 99], gasAvailable := .ofNat 10000})
#guard isBadJump (EvmYul.EVM.X 2 #[]
  {(initial [0x57]) with stack := [.ofNat 99, .ofNat 1], gasAvailable := .ofNat 10000})
#guard isSuccess (EvmYul.EVM.X 3 #[]
  {(initial [0x57, 0x00]) with stack := [.ofNat 99, .ofNat 0], gasAvailable := .ofNat 10000})

example : run [.push (.val wMax)] Machine.init =
    .ok {Machine.init with stack := [.val wMax]} 0 := rfl

-- Paired source outcomes for the positive compiled observations above.
example : run [.push w[1], .jumpi 1, .push w[7], .push w[9]] Machine.init =
    .ok {Machine.init with stack := [w[9]]} 0 := rfl
example : run [.push w[0], .jumpi 1, .push w[7], .push w[9]] Machine.init =
    .ok {Machine.init with stack := [w[9], w[7]]} 0 := rfl
example : run [.jump 1, .push w[7], .push w[9]] Machine.init =
    .ok {Machine.init with stack := [w[9]]} 0 := rfl
example : (Instr.loop [.push w[0]] []).step Machine.init = .ok Machine.init 0 := by
  exact loopRun_of_iterN (n := 1) rfl

-- The core classifies an infinite loop as fault; the target observation
-- above is one back edge, not an assertion that its driver returns fault.
example (m : Machine) : (Instr.loop [.push w[1]] []).step m = .fault := by
  apply loopRun_of_forall
  intro n
  refine ⟨m, ?_⟩
  induction n with
  | zero => rfl
  | succ n ih => exact ih

end Solidity.Evm.External.Assembly

/-- info: 'Solidity.Evm.External.Assembly.jumpMacro_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.jumpMacro_eq
/-- info: 'Solidity.Evm.External.Assembly.jumpiMacro_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.jumpiMacro_eq
/-- info: 'Solidity.Evm.External.Assembly.fetched_jump_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.fetched_jump_trace
/-- info: 'Solidity.Evm.External.Assembly.sequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.sequence

/-- info: 'Solidity.Evm.External.Assembly.trueLoop_emitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.trueLoop_emitted
/-- info: 'Solidity.Evm.External.Assembly.trueLoop_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.trueLoop_cycle
/-- info: 'Solidity.Evm.External.Assembly.trueLoop_prefixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.trueLoop_prefixes
/-- info: 'Solidity.Evm.External.Assembly.trueLoop_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.trueLoop_core
