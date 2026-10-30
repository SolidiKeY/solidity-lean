import SolidityBridge.ExternalEvm.Assembly.Driver
import SolidityBridge.ExternalEvm.Assembly.AutoChecks

namespace Solidity.Evm.External.Assembly.LinkedChecks
open EvmYul EvmYul.EVM

def destinations : List UInt256 := ([0, 1, 37, 72] : List Nat).map UInt256.ofNat

/-- A kernel-visible scan of actual opcodes, including both PUSH payload
skips. These are instruction boundaries, not occurrences of byte 0x5b. -/
def loopScan : ScanResult StackLoop.ambient (.ofNat 0) := ⟨destinations, by
  refine ScanPath.step _ .JUMPDEST ([1, 37, 72].map UInt256.ofNat) rfl ?_
  refine ScanPath.step _ .JUMPDEST ([37, 72].map UInt256.ofNat) rfl ?_
  refine ScanPath.step _ .ISZERO ([37, 72].map UInt256.ofNat) rfl ?_
  refine ScanPath.step _ (.Push .PUSH32) ([37, 72].map UInt256.ofNat) rfl ?_
  refine ScanPath.step _ .JUMPI ([37, 72].map UInt256.ofNat) rfl ?_
  refine ScanPath.step _ .JUMPDEST ([72].map UInt256.ofNat) rfl ?_
  refine ScanPath.step _ (.Push .PUSH32) ([72].map UInt256.ofNat) rfl ?_
  refine ScanPath.step _ .JUMP ([72].map UInt256.ofNat) rfl ?_
  refine ScanPath.step _ .JUMPDEST [] rfl ?_
  refine ScanPath.step _ .STOP [] rfl ?_
  exact ScanPath.stop _ rfl⟩

/-- The recursive safe certificate is produced by the checker. -/
def loopSafe : ScannedCode (StackLoop.initial []) destinations StackLoop.image :=
  ((certifyScannedCode StackLoop.image (StackLoop.initial []) destinations).get (by
    rw [certifyScannedCode.eq_def]
    simp only [checkLabels]
    dsimp only [StackLoop.code, List.length_cons, List.length_nil, collectFin, bind, Option.bind]
    simp only [Fin.getElem_fin, List.getElem_cons_zero]
    simp only [certifyScannedSite.eq_def]
    simp only [certifyScannedCode.eq_def, List.length_nil, collectFin, bind, Option.bind]
    simp only [assembleChild]
    decide +kernel)).down

def loopProgram : LinkedProgram StackLoop.code where
  base := 0
  frame := StackLoop.initial []
  checked := ⟨StackLoop.image, by unfold Placed; decide +kernel, loopSafe.decoded⟩
  scanner := loopScan
  scanned := loopSafe
  labels := loopSafe.labels
  refs := by
    intro n hn
    change n ∈ [0, 72] at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl
    · exact .head _
    · exact .tail _ (.tail _ (.tail _ (.head _)))

private def successful (result : Except ExecutionException (ExecutionResult EVM.State)) :
    Option (Nat × List Nat) := match result with
  | .ok (.success s _) => some (s.pc.toNat, s.stack.map UInt256.toNat)
  | _ => none

def input : EVM.State :=
  {(StackLoop.initial [.ofNat 1, .ofNat 2, .ofNat 0, .ofNat 9]) with gasAvailable := .ofNat 10000}

#guard successful (X 24 loopProgram.validJumps input) = some (73, [9])
example : successful (X 24 loopProgram.validJumps input) = some (73, [9]) := by decide +kernel
#guard (checkReady 21 24 loopProgram.validJumps input).isSome
/-- Actual driver readiness is inhabited, not merely postulated. -/
def ready : DriverReady 21 24 loopProgram.validJumps input :=
  ((checkReady 21 24 loopProgram.validJumps input).get (by decide +kernel)).down
example : run StackLoop.code {Machine.init with stack := [w[1], w[2], w[0], w[9]]} =
    .ok {Machine.init with stack := [w[9]]} 0 := by
  have h : (Instr.loop [] []).step {Machine.init with stack := [w[1], w[2], w[0], w[9]]} =
      .ok {Machine.init with stack := [w[9]]} 0 := loopRun_of_iterN (n := 3) rfl
  change ((Instr.loop [] []).step _).bind _ = _
  rw [h]
  rfl

#guard (linkChecked StackLoop.code [] [0x00] input).isSome
#guard (linkChecked ComposedBranch.code (List.replicate 5 0x00) [0x00] input).isSome
-- A PUSH immediate swallowing the entry is refused despite direct JD decode.
#guard (linkChecked [.push w[9]] [0x7f] [0x00] input).isNone
-- A complete, aligned PUSH prefix remains accepted.
#guard (linkChecked [.push w[9]] ([0x7f] ++ List.replicate 32 0x00) [0x00] input).isSome
#guard (linkChecked [.jump 1] [] [0x00] input).isNone
#guard (linkChecked [.sload] [] [0x00] input).isNone
#guard (certifyScannedCode StackLoop.image (StackLoop.initial []) []).isNone
private def nested : List Instr := [.loop [.push w[0]] [.loop [] []], .push w[9]]
#guard (linkChecked nested [] [0x00] input).isSome
#guard successful (X 24 #[] input) = none
#guard successful (X 1 loopProgram.validJumps input) = none
#guard successful (X 24 loopProgram.validJumps {input with gasAvailable := .ofNat 0}) = none

/-- Both the outer body and its nested loop execute; the inner loop consumes
one true and one false condition before the outer false condition. -/
private def nestedLive : List Instr := [.loop [] [.loop [] []], .push w[9]]
private def nestedProgram : Option (LinkedProgram nestedLive) :=
  linkChecked nestedLive [] [0x00] {input with stack := [.ofNat 1, .ofNat 1, .ofNat 0, .ofNat 0]}
#guard nestedProgram.isSome
#guard (nestedProgram.bind (fun p => successful (X 32 p.validJumps p.frame))) = some (179, [9])


/-- Paired core observation for the live nested target execution above. -/
example : run nestedLive {Machine.init with stack := [w[1], w[1], w[0], w[0]]} =
    .ok {Machine.init with stack := [w[9]]} 0 := by
  let start := {Machine.init with stack := [w[1], w[1], w[0], w[0]]}
  let innerStart := {Machine.init with stack := [w[1], w[0], w[0]]}
  let afterInner := {Machine.init with stack := [w[0]]}
  have inner : (Instr.loop [] []).step innerStart = .ok afterInner 0 :=
    loopRun_of_iterN (n := 2) rfl
  have body : run [Instr.loop [] []] innerStart = .ok afterInner 0 := by
    change ((Instr.loop [] []).step innerStart).bind _ = _
    rw [inner]
    rfl
  have first : loopTurn (run []) (run [Instr.loop [] []]) start = .inl afterInner := by
    change (match run [Instr.loop [] []] innerStart with
      | .ok m 0 => Sum.inl m
      | .ok _ (_ + 1) => Sum.inr Out.fault
      | r => .inr r) = _
    rw [body]
  have outer : (Instr.loop [] [Instr.loop [] []]).step start = .ok Machine.init 0 := by
    apply loopRun_of_iterN (n := 2)
    change (match loopTurn (run []) (run [Instr.loop [] []]) start with
      | .inl m => loopIterN (run []) (run [Instr.loop [] []]) 1 m
      | .inr r => .inr r) = _
    rw [first]
    rfl
  change ((Instr.loop [] [Instr.loop [] []]).step start).bind _ = _
  rw [outer]
  rfl

end Solidity.Evm.External.Assembly.LinkedChecks

/-- info: 'Solidity.Evm.External.Assembly.LinkedChecks.ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.LinkedChecks.ready
