import SolidityBridge.ExternalEvm.Assembly.ResourceReady

namespace Solidity.Evm.External.Assembly.PopChecks
open EvmYul EvmYul.EVM

def code : List Instr := [.push w[1], .pop, .push w[9]]
def bytes : List UInt8 := [0x5b] ++ push32 ⟨1, by decide⟩ ++ [0x5b,0x50,0x5b] ++
  push32 ⟨9, by decide⟩ ++ [0x5b]
def image : Image code 0 where
  bytes := bytes
  size := 70
  span_eq := rfl
  emitted := by simp only [code, bytes, emit.eq_def, emitInstr.eq_def, width]; rfl
  length_eq := by decide +kernel
  fits := by decide
  destinations := by
    have hd : ∀ l : Label code, (address code 0 l).any (fun n => bytes[n]? == some 0x5b) = true := by decide +kernel
    intro l
    have hh := hd l
    cases ha : address code 0 l with
    | none => simp only [ha, Option.any_none, Bool.false_eq_true] at hh
    | some n =>
      refine ⟨n, rfl, ?_⟩
      simpa only [ha, Option.any_some, beq_iff_eq, Nat.sub_zero] using hh
  refs := []
  targets_eq := by simp only [code, targets.eq_def, instrTargets.eq_def, width]; rfl
  validRefs := by intro n hn; cases hn

def frame : EVM.State := {(default : EVM.State) with
  executionEnv := {(default : ExecutionEnv .EVM) with code := ⟨(bytes ++ [0x00]).toArray⟩}}
def certificate : DecodedCode frame image :=
  ((certifyAtoms image frame).get (by decide +kernel)).down

theorem sourceRun : run code Machine.init = .ok {Machine.init with stack := [w[9]]} 0 := rfl

theorem compiled : ∃ n t, fetchedSteps n frame = .ok t ∧
    Boundary image frame code.length {Machine.init with stack := [w[9]]} t :=
  certified_run_simulation image frame certificate _ _ frame ⟨by decide, rfl, rfl, rfl, rfl⟩ sourceRun

private def beforePop : EVM.State := {frame with pc := .ofNat 34, stack := [.ofNat 1]}
private def popSite : AtomicSite image frame 1 .pop := (checkAtom image frame 1 .pop).get (by decide +kernel)
example : ∃ n t, SafeTrace [] n beforePop t ∧ Boundary image frame 2 Machine.init t :=
  popSite.safe_refinement trivial {Machine.init with stack := [w[1]]} Machine.init 0 beforePop
    ⟨by decide, rfl, rfl, rfl, rfl⟩ rfl

#guard (fetchedSteps 6 frame).toOption.map (fun t => (t.pc.toNat, words t.stack)) = some (70, [w[9]])
#guard (match X 9 #[] {frame with gasAvailable := .ofNat 10000} with
  | .ok (.success out _) => some (out.pc.toNat, words out.stack)
  | _ => none) = some (71, [w[9]])

private def emptyPop : EVM.State := {(default : EVM.State) with
  executionEnv := {(default : ExecutionEnv .EVM) with code := ⟨#[0x5b,0x50,0x5b,0x00]⟩}}
example : Instr.pop.step Machine.init = .fault := rfl
example : fetchedSteps 2 emptyPop = .error .StackUnderflow := rfl
#guard (checkResources 2 5 {emptyPop with gasAvailable := .ofNat 10000}).isNone
#guard (match X 5 #[] {emptyPop with gasAvailable := .ofNat 10000} with
  | .error .StackUnderflow => true
  | _ => false)

end Solidity.Evm.External.Assembly.PopChecks
