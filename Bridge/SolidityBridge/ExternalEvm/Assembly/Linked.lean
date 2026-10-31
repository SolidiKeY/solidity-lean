import SolidityBridge.ExternalEvm.Assembly.Scanned
import SolidityBridge.ExternalEvm.Assembly.Scanner
import SolidityBridge.ExternalEvm.Assembly.Placement

namespace Solidity.Evm.External.Assembly

/-- An assembled, placed, recursively decoded program with a certified
scanner walk and membership for every source boundary and nested jump target. -/
structure LinkedProgram (code : List Instr) where
  base : Nat
  frame : EvmYul.EVM.State
  checked : CheckedImage code base frame
  scanner : ScanResult frame.executionEnv.code (.ofNat 0)
  scanned : ScannedCode frame scanner.destinations checked.image
  labels : ∀ l : Label code, ∃ n, address code base l = some n ∧ .ofNat n ∈ scanner.destinations
  refs : ∀ n ∈ checked.image.refs, EvmYul.UInt256.ofNat n ∈ scanner.destinations

local instance : DecidableEq EvmYul.UInt256
  | ⟨a⟩, ⟨b⟩ => if h : a = b then .isTrue (congrArg EvmYul.UInt256.mk h)
    else .isFalse (fun he => h (congrArg EvmYul.UInt256.val he))

local instance : LawfulBEq EvmYul.UInt256 where
  rfl {a} := by
    cases a with
    | mk a => change (a == a) = true; exact BEq.rfl
  eq_of_beq {a b} h := by
    cases a with
    | mk a =>
      cases b with
      | mk b =>
        apply congrArg EvmYul.UInt256.mk
        change (a == b) = true at h
        exact eq_of_beq h

/-- Link actual bytecode, refusing prefixes or relocations that hide a
required boundary (for example inside a preceding PUSH immediate). -/
def linkChecked (code : List Instr) (pre suffix : List UInt8) (template : EvmYul.EVM.State) :
    Option (LinkedProgram code) := do
  let image ← assemble code pre.length
  let frame : EvmYul.EVM.State := {template with
    pc := .ofNat pre.length
    executionEnv := {template.executionEnv with code := ⟨(pre ++ image.bytes ++ suffix).toArray⟩}}
  if hp : (frame.executionEnv.code.data.toList.drop pre.length).take image.bytes.length = image.bytes then
    let scanner ← scanCode frame.executionEnv.code
    let certificate ← certifyScannedCode image frame scanner.destinations
    if hl : ∀ l : Label code, (address code pre.length l).any
        (fun n => decide (EvmYul.UInt256.ofNat n ∈ scanner.destinations)) = true then
      if hr : ∀ n ∈ image.refs, EvmYul.UInt256.ofNat n ∈ scanner.destinations then
        return ⟨pre.length, frame, ⟨image, hp, certificate.down.decoded⟩, scanner, certificate.down, fun l => by
          have hh := hl l
          cases ha : address code pre.length l with
          | none => simp only [ha, Option.any_none, Bool.false_eq_true] at hh
          | some n =>
            refine ⟨n, rfl, ?_⟩
            simpa only [ha, Option.any_some, decide_eq_true_eq] using hh, hr⟩
      else none
    else none
  else none

/-- Every source boundary is both directly decoded and recognized along a
certified full-code scanner path, with an exact nonwrapping word PC. -/
theorem LinkedProgram.destination {code : List Instr} (program : LinkedProgram code)
    (l : Label code) : ∃ n : Fin W,
      address code program.base l = some n.val ∧
      EvmYul.UInt256.ofNat n.val ∈ program.scanner.destinations ∧
      EvmYul.EVM.decode program.frame.executionEnv.code (.ofNat n.val) = some (.JUMPDEST, none) := by
  obtain ⟨n, ha, hd⟩ := program.checked.image.decoded_destination program.frame program.checked.placement l
  obtain ⟨v, hv, hm⟩ := program.labels l
  have he : v = n.val := Option.some.inj (hv.symm.trans ha)
  subst v
  exact ⟨n, ha, hm, hd⟩

/-- Includes loop entry/exit and branch targets inside nested condition/body
images, not just the outer source labels. -/
theorem LinkedProgram.reference {code : List Instr} (program : LinkedProgram code)
    (n : Nat) (hn : n ∈ program.checked.image.refs) :
    (EvmYul.UInt256.ofNat n).toNat = n ∧
    EvmYul.UInt256.ofNat n ∈ program.scanner.destinations ∧
    EvmYul.EVM.decode program.frame.executionEnv.code (.ofNat n) = some (.JUMPDEST, none) := by
  have hf := program.checked.image.validRefs n hn
  have hm := program.refs n hn
  exact ⟨word_nat n hf.2.1, hm, program.scanner.valid _ hm⟩

/-- The exact certified destination array supplied to the upstream driver.
Equality to opaque D_J is not silently assumed. -/
def LinkedProgram.validJumps {code : List Instr} (program : LinkedProgram code) : Array EvmYul.UInt256 :=
  program.scanner.destinations.toArray

theorem LinkedProgram.simulation {code : List Instr} (program : LinkedProgram code)
    (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : Boundary program.checked.image program.frame 0 m s) (source : run code m = .ok m' 0) :
    ∃ n t, fetchedSteps n s = .ok t ∧ Boundary program.checked.image program.frame code.length m' t ∧
      Placed program.checked.image t := by
  obtain ⟨n, t, ht, he⟩ := program.checked.simulation m m' s entry source
  exact ⟨n, t, ht, he, he.placed program.checked.placement⟩

end Solidity.Evm.External.Assembly
