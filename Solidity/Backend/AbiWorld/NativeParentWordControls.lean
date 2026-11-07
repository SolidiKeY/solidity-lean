import Solidity.Backend.AbiWorld.NativeParentWord

/-! Native fixtures are applications of actual installed Entry/run proofs.
Printed packets are the codec bytes of the PROVED recovered counters; the
producer's chosen machines are noncomputable witnesses, not replayed here. -/
namespace Solidity.Backend.AbiWorld.NativeParentWordControls
open Solidity Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
open RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes AllocatingEmission
open NativeParentWord
abbrev A := NativeParentWord.A

theorem applied (n : Nat) (small : n+1≤2) (suffix : List UInt8) :
 let C := CountdownWitness.P.C
 let σ := CountdownWitness.callee
 let base := CountdownWitness.P.base
 let before := EmissionPrefixes.Checks.before
 let start := 10
 let b := 2
 let lo := 8
 let L := 1
 let frame := 16
 let F := CountdownWitness.F
 ∃ (ref : HRef σ.H A) (η τ : State C (Parameters A)) (ep : σ.H <+: η.H) (ef : σ.H <+: τ.H)
   (entered mid down last : Machine) (prefixAddresses addresses : Nat → Fin W)
   (out : Solidity.Out C (AllocatingActivation.allocated η).H (Parameters A)),
 TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref ∧
 run (RecursiveIngress.code lo (lo-1)) before=.ok entered 0 ∧
 loopIterN (run (guardCompiled (C:=C) b F).code) (run (AllocatingActivation.code (C:=C) b F lo))
   ((counter σ).val-(n+1)) entered=.inl mid ∧
 StateRepr L b frame F η prefixAddresses mid ∧
 η.env=(countValue (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt),(some (ref.wk ep),())) ∧
 η.H.length=σ.H.length+((counter σ).val-(n+1)) ∧ Heap.Keeps ep σ.heap η.heap ∧
 BaseExtends σ.H base prefixAddresses ∧
 GrowsAllocator b frame (4*((counter σ).val-(n+1))) σ base before η prefixAddresses mid ∧
 loopIterN (run (guardCompiled (C:=C) b F).code) (run (AllocatingActivation.code (C:=C) b F lo))
   (counter σ).val entered=.inl down ∧
 (.call "allocatingCountdown" (nextArgs A rfl) .none (AllocatingActivation.body (n+1)) :
   Stmt C (Parameters A) (Parameters A)).run (AllocatingActivation.allocated η)=.ok out ∧
 out.st=ParentPrefixes.sourceAt τ (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt) ∧
 loopIterN (run (PairedUnwind.condition lo (lo-1)))
   (run (Restore.restoreCells lo (Restore.contextCells b (Parameters A)))) (n+1) down=.inl last ∧
 StateRepr L b frame F out.st addresses last ∧
 τ.env=(countValue 0 W_pos,(some (ref.wk ef),())) ∧
 τ.H.length=σ.H.length+(counter σ).val ∧ Heap.Keeps ef σ.heap τ.heap ∧
 last.stack=before.stack ∧ BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (4*(counter σ).val) σ base before out.st addresses last ∧
 last.mem lo=.val (wmod (start+2*((counter σ).val-(n+1)))) ∧
 last.mem b=.val (base ref.id) ∧
 last.mem (lvl b (.here : Idx (Parameters A) (.val .uint)))=.val (wmod (n+1)) ∧
 AbiEntry.encodeArgs (ReturnWordTransport.values [uintWord (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt)])=AbiEntry.wordBytes (n+1) ∧
 ExternalReturnBytes.words 1
  (AbiEntry.encodeArgs (ReturnWordTransport.values [uintWord (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt)])++suffix)=
 .ok [ReturnWordTransport.semanticWord (uintWord (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt))] := by
 exact native_parent CountdownWitness.callee CountdownWitness.P.base EmissionPrefixes.Checks.before 10 suffix
  AllocatingEmission.Checks.entry
  (by rw [AllocatingEmission.Checks.counter_two,AllocatingEmission.Checks.length_two];decide) n
  (by rw [AllocatingEmission.Checks.counter_two];exact small)

theorem initial_nonempty :
 CountdownWitness.callee.H.length=2 ∧ EmissionPrefixes.Checks.before.stack=[w[77]] := by decide +kernel

theorem wrong_child_word :
 AbiEntry.encodeArgs (ReturnWordTransport.values [uintWord 1 (by decide +kernel)])≠
 AbiEntry.encodeArgs (ReturnWordTransport.values [uintWord 0 (by decide +kernel)]) := by decide +kernel

theorem wrong_initial_word :
 AbiEntry.encodeArgs (ReturnWordTransport.values [uintWord 1 (by decide +kernel)])≠
 AbiEntry.encodeArgs (ReturnWordTransport.values [uintWord 2 (by decide +kernel)]) := by decide +kernel

theorem truncated_parent :
 ExternalReturnBytes.words 1 ((AbiEntry.encodeArgs (ReturnWordTransport.values [uintWord 1 (by decide +kernel)])).take 31)=
 .error .revert := ReturnWordTransport.truncated [uintWord 1 (by decide +kernel)] (by intro impossible; cases impossible)

theorem suffix_readback :
 ExternalReturnBytes.words 1 (AbiEntry.encodeArgs (ReturnWordTransport.values [uintWord 2 (by decide +kernel)])++[0,255])=
 .ok [ReturnWordTransport.semanticWord (uintWord 2 (by decide +kernel))] := readback 2 (by decide +kernel) [0,255]

theorem slot_is_not_value (name : Evm.Slot) : Evm.Word.slot name≠Evm.Word.val (wmod 1) := by intro same; cases same

def packet (k : Nat) (bound : k<Evm.W) := AbiEntry.encodeArgs (ReturnWordTransport.values [uintWord k bound])
def render (bs : List UInt8) := "["++String.intercalate "," (bs.map (fun b=>toString b.toNat))++"]"
def row (k : Nat) (bound : k<Evm.W) := "{\"counter\":"++toString k++",\"bytes\":"++render (packet k bound)++"}"
#eval "NATIVE_PARENT_CODEC=["++row 1 (by decide +kernel)++","++row 2 (by decide +kernel)++"]"
#eval "NATIVE_WORD_CODEC_BOUNDARIES=["++String.intercalate "," [row 0 (by decide +kernel),row 300 (by decide +kernel),row (2^255) (by decide +kernel),row (2^256-1) (by decide +kernel)]++"]"
#check applied
#print axioms uintWord
#print axioms represented_counter
#print axioms encoded
#print axioms readback
#print axioms native_parent
#print axioms applied
#print axioms initial_nonempty
#print axioms wrong_child_word
#print axioms wrong_initial_word
#print axioms truncated_parent
#print axioms suffix_readback
#print axioms slot_is_not_value
end Solidity.Backend.AbiWorld.NativeParentWordControls
