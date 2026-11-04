import Solidity.Backend.InternalFlow.RuntimeFrameV3NativeUnwind
import Solidity.Backend.AbiWorld.ReturnWordTransport

/-! Full-word ABI observation of the actual recovered native parent counter.
The native source call, target prefixes/unwind, represented caller, stack,
references and allocation relations are retained. The byte packet is a pure
observation of that represented word, not an unknown-memory runtime encoder.
The actual call has `.none` return binders: these are restored CALLER counter
bytes, not callee ABI return data. -/
namespace Solidity.Backend.AbiWorld.NativeParentWord
open Solidity Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
open RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes AllocatingEmission
abbrev A := NativeUnwind.A

def uintWord (n : Nat) (bound : n<Evm.W) : ReturnWordTransport.UInt :=
 ⟨n,by simpa only [AbiEntry.W_eq] using bound,decide_eq_true bound⟩

theorem represented_counter {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (base : Nat → Fin Evm.W) (machine : Machine)
 (k : Nat) (bound : k<Evm.W) (repr : StateRepr L b frame F σ base machine)
 (counter : σ.env.1=countValue k bound) :
 machine.mem (lvl b (.here : Idx (Parameters A) (.val .uint)))=.val (wmod k) := by
 have value := repr.core.vals (.here : Idx (Parameters A) (.val .uint))
 change ReprV .uint σ.env.1 (machine.mem (lvl b (.here : Idx (Parameters A) (.val .uint)))) at value
 rw [counter] at value
 obtain ⟨actual,range,number,cell⟩ := value.uint_inv
 have same : actual=k := by change (k : Int)=(actual : Int) at number; omega
 subst actual
 simpa only [wmod,Nat.mod_eq_of_lt bound] using cell

theorem encoded (k : Nat) (bound : k<Evm.W) :
 AbiEntry.encodeArgs (ReturnWordTransport.values [uintWord k bound])=AbiEntry.wordBytes k := by
 simp only [ReturnWordTransport.encoded_values,List.flatMap_cons,List.flatMap_nil,List.append_nil,uintWord]

theorem readback (k : Nat) (bound : k<Evm.W) (suffix : List UInt8) :
 ExternalReturnBytes.words 1 (AbiEntry.encodeArgs (ReturnWordTransport.values [uintWord k bound])++suffix)=
 .ok [ReturnWordTransport.semanticWord (uintWord k bound)] :=
 ReturnWordTransport.words_readback [uintWord k bound] suffix

theorem native_parent {C : Contract} {b lo L frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (base : Nat → Fin W) (before : Machine) (start : Nat)
 (suffix : List UInt8)
 (entry : InterfaceV1.Entry (plan b lo F) L b frame F σ base before start)
 (reads : (counter σ).val≤length σ) (n : Nat) (small : n+1≤(counter σ).val) :
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
 obtain ⟨ref,η,τ,ep,ef,entered,mid,down,last,prefixAddresses,addresses,out,alias,setup,prefixRun,prefixRepr,
  ancestorEnv,prefixSize,prefixKept,prefixExtended,prefixGrowth,descent,native,outputView,unwinding,
  represented,zeroEnv,size,kept,stack,extended,growth,cursor,reference⟩ :=
  NativeUnwind.parent σ base before start entry reads n small
 have restored : out.st.env.1=countValue (n+1) (Nat.lt_of_le_of_lt small (counter σ).isLt) := by
  rw [outputView]
  rfl
 refine ⟨ref,η,τ,ep,ef,entered,mid,down,last,prefixAddresses,addresses,out,alias,setup,prefixRun,prefixRepr,
  ancestorEnv,prefixSize,prefixKept,prefixExtended,prefixGrowth,descent,native,outputView,unwinding,
  represented,zeroEnv,size,kept,stack,extended,growth,cursor,reference,?_,encoded _ _,readback _ _ suffix⟩
 exact represented_counter out.st addresses last _ _ represented restored

end Solidity.Backend.AbiWorld.NativeParentWord
