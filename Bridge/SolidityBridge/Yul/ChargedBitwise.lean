import SolidityBridge.Yul.QuotientPlacement
import SolidityBridge.RoadmapV15.P10.BitwiseConsumer
import Solidity.Yul.Compilation.BitMachineExecution
/-! Actual compiler-origin bitwise sites consuming P10's charged three-gas
steps. Prefix reachability/execution, scanner certificates, Source/G24 and
whole-program Osaka/world/resource closure remain separate. -/
namespace SolidityBridge.Yul.ChargedBitwise
open Solidity Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation
open Backend Scalar Solidity.Evm.External EvmYul
open SolidityBridge.RoadmapV15

variable (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length+3<UInt256.size)

def input (seed : EVM.State) (op : Backend.Op) (a b : Scalar.Word)
    (caller : Scalar.Stack) : EVM.State :=
  (P10.modularSite (QuotientPlacement.arithmeticSite headCode tailCode fits seed op)
    (ChargedQuotients.packet a b caller)).state

def after (seed : EVM.State) (op : Backend.Op) (value a b : Scalar.Word)
    (caller : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (input headCode tailCode fits seed op a b caller) 3).replaceStackAndIncrPC
    ((value::a::b::caller).map (fun w => UInt256.mk w.toFin))


/-- Actual ordered image of the source compiler's emitted program, at a byte
PC rather than an instruction-count offset. No decoder result is assumed. -/
theorem and_image (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack) :
    (input headCode tailCode fits seed .AND a b caller).executionEnv.code.data.toList =
      Backend.encode (headCode ++ BitMachineExecution.andProgram ++ tailCode) := by
  have actual := P10.Site.code_bytes (P10.modularSite
    (QuotientPlacement.arithmeticSite headCode tailCode fits seed .AND)
    (ChargedQuotients.packet a b caller))
  simpa only [input,QuotientPlacement.arithmeticSite,P10.modularSite,
    BitMachineExecution.andProgram,BitMachineExecution.reads,ChargedQuotients.reads,
    List.append_assoc,List.cons_append,List.nil_append] using actual

/-- Actual ordered image of the source compiler's emitted program, at a byte
PC rather than an instruction-count offset. No decoder result is assumed. -/
theorem or_image (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack) :
    (input headCode tailCode fits seed .OR a b caller).executionEnv.code.data.toList =
      Backend.encode (headCode ++ BitMachineExecution.orProgram ++ tailCode) := by
  have actual := P10.Site.code_bytes (P10.modularSite
    (QuotientPlacement.arithmeticSite headCode tailCode fits seed .OR)
    (ChargedQuotients.packet a b caller))
  simpa only [input,QuotientPlacement.arithmeticSite,P10.modularSite,
    BitMachineExecution.orProgram,BitMachineExecution.reads,ChargedQuotients.reads,
    List.append_assoc,List.cons_append,List.nil_append] using actual

/-- Actual ordered image of the source compiler's emitted program, at a byte
PC rather than an instruction-count offset. No decoder result is assumed. -/
theorem xor_image (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack) :
    (input headCode tailCode fits seed .XOR a b caller).executionEnv.code.data.toList =
      Backend.encode (headCode ++ BitMachineExecution.xorProgram ++ tailCode) := by
  have actual := P10.Site.code_bytes (P10.modularSite
    (QuotientPlacement.arithmeticSite headCode tailCode fits seed .XOR)
    (ChargedQuotients.packet a b caller))
  simpa only [input,QuotientPlacement.arithmeticSite,P10.modularSite,
    BitMachineExecution.xorProgram,BitMachineExecution.reads,ChargedQuotients.reads,
    List.append_assoc,List.cons_append,List.nil_append] using actual


/-- Actual source horizon, emitted code image and charged arithmetic-site step.
The DUP prefix's reachability/execution is NOT a conclusion of this theorem.
Only the real three-gas primitive is charged here; caller capacity is explicit. -/
theorem and_correspondence (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1020) (gas : 3≤seed.gasAvailable.toNat) (fuel : Nat) :
    BitMachineExecution.andCompiled.lowered.code 0 = some BitMachineExecution.andProgram ∧
    evalExpr 2 .nil True.intro BitMachineExecution.andExpr BitMachineExecution.andCompiled.profile
      (ProducerExpressions.sourceLocals #v[a,b]) =
      some (fun _ => (BitMachineExecution.andCompiled.value #v[a,b]).toFin) ∧
    (input headCode tailCode fits seed .AND a b caller).executionEnv.code.data.toList =
      Backend.encode (headCode ++ BitMachineExecution.andProgram ++ tailCode) ∧
    Assembly.driverSteps 1 (fuel+2) #[] (input headCode tailCode fits seed .AND a b caller) =
      .ok (after headCode tailCode fits seed .AND (BitMachineExecution.andCompiled.value #v[a,b]) a b caller) ∧
    EVM.X (fuel+2) #[] (input headCode tailCode fits seed .AND a b caller) =
      EVM.X (fuel+1) #[] (after headCode tailCode fits seed .AND (BitMachineExecution.andCompiled.value #v[a,b]) a b caller) := by
  refine ⟨BitMachineExecution.and_origin,BitMachineExecution.andCompiled.source #v[a,b],
    and_image headCode tailCode fits seed a b caller,?_⟩
  exact (P10.bitwise_and_agreement
    (QuotientPlacement.arithmeticSite headCode tailCode fits seed .AND)
    a b (a::b::caller) (by simp only [List.length_cons];omega) gas fuel).2
#print axioms and_correspondence

/-- Actual source horizon, emitted code image and charged arithmetic-site step.
The DUP prefix's reachability/execution is NOT a conclusion of this theorem.
Only the real three-gas primitive is charged here; caller capacity is explicit. -/
theorem or_correspondence (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1020) (gas : 3≤seed.gasAvailable.toNat) (fuel : Nat) :
    BitMachineExecution.orCompiled.lowered.code 0 = some BitMachineExecution.orProgram ∧
    evalExpr 2 .nil True.intro BitMachineExecution.orExpr BitMachineExecution.orCompiled.profile
      (ProducerExpressions.sourceLocals #v[a,b]) =
      some (fun _ => (BitMachineExecution.orCompiled.value #v[a,b]).toFin) ∧
    (input headCode tailCode fits seed .OR a b caller).executionEnv.code.data.toList =
      Backend.encode (headCode ++ BitMachineExecution.orProgram ++ tailCode) ∧
    Assembly.driverSteps 1 (fuel+2) #[] (input headCode tailCode fits seed .OR a b caller) =
      .ok (after headCode tailCode fits seed .OR (BitMachineExecution.orCompiled.value #v[a,b]) a b caller) ∧
    EVM.X (fuel+2) #[] (input headCode tailCode fits seed .OR a b caller) =
      EVM.X (fuel+1) #[] (after headCode tailCode fits seed .OR (BitMachineExecution.orCompiled.value #v[a,b]) a b caller) := by
  refine ⟨BitMachineExecution.or_origin,BitMachineExecution.orCompiled.source #v[a,b],
    or_image headCode tailCode fits seed a b caller,?_⟩
  exact (P10.bitwise_or_agreement
    (QuotientPlacement.arithmeticSite headCode tailCode fits seed .OR)
    a b (a::b::caller) (by simp only [List.length_cons];omega) gas fuel).2
#print axioms or_correspondence

/-- Actual source horizon, emitted code image and charged arithmetic-site step.
The DUP prefix's reachability/execution is NOT a conclusion of this theorem.
Only the real three-gas primitive is charged here; caller capacity is explicit. -/
theorem xor_correspondence (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1020) (gas : 3≤seed.gasAvailable.toNat) (fuel : Nat) :
    BitMachineExecution.xorCompiled.lowered.code 0 = some BitMachineExecution.xorProgram ∧
    evalExpr 2 .nil True.intro BitMachineExecution.xorExpr BitMachineExecution.xorCompiled.profile
      (ProducerExpressions.sourceLocals #v[a,b]) =
      some (fun _ => (BitMachineExecution.xorCompiled.value #v[a,b]).toFin) ∧
    (input headCode tailCode fits seed .XOR a b caller).executionEnv.code.data.toList =
      Backend.encode (headCode ++ BitMachineExecution.xorProgram ++ tailCode) ∧
    Assembly.driverSteps 1 (fuel+2) #[] (input headCode tailCode fits seed .XOR a b caller) =
      .ok (after headCode tailCode fits seed .XOR (BitMachineExecution.xorCompiled.value #v[a,b]) a b caller) ∧
    EVM.X (fuel+2) #[] (input headCode tailCode fits seed .XOR a b caller) =
      EVM.X (fuel+1) #[] (after headCode tailCode fits seed .XOR (BitMachineExecution.xorCompiled.value #v[a,b]) a b caller) := by
  refine ⟨BitMachineExecution.xor_origin,BitMachineExecution.xorCompiled.source #v[a,b],
    xor_image headCode tailCode fits seed a b caller,?_⟩
  exact (P10.bitwise_xor_agreement
    (QuotientPlacement.arithmeticSite headCode tailCode fits seed .XOR)
    a b (a::b::caller) (by simp only [List.length_cons];omega) gas fuel).2
#print axioms xor_correspondence
end SolidityBridge.Yul.ChargedBitwise
