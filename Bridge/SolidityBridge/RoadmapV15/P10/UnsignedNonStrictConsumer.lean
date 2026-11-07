import SolidityBridge.RoadmapV15.P10.UnsignedOrderConsumer
import SolidityBridge.RoadmapV15.P10.InequalityConsumer

/-! Actual fetched unsigned non-strict comparison sequences. Existing primitive
and typed source certificates remain read-only; compiler/frame origin is open. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def unsignedLeInput (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  {seed with
    executionEnv := {seed.executionEnv with
      code := ⟨(Backend.encode (before ++ [.op .GT,.op .ISZERO] ++ after)).toArray⟩}
    pc := UInt256.ofNat (Backend.encode before).length
    stack := (a::b::tail).map (fun w => UInt256.mk w.toFin)}
def unsignedLeCompared (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (unsignedLeInput seed before after a b tail) 3).replaceStackAndIncrPC
    ((Scalar.flag (decide (b.toNat < a.toNat))::tail).map (fun w => UInt256.mk w.toFin))
def unsignedLeOutput (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (unsignedLeCompared seed before after a b tail) 3).replaceStackAndIncrPC
    ((Scalar.flag (!(decide (b.toNat < a.toNat)))::tail).map (fun w => UInt256.mk w.toFin))

private theorem pc_one_le (n : Nat) : UInt256.ofNat n + UInt256.ofNat 1 = UInt256.ofNat (n+1) := by
  apply congrArg UInt256.mk
  apply Fin.ext
  exact (Nat.add_mod n 1 UInt256.size).symm

private theorem first_alignment_le (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) (fits : (Backend.encode before).length < UInt256.size) :
    (modularSite (⟨seed,before,.op .ISZERO::after,fits⟩ : Site .GT) (a::b::tail)).state =
      unsignedLeInput seed before after a b tail := by
  simp only [modularSite,Site.state,unsignedLeInput,List.append_assoc,List.cons_append,List.nil_append]

private theorem second_alignment_le (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op .GT])).length < UInt256.size) :
    (modularSite (⟨unsignedLeCompared seed before after a b tail,before ++ [.op .GT],after,fits⟩ :
      Site .ISZERO) (Scalar.flag (decide (b.toNat < a.toNat))::tail)).state = unsignedLeCompared seed before after a b tail := by
  simp only [modularSite,Site.state,unsignedLeCompared,unsignedLeInput,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,List.map_cons,List.append_assoc,List.cons_append,
    List.nil_append,Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Instr.encode,
    List.length_append,List.length_cons,List.length_nil,List.append_nil,pc_one_le,Nat.zero_add]

theorem unsigned_le_execution (valid : Array UInt256) (seed : EVM.State)
    (before after : Backend.Program) (a b : Scalar.Word) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op .GT])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Scalar.run [.op .GT,.op .ISZERO] (a::b::tail) = some (Scalar.flag (!(decide (b.toNat < a.toNat)))::tail) ∧
    Assembly.driverSteps 2 (fuel+3) valid (unsignedLeInput seed before after a b tail) =
      .ok (unsignedLeOutput seed before after a b tail) ∧
    EVM.X (fuel+3) valid (unsignedLeInput seed before after a b tail) =
      EVM.X (fuel+1) valid (unsignedLeOutput seed before after a b tail) := by
  have initialFits : (Backend.encode before).length < UInt256.size := by
    simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Instr.encode,
      List.length_append,List.length_cons,List.length_nil] at fits
    omega
  have first := unsigned_gt_agreement valid (⟨seed,before,.op .ISZERO::after,initialFits⟩)
    a b tail room (by change 3 ≤ seed.gasAvailable.toNat;omega) (fuel+1)
  dsimp only at first
  rw [first_alignment_le] at first
  have debit : (unsignedLeCompared seed before after a b tail).gasAvailable.toNat =
      seed.gasAvailable.toNat-3 := reference_gas_debit seed.gasAvailable 3 (by omega)
  have second := iszero_agreement valid
    (⟨unsignedLeCompared seed before after a b tail,before ++ [.op .GT],after,fits⟩)
    (Scalar.flag (decide (b.toNat < a.toNat))) tail (by omega)
    (by change 3 ≤ (unsignedLeCompared seed before after a b tail).gasAvailable.toNat;rw [debit];omega) fuel
  dsimp only at second
  rw [second_alignment_le,Scalar.flag_iszero] at second
  have firstDriver : Assembly.driverSteps 1 (fuel+3) valid (unsignedLeInput seed before after a b tail) =
      .ok (unsignedLeCompared seed before after a b tail) := first.2.1
  refine ⟨?_,?_,first.2.2.trans second.2.2⟩
  · change some (Scalar.flag (Scalar.flag (decide (b.toNat < a.toNat)) == 0)::tail) = _
    rw [Scalar.flag_iszero]
  · rw [fetched_steps_append 1 1 (fuel+1),firstDriver]
    exact second.2.1

/-- Actual typed certificate and native two-step result for the same operands. -/
theorem selected_unsigned_le_execution (valid : Array UInt256) (seed : EVM.State)
    (before after : Backend.Program) (a b : PrimTy.uint.Denote) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op .GT])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Scalar.run (Scalar.uintLe).code (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::tail) =
      (BinOp.le.evalT (p := .uint) rfl a b).map
        (fun result => Scalar.encodeValue .bool result::tail) ∧
    Assembly.driverSteps 2 (fuel+3) valid
      (unsignedLeInput seed before after (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail) =
      .ok (unsignedLeOutput seed before after (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail) ∧
    EVM.X (fuel+3) valid
      (unsignedLeInput seed before after (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail) =
      EVM.X (fuel+1) valid
        (unsignedLeOutput seed before after (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail) := by
  exact ⟨(Scalar.uintLe).correct a b tail,
    (unsigned_le_execution valid seed before after (Scalar.encodeValue .uint a)
      (Scalar.encodeValue .uint b) tail fits room gas fuel).2⟩

theorem unsigned_le_debit (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) (gas : 6 ≤ seed.gasAvailable.toNat) :
    (unsignedLeOutput seed before after a b tail).gasAvailable.toNat = seed.gasAvailable.toNat-6 := by
  have first := reference_gas_debit seed.gasAvailable 3 (by omega)
  have second := reference_gas_debit (seed.gasAvailable-UInt256.ofNat 3) 3 (by rw [first];omega)
  change ((seed.gasAvailable-UInt256.ofNat 3)-UInt256.ofNat 3).toNat = _
  rw [second,first,Nat.sub_sub]

theorem unsigned_le_frame (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) :
    (unsignedLeOutput seed before after a b tail).toState = (unsignedLeInput seed before after a b tail).toState ∧
    (unsignedLeOutput seed before after a b tail).memory = seed.memory ∧
    (unsignedLeOutput seed before after a b tail).returnData = seed.returnData ∧
    (unsignedLeOutput seed before after a b tail).H_return = seed.H_return ∧
    (unsignedLeOutput seed before after a b tail).stack =
      (Scalar.flag (!(decide (b.toNat < a.toNat)))::tail).map (fun w => UInt256.mk w.toFin) ∧
    (unsignedLeOutput seed before after a b tail).execLength = seed.execLength+2 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩


def unsignedGeInput (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  {seed with
    executionEnv := {seed.executionEnv with
      code := ⟨(Backend.encode (before ++ [.op .LT,.op .ISZERO] ++ after)).toArray⟩}
    pc := UInt256.ofNat (Backend.encode before).length
    stack := (a::b::tail).map (fun w => UInt256.mk w.toFin)}
def unsignedGeCompared (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (unsignedGeInput seed before after a b tail) 3).replaceStackAndIncrPC
    ((Scalar.flag (decide (a.toNat < b.toNat))::tail).map (fun w => UInt256.mk w.toFin))
def unsignedGeOutput (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (unsignedGeCompared seed before after a b tail) 3).replaceStackAndIncrPC
    ((Scalar.flag (!(decide (a.toNat < b.toNat)))::tail).map (fun w => UInt256.mk w.toFin))

private theorem pc_one_ge (n : Nat) : UInt256.ofNat n + UInt256.ofNat 1 = UInt256.ofNat (n+1) := by
  apply congrArg UInt256.mk
  apply Fin.ext
  exact (Nat.add_mod n 1 UInt256.size).symm

private theorem first_alignment_ge (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) (fits : (Backend.encode before).length < UInt256.size) :
    (modularSite (⟨seed,before,.op .ISZERO::after,fits⟩ : Site .LT) (a::b::tail)).state =
      unsignedGeInput seed before after a b tail := by
  simp only [modularSite,Site.state,unsignedGeInput,List.append_assoc,List.cons_append,List.nil_append]

private theorem second_alignment_ge (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op .LT])).length < UInt256.size) :
    (modularSite (⟨unsignedGeCompared seed before after a b tail,before ++ [.op .LT],after,fits⟩ :
      Site .ISZERO) (Scalar.flag (decide (a.toNat < b.toNat))::tail)).state = unsignedGeCompared seed before after a b tail := by
  simp only [modularSite,Site.state,unsignedGeCompared,unsignedGeInput,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,List.map_cons,List.append_assoc,List.cons_append,
    List.nil_append,Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Instr.encode,
    List.length_append,List.length_cons,List.length_nil,List.append_nil,pc_one_ge,Nat.zero_add]

theorem unsigned_ge_execution (valid : Array UInt256) (seed : EVM.State)
    (before after : Backend.Program) (a b : Scalar.Word) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op .LT])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Scalar.run [.op .LT,.op .ISZERO] (a::b::tail) = some (Scalar.flag (!(decide (a.toNat < b.toNat)))::tail) ∧
    Assembly.driverSteps 2 (fuel+3) valid (unsignedGeInput seed before after a b tail) =
      .ok (unsignedGeOutput seed before after a b tail) ∧
    EVM.X (fuel+3) valid (unsignedGeInput seed before after a b tail) =
      EVM.X (fuel+1) valid (unsignedGeOutput seed before after a b tail) := by
  have initialFits : (Backend.encode before).length < UInt256.size := by
    simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Instr.encode,
      List.length_append,List.length_cons,List.length_nil] at fits
    omega
  have first := unsigned_lt_agreement valid (⟨seed,before,.op .ISZERO::after,initialFits⟩)
    a b tail room (by change 3 ≤ seed.gasAvailable.toNat;omega) (fuel+1)
  dsimp only at first
  rw [first_alignment_ge] at first
  have debit : (unsignedGeCompared seed before after a b tail).gasAvailable.toNat =
      seed.gasAvailable.toNat-3 := reference_gas_debit seed.gasAvailable 3 (by omega)
  have second := iszero_agreement valid
    (⟨unsignedGeCompared seed before after a b tail,before ++ [.op .LT],after,fits⟩)
    (Scalar.flag (decide (a.toNat < b.toNat))) tail (by omega)
    (by change 3 ≤ (unsignedGeCompared seed before after a b tail).gasAvailable.toNat;rw [debit];omega) fuel
  dsimp only at second
  rw [second_alignment_ge,Scalar.flag_iszero] at second
  have firstDriver : Assembly.driverSteps 1 (fuel+3) valid (unsignedGeInput seed before after a b tail) =
      .ok (unsignedGeCompared seed before after a b tail) := first.2.1
  refine ⟨?_,?_,first.2.2.trans second.2.2⟩
  · change some (Scalar.flag (Scalar.flag (decide (a.toNat < b.toNat)) == 0)::tail) = _
    rw [Scalar.flag_iszero]
  · rw [fetched_steps_append 1 1 (fuel+1),firstDriver]
    exact second.2.1

/-- Actual typed certificate and native two-step result for the same operands. -/
theorem selected_unsigned_ge_execution (valid : Array UInt256) (seed : EVM.State)
    (before after : Backend.Program) (a b : PrimTy.uint.Denote) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op .LT])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Scalar.run (Scalar.uintGe).code (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::tail) =
      (BinOp.ge.evalT (p := .uint) rfl a b).map
        (fun result => Scalar.encodeValue .bool result::tail) ∧
    Assembly.driverSteps 2 (fuel+3) valid
      (unsignedGeInput seed before after (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail) =
      .ok (unsignedGeOutput seed before after (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail) ∧
    EVM.X (fuel+3) valid
      (unsignedGeInput seed before after (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail) =
      EVM.X (fuel+1) valid
        (unsignedGeOutput seed before after (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail) := by
  exact ⟨(Scalar.uintGe).correct a b tail,
    (unsigned_ge_execution valid seed before after (Scalar.encodeValue .uint a)
      (Scalar.encodeValue .uint b) tail fits room gas fuel).2⟩

theorem unsigned_ge_debit (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) (gas : 6 ≤ seed.gasAvailable.toNat) :
    (unsignedGeOutput seed before after a b tail).gasAvailable.toNat = seed.gasAvailable.toNat-6 := by
  have first := reference_gas_debit seed.gasAvailable 3 (by omega)
  have second := reference_gas_debit (seed.gasAvailable-UInt256.ofNat 3) 3 (by rw [first];omega)
  change ((seed.gasAvailable-UInt256.ofNat 3)-UInt256.ofNat 3).toNat = _
  rw [second,first,Nat.sub_sub]

theorem unsigned_ge_frame (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) :
    (unsignedGeOutput seed before after a b tail).toState = (unsignedGeInput seed before after a b tail).toState ∧
    (unsignedGeOutput seed before after a b tail).memory = seed.memory ∧
    (unsignedGeOutput seed before after a b tail).returnData = seed.returnData ∧
    (unsignedGeOutput seed before after a b tail).H_return = seed.H_return ∧
    (unsignedGeOutput seed before after a b tail).stack =
      (Scalar.flag (!(decide (a.toNat < b.toNat)))::tail).map (fun w => UInt256.mk w.toFin) ∧
    (unsignedGeOutput seed before after a b tail).execLength = seed.execLength+2 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩


#print axioms unsigned_le_execution
#print axioms selected_unsigned_le_execution
#print axioms unsigned_le_debit
#print axioms unsigned_le_frame
#print axioms unsigned_ge_execution
#print axioms selected_unsigned_ge_execution
#print axioms unsigned_ge_debit
#print axioms unsigned_ge_frame
end SolidityBridge.RoadmapV15.P10
