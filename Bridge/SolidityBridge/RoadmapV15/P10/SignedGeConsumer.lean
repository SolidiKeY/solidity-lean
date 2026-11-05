import SolidityBridge.RoadmapV15.P10.SignedLeWord
import SolidityBridge.RoadmapV15.P10.InequalityConsumer

/-! General fetched signed LT and the actual intGe SLT/ISZERO sequence.
Reserved signed-word mathematics and typed certificates are consumed read-only. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem signed_lt_word (a b : Scalar.Word) :
    UInt256.slt ⟨a.toFin⟩ ⟨b.toFin⟩ = ⟨(Scalar.flag (decide (a.toInt < b.toInt))).toFin⟩ := by
  have ha : Solidity.Evm.sgn a.toFin.val = a.toInt := Scalar.signedOf_word a
  have hb : Solidity.Evm.sgn b.toFin.val = b.toInt := Scalar.signedOf_word b
  have encoded (x : Scalar.Word) : encode x.toFin = UInt256.mk x.toFin := by
    apply congrArg UInt256.mk
    apply Fin.ext
    rfl
  rw [UInt256.slt,←encoded a,←encoded b,←signed_lt_bool a.toFin b.toFin,ha,hb]
  cases h : decide (a.toInt < b.toInt) <;> rfl

private theorem signed_lt_gate (valid : Array UInt256) (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (enough : 2 ≤ s.stack.length)
    (room : s.stack.length-2+1 ≤ 1024) :
    Assembly.driverGate valid s .SLT = .ok (s,3) := by
  have expansion : EVM.memoryExpansionCost s .SLT = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  change (if s.gasAvailable.toNat < 3 then _ else _) = _
  rw [if_neg (Nat.not_lt_of_ge gas)]
  simp only [EVM.δ,EVM.α,Option.getD_some,if_neg (Nat.not_lt_of_ge enough),
    if_neg (Nat.not_lt_of_ge room)]
  cases s.executionEnv.perm <;> rfl

/-- Actual fetched SLT, preserving the complete charged State and continuation. -/
theorem signed_lt_agreement (valid : Array UInt256) (site : Site .SLT)
    (a b : Scalar.Word) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (((Scalar.flag (decide (a.toInt < b.toInt)))::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .SLT) (a::b::tail) = some ((Scalar.flag (decide (a.toInt < b.toInt)))::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate valid input .SLT = .ok (input,3) := by
    apply signed_lt_gate valid input gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 3 (some (.SLT,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        (((Scalar.flag (decide (a.toInt < b.toInt)))::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := signed_lt_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.SLT,none) :=
    DecoderAgreement.decode_all (modularSite site (a::b::tail))
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel valid input input _ (.SLT,none) 3 decoded gate step
      (by unfold Assembly.NonhaltingOpcode;decide)


theorem selected_signed_lt_agreement (valid : Array UInt256) (site : Site .SLT)
    (a b : PrimTy.int.Denote) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let aw := Scalar.encodeValue .int a
    let bw := Scalar.encodeValue .int b
    let input := (modularSite site (aw::bw::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((Scalar.flag (decide (aw.toInt < bw.toInt))::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.run (Scalar.intLt).code (aw::bw::tail) =
      (BinOp.lt.evalT (p := .int) rfl a b).map
        (fun result => Scalar.encodeValue .bool result::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  exact ⟨(Scalar.intLt).correct a b tail,
    (signed_lt_agreement valid site (Scalar.encodeValue .int a) (Scalar.encodeValue .int b)
      tail room gas fuel).2⟩



def signedGeInput (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  {seed with
    executionEnv := {seed.executionEnv with
      code := ⟨(Backend.encode (before ++ [.op .SLT,.op .ISZERO] ++ after)).toArray⟩}
    pc := UInt256.ofNat (Backend.encode before).length
    stack := (a::b::tail).map (fun w => UInt256.mk w.toFin)}
def signedGeCompared (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (signedGeInput seed before after a b tail) 3).replaceStackAndIncrPC
    ((Scalar.flag (decide (a.toInt < b.toInt))::tail).map (fun w => UInt256.mk w.toFin))
def signedGeOutput (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (signedGeCompared seed before after a b tail) 3).replaceStackAndIncrPC
    ((Scalar.flag (!(decide (a.toInt < b.toInt)))::tail).map (fun w => UInt256.mk w.toFin))

private theorem pc_one_ge (n : Nat) : UInt256.ofNat n + UInt256.ofNat 1 = UInt256.ofNat (n+1) := by
  apply congrArg UInt256.mk
  apply Fin.ext
  exact (Nat.add_mod n 1 UInt256.size).symm

private theorem first_alignment_ge (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) (fits : (Backend.encode before).length < UInt256.size) :
    (modularSite (⟨seed,before,.op .ISZERO::after,fits⟩ : Site .SLT) (a::b::tail)).state =
      signedGeInput seed before after a b tail := by
  simp only [modularSite,Site.state,signedGeInput,List.append_assoc,List.cons_append,List.nil_append]

private theorem second_alignment_ge (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op .SLT])).length < UInt256.size) :
    (modularSite (⟨signedGeCompared seed before after a b tail,before ++ [.op .SLT],after,fits⟩ :
      Site .ISZERO) (Scalar.flag (decide (a.toInt < b.toInt))::tail)).state = signedGeCompared seed before after a b tail := by
  simp only [modularSite,Site.state,signedGeCompared,signedGeInput,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,List.map_cons,List.append_assoc,List.cons_append,
    List.nil_append,Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Instr.encode,
    List.length_append,List.length_cons,List.length_nil,List.append_nil,pc_one_ge,Nat.zero_add]

theorem signed_ge_execution (valid : Array UInt256) (seed : EVM.State)
    (before after : Backend.Program) (a b : Scalar.Word) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op .SLT])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Scalar.run [.op .SLT,.op .ISZERO] (a::b::tail) = some (Scalar.flag (!(decide (a.toInt < b.toInt)))::tail) ∧
    Assembly.driverSteps 2 (fuel+3) valid (signedGeInput seed before after a b tail) =
      .ok (signedGeOutput seed before after a b tail) ∧
    EVM.X (fuel+3) valid (signedGeInput seed before after a b tail) =
      EVM.X (fuel+1) valid (signedGeOutput seed before after a b tail) := by
  have initialFits : (Backend.encode before).length < UInt256.size := by
    simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,Instr.encode,
      List.length_append,List.length_cons,List.length_nil] at fits
    omega
  have first := signed_lt_agreement valid (⟨seed,before,.op .ISZERO::after,initialFits⟩)
    a b tail room (by change 3 ≤ seed.gasAvailable.toNat;omega) (fuel+1)
  dsimp only at first
  rw [first_alignment_ge] at first
  have debit : (signedGeCompared seed before after a b tail).gasAvailable.toNat =
      seed.gasAvailable.toNat-3 := reference_gas_debit seed.gasAvailable 3 (by omega)
  have second := iszero_agreement valid
    (⟨signedGeCompared seed before after a b tail,before ++ [.op .SLT],after,fits⟩)
    (Scalar.flag (decide (a.toInt < b.toInt))) tail (by omega)
    (by change 3 ≤ (signedGeCompared seed before after a b tail).gasAvailable.toNat;rw [debit];omega) fuel
  dsimp only at second
  rw [second_alignment_ge,Scalar.flag_iszero] at second
  have firstDriver : Assembly.driverSteps 1 (fuel+3) valid (signedGeInput seed before after a b tail) =
      .ok (signedGeCompared seed before after a b tail) := first.2.1
  refine ⟨?_,?_,first.2.2.trans second.2.2⟩
  · change some (Scalar.flag (Scalar.flag (decide (a.toInt < b.toInt)) == 0)::tail) = _
    rw [Scalar.flag_iszero]
  · rw [fetched_steps_append 1 1 (fuel+1),firstDriver]
    exact second.2.1

/-- Actual typed certificate and native two-step result for the same operands. -/
theorem selected_signed_ge_execution (valid : Array UInt256) (seed : EVM.State)
    (before after : Backend.Program) (a b : PrimTy.int.Denote) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [.op .SLT])).length < UInt256.size)
    (room : tail.length+2 ≤ 1024) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Scalar.run (Scalar.intGe).code (Scalar.encodeValue .int a::Scalar.encodeValue .int b::tail) =
      (BinOp.ge.evalT (p := .int) rfl a b).map
        (fun result => Scalar.encodeValue .bool result::tail) ∧
    Assembly.driverSteps 2 (fuel+3) valid
      (signedGeInput seed before after (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) tail) =
      .ok (signedGeOutput seed before after (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) tail) ∧
    EVM.X (fuel+3) valid
      (signedGeInput seed before after (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) tail) =
      EVM.X (fuel+1) valid
        (signedGeOutput seed before after (Scalar.encodeValue .int a) (Scalar.encodeValue .int b) tail) := by
  exact ⟨(Scalar.intGe).correct a b tail,
    (signed_ge_execution valid seed before after (Scalar.encodeValue .int a)
      (Scalar.encodeValue .int b) tail fits room gas fuel).2⟩

theorem signed_ge_debit (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) (gas : 6 ≤ seed.gasAvailable.toNat) :
    (signedGeOutput seed before after a b tail).gasAvailable.toNat = seed.gasAvailable.toNat-6 := by
  have first := reference_gas_debit seed.gasAvailable 3 (by omega)
  have second := reference_gas_debit (seed.gasAvailable-UInt256.ofNat 3) 3 (by rw [first];omega)
  change ((seed.gasAvailable-UInt256.ofNat 3)-UInt256.ofNat 3).toNat = _
  rw [second,first,Nat.sub_sub]

theorem signed_ge_frame (seed : EVM.State) (before after : Backend.Program)
    (a b : Scalar.Word) (tail : Scalar.Stack) :
    (signedGeOutput seed before after a b tail).toState = (signedGeInput seed before after a b tail).toState ∧
    (signedGeOutput seed before after a b tail).memory = seed.memory ∧
    (signedGeOutput seed before after a b tail).returnData = seed.returnData ∧
    (signedGeOutput seed before after a b tail).H_return = seed.H_return ∧
    (signedGeOutput seed before after a b tail).stack =
      (Scalar.flag (!(decide (a.toInt < b.toInt)))::tail).map (fun w => UInt256.mk w.toFin) ∧
    (signedGeOutput seed before after a b tail).execLength = seed.execLength+2 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩


#print axioms signed_lt_word
#print axioms signed_lt_agreement
#print axioms selected_signed_lt_agreement
#print axioms signed_ge_execution
#print axioms selected_signed_ge_execution
#print axioms signed_ge_debit
#print axioms signed_ge_frame
end SolidityBridge.RoadmapV15.P10
