import SolidityBridge.RoadmapV15.P10.NegationBody
import SolidityBridge.RoadmapV15.P10.EqualityConsumer
import SolidityBridge.RoadmapV15.P10.StackFamilyConsumer

/-! Actual three fetched instructions of the published G25 negation test.
The conditional branch, panic emitter and compiler/frame origin remain open. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def negationDup : Backend.Instr := .op (.DUP ⟨0,by decide⟩)
def negationTestInput (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack) : EVM.State :=
  {seed with
    executionEnv := {seed.executionEnv with
      code := ⟨(Backend.encode (before ++ Scalar.negationTest ++ after)).toArray⟩}
    pc := UInt256.ofNat (Backend.encode before).length
    stack := (Scalar.encodeValue .int a::tail).map (fun w => UInt256.mk w.toFin)}
def negationTestDup (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (negationTestInput seed before after a tail) 3).replaceStackAndIncrPC
    ((Scalar.encodeValue .int a::Scalar.encodeValue .int a::tail).map (fun w => UInt256.mk w.toFin))
def negationTestPushed (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (negationTestDup seed before after a tail) 3).replaceStackAndIncrPC
    ((Scalar.encodeValue .int Scalar.minimumInt::Scalar.encodeValue .int a::
      Scalar.encodeValue .int a::tail).map (fun w => UInt256.mk w.toFin)) 33
def negationTestOutput (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (negationTestPushed seed before after a tail) 3).replaceStackAndIncrPC
    ((Scalar.flag (!PrimTy.int.inRange (-a.val))::Scalar.encodeValue .int a::tail).map
      (fun w => UInt256.mk w.toFin))

theorem negation_test_word (a : PrimTy.int.Denote) :
    Scalar.flag (Scalar.encodeValue .int Scalar.minimumInt == Scalar.encodeValue .int a) =
      Scalar.flag (!PrimTy.int.inRange (-a.val)) := by
  have h := Scalar.negationTest_typed a []
  rw [Scalar.negationTest,Scalar.run] at h
  change Scalar.run [Scalar.pushWord (Scalar.encodeValue .int Scalar.minimumInt),.op .EQ]
    [Scalar.encodeValue .int a,Scalar.encodeValue .int a] = _ at h
  rw [Scalar.run,Scalar.step_pushWord] at h
  change some (Scalar.flag (Scalar.encodeValue .int Scalar.minimumInt == Scalar.encodeValue .int a)::
    Scalar.encodeValue .int a::[]) = _ at h
  exact (List.cons.inj (Option.some.inj h)).1

private theorem dup_bytes : Instr.encode (.op (.DUP ⟨0,by decide⟩)) = [0x80] := by rfl

private theorem pc_one (n : Nat) : UInt256.ofNat n + UInt256.ofNat 1 = UInt256.ofNat (n+1) := by
  apply congrArg UInt256.mk
  apply Fin.ext
  exact (Nat.add_mod n 1 UInt256.size).symm

private theorem dup_alignment (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack) (fits : (Backend.encode before).length < UInt256.size) :
    (modularSite (⟨seed,before,
      [Scalar.pushWord (Scalar.encodeValue .int Scalar.minimumInt),.op .EQ] ++ after,fits⟩ :
      Site (.DUP ⟨0,by decide⟩)) (Scalar.encodeValue .int a::tail)).state =
      negationTestInput seed before after a tail := by
  simp only [modularSite,Site.state,negationTestInput,Scalar.negationTest,
    List.append_assoc,List.cons_append,List.nil_append]

private theorem push_alignment (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack) :
    wordPushInput (negationTestDup seed before after a tail) (before ++ [negationDup])
      (.op .EQ::after) (Scalar.encodeValue .int Scalar.minimumInt)
      (Scalar.encodeValue .int a::Scalar.encodeValue .int a::tail) =
      negationTestDup seed before after a tail := by
  simp only [negationTestDup,negationTestInput,wordPushInput,Scalar.negationTest,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,
    List.map_cons,List.append_assoc,List.cons_append,List.nil_append,Backend.encode_append,
    Backend.encode_cons,Backend.encode_nil,negationDup,dup_bytes,List.length_append,List.length_cons,
    List.length_nil,List.append_nil,pc_one,Nat.zero_add]

private theorem eq_alignment (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [negationDup,
      Scalar.pushWord (Scalar.encodeValue .int Scalar.minimumInt)])).length < UInt256.size) :
    (modularSite (⟨negationTestPushed seed before after a tail,
      before ++ [negationDup,Scalar.pushWord (Scalar.encodeValue .int Scalar.minimumInt)],after,fits⟩ :
      Site .EQ) (Scalar.encodeValue .int Scalar.minimumInt::Scalar.encodeValue .int a::
        Scalar.encodeValue .int a::tail)).state = negationTestPushed seed before after a tail := by
  simp only [modularSite,Site.state,negationTestPushed,negationTestDup,negationTestInput,
    Scalar.negationTest,Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,
    EVM.State.incrPC,List.map_cons,List.append_assoc,List.cons_append,List.nil_append,
    Backend.encode_append,Backend.encode_cons,Backend.encode_nil,negationDup,dup_bytes,
    List.length_append,List.length_cons,List.append_nil,Scalar.encode_pushWord,
    Vector.length_toList,pc_one,signed_push_pc,Nat.add_assoc]

/-- The selected three-opcode test, without an assumed test run or decode. -/
theorem negation_test_execution (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [negationDup,
      Scalar.pushWord (Scalar.encodeValue .int Scalar.minimumInt)])).length < UInt256.size)
    (room : tail.length+3 ≤ 1024) (gas : 9 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Scalar.run Scalar.negationTest (Scalar.encodeValue .int a::tail) =
      some (Scalar.flag (!PrimTy.int.inRange (-a.val))::Scalar.encodeValue .int a::tail) ∧
    Assembly.driverSteps 3 (fuel+4) #[] (negationTestInput seed before after a tail) =
      .ok (negationTestOutput seed before after a tail) ∧
    EVM.X (fuel+4) #[] (negationTestInput seed before after a tail) =
      EVM.X (fuel+1) #[] (negationTestOutput seed before after a tail) := by
  have lengths : (Backend.encode (before ++ [negationDup,
      Scalar.pushWord (Scalar.encodeValue .int Scalar.minimumInt)])).length =
      (Backend.encode before).length+34 := by
    simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,negationDup,dup_bytes,
      List.length_append,List.length_cons,List.length_nil,Scalar.encode_pushWord,Vector.length_toList]
  have initialFits : (Backend.encode before).length < UInt256.size := by rw [lengths] at fits;omega
  have pushFits : (Backend.encode (before ++ [negationDup])).length < UInt256.size := by
    simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,negationDup,dup_bytes,
      List.length_append,List.length_cons,List.length_nil]
    rw [lengths] at fits
    omega
  have first := dup_family_agreement ⟨0,by decide⟩
    (⟨seed,before,[Scalar.pushWord (Scalar.encodeValue .int Scalar.minimumInt),.op .EQ] ++ after,initialFits⟩)
    [] tail (Scalar.encodeValue .int a) rfl (by simp only [List.length_nil];omega) (by change 3 ≤ seed.gasAvailable.toNat;omega) (fuel+2)
  dsimp only at first
  simp only [List.nil_append] at first
  rw [dup_alignment] at first
  have firstDebit : (negationTestDup seed before after a tail).gasAvailable.toNat =
      seed.gasAvailable.toNat-3 := reference_gas_debit seed.gasAvailable 3 (by omega)
  have second := word_push_table_agreement #[] (negationTestDup seed before after a tail)
    (before ++ [negationDup]) (.op .EQ::after) (Scalar.encodeValue .int Scalar.minimumInt)
    (Scalar.encodeValue .int a::Scalar.encodeValue .int a::tail) pushFits
    (by rw [firstDebit];omega) (by simp only [List.length_cons];omega) (fuel+1)
  dsimp only at second
  rw [push_alignment] at second
  have secondDebit : (negationTestPushed seed before after a tail).gasAvailable.toNat =
      (negationTestDup seed before after a tail).gasAvailable.toNat-3 :=
    reference_gas_debit _ 3 (by rw [firstDebit];omega)
  have third := equality_agreement #[]
    (⟨negationTestPushed seed before after a tail,before ++ [negationDup,
      Scalar.pushWord (Scalar.encodeValue .int Scalar.minimumInt)],after,fits⟩)
    (Scalar.encodeValue .int Scalar.minimumInt) (Scalar.encodeValue .int a)
    (Scalar.encodeValue .int a::tail) (by simp only [List.length_cons];omega)
    (by rw [secondDebit,firstDebit];omega) fuel
  dsimp only at third
  rw [eq_alignment,negation_test_word] at third
  have d1 : Assembly.driverSteps 1 (fuel+4) #[] (negationTestInput seed before after a tail) =
      .ok (negationTestDup seed before after a tail) := first.2.1
  have d2 : Assembly.driverSteps 1 (fuel+3) #[] (negationTestDup seed before after a tail) =
      .ok (negationTestPushed seed before after a tail) := second.2.1
  refine ⟨Scalar.negationTest_typed a tail,?_,first.2.2.trans (second.2.2.trans third.2.2)⟩
  rw [fetched_steps_append 1 2 (fuel+2),d1]
  change Assembly.driverSteps 2 (fuel+3) #[] (negationTestDup seed before after a tail) = _
  rw [fetched_steps_append 1 1 (fuel+1),d2]
  exact third.2.1

/-- A legal 1023-word input passes DUP1, then fails at PUSH32's peak 1025. -/
theorem negation_test_overflow (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack)
    (fits : (Backend.encode (before ++ [negationDup])).length < UInt256.size)
    (full : tail.length = 1022) (gas : 6 ≤ seed.gasAvailable.toNat) :
    Assembly.driverSteps 3 4 #[] (negationTestInput seed before after a tail) = .error .StackOverflow := by
  have initialFits : (Backend.encode before).length < UInt256.size := by
    simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,negationDup,dup_bytes,
      List.length_append,List.length_cons,List.length_nil] at fits
    omega
  have first := dup_family_agreement ⟨0,by decide⟩
    (⟨seed,before,[Scalar.pushWord (Scalar.encodeValue .int Scalar.minimumInt),.op .EQ] ++ after,initialFits⟩)
    [] tail (Scalar.encodeValue .int a) rfl
    (by simp only [List.length_nil,full];decide) (by change 3 ≤ seed.gasAvailable.toNat;omega) 2
  dsimp only at first
  simp only [List.nil_append] at first
  rw [dup_alignment] at first
  have debit : (negationTestDup seed before after a tail).gasAvailable.toNat =
      seed.gasAvailable.toNat-3 := reference_gas_debit seed.gasAvailable 3 (by omega)
  have second := word_push_full_stack (negationTestDup seed before after a tail)
    (before ++ [negationDup]) (.op .EQ::after) (Scalar.encodeValue .int Scalar.minimumInt)
    (Scalar.encodeValue .int a::Scalar.encodeValue .int a::tail) fits (by rw [debit];omega)
    (by simp only [List.length_cons,full]) 1
  dsimp only at second
  rw [push_alignment] at second
  rw [fetched_steps_append 1 2 2,first.2.1]
  change Assembly.driverSteps 2 3 #[] (negationTestDup seed before after a tail) = _
  rw [fetched_steps_append 1 1 1,second.1]
  rfl

theorem negation_test_debit (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack) (gas : 9 ≤ seed.gasAvailable.toNat) :
    (negationTestOutput seed before after a tail).gasAvailable.toNat = seed.gasAvailable.toNat-9 := by
  have first := reference_gas_debit seed.gasAvailable 3 (by omega)
  have second := reference_gas_debit (seed.gasAvailable-UInt256.ofNat 3) 3 (by rw [first];omega)
  have third := reference_gas_debit ((seed.gasAvailable-UInt256.ofNat 3)-UInt256.ofNat 3) 3
    (by rw [second,first];omega)
  change (((seed.gasAvailable-UInt256.ofNat 3)-UInt256.ofNat 3)-UInt256.ofNat 3).toNat = _
  rw [third,second,first,Nat.sub_sub,Nat.sub_sub]

theorem negation_test_frame (seed : EVM.State) (before after : Backend.Program)
    (a : PrimTy.int.Denote) (tail : Scalar.Stack) :
    (negationTestOutput seed before after a tail).toState =
      (negationTestInput seed before after a tail).toState ∧
    (negationTestOutput seed before after a tail).memory = seed.memory ∧
    (negationTestOutput seed before after a tail).returnData = seed.returnData ∧
    (negationTestOutput seed before after a tail).H_return = seed.H_return ∧
    (negationTestOutput seed before after a tail).stack =
      (Scalar.flag (!PrimTy.int.inRange (-a.val))::Scalar.encodeValue .int a::tail).map
        (fun w => UInt256.mk w.toFin) ∧
    (negationTestOutput seed before after a tail).execLength = seed.execLength+3 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms negation_test_word
#print axioms negation_test_execution
#print axioms negation_test_debit
#print axioms negation_test_frame
#print axioms negation_test_overflow
end SolidityBridge.RoadmapV15.P10
