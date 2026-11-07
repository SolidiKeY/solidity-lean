import Solidity.Yul.Compilation.WordInstructionCertificates
/-! Closed-stack fault/success, exact occurrence origin and width-erasure
controls. Equal compiler-model PUSHes do not imply equal native bytes. Caller
rescue and intermediate capacity controls prevent broader failure claims. -/
namespace Solidity.Yul.Compilation.WordInstructionCertificates.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation MachineAdapter

def shortPush : Backend.Instr := .push 1 #v[1]
def paddedPush : Backend.Instr := .push 2 #v[0,1]
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def program : Backend.Program := [paddedPush,.op .ADD,.op (.DUP 0),.op .NOT]
def model : List Evm.Instr := [.push (coreWord 1),.add,.dup 1,.not]
def pushCertificate := instruction paddedPush (.push (coreWord 1)) (by rfl)

theorem selected_model : WordMachine.selectCode program = some model := rfl

theorem padded_origin : pushCertificate.code = [paddedPush] := rfl

theorem same_model_selection : WordMachine.selectCode [shortPush] = WordMachine.selectCode [paddedPush] := rfl
theorem distinct_bytes : Backend.encode [shortPush] ≠ Backend.encode [paddedPush] := by decide

/-- Exact local encode/decode roundtrip only; no fetched execution theorem. -/
theorem decode_roundtrip : Backend.decode (Backend.encode pushCertificate.code) = some [paddedPush] :=
 Backend.decode_encode [paddedPush]

theorem closed_model (input : Stack) (m : Evm.Machine) :
 Evm.run model {m with stack := input.map coreWord} =
 match Scalar.run program input with
 | none => .fault
 | some output => .ok {m with stack := output.map coreWord} 0 :=
 WordClosedExecution.run program model selected_model input m

theorem scalar_result (a : Scalar.Word) : Scalar.run program [a] = some [~~~(1+a),1+a] := by rfl

theorem model_result (a : Scalar.Word) (m : Evm.Machine) :
 Evm.run model {m with stack := [coreWord a]} =
 .ok {m with stack := [coreWord (~~~(1+a)),coreWord (1+a)]} 0 := by
 have law := closed_model [a] m
 rw [scalar_result] at law
 exact law

/-- The first PUSH succeeds; the following ADD fails on a closed empty input. -/
theorem prefix_failure (m : Evm.Machine) : Evm.run model {m with stack := []} = .fault := by
 exact (closed_model [] m)

theorem caller_rescue (m : Evm.Machine) : Scalar.run program [] = none ∧
 Evm.run model {m with stack := [coreWord dirty]} =
 .ok {m with stack := [coreWord (~~~(1+dirty)),coreWord (1+dirty)]} 0 :=
 ⟨rfl,model_result dirty m⟩

/-- Even a symbolic caller can supply a missing DUP operand; no closed-stack
failure theorem may be generalized to an arbitrary suffix. -/
theorem symbolic_rescue (m : Evm.Machine) : Scalar.run [.op (.DUP 0)] [] = none ∧
 Evm.run [.dup 1] {m with stack := [.slot (.root 17)]} =
 .ok {m with stack := [.slot (.root 17),.slot (.root 17)]} 0 := by
 constructor <;> rfl

/-- Existing model selection still succeeds when a real capacity check fails
at the PUSH output, even though the input height is exactly1024. -/
theorem capacity_separate (input : Vector Scalar.Word 1024) (m : Evm.Machine) :
 Evm.run [.push (coreWord 0)] {m with stack := input.toList.map coreWord} =
 .ok {m with stack := coreWord 0::input.toList.map coreWord} 0 ∧
 Scalar.stackBound [pushWord 0] 1024 = false := by
 constructor
 · have scalar : Scalar.run [pushWord 0] input.toList = some (0::input.toList) := by
     simp only [Scalar.run,step_pushWord,Option.bind_some]
   have law := WordClosedExecution.run [pushWord 0] [.push (coreWord 0)] (by rfl) input.toList m
   rw [scalar] at law
   exact law
 · decide

/-- The generic result is a real existing lowering certificate for this leaf,
not an upgrade to full-source or native/charged correctness. -/
def leafCertificate : LoweringCertificate model (.code program) := lowering program model selected_model

def sixteen : Stack := List.replicate 15 0 ++ [dirty]
#guard Scalar.run [.op (.DUP 15)] (List.replicate 15 dirty) = none
#guard Scalar.run [.op (.DUP 15)] sixteen = some (dirty::sixteen)
#guard Scalar.run [.op (.SWAP 15)] sixteen = none
#guard Scalar.run [.op (.SWAP 15)] (7::sixteen) = some (dirty::(List.replicate 15 0++[7]))
#guard (WordMachine.selectInstr paddedPush).isSome
#guard (WordMachine.selectInstr shortPush).isSome
#guard (WordMachine.selectInstr (.op .SDIV)).isNone
#guard (WordMachine.selectInstr (.op .SSTORE)).isNone
#guard (WordMachine.selectInstr (.op .GAS)).isNone
#guard match Evm.run model {Evm.Machine.init with stack := []} with | .fault => true | _ => false
#guard match Evm.run model {Evm.Machine.init with stack := [coreWord dirty]} with
 | .ok m 0 => m.stack == [coreWord (~~~(1+dirty)),coreWord (1+dirty)]
 | _ => false
#guard Backend.encode [shortPush] == [0x60,0x01]
#guard Backend.encode [paddedPush] == [0x61,0x00,0x01]
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.Controls.selected_model' depends on axioms: [propext] -/
#guard_msgs in
#print axioms selected_model
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.Controls.padded_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms padded_origin
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.Controls.same_model_selection' depends on axioms: [propext] -/
#guard_msgs in
#print axioms same_model_selection
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.Controls.distinct_bytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms distinct_bytes
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.Controls.decode_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms decode_roundtrip
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.Controls.closed_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms closed_model
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.Controls.scalar_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scalar_result
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.Controls.model_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_result
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.Controls.prefix_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms prefix_failure
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.Controls.caller_rescue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms caller_rescue
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.Controls.symbolic_rescue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms symbolic_rescue
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.Controls.capacity_separate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms capacity_separate
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.Controls.pushCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pushCertificate
/-- info: 'Solidity.Yul.Compilation.WordInstructionCertificates.Controls.leafCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms leafCertificate
end Solidity.Yul.Compilation.WordInstructionCertificates.Controls
