import Solidity.Backend.Executable.TransferCallChecks
import Solidity.Backend.Executable.PrefixChecks

/-! Constructor/runtime consumer for the actual assembled payment program.
The existing creation slice only executes COPY/RETURN/REVERT wrappers. It does
not execute the contained runtime's CALLs, scalar instructions or jumps.
Runtime frame/source/world/gas and fetched execution correspondence stay OPEN.
Constructor Exec exposes an outcome, not a final stack or universal headroom. -/
namespace Solidity.Backend.Executable.PaymentArtifact
open Creation
open TransferCallChecks (payment output assembled)

def runtime : List UInt8 := Backend.encode output.code

private theorem selected_sizes (W : Widths Nat) :
    ((TransferCall.items payment).map (Item.size W)).sum = 318+(W 0).val+(W 1).val := by
  simp only [TransferCall.items, List.map_append, List.sum_append_nat, List.map_map,
    Function.comp_def, Item.size]
  change Backend.size payment + ((TransferCall.branch.expand 0).1.map (Item.size W)).sum = _
  rw [← Backend.length_encode, TransferCallChecks.prefix_lengths.2]
  simp only [TransferCall.branch, Block.expand, Failure.emit, Failure.Input.bytes,
    Failure.Input.terminal, Failure.writes, Failure.pushNat, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Item.size, Instr.size, Nat.reduceAdd]
  omega

private theorem label_offsets (W : Widths Nat) :
    tagOffset W (TransferCall.items payment) 0 = 249+(W 0).val+(W 1).val ∧
    tagOffset W (TransferCall.items payment) 1 = 317+(W 0).val+(W 1).val := by
  have first : tagIndex (TransferCall.items payment) 0 = some 23 := by decide +kernel
  have second : tagIndex (TransferCall.items payment) 1 = some 27 := by decide +kernel
  constructor
  · rw [tagOffset, first]
    simp only [itemOffset, TransferCall.items, TransferCallChecks.payment, TransferCallChecks.prelude,
      TransferCall.branch, Block.expand, StipendCall.code, StipendCall.operands, StipendCall.gasCode,
      ValueCall.emptyBuffers, ValueCall.localAmount, Scalar.literal, Scalar.pushWord, Scalar.pushByte,
      ScalarSequence.frameTail, ScalarSequence.callerFrame, Failure.emit, Failure.Input.bytes,
      Failure.Input.terminal, Failure.writes, Failure.pushNat, Failure.pushByte,
      List.cons_append, List.nil_append, List.reverse_cons, List.reverse_nil,
      List.map_cons, List.map_nil, List.take_succ_cons, List.take_zero,
      Item.size, Instr.size, List.sum_cons, List.sum_nil, Nat.reduceAdd]
    omega
  · rw [tagOffset, second]
    simp only [itemOffset, TransferCall.items, TransferCallChecks.payment, TransferCallChecks.prelude,
      TransferCall.branch, Block.expand, StipendCall.code, StipendCall.operands, StipendCall.gasCode,
      ValueCall.emptyBuffers, ValueCall.localAmount, Scalar.literal, Scalar.pushWord, Scalar.pushByte,
      ScalarSequence.frameTail, ScalarSequence.callerFrame, Failure.emit, Failure.Input.bytes,
      Failure.Input.terminal, Failure.writes, Failure.pushNat, Failure.pushByte,
      List.cons_append, List.nil_append, List.reverse_cons, List.reverse_nil,
      List.map_cons, List.map_nil, List.take_succ_cons, List.take_zero,
      Item.size, Instr.size, List.sum_cons, List.sum_nil, Nat.reduceAdd]
    omega

private def widened : Widths Nat := widen 0 (TransferCall.items payment) (fun _ => 0)
private theorem widened_first : widened 0 = (1 : Fin 33) := by
  apply Fin.ext
  change min 32 (max 0 (byteWidth 249)) = 1
  rw [byteWidth_small 249 (by decide) (by decide)]
  rfl
private theorem widened_second : widened 1 = (2 : Fin 33) := by
  apply Fin.ext
  change min 32 (max 0 (byteWidth 317)) = 2
  rw [byteWidth]
  change min 32 (max 0 (byteWidth 1+1)) = 2
  rw [byteWidth_small 1 (by decide) (by decide)]
  rfl
private theorem selected_widths : asmWidths 0 (TransferCall.items payment) = widened := by
  have firstOffset : tagOffset widened (TransferCall.items payment) 0 = 252 := by
    rw [(label_offsets widened).1, widened_first, widened_second]
    rfl
  have secondOffset : tagOffset widened (TransferCall.items payment) 1 = 320 := by
    rw [(label_offsets widened).2, widened_first, widened_second]
    rfl
  have nextFirst : widen 0 (TransferCall.items payment) widened 0 = widened 0 := by
    apply Fin.ext
    change min 32 (max (widened 0).val (byteWidth (0+tagOffset widened (TransferCall.items payment) 0))) = (widened 0).val
    rw [firstOffset, widened_first, byteWidth_small 252 (by decide) (by decide)]
    rfl
  have nextSecond : widen 0 (TransferCall.items payment) widened 1 = widened 1 := by
    apply Fin.ext
    change min 32 (max (widened 1).val (byteWidth (0+tagOffset widened (TransferCall.items payment) 1))) = (widened 1).val
    rw [secondOffset, widened_second, byteWidth]
    change min 32 (max 2 (byteWidth 1+1)) = 2
    rw [byteWidth_small 1 (by decide) (by decide)]
    rfl
  have first : (refs (TransferCall.items payment)).all (fun l => widen 0 (TransferCall.items payment) (fun _ => 0) l == (0 : Fin 33)) = false := by
    change ((widened 0 == (0 : Fin 33)) && ((widened 1 == (0 : Fin 33)) && true)) = false
    rw [widened_first, widened_second]
    rfl
  have stable : (refs (TransferCall.items payment)).all (fun l => widen 0 (TransferCall.items payment) widened l == widened l) = true := by
    change ((widen 0 (TransferCall.items payment) widened 0 == widened 0) &&
      ((widen 0 (TransferCall.items payment) widened 1 == widened 1) && true)) = true
    rw [nextFirst, nextSecond, widened_first, widened_second]
    rfl
  unfold asmWidths
  rw [fixWidths]
  simp only [first, Bool.false_eq_true, dite_false]
  change fixWidths 0 (TransferCall.items payment) widened = widened
  rw [fixWidths]
  simp only [stable, dite_true]

/-- Actual selected widths determine the runtime length; no arbitrary byte
length or completed simulation certificate is supplied to the artifact. -/
theorem runtime_length : runtime.length = 318+(asmWidths 0 (TransferCall.items payment) 0).val+
    (asmWidths 0 (TransferCall.items payment) 1).val := by
  have emitted := (assemble_eq assembled).2.1
  rw [runtime, Backend.length_encode, emitted]
  simp only [Backend.size, List.map_map, Function.comp_def, Item.size_emit]
  exact selected_sizes _

theorem runtime_length_exact : runtime.length = 321 := by
  rw [runtime_length, selected_widths, widened_first, widened_second]
  rfl

/-- The complete control/terminal suffix is emitted by the actual assembler,
including both immediate payloads and the existing empty-REVERT emitter. -/
theorem runtime_bytes : runtime = Backend.encode payment ++
    [0x15,0x60,252,0x57,0x61,1,64,0x56,0x5b] ++
      Backend.encode (Failure.emit 0 .empty) ++ [0x5b] := by
  have firstOffset : tagOffset widened (TransferCall.items payment) 0 = 252 := by
    rw [(label_offsets widened).1, widened_first, widened_second]
    rfl
  have secondOffset : tagOffset widened (TransferCall.items payment) 1 = 320 := by
    rw [(label_offsets widened).2, widened_first, widened_second]
    rfl
  have suffix : ((TransferCall.branch.expand 0).1.map
      (Item.emit (asmWidths 0 (TransferCall.items payment))
        (tagOffset (asmWidths 0 (TransferCall.items payment)) (TransferCall.items payment)) 0 TransferCall.noLink)) =
      [.op .ISZERO,.push 1 #v[252],.op .JUMPI,.push 2 #v[1,64],.op .JUMP,.op .JUMPDEST] ++
        Failure.emit 0 .empty ++ [.op .JUMPDEST] := by
    rw [selected_widths]
    simp only [TransferCall.branch, Block.expand, Failure.emit, Failure.Input.bytes,
      Failure.Input.terminal, Failure.writes, List.cons_append, List.nil_append,
      List.map_cons, List.map_nil, Item.emit, Nat.reduceAdd]
    rw [firstOffset, secondOffset, widened_first, widened_second]
    rfl
  have headBytes : Backend.encode [.op .ISZERO,.push 1 #v[252],.op .JUMPI,.push 2 #v[1,64],.op .JUMP,.op .JUMPDEST] =
      [0x15,0x60,252,0x57,0x61,1,64,0x56,0x5b] := rfl
  have endBytes : Backend.encode [.op .JUMPDEST] = [0x5b] := rfl
  rw [runtime, TransferCall.prefix_preserved payment assembled, suffix]
  simp only [Backend.encode_append, headBytes, endBytes]
  simp only [List.append_assoc]

theorem runtime_range : 318 ≤ runtime.length ∧ runtime.length ≤ 382 := by
  rw [runtime_length]
  have first := (asmWidths 0 (TransferCall.items payment) 0).isLt
  have second := (asmWidths 0 (TransferCall.items payment) 1).isLt
  omega

theorem runtime_fits : runtime.length < 256^32 := by
  have large : 382 < 256^32 := by decide +kernel
  exact Nat.lt_of_le_of_lt runtime_range.2 large

theorem runtime_width : byteWidth runtime.length = 2 := by
  have nonzero : runtime.length ≠ 0 := by have := runtime_range; omega
  have divide : runtime.length / 256 = 1 := by have := runtime_range; omega
  rw [byteWidth, if_neg nonzero, divide, byteWidth_small 1 (by decide) (by decide)]

def artifact (args : List UInt8) : Artifact Empty := fromAssembly 0 output args runtime_fits

def placement : Placement (Backend.encode copyPrefix) runtime where
  lengthWord := ⟨runtime.length,runtime_fits⟩
  length_eq := rfl
  offsetWord := ⟨18,by decide⟩
  aligned := by
    rw [placed_size, Backend.length_encode]
    change 18 = 6+(2*byteWidth runtime.length+byteWidth 18+7)
    rw [runtime_width, byteWidth_small 18 (by decide) (by decide)]

/-- Both actual nonempty constructor segments precede the copy/exit. Runtime
coordinates stay based at zero, independently of this eighteen-byte prefix. -/
def front (success : Bool) : List UInt8 :=
  Backend.encode copyPrefix ++ Backend.encode (exitWrapper success placement.lengthWord placement.offsetWord)
def image (success : Bool) (args : List UInt8) : List UInt8 := front success ++ runtime ++ args

theorem front_length (success : Bool) : (front success).length = 18 := by
  simp only [front, List.length_append, Backend.length_encode, exitWrapper_size]
  exact placement.aligned.symm

theorem constructor_exec (success : Bool) (args : List UInt8) (tail : List StackWord) :
    Exec (image success args) (image success args) tail [] (exitOutcome success runtime) :=
  PrefixChecks.segmented placement success args tail

theorem runtime_slice (success : Bool) (args : List UInt8) :
    ((image success args).drop 18).take runtime.length = runtime := by
  rw [image, List.append_assoc, ← front_length success, List.drop_left, List.take_left]

theorem arguments_slice (success : Bool) (args : List UInt8) :
    (image success args).drop (18+runtime.length) = args := by
  rw [image, ← front_length success, ← List.length_append, List.drop_left]

theorem decode_runtime : Backend.decode runtime = some output.code := Backend.decode_encode _

/-- Standalone fromAssembly and the nonempty-prefix image both return exactly
the same real assembled runtime. This is no account-installation theorem. -/
theorem standalone_installs (args : List UInt8) :
    Exec (artifact args).payload (artifact args).payload [] [] (.returned runtime) :=
  installs_runtime _

private theorem failure_tail : output.code.drop 23 =
    [.op .JUMPDEST] ++ Failure.emit 0 .empty ++ [.op .JUMPDEST] := by
  rw [TransferCall.prefix_preserved payment assembled, List.drop_append]
  have count : payment.length = 18 := rfl
  rw [count]
  have dropped : payment.drop 23 = [] := List.drop_eq_nil_of_le (by rw [count]; decide)
  simp only [show (23 : Nat)-18 = 5 from rfl, dropped, List.nil_append]
  rfl

private theorem misplaced_byte (imm : Vector UInt8 (asmWidths 0 (TransferCall.items payment) 0))
    (value : ofBytesBE imm.toList = offset output.code 23) :
    runtime[18+ofBytesBE imm.toList]? = some 0 := by
  have split : output.code = output.code.take 23 ++
      ([.op .JUMPDEST] ++ Failure.emit 0 .empty ++ [.op .JUMPDEST]) := by
    rw [← failure_tail]
    exact (List.take_append_drop 23 output.code).symm
  have boundary : (Backend.encode (output.code.take 23)).length = ofBytesBE imm.toList := by
    rw [Backend.length_encode]
    exact value.symm
  rw [runtime, split, Backend.encode_append,
    List.getElem?_append_right (by rw [boundary]; omega)]
  rw [boundary]
  have sub : 18+ofBytesBE imm.toList-ofBytesBE imm.toList = 18 := by omega
  rw [sub]
  decide +kernel

/-- The actual selected false target is valid at runtime coordinate zero and
at its constructor-data position, but adding the constructor offset to the
installed runtime's operand targets PUSH data. The input is actual assembly,
not a desired jump-execution premise. -/
theorem constructor_runtime_coordinates (success : Bool) (args : List UInt8) :
    ∃ imm, output.code[payment.length+1]? =
        some (.push (asmWidths 0 (TransferCall.items payment) 0) imm) ∧
      validJumpdest runtime (ofBytesBE imm.toList) = true ∧
      validJumpdest (image success args) (18+ofBytesBE imm.toList) = true ∧
      validJumpdest runtime (18+ofBytesBE imm.toList) = false := by
  obtain ⟨j,imm,index,dest,push,value,_,valid⟩ :=
    assemble_pushTag assembled (show (TransferCall.items payment)[payment.length+1]? = some (.pushTag 0) from rfl)
  have actualIndex : tagIndex (TransferCall.items payment) 0 = some 23 := by decide +kernel
  have same : j = 23 := Option.some.inj (index.symm.trans actualIndex)
  subst j
  have coordinate : ofBytesBE imm.toList = offset output.code 23 := by
    simpa only [Nat.zero_add] using value
  let ctor : Program := copyPrefix ++ exitWrapper success placement.lengthWord placement.offsetWord
  have frontCode : Backend.encode ctor = front success := Backend.encode_append _ _
  have ctorSize : Backend.size ctor = 18 := by
    rw [← Backend.length_encode, frontCode]
    exact front_length success
  have whole : (ctor ++ output.code)[ctor.length+23]? = some (.op .JUMPDEST) := by
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact dest
  have shifted := validJumpdest_encode_append (ctor ++ output.code) args whole
  rw [offset_append, ctorSize, ← coordinate, Backend.encode_append, frontCode] at shifted
  refine ⟨imm,push,?_,shifted,?_⟩
  · simpa only [Backend.encode_nil, List.nil_append, List.append_nil] using valid [] [] rfl
  · apply Bool.eq_false_iff.mpr
    intro bad
    have byte := (validJumpdest_iff _ _).mp bad |>.1
    rw [misplaced_byte imm coordinate] at byte
    cases byte

/-- info: 'Solidity.Backend.Executable.PaymentArtifact.runtime_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runtime_length

/-- info: 'Solidity.Backend.Executable.PaymentArtifact.runtime_length_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runtime_length_exact

/-- info: 'Solidity.Backend.Executable.PaymentArtifact.runtime_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runtime_bytes

/-- info: 'Solidity.Backend.Executable.PaymentArtifact.runtime_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runtime_range

/-- info: 'Solidity.Backend.Executable.PaymentArtifact.runtime_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runtime_fits

/-- info: 'Solidity.Backend.Executable.PaymentArtifact.runtime_width' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runtime_width

/-- info: 'Solidity.Backend.Executable.PaymentArtifact.front_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms front_length

/-- info: 'Solidity.Backend.Executable.PaymentArtifact.constructor_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms constructor_exec

/-- info: 'Solidity.Backend.Executable.PaymentArtifact.runtime_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runtime_slice

/-- info: 'Solidity.Backend.Executable.PaymentArtifact.arguments_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms arguments_slice

/-- info: 'Solidity.Backend.Executable.PaymentArtifact.decode_runtime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decode_runtime

/-- info: 'Solidity.Backend.Executable.PaymentArtifact.standalone_installs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms standalone_installs

/-- info: 'Solidity.Backend.Executable.PaymentArtifact.constructor_runtime_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms constructor_runtime_coordinates

end Solidity.Backend.Executable.PaymentArtifact
