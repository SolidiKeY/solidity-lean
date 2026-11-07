import Solidity.Backend.Selection.ControlPackets

/-! Inhabited assembler clients and independent literal byte-vector controls.
The literal vectors do not assert the assembler's least chosen width. -/
namespace Solidity.Backend.Selection.ExecutionTrace.PacketControls

open LabelExec

def before : List (Item Nat Empty) := [.instr (Scalar.pushWord 99)]
def after : List (Item Nat Empty) := [.instr (Scalar.pushByte 42), .tag 0, .instr (.op .POP)]
def items : List (Item Nat Empty) := testItems before after 0

/-- Actual assembly is constructed using the published assembler theorem. -/
theorem assembly_exists : ∃ out : Assembled Empty, assemble 0 emptyLink items = some out := by
  have onlyRef : ∀ label ∈ refs items, label = 0 := by
    intro label member
    simpa only [show refs items = [0] from rfl, List.mem_cons, List.not_mem_nil, or_false] using member
  have defined : ∀ label ∈ refs items, (tagIndex items label).isSome := by
    intro label member; rw [onlyRef label member]; decide
  have fits : ∀ label ∈ refs items,
      0 + tagOffset (fun _ => (32 : Fin 33)) items label < 256 ^ 32 := by
    intro label member; rw [onlyRef label member]; decide
  exact Option.isSome_iff_exists.mp (assemble_isSome emptyLink (by decide) defined fits)

/-- Both generated arms use actual assembled bytes and derive all bounds. -/
theorem certified (tail : Scalar.Stack) (room : tail.length + 2 ≤ 1024) :
    ∃ out : Assembled Empty, assemble 0 emptyLink items = some out ∧
      Safe (encode out.code) 3 ⟨33,0 :: tail⟩ ⟨offset out.code 5,tail⟩ ∧
      Safe (encode out.code) 3 ⟨33,7 :: tail⟩
        ⟨size (emitPrefix items (before ++ [.instr (.op .ISZERO), .pushTag 0, .instr (.op .JUMPI)])),tail⟩ := by
  obtain ⟨out,assembly⟩ := assembly_exists
  obtain ⟨zeroIndex,zeroFound,zeroSafe⟩ := test before after 0 out assembly 0 tail room
  obtain ⟨nonzeroIndex,nonzeroFound,nonzeroSafe⟩ := test before after 0 out assembly 7 tail room
  have zero_at : zeroIndex = 5 := Option.some.inj (zeroFound.symm.trans (show tagIndex items 0 = some 5 from rfl))
  subst zeroIndex
  exact ⟨out,assembly,zeroSafe,nonzeroSafe⟩

/-- Explicit executable bytes, checked independently of width-fixpoint evaluation. -/
def program : Program := [Scalar.pushWord 99, .op .ISZERO, Scalar.pushByte 39, .op .JUMPI,
  Scalar.pushByte 42, .op .JUMPDEST, .op .POP]

theorem destination_valid : validJumpdest (encode program) 39 = true := by
  have valid : validJumpdest (encode program ++ []) (offset program 5) = true :=
    validJumpdest_encode_append program [] (show program[5]? = some (.op .JUMPDEST) from rfl)
  simpa only [List.append_nil] using valid

theorem zero_run (tail : Scalar.Stack) :
    advance 3 (encode program) ⟨33,0 :: tail⟩ = some ⟨39,tail⟩ := by
  have packet : advance 3 (encode program) ⟨33,0 :: tail⟩ =
      (if (0 : Scalar.Word) == 0 then
        if validJumpdest (encode program) 39 then some ⟨39,tail⟩ else none
        else some ⟨37,tail⟩) :=
    test_packet (encode [Scalar.pushWord 99]) 1 #v[39]
      (encode [Scalar.pushByte 42, .op .JUMPDEST, .op .POP]) 0 tail
  simpa only [beq_self_eq_true, destination_valid, if_true] using packet

theorem nonzero_run (tail : Scalar.Stack) :
    advance 3 (encode program) ⟨33,7 :: tail⟩ = some ⟨37,tail⟩ := by rfl

/-- ISZERO does not add a word; the following label PUSH supplies the peak. -/
theorem peak (tail : Scalar.Stack) :
    advance 2 (encode program) ⟨33,0 :: tail⟩ = some ⟨36,39 :: 1 :: tail⟩ := by rfl

/-- The literal byte-vector control independently checks every prefix. -/
theorem bounded_zero (tail : Scalar.Stack) (room : tail.length + 2 ≤ 1024) :
    Safe (encode program) 3 ⟨33,0 :: tail⟩ ⟨39,tail⟩ := by
  refine ⟨zero_run tail,?_⟩
  intro k within
  have cases_k : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases cases_k with rfl | rfl | rfl | rfl
  · exact ⟨⟨33,0 :: tail⟩,rfl,by change tail.length + 1 ≤ 1024; omega⟩
  · exact ⟨⟨34,1 :: tail⟩,rfl,by change tail.length + 1 ≤ 1024; omega⟩
  · exact ⟨⟨36,39 :: 1 :: tail⟩,peak tail,by change tail.length + 1 + 1 ≤ 1024; omega⟩
  · exact ⟨⟨39,tail⟩,zero_run tail,by change tail.length ≤ 1024; omega⟩

theorem exact_capacity : Safe (encode program) 3
    ⟨33,0 :: List.replicate 1022 23⟩ ⟨39,List.replicate 1022 23⟩ :=
  bounded_zero _ (by simp only [List.length_replicate]; omega)

/-- The gasless machine can overfill; Safe rejects that actual intermediate state. -/
theorem hidden_overflow (finish : LabelExec.State) :
    ¬ Safe (encode program) 3 ⟨33,0 :: List.replicate 1023 23⟩ finish := by
  intro safe
  obtain ⟨reached,actual,bound⟩ := safe.2 2 (by decide)
  have same : reached = ⟨36,39 :: 1 :: List.replicate 1023 23⟩ :=
    Option.some.inj (actual.symm.trans (peak _))
  rw [same] at bound
  simp only [List.length_cons, List.length_replicate] at bound
  omega

theorem unaligned_entry : advance 3 (encode program) ⟨1,[0,23]⟩ = none := by decide

theorem wrong_result : advance 3 (encode program) ⟨33,[0,23]⟩ ≠ some ⟨39,[0,23]⟩ := by
  rw [zero_run]; decide

theorem corrupted_tail : advance 3 (encode program) ⟨33,[0,23]⟩ ≠ some ⟨39,[24]⟩ := by
  rw [zero_run]; decide

def corrupt : Program := [Scalar.pushWord 99, .op .ISZERO, Scalar.pushByte 38, .op .JUMPI,
  Scalar.pushByte 0x5b, .op .JUMPDEST, .op .POP]

/-- Its byte is JUMPDEST, but it lies inside PUSH data rather than at a boundary. -/
theorem corrupt_payload : (encode corrupt)[38]? = some Op.JUMPDEST.code ∧
    InPushData (encode corrupt) 38 := by
  have boundary : 37 ∈ starts (encode corrupt) := by
    rw [← List.append_nil (encode corrupt), starts_encode_append]
    apply List.mem_append.mpr
    left
    exact List.mem_map.mpr ⟨4,by decide,rfl⟩
  exact ⟨by decide,⟨37,boundary,0x60,by decide,by decide,by decide⟩⟩

theorem corrupt_invalid : validJumpdest (encode corrupt) 38 = false := by
  apply Bool.eq_false_iff.mpr
  intro valid
  exact ((validJumpdest_iff _ _).mp valid).2 corrupt_payload.2

theorem corrupt_taken : advance 3 (encode corrupt) ⟨33,[0,23]⟩ = none := by
  have packet : advance 3 (encode corrupt) ⟨33,[0,23]⟩ =
      (if (0 : Scalar.Word) == 0 then
        if validJumpdest (encode corrupt) 38 then some ⟨38,[23]⟩ else none
        else some ⟨37,[23]⟩) :=
    test_packet (encode [Scalar.pushWord 99]) 1 #v[38]
      (encode [Scalar.pushByte 0x5b, .op .JUMPDEST, .op .POP]) 0 [23]
  simpa only [beq_self_eq_true, corrupt_invalid, Bool.false_eq_true, if_true, if_false] using packet

/-- An untaken JUMPI never needs its corrupted target to be valid. -/
theorem corrupt_untaken : advance 3 (encode corrupt) ⟨33,[7,23]⟩ = some ⟨37,[23]⟩ := by decide

def jumpItems : List (Item Nat Empty) :=
  before ++ [.pushTag 0, .instr (.op .JUMP), .instr (Scalar.pushByte 42), .tag 0]

theorem jump_assembly_exists : ∃ out : Assembled Empty, assemble 0 emptyLink jumpItems = some out := by
  have onlyRef : ∀ label ∈ refs jumpItems, label = 0 := by
    intro label member
    simpa only [show refs jumpItems = [0] from rfl, List.mem_cons, List.not_mem_nil, or_false] using member
  have defined : ∀ label ∈ refs jumpItems, (tagIndex jumpItems label).isSome := by
    intro label member; rw [onlyRef label member]; decide
  have fits : ∀ label ∈ refs jumpItems,
      0 + tagOffset (fun _ => (32 : Fin 33)) jumpItems label < 256 ^ 32 := by
    intro label member; rw [onlyRef label member]; decide
  exact Option.isSome_iff_exists.mp (assemble_isSome emptyLink (by decide) defined fits)

theorem certified_jump (tail : Scalar.Stack) (room : tail.length + 1 ≤ 1024) :
    ∃ out : Assembled Empty, assemble 0 emptyLink jumpItems = some out ∧
      Safe (encode out.code) 2 ⟨33,tail⟩ ⟨offset out.code 4,tail⟩ := by
  obtain ⟨out,assembly⟩ := jump_assembly_exists
  obtain ⟨index,found,safe⟩ := jump before [.instr (Scalar.pushByte 42), .tag 0]
    0 out assembly tail room
  have index_at : index = 4 := Option.some.inj (found.symm.trans (show tagIndex jumpItems 0 = some 4 from rfl))
  subst index
  exact ⟨out,assembly,safe⟩

/-- JUMPDEST is actually executed in the assembled control witness. -/
theorem destination_step (tail : Scalar.Stack) (room : tail.length ≤ 1024) :
    ∃ out : Assembled Empty, assemble 0 emptyLink items = some out ∧
      Safe (encode out.code) 1 ⟨offset out.code 5,tail⟩ ⟨offset out.code 5 + 1,tail⟩ := by
  obtain ⟨out,assembly⟩ := assembly_exists
  have first : LabelExec.step (encode out.code) ⟨offset out.code 5,tail⟩ =
      some ⟨offset out.code 5 + 1,tail⟩ :=
    assembled_tag_step items 0 5 out assembly rfl tail
  exact ⟨out,assembly,single _ _ _ first room room⟩

#print axioms assembly_exists
#print axioms certified
#print axioms destination_valid
#print axioms zero_run
#print axioms nonzero_run
#print axioms peak
#print axioms exact_capacity
#print axioms hidden_overflow
#print axioms unaligned_entry
#print axioms wrong_result
#print axioms corrupted_tail
#print axioms corrupt_payload
#print axioms corrupt_invalid
#print axioms corrupt_taken
#print axioms corrupt_untaken
#print axioms certified_jump
#print axioms destination_step

end Solidity.Backend.Selection.ExecutionTrace.PacketControls
