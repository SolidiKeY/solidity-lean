import Solidity.Backend.LabelExec.Packets
import Solidity.Backend.Control

/-! Execution clients of the existing assembler. Layout bounds are consumed,
not asserted as a new execution certificate or favourable destination table. -/
namespace Solidity.Backend.LabelExec

def emptyLink (x : Empty) : Option (Vector UInt8 20) := nomatch x

/-- The real emitted prefix at coordinate base zero. -/
def emitPrefix (items pre : List (Item Nat Empty)) : Program :=
  pre.map (Item.emit (asmWidths 0 items) (tagOffset (asmWidths 0 items) items) 0 emptyLink)

/-- Exactly the immediate emitted by the existing label assembler at base zero. -/
def labelImm (items : List (Item Nat Empty)) (label : Nat) :
    Vector UInt8 (asmWidths 0 items label) :=
  toBytesBE (asmWidths 0 items label) (tagOffset (asmWidths 0 items) items label)

/-- A fitting assembler operand does not wrap when read by the numeric slice. -/
theorem immediate_fit (n : Fin 33) (v : Nat) (h : v < 256 ^ n.val) :
    (Scalar.immediate (toBytesBE n.val v).toList).toNat = v := by
  have hw : n.val ≤ 32 := by omega
  have hp : (256 : Nat) ^ 32 = 2 ^ 256 := by
    calc
      (256 : Nat) ^ 32 = (2 ^ 8) ^ 32 := rfl
      _ = 2 ^ (8 * 32) := (Nat.pow_mul 2 8 32).symm
      _ = 2 ^ 256 := rfl
  have hb : v < 2 ^ 256 := by
    rw [← hp]
    exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hw)
  simp only [Scalar.immediate, ofBytesBE_toBytesBE n.val v h, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hb]

/-- Actual assembly produces an exact encoded branch packet, a nonwrapping
operand and a destination accepted by the published byte scanner. -/
theorem resolved_layout (pre post : List (Item Nat Empty)) (label : Nat)
    (branch : Op) (out : Assembled Empty)
    (h : assemble 0 emptyLink (pre ++ (.pushTag label :: .instr (.op branch) :: post)) = some out) :
    ∃ j, tagIndex (pre ++ (.pushTag label :: .instr (.op branch) :: post)) label = some j ∧
      encode out.code = branchCode (encode (emitPrefix (pre ++ (.pushTag label :: .instr (.op branch) :: post)) pre))
        (asmWidths 0 (pre ++ (.pushTag label :: .instr (.op branch) :: post)) label) (labelImm (pre ++ (.pushTag label :: .instr (.op branch) :: post)) label) branch
        (encode (emitPrefix (pre ++ (.pushTag label :: .instr (.op branch) :: post)) post)) ∧
      (Scalar.immediate (labelImm (pre ++ (.pushTag label :: .instr (.op branch) :: post)) label).toList).toNat = offset out.code j ∧
      validJumpdest (encode out.code)
        (Scalar.immediate (labelImm (pre ++ (.pushTag label :: .instr (.op branch) :: post)) label).toList).toNat = true := by
  let items : List (Item Nat Empty) := (pre ++ (.pushTag label :: .instr (.op branch) :: post))
  have hk : items[pre.length]? = some (.pushTag label) := by
    simp only [items, List.getElem?_append_right (Nat.le_refl pre.length),
      Nat.sub_self, List.getElem?_cons_zero]
  obtain ⟨j, hj, _, _, hoff, hfit⟩ := assemble_ref h hk rfl
  have hf : tagOffset (asmWidths 0 items) items label <
      256 ^ (asmWidths 0 items label).val := by
    rw [hoff]
    simpa only [Nat.zero_add] using hfit
  have ht : (Scalar.immediate (labelImm items label).toList).toNat = offset out.code j := by
    rw [labelImm, immediate_fit _ _ hf, hoff]
  have hv : validJumpdest (encode out.code) (offset out.code j) = true := by
    obtain ⟨j', imm, hj', _, _, hval, _, hvalid⟩ := assemble_pushTag h hk
    have he : j' = j := Option.some.inj (hj'.symm.trans hj)
    subst j'
    have q : validJumpdest (encode [] ++ encode out.code ++ []) (ofBytesBE imm.toList) = true :=
      hvalid [] [] rfl
    simpa only [encode_nil, List.nil_append, List.append_nil, hval, Nat.zero_add] using q
  refine ⟨j, hj, ?_, ht, ?_⟩
  · have hc : out.code = items.map (Item.emit (asmWidths 0 items)
        (tagOffset (asmWidths 0 items) items) 0 emptyLink) := (assemble_eq h).2.1
    simp only [hc, items, emitPrefix, branchCode, labelImm, List.map_append,
      List.map_cons, encode_append, encode_cons, Item.emit, Nat.zero_add]
  · rw [ht]
    exact hv

/-- A labelled PUSH/JUMP in actual assembled runtime bytes executes to its
own label, retaining the physical tail. No reached-state/step/target premise. -/
theorem assembled_jump (pre post : List (Item Nat Empty)) (label : Nat)
    (out : Assembled Empty) (h : assemble 0 emptyLink (pre ++ (.pushTag label :: .instr (.op .JUMP) :: post)) = some out)
    (tail : Scalar.Stack) :
    ∃ j, tagIndex (pre ++ (.pushTag label :: .instr (.op .JUMP) :: post)) label = some j ∧
      advance 2 (encode out.code) ⟨size (emitPrefix (pre ++ (.pushTag label :: .instr (.op .JUMP) :: post)) pre),tail⟩ =
        some ⟨offset out.code j,tail⟩ := by
  obtain ⟨j, hj, hcode, ht, hv⟩ := resolved_layout pre post label .JUMP out h
  refine ⟨j, hj, ?_⟩
  rw [← length_encode (emitPrefix (pre ++ (.pushTag label :: .instr (.op .JUMP) :: post)) pre), hcode, jump_packet, ← hcode, hv, if_pos rfl, ht]

/-- Both actual conditional-label arms, after assembler checks have resolved
all target bytes. The condition is consumed, never supplied as a success bit. -/
theorem assembled_jumpi (pre post : List (Item Nat Empty)) (label : Nat)
    (out : Assembled Empty) (h : assemble 0 emptyLink (pre ++ (.pushTag label :: .instr (.op .JUMPI) :: post)) = some out)
    (condition : Scalar.Word) (tail : Scalar.Stack) :
    ∃ j, tagIndex (pre ++ (.pushTag label :: .instr (.op .JUMPI) :: post)) label = some j ∧
      advance 2 (encode out.code)
        ⟨size (emitPrefix (pre ++ (.pushTag label :: .instr (.op .JUMPI) :: post)) pre),condition :: tail⟩ =
      if condition == 0 then
        some ⟨size (emitPrefix (pre ++ (.pushTag label :: .instr (.op .JUMPI) :: post)) pre) +
          (Instr.push (asmWidths 0 (pre ++ (.pushTag label :: .instr (.op .JUMPI) :: post)) label) (labelImm (pre ++ (.pushTag label :: .instr (.op .JUMPI) :: post)) label)).size + 1,tail⟩
      else some ⟨offset out.code j,tail⟩ := by
  obtain ⟨j, hj, hcode, ht, hv⟩ := resolved_layout pre post label .JUMPI out h
  refine ⟨j, hj, ?_⟩
  rw [← length_encode (emitPrefix (pre ++ (.pushTag label :: .instr (.op .JUMPI) :: post)) pre), hcode, jumpi_packet,
    ← hcode, hv, if_pos rfl, ht]

/-- The actual item-level conditional test used by structured expansion. -/
def testItems (pre post : List (Item Nat Empty)) (label : Nat) : List (Item Nat Empty) :=
  pre ++ (.instr (.op .ISZERO) :: .pushTag label :: .instr (.op .JUMPI) :: post)

/-- The actual ISZERO test in assembled control code: zero takes the label,
nonzero continues after the conditional branch, preserving the real tail. -/
theorem assembled_test (pre post : List (Item Nat Empty)) (label : Nat)
    (out : Assembled Empty)
    (h : assemble 0 emptyLink (testItems pre post label) = some out)
    (condition : Scalar.Word) (tail : Scalar.Stack) :
    ∃ j, tagIndex (testItems pre post label) label = some j ∧
      advance 3 (encode out.code)
        ⟨size (emitPrefix (testItems pre post label) pre),condition :: tail⟩ =
      if condition == 0 then some ⟨offset out.code j,tail⟩
      else some ⟨size (emitPrefix (testItems pre post label) pre) + 1 +
        (Instr.push (asmWidths 0 (testItems pre post label) label)
          (labelImm (testItems pre post label) label)).size + 1,tail⟩ := by
  let items := testItems pre post label
  have hi : ((pre ++ [.instr (.op .ISZERO)]) ++
      (.pushTag label :: .instr (.op .JUMPI) :: post)) = items := by
    simp only [items, testItems, List.append_assoc, List.cons_append, List.nil_append]
  have hp : assemble 0 emptyLink ((pre ++ [.instr (.op .ISZERO)]) ++
      (.pushTag label :: .instr (.op .JUMPI) :: post)) = some out := by
    rw [hi]
    exact h
  obtain ⟨j, hj, hcode, ht, hv⟩ := resolved_layout
    (pre ++ [.instr (.op .ISZERO)]) post label .JUMPI out hp
  rw [hi] at hj hcode ht hv
  have hx : encode out.code = testCode (encode (emitPrefix items pre))
      (asmWidths 0 items label) (labelImm items label) (encode (emitPrefix items post)) := by
    simpa only [emitPrefix, List.map_append, List.map_cons, List.map_nil, Item.emit,
      encode_append, encode_cons, encode_nil, List.append_nil, branchCode, testCode,
      List.append_assoc] using hcode
  refine ⟨j, hj, ?_⟩
  rw [← length_encode (emitPrefix items pre), hx, test_packet, ← hx, hv, if_pos rfl, ht]

end Solidity.Backend.LabelExec
