import Solidity.Backend.Executable.Relocation
import Solidity.Backend.Scalar.Heights

/-! A linked PUSH20 section with a genuine backward JUMP operand, embedded
between nonempty code. All0x5b address bytes remain PUSH data. Numeric setup
slices preserve a populated tail; neither JUMPDEST nor JUMP is executed here. -/
namespace Solidity.Backend.Executable.RelocationChecks
open Scalar

def pre : Program := [.push 1 #v[0x5b], .op .POP]
def suffix : List UInt8 := [0x5b,0x60,0x5b]
def address (_ : Unit) : Vector UInt8 20 := Vector.replicate 20 0x5b
def items : List (Item Nat Unit) :=
  [.tag 0, .pushLibraryAddress (), .instr (.op .POP),
   .instr (.push 2 #v[0x5b,0x5b]), .instr (.op .POP), .pushTag 0, .instr (.op .JUMP)]
def output (link : Unit → Option (Vector UInt8 20)) : Assembled Unit :=
  ⟨[.op .JUMPDEST, .push 20 ((link ()).getD placeholder), .op .POP,
    .push 2 #v[0x5b,0x5b], .op .POP, .push 1 #v[3], .op .JUMP],
    if (link ()).isNone then [(5,())] else []⟩
def unresolved : Assembled Unit := output (fun _ => none)
def linked : Assembled Unit := output (fun _ => some (address ()))

private def widened : Widths Nat := widen 3 items (fun _ => 0)
private theorem widened_at_zero : widened 0 = (1 : Fin 33) := by
  apply Fin.ext
  change min 32 (max 0 (byteWidth 3)) = 1
  rw [Creation.byteWidth_small 3 (by decide) (by decide)]
  rfl

/-- Real fixpoint widening changes PUSH0 to PUSH1 at nonzero base3. The
library bytes never enter the label-width or code-layout calculation. -/
theorem selected_widths : asmWidths (size pre) items = widened := by
  have next : widen 3 items widened 0 = widened 0 := by
    apply Fin.ext
    change min 32 (max (widened 0).val (byteWidth 3)) = (widened 0).val
    rw [widened_at_zero, Creation.byteWidth_small 3 (by decide) (by decide)]
    rfl
  have first : (refs items).all (fun l => widen 3 items (fun _ => 0) l == (0 : Fin 33)) = false := by
    change ((widened 0 == (0 : Fin 33)) && true) = false
    rw [widened_at_zero]
    rfl
  have fixed : (refs items).all (fun l => widen 3 items widened l == widened l) = true := by
    change ((widen 3 items widened 0 == widened 0) && true) = true
    rw [next, widened_at_zero]
    rfl
  change asmWidths 3 items = _
  unfold asmWidths
  rw [fixWidths]
  simp only [first, Bool.false_eq_true, dite_false]
  change fixWidths 3 items widened = widened
  rw [fixWidths]
  simp only [fixed, dite_true]

theorem assembled (link : Unit → Option (Vector UInt8 20)) :
    assemble (size pre) link items = some (output link) := by
  unfold assemble
  rw [selected_widths]
  have zero : tagOffset widened items 0 = 0 := rfl
  have layout : layoutOk (size pre) items widened = true := by
    simp only [layoutOk, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨by decide +kernel, by rfl⟩, ?_⟩
    rw [show refs items = [0] from rfl]
    simp only [List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq]
    rw [zero, widened_at_zero]
    decide +kernel
  simp only [layout, if_true]
  have emission : items.map (Item.emit widened (tagOffset widened items) (size pre) link) = (output link).code := by
    change ([.op .JUMPDEST, .push 20 ((link ()).getD placeholder), .op .POP,
      .push 2 #v[0x5b,0x5b], .op .POP,
      .push (widened 0) (toBytesBE (widened 0) (size pre + tagOffset widened items 0)), .op .JUMP] : Program) = _
    rw [zero, Nat.add_zero, widened_at_zero]
    rfl
  have references : linkRefsFrom widened link (size pre) items = (output link).linkRefs := by
    change (if (link ()).isNone then [(5,())] else []) ++ [] = _
    rw [List.append_nil]
    rfl
  rw [emission, references]

theorem actual_unresolved : assemble (size pre) (fun _ => none) items = some unresolved := assembled _
theorem actual_linked : assemble (size pre) (fillLink (fun _ => none) address) items = some linked := assembled _

/-- Consume the general composition on a real backward reference. Both the
encoded pre/suffix and all linked target/data facts survive its real patch. -/
theorem client :
    linkBytes (encode pre ++ encode unresolved.code ++ suffix) unresolved.linkRefs address =
      encode pre ++ encode linked.code ++ suffix ∧
    (∃ imm, linked.code[5]? = some (.push (asmWidths (size pre) items 0) imm) ∧
      ofBytesBE imm.toList = 3 ∧ ofBytesBE imm.toList < 256 ^ (asmWidths (size pre) items 0).val ∧
      ofBytesBE imm.toList < size pre + offset linked.code 5) ∧
    validJumpdest (encode pre ++ encode linked.code ++ suffix) 3 = true ∧
    (∀ n, InPushData (encode linked.code ++ suffix) n →
      validJumpdest (encode pre ++ encode linked.code ++ suffix) (size pre+n) = false) := by
  obtain ⟨out, imm, ran, _, patch, _, _, _, _, push, _, value, fit, back, valid, data⟩ :=
    Relocation.linked_backedge pre suffix address actual_unresolved
      (j := 0) (k := 5) (label := 0) rfl rfl (by decide)
  have same : out = linked := Option.some.inj (ran.symm.trans actual_linked)
  subst out
  change ofBytesBE imm.toList = 3 at value
  exact ⟨patch, ⟨imm,push,value,fit,back⟩, by rw [value] at valid; exact valid, data⟩

/-- Actual assembler origins and all final instruction offsets are checked,
not supplied as a desired layout certificate. -/
theorem layout : linked.code.length = 7 ∧ size pre = 3 ∧ size linked.code = 30 ∧
    unresolved.linkRefs = [(5,())] ∧ linked.linkRefs = [] ∧
    offset linked.code 0 = 0 ∧ offset linked.code 5 = 27 ∧ offset linked.code 6 = 29 ∧
    (∀ k, offset linked.code k = itemOffset (asmWidths (size pre) items) items k) := by
  have actual := assemble_layout actual_linked
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,actual.2.1⟩

/-- Every byte of the actual linked address is0x5b, but none is a target. -/
theorem address_payload (i : Nat) (bound : i < 20) :
    InPushData (encode linked.code ++ suffix) (2+i) ∧
    validJumpdest (encode pre ++ encode linked.code ++ suffix) (5+i) = false := by
  have data : InPushData (encode linked.code ++ suffix) (2+i) :=
    ⟨1, by
      rw [starts_encode_append]
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨1, by decide, rfl⟩,
      0x73, rfl, by omega, by change 2+i ≤ 21; omega⟩
  refine ⟨data, ?_⟩
  have invalid := client.2.2.2 (2+i) data
  simpa only [show size pre = 3 from rfl, ← Nat.add_assoc] using invalid

theorem exact_link_bytes :
    ((encode pre ++ encode linked.code ++ suffix).drop 5).take 20 = List.replicate 20 0x5b ∧
    encode linked.code = [0x5b,0x73] ++ List.replicate 20 0x5b ++
      [0x50,0x61,0x5b,0x5b,0x50,0x60,3,0x56] := by exact ⟨rfl,rfl⟩

private theorem whole_scan : jumpdests (encode pre ++ encode linked.code ++ suffix) = [3,33] := by
  have bytes : encode pre ++ encode linked.code ++ suffix =
      encode (pre ++ linked.code ++ [.op .JUMPDEST, .push 1 #v[0x5b]]) ++ [] := by
    rw [encode_append, encode_append, List.append_nil]
    rfl
  rw [bytes]
  unfold jumpdests
  rw [starts_encode_append]
  simp only [starts, List.map_nil, List.append_nil]
  rfl
private theorem local_scan : jumpdests (encode linked.code ++ suffix) = [0,30] := by
  have bytes : encode linked.code ++ suffix =
      encode (linked.code ++ [.op .JUMPDEST, .push 1 #v[0x5b]]) ++ [] := by
    rw [encode_append, List.append_nil]
    rfl
  rw [bytes]
  unfold jumpdests
  rw [starts_encode_append]
  simp only [starts, List.map_nil, List.append_nil]
  rfl

/-- The prefix payload, fragment PUSH2 data, unrelocated0 and one-past-code
are all invalid. A real suffix JUMPDEST remains a separate valid boundary. -/
theorem invalid_targets :
    validJumpdest (encode pre ++ encode linked.code ++ suffix) 0 = false ∧
    validJumpdest (encode pre ++ encode linked.code ++ suffix) 1 = false ∧
    validJumpdest (encode pre ++ encode linked.code ++ suffix) 27 = false ∧
    validJumpdest (encode pre ++ encode linked.code ++ suffix) 28 = false ∧
    validJumpdest (encode pre ++ encode linked.code ++ suffix) 33 = true ∧
    validJumpdest (encode pre ++ encode linked.code ++ suffix) 36 = false := by
  unfold validJumpdest
  rw [whole_scan]
  decide +kernel

/-- Empty versus nonempty enclosing prefix changes the correct coordinate. -/
theorem relocation_coordinates :
    validJumpdest (encode linked.code ++ suffix) 0 = true ∧
    validJumpdest (encode pre ++ encode linked.code ++ suffix) 0 = false ∧
    validJumpdest (encode pre ++ encode linked.code ++ suffix) (size pre+0) = true ∧
    encode pre ≠ [] ∧ suffix ≠ [] := by
  unfold validJumpdest
  rw [whole_scan, local_scan]
  decide +kernel

/-- Precisely the real straight-line instructions after the head JUMPDEST
and before JUMP. No instruction transition across either control opcode. -/
def setup : Program := linked.code.drop 1 |>.take 5

theorem setup_tail (tail : Stack) :
    run pre tail = some tail ∧ run setup tail = some ((3 : Word) :: tail) := ⟨rfl,rfl⟩

theorem setup_capacity (tail : Stack) :
    stackBound setup (tail.length : Int) = true ↔ tail.length ≤ 1023 := by
  change (stackBound [.push 20 (address ()), .op .POP, .push 2 #v[0x5b,0x5b], .op .POP, .push 1 #v[3]] (tail.length : Int) = true ↔ tail.length ≤ 1023)
  simp only [stackBound, heightTrace, stackDelta, safeHeight, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem setup_prefix_capacity (tail : Stack) (room : tail.length ≤ 1023)
    (first rest : Program) (split : first ++ rest = setup) {st : Stack}
    (ran : run first tail = some st) : st.length ≤ 1024 := by
  apply prefix_capacity first rest ran
  rw [split]
  exact (setup_capacity tail).mpr room

/-- Distinct protected caller words survive real operand materialization.
Capacity refusal is independent of the gasless runner's mathematical result. -/
theorem inhabited_tail : run setup [17,29] = some [3,17,29] ∧
    run setup [] = some [3] ∧ stackBound setup 2 = true ∧
    stackBound setup 1024 = false := by decide +kernel

theorem roundtrip : decode (encode pre ++ encode linked.code ++ suffix) =
    some (pre ++ linked.code ++ [.op .JUMPDEST, .push 1 #v[0x5b]]) := by
  have exactBytes : encode pre ++ encode linked.code ++ suffix =
      encode (pre ++ linked.code ++ [.op .JUMPDEST, .push 1 #v[0x5b]]) := by
    rw [encode_append, encode_append]
    rfl
  rw [exactBytes]
  exact decode_encode _
/-- info: 'Solidity.Backend.Executable.RelocationChecks.assembled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assembled
/-- info: 'Solidity.Backend.Executable.RelocationChecks.client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms client
/-- info: 'Solidity.Backend.Executable.RelocationChecks.layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms layout
/-- info: 'Solidity.Backend.Executable.RelocationChecks.address_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms address_payload
/-- info: 'Solidity.Backend.Executable.RelocationChecks.exact_link_bytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms exact_link_bytes
/-- info: 'Solidity.Backend.Executable.RelocationChecks.invalid_targets' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invalid_targets
/-- info: 'Solidity.Backend.Executable.RelocationChecks.relocation_coordinates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms relocation_coordinates
/-- info: 'Solidity.Backend.Executable.RelocationChecks.setup_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms setup_tail
/-- info: 'Solidity.Backend.Executable.RelocationChecks.setup_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms setup_capacity
/-- info: 'Solidity.Backend.Executable.RelocationChecks.setup_prefix_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms setup_prefix_capacity
/-- info: 'Solidity.Backend.Executable.RelocationChecks.inhabited_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inhabited_tail
/-- info: 'Solidity.Backend.Executable.RelocationChecks.roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundtrip
end Solidity.Backend.Executable.RelocationChecks
