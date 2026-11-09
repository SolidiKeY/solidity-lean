import Solidity.Backend.Assembler

/-! Guard library patching that corrupts an emitted label reference, treats
address payload bytes as labels, or re-links already completed code. Reuse the
actual checked assembler and link_patch APIs: no new linker/interface or source
semantics. Scanner validity and byte substitution are proved, not jump execution,
gas, Source/G24 or native realization. Existing resolved addresses stay fixed. -/
namespace Solidity.Yul.Compilation
open Backend

/-- Every byte inside an actual PUSH immediate is data, even when it equals
JUMPDEST. An arbitrary trailing byte sequence cannot change that classification. -/
theorem push_payload_not_jumpdest (p : Program) (suffix : List UInt8)
    {k : Nat} {width : Fin 33} {imm : Vector UInt8 width.val}
    (selected : p[k]? = some (.push width imm)) (byte : Fin width.val) :
    validJumpdest (encode p ++ suffix) (offset p k + 1 + byte.val) = false := by
  have member : offset p k ∈ (List.range p.length).map (offset p) :=
    List.mem_map.mpr ⟨k, List.mem_range.mpr (List.getElem?_eq_some_iff.mp selected).1, rfl⟩
  have boundary : offset p k ∈ starts (encode p ++ suffix) := by
    rw [starts_encode_append]
    exact List.mem_append_left _ member
  have opcode := getElem?_encode_append_offset p suffix selected
  have digits : immWidth (Instr.push width imm).opcode = width.val := by
    have size := immWidth_opcode (Instr.push width imm)
    change immWidth (Instr.push width imm).opcode + 1 = width.val + 1 at size
    exact Nat.add_right_cancel size
  have inside : InPushData (encode p ++ suffix) (offset p k + 1 + byte.val) := by
    refine ⟨offset p k, boundary, (Instr.push width imm).opcode, opcode, ?_, ?_⟩
    · omega
    · rw [digits]
      have bound := byte.isLt
      omega
  cases checked : validJumpdest (encode p ++ suffix) (offset p k + 1 + byte.val) with
  | false => rfl
  | true => exact (((validJumpdest_iff _ _).mp checked).2 inside).elim

section Generic
variable {L Lib : Type} [DecidableEq L]

/-- A specific original emitted reference survives actual byte patching, with
no unresolved links and no effect from a second link pass. -/
theorem linked_pushTag_reference {base : Nat} {link : Lib → Option (Vector UInt8 20)}
    {items : List (Item L Lib)} {out : Assembled Lib} (addr : Lib → Vector UInt8 20)
    (assembled : assemble base link items = some out) {k : Nat} {l : L}
    (ref : items[k]? = some (.pushTag l)) :
    ∃ linked : Assembled Lib, ∃ j : Nat,
    ∃ imm : Vector UInt8 (asmWidths base items l).val,
      assemble base (fillLink link addr) items = some linked ∧ linked.linkRefs = [] ∧
      out.code[k]? = some (.push (asmWidths base items l) imm) ∧
      linked.code[k]? = some (.push (asmWidths base items l) imm) ∧
      linked.code[j]? = some (.op .JUMPDEST) ∧
      ofBytesBE imm.toList = base + offset out.code j ∧
      (∀ i : Nat, offset linked.code i = offset out.code i) ∧
      ∀ (pre : Program) (suffix : List UInt8), size pre = base →
        linkBytes (encode pre ++ encode out.code ++ suffix) out.linkRefs addr =
          encode pre ++ encode linked.code ++ suffix ∧
        validJumpdest (linkBytes (encode pre ++ encode out.code ++ suffix)
          out.linkRefs addr) (ofBytesBE imm.toList) = true ∧
        ∀ other : Lib → Vector UInt8 20,
          linkBytes (encode pre ++ encode linked.code ++ suffix) linked.linkRefs other =
            encode pre ++ encode linked.code ++ suffix := by
  obtain ⟨linked, selected, done, patched, offsets, unchanged⟩ := link_patch addr assembled
  obtain ⟨j, imm, tag, destOld, codeOld, valueOld, tagValue, validOld⟩ :=
    assemble_pushTag assembled ref
  obtain ⟨other, next, nextTag, destNew, codeNew, valueNew, nextValue, validNew⟩ :=
    assemble_pushTag selected ref
  have same : other = j := Option.some.inj (nextTag.symm.trans tag)
  subst other
  have kept : linked.code[k]? = out.code[k]? :=
    unchanged k (.pushTag l) ref (by intro x impossible; cases impossible)
  have target : ofBytesBE imm.toList = ofBytesBE next.toList := by
    rw [valueOld, valueNew, offsets]
  refine ⟨linked, j, imm, selected, done, codeOld, kept.trans codeOld,
    destNew, valueOld, offsets, ?_⟩
  intro pre suffix placed
  refine ⟨patched pre suffix placed, ?_, ?_⟩
  · rw [patched pre suffix placed, target]
    exact validNew pre suffix placed
  · intro other
    rw [done, linkBytes, List.foldl_nil]
/-- A source library push really emits a PUSH20, so its entire payload stays
outside the scanner's destination set behind any correctly sized code prefix. -/
theorem assembled_library_payload_not_jumpdest {base : Nat}
    {link : Lib → Option (Vector UInt8 20)} {items : List (Item L Lib)} {out : Assembled Lib}
    (assembled : assemble base link items = some out) {k : Nat} {x : Lib}
    (ref : items[k]? = some (.pushLibraryAddress x))
    (pre : Program) (suffix : List UInt8) (placed : size pre = base) (byte : Fin 20) :
    validJumpdest (encode pre ++ encode out.code ++ suffix)
      (base + offset out.code k + 1 + byte.val) = false := by
  have library : out.code[k]? = some (.push 20 ((link x).getD placeholder)) := by
    rw [(assemble_eq assembled).2.1, List.getElem?_map, ref]
    rfl
  have blocked := push_payload_not_jumpdest out.code suffix library byte
  have shifted := validJumpdest_encode_prefix pre (encode out.code ++ suffix)
    (offset out.code k + 1 + byte.val)
  rw [placed] at shifted
  simpa only [List.append_assoc, Nat.add_assoc] using shifted.trans blocked

end Generic

theorem known_link_preserved {Lib : Type} (link : Lib → Option (Vector UInt8 20))
    (addr : Lib → Vector UInt8 20) (x : Lib) (known : Vector UInt8 20)
    (present : link x = some known) : fillLink link addr x = some known := by
  rw [fillLink, present]
  rfl

/-- Already resolved zero bytes are retained, rather than overwritten by a
new address full of JUMPDEST-looking bytes. This concerns PUSH20 data only. -/
theorem resolved_address_witness :
    fillLink (fun _ : Fin 1 => some (Vector.replicate 20 (0 : UInt8)))
      (fun _ => Vector.replicate 20 (0x5b : UInt8)) 0 =
        some (Vector.replicate 20 (0 : UInt8)) ∧
    fillLink (fun _ : Fin 1 => some (Vector.replicate 20 (0 : UInt8)))
      (fun _ => Vector.replicate 20 (0x5b : UInt8)) 0 ≠
        some (Vector.replicate 20 (0x5b : UInt8)) := by
  refine ⟨rfl, ?_⟩
  change some (Vector.replicate 20 (0 : UInt8)) ≠ some (Vector.replicate 20 (0x5b : UInt8))
  decide +kernel

/-- Actual nonempty placeholder metadata is consumed while preserving the
original emitted jump reference behind every correctly sized prefix. -/
theorem linked_reference_witness :
    let items : List (Item (Fin 1) (Fin 1)) := [.pushTag 0, .pushLibraryAddress 0, .tag 0]
    let addr : Fin 1 → Vector UInt8 20 := fun _ => Vector.replicate 20 (0x5b : UInt8)
    ∃ out linked : Assembled (Fin 1), ∃ j : Nat,
    ∃ imm : Vector UInt8 (asmWidths 16 items (0 : Fin 1)).val,
      assemble 16 (fun _ => none) items = some out ∧
      assemble 16 (fillLink (fun _ => none) addr) items = some linked ∧
      out.linkRefs ≠ [] ∧ linked.linkRefs = [] ∧
      out.code[0]? = some (.push (asmWidths 16 items 0) imm) ∧
      linked.code[0]? = some (.push (asmWidths 16 items 0) imm) ∧
      linked.code[j]? = some (.op .JUMPDEST) ∧
      ∀ (pre : Program) (suffix : List UInt8), size pre = 16 →
        validJumpdest (linkBytes (encode pre ++ encode out.code ++ suffix)
          out.linkRefs addr) (ofBytesBE imm.toList) = true ∧
        ∀ byte : Fin 20,
          validJumpdest (linkBytes (encode pre ++ encode out.code ++ suffix)
            out.linkRefs addr) (16 + offset linked.code 1 + 1 + byte.val) = false := by
  let items : List (Item (Fin 1) (Fin 1)) := [.pushTag 0, .pushLibraryAddress 0, .tag 0]
  let addr : Fin 1 → Vector UInt8 20 := fun _ => Vector.replicate 20 (0x5b : UInt8)
  have available : (assemble 16 (fun _ => none) items).isSome := by
    apply assemble_isSome
    · decide
    · intro l member
      have zero : l = 0 := Fin.ext (by have bound := l.isLt; omega)
      subst l
      rfl
    · intro l member
      have zero : l = 0 := Fin.ext (by have bound := l.isLt; omega)
      subst l
      decide +kernel
  obtain ⟨out, assembled⟩ := Option.isSome_iff_exists.mp available
  have nonempty : out.linkRefs ≠ [] := by
    intro empty
    have rows := (assemble_eq assembled).2.2
    rw [empty] at rows
    cases rows
  obtain ⟨linked, j, imm, selected, done, oldCode, newCode, dest, value, offsets, valid⟩ :=
    linked_pushTag_reference addr assembled (k := 0) (l := 0) rfl
  refine ⟨out, linked, j, imm, assembled, selected, nonempty, done, oldCode, newCode, dest, ?_⟩
  intro pre suffix placed
  refine ⟨(valid pre suffix placed).2.1, ?_⟩
  intro byte
  rw [(valid pre suffix placed).1]
  exact assembled_library_payload_not_jumpdest selected (k := 1) (x := 0) rfl
    pre suffix placed byte

/-- info: 'Solidity.Yul.Compilation.linked_pushTag_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms linked_pushTag_reference
/-- info: 'Solidity.Yul.Compilation.known_link_preserved' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms known_link_preserved
/-- info: 'Solidity.Yul.Compilation.resolved_address_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms resolved_address_witness
/-- info: 'Solidity.Yul.Compilation.linked_reference_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms linked_reference_witness
/-- info: 'Solidity.Yul.Compilation.push_payload_not_jumpdest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms push_payload_not_jumpdest
/-- info: 'Solidity.Yul.Compilation.assembled_library_payload_not_jumpdest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms assembled_library_payload_not_jumpdest
end Solidity.Yul.Compilation
