import Solidity.Backend.Executable.Assembly

/-! Linked section consumers with an actual enclosing encoded prefix. Relocated
backedges and PUSH-data exclusion are byte-layout facts, not execution of JUMP.
Assembly success retains its real tag/word-fit checks; no gas/code admission or
source-frame correspondence is assumed or inferred. -/
namespace Solidity.Backend.Executable.Relocation

/-- Earlier instruction indices have strictly earlier byte offsets, rather
than merely an ordering in an assumed external layout. -/
theorem offset_before {p : Program} {j k : Nat} (earlier : j < k)
    (present : k < p.length) : offset p j < offset p k := by
  have small : j < (p.take k).length := by
    rw [List.length_take]
    omega
  have h := offset_lt_size small
  change size ((p.take k).take j) < size (p.take k) at h
  rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt earlier)] at h
  exact h

/-- Linking, real assembly offsets, absolute backward operands and jump scans
compose for any encoded prefix and arbitrary suffix. Caller execution and
stack capacity are separate obligations, exercised by the concrete client. -/
theorem linked_backedge {L Lib : Type} [DecidableEq L]
    (pre : Program) (suffix : List UInt8) (addr : Lib → Vector UInt8 20)
    {link : Lib → Option (Vector UInt8 20)} {items : List (Item L Lib)}
    {out : Assembled Lib} (assembled : assemble (size pre) link items = some out)
    {j k : Nat} {label : L} (tag : tagIndex items label = some j)
    (reference : items[k]? = some (.pushTag label)) (earlier : j < k) :
    ∃ linked imm,
      assemble (size pre) (fillLink link addr) items = some linked ∧
      linked.linkRefs = [] ∧
      linkBytes (encode pre ++ encode out.code ++ suffix) out.linkRefs addr =
        encode pre ++ encode linked.code ++ suffix ∧
      linked.code.length = items.length ∧
      (∀ n, offset linked.code n = itemOffset (asmWidths (size pre) items) items n ∧
        offset linked.code n = offset out.code n) ∧
      size linked.code = itemOffset (asmWidths (size pre) items) items items.length ∧
      linked.code[j]? = some (.op .JUMPDEST) ∧
      linked.code[k]? = some (.push (asmWidths (size pre) items label) imm) ∧
      linked.code[k]? = out.code[k]? ∧
      ofBytesBE imm.toList = size pre + itemOffset (asmWidths (size pre) items) items j ∧
      ofBytesBE imm.toList < 256 ^ (asmWidths (size pre) items label).val ∧
      ofBytesBE imm.toList < size pre + offset linked.code k ∧
      validJumpdest (encode pre ++ encode linked.code ++ suffix) (ofBytesBE imm.toList) = true ∧
      (∀ n, InPushData (encode linked.code ++ suffix) n →
        validJumpdest (encode pre ++ encode linked.code ++ suffix) (size pre + n) = false) := by
  obtain ⟨linked, ran, resolved, patch, offsets, unchanged⟩ := link_patch addr assembled
  obtain ⟨len, layout, total⟩ := assemble_layout ran
  obtain ⟨actual, imm, found, dest, push, value, _, _⟩ := assemble_pushTag ran reference
  have same : actual = j := Option.some.inj (found.symm.trans tag)
  subst actual
  obtain ⟨actual, found, _, _, _, fit⟩ := assemble_ref ran reference rfl
  have same : actual = j := Option.some.inj (found.symm.trans tag)
  subst actual
  have present : k < linked.code.length := by
    rw [len]
    exact (List.getElem?_eq_some_iff.mp reference).1
  have back : offset linked.code j < offset linked.code k := offset_before earlier present
  refine ⟨linked, imm, ran, resolved, patch pre suffix rfl, len,
    fun n => ⟨layout n, offsets n⟩, total, dest, push,
    unchanged k (.pushTag label) reference (fun x bad => by cases bad),
    value.trans (congrArg (fun n => size pre + n) (layout j)), ?_, ?_, ?_, ?_⟩
  · rw [value]
    exact fit
  · rw [value]
    omega
  · rw [value, List.append_assoc, validJumpdest_encode_prefix]
    exact validJumpdest_encode_append linked.code suffix dest
  · intro n data
    rw [List.append_assoc, validJumpdest_encode_prefix]
    apply Bool.eq_false_iff.mpr
    intro valid
    exact ((validJumpdest_iff _ _).mp valid).2 data

/-- info: 'Solidity.Backend.Executable.Relocation.offset_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms offset_before
/-- info: 'Solidity.Backend.Executable.Relocation.linked_backedge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linked_backedge
end Solidity.Backend.Executable.Relocation
