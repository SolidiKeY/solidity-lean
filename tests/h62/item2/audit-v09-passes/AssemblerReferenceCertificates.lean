import Solidity.Backend.Assembler

/-! Guard conflating absolute and section-relative emitted label immediates or
claiming reference uniqueness without a successful checked assembly. Reuse the
actual assembler/reference/scanner certificates, not finite identity arithmetic.
A nonzero-base witness checks the correct absolute destination and proves that
the raw relative value differs from that destination. No jump execution, gas,
G24 or native realization is asserted, and no new assembler/interface is defined. -/
namespace Solidity.Yul.Compilation
open Backend

section Generic
variable {L Lib : Type} [DecidableEq L]

/-- Successful checked assembly supplies the distinct-tag premise for uniqueness. -/
theorem assembled_tag_unique {base : Nat} {items : List (Item L Lib)}
    {link : Lib → Option (Vector UInt8 20)} {out : Assembled Lib}
    (assembled : assemble base link items = some out) {l : L} {i j : Nat}
    (left : items[i]? = some (.tag l)) (right : items[j]? = some (.tag l)) : i = j := by
  have checked := (assemble_eq assembled).1
  simp only [layoutOk, Bool.and_eq_true, decide_eq_true_eq] at checked
  have hi := tagIndex_unique checked.1.1 left
  have hj := tagIndex_unique checked.1.1 right
  exact Option.some.inj (hi.symm.trans hj)

/-- Both actual emitted pushes name one unique source tag/JUMPDEST. The relative
word becomes the absolute word only after adding the same checked section base. -/
theorem assembled_reference_pair {base : Nat} {items : List (Item L Lib)}
    {link : Lib → Option (Vector UInt8 20)} {out : Assembled Lib}
    (assembled : assemble base link items = some out) {l : L} {a r : Nat}
    (absolute : items[a]? = some (.pushTag l))
    (relative : items[r]? = some (.pushTagRel l)) :
    ∃ j : Nat, ∃ absImm relImm : Vector UInt8 (asmWidths base items l).val,
      items[j]? = some (.tag l) ∧
      (∀ k : Nat, items[k]? = some (.tag l) → k = j) ∧
      out.code[j]? = some (.op .JUMPDEST) ∧
      out.code[a]? = some (.push (asmWidths base items l) absImm) ∧
      out.code[r]? = some (.push (asmWidths base items l) relImm) ∧
      ofBytesBE absImm.toList = base + ofBytesBE relImm.toList ∧
      ∀ (pre : Program) (suffix : List UInt8), size pre = base →
        validJumpdest (encode pre ++ encode out.code ++ suffix)
          (ofBytesBE absImm.toList) = true ∧
        validJumpdest (encode pre ++ encode out.code ++ suffix)
          (base + ofBytesBE relImm.toList) = true := by
  obtain ⟨j, absImm, hj, dest, absCode, absValue, absOffset, absValid⟩ :=
    assemble_pushTag assembled absolute
  obtain ⟨k, relImm, hk, relDest, relCode, relValue, relValid⟩ :=
    assemble_pushTagRel assembled relative
  have equal : k = j := Option.some.inj (hk.symm.trans hj)
  subst k
  have tag : items[j]? = some (.tag l) := tagIndex_get hj
  refine ⟨j, absImm, relImm, tag, ?_, dest, absCode, relCode, ?_, ?_⟩
  · intro other present
    exact assembled_tag_unique assembled present tag
  · rw [absValue, relValue]
  · intro pre suffix placed
    exact ⟨absValid pre suffix placed, relValid pre suffix placed⟩
end Generic

/-- A genuinely successful nonzero placement supplies both emitted words and
scanner validity of the correct target. The raw relative word is a different
target; this does not claim it could never be some other valid JUMPDEST. -/
theorem assembled_reference_witness :
    let items : List (Item (Fin 1) Empty) := [.pushTag 0, .pushTagRel 0, .tag 0]
    ∃ out : Assembled Empty,
      assemble 16 (fun _ => none) items = some out ∧
      ∃ j : Nat, ∃ absImm relImm : Vector UInt8 (asmWidths 16 items 0).val,
        out.code[j]? = some (.op .JUMPDEST) ∧
        out.code[0]? = some (.push (asmWidths 16 items 0) absImm) ∧
        out.code[1]? = some (.push (asmWidths 16 items 0) relImm) ∧
        ofBytesBE absImm.toList = 16 + ofBytesBE relImm.toList ∧
        ofBytesBE absImm.toList ≠ ofBytesBE relImm.toList ∧
        validJumpdest (encode (List.replicate 16 (.op .STOP)) ++ encode out.code)
          (ofBytesBE absImm.toList) = true := by
  let items : List (Item (Fin 1) Empty) := [.pushTag 0, .pushTagRel 0, .tag 0]
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
  obtain ⟨j, absImm, relImm, tag, unique, dest, absCode, relCode, value, valid⟩ :=
    assembled_reference_pair assembled (a := 0) (r := 1) (l := 0) rfl rfl
  refine ⟨out, assembled, j, absImm, relImm, dest, absCode, relCode, value, ?_, ?_⟩
  · omega
  · have checked := (valid (List.replicate 16 (.op .STOP)) [] (by decide +kernel)).1
    simpa only [List.append_nil] using checked

/-- info: 'Solidity.Yul.Compilation.assembled_tag_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assembled_tag_unique
/-- info: 'Solidity.Yul.Compilation.assembled_reference_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assembled_reference_pair
/-- info: 'Solidity.Yul.Compilation.assembled_reference_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assembled_reference_witness
end Solidity.Yul.Compilation
