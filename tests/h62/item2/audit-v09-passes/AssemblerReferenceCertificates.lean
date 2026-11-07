import Solidity.Yul.Compilation.Relocation

/-! Guard conflating absolute and section-relative emitted label immediates or
claiming reference uniqueness without a successful checked assembly. Reuse the
actual assembler/reference/scanner certificates, not finite identity arithmetic.
A nonzero-base witness checks the correct absolute destination and proves that
the raw relative value differs from that destination. No jump execution, gas,
G24 or native realization is asserted, and no new assembler/interface is defined. Relative
relocation retains checked success at both placements and stable widths; no
unconditional law across a push-width boundary is asserted. -/
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
/-- Relative values stay section-local under stable-width relocation; actual
scanner targets still add the new base. All success/width premises are retained. -/
theorem relocated_relative_reference {base delta : Nat} {items : List (Item L Lib)}
    {link : Lib → Option (Vector UInt8 20)} {a b : Assembled Lib}
    (ha : assemble base link items = some a)
    (hb : assemble (delta + base) link items = some b)
    (widths : asmWidths (delta + base) items = asmWidths base items)
    {k : Nat} {l : L} (ref : items[k]? = some (.pushTagRel l)) :
    ∃ j : Nat, ∃ x y,
      a.code[k]? = some (.push (asmWidths base items l) x) ∧
      b.code[k]? = some (.push (asmWidths (delta + base) items l) y) ∧
      a.code[j]? = some (.op .JUMPDEST) ∧ b.code[j]? = some (.op .JUMPDEST) ∧
      ofBytesBE y.toList = ofBytesBE x.toList ∧
      ∀ (pre : Program) (suffix : List UInt8), size pre = delta + base →
        validJumpdest (encode pre ++ encode b.code ++ suffix)
          (delta + base + ofBytesBE y.toList) = true := by
  obtain ⟨j, x, hj, destA, codeA, valueA, validA⟩ := assemble_pushTagRel ha ref
  obtain ⟨other, y, ho, destB, codeB, valueB, validB⟩ := assemble_pushTagRel hb ref
  have same : other = j := Option.some.inj (ho.symm.trans hj)
  subst other
  refine ⟨j, x, y, codeA, codeB, destA, destB, ?_, validB⟩
  rw [valueB, valueA, relocated_offsets ha hb widths j]

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

namespace LeadingRelativeFixture
/-- Leading tag makes its section-relative offset zero independently of width. -/
def items : List (Item (Fin 1) Empty) := [.tag 0, .pushTagRel 0]
def output : Assembled Empty := ⟨[.op .JUMPDEST, .push ⟨1, by decide⟩ #v[0]], []⟩

theorem widths (base : Nat) (positive : 0 < base) (small : base < 256) :
    asmWidths base items = fun _ => (1 : Fin 33) := by
  have byte : byteWidth base = 1 := by
    rw [byteWidth, if_neg (by omega), Nat.div_eq_of_lt small, byteWidth, if_pos rfl]
  have pinned (w : Fin 33) : widen base items (fun _ => w) =
      fun _ => (⟨min 32 (max w.val 1), by omega⟩ : Fin 33) := by
    funext l
    have zero : l = 0 := Fin.ext (by have bound := l.isLt; omega)
    subst l
    apply Fin.ext
    change min 32 (max w.val (byteWidth base)) = min 32 (max w.val 1)
    rw [byte]
  unfold asmWidths
  rw [fixWidths, pinned 0]
  change fixWidths base items (fun _ => (1 : Fin 33)) = _
  rw [fixWidths, pinned 1]
  rfl

theorem assembled (base : Nat) (positive : 0 < base) (small : base < 256) :
    assemble base (fun _ => none) items = some output := by
  rw [assemble, widths base positive small]
  have checked : layoutOk base items (fun _ => (1 : Fin 33)) = true := by
    have fit : decide (base < 256) = true := decide_eq_true small
    change (true && true && (decide (base < 256) && true)) = true
    rw [fit]
    rfl
  rw [checked]
  rfl

/-- A nonzero delta15 is witnessed by actual assembly at1and16, including the
stable-width premise; its relative word stays fixed and its absolute base moves. -/
theorem witness :
    assemble 1 (fun _ => none) items = some output ∧
    assemble 16 (fun _ => none) items = some output ∧
    asmWidths 16 items = asmWidths 1 items ∧
    ∃ j : Nat, ∃ x y,
      output.code[1]? = some (.push (asmWidths 1 items (0 : Fin 1)) x) ∧
      output.code[1]? = some (.push (asmWidths 16 items (0 : Fin 1)) y) ∧
      output.code[j]? = some (.op .JUMPDEST) ∧
      ofBytesBE y.toList = ofBytesBE x.toList ∧
      16 + ofBytesBE y.toList = 15 + (1 + ofBytesBE x.toList) ∧
      ∀ (pre : Program) (suffix : List UInt8), size pre = 16 →
        validJumpdest (encode pre ++ encode output.code ++ suffix)
          (16 + ofBytesBE y.toList) = true := by
  have old := assembled 1 (by decide) (by decide)
  have moved := assembled 16 (by decide) (by decide)
  have stable : asmWidths 16 items = asmWidths 1 items := by
    rw [widths 16 (by decide) (by decide), widths 1 (by decide) (by decide)]
  obtain ⟨j, x, y, codeA, codeB, destA, destB, value, valid⟩ :=
    relocated_relative_reference (base := 1) (delta := 15) old moved stable
      (k := 1) (l := 0) rfl
  refine ⟨old, moved, stable, j, x, y, codeA, codeB, destA, value, ?_, valid⟩
  omega
/-- This is a failed stable-width premise, not a claim that assembly at0fails. -/
theorem zero_width_refusal : asmWidths 0 items ≠ asmWidths 16 items := by
  have fixed : widen 0 items (fun _ => (0 : Fin 33)) = fun _ => (0 : Fin 33) := by
    funext l
    have zero : l = 0 := Fin.ext (by have bound := l.isLt; omega)
    subst l
    apply Fin.ext
    change min 32 (max 0 (byteWidth 0)) = 0
    rw [byteWidth, if_pos rfl]
    rfl
  have atZero : asmWidths 0 items = fun _ => (0 : Fin 33) := by
    unfold asmWidths
    rw [fixWidths, fixed]
    rfl
  intro equal
  have values := congrArg (fun w => (w (0 : Fin 1)).val) equal
  rw [atZero, widths 16 (by decide) (by decide)] at values
  cases values

end LeadingRelativeFixture

/-- info: 'Solidity.Yul.Compilation.assembled_tag_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assembled_tag_unique
/-- info: 'Solidity.Yul.Compilation.assembled_reference_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assembled_reference_pair
/-- info: 'Solidity.Yul.Compilation.assembled_reference_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms assembled_reference_witness
/-- info: 'Solidity.Yul.Compilation.relocated_relative_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms relocated_relative_reference
/-- info: 'Solidity.Yul.Compilation.LeadingRelativeFixture.items' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeadingRelativeFixture.items
/-- info: 'Solidity.Yul.Compilation.LeadingRelativeFixture.output' does not depend on any axioms -/
#guard_msgs in
#print axioms LeadingRelativeFixture.output
/-- info: 'Solidity.Yul.Compilation.LeadingRelativeFixture.widths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeadingRelativeFixture.widths
/-- info: 'Solidity.Yul.Compilation.LeadingRelativeFixture.assembled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeadingRelativeFixture.assembled
/-- info: 'Solidity.Yul.Compilation.LeadingRelativeFixture.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeadingRelativeFixture.witness
/-- info: 'Solidity.Yul.Compilation.LeadingRelativeFixture.zero_width_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeadingRelativeFixture.zero_width_refusal
end Solidity.Yul.Compilation
