import Solidity.Backend.Control

/-! Actual assembler placement, under an explicit stable-width premise.
Moving a section across a PUSH-width boundary can change internal offsets;
no unconditional byte-offset relocation law is asserted. -/
namespace Solidity.Yul.Compilation
open Backend

section Generic
variable {L Lib : Type} [DecidableEq L]

theorem relocated_offsets {base delta : Nat} {items : List (Item L Lib)}
    {link : Lib → Option (Vector UInt8 20)} {a b : Assembled Lib}
    (ha : assemble base link items = some a)
    (hb : assemble (delta + base) link items = some b)
    (widths : asmWidths (delta + base) items = asmWidths base items) (k : Nat) :
    offset b.code k = offset a.code k := by
  rw [(assemble_layout hb).2.1 k, (assemble_layout ha).2.1 k, widths]

/-- Both pushes are actual emitted instructions. The relocated immediate
moves by `delta` and remains a scanner-valid JUMPDEST in any matching prefix.
Success and stable widths are checked inputs, not a runtime simulation. -/
theorem relocated_jump {base delta : Nat} {items : List (Item L Lib)}
    {link : Lib → Option (Vector UInt8 20)} {a b : Assembled Lib}
    (ha : assemble base link items = some a)
    (hb : assemble (delta + base) link items = some b)
    (widths : asmWidths (delta + base) items = asmWidths base items)
    {k : Nat} {l : L} (ref : items[k]? = some (.pushTag l)) :
    ∃ j : Nat, ∃ x y,
      a.code[k]? = some (.push (asmWidths base items l) x) ∧
      b.code[k]? = some (.push (asmWidths (delta + base) items l) y) ∧
      a.code[j]? = some (.op .JUMPDEST) ∧ b.code[j]? = some (.op .JUMPDEST) ∧
      ofBytesBE y.toList = delta + ofBytesBE x.toList ∧
      ∀ (pre : Program) (suffix : List UInt8), size pre = delta + base →
        validJumpdest (encode pre ++ encode b.code ++ suffix) (ofBytesBE y.toList) = true := by
  obtain ⟨j, x, hj, hja, hka, hxa, _hxtag, _hvalid⟩ := assemble_pushTag ha ref
  obtain ⟨j', y, hj', hjb, hkb, hyb, _hytag, hvalid⟩ := assemble_pushTag hb ref
  have he : j' = j := Option.some.inj (hj'.symm.trans hj)
  subst j'
  refine ⟨j, x, y, hka, hkb, hja, hjb, ?_, hvalid⟩
  rw [hxa, hyb, relocated_offsets ha hb widths j]
  omega

end Generic

/-- Finite label identity and a nonzero placement witness. -/
def jumpImage : List (Item (Fin 1) Empty) :=
  [.pushTag 0, .instr (.op .JUMP), .tag 0]

private theorem byteWidth_small (n : Nat) (positive : 0 < n) (small : n < 256) :
    byteWidth n = 1 := by
  rw [byteWidth, if_neg (by omega), Nat.div_eq_of_lt small, byteWidth, if_pos rfl]

private theorem widen_image (base width next : Nat) (hw : width < 33) (_hn : next < 33)
    (hbyte : byteWidth (base + (1 + width + 1)) = next) :
    widen base jumpImage (fun _ => (⟨width, hw⟩ : Fin 33)) =
      fun _ => (⟨min 32 (max width next), by omega⟩ : Fin 33) := by
  funext l
  have hl : l = (0 : Fin 1) := Fin.ext (by have h := l.isLt; omega)
  subst l
  apply Fin.ext
  have hoff : tagOffset (fun _ => (⟨width, hw⟩ : Fin 33)) jumpImage 0 =
      1 + width + 1 := by
    change width + 1 + 1 = 1 + width + 1
    omega
  simp only [widen, hoff, hbyte]

private theorem widths_small (base : Nat) (h : base + 3 < 256) :
    asmWidths base jumpImage = fun _ => (1 : Fin 33) := by
  have h0 : widen base jumpImage (fun _ => (0 : Fin 33)) = fun _ => (1 : Fin 33) :=
    widen_image base 0 1 (by decide) (by decide) (byteWidth_small _ (by omega) (by omega))
  have h1 : widen base jumpImage (fun _ => (1 : Fin 33)) = fun _ => (1 : Fin 33) :=
    widen_image base 1 1 (by decide) (by decide) (byteWidth_small _ (by omega) (by omega))
  unfold asmWidths
  rw [fixWidths, h0]
  change fixWidths base jumpImage (fun _ => (1 : Fin 33)) = _
  rw [fixWidths, h1]
  rfl

private theorem widths_boundary : asmWidths 253 jumpImage = fun _ => (2 : Fin 33) := by
  have bw256 : byteWidth 256 = 2 := by
    rw [byteWidth, if_neg (by decide)]
    change byteWidth 1 + 1 = 2
    rw [byteWidth_small 1 (by decide) (by decide)]
  have bw257 : byteWidth 257 = 2 := by
    rw [byteWidth, if_neg (by decide)]
    change byteWidth 1 + 1 = 2
    rw [byteWidth_small 1 (by decide) (by decide)]
  have h0 : widen 253 jumpImage (fun _ => (0 : Fin 33)) = fun _ => (1 : Fin 33) :=
    widen_image 253 0 1 (by decide) (by decide) (byteWidth_small 255 (by decide) (by decide))
  have h1 : widen 253 jumpImage (fun _ => (1 : Fin 33)) = fun _ => (2 : Fin 33) :=
    widen_image 253 1 2 (by decide) (by decide) bw256
  have h2 : widen 253 jumpImage (fun _ => (2 : Fin 33)) = fun _ => (2 : Fin 33) :=
    widen_image 253 2 2 (by decide) (by decide) bw257
  unfold asmWidths
  rw [fixWidths, h0]
  change fixWidths 253 jumpImage (fun _ => (1 : Fin 33)) = _
  rw [fixWidths, h1]
  change fixWidths 253 jumpImage (fun _ => (2 : Fin 33)) = _
  rw [fixWidths, h2]
  rfl

example : (assemble 0 (fun _ => none) jumpImage).map (fun a => encode a.code) =
    some [0x60, 0x03, 0x56, 0x5b] := by
  rw [assemble, widths_small 0 (by decide)]
  decide +kernel
example : (assemble 16 (fun _ => none) jumpImage).map (fun a => encode a.code) =
    some [0x60, 0x13, 0x56, 0x5b] := by
  rw [assemble, widths_small 16 (by decide)]
  decide +kernel
example : (assemble 252 (fun _ => none) jumpImage).map (fun a => encode a.code) =
    some [0x60, 0xff, 0x56, 0x5b] := by
  rw [assemble, widths_small 252 (by decide)]
  decide +kernel
example : (assemble 253 (fun _ => none) jumpImage).map (fun a => encode a.code) =
    some [0x61, 0x01, 0x01, 0x56, 0x5b] := by
  rw [assemble, widths_boundary]
  decide +kernel
example : asmWidths 253 jumpImage (0 : Fin 1) ≠ asmWidths 0 jumpImage 0 := by
  rw [widths_boundary, widths_small 0 (by decide)]
  decide +kernel

def imageAt (base : Nat) : Assembled Empty :=
  (assemble base (fun _ => none) jumpImage).getD ⟨[], []⟩

theorem stable_image_widths : asmWidths 16 jumpImage = asmWidths 0 jumpImage := by
  rw [widths_small 16 (by decide), widths_small 0 (by decide)]

private theorem image_success (base : Nat) (h : base + 3 < 256) :
    assemble base (fun _ => none) jumpImage = some (imageAt base) := by
  unfold imageAt
  rw [assemble, widths_small base h]
  have ok : layoutOk base jumpImage (fun _ => (1 : Fin 33)) = true := by
    have hb : decide (base + 3 < 256) = true := decide_eq_true h
    change (true && true && (decide (base + 3 < 256) && true)) = true
    rw [hb]
    rfl
  rw [ok]
  rfl

example : ∃ j : Nat, ∃ x y,
    (imageAt 0).code[0]? = some (.push (asmWidths 0 jumpImage 0) x) ∧
    (imageAt 16).code[0]? = some (.push (asmWidths 16 jumpImage 0) y) ∧
    (imageAt 0).code[j]? = some (.op .JUMPDEST) ∧
    (imageAt 16).code[j]? = some (.op .JUMPDEST) ∧
    ofBytesBE y.toList = 16 + ofBytesBE x.toList ∧
    ∀ (pre : Program) (suffix : List UInt8), size pre = 16 →
      validJumpdest (encode pre ++ encode (imageAt 16).code ++ suffix)
        (ofBytesBE y.toList) = true :=
  relocated_jump (base := 0) (delta := 16) (link := fun _ => none)
    (a := imageAt 0) (b := imageAt 16) (image_success 0 (by decide))
    (image_success 16 (by decide)) stable_image_widths (k := 0) (l := 0) rfl

#print axioms relocated_offsets
#print axioms relocated_jump
end Solidity.Yul.Compilation
