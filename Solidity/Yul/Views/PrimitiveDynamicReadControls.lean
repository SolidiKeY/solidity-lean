import Solidity.Yul.Views.PrimitiveDynamicSequence
import Solidity.Yul.Views.PrimitiveOwnershipStable

namespace Solidity.Yul.Views.Controls

theorem pc_integer_read (entry : {entry // entry ∈ pcLayout.integerTrace}) (i : Nat)
    (bound : i < (pcRegrowRaw ((pcLayout.integerHeader entry).registration account).slot).val) :
    (Source.readLoc packedStepFrame (Source.Loc.stor (τ := .int entry.val.2.1)
      ((pcLayout.integerHeader entry).elementPath i))).run pcRegrow.step.1.2 =
      (.ok (((pcLayout.integerHeader entry).element_type i) ▸
        (pcLayout.integerHeader entry).elementValue pcFixed account i (pcRegrowRaw ((pcLayout.integerHeader entry).element pcFixed account i).slot)),pcRegrow.step.1.2) := by
  let h := pcLayout.integerHeader entry
  have member : h.element pcFixed account i ∈ pcRegrow.next := by
    change _ ∈ pcLayout.primitiveSnapshot pcFixed pcRegrow.nextRaw
    rw [pcregrow_next]
    exact pcLayout.primitive_integer_subset pcFixed pcRegrowRaw _ (pcLayout.integer_element_member pcFixed pcRegrowRaw entry i bound)
  have view := pcRegrow.view rfl (h.element pcFixed account i) member
  have bank := pcLayout.primitive_bank_agreement pcFixed pcRegrow.nextRaw _ member
  rw [pcregrow_next] at view
  exact h.read_element packedStepFrame pcRegrow.step.1.2 pcFixed i pcRegrowRaw bank view

theorem pc_scalar_read (entry : {entry // entry ∈ pcLayout.scalarFamilyTrace}) (i : Nat)
    (bound : i < (pcRegrowRaw ((pcLayout.scalarFamilyHeader entry).registration account).slot).val)
    (v : Source.Val pcEnv.layout (pcEnv.cellTy ((pcLayout.scalarFamilyHeader entry).elementPath i)))
    (decoded : ((pcLayout.scalarFamilyHeader entry).element pcFixed account i).codec.decode
      (((pcLayout.scalarFamilyHeader entry).element pcFixed account i).field.findWord
      (pcRegrowRaw ((pcLayout.scalarFamilyHeader entry).element pcFixed account i).slot)) = some v) :
    (Source.readLoc packedStepFrame (Source.Loc.stor (τ := entry.val.2.1.ty)
      ((pcLayout.scalarFamilyHeader entry).elementPath i))).run pcRegrow.step.1.2 =
      (.ok (((pcLayout.scalarFamilyHeader entry).element_type i) ▸ v),pcRegrow.step.1.2) := by
  let h := pcLayout.scalarFamilyHeader entry
  have member : h.element pcFixed account i ∈ pcRegrow.next := by
    change _ ∈ pcLayout.primitiveSnapshot pcFixed pcRegrow.nextRaw
    rw [pcregrow_next]
    exact pcLayout.primitive_scalar_subset pcFixed pcRegrowRaw _ (pcLayout.scalarFamily_element_member pcFixed pcRegrowRaw entry i bound)
  have view := pcRegrow.view rfl (h.element pcFixed account i) member
  have bank := pcLayout.primitive_bank_agreement pcFixed pcRegrow.nextRaw _ member
  rw [pcregrow_next] at view
  exact h.read_decoded packedStepFrame pcRegrow.step.1.2 pcFixed i pcRegrowRaw v decoded bank view

theorem pc_signed_negative :
    (Source.readLoc (E := pcEnv) packedStepFrame (Source.Loc.stor (τ := .int pcI16) ⟨pcName "ss",[.index 0]⟩)).run pcRegrow.step.1.2 =
      (.ok (.int (-1) (by decide)),pcRegrow.step.1.2) := pc_integer_read pcSEntry 0 (by decide)

theorem pc_signed_tail77 :
    (Source.readLoc (E := pcEnv) packedStepFrame (Source.Loc.stor (τ := .int pcI16) ⟨pcName "ss",[.index 16]⟩)).run pcRegrow.step.1.2 =
      (.ok (.int 77 (by decide)),pcRegrow.step.1.2) := pc_integer_read pcSEntry 16 (by decide)

theorem pc_signed_tail_min :
    (Source.readLoc (E := pcEnv) packedStepFrame (Source.Loc.stor (τ := .int pcI16) ⟨pcName "ss",[.index 17]⟩)).run pcRegrow.step.1.2 =
      (.ok (.int (-32768) (by decide)),pcRegrow.step.1.2) := pc_integer_read pcSEntry 17 (by decide)

theorem pc_unsigned_other_family :
    (Source.readLoc (E := pcEnv) packedStepFrame (Source.Loc.stor (τ := .int pcU24) ⟨pcName "us",[.index 10]⟩)).run pcRegrow.step.1.2 =
      (.ok (.int 77 (by decide)),pcRegrow.step.1.2) := pc_integer_read pcUEntry 10 (by decide)

theorem pc_full_word :
    (Source.readLoc (E := pcEnv) packedStepFrame (Source.Loc.stor (τ := .int .u256) ⟨pcName "ws",[.index 0]⟩)).run pcRegrow.step.1.2 =
      (.ok (.int 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff (by decide)),pcRegrow.step.1.2) := pc_integer_read pcWEntry 0 (by decide)

theorem pc_bool_other_family :
    (Source.readLoc (E := pcEnv) packedStepFrame (Source.Loc.stor (τ := .bool) ⟨pcName "bs",[.index 1]⟩)).run pcRegrow.step.1.2 =
      (.ok (.bool true),pcRegrow.step.1.2) := pc_scalar_read pcBEntry 1 (by decide) (.bool true) rfl

theorem pc_bytes_other_family :
    (Source.readLoc (E := pcEnv) packedStepFrame (Source.Loc.stor (τ := pcBytes.ty) ⟨pcName "ys",[.index 0]⟩)).run pcRegrow.step.1.2 =
      (.ok (.fixedBytes [1,2,3] rfl),pcRegrow.step.1.2) := pc_scalar_read pcYEntry 0 (by decide) (.fixedBytes [1,2,3] rfl) rfl

theorem pc_address_other_family :
    (Source.readLoc (E := pcEnv) packedStepFrame (Source.Loc.stor (τ := .address false) ⟨pcName "zs",[.index 0]⟩)).run pcRegrow.step.1.2 =
      (.ok (.address ⟨0x1234,by decide⟩),pcRegrow.step.1.2) := pc_scalar_read pcZEntry 0 (by decide) (.address ⟨0x1234,by decide⟩) rfl

end Solidity.Yul.Views.Controls
