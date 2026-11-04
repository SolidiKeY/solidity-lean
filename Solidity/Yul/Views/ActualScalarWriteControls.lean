import Solidity.Yul.Views.ActualScalarWrite
import Solidity.Yul.Views.RetainedCompoundControls

/-! Actual scalar Source write and the existing retained coordinate share one
physical field. Nonzero padding/siblings survive. Default writes keep actual
administrative effects, distinct from unchanged preparation. Fixed hashes below
are the existing synthetic layout controls, not compiler Keccak observations. -/
namespace Solidity.Yul.Views.Controls

def asWrite := actualScalarWrite packedStepFrame rhC3.path rhC3.codec rhC3.slot
  (Source.intWrap rcU16 154) rhRaw0 agShrink.2

theorem as_coordinate : (rhC3.path,rhC3.slot.val,rhC3.field.offset,rhC3.field.width)=(rlPath,1000,0,2) := rfl

theorem as_same_compound_store (G : Source.Glob agEnv) : asWrite.1.2=(rcompound G).1.2 := rfl

theorem as_raw_word : (asWrite.2 1000).val=154+88*65536+77*2^32+2^240 := rfl

theorem as_reencode : encodeScalarPath rhC3.path rhC3.codec rhC3.slot
    (asWrite.1.2.2.ex.world.accounts account).storage rhRaw0=some asWrite.2 :=
  actualScalarWrite_reencode packedStepFrame rhC3.path rhC3.codec rhC3.slot _ rhRaw0 agShrink.2 rfl rfl

/-- The same actual compound-expression state reconstructs the patched word. -/
theorem as_compound_reencode (G : Source.Glob agEnv) : encodeScalarPath rhC3.path rhC3.codec rhC3.slot
    ((rcompound G).1.2.2.ex.world.accounts account).storage rhRaw0=some asWrite.2 := by
  first | (simp only;done) | decide | omega | skip
  rw [← as_same_compound_store G]
  exact as_reencode

theorem as_other_raw : asWrite.2 2000=rhRaw0 2000 := rfl

theorem as_unowned_byte : slotBytes asWrite.2 (1000*32+30)=slotBytes rhRaw0 (1000*32+30) :=
  actualScalarWrite_unowned_byte packedStepFrame rhC3.path rhC3.codec rhC3.slot _ rhRaw0 agShrink.2 rfl rfl _ (by decide) (by unfold scalarByteUnowned; decide)

def asDefault := actualScalarWrite packedStepFrame rhC3.path rhC3.codec rhC3.slot
  (Source.intWrap rcU16 0) rhRaw0 agState

theorem as_explicit_default :
    (agState.2.ex.world.accounts account).storage.cell rhC3.path=none ∧
    (asDefault.1.2.2.ex.world.accounts account).storage.cell rhC3.path=some (Source.intWrap rcU16 0) := ⟨rfl,rfl⟩

theorem as_static : actualScalarWrite rcompoundStatic rhC3.path rhC3.codec rhC3.slot
    (Source.intWrap rcU16 154) rhRaw0 agShrink.2=((.error (.revert []),agShrink.2),rhRaw0) :=
  actualScalarWrite_static rcompoundStatic rhC3.path rhC3.codec rhC3.slot _ rhRaw0 agShrink.2 rfl

theorem as_wrong_clean_padding : (asWrite.2 1000).val≠154+88*65536+77*2^32 := by decide
end Solidity.Yul.Views.Controls
