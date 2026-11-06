import Solidity.Backend.AbiEntry.CalldataWordInterface
import Solidity.Yul.Views.AbiCalldataAgreement

/-! Reuse the published byte-window padding and reader bound. This is raw word
access, with no ABI head/span/canonicality admission added. -/
namespace Solidity.Backend.AbiEntry.CalldataWord

theorem window (bytes : List UInt8) (offset width : Nat) :
    Solidity.AbiEntry.bytesAt bytes offset width=Source.fitBytes width (bytes.drop offset) :=
  Yul.Views.abi_readBytes_fit bytes offset width

theorem load (frame : Source.Fr) (offset : Nat) :
    Solidity.AbiEntry.load frame.cd offset=Source.cdWordAt frame offset := by
  have fold : Solidity.AbiEntry.load frame.cd offset=
      Source.beValue (Solidity.AbiEntry.bytesAt frame.cd offset 32)%Solidity.AbiEntry.W := by
    simp only [Solidity.AbiEntry.load,Source.beValue,Solidity.AbiEntry.bytesAt,List.foldl_map]
  have bound : Source.beValue (Source.fitBytes 32 (frame.cd.drop offset))<
      256^(Source.fitBytes 32 (frame.cd.drop offset)).length :=
    Yul.Views.scalar_beValue_bound _
  have width : (256 : Nat)^32=Solidity.AbiEntry.W := by decide
  rw [Source.fitBytes_length,width] at bound
  rw [fold,window,Nat.mod_eq_of_lt bound]
  rfl

def certificate : Interface.CalldataWordCertificate where
  window := window
  load := load

/-- info: 'Solidity.Backend.AbiEntry.CalldataWord.window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms window
/-- info: 'Solidity.Backend.AbiEntry.CalldataWord.load' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms load
/-- info: 'Solidity.Backend.AbiEntry.CalldataWord.certificate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.CalldataWord
