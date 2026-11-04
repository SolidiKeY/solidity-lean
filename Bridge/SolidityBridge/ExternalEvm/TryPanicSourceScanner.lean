import SolidityBridge.ExternalEvm.BoundedScannerPrefix
import SolidityBridge.ExternalEvm.TryMemoryCode

/-! H8 original-runtime consumers of the published H7 bounded scanner.
Membership is about these complete pinned arrays. It is not path attainment,
installation, source adequacy or native scanner correctness. -/
namespace Solidity.Evm.External.TryPanicSourceScanner
open EvmYul EvmYul.EVM Assembly TryMemoryCode
open private get_append legacyChunk0 legacyChunk0_size legacyChunk1_size legacyChunk2_size legacyChunk3_size legacyChunk4_size legacyChunk5_size legacyChunk6_size legacyChunk7_size legacyChunk8_size legacyChunk9_size legacyChunk10_size legacyChunk11_size legacyChunk12_size legacyChunk13_size legacyChunk14_size legacyChunk15_size legacyChunk16_size legacyChunk17_size legacyChunk18_size legacyChunk19_size legacyChunk20_size legacyChunk21_size legacyChunk22_size legacyChunk23_size legacyChunk24_size legacyChunk25_size legacyChunk26_size legacyChunk27_size legacyChunk28_size legacyChunk29_size legacyChunk30_size legacyChunk31_size legacyChunk32_size legacyChunk33_size legacyChunk34_size viaIRChunk0 viaIRChunk0_size viaIRChunk1_size viaIRChunk2_size viaIRChunk3_size viaIRChunk4_size viaIRChunk5_size viaIRChunk6_size viaIRChunk7_size viaIRChunk8_size viaIRChunk9_size viaIRChunk10_size viaIRChunk11_size viaIRChunk12_size viaIRChunk13_size viaIRChunk14_size viaIRChunk15_size viaIRChunk16_size viaIRChunk17_size viaIRChunk18_size viaIRChunk19_size viaIRChunk20_size viaIRChunk21_size viaIRChunk22_size viaIRChunk23_size viaIRChunk24_size viaIRChunk25_size viaIRChunk26_size viaIRChunk27_size viaIRChunk28_size viaIRChunk29_size viaIRChunk30_size viaIRChunk31_size viaIRChunk32_size viaIRChunk33_size viaIRChunk34_size viaIRChunk35_size viaIRChunk36_size viaIRChunk37_size viaIRChunk38_size viaIRChunk39_size viaIRChunk40_size from SolidityBridge.ExternalEvm.TryMemoryCode

private theorem legacy_leaf0_h7 : legacyChunk0.get? 0 = some 0x60 := rfl
private theorem legacy_byte0_h7 : legacyRuntime.get? 0 = some 0x60 := by
  norm_num only [legacyRuntime, get_append, ByteArray.size_append, legacyChunk0_size, legacyChunk1_size, legacyChunk2_size, legacyChunk3_size, legacyChunk4_size, legacyChunk5_size, legacyChunk6_size, legacyChunk7_size, legacyChunk8_size, legacyChunk9_size, legacyChunk10_size, legacyChunk11_size, legacyChunk12_size, legacyChunk13_size, legacyChunk14_size, legacyChunk15_size, legacyChunk16_size, legacyChunk17_size, legacyChunk18_size, legacyChunk19_size, legacyChunk20_size, legacyChunk21_size, legacyChunk22_size, legacyChunk23_size, legacyChunk24_size, legacyChunk25_size, legacyChunk26_size, legacyChunk27_size, legacyChunk28_size, legacyChunk29_size, legacyChunk30_size, legacyChunk31_size, legacyChunk32_size, legacyChunk33_size, legacyChunk34_size, legacy_leaf0_h7]
  simp only [ite_true]

private theorem legacy_leaf1_h7 : legacyChunk0.get? 1 = some 0x80 := rfl
private theorem legacy_byte1_h7 : legacyRuntime.get? 1 = some 0x80 := by
  norm_num only [legacyRuntime, get_append, ByteArray.size_append, legacyChunk0_size, legacyChunk1_size, legacyChunk2_size, legacyChunk3_size, legacyChunk4_size, legacyChunk5_size, legacyChunk6_size, legacyChunk7_size, legacyChunk8_size, legacyChunk9_size, legacyChunk10_size, legacyChunk11_size, legacyChunk12_size, legacyChunk13_size, legacyChunk14_size, legacyChunk15_size, legacyChunk16_size, legacyChunk17_size, legacyChunk18_size, legacyChunk19_size, legacyChunk20_size, legacyChunk21_size, legacyChunk22_size, legacyChunk23_size, legacyChunk24_size, legacyChunk25_size, legacyChunk26_size, legacyChunk27_size, legacyChunk28_size, legacyChunk29_size, legacyChunk30_size, legacyChunk31_size, legacyChunk32_size, legacyChunk33_size, legacyChunk34_size, legacy_leaf1_h7]
  simp only [ite_true]

private theorem legacy_leaf2_h7 : legacyChunk0.get? 2 = some 0x60 := rfl
private theorem legacy_byte2_h7 : legacyRuntime.get? 2 = some 0x60 := by
  norm_num only [legacyRuntime, get_append, ByteArray.size_append, legacyChunk0_size, legacyChunk1_size, legacyChunk2_size, legacyChunk3_size, legacyChunk4_size, legacyChunk5_size, legacyChunk6_size, legacyChunk7_size, legacyChunk8_size, legacyChunk9_size, legacyChunk10_size, legacyChunk11_size, legacyChunk12_size, legacyChunk13_size, legacyChunk14_size, legacyChunk15_size, legacyChunk16_size, legacyChunk17_size, legacyChunk18_size, legacyChunk19_size, legacyChunk20_size, legacyChunk21_size, legacyChunk22_size, legacyChunk23_size, legacyChunk24_size, legacyChunk25_size, legacyChunk26_size, legacyChunk27_size, legacyChunk28_size, legacyChunk29_size, legacyChunk30_size, legacyChunk31_size, legacyChunk32_size, legacyChunk33_size, legacyChunk34_size, legacy_leaf2_h7]
  simp only [ite_true]

private theorem legacy_leaf4_h7 : legacyChunk0.get? 4 = some 0x52 := rfl
private theorem legacy_byte4_h7 : legacyRuntime.get? 4 = some 0x52 := by
  norm_num only [legacyRuntime, get_append, ByteArray.size_append, legacyChunk0_size, legacyChunk1_size, legacyChunk2_size, legacyChunk3_size, legacyChunk4_size, legacyChunk5_size, legacyChunk6_size, legacyChunk7_size, legacyChunk8_size, legacyChunk9_size, legacyChunk10_size, legacyChunk11_size, legacyChunk12_size, legacyChunk13_size, legacyChunk14_size, legacyChunk15_size, legacyChunk16_size, legacyChunk17_size, legacyChunk18_size, legacyChunk19_size, legacyChunk20_size, legacyChunk21_size, legacyChunk22_size, legacyChunk23_size, legacyChunk24_size, legacyChunk25_size, legacyChunk26_size, legacyChunk27_size, legacyChunk28_size, legacyChunk29_size, legacyChunk30_size, legacyChunk31_size, legacyChunk32_size, legacyChunk33_size, legacyChunk34_size, legacy_leaf4_h7]
  simp only [ite_true]

private theorem legacy_leaf5_h7 : legacyChunk0.get? 5 = some 0x34 := rfl
private theorem legacy_byte5_h7 : legacyRuntime.get? 5 = some 0x34 := by
  norm_num only [legacyRuntime, get_append, ByteArray.size_append, legacyChunk0_size, legacyChunk1_size, legacyChunk2_size, legacyChunk3_size, legacyChunk4_size, legacyChunk5_size, legacyChunk6_size, legacyChunk7_size, legacyChunk8_size, legacyChunk9_size, legacyChunk10_size, legacyChunk11_size, legacyChunk12_size, legacyChunk13_size, legacyChunk14_size, legacyChunk15_size, legacyChunk16_size, legacyChunk17_size, legacyChunk18_size, legacyChunk19_size, legacyChunk20_size, legacyChunk21_size, legacyChunk22_size, legacyChunk23_size, legacyChunk24_size, legacyChunk25_size, legacyChunk26_size, legacyChunk27_size, legacyChunk28_size, legacyChunk29_size, legacyChunk30_size, legacyChunk31_size, legacyChunk32_size, legacyChunk33_size, legacyChunk34_size, legacy_leaf5_h7]
  simp only [ite_true]

private theorem legacy_leaf6_h7 : legacyChunk0.get? 6 = some 0x80 := rfl
private theorem legacy_byte6_h7 : legacyRuntime.get? 6 = some 0x80 := by
  norm_num only [legacyRuntime, get_append, ByteArray.size_append, legacyChunk0_size, legacyChunk1_size, legacyChunk2_size, legacyChunk3_size, legacyChunk4_size, legacyChunk5_size, legacyChunk6_size, legacyChunk7_size, legacyChunk8_size, legacyChunk9_size, legacyChunk10_size, legacyChunk11_size, legacyChunk12_size, legacyChunk13_size, legacyChunk14_size, legacyChunk15_size, legacyChunk16_size, legacyChunk17_size, legacyChunk18_size, legacyChunk19_size, legacyChunk20_size, legacyChunk21_size, legacyChunk22_size, legacyChunk23_size, legacyChunk24_size, legacyChunk25_size, legacyChunk26_size, legacyChunk27_size, legacyChunk28_size, legacyChunk29_size, legacyChunk30_size, legacyChunk31_size, legacyChunk32_size, legacyChunk33_size, legacyChunk34_size, legacy_leaf6_h7]
  simp only [ite_true]

private theorem legacy_leaf7_h7 : legacyChunk0.get? 7 = some 0x15 := rfl
private theorem legacy_byte7_h7 : legacyRuntime.get? 7 = some 0x15 := by
  norm_num only [legacyRuntime, get_append, ByteArray.size_append, legacyChunk0_size, legacyChunk1_size, legacyChunk2_size, legacyChunk3_size, legacyChunk4_size, legacyChunk5_size, legacyChunk6_size, legacyChunk7_size, legacyChunk8_size, legacyChunk9_size, legacyChunk10_size, legacyChunk11_size, legacyChunk12_size, legacyChunk13_size, legacyChunk14_size, legacyChunk15_size, legacyChunk16_size, legacyChunk17_size, legacyChunk18_size, legacyChunk19_size, legacyChunk20_size, legacyChunk21_size, legacyChunk22_size, legacyChunk23_size, legacyChunk24_size, legacyChunk25_size, legacyChunk26_size, legacyChunk27_size, legacyChunk28_size, legacyChunk29_size, legacyChunk30_size, legacyChunk31_size, legacyChunk32_size, legacyChunk33_size, legacyChunk34_size, legacy_leaf7_h7]
  simp only [ite_true]

private theorem legacy_leaf8_h7 : legacyChunk0.get? 8 = some 0x61 := rfl
private theorem legacy_byte8_h7 : legacyRuntime.get? 8 = some 0x61 := by
  norm_num only [legacyRuntime, get_append, ByteArray.size_append, legacyChunk0_size, legacyChunk1_size, legacyChunk2_size, legacyChunk3_size, legacyChunk4_size, legacyChunk5_size, legacyChunk6_size, legacyChunk7_size, legacyChunk8_size, legacyChunk9_size, legacyChunk10_size, legacyChunk11_size, legacyChunk12_size, legacyChunk13_size, legacyChunk14_size, legacyChunk15_size, legacyChunk16_size, legacyChunk17_size, legacyChunk18_size, legacyChunk19_size, legacyChunk20_size, legacyChunk21_size, legacyChunk22_size, legacyChunk23_size, legacyChunk24_size, legacyChunk25_size, legacyChunk26_size, legacyChunk27_size, legacyChunk28_size, legacyChunk29_size, legacyChunk30_size, legacyChunk31_size, legacyChunk32_size, legacyChunk33_size, legacyChunk34_size, legacy_leaf8_h7]
  simp only [ite_true]

private theorem legacy_leaf11_h7 : legacyChunk0.get? 11 = some 0x57 := rfl
private theorem legacy_byte11_h7 : legacyRuntime.get? 11 = some 0x57 := by
  norm_num only [legacyRuntime, get_append, ByteArray.size_append, legacyChunk0_size, legacyChunk1_size, legacyChunk2_size, legacyChunk3_size, legacyChunk4_size, legacyChunk5_size, legacyChunk6_size, legacyChunk7_size, legacyChunk8_size, legacyChunk9_size, legacyChunk10_size, legacyChunk11_size, legacyChunk12_size, legacyChunk13_size, legacyChunk14_size, legacyChunk15_size, legacyChunk16_size, legacyChunk17_size, legacyChunk18_size, legacyChunk19_size, legacyChunk20_size, legacyChunk21_size, legacyChunk22_size, legacyChunk23_size, legacyChunk24_size, legacyChunk25_size, legacyChunk26_size, legacyChunk27_size, legacyChunk28_size, legacyChunk29_size, legacyChunk30_size, legacyChunk31_size, legacyChunk32_size, legacyChunk33_size, legacyChunk34_size, legacy_leaf11_h7]
  simp only [ite_true]

private theorem legacy_leaf12_h7 : legacyChunk0.get? 12 = some 0x5f := rfl
private theorem legacy_byte12_h7 : legacyRuntime.get? 12 = some 0x5f := by
  norm_num only [legacyRuntime, get_append, ByteArray.size_append, legacyChunk0_size, legacyChunk1_size, legacyChunk2_size, legacyChunk3_size, legacyChunk4_size, legacyChunk5_size, legacyChunk6_size, legacyChunk7_size, legacyChunk8_size, legacyChunk9_size, legacyChunk10_size, legacyChunk11_size, legacyChunk12_size, legacyChunk13_size, legacyChunk14_size, legacyChunk15_size, legacyChunk16_size, legacyChunk17_size, legacyChunk18_size, legacyChunk19_size, legacyChunk20_size, legacyChunk21_size, legacyChunk22_size, legacyChunk23_size, legacyChunk24_size, legacyChunk25_size, legacyChunk26_size, legacyChunk27_size, legacyChunk28_size, legacyChunk29_size, legacyChunk30_size, legacyChunk31_size, legacyChunk32_size, legacyChunk33_size, legacyChunk34_size, legacy_leaf12_h7]
  simp only [ite_true]

private theorem legacy_leaf13_h7 : legacyChunk0.get? 13 = some 0x5f := rfl
private theorem legacy_byte13_h7 : legacyRuntime.get? 13 = some 0x5f := by
  norm_num only [legacyRuntime, get_append, ByteArray.size_append, legacyChunk0_size, legacyChunk1_size, legacyChunk2_size, legacyChunk3_size, legacyChunk4_size, legacyChunk5_size, legacyChunk6_size, legacyChunk7_size, legacyChunk8_size, legacyChunk9_size, legacyChunk10_size, legacyChunk11_size, legacyChunk12_size, legacyChunk13_size, legacyChunk14_size, legacyChunk15_size, legacyChunk16_size, legacyChunk17_size, legacyChunk18_size, legacyChunk19_size, legacyChunk20_size, legacyChunk21_size, legacyChunk22_size, legacyChunk23_size, legacyChunk24_size, legacyChunk25_size, legacyChunk26_size, legacyChunk27_size, legacyChunk28_size, legacyChunk29_size, legacyChunk30_size, legacyChunk31_size, legacyChunk32_size, legacyChunk33_size, legacyChunk34_size, legacy_leaf13_h7]
  simp only [ite_true]

private theorem legacy_leaf14_h7 : legacyChunk0.get? 14 = some 0xfd := rfl
private theorem legacy_byte14_h7 : legacyRuntime.get? 14 = some 0xfd := by
  norm_num only [legacyRuntime, get_append, ByteArray.size_append, legacyChunk0_size, legacyChunk1_size, legacyChunk2_size, legacyChunk3_size, legacyChunk4_size, legacyChunk5_size, legacyChunk6_size, legacyChunk7_size, legacyChunk8_size, legacyChunk9_size, legacyChunk10_size, legacyChunk11_size, legacyChunk12_size, legacyChunk13_size, legacyChunk14_size, legacyChunk15_size, legacyChunk16_size, legacyChunk17_size, legacyChunk18_size, legacyChunk19_size, legacyChunk20_size, legacyChunk21_size, legacyChunk22_size, legacyChunk23_size, legacyChunk24_size, legacyChunk25_size, legacyChunk26_size, legacyChunk27_size, legacyChunk28_size, legacyChunk29_size, legacyChunk30_size, legacyChunk31_size, legacyChunk32_size, legacyChunk33_size, legacyChunk34_size, legacy_leaf14_h7]
  simp only [ite_true]

private theorem legacy_leaf15_h7 : legacyChunk0.get? 15 = some 0x5b := rfl
private theorem legacy_byte15_h7 : legacyRuntime.get? 15 = some 0x5b := by
  norm_num only [legacyRuntime, get_append, ByteArray.size_append, legacyChunk0_size, legacyChunk1_size, legacyChunk2_size, legacyChunk3_size, legacyChunk4_size, legacyChunk5_size, legacyChunk6_size, legacyChunk7_size, legacyChunk8_size, legacyChunk9_size, legacyChunk10_size, legacyChunk11_size, legacyChunk12_size, legacyChunk13_size, legacyChunk14_size, legacyChunk15_size, legacyChunk16_size, legacyChunk17_size, legacyChunk18_size, legacyChunk19_size, legacyChunk20_size, legacyChunk21_size, legacyChunk22_size, legacyChunk23_size, legacyChunk24_size, legacyChunk25_size, legacyChunk26_size, legacyChunk27_size, legacyChunk28_size, legacyChunk29_size, legacyChunk30_size, legacyChunk31_size, legacyChunk32_size, legacyChunk33_size, legacyChunk34_size, legacy_leaf15_h7]
  simp only [ite_true]

private theorem viaIR_leaf0_h7 : viaIRChunk0.get? 0 = some 0x60 := rfl
private theorem viaIR_byte0_h7 : viaIRRuntime.get? 0 = some 0x60 := by
  norm_num only [viaIRRuntime, get_append, ByteArray.size_append, viaIRChunk0_size, viaIRChunk1_size, viaIRChunk2_size, viaIRChunk3_size, viaIRChunk4_size, viaIRChunk5_size, viaIRChunk6_size, viaIRChunk7_size, viaIRChunk8_size, viaIRChunk9_size, viaIRChunk10_size, viaIRChunk11_size, viaIRChunk12_size, viaIRChunk13_size, viaIRChunk14_size, viaIRChunk15_size, viaIRChunk16_size, viaIRChunk17_size, viaIRChunk18_size, viaIRChunk19_size, viaIRChunk20_size, viaIRChunk21_size, viaIRChunk22_size, viaIRChunk23_size, viaIRChunk24_size, viaIRChunk25_size, viaIRChunk26_size, viaIRChunk27_size, viaIRChunk28_size, viaIRChunk29_size, viaIRChunk30_size, viaIRChunk31_size, viaIRChunk32_size, viaIRChunk33_size, viaIRChunk34_size, viaIRChunk35_size, viaIRChunk36_size, viaIRChunk37_size, viaIRChunk38_size, viaIRChunk39_size, viaIRChunk40_size, viaIR_leaf0_h7]
  simp only [ite_true]

private theorem viaIR_leaf1_h7 : viaIRChunk0.get? 1 = some 0x80 := rfl
private theorem viaIR_byte1_h7 : viaIRRuntime.get? 1 = some 0x80 := by
  norm_num only [viaIRRuntime, get_append, ByteArray.size_append, viaIRChunk0_size, viaIRChunk1_size, viaIRChunk2_size, viaIRChunk3_size, viaIRChunk4_size, viaIRChunk5_size, viaIRChunk6_size, viaIRChunk7_size, viaIRChunk8_size, viaIRChunk9_size, viaIRChunk10_size, viaIRChunk11_size, viaIRChunk12_size, viaIRChunk13_size, viaIRChunk14_size, viaIRChunk15_size, viaIRChunk16_size, viaIRChunk17_size, viaIRChunk18_size, viaIRChunk19_size, viaIRChunk20_size, viaIRChunk21_size, viaIRChunk22_size, viaIRChunk23_size, viaIRChunk24_size, viaIRChunk25_size, viaIRChunk26_size, viaIRChunk27_size, viaIRChunk28_size, viaIRChunk29_size, viaIRChunk30_size, viaIRChunk31_size, viaIRChunk32_size, viaIRChunk33_size, viaIRChunk34_size, viaIRChunk35_size, viaIRChunk36_size, viaIRChunk37_size, viaIRChunk38_size, viaIRChunk39_size, viaIRChunk40_size, viaIR_leaf1_h7]
  simp only [ite_true]

private theorem viaIR_leaf2_h7 : viaIRChunk0.get? 2 = some 0x60 := rfl
private theorem viaIR_byte2_h7 : viaIRRuntime.get? 2 = some 0x60 := by
  norm_num only [viaIRRuntime, get_append, ByteArray.size_append, viaIRChunk0_size, viaIRChunk1_size, viaIRChunk2_size, viaIRChunk3_size, viaIRChunk4_size, viaIRChunk5_size, viaIRChunk6_size, viaIRChunk7_size, viaIRChunk8_size, viaIRChunk9_size, viaIRChunk10_size, viaIRChunk11_size, viaIRChunk12_size, viaIRChunk13_size, viaIRChunk14_size, viaIRChunk15_size, viaIRChunk16_size, viaIRChunk17_size, viaIRChunk18_size, viaIRChunk19_size, viaIRChunk20_size, viaIRChunk21_size, viaIRChunk22_size, viaIRChunk23_size, viaIRChunk24_size, viaIRChunk25_size, viaIRChunk26_size, viaIRChunk27_size, viaIRChunk28_size, viaIRChunk29_size, viaIRChunk30_size, viaIRChunk31_size, viaIRChunk32_size, viaIRChunk33_size, viaIRChunk34_size, viaIRChunk35_size, viaIRChunk36_size, viaIRChunk37_size, viaIRChunk38_size, viaIRChunk39_size, viaIRChunk40_size, viaIR_leaf2_h7]
  simp only [ite_true]

private theorem viaIR_leaf4_h7 : viaIRChunk0.get? 4 = some 0x52 := rfl
private theorem viaIR_byte4_h7 : viaIRRuntime.get? 4 = some 0x52 := by
  norm_num only [viaIRRuntime, get_append, ByteArray.size_append, viaIRChunk0_size, viaIRChunk1_size, viaIRChunk2_size, viaIRChunk3_size, viaIRChunk4_size, viaIRChunk5_size, viaIRChunk6_size, viaIRChunk7_size, viaIRChunk8_size, viaIRChunk9_size, viaIRChunk10_size, viaIRChunk11_size, viaIRChunk12_size, viaIRChunk13_size, viaIRChunk14_size, viaIRChunk15_size, viaIRChunk16_size, viaIRChunk17_size, viaIRChunk18_size, viaIRChunk19_size, viaIRChunk20_size, viaIRChunk21_size, viaIRChunk22_size, viaIRChunk23_size, viaIRChunk24_size, viaIRChunk25_size, viaIRChunk26_size, viaIRChunk27_size, viaIRChunk28_size, viaIRChunk29_size, viaIRChunk30_size, viaIRChunk31_size, viaIRChunk32_size, viaIRChunk33_size, viaIRChunk34_size, viaIRChunk35_size, viaIRChunk36_size, viaIRChunk37_size, viaIRChunk38_size, viaIRChunk39_size, viaIRChunk40_size, viaIR_leaf4_h7]
  simp only [ite_true]

private theorem viaIR_leaf5_h7 : viaIRChunk0.get? 5 = some 0x60 := rfl
private theorem viaIR_byte5_h7 : viaIRRuntime.get? 5 = some 0x60 := by
  norm_num only [viaIRRuntime, get_append, ByteArray.size_append, viaIRChunk0_size, viaIRChunk1_size, viaIRChunk2_size, viaIRChunk3_size, viaIRChunk4_size, viaIRChunk5_size, viaIRChunk6_size, viaIRChunk7_size, viaIRChunk8_size, viaIRChunk9_size, viaIRChunk10_size, viaIRChunk11_size, viaIRChunk12_size, viaIRChunk13_size, viaIRChunk14_size, viaIRChunk15_size, viaIRChunk16_size, viaIRChunk17_size, viaIRChunk18_size, viaIRChunk19_size, viaIRChunk20_size, viaIRChunk21_size, viaIRChunk22_size, viaIRChunk23_size, viaIRChunk24_size, viaIRChunk25_size, viaIRChunk26_size, viaIRChunk27_size, viaIRChunk28_size, viaIRChunk29_size, viaIRChunk30_size, viaIRChunk31_size, viaIRChunk32_size, viaIRChunk33_size, viaIRChunk34_size, viaIRChunk35_size, viaIRChunk36_size, viaIRChunk37_size, viaIRChunk38_size, viaIRChunk39_size, viaIRChunk40_size, viaIR_leaf5_h7]
  simp only [ite_true]

private theorem viaIR_leaf7_h7 : viaIRChunk0.get? 7 = some 0x36 := rfl
private theorem viaIR_byte7_h7 : viaIRRuntime.get? 7 = some 0x36 := by
  norm_num only [viaIRRuntime, get_append, ByteArray.size_append, viaIRChunk0_size, viaIRChunk1_size, viaIRChunk2_size, viaIRChunk3_size, viaIRChunk4_size, viaIRChunk5_size, viaIRChunk6_size, viaIRChunk7_size, viaIRChunk8_size, viaIRChunk9_size, viaIRChunk10_size, viaIRChunk11_size, viaIRChunk12_size, viaIRChunk13_size, viaIRChunk14_size, viaIRChunk15_size, viaIRChunk16_size, viaIRChunk17_size, viaIRChunk18_size, viaIRChunk19_size, viaIRChunk20_size, viaIRChunk21_size, viaIRChunk22_size, viaIRChunk23_size, viaIRChunk24_size, viaIRChunk25_size, viaIRChunk26_size, viaIRChunk27_size, viaIRChunk28_size, viaIRChunk29_size, viaIRChunk30_size, viaIRChunk31_size, viaIRChunk32_size, viaIRChunk33_size, viaIRChunk34_size, viaIRChunk35_size, viaIRChunk36_size, viaIRChunk37_size, viaIRChunk38_size, viaIRChunk39_size, viaIRChunk40_size, viaIR_leaf7_h7]
  simp only [ite_true]

private theorem viaIR_leaf8_h7 : viaIRChunk0.get? 8 = some 0x11 := rfl
private theorem viaIR_byte8_h7 : viaIRRuntime.get? 8 = some 0x11 := by
  norm_num only [viaIRRuntime, get_append, ByteArray.size_append, viaIRChunk0_size, viaIRChunk1_size, viaIRChunk2_size, viaIRChunk3_size, viaIRChunk4_size, viaIRChunk5_size, viaIRChunk6_size, viaIRChunk7_size, viaIRChunk8_size, viaIRChunk9_size, viaIRChunk10_size, viaIRChunk11_size, viaIRChunk12_size, viaIRChunk13_size, viaIRChunk14_size, viaIRChunk15_size, viaIRChunk16_size, viaIRChunk17_size, viaIRChunk18_size, viaIRChunk19_size, viaIRChunk20_size, viaIRChunk21_size, viaIRChunk22_size, viaIRChunk23_size, viaIRChunk24_size, viaIRChunk25_size, viaIRChunk26_size, viaIRChunk27_size, viaIRChunk28_size, viaIRChunk29_size, viaIRChunk30_size, viaIRChunk31_size, viaIRChunk32_size, viaIRChunk33_size, viaIRChunk34_size, viaIRChunk35_size, viaIRChunk36_size, viaIRChunk37_size, viaIRChunk38_size, viaIRChunk39_size, viaIRChunk40_size, viaIR_leaf8_h7]
  simp only [ite_true]

private theorem viaIR_leaf9_h7 : viaIRChunk0.get? 9 = some 0x61 := rfl
private theorem viaIR_byte9_h7 : viaIRRuntime.get? 9 = some 0x61 := by
  norm_num only [viaIRRuntime, get_append, ByteArray.size_append, viaIRChunk0_size, viaIRChunk1_size, viaIRChunk2_size, viaIRChunk3_size, viaIRChunk4_size, viaIRChunk5_size, viaIRChunk6_size, viaIRChunk7_size, viaIRChunk8_size, viaIRChunk9_size, viaIRChunk10_size, viaIRChunk11_size, viaIRChunk12_size, viaIRChunk13_size, viaIRChunk14_size, viaIRChunk15_size, viaIRChunk16_size, viaIRChunk17_size, viaIRChunk18_size, viaIRChunk19_size, viaIRChunk20_size, viaIRChunk21_size, viaIRChunk22_size, viaIRChunk23_size, viaIRChunk24_size, viaIRChunk25_size, viaIRChunk26_size, viaIRChunk27_size, viaIRChunk28_size, viaIRChunk29_size, viaIRChunk30_size, viaIRChunk31_size, viaIRChunk32_size, viaIRChunk33_size, viaIRChunk34_size, viaIRChunk35_size, viaIRChunk36_size, viaIRChunk37_size, viaIRChunk38_size, viaIRChunk39_size, viaIRChunk40_size, viaIR_leaf9_h7]
  simp only [ite_true]

private theorem viaIR_leaf12_h7 : viaIRChunk0.get? 12 = some 0x57 := rfl
private theorem viaIR_byte12_h7 : viaIRRuntime.get? 12 = some 0x57 := by
  norm_num only [viaIRRuntime, get_append, ByteArray.size_append, viaIRChunk0_size, viaIRChunk1_size, viaIRChunk2_size, viaIRChunk3_size, viaIRChunk4_size, viaIRChunk5_size, viaIRChunk6_size, viaIRChunk7_size, viaIRChunk8_size, viaIRChunk9_size, viaIRChunk10_size, viaIRChunk11_size, viaIRChunk12_size, viaIRChunk13_size, viaIRChunk14_size, viaIRChunk15_size, viaIRChunk16_size, viaIRChunk17_size, viaIRChunk18_size, viaIRChunk19_size, viaIRChunk20_size, viaIRChunk21_size, viaIRChunk22_size, viaIRChunk23_size, viaIRChunk24_size, viaIRChunk25_size, viaIRChunk26_size, viaIRChunk27_size, viaIRChunk28_size, viaIRChunk29_size, viaIRChunk30_size, viaIRChunk31_size, viaIRChunk32_size, viaIRChunk33_size, viaIRChunk34_size, viaIRChunk35_size, viaIRChunk36_size, viaIRChunk37_size, viaIRChunk38_size, viaIRChunk39_size, viaIRChunk40_size, viaIR_leaf12_h7]
  simp only [ite_true]

private theorem viaIR_leaf13_h7 : viaIRChunk0.get? 13 = some 0x5b := rfl
private theorem viaIR_byte13_h7 : viaIRRuntime.get? 13 = some 0x5b := by
  norm_num only [viaIRRuntime, get_append, ByteArray.size_append, viaIRChunk0_size, viaIRChunk1_size, viaIRChunk2_size, viaIRChunk3_size, viaIRChunk4_size, viaIRChunk5_size, viaIRChunk6_size, viaIRChunk7_size, viaIRChunk8_size, viaIRChunk9_size, viaIRChunk10_size, viaIRChunk11_size, viaIRChunk12_size, viaIRChunk13_size, viaIRChunk14_size, viaIRChunk15_size, viaIRChunk16_size, viaIRChunk17_size, viaIRChunk18_size, viaIRChunk19_size, viaIRChunk20_size, viaIRChunk21_size, viaIRChunk22_size, viaIRChunk23_size, viaIRChunk24_size, viaIRChunk25_size, viaIRChunk26_size, viaIRChunk27_size, viaIRChunk28_size, viaIRChunk29_size, viaIRChunk30_size, viaIRChunk31_size, viaIRChunk32_size, viaIRChunk33_size, viaIRChunk34_size, viaIRChunk35_size, viaIRChunk36_size, viaIRChunk37_size, viaIRChunk38_size, viaIRChunk39_size, viaIRChunk40_size, viaIR_leaf13_h7]
  simp only [ite_true]

private theorem viaIR_leaf14_h7 : viaIRChunk0.get? 14 = some 0x61 := rfl
private theorem viaIR_byte14_h7 : viaIRRuntime.get? 14 = some 0x61 := by
  norm_num only [viaIRRuntime, get_append, ByteArray.size_append, viaIRChunk0_size, viaIRChunk1_size, viaIRChunk2_size, viaIRChunk3_size, viaIRChunk4_size, viaIRChunk5_size, viaIRChunk6_size, viaIRChunk7_size, viaIRChunk8_size, viaIRChunk9_size, viaIRChunk10_size, viaIRChunk11_size, viaIRChunk12_size, viaIRChunk13_size, viaIRChunk14_size, viaIRChunk15_size, viaIRChunk16_size, viaIRChunk17_size, viaIRChunk18_size, viaIRChunk19_size, viaIRChunk20_size, viaIRChunk21_size, viaIRChunk22_size, viaIRChunk23_size, viaIRChunk24_size, viaIRChunk25_size, viaIRChunk26_size, viaIRChunk27_size, viaIRChunk28_size, viaIRChunk29_size, viaIRChunk30_size, viaIRChunk31_size, viaIRChunk32_size, viaIRChunk33_size, viaIRChunk34_size, viaIRChunk35_size, viaIRChunk36_size, viaIRChunk37_size, viaIRChunk38_size, viaIRChunk39_size, viaIRChunk40_size, viaIR_leaf14_h7]
  simp only [ite_true]

private theorem viaIR_leaf17_h7 : viaIRChunk0.get? 17 = some 0x56 := rfl
private theorem viaIR_byte17_h7 : viaIRRuntime.get? 17 = some 0x56 := by
  norm_num only [viaIRRuntime, get_append, ByteArray.size_append, viaIRChunk0_size, viaIRChunk1_size, viaIRChunk2_size, viaIRChunk3_size, viaIRChunk4_size, viaIRChunk5_size, viaIRChunk6_size, viaIRChunk7_size, viaIRChunk8_size, viaIRChunk9_size, viaIRChunk10_size, viaIRChunk11_size, viaIRChunk12_size, viaIRChunk13_size, viaIRChunk14_size, viaIRChunk15_size, viaIRChunk16_size, viaIRChunk17_size, viaIRChunk18_size, viaIRChunk19_size, viaIRChunk20_size, viaIRChunk21_size, viaIRChunk22_size, viaIRChunk23_size, viaIRChunk24_size, viaIRChunk25_size, viaIRChunk26_size, viaIRChunk27_size, viaIRChunk28_size, viaIRChunk29_size, viaIRChunk30_size, viaIRChunk31_size, viaIRChunk32_size, viaIRChunk33_size, viaIRChunk34_size, viaIRChunk35_size, viaIRChunk36_size, viaIRChunk37_size, viaIRChunk38_size, viaIRChunk39_size, viaIRChunk40_size, viaIR_leaf17_h7]
  simp only [ite_true]

private theorem viaIR_leaf18_h7 : viaIRChunk0.get? 18 = some 0x5b := rfl
private theorem viaIR_byte18_h7 : viaIRRuntime.get? 18 = some 0x5b := by
  norm_num only [viaIRRuntime, get_append, ByteArray.size_append, viaIRChunk0_size, viaIRChunk1_size, viaIRChunk2_size, viaIRChunk3_size, viaIRChunk4_size, viaIRChunk5_size, viaIRChunk6_size, viaIRChunk7_size, viaIRChunk8_size, viaIRChunk9_size, viaIRChunk10_size, viaIRChunk11_size, viaIRChunk12_size, viaIRChunk13_size, viaIRChunk14_size, viaIRChunk15_size, viaIRChunk16_size, viaIRChunk17_size, viaIRChunk18_size, viaIRChunk19_size, viaIRChunk20_size, viaIRChunk21_size, viaIRChunk22_size, viaIRChunk23_size, viaIRChunk24_size, viaIRChunk25_size, viaIRChunk26_size, viaIRChunk27_size, viaIRChunk28_size, viaIRChunk29_size, viaIRChunk30_size, viaIRChunk31_size, viaIRChunk32_size, viaIRChunk33_size, viaIRChunk34_size, viaIRChunk35_size, viaIRChunk36_size, viaIRChunk37_size, viaIRChunk38_size, viaIRChunk39_size, viaIRChunk40_size, viaIR_leaf18_h7]
  simp only [ite_true]


theorem legacy_bound : legacyRuntime.size + 33 < UInt256.size := by
  rw [legacy_size]
  decide

private theorem legacy_prefix (acc : Array UInt256) :
    D_J_scan legacyRuntime 0 acc = D_J_scan legacyRuntime 16 (acc.push (.ofNat 15)) := by
  generalize hscan : D_J_scan legacyRuntime = run
  have e0 : run 0 acc = run 2 acc := by
    have edge : D_J_scan legacyRuntime 0 acc = D_J_scan legacyRuntime 2 acc :=
      scanner_byte_step legacyRuntime 0 0x60 1 false acc
        (legacy_byte0_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e1 : run 2 acc = run 4 acc := by
    have edge : D_J_scan legacyRuntime 2 acc = D_J_scan legacyRuntime 4 acc :=
      scanner_byte_step legacyRuntime 2 0x60 1 false acc
        (legacy_byte2_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e2 : run 4 acc = run 5 acc := by
    have edge : D_J_scan legacyRuntime 4 acc = D_J_scan legacyRuntime 5 acc :=
      scanner_byte_step legacyRuntime 4 0x52 0 false acc
        (legacy_byte4_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e3 : run 5 acc = run 6 acc := by
    have edge : D_J_scan legacyRuntime 5 acc = D_J_scan legacyRuntime 6 acc :=
      scanner_byte_step legacyRuntime 5 0x34 0 false acc
        (legacy_byte5_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e4 : run 6 acc = run 7 acc := by
    have edge : D_J_scan legacyRuntime 6 acc = D_J_scan legacyRuntime 7 acc :=
      scanner_byte_step legacyRuntime 6 0x80 0 false acc
        (legacy_byte6_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e5 : run 7 acc = run 8 acc := by
    have edge : D_J_scan legacyRuntime 7 acc = D_J_scan legacyRuntime 8 acc :=
      scanner_byte_step legacyRuntime 7 0x15 0 false acc
        (legacy_byte7_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e6 : run 8 acc = run 11 acc := by
    have edge : D_J_scan legacyRuntime 8 acc = D_J_scan legacyRuntime 11 acc :=
      scanner_byte_step legacyRuntime 8 0x61 2 false acc
        (legacy_byte8_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e7 : run 11 acc = run 12 acc := by
    have edge : D_J_scan legacyRuntime 11 acc = D_J_scan legacyRuntime 12 acc :=
      scanner_byte_step legacyRuntime 11 0x57 0 false acc
        (legacy_byte11_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e8 : run 12 acc = run 13 acc := by
    have edge : D_J_scan legacyRuntime 12 acc = D_J_scan legacyRuntime 13 acc :=
      scanner_byte_step legacyRuntime 12 0x5f 0 false acc
        (legacy_byte12_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e9 : run 13 acc = run 14 acc := by
    have edge : D_J_scan legacyRuntime 13 acc = D_J_scan legacyRuntime 14 acc :=
      scanner_byte_step legacyRuntime 13 0x5f 0 false acc
        (legacy_byte13_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e10 : run 14 acc = run 15 acc := by
    have edge : D_J_scan legacyRuntime 14 acc = D_J_scan legacyRuntime 15 acc :=
      scanner_byte_step legacyRuntime 14 0xfd 0 false acc
        (legacy_byte14_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e11 : run 15 acc = run 16 (acc.push (.ofNat 15)) := by
    have edge : D_J_scan legacyRuntime 15 acc = D_J_scan legacyRuntime 16 (acc.push (.ofNat 15)) :=
      scanner_byte_step legacyRuntime 15 0x5b 0 true acc
        (legacy_byte15_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  exact e0.trans (e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans (e7.trans (e8.trans (e9.trans (e10.trans (e11)))))))))))

theorem legacy_first_destination :
    (D_J legacyRuntime (.ofNat 0)).contains (.ofNat 15) = true := by
  have reduced : D_J legacyRuntime (.ofNat 0) = D_J_scan legacyRuntime 0 #[] :=
    D_J_aux_bounded legacyRuntime (.ofNat 0) #[] legacy_bound
  have reached : D_J legacyRuntime (.ofNat 0) = D_J_scan legacyRuntime 16 (#[].push (.ofNat 15)) :=
    reduced.trans (legacy_prefix #[])
  have kept : (D_J_scan legacyRuntime 16 (#[].push (.ofNat 15))).contains (.ofNat 15) = true :=
    scanner_preserves_contains legacyRuntime 16 (#[].push (.ofNat 15)) (.ofNat 15) (by decide)
  exact (congrArg (fun table : Array UInt256 => table.contains (.ofNat 15)) reached).trans kept

theorem viaIR_bound : viaIRRuntime.size + 33 < UInt256.size := by
  rw [viaIR_size]
  decide

private theorem viaIR_prefix (acc : Array UInt256) :
    D_J_scan viaIRRuntime 0 acc = D_J_scan viaIRRuntime 19 ((acc.push (.ofNat 13)).push (.ofNat 18)) := by
  generalize hscan : D_J_scan viaIRRuntime = run
  have e0 : run 0 acc = run 2 acc := by
    have edge : D_J_scan viaIRRuntime 0 acc = D_J_scan viaIRRuntime 2 acc :=
      scanner_byte_step viaIRRuntime 0 0x60 1 false acc
        (viaIR_byte0_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e1 : run 2 acc = run 4 acc := by
    have edge : D_J_scan viaIRRuntime 2 acc = D_J_scan viaIRRuntime 4 acc :=
      scanner_byte_step viaIRRuntime 2 0x60 1 false acc
        (viaIR_byte2_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e2 : run 4 acc = run 5 acc := by
    have edge : D_J_scan viaIRRuntime 4 acc = D_J_scan viaIRRuntime 5 acc :=
      scanner_byte_step viaIRRuntime 4 0x52 0 false acc
        (viaIR_byte4_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e3 : run 5 acc = run 7 acc := by
    have edge : D_J_scan viaIRRuntime 5 acc = D_J_scan viaIRRuntime 7 acc :=
      scanner_byte_step viaIRRuntime 5 0x60 1 false acc
        (viaIR_byte5_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e4 : run 7 acc = run 8 acc := by
    have edge : D_J_scan viaIRRuntime 7 acc = D_J_scan viaIRRuntime 8 acc :=
      scanner_byte_step viaIRRuntime 7 0x36 0 false acc
        (viaIR_byte7_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e5 : run 8 acc = run 9 acc := by
    have edge : D_J_scan viaIRRuntime 8 acc = D_J_scan viaIRRuntime 9 acc :=
      scanner_byte_step viaIRRuntime 8 0x11 0 false acc
        (viaIR_byte8_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e6 : run 9 acc = run 12 acc := by
    have edge : D_J_scan viaIRRuntime 9 acc = D_J_scan viaIRRuntime 12 acc :=
      scanner_byte_step viaIRRuntime 9 0x61 2 false acc
        (viaIR_byte9_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e7 : run 12 acc = run 13 acc := by
    have edge : D_J_scan viaIRRuntime 12 acc = D_J_scan viaIRRuntime 13 acc :=
      scanner_byte_step viaIRRuntime 12 0x57 0 false acc
        (viaIR_byte12_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e8 : run 13 acc = run 14 (acc.push (.ofNat 13)) := by
    have edge : D_J_scan viaIRRuntime 13 acc = D_J_scan viaIRRuntime 14 (acc.push (.ofNat 13)) :=
      scanner_byte_step viaIRRuntime 13 0x5b 0 true acc
        (viaIR_byte13_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e9 : run 14 (acc.push (.ofNat 13)) = run 17 (acc.push (.ofNat 13)) := by
    have edge : D_J_scan viaIRRuntime 14 (acc.push (.ofNat 13)) = D_J_scan viaIRRuntime 17 (acc.push (.ofNat 13)) :=
      scanner_byte_step viaIRRuntime 14 0x61 2 false (acc.push (.ofNat 13))
        (viaIR_byte14_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e10 : run 17 (acc.push (.ofNat 13)) = run 18 (acc.push (.ofNat 13)) := by
    have edge : D_J_scan viaIRRuntime 17 (acc.push (.ofNat 13)) = D_J_scan viaIRRuntime 18 (acc.push (.ofNat 13)) :=
      scanner_byte_step viaIRRuntime 17 0x56 0 false (acc.push (.ofNat 13))
        (viaIR_byte17_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  have e11 : run 18 (acc.push (.ofNat 13)) = run 19 ((acc.push (.ofNat 13)).push (.ofNat 18)) := by
    have edge : D_J_scan viaIRRuntime 18 (acc.push (.ofNat 13)) = D_J_scan viaIRRuntime 19 ((acc.push (.ofNat 13)).push (.ofNat 18)) :=
      scanner_byte_step viaIRRuntime 18 0x5b 0 true (acc.push (.ofNat 13))
        (viaIR_byte18_h7) (by decide +kernel) (by decide +kernel)
    rw [hscan] at edge
    exact edge
  exact e0.trans (e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans (e7.trans (e8.trans (e9.trans (e10.trans (e11)))))))))))

theorem viaIR_first_destination :
    (D_J viaIRRuntime (.ofNat 0)).contains (.ofNat 18) = true := by
  have reduced : D_J viaIRRuntime (.ofNat 0) = D_J_scan viaIRRuntime 0 #[] :=
    D_J_aux_bounded viaIRRuntime (.ofNat 0) #[] viaIR_bound
  have reached : D_J viaIRRuntime (.ofNat 0) = D_J_scan viaIRRuntime 19 ((#[].push (.ofNat 13)).push (.ofNat 18)) :=
    reduced.trans (viaIR_prefix #[])
  have kept : (D_J_scan viaIRRuntime 19 ((#[].push (.ofNat 13)).push (.ofNat 18))).contains (.ofNat 18) = true :=
    scanner_preserves_contains viaIRRuntime 19 ((#[].push (.ofNat 13)).push (.ofNat 18)) (.ofNat 18) (by decide)
  exact (congrArg (fun table : Array UInt256 => table.contains (.ofNat 18)) reached).trans kept

-- Same local equality law as published Assembly.Scanned; no global instance.
local instance : LawfulBEq UInt256 where
  rfl {a} := by cases a with | mk a => change (a == a) = true; exact BEq.rfl
  eq_of_beq {a b} h := by
    cases a with
    | mk a => cases b with
      | mk b => apply congrArg UInt256.mk; change (a == b) = true at h; exact eq_of_beq h

/-- The table is the actual bounded scan; no chosen certificate/table is input. -/
theorem actual_member_decodes (code : ByteArray) (target : UInt256)
    (bound : code.size + 33 < UInt256.size)
    (member : (D_J code (.ofNat 0)).contains target = true) :
    decode code target = some (.JUMPDEST,none) := by
  obtain ⟨scan,_⟩ := bounded_actual_scan code (.ofNat 0) bound #[]
  rw [scanResult_actual_destinations scan bound,List.contains_toArray] at member
  exact scan.path.valid target (List.contains_iff_mem.mp member)

/-- Original PUSH immediate positions are not destinations. -/
theorem legacy_immediate_refused :
    (D_J legacyRuntime (.ofNat 0)).contains (.ofNat 1) = false := by
  cases h : (D_J legacyRuntime (.ofNat 0)).contains (.ofNat 1) with
  | false => rfl
  | true =>
    have decoded : decode legacyRuntime (.ofNat 1) = some (.JUMPDEST,none) :=
      actual_member_decodes _ _ legacy_bound h
    have wrong : decode legacyRuntime (.ofNat 1) ≠ some (.JUMPDEST,none) := by
      have pc1 : (UInt256.ofNat 1).toNat = 1 := by decide +kernel
      simp only [decode,pc1,legacy_byte1_h7]
      decide +kernel
    exact False.elim (wrong decoded)

theorem viaIR_immediate_refused :
    (D_J viaIRRuntime (.ofNat 0)).contains (.ofNat 1) = false := by
  cases h : (D_J viaIRRuntime (.ofNat 0)).contains (.ofNat 1) with
  | false => rfl
  | true =>
    have decoded : decode viaIRRuntime (.ofNat 1) = some (.JUMPDEST,none) :=
      actual_member_decodes _ _ viaIR_bound h
    have wrong : decode viaIRRuntime (.ofNat 1) ≠ some (.JUMPDEST,none) := by
      have pc1 : (UInt256.ofNat 1).toNat = 1 := by decide +kernel
      simp only [decode,pc1,viaIR_byte1_h7]
      decide +kernel
    exact False.elim (wrong decoded)

end Solidity.Evm.External.TryPanicSourceScanner
