import Solidity.Backend.Assembler

/-!
Creation-artifact layout, independent of source execution and account CREATE.
Runtime and arguments are arbitrary bytes. The wrapper uses the existing Osaka
instruction type and assembler's minimal big-endian PUSH encoding. No EIP-170 or
EIP-3860 bound is imposed; the length must fit a 256-bit stack operand.
-/
namespace Solidity.Backend.Creation

/-- An immediate whose value fits the EVM stack word. -/
structure Immediate where
  value : Nat
  fits : value < 256 ^ 32

def Immediate.width (v : Immediate) : Fin 33 :=
  ⟨byteWidth v.value, Nat.lt_succ_of_le (byteWidth_le v.fits)⟩

def Immediate.instr (v : Immediate) : Instr :=
  .push v.width (toBytesBE v.width.val v.value)

theorem Immediate.read (v : Immediate) :
    ofBytesBE (toBytesBE v.width.val v.value).toList = v.value :=
  ofBytesBE_toBytesBE _ _ (lt_pow_byteWidth _)

/-- This standalone wrapper has offset 2*w+8, always in PUSH1 range. -/
def runtimeOffset (n : Immediate) : Nat := 2 * n.width.val + 8

theorem runtimeOffset_fits (n : Immediate) : runtimeOffset n < 256 := by
  have h := n.width.isLt
  simp only [runtimeOffset]
  omega

def offsetInstr (n : Immediate) : Instr :=
  .push 1 (toBytesBE 1 (runtimeOffset n))

/-- Stack order: length, code offset, memory destination; then length, return offset. -/
def wrapper (n : Immediate) : Program :=
  [n.instr, offsetInstr n, .push 0 #v[], .op .CODECOPY,
   n.instr, .push 0 #v[], .op .RETURN]

theorem wrapper_size (n : Immediate) : size (wrapper n) = runtimeOffset n := by
  simp only [wrapper, size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Immediate.instr, offsetInstr, Instr.size, runtimeOffset]
  omega

theorem wrapper_length (n : Immediate) : (encode (wrapper n)).length = runtimeOffset n := by
  rw [length_encode, wrapper_size]

/-- Library reference format is the assembler's absolute byte-offset/name pair.
Certification and refusal of unresolved references are added by the linking layer. -/
structure Artifact (Lib : Type) where
  runtime : List UInt8
  args : List UInt8
  runtimeFits : runtime.length < 256 ^ 32
  /-- Absolute origin used by the assembler for these references. -/
  linkBase : Nat
  runtimeLinks : List (Nat × Lib)

def Artifact.lengthWord (a : Artifact Lib) : Immediate := ⟨a.runtime.length, a.runtimeFits⟩
def Artifact.initcode (a : Artifact Lib) : List UInt8 :=
  encode (wrapper a.lengthWord) ++ a.runtime

def Artifact.payload (a : Artifact Lib) : List UInt8 := a.initcode ++ a.args

def Artifact.runtimeStart (a : Artifact Lib) : Nat := runtimeOffset a.lengthWord

def Artifact.argsStart (a : Artifact Lib) : Nat := a.runtimeStart + a.runtime.length

theorem Artifact.runtime_slice (a : Artifact Lib) :
    (a.payload.drop a.runtimeStart).take a.runtime.length = a.runtime := by
  unfold Artifact.payload Artifact.initcode Artifact.runtimeStart
  rw [List.append_assoc, ← wrapper_length a.lengthWord, List.drop_left]
  exact List.take_left

theorem Artifact.args_slice (a : Artifact Lib) :
    a.payload.drop a.argsStart = a.args := by
  unfold Artifact.payload Artifact.argsStart Artifact.initcode Artifact.runtimeStart
  rw [← wrapper_length a.lengthWord, ← List.length_append, List.drop_left]

theorem Artifact.initcode_length (a : Artifact Lib) : a.initcode.length = a.argsStart := by
  simp only [Artifact.initcode, List.length_append, wrapper_length,
    Artifact.argsStart, Artifact.runtimeStart]

/-- Reuse an assembled runtime without decoding, relocating, or changing its algorithm. -/
def fromAssembly (base : Nat) (r : Assembled Lib) (args : List UInt8)
    (fits : (encode r.code).length < 256 ^ 32) : Artifact Lib :=
  ⟨encode r.code, args, fits, base, r.linkRefs⟩

theorem byteWidth_zero : byteWidth 0 = 0 := by
  rw [byteWidth]
  rfl

theorem byteWidth_small (v : Nat) (hp : 0 < v) (hlt : v < 256) : byteWidth v = 1 := by
  rw [byteWidth]
  simp only [Nat.ne_of_gt hp, if_false, Nat.div_eq_of_lt hlt, byteWidth_zero]

example : encode (wrapper ⟨3, by decide⟩) =
    [0x60, 3, 0x60, 10, 0x5f, 0x39, 0x60, 3, 0x5f, 0xf3] := by
  have h : byteWidth 3 = 1 := byteWidth_small 3 (by decide) (by decide)
  have hb : (toBytesBE (byteWidth 3) 3).toList = (toBytesBE 1 3).toList :=
    congrArg (fun k => (toBytesBE k 3).toList) h
  unfold wrapper Immediate.instr offsetInstr runtimeOffset Immediate.width
  simp only [encode, List.flatMap_cons, List.flatMap_nil, Instr.encode, pushCode, h, hb]
  decide
example : encode (wrapper ⟨0, by decide⟩) =
    [0x5f, 0x60, 8, 0x5f, 0x39, 0x5f, 0x5f, 0xf3] := by
  have hb : (toBytesBE (byteWidth 0) 0).toList = (toBytesBE 0 0).toList :=
    congrArg (fun k => (toBytesBE k 0).toList) byteWidth_zero
  unfold wrapper Immediate.instr offsetInstr runtimeOffset Immediate.width
  simp only [encode, List.flatMap_cons, List.flatMap_nil, Instr.encode, pushCode, byteWidth_zero, hb]
  decide
example : runtimeOffset ⟨255, by decide⟩ = 10 := by
  have h : byteWidth 255 = 1 := byteWidth_small 255 (by decide) (by decide)
  unfold runtimeOffset Immediate.width
  simp only [h]
example : runtimeOffset ⟨256, by decide⟩ = 12 := by
  have h : byteWidth 256 = 2 := by
    rw [byteWidth]
    simp only [show (256 : Nat) ≠ 0 by decide, if_false]
    change byteWidth 1 + 1 = 2
    rw [byteWidth_small 1 (by decide) (by decide)]
  unfold runtimeOffset Immediate.width
  simp only [h]

end Solidity.Backend.Creation
