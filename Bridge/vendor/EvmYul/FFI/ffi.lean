import Init.Data.Array.Lemmas

namespace ffi

@[extern "sha256"]
opaque sha256 (input : @& ByteArray) (len : USize) : ByteArray

def SHA256 (d : ByteArray) : Except String ByteArray :=
  pure <| sha256 d d.size.toUSize

@[extern "blake2compressb64"]
opaque BLAKE2Compress (input : @& ByteArray) : ByteArray

def BLAKE2 (d : ByteArray) : Except String ByteArray := do
  if d.size != 213                    then throw "error"
  if d[212]! ∉ [0, 1].map Nat.toUInt8 then throw "error"
  return BLAKE2Compress d

@[extern "memset_zero"]
def ByteArray.zeroes (n : USize) : ByteArray :=
  ⟨Array.replicate n.toNat (0 : UInt8)⟩

/-- Kernel specification of the retained memset_zero ABI. Native allocation
and implementation correspondence are separate from these logical laws. -/
theorem ByteArray.zeroes_size (n : USize) : (zeroes n).size = n.toNat := by
  simp only [zeroes, _root_.ByteArray.size, Array.size_replicate]

theorem ByteArray.zeroes_zero : zeroes (0 : USize) = _root_.ByteArray.empty := rfl

theorem ByteArray.zeroes_get (n : USize) (i : Nat) (h : i < n.toNat) :
    (zeroes n).data[i]'(by simpa only [zeroes, Array.size_replicate] using h) = 0 := by
  exact Array.getElem_replicate _

@[extern "keccak256"]
opaque keccak256 (input : @& ByteArray) (len : USize) : ByteArray

def KECCAK256 (d : ByteArray) : Except String ByteArray :=
  pure <| keccak256 d d.size.toUSize

def KEC (data : ByteArray) : ByteArray :=
  ffi.KECCAK256 data |>.toOption.getD .empty

end ffi
