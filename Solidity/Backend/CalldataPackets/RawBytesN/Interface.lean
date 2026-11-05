import Solidity.Backend.MemoryOps.SourceCalldataCopy

/-! Raw bytesN packets use the existing Source decoder and allocator.
No compiler, physical-memory or Source adequacy premise is introduced. -/
namespace Solidity.Backend.CalldataPackets.RawBytesN
abbrev ArrayTy (n : Nat) (h : 1 ≤ n ∧ n ≤ 32) : Source.STy :=
  .array .memory (.fixedBytes n h) none

def decoded (D : Source.Layout) (n : Nat) (h : 1 ≤ n ∧ n ≤ 32)
    (F : Source.Fr) (off len : Nat) : Source.R (List (Source.Val D (.fixedBytes n h))) :=
  (List.range len).mapM fun j => Source.decodeWord D (Source.cdWordAt F (off+32*j)) (.fixedBytes n h)

def memory {D : Source.Layout} {n : Nat} {h : 1 ≤ n ∧ n ≤ 32}
    (vs : List (Source.Val D (.fixedBytes n h))) : Source.Data D (ArrayTy n h) :=
  .array vs.length (fun _ h => nomatch h) (fun i => .val (vs.get i))

/-- Signature for exact raw decoding, including dirty low-byte refusal. -/
structure DecodeCertificate (D : Source.Layout) (n : Nat) (h : 1 ≤ n ∧ n ≤ 32) where
  word : ∀ w, Source.decodeWord D w (.fixedBytes n h) =
    if (Source.natBytes 32 w).drop n = List.replicate (32-n) 0 then
      .ok (Source.mkBytes (n := n) (h := h) (Source.natBytes 32 w))
    else .error (.revert [])
end Solidity.Backend.CalldataPackets.RawBytesN
