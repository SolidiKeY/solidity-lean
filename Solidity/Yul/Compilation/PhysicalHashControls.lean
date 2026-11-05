import Solidity.Yul.Compilation.PhysicalHash
import Solidity.Backend.Environment.ObservationsChecks
/-! Executable byte-slice controls; no native gas/capacity or hash-injectivity claim. -/
namespace Solidity.Yul.Compilation.PhysicalHash.Controls
open Solidity.Yul.Views
open Backend.Environment (sample)
def dirty : Roadmap.Word := ⟨2^200+257,by decide⟩
def memory : ByteView := fun n => UInt8.ofNat (n+9)
def initial : Backend.Environment.Slice := ⟨[uintOfNat 77,uintOfNat 99],memory⟩
def observe (code : Backend.Program) :=
  (Backend.Environment.runSlice sample code initial).map
    (fun out => (out.stack.map (fun w => w.1.toNat),readBytes out.memory 31 32,out.memory 30,out.memory 63))
#check store_hash_run sample 31 dirty initial (by decide)
#guard observe (storeThenHash 31 dirty) = some
  ((keccak256 Roadmap.Evm.withKeccak (mstore memory 31 dirty) 31 32).val :: [77,99],
    readBytes (mstore memory 31 dirty) 31 32,39,72)
#guard (Backend.Environment.runSlice sample (storeThenHash 31 dirty) initial).map
  (fun out => (mload out.memory 31).val) = some dirty.val
#guard (storeThenHash 31 dirty).length = 99
#guard (selectHash ⟨2^256-1,by decide⟩ 0).isSome
#guard (selectHash ⟨2^256-32,by decide⟩ 32).isSome
#guard (selectHash ⟨2^256-31,by decide⟩ 32).isNone
#guard (Backend.Environment.runSlice sample [.op .KECCAK256]
  (⟨[],memory⟩ : Backend.Environment.Slice)).isNone
#guard (Backend.Environment.runSlice sample [.op .KECCAK256]
  (⟨[uintOfNat 31],memory⟩ : Backend.Environment.Slice)).isNone
#guard (Backend.Environment.runSlice sample [.op .SSTORE] initial).isNone
-- Explicit operand-order check: offset on top, length underneath.
#guard (Backend.Environment.runSlice sample (hashCode 31 2) initial).map
  (fun out => (out.stack.headD (uintOfNat 0)).1.toNat) =
  some (keccak256 Roadmap.Evm.withKeccak memory 31 2).val
-- Oversized caller success in this slice does not certify native capacity.
def oversized : Backend.Environment.Slice := ⟨List.replicate 1025 (uintOfNat 1),memory⟩
#guard (Backend.Environment.runSlice sample (storeThenHash 31 dirty) oversized).map
  (fun out => out.stack.length) = some 1026
#print axioms store_hash_run
#print axioms digest_view
end Solidity.Yul.Compilation.PhysicalHash.Controls
