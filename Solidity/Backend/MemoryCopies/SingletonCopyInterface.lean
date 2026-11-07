import Solidity.Backend.MemoryCopies.InterfaceV2Roots
import Solidity.Backend.MemoryCopies.HeapContents
import Solidity.Evm.MemoryObjectPrimitive
import Solidity.Semantics.AllocBytes

/-! A populated resolved-value array copy, using existing allocator and typed
store emitters. This interface does not assert a storage-load compiler. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def singletonArrayValue (primitive : PrimTy) (value : primitive.Denote) : SVal (.ref (.array (.prim primitive))) :=
  .array (.cons (.prim value) .nil) .nil (by decide)

def singletonCopyCode (word : Word) : List Instr :=
  [.push word,.push w[1]] ++ allocateArrayCode ++ [.swap 1,.dup 2] ++ writeFieldCode 1

structure SingletonWordCopy (primitive : PrimTy) (value : primitive.Denote) (word : Word) where
  representation : ReprV primitive value word
  certificate : V2.StorageWordCertificate (singletonArrayValue primitive value) rfl 2
  rootGap : V2.StorageWordRootCertificate certificate
  code : certificate.code = singletonCopyCode word
end Solidity.Backend.MemoryCopies
