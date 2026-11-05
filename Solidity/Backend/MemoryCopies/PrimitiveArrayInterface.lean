import Solidity.Backend.MemoryCopies.SingletonCopy
import Solidity.Evm.MemoryObjectReserve

/-! Resolved finite primitive arrays reuse the existing allocator and typed
stores. This interface does not assert runtime storage-load selection. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def primitiveArrayValue (primitive : PrimTy) (values : List primitive.Denote)
    (bounded : values.length < W) : SVal (.ref (.array (.prim primitive))) :=
  .array (SVec.ofList (values.map SVal.prim)) .nil (by simpa only [List.length_map] using bounded)

def primitiveArrayObject {H : HTy} (primitive : PrimTy) (values : List primitive.Denote)
    (bounded : values.length < W) : MObj H (.array (.prim primitive)) := ⟨values,bounded⟩

structure PrimitiveWords (primitive : PrimTy) (values : List primitive.Denote) (words : List Word) : Prop where
  length : words.length = values.length
  elements : ∀ (index : Nat) (value : primitive.Denote), values[index]? = some value →
    ∃ word, words[index]? = some word ∧ ReprV primitive value word

def arrayWordsCode (offset : Nat) : List Word → List Instr
  | [] => []
  | word :: words => [.push word,.dup 2] ++ writeFieldCode offset ++ arrayWordsCode (offset + 1) words

def arrayWordsMachine (cursor : Fin W) (offset : Nat) : List Word → Machine → Machine
  | [],machine => machine
  | word :: words,machine => arrayWordsMachine cursor (offset + 1) words
      (writeMachine machine (cursor.val + offset) word)

def primitiveArrayCode (words : List Word) : List Instr :=
  [.push (.val (wmod words.length))] ++ allocateArrayCode ++ arrayWordsCode 1 words

structure PrimitiveArrayWordCopy (primitive : PrimTy) (values : List primitive.Denote)
    (bounded : values.length < W) (words : List Word) where
  representation : PrimitiveWords primitive values words
  certificate : V2.StorageWordCertificate (primitiveArrayValue primitive values bounded) rfl (values.length + 1)
  rootGap : V2.StorageWordRootCertificate certificate
  code : certificate.code = primitiveArrayCode words
end Solidity.Backend.MemoryCopies
