import Solidity.Backend.Scalar.Heights
import Solidity.Backend.Scalar.Values
import Solidity.Backend.Scalar.Checked

/-! Resource-bearing consumers of the typed scalar certificates. Capacity is
checked on all instruction boundaries, not inferred from untouched-tail laws.
These witnesses concern gasless slices and do not assert fetched EVM execution. -/
namespace Solidity.Backend.Scalar

structure BinaryInvocation {op : BinOp} {p : PrimTy} {h : op.accepts p = true}
    (c : BinaryCertificate op p h) (a b : p.Denote) (tail : Stack) where
  capacity : stackBound c.code ((tail.length+2 : Nat) : Int) = true

def BinaryInvocation.bytes {op : BinOp} {p : PrimTy} {h : op.accepts p = true}
    {c : BinaryCertificate op p h} {a b : p.Denote} {tail : Stack}
    (_ : BinaryInvocation c a b tail) : List UInt8 := Backend.encode c.code

theorem BinaryInvocation.decode_bytes {op : BinOp} {p : PrimTy} {h : op.accepts p = true}
    {c : BinaryCertificate op p h} {a b : p.Denote} {tail : Stack}
    (v : BinaryInvocation c a b tail) : Backend.decode v.bytes = some c.code :=
  Backend.decode_encode c.code

theorem BinaryInvocation.correct {op : BinOp} {p : PrimTy} {h : op.accepts p = true}
    {c : BinaryCertificate op p h} {a b : p.Denote} {tail : Stack}
    (_ : BinaryInvocation c a b tail) :
    run c.code (encodeValue p a::encodeValue p b::tail) =
      (op.evalT h a b).map (fun r => encodeValue (op.ret p) r::tail) := c.correct a b tail

theorem BinaryInvocation.prefix_safe {op : BinOp} {p : PrimTy} {h : op.accepts p = true}
    {c : BinaryCertificate op p h} {a b : p.Denote} {tail : Stack}
    (v : BinaryInvocation c a b tail) (before after : Program) (he : before++after=c.code)
    {st : Stack} (hr : run before (encodeValue p a::encodeValue p b::tail) = some st) :
    st.length ≤ 1024 := by
  apply prefix_capacity before after hr
  rw [he]
  exact v.capacity

structure CheckedInvocation {op : BinOp} {p : PrimTy} {h : op.accepts p = true}
    (c : CheckedCertificate op p h) (a b : p.Denote) (tail : Stack) where
  testCapacity : stackBound c.test ((tail.length+2 : Nat) : Int) = true
  bodyCapacity : stackBound c.body ((tail.length+2 : Nat) : Int) = true

def CheckedInvocation.testBytes {op : BinOp} {p : PrimTy} {h : op.accepts p = true}
    {c : CheckedCertificate op p h} {a b : p.Denote} {tail : Stack}
    (_ : CheckedInvocation c a b tail) : List UInt8 := Backend.encode c.test

def CheckedInvocation.bodyBytes {op : BinOp} {p : PrimTy} {h : op.accepts p = true}
    {c : CheckedCertificate op p h} {a b : p.Denote} {tail : Stack}
    (_ : CheckedInvocation c a b tail) : List UInt8 := Backend.encode c.body

theorem CheckedInvocation.correct {op : BinOp} {p : PrimTy} {h : op.accepts p = true}
    {c : CheckedCertificate op p h} {a b : p.Denote} {tail : Stack}
    (_ : CheckedInvocation c a b tail) :
    guarded c.test c.body overflowFailure (encodeValue p a::encodeValue p b::tail) =
      some (checkedOutcome (op.ret p) (op.evalT h a b) tail) := c.correct a b tail

theorem CheckedInvocation.testPrefix_safe {op : BinOp} {p : PrimTy} {h : op.accepts p = true}
    {c : CheckedCertificate op p h} {a b : p.Denote} {tail : Stack}
    (v : CheckedInvocation c a b tail) (before after : Program) (he : before++after=c.test)
    {st : Stack} (hr : run before (encodeValue p a::encodeValue p b::tail) = some st) :
    st.length ≤ 1024 := by
  apply prefix_capacity before after hr
  rw [he]
  exact v.testCapacity

/-- An inhabited invocation stores concrete capacity evidence, including DUP peaks. -/
def checkedAdditionWitness : CheckedInvocation checkedUintAdd
    (⟨255, by decide⟩ : PrimTy.uint.Denote) (⟨1, by decide⟩ : PrimTy.uint.Denote) [99] where
  testCapacity := by decide +kernel
  bodyCapacity := by decide +kernel

/-- Tail preservation cannot be used to bypass physical capacity. -/
example : stackBound checkedUintAdd.test 1023 = false := by decide +kernel


structure ClosedInvocation {C : Contract} {Γ : Ctx} {p : PrimTy} {e : Val C Γ p}
    (c : ClosedCertificate e) (tail : Stack) where
  capacity : stackBound c.code (tail.length : Int) = true

theorem ClosedInvocation.prefix_safe {C : Contract} {Γ : Ctx} {p : PrimTy} {e : Val C Γ p}
    {c : ClosedCertificate e} {tail : Stack} (v : ClosedInvocation c tail)
    (before after : Program) (he : before++after=c.code)
    {st : Stack} (hr : run before tail = some st) : st.length ≤ 1024 := by
  apply prefix_capacity before after hr
  rw [he]
  exact v.capacity

#print axioms ClosedInvocation.prefix_safe

#print axioms BinaryInvocation.correct
#print axioms BinaryInvocation.prefix_safe
#print axioms CheckedInvocation.correct
#print axioms CheckedInvocation.testPrefix_safe
#print axioms checkedAdditionWitness
end Solidity.Backend.Scalar
