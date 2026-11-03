import Solidity.Backend.Scalar.Wrapping
import Solidity.Backend.Scalar.Capacity
import Solidity.Backend.Environment.Composition
import Solidity.Backend.Passes.ValueCertificate

/-! Applications of the published scalar/environment certificates. Both
component semantics remain independent; only the shared SUB slice is joined.
This does not assert fetched EVM execution, public gas, or Source lowering. -/
namespace Solidity.Backend.Passes.PublishedValues

/-- Word representation transport, not a second arithmetic implementation. -/
theorem encode_wrap_sub (a b : PrimTy.uint.Denote) :
    Backend.Scalar.encodeValue .uint (Backend.Environment.wrap (a.val.toNat + 2^256 - b.val.toNat)) =
      Backend.Scalar.encodeValue .uint a - Backend.Scalar.encodeValue .uint b := by
  apply BitVec.eq_of_toNat_eq
  rw [Backend.Scalar.encode_uint_toNat, Backend.Environment.wrap_nat, BitVec.toNat_sub,
    Backend.Scalar.encode_uint_toNat, Backend.Scalar.encode_uint_toNat]
  have hb := Backend.Scalar.uint_range b
  congr 1
  omega

/-- Use the owner's typed scalar certificate to recover the actual intrinsic
result of the same SUB, without duplicating the wrapping arithmetic proof. -/
theorem sub_result (a b : PrimTy.uint.Denote) :
    BinOp.subW.evalT rfl a b = some (Backend.Environment.wrap (a.val.toNat + 2^256 - b.val.toNat)) := by
  have hc := Backend.Scalar.wrappingSub.correct a b []
  change some [Backend.Scalar.encodeValue .uint a - Backend.Scalar.encodeValue .uint b] = _ at hc
  cases hs : BinOp.subW.evalT rfl a b with
  | none => rw [hs] at hc; cases hc
  | some v =>
    rw [hs] at hc
    have he : Backend.Scalar.encodeValue .uint a - Backend.Scalar.encodeValue .uint b = Backend.Scalar.encodeValue .uint v :=
      (List.cons.inj (Option.some.inj hc)).1
    have hv : v = Backend.Environment.wrap (a.val.toNat + 2^256 - b.val.toNat) :=
      Backend.Scalar.encode_uint_injective (he.symm.trans (encode_wrap_sub a b).symm)
    exact congrArg some hv

variable {C : Contract} {Γ : Ctx}
def expression (k : EnvKey) (rhs : PrimTy.uint.Denote) : Val C Γ .uint :=
  .binop .subW rfl rfl (.simple (.env k rfl)) (.simple (.lit rhs.val rhs.property))

theorem source (σ : State C Γ) (f : Backend.Environment.Frame) (rep : Backend.Environment.Represents f σ)
    (k : EnvKey) (rhs : PrimTy.uint.Denote) :
    (expression (C := C) (Γ := Γ) k rhs).evalT σ =
      .ok (Backend.Environment.wrap ((Backend.Environment.observe f k).val.toNat + 2^256 - rhs.val.toNat)) := by
  simp only [expression, Val.evalT, Simple.evalT, BinOp.shortT, rep.denote,
    sub_result, TRes.ofOpt, Except.bind, Except.instMonad, PrimTy.ofLit]

/-- Actual shared emitted SUB and existing environment slice; memory is framed. -/
theorem suffix (f : Backend.Environment.Frame) (a b : Backend.Environment.Word) (tail : List Backend.Environment.Word) (m : Backend.Environment.Memory) :
    Backend.Environment.runSlice f Backend.Scalar.wrappingSub.code ⟨a::b::tail, m⟩ =
      some ⟨Backend.Environment.wrap (a.val.toNat + 2^256 - b.val.toNat)::tail, m⟩ := rfl

/-- Two evaluated pure values are scheduled right then left so that SUB sees
left on top. The exact supplied environment frame relation is retained. -/
def code (k : EnvKey) (n : Fin (256^1)) : List Backend.Instr :=
  [Backend.Environment.constant 1 n, Backend.Environment.select k] ++ Backend.Scalar.wrappingSub.code

theorem operands (f : Backend.Environment.Frame) (k : EnvKey) (n : Fin (256^1))
    (tail : List Backend.Environment.Word) (m : Backend.Environment.Memory) :
    Backend.Environment.runSlice f [Backend.Environment.constant 1 n, Backend.Environment.select k]
      ⟨tail,m⟩ = some ⟨Backend.Environment.observe f k ::
        lenU n.val (Backend.Environment.constant_bound 1 n)::tail,m⟩ := by
  change Backend.Environment.runSlice f
    ([Backend.Environment.constant 1 n] ++ [Backend.Environment.select k]) ⟨tail,m⟩ = _
  rw [Backend.Environment.runSlice_append, Backend.Environment.slice_constant]
  exact Backend.Environment.slice_select f k _

theorem mixed_run (f : Backend.Environment.Frame) (k : EnvKey) (n : Fin (256^1))
    (tail : List Backend.Environment.Word) (m : Backend.Environment.Memory) :
    Backend.Environment.runSlice f (code k n) ⟨tail, m⟩ =
      some ⟨Backend.Environment.wrap ((Backend.Environment.observe f k).val.toNat + 2^256 - n.val)::tail, m⟩ := by
  rw [code, Backend.Environment.runSlice_append]
  change (Backend.Environment.runSlice f ([Backend.Environment.constant 1 n] ++ [Backend.Environment.select k]) ⟨tail,m⟩).bind _ = _
  rw [Backend.Environment.runSlice_append, Backend.Environment.slice_constant]
  change (Backend.Environment.runSlice f [Backend.Environment.select k]
    ⟨Solidity.lenU n.val (Backend.Environment.constant_bound 1 n)::tail,m⟩).bind _ = _
  rw [Backend.Environment.slice_select]
  change Backend.Environment.runSlice f Backend.Scalar.wrappingSub.code
    ⟨Backend.Environment.observe f k::Solidity.lenU n.val (Backend.Environment.constant_bound 1 n)::tail,m⟩ = _
  simpa only [Solidity.lenU, Int.toNat_natCast] using
    suffix f (Backend.Environment.observe f k) (Solidity.lenU n.val (Backend.Environment.constant_bound 1 n)) tail m

/-- A real reusable environment value certificate over the existing expression,
using the owner's target slice, actual code and independent intrinsic source. -/
def certificate (σ : State C Γ) (f : Backend.Environment.Frame) (rep : Backend.Environment.Represents f σ)
    (k : EnvKey) (n : Fin (256^1)) (m : Backend.Environment.Memory) :
    Backend.Environment.ValueCertificate σ (expression k (Solidity.lenU n.val (Backend.Environment.constant_bound 1 n))) f (code k n) m :=
  { value := Backend.Environment.wrap ((Backend.Environment.observe f k).val.toNat + 2^256 - n.val)
    memoryOut := m
    source := by
      simpa only [Solidity.lenU, Int.toNat_natCast] using
        source σ f rep k (Solidity.lenU n.val (Backend.Environment.constant_bound 1 n))
    target := fun tail => mixed_run f k n tail m }

/-- The same intrinsic result also passes the existing symbolic compilation
value relation. Neither local numeric slice is renamed full EVM semantics. -/
theorem symbolic_value {b L frame : Nat} {F : Evm.Frag Γ}
    (σ : State C Γ) (f : Backend.Environment.Frame) (rep : Backend.Environment.Represents f σ) (k : EnvKey)
    (rhs : PrimTy.uint.Denote)
    (result : Evm.Memory.CompiledVal b F (expression (C := C) k rhs))
    {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (input : Evm.Memory.StateRepr L b frame F σ base machine) (tail : List Evm.Word) :
    ∃ w, Evm.ReprV .uint (Backend.Environment.wrap ((Backend.Environment.observe f k).val.toNat + 2^256 - rhs.val.toNat)) w ∧
      Evm.run result.code {machine with stack := tail} =
        .ok ({machine with stack := tail}.push w) 0 :=
  value_success_tail result input (source σ f rep k rhs) tail

/-- Existing symbolic uint representation and numeric ABI-word encoding agree.
No partial observation of an arbitrary symbolic slot is fabricated. -/
theorem represented_word {v : PrimTy.uint.Denote} {w : Evm.Word}
    (h : Evm.ReprV .uint v w) :
    ∃ a : Fin Evm.W, w = .val a ∧
      Backend.Scalar.encodeValue .uint v = BitVec.ofNat 256 a.val := by
  obtain ⟨a, hw, hv⟩ := h
  refine ⟨a, hw, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [Backend.Scalar.encode_uint_toNat, hv, Int.toNat_natCast,
    BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (show a.val < 2^256 from a.isLt)).symm

/-- Checked application consumes the reached environment value and BOTH
original capacity certificates. Guarded outcomes are the owner's component
boundary, not generic bytecode branch/payload execution. -/
theorem checked_application {op : BinOp} {h : op.accepts .uint = true}
    (c : Backend.Scalar.CheckedCertificate op .uint h)
    (σ : State C Γ) (f : Backend.Environment.Frame) (rep : Backend.Environment.Represents f σ)
    (k : EnvKey) (rhs : PrimTy.uint.Denote) (tail : Backend.Scalar.Stack)
    (invocation : Backend.Scalar.CheckedInvocation c (σ.envVal k) rhs tail) :
    Backend.Scalar.guarded c.test c.body Backend.Scalar.overflowFailure
      (Backend.Scalar.encodeValue .uint (Backend.Environment.observe f k) ::
        Backend.Scalar.encodeValue .uint rhs :: tail) =
      some (Backend.Scalar.checkedOutcome (op.ret .uint)
        (op.evalT h (σ.envVal k) rhs) tail) := by
  rw [← rep.denote k]
  exact invocation.correct

/-- The shared code decoder is used without a second instruction language. -/
theorem decode_code (k : EnvKey) (n : Fin (256^1)) :
    Backend.decode (Backend.encode (code k n)) = some (code k n) :=
  Backend.decode_encode _

end Solidity.Backend.Passes.PublishedValues
