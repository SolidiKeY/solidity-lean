import Solidity.Backend.Passes.PublishedValues
import Solidity.Backend.Scalar.SignedChecked

/-! Apply the published uniform closed-value certificate to the SAME intrinsic
expression recognized by the existing symbolic compiler. The two target
semantics stay separate; primitive ABI-word observations agree. -/
namespace Solidity.Backend.Passes.ClosedValues

theorem represented_word {p : PrimTy} {v : p.Denote} {w : Evm.Word}
    (h : Evm.ReprV p v w) :
    ∃ a : Fin Evm.W, w = .val a ∧
      Backend.Scalar.encodeValue p v = BitVec.ofNat 256 a.val := by
  cases p with
  | uint => exact PublishedValues.represented_word h
  | bool =>
    refine ⟨Evm.bword v, h, ?_⟩
    cases v <;> rfl
  | int =>
    obtain ⟨a, hw, hv⟩ := h
    refine ⟨a, hw, ?_⟩
    apply BitVec.eq_of_toInt_eq
    rw [Backend.Scalar.encode_int_toInt, hv, ← Backend.Scalar.sgn_word]
    congr 1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show a.val < 2^256 from a.isLt)]

variable {C : Contract} {Γ : Ctx} {p : PrimTy} {e : Val C Γ p}
  {b L frame : Nat} {F : Evm.Frag Γ}
  {σ : State C Γ} {base : Nat → Fin Evm.W} {m : Evm.Machine}

/-- Independent source and both actual target runs share the represented
primitive value, with all saved words and all symbolic non-stack fields intact.
The supplied numeric invocation retains the original physical capacity check. -/
theorem application (c : Backend.Scalar.ClosedCertificate e)
    (compiled : Evm.Memory.CompiledVal b F e)
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    (saved : List (Fin Evm.W))
    (invocation : Backend.Scalar.ClosedInvocation c
      (saved.map (fun a => BitVec.ofNat 256 a.val))) :
    e.evalT σ = .ok c.value ∧
    ∃ a : Fin Evm.W, Evm.ReprV p c.value (.val a) ∧
      Backend.Scalar.encodeValue p c.value = BitVec.ofNat 256 a.val ∧
      Backend.Scalar.run c.code (saved.map (fun a => BitVec.ofNat 256 a.val)) =
        some (BitVec.ofNat 256 a.val :: saved.map (fun a => BitVec.ofNat 256 a.val)) ∧
      Evm.run compiled.code {m with stack := saved.map Evm.Word.val} =
        .ok ({m with stack := saved.map Evm.Word.val}.push (.val a)) 0 ∧
      Backend.Scalar.stackBound c.code (saved.length : Int) = true := by
  obtain ⟨word, hw, ht⟩ := value_success_tail compiled input (c.source σ)
    (saved.map Evm.Word.val)
  obtain ⟨a, ha, he⟩ := represented_word hw
  subst word
  refine ⟨c.source σ, a, hw, he, ?_, ht, ?_⟩
  · rw [← he]
    exact c.target _
  · simpa only [List.length_map] using invocation.capacity

/-- Prefix adequacy uses the owner's capacity theorem, not just a mathematical
arbitrary-tail execution equation. -/
theorem prefix_capacity (c : Backend.Scalar.ClosedCertificate e)
    (saved : Backend.Scalar.Stack) (invocation : Backend.Scalar.ClosedInvocation c saved)
    (before after : Backend.Program) (code : before ++ after = c.code)
    {reached : Backend.Scalar.Stack}
    (run : Backend.Scalar.run before saved = some reached) : reached.length ≤ 1024 :=
  invocation.prefix_safe before after code run

theorem bytes (c : Backend.Scalar.ClosedCertificate e) :
    Backend.decode c.bytes = some c.code := Backend.decode_encode c.code

end Solidity.Backend.Passes.ClosedValues
