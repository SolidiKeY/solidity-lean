import Solidity.Backend.Passes.StatefulValues

/-! Source-value and operand-word applications of the published modular
certificates. There is deliberately NO whole-expression symbolic certificate:
the current legacy recognizer refuses modular values, recorded in controls. -/
namespace Solidity.Backend.Passes.StatefulModular
variable {C : Contract} {Γ : Ctx} {σ : State C Γ} {b L frame : Nat}
  {F : Evm.Frag Γ} {base : Nat → Fin Evm.W} {m : Evm.Machine}

theorem source (op : ModOp) {left right modulus : Val C Γ .uint}
    {a d k : PrimTy.uint.Denote} (hl : left.evalT σ = .ok a)
    (hr : right.evalT σ = .ok d) (hk : modulus.evalT σ = .ok k) :
    (Val.modular op left right modulus).evalT σ = TRes.ofOpt (op.evalT a d k) := by
  simp only [Val.evalT,hl,hr,hk,bind,Except.bind]

/-- Actual accepted operand compilers provide all three canonical words and
preserve the entire machine under the stack. No numeric memory loader or
unsupported whole-expression compiler is invented. -/
theorem operands {left right modulus : Val C Γ .uint}
    (lc : Evm.Memory.CompiledVal b F left) (rc : Evm.Memory.CompiledVal b F right)
    (kc : Evm.Memory.CompiledVal b F modulus)
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a d k : PrimTy.uint.Denote} (hl : left.evalT σ = .ok a)
    (hr : right.evalT σ = .ok d) (hk : modulus.evalT σ = .ok k)
    (tail : List Evm.Word) :
    ∃ (wa wd wk : Fin Evm.W),
      Evm.ReprV .uint a (.val wa) ∧ Evm.ReprV .uint d (.val wd) ∧ Evm.ReprV .uint k (.val wk) ∧
      Backend.Scalar.encodeValue .uint a = BitVec.ofNat 256 wa.val ∧
      Backend.Scalar.encodeValue .uint d = BitVec.ofNat 256 wd.val ∧
      Backend.Scalar.encodeValue .uint k = BitVec.ofNat 256 wk.val ∧
      Evm.run (kc.code ++ (rc.code ++ lc.code)) {m with stack := tail} =
        .ok ((({m with stack := tail}.push (.val wk)).push (.val wd)).push (.val wa)) 0 := by
  obtain ⟨word,hword,hkc⟩ := value_success_tail kc input hk tail
  obtain ⟨wk,ew,he⟩ := ClosedValues.represented_word hword
  subst word
  obtain ⟨wa,wd,ha,hd,hea,hed,hpair⟩ := StatefulValues.operands lc rc input hl hr (.val wk :: tail)
  refine ⟨wa,wd,wk,ha,hd,hword,hea,hed,he,?_⟩
  rw [Evm.run_append_ok hkc]
  exact hpair

theorem component (op : ModOp) (c : Backend.Scalar.ModularCertificate op)
    {left right modulus : Val C Γ .uint} {a d k : PrimTy.uint.Denote}
    (hl : left.evalT σ = .ok a) (hr : right.evalT σ = .ok d) (hk : modulus.evalT σ = .ok k)
    (saved : List (Fin Evm.W))
    (testCapacity : Backend.Scalar.stackBound c.test ((saved.length+3 : Nat) : Int) = true)
    (bodyCapacity : Backend.Scalar.stackBound c.body ((saved.length+3 : Nat) : Int) = true) :
    (Val.modular op left right modulus).evalT σ = TRes.ofOpt (op.evalT a d k) ∧
      Backend.Scalar.guarded c.test c.body Backend.Scalar.divisionFailure
        (Backend.Scalar.encodeValue .uint a :: Backend.Scalar.encodeValue .uint d ::
          Backend.Scalar.encodeValue .uint k :: saved.map (fun w => BitVec.ofNat 256 w.val)) =
        some (Backend.Scalar.modularOutcome op a d k (saved.map (fun w => BitVec.ofNat 256 w.val))) ∧
      Backend.Scalar.stackBound c.test ((saved.length+3 : Nat) : Int) = true ∧
      Backend.Scalar.stackBound c.body ((saved.length+3 : Nat) : Int) = true :=
  ⟨source op hl hr hk,c.correct a d k _,testCapacity,bodyCapacity⟩

/-- Exact failure-class transport at the EXISTING local guarded boundary.
This does not identify coarse source revert with public ABI bytes. -/
theorem failure_iff (op : ModOp) (c : Backend.Scalar.ModularCertificate op)
    {left right modulus : Val C Γ .uint} {a d k : PrimTy.uint.Denote}
    (hl : left.evalT σ = .ok a) (hr : right.evalT σ = .ok d) (hk : modulus.evalT σ = .ok k)
    (tail : Backend.Scalar.Stack) :
    (Val.modular op left right modulus).evalT σ = .error .revert ↔
      Backend.Scalar.guarded c.test c.body Backend.Scalar.divisionFailure
        (Backend.Scalar.encodeValue .uint a :: Backend.Scalar.encodeValue .uint d ::
          Backend.Scalar.encodeValue .uint k :: tail) = some (.error Backend.Scalar.divisionFailure) := by
  rw [source op hl hr hk,c.correct]
  cases result : op.evalT a d k with
  | none =>
    constructor <;> intro _ <;> simp only [Backend.Scalar.modularOutcome,result,TRes.ofOpt]
  | some v =>
    simp only [TRes.ofOpt,Backend.Scalar.modularOutcome,result,reduceCtorEq]
    constructor
    · intro impossible; cases impossible
    · intro impossible; cases Option.some.inj impossible

private def modularShape {p : PrimTy} : Val C Γ p → Bool
  | .modular .. => true
  | _ => false

private theorem no_modular_shape {p : PrimTy} {e : Val C Γ p} {code : List Evm.Instr}
    (cert : Evm.Memory.ValFrag b F e code) : modularShape e = false := by
  cases cert <;> try rfl
  case core accepted =>
    cases e <;> try rfl
    cases accepted

/-- This is a missing published certificate constructor, not merely failure
of one recognizer call. No current legacy ValFrag can index a modular value. -/
theorem certificate_refused (op : ModOp) (left right modulus : Val C Γ .uint) :
    ¬ Nonempty (Evm.Memory.CompiledVal b F (.modular op left right modulus)) := by
  rintro ⟨⟨code,cert⟩⟩
  have impossible := no_modular_shape cert
  cases impossible

end Solidity.Backend.Passes.StatefulModular
