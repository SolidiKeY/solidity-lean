import Solidity.Evm.MemoryObjectAllocator
import Solidity.Evm.MemoryExpr

/-! Composition over the stronger typed object relation. Target code and
arithmetic tails are shared with MemoryExpr; these proofs thread the stronger
heap through operand stacks, including fallible fixed-array reads. -/
namespace Solidity.Evm.Memory.Objects
variable {C : Contract}

def ValueSim {Γ : Ctx} (L b frame : Nat) (F : Frag Γ) (σ : State C Γ)
    (base : Nat → Fin W) {p : PrimTy} (e : Val C Γ p) (code : List Instr) : Prop :=
  ∀ {m : Machine}, StateRepr L b frame F σ base m → ValOutT p (e.evalT σ) (run code m) m

theorem binaryValue_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {p : PrimTy}
    (op : BinOp) (hop : binInFrag op p = true) (hacc : op.accepts p = true)
    (x y : Val C Γ p) (left right : List Instr)
    (hx : ValueSim L b frame F σ base x left) (hy : ValueSim L b frame F σ base y right)
    (h : StateRepr L b frame F σ base m) :
    ValOutT (op.ret p) ((Val.binop op hacc rfl x y).evalT σ)
      (run (binaryCode p op left right) m) m := by
  simp only [Solidity.Val.evalT]
  by_cases hand : op = .and
  · subst hand
    obtain rfl : p = .bool := by cases p <;> simp only [binInFrag, BEq.rfl, beq_iff_eq,
        reduceCtorEq] at hop ⊢
    simp only [binaryCode, List.append_assoc]
    rcases hx h with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
    · obtain rfl := hra.bool_inv
      rw [run_append_ok hruna, hva]
      cases va
      · refine .inl ⟨false, .val (bword false), rfl, rfl, ?_⟩
        rw [show [Instr.dup 1, .iszero, .jumpi (right.length + 1), .pop] ++
            right = [Instr.dup 1, .iszero, .jumpi (right.length + 1)] ++
            ([.pop] ++ right) from rfl,
          run_append_skip (m' := m.push (.val (bword false)))
          (k := right.length + 1) rfl]
        exact exec_length ([.pop] ++ right) _
      · rw [show [Instr.dup 1, .iszero, .jumpi (right.length + 1), .pop] ++
            right = [Instr.dup 1, .iszero, .jumpi (right.length + 1), .pop] ++
            right from rfl, run_append_ok (m' := m) rfl]
        rcases hy h with ⟨vb, wb, hvb, hrb, hrunb⟩ | ⟨hvb, hrunb⟩
        · obtain rfl := hrb.bool_inv
          refine .inl ⟨vb, .val (bword vb), ?_, rfl, hrunb⟩
          simp only [bind, Except.bind, BinOp.shortT, Solidity.boolT, hvb, ↓reduceIte]
          cases vb <;> rfl
        · exact .inr ⟨by simp only [bind, Except.bind, BinOp.shortT, Solidity.boolT, hvb,
            ↓reduceIte], hrunb⟩
    · exact .inr ⟨by simp only [bind, Except.bind, hva], run_append_revert hruna⟩
  by_cases hor : op = .or
  · subst hor
    obtain rfl : p = .bool := by cases p <;> simp only [binInFrag, BEq.rfl, beq_iff_eq,
        reduceCtorEq] at hop ⊢
    simp only [binaryCode, List.append_assoc]
    rcases hx h with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
    · obtain rfl := hra.bool_inv
      rw [run_append_ok hruna, hva]
      cases va
      · rw [show [Instr.dup 1, .jumpi (right.length + 1), .pop] ++ right
          = [Instr.dup 1, .jumpi (right.length + 1), .pop] ++ right
          from rfl, run_append_ok (m' := m) rfl]
        rcases hy h with ⟨vb, wb, hvb, hrb, hrunb⟩ | ⟨hvb, hrunb⟩
        · obtain rfl := hrb.bool_inv
          refine .inl ⟨vb, .val (bword vb), ?_, rfl, hrunb⟩
          simp only [bind, Except.bind, BinOp.shortT, Solidity.boolT, hvb,
            Bool.false_eq_true, ↓reduceIte]
          cases vb <;> rfl
        · exact .inr ⟨by simp only [bind, Except.bind, BinOp.shortT, Solidity.boolT, hvb,
            Bool.false_eq_true, ↓reduceIte], hrunb⟩
      · refine .inl ⟨true, .val (bword true), rfl, rfl, ?_⟩
        rw [show [Instr.dup 1, .jumpi (right.length + 1), .pop] ++ right
          = [Instr.dup 1, .jumpi (right.length + 1)] ++ ([.pop] ++ right)
          from rfl, run_append_skip (m' := m.push (.val (bword true)))
          (k := right.length + 1) rfl]
        exact exec_length ([.pop] ++ right) _
    · exact .inr ⟨by simp only [bind, Except.bind, hva], run_append_revert hruna⟩
  have hcode : binaryCode p op left right =
      left ++ right ++ binTail p op := by
    cases op <;> simp_all only [reduceCtorEq, not_false_eq_true, binaryCode,
        List.append_assoc, not_true_eq_false]
  rw [hcode, List.append_assoc]
  rcases hx h with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
  · rw [run_append_ok hruna, hva]
    have hs : op.shortT va = none := by
      cases op <;> cases p <;> simp_all only [BinOp.shortT, not_true_eq_false,
        reduceCtorEq, not_false_eq_true]
    simp only [bind, Except.bind, hs]
    rcases hy (h.push wa) with ⟨vb, wb, hvb, hrb, hrunb⟩ | ⟨hvb, hrunb⟩
    · rw [run_append_ok hrunb, hvb]
      exact tail_simT hop hand hor hacc hra hrb m
    · exact .inr ⟨by rw [hvb], run_append_revert hrunb⟩
  · exact .inr ⟨by simp only [bind, Except.bind, hva], run_append_revert hruna⟩

theorem unaryValue_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {p : PrimTy}
    (op : UnOp) (hop : unInFrag op p = true) (hacc : op.accepts p = true)
    (x : Val C Γ p) (code : List Instr) (hx : ValueSim L b frame F σ base x code)
    (h : StateRepr L b frame F σ base m) :
    ValOutT (op.ret p) ((Val.unop op hacc rfl x).evalT σ) (run (unaryCode op code) m) m := by
  have key : ∀ {va : p.Denote}, x.evalT σ = .ok va →
      (Solidity.Val.unop op hacc rfl x).evalT σ = TRes.ofOpt (op.evalT hacc va) := fun h => by
    simp only [Solidity.Val.evalT, h, bind, Except.bind]
  have err : ∀ {e : Solidity.THalt}, x.evalT σ = .error e →
      (Solidity.Val.unop op hacc rfl x).evalT σ = .error e := fun h => by
    simp only [Solidity.Val.evalT, h, bind, Except.bind]
  cases op with
  | not =>
    obtain rfl : p = .bool := by cases p <;> simp only [UnOp.accepts, BEq.rfl, beq_iff_eq,
        reduceCtorEq] at hacc ⊢
    simp only [unaryCode]
    rcases hx h with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
    · obtain rfl := hra.bool_inv
      rw [run_append_ok hruna, key hva]
      refine .inl ⟨!va, .val (bword !va), rfl, rfl, ?_⟩
      cases va <;> rfl
    · exact .inr ⟨err hva, run_append_revert hruna⟩
  | neg =>
    obtain rfl : p = .int := by simpa only [unInFrag, beq_iff_eq] using hop
    simp only [unaryCode]
    rcases hx h with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
    · rw [run_append_ok hruna, key hva]
      exact neg_simT hra m
    · exact .inr ⟨err hva, run_append_revert hruna⟩
  | bnot =>
    obtain rfl : p = .uint := by simpa only [unInFrag, beq_iff_eq] using hop
    simp only [unaryCode]
    rcases hx h with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
    · rw [run_append_ok hruna, key hva]
      exact bnot_simT hra m
    · exact .inr ⟨err hva, run_append_revert hruna⟩
  | toInt =>
    obtain rfl : p = .uint := by simpa only [unInFrag, beq_iff_eq] using hop
    simp only [unaryCode]
    rcases hx h with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
    · rw [run_append_ok hruna, key hva]
      exact toInt_simT hra m
    · exact .inr ⟨err hva, run_append_revert hruna⟩
  | toUint =>
    obtain rfl : p = .int := by simpa only [unInFrag, beq_iff_eq] using hop
    simp only [unaryCode]
    rcases hx h with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
    · rw [run_append_ok hruna, key hva]
      exact toUint_simT hra m
    · exact .inr ⟨err hva, run_append_revert hruna⟩

theorem conditionalValue_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {p : PrimTy}
    (c : Val C Γ .bool) (x y : Val C Γ p) (cond left right : List Instr)
    (hc : ValueSim L b frame F σ base c cond) (hx : ValueSim L b frame F σ base x left)
    (hy : ValueSim L b frame F σ base y right) (h : StateRepr L b frame F σ base m) :
    ValOutT p ((Val.ternary c x y).evalT σ) (run (conditionalCode cond left right) m) m := by
  simp only [Solidity.Val.evalT, conditionalCode, List.append_assoc]
  rcases hc h with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain rfl := hrc.bool_inv
    rw [run_append_ok hrunc, hvc]
    simp only [bind, Except.bind, Solidity.boolT]
    cases vc
    · rw [run_append_skip (m' := m) (k := left.length + 1) rfl,
        show left.length + 1 = left.length + 1 from rfl, exec_append,
        exec_skip]
      simp only [Out.ok_bind, Bool.false_eq_true, ↓reduceIte]
      exact hy h
    · rw [run_append_skip (m' := m) (k := 0) rfl]
      simp only [↓reduceIte]
      rcases hx h with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
      · refine .inl ⟨va, wa, hva, hra, ?_⟩
        change run _ m = _
        rw [run_append_ok hruna]
        exact exec_length _ _
      · exact .inr ⟨hva, run_append_revert hruna⟩
  · exact .inr ⟨by simp only [bind, Except.bind, hvc], run_append_revert hrunc⟩

end Solidity.Evm.Memory.Objects
