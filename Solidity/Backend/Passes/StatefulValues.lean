import Solidity.Backend.Passes.ClosedValues
import Solidity.Backend.Passes.ValueSequence
import Solidity.Backend.Scalar.Select

/-! State-dependent intrinsic operand applications of PUBLISHED scalar
certificates. Numeric component code and symbolic whole-expression code remain
separate target interfaces. No Source calls/effects or fetched EVM is inferred. -/
namespace Solidity.Backend.Passes.StatefulValues
variable {C : Contract} {Γ : Ctx} {p : PrimTy} {σ : State C Γ}
  {b L frame : Nat} {F : Evm.Frag Γ} {base : Nat → Fin Evm.W} {m : Evm.Machine}

theorem binary_source {op : BinOp} {h : op.accepts p = true}
    {left right : Val C Γ p} {a b : p.Denote}
    (hl : left.evalT σ = .ok a) (hr : right.evalT σ = .ok b)
    (short : op.shortT a = none) :
    (Val.binop op h rfl left right).evalT σ = TRes.ofOpt (op.evalT h a b) := by
  simp only [Val.evalT,hl,hr,short,bind,Except.bind]

theorem unary_source {op : UnOp} {h : op.accepts p = true}
    {e : Val C Γ p} {a : p.Denote} (source : e.evalT σ = .ok a) :
    (Val.unop op h rfl e).evalT σ = TRes.ofOpt (op.evalT h a) := by
  simp only [Val.evalT,source,bind,Except.bind]

/-- Real represented operand LOADS reach canonical numeric words with left
on top. Both operands must independently succeed; this is NOT an eager
evaluation law for skipped or failing source operands. -/
theorem operands {left right : Val C Γ p}
    (lc : Evm.Memory.CompiledVal b F left) (rc : Evm.Memory.CompiledVal b F right)
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a d : p.Denote} (hl : left.evalT σ = .ok a) (hr : right.evalT σ = .ok d)
    (tail : List Evm.Word) :
    ∃ (wa wd : Fin Evm.W),
      Evm.ReprV p a (.val wa) ∧ Evm.ReprV p d (.val wd) ∧
      Backend.Scalar.encodeValue p a = BitVec.ofNat 256 wa.val ∧
      Backend.Scalar.encodeValue p d = BitVec.ofNat 256 wd.val ∧
      Evm.run (rc.code ++ lc.code) {m with stack := tail} =
        .ok (({m with stack := tail}.push (.val wd)).push (.val wa)) 0 := by
  obtain ⟨w1,w2,h1,h2,ht⟩ := value_pair_success_tail rc lc input hr hl tail
  obtain ⟨wd,ed,hd⟩ := ClosedValues.represented_word h1
  obtain ⟨wa,ea,ha⟩ := ClosedValues.represented_word h2
  subst w1
  subst w2
  exact ⟨wa,wd,h2,h1,ha,hd,ht⟩

theorem binary {op : BinOp} {h : op.accepts p = true} {left right : Val C Γ p}
    (c : Backend.Scalar.BinaryCertificate op p h)
    (whole : Evm.Memory.CompiledVal b F (.binop op h rfl left right))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a d : p.Denote} (hl : left.evalT σ = .ok a) (hr : right.evalT σ = .ok d)
    (short : op.shortT a = none) {v : (op.ret p).Denote}
    (operation : op.evalT h a d = some v) (saved : List (Fin Evm.W))
    (invocation : Backend.Scalar.BinaryInvocation c a d (saved.map (fun w => BitVec.ofNat 256 w.val))) :
    (Val.binop op h rfl left right).evalT σ = .ok v ∧
    ∃ w : Fin Evm.W, Evm.ReprV (op.ret p) v (.val w) ∧
      Backend.Scalar.encodeValue (op.ret p) v = BitVec.ofNat 256 w.val ∧
      Backend.Scalar.run c.code
        (Backend.Scalar.encodeValue p a :: Backend.Scalar.encodeValue p d ::
          saved.map (fun w => BitVec.ofNat 256 w.val)) =
        some (BitVec.ofNat 256 w.val :: saved.map (fun w => BitVec.ofNat 256 w.val)) ∧
      Evm.run whole.code {m with stack := saved.map Evm.Word.val} =
        .ok ({m with stack := saved.map Evm.Word.val}.push (.val w)) 0 ∧
      Backend.Scalar.stackBound c.code ((saved.length + 2 : Nat) : Int) = true := by
  have source : (Val.binop op h rfl left right).evalT σ = .ok v := by
    rw [binary_source hl hr short,operation]
    rfl
  obtain ⟨word,hw,ht⟩ := value_success_tail whole input source (saved.map Evm.Word.val)
  obtain ⟨w,ew,he⟩ := ClosedValues.represented_word hw
  subst word
  refine ⟨source,w,hw,he,?_,ht,?_⟩
  · rw [← he]
    simpa only [operation,Option.map_some] using invocation.correct
  · simpa only [List.length_map] using invocation.capacity

theorem unary {op : UnOp} {h : op.accepts p = true} {e : Val C Γ p}
    (c : Backend.Scalar.UnaryCertificate op p h)
    (whole : Evm.Memory.CompiledVal b F (.unop op h rfl e))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a : p.Denote} (hs : e.evalT σ = .ok a) {v : (op.ret p).Denote}
    (operation : op.evalT h a = some v) (saved : List (Fin Evm.W))
    (capacity : Backend.Scalar.stackBound c.code ((saved.length + 1 : Nat) : Int) = true) :
    (Val.unop op h rfl e).evalT σ = .ok v ∧
    ∃ w : Fin Evm.W, Evm.ReprV (op.ret p) v (.val w) ∧
      Backend.Scalar.encodeValue (op.ret p) v = BitVec.ofNat 256 w.val ∧
      Backend.Scalar.run c.code (Backend.Scalar.encodeValue p a ::
        saved.map (fun w => BitVec.ofNat 256 w.val)) =
        some (BitVec.ofNat 256 w.val :: saved.map (fun w => BitVec.ofNat 256 w.val)) ∧
      Evm.run whole.code {m with stack := saved.map Evm.Word.val} =
        .ok ({m with stack := saved.map Evm.Word.val}.push (.val w)) 0 ∧
      Backend.Scalar.stackBound c.code ((saved.length + 1 : Nat) : Int) = true := by
  have source : (Val.unop op h rfl e).evalT σ = .ok v := by
    rw [unary_source hs,operation]
    rfl
  obtain ⟨word,hw,ht⟩ := value_success_tail whole input source (saved.map Evm.Word.val)
  obtain ⟨w,ew,he⟩ := ClosedValues.represented_word hw
  subst word
  refine ⟨source,w,hw,he,?_,ht,capacity⟩
  rw [← he]
  simpa only [operation,Option.map_some] using c.correct a (saved.map (fun w => BitVec.ofNat 256 w.val))

/-- Exact coarse whole-expression failure reflection under the original eager
branch guard. Numeric component failure bytes are a DIFFERENT observation. -/
theorem binary_revert_iff {op : BinOp} {h : op.accepts p = true} {left right : Val C Γ p}
    (whole : Evm.Memory.CompiledVal b F (.binop op h rfl left right))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a d : p.Denote} (hl : left.evalT σ = .ok a) (hr : right.evalT σ = .ok d)
    (short : op.shortT a = none) (tail : List Evm.Word) :
    Evm.run whole.code {m with stack := tail} = .revert ↔ op.evalT h a d = none := by
  rw [value_revert_iff whole input tail,binary_source hl hr short]
  cases operation : op.evalT h a d with
  | none => constructor <;> intro _ <;> rfl
  | some v => constructor <;> intro impossible <;> cases impossible

theorem left_revert {op : BinOp} {h : op.accepts p = true} {left right : Val C Γ p}
    (whole : Evm.Memory.CompiledVal b F (.binop op h rfl left right))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    (failed : left.evalT σ = .error .revert) (tail : List Evm.Word) :
    (Val.binop op h rfl left right).evalT σ = .error .revert ∧
      Evm.run whole.code {m with stack := tail} = .revert := by
  have source : (Val.binop op h rfl left right).evalT σ = .error .revert := by
    simp only [Val.evalT,failed,bind,Except.bind]
  exact ⟨source,(value_revert_iff whole input tail).mpr source⟩

theorem right_revert {op : BinOp} {h : op.accepts p = true} {left right : Val C Γ p}
    (whole : Evm.Memory.CompiledVal b F (.binop op h rfl left right))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a : p.Denote} (hl : left.evalT σ = .ok a) (short : op.shortT a = none)
    (failed : right.evalT σ = .error .revert) (tail : List Evm.Word) :
    (Val.binop op h rfl left right).evalT σ = .error .revert ∧
      Evm.run whole.code {m with stack := tail} = .revert := by
  have source : (Val.binop op h rfl left right).evalT σ = .error .revert := by
    simp only [Val.evalT,hl,short,failed,bind,Except.bind]
  exact ⟨source,(value_revert_iff whole input tail).mpr source⟩

/-- A taken source short circuit has NO right evaluation premise and makes no
claim that the eager numeric primitive was executed. -/
theorem short_taken {op : BinOp} {h : op.accepts p = true} {left right : Val C Γ p}
    (whole : Evm.Memory.CompiledVal b F (.binop op h rfl left right))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a : p.Denote} {v : (op.ret p).Denote} (hl : left.evalT σ = .ok a)
    (short : op.shortT a = some v) (tail : List Evm.Word) :
    (Val.binop op h rfl left right).evalT σ = .ok v ∧
    ∃ w : Fin Evm.W, Evm.ReprV (op.ret p) v (.val w) ∧
      Backend.Scalar.encodeValue (op.ret p) v = BitVec.ofNat 256 w.val ∧
      Evm.run whole.code {m with stack := tail} =
        .ok ({m with stack := tail}.push (.val w)) 0 := by
  have source : (Val.binop op h rfl left right).evalT σ = .ok v := by
    simp only [Val.evalT,hl,short,bind,Except.bind,pure,Except.pure]
  obtain ⟨word,hw,ht⟩ := value_success_tail whole input source tail
  obtain ⟨w,ew,he⟩ := ClosedValues.represented_word hw
  subst word
  exact ⟨source,w,hw,he,ht⟩

end Solidity.Backend.Passes.StatefulValues
