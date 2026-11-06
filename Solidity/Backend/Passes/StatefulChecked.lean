import Solidity.Backend.Passes.StatefulValues

/-! State-dependent checked component applications. The owner's Panic(0x11)
component boundary and the existing symbolic coarse revert remain distinct.
Both original test/body capacity conditions are retained and exposed. -/
namespace Solidity.Backend.Passes.StatefulChecked
variable {C : Contract} {Γ : Ctx} {p : PrimTy} {σ : State C Γ}
  {b L frame : Nat} {F : Evm.Frag Γ} {base : Nat → Fin Evm.W} {m : Evm.Machine}

theorem binary_success {op : BinOp} {h : op.accepts p = true} {left right : Val C Γ p}
    (c : Backend.Scalar.CheckedCertificate op p h)
    (whole : Evm.Memory.CompiledVal b F (.binop op h rfl left right))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a d : p.Denote} (hl : left.evalT σ = .ok a) (hr : right.evalT σ = .ok d)
    (short : op.shortT a = none) {v : (op.ret p).Denote}
    (operation : op.evalT h a d = some v) (saved : List (Fin Evm.W))
    (invocation : Backend.Scalar.CheckedInvocation c a d (saved.map (fun w => BitVec.ofNat 256 w.val))) :
    (Val.binop op h rfl left right).evalT σ = .ok v ∧
    ∃ w : Fin Evm.W, Evm.ReprV (op.ret p) v (.val w) ∧
      Backend.Scalar.encodeValue (op.ret p) v = BitVec.ofNat 256 w.val ∧
      Backend.Scalar.guarded c.test c.body Backend.Scalar.overflowFailure
        (Backend.Scalar.encodeValue p a :: Backend.Scalar.encodeValue p d ::
          saved.map (fun w => BitVec.ofNat 256 w.val)) =
        some (.ok (BitVec.ofNat 256 w.val :: saved.map (fun w => BitVec.ofNat 256 w.val))) ∧
      Evm.run whole.code {m with stack := saved.map Evm.Word.val} =
        .ok ({m with stack := saved.map Evm.Word.val}.push (.val w)) 0 ∧
      Backend.Scalar.stackBound c.test ((saved.length + 2 : Nat) : Int) = true ∧
      Backend.Scalar.stackBound c.body ((saved.length + 2 : Nat) : Int) = true := by
  have source : (Val.binop op h rfl left right).evalT σ = .ok v := by
    rw [StatefulValues.binary_source hl hr short,operation]
    rfl
  obtain ⟨word,hw,ht⟩ := value_success_tail whole input source (saved.map Evm.Word.val)
  obtain ⟨w,ew,he⟩ := ClosedValues.represented_word hw
  subst word
  refine ⟨source,w,hw,he,?_,ht,?_,?_⟩
  · rw [← he]
    simpa only [operation,Backend.Scalar.checkedOutcome,Option.elim_some] using invocation.correct
  · simpa only [List.length_map] using invocation.testCapacity
  · simpa only [List.length_map] using invocation.bodyCapacity

theorem binary_failure {op : BinOp} {h : op.accepts p = true} {left right : Val C Γ p}
    (c : Backend.Scalar.CheckedCertificate op p h)
    (whole : Evm.Memory.CompiledVal b F (.binop op h rfl left right))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a d : p.Denote} (hl : left.evalT σ = .ok a) (hr : right.evalT σ = .ok d)
    (short : op.shortT a = none) (operation : op.evalT h a d = none)
    (saved : List (Fin Evm.W))
    (invocation : Backend.Scalar.CheckedInvocation c a d (saved.map (fun w => BitVec.ofNat 256 w.val))) :
    (Val.binop op h rfl left right).evalT σ = .error .revert ∧
      Evm.run whole.code {m with stack := saved.map Evm.Word.val} = .revert ∧
      Backend.Scalar.guarded c.test c.body Backend.Scalar.overflowFailure
        (Backend.Scalar.encodeValue p a :: Backend.Scalar.encodeValue p d ::
          saved.map (fun w => BitVec.ofNat 256 w.val)) = some (.error Backend.Scalar.overflowFailure) ∧
      Backend.Scalar.stackBound c.test ((saved.length + 2 : Nat) : Int) = true ∧
      Backend.Scalar.stackBound c.body ((saved.length + 2 : Nat) : Int) = true := by
  have source : (Val.binop op h rfl left right).evalT σ = .error .revert := by
    rw [StatefulValues.binary_source hl hr short,operation]
    rfl
  refine ⟨source,(value_revert_iff whole input _).mpr source,?_,?_,?_⟩
  · simpa only [operation,Backend.Scalar.checkedOutcome,Option.elim_none] using invocation.correct
  · simpa only [List.length_map] using invocation.testCapacity
  · simpa only [List.length_map] using invocation.bodyCapacity

theorem unary_success {op : UnOp} {h : op.accepts p = true} {e : Val C Γ p}
    (c : Backend.Scalar.CheckedUnaryCertificate op p h)
    (whole : Evm.Memory.CompiledVal b F (.unop op h rfl e))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a : p.Denote} (hs : e.evalT σ = .ok a) {v : (op.ret p).Denote}
    (operation : op.evalT h a = some v) (saved : List (Fin Evm.W))
    (testCapacity : Backend.Scalar.stackBound c.test ((saved.length + 1 : Nat) : Int) = true)
    (bodyCapacity : Backend.Scalar.stackBound c.body ((saved.length + 1 : Nat) : Int) = true) :
    (Val.unop op h rfl e).evalT σ = .ok v ∧
    ∃ w : Fin Evm.W, Evm.ReprV (op.ret p) v (.val w) ∧
      Backend.Scalar.encodeValue (op.ret p) v = BitVec.ofNat 256 w.val ∧
      Backend.Scalar.guarded c.test c.body Backend.Scalar.overflowFailure
        (Backend.Scalar.encodeValue p a :: saved.map (fun w => BitVec.ofNat 256 w.val)) =
        some (.ok (BitVec.ofNat 256 w.val :: saved.map (fun w => BitVec.ofNat 256 w.val))) ∧
      Evm.run whole.code {m with stack := saved.map Evm.Word.val} =
        .ok ({m with stack := saved.map Evm.Word.val}.push (.val w)) 0 ∧
      Backend.Scalar.stackBound c.test ((saved.length + 1 : Nat) : Int) = true ∧
      Backend.Scalar.stackBound c.body ((saved.length + 1 : Nat) : Int) = true := by
  have source : (Val.unop op h rfl e).evalT σ = .ok v := by
    rw [StatefulValues.unary_source hs,operation]
    rfl
  obtain ⟨word,hw,ht⟩ := value_success_tail whole input source (saved.map Evm.Word.val)
  obtain ⟨w,ew,he⟩ := ClosedValues.represented_word hw
  subst word
  refine ⟨source,w,hw,he,?_,ht,testCapacity,bodyCapacity⟩
  rw [← he]
  simpa only [operation,Backend.Scalar.checkedOutcome,Option.elim_some] using
    c.correct a (saved.map (fun w => BitVec.ofNat 256 w.val))

theorem unary_failure {op : UnOp} {h : op.accepts p = true} {e : Val C Γ p}
    (c : Backend.Scalar.CheckedUnaryCertificate op p h)
    (whole : Evm.Memory.CompiledVal b F (.unop op h rfl e))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a : p.Denote} (hs : e.evalT σ = .ok a)
    (operation : op.evalT h a = none) (saved : List (Fin Evm.W))
    (testCapacity : Backend.Scalar.stackBound c.test ((saved.length + 1 : Nat) : Int) = true)
    (bodyCapacity : Backend.Scalar.stackBound c.body ((saved.length + 1 : Nat) : Int) = true) :
    (Val.unop op h rfl e).evalT σ = .error .revert ∧
      Evm.run whole.code {m with stack := saved.map Evm.Word.val} = .revert ∧
      Backend.Scalar.guarded c.test c.body Backend.Scalar.overflowFailure
        (Backend.Scalar.encodeValue p a :: saved.map (fun w => BitVec.ofNat 256 w.val)) =
        some (.error Backend.Scalar.overflowFailure) ∧
      Backend.Scalar.stackBound c.test ((saved.length + 1 : Nat) : Int) = true ∧
      Backend.Scalar.stackBound c.body ((saved.length + 1 : Nat) : Int) = true := by
  have source : (Val.unop op h rfl e).evalT σ = .error .revert := by
    rw [StatefulValues.unary_source hs,operation]
    rfl
  refine ⟨source,(value_revert_iff whole input _).mpr source,?_,testCapacity,bodyCapacity⟩
  simpa only [operation,Backend.Scalar.checkedOutcome,Option.elim_none] using
    c.correct a (saved.map (fun w => BitVec.ofNat 256 w.val))

end Solidity.Backend.Passes.StatefulChecked
