import Solidity.Backend.Passes.StatefulValues

/-! Apply the owner's separate universal division/remainder contracts. Zero
division and signed overflow stay distinct component failures; the existing
symbolic boundary is coarse revert. No arithmetic or guard execution is copied. -/
namespace Solidity.Backend.Passes.StatefulDivision
variable {C : Contract} {Γ : Ctx} {p : PrimTy} {σ : State C Γ}
  {b L frame : Nat} {F : Evm.Frag Γ} {base : Nat → Fin Evm.W} {m : Evm.Machine}

theorem physical {op : BinOp} {h : op.accepts p = true} {left right : Val C Γ p}
    (whole : Evm.Memory.CompiledVal b F (.binop op h rfl left right))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a d : p.Denote} (hl : left.evalT σ = .ok a) (hr : right.evalT σ = .ok d)
    (short : op.shortT a = none) (tail : List Evm.Word) :
    Evm.ValOutT (op.ret p) (TRes.ofOpt (op.evalT h a d))
      (Evm.run whole.code {m with stack := tail}) {m with stack := tail} := by
  have hc := whole.cert.correct (input.stack tail)
  change Evm.ValOutT (op.ret p) ((Val.binop op h rfl left right).evalT σ)
    (Evm.run whole.code {m with stack := tail}) {m with stack := tail} at hc
  rw [StatefulValues.binary_source hl hr short] at hc
  exact hc

theorem uint_division {left right : Val C Γ .uint}
    (whole : Evm.Memory.CompiledVal b F (.binop .div rfl rfl left right))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a d : PrimTy.uint.Denote} (hl : left.evalT σ = .ok a) (hr : right.evalT σ = .ok d)
    (saved : List (Fin Evm.W))
    (testCapacity : Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) ((saved.length+2 : Nat) : Int) = true)
    (bodyCapacity : Backend.Scalar.stackBound [.op .DIV] ((saved.length+2 : Nat) : Int) = true) :
    Evm.ValOutT .uint (TRes.ofOpt (BinOp.div.evalT rfl a d))
      (Evm.run whole.code {m with stack := saved.map Evm.Word.val}) {m with stack := saved.map Evm.Word.val} ∧
    Backend.Scalar.guarded (Backend.Scalar.zeroTest ⟨1,by decide⟩) [.op .DIV] Backend.Scalar.divisionFailure
      (Backend.Scalar.encodeValue .uint a :: Backend.Scalar.encodeValue .uint d ::
        saved.map (fun w => BitVec.ofNat 256 w.val)) =
      some (Backend.Scalar.divisionOutcome .uint (BinOp.div.evalT rfl a d)
        (saved.map (fun w => BitVec.ofNat 256 w.val))) ∧
    Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) ((saved.length+2 : Nat) : Int) = true ∧
    Backend.Scalar.stackBound [.op .DIV] ((saved.length+2 : Nat) : Int) = true :=
  ⟨physical whole input hl hr rfl _,Backend.Scalar.uint_div_correct a d _,testCapacity,bodyCapacity⟩

theorem uint_remainder {left right : Val C Γ .uint}
    (whole : Evm.Memory.CompiledVal b F (.binop .mod rfl rfl left right))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a d : PrimTy.uint.Denote} (hl : left.evalT σ = .ok a) (hr : right.evalT σ = .ok d)
    (saved : List (Fin Evm.W))
    (testCapacity : Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) ((saved.length+2 : Nat) : Int) = true)
    (bodyCapacity : Backend.Scalar.stackBound [.op .MOD] ((saved.length+2 : Nat) : Int) = true) :
    Evm.ValOutT .uint (TRes.ofOpt (BinOp.mod.evalT rfl a d))
      (Evm.run whole.code {m with stack := saved.map Evm.Word.val}) {m with stack := saved.map Evm.Word.val} ∧
    Backend.Scalar.guarded (Backend.Scalar.zeroTest ⟨1,by decide⟩) [.op .MOD] Backend.Scalar.divisionFailure
      (Backend.Scalar.encodeValue .uint a :: Backend.Scalar.encodeValue .uint d ::
        saved.map (fun w => BitVec.ofNat 256 w.val)) =
      some (Backend.Scalar.divisionOutcome .uint (BinOp.mod.evalT rfl a d)
        (saved.map (fun w => BitVec.ofNat 256 w.val))) ∧
    Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) ((saved.length+2 : Nat) : Int) = true ∧
    Backend.Scalar.stackBound [.op .MOD] ((saved.length+2 : Nat) : Int) = true :=
  ⟨physical whole input hl hr rfl _,Backend.Scalar.uint_mod_correct a d _,testCapacity,bodyCapacity⟩

theorem int_remainder {left right : Val C Γ .int}
    (whole : Evm.Memory.CompiledVal b F (.binop .mod rfl rfl left right))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a d : PrimTy.int.Denote} (hl : left.evalT σ = .ok a) (hr : right.evalT σ = .ok d)
    (saved : List (Fin Evm.W))
    (testCapacity : Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) ((saved.length+2 : Nat) : Int) = true)
    (bodyCapacity : Backend.Scalar.stackBound [.op .SMOD] ((saved.length+2 : Nat) : Int) = true) :
    Evm.ValOutT .int (TRes.ofOpt (BinOp.mod.evalT rfl a d))
      (Evm.run whole.code {m with stack := saved.map Evm.Word.val}) {m with stack := saved.map Evm.Word.val} ∧
    Backend.Scalar.guarded (Backend.Scalar.zeroTest ⟨1,by decide⟩) [.op .SMOD] Backend.Scalar.divisionFailure
      (Backend.Scalar.encodeValue .int a :: Backend.Scalar.encodeValue .int d ::
        saved.map (fun w => BitVec.ofNat 256 w.val)) =
      some (Backend.Scalar.divisionOutcome .int (BinOp.mod.evalT rfl a d)
        (saved.map (fun w => BitVec.ofNat 256 w.val))) ∧
    Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) ((saved.length+2 : Nat) : Int) = true ∧
    Backend.Scalar.stackBound [.op .SMOD] ((saved.length+2 : Nat) : Int) = true :=
  ⟨physical whole input hl hr rfl _,Backend.Scalar.int_mod_correct a d _,testCapacity,bodyCapacity⟩

theorem int_division {left right : Val C Γ .int}
    (whole : Evm.Memory.CompiledVal b F (.binop .div rfl rfl left right))
    (input : Evm.Memory.StateRepr L b frame F σ base m)
    {a d : PrimTy.int.Denote} (hl : left.evalT σ = .ok a) (hr : right.evalT σ = .ok d)
    (saved : List (Fin Evm.W))
    (zeroCapacity : Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) ((saved.length+2 : Nat) : Int) = true)
    (overflowCapacity : Backend.Scalar.stackBound Backend.Scalar.signedDivOverflowTest ((saved.length+2 : Nat) : Int) = true)
    (bodyCapacity : Backend.Scalar.stackBound [.op .SDIV] ((saved.length+2 : Nat) : Int) = true) :
    Evm.ValOutT .int (TRes.ofOpt (BinOp.div.evalT rfl a d))
      (Evm.run whole.code {m with stack := saved.map Evm.Word.val}) {m with stack := saved.map Evm.Word.val} ∧
    Backend.Scalar.signedDivExecute
      (Backend.Scalar.encodeValue .int a :: Backend.Scalar.encodeValue .int d ::
        saved.map (fun w => BitVec.ofNat 256 w.val)) =
      some (Backend.Scalar.signedDivOutcome a d (saved.map (fun w => BitVec.ofNat 256 w.val))) ∧
    Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) ((saved.length+2 : Nat) : Int) = true ∧
    Backend.Scalar.stackBound Backend.Scalar.signedDivOverflowTest ((saved.length+2 : Nat) : Int) = true ∧
    Backend.Scalar.stackBound [.op .SDIV] ((saved.length+2 : Nat) : Int) = true :=
  ⟨physical whole input hl hr rfl _,Backend.Scalar.int_div_correct a d _,zeroCapacity,overflowCapacity,bodyCapacity⟩

end Solidity.Backend.Passes.StatefulDivision
