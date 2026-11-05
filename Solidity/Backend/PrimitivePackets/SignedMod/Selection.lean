import Solidity.Backend.PrimitivePackets.SignedMod.Source
import Solidity.Backend.Passes.StatefulDivision

/-! Public compiler selection for the entire pure signed-local remainder family.
The certificate is constructed here and proved to be the public compiler result;
it is never a caller-supplied desired compilation. Numeric component code and
the symbolic memory machine retain their original separate observation boundary. -/
namespace Solidity.Backend.PrimitivePackets.SignedMod
open Solidity.Lowering.V07 Solidity.Backend.Passes
variable {C : Contract} {Γ : Ctx}

def expression (a d : Idx Γ (.val .int)) : Val C Γ .int :=
  .binop .mod rfl rfl (.simple (.local a)) (.simple (.local d))

def selected (b : Nat) (F : Evm.Frag Γ) (a d : Idx Γ (.val .int)) :
    Evm.Memory.CompiledVal b F (expression (C := C) a d) :=
  ⟨Evm.Memory.binaryCode .int .mod [.mload (Evm.cellOf b a)] [.mload (Evm.cellOf b d)],
    .binary .mod rfl rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩

theorem public_selection (b : Nat) (F : Evm.Frag Γ) (a d : Idx Γ (.val .int)) :
    Evm.Memory.compileVal b F (expression (C := C) a d) = some (selected (C := C) b F a d) := rfl

theorem target_nonzero (x y : Int) (hx : Range x) (hy : Range y) (nonzero : y ≠ 0) :
    BinOp.mod.evalT rfl (lower x hx) (lower y hy) =
      some (lower (x.tmod y) (remainder_range x y hy nonzero)) := by
  change ((if y = 0 then none else some (x.tmod y)).bind PrimTy.int.ofInt?) = _
  rw [if_neg nonzero, Option.bind_some]
  exact dif_pos (integer_range ty (x.tmod y) (remainder_range x y hy nonzero))

theorem target_zero (x : Int) (hx : Range x) (hz : Range 0) :
    BinOp.mod.evalT rfl (lower x hx) (lower 0 hz) = none := rfl

theorem int_repr_unique {v : PrimTy.int.Denote} {a b : Evm.Word}
    (ha : Evm.ReprV .int v a) (hb : Evm.ReprV .int v b) : a = b := by
  obtain ⟨x, rfl, hx⟩ := ha
  obtain ⟨y, rfl, hy⟩ := hb
  exact congrArg Evm.Word.val (Fin.ext (Evm.sgn_inj x.isLt y.isLt (hx.symm.trans hy)))

/-- General selected-code application with independent Source local origins.
The physical input relates the actual intrinsic state to the machine; initial
local content alignment is the only Source/target scalar premise. All Source
state and all symbolic non-stack fields are retained on success. Failure keeps
Source Panic(0x12) distinct from the target's coarse revert. -/
theorem selected_remainder {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (sa sd : Source.Idx srcΓ (.int ty)) (ta td : Idx Γ (.val .int))
    (x y : Int) (hx : Range x) (hy : Range y)
    (readA : source.1.get sa = .int x hx) (readD : source.1.get sd = .int y hy)
    (targetA : TEnv.get ta target.env = lower x hx)
    (targetD : TEnv.get td target.env = lower y hy)
    (b L frame : Nat) (F : Evm.Frag Γ) (base : Nat → Fin Evm.W) (m : Evm.Machine)
    (input : Evm.Memory.StateRepr L b frame F target base m)
    (saved : List (Fin Evm.W))
    (testCapacity : Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1, by decide⟩)
      ((saved.length + 2 : Nat) : Int) = true)
    (bodyCapacity : Backend.Scalar.stackBound [.op .SMOD] ((saved.length + 2 : Nat) : Int) = true) :
    Evm.Memory.compileVal b F (expression (C := C) ta td) = some (selected (C := C) b F ta td) ∧
    (Source.evalE G Fsrc (fuel + 3) (.binary .mod (.local sa) (.local sd))).run source =
      ((Source.binVal Fsrc.checked .mod (.int x hx : Source.Val E.layout (.int ty))
        (.int y hy)).map Source.RVal.val, source) ∧
    Evm.ValOutT .int (TRes.ofOpt (BinOp.mod.evalT rfl (lower x hx) (lower y hy)))
      (Evm.run (selected (C := C) b F ta td).code {m with stack := saved.map Evm.Word.val})
      {m with stack := saved.map Evm.Word.val} ∧
    Backend.Scalar.guarded (Backend.Scalar.zeroTest ⟨1, by decide⟩) [.op .SMOD]
      Backend.Scalar.divisionFailure
      (Backend.Scalar.encodeValue .int (lower x hx) :: Backend.Scalar.encodeValue .int (lower y hy) ::
        saved.map (fun w => BitVec.ofNat 256 w.val)) =
      some (Backend.Scalar.divisionOutcome .int (BinOp.mod.evalT rfl (lower x hx) (lower y hy))
        (saved.map (fun w => BitVec.ofNat 256 w.val))) := by
  have left : (Val.simple (.local ta) : Val C Γ .int).evalT target = .ok (lower x hx) :=
    congrArg Except.ok targetA
  have right : (Val.simple (.local td) : Val C Γ .int).evalT target = .ok (lower y hy) :=
    congrArg Except.ok targetD
  have runs := StatefulDivision.int_remainder (selected (C := C) b F ta td) input left right saved
    testCapacity bodyCapacity
  exact ⟨public_selection b F ta td,
    source_locals G Fsrc fuel source sa sd x y hx hy readA readD, runs.1, runs.2.1⟩

/-- Exact success machine, including arbitrary saved stack and every protected
field. This symbolic machine law does not assert a numeric stack-capacity waiver. -/
theorem selected_success (target : State C Γ) (a d : Idx Γ (.val .int))
    (x y : Int) (hx : Range x) (hy : Range y) (nonzero : y ≠ 0)
    (readA : TEnv.get a target.env = lower x hx)
    (readD : TEnv.get d target.env = lower y hy)
    (b L frame : Nat) (F : Evm.Frag Γ) (base : Nat → Fin Evm.W) (m : Evm.Machine)
    (input : Evm.Memory.StateRepr L b frame F target base m) (tail : List Evm.Word) :
    ∃ w : Evm.Word, Evm.ReprV .int (lower (x.tmod y) (remainder_range x y hy nonzero)) w ∧
      Evm.run (selected (C := C) b F a d).code {m with stack := tail} =
        .ok ({m with stack := tail}.push w) 0 := by
  have left : (Val.simple (.local a) : Val C Γ .int).evalT target = .ok (lower x hx) :=
    congrArg Except.ok readA
  have right : (Val.simple (.local d) : Val C Γ .int).evalT target = .ok (lower y hy) :=
    congrArg Except.ok readD
  have value : (expression (C := C) a d).evalT target =
      .ok (lower (x.tmod y) (remainder_range x y hy nonzero)) := by
    rw [expression, StatefulValues.binary_source left right rfl, target_nonzero x y hx hy nonzero]
    rfl
  exact value_success_tail (selected (C := C) b F a d) input value tail

theorem selected_zero (target : State C Γ) (a d : Idx Γ (.val .int))
    (x : Int) (hx : Range x) (hz : Range 0)
    (readA : TEnv.get a target.env = lower x hx)
    (readD : TEnv.get d target.env = lower 0 hz)
    (b L frame : Nat) (F : Evm.Frag Γ) (base : Nat → Fin Evm.W) (m : Evm.Machine)
    (input : Evm.Memory.StateRepr L b frame F target base m) (tail : List Evm.Word) :
    Evm.run (selected (C := C) b F a d).code {m with stack := tail} = .revert := by
  have left : (Val.simple (.local a) : Val C Γ .int).evalT target = .ok (lower x hx) :=
    congrArg Except.ok readA
  have right : (Val.simple (.local d) : Val C Γ .int).evalT target = .ok (lower 0 hz) :=
    congrArg Except.ok readD
  apply (value_revert_iff (selected (C := C) b F a d) input tail).mpr
  rw [expression, StatefulValues.binary_source left right rfl, target_zero x hx hz]
  rfl

/-- Independent Source-local evaluation through the public-selected code.
No desired Source execution, supplied CompiledVal or poststate is accepted. -/
theorem origin_success {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (sa sd : Source.Idx srcΓ (.int ty)) (ta td : Idx Γ (.val .int))
    (x y : Int) (hx : Range x) (hy : Range y) (nonzero : y ≠ 0)
    (readA : source.1.get sa = .int x hx) (readD : source.1.get sd = .int y hy)
    (targetA : TEnv.get ta target.env = lower x hx)
    (targetD : TEnv.get td target.env = lower y hy)
    (b L frame : Nat) (F : Evm.Frag Γ) (base : Nat → Fin Evm.W) (m : Evm.Machine)
    (input : Evm.Memory.StateRepr L b frame F target base m) (tail : List Evm.Word) :
    Evm.Memory.compileVal b F (expression (C := C) ta td) = some (selected (C := C) b F ta td) ∧
    (Source.evalE G Fsrc (fuel + 3) (.binary .mod (.local sa) (.local sd))).run source =
      (.ok (.val (.int (x.tmod y) (remainder_range x y hy nonzero))), source) ∧
    ∃ w : Evm.Word, Evm.ReprV .int (lower (x.tmod y) (remainder_range x y hy nonzero)) w ∧
      Evm.run (selected (C := C) b F ta td).code {m with stack := tail} =
        .ok ({m with stack := tail}.push w) 0 :=
  ⟨public_selection b F ta td,
    source_locals_nonzero G Fsrc fuel source sa sd x y hx hy readA readD nonzero,
    selected_success target ta td x y hx hy nonzero targetA targetD b L frame F base m input tail⟩

end Solidity.Backend.PrimitivePackets.SignedMod
