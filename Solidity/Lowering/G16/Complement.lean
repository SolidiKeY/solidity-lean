import Solidity.Lowering.V07.UnsignedComplement
import Solidity.Lowering.V07.SignedComplement

/-! Integer complement at all widths and signs, through the published V07 programs. This is a local-expression leaf, not a frontend selection theorem. -/
namespace Solidity.Lowering.G16.Complement
open Solidity.Lowering.V07

def value {C : Contract} {Γ : Ctx} (t : Source.IntTy) :
    Val C Γ (integerPrim t) → Val C Γ (integerPrim t) :=
  match t with
  | ⟨false,bits,_⟩ => UnsignedComplement.complementValue bits
  | ⟨true,bits,_⟩ => SignedComplement.complementValue bits

/-- One integer-complement statement includes all valid signs and widths in both checked and unchecked frames. Initial aligned locals supply the inputs. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (t : Source.IntTy)
    (si : ι → Source.Idx srcΓ (.int t)) (ti : ι → Idx Γ (.val (integerPrim t)))
    (family : IntegerLocalFamily t si ti source.1 target.env)
    (k : ι) (x : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (read : source.1.get (si k) = .int x hx) :
    (Source.evalE G F (fuel+2) (.unary .bitNot (.local (si k)))).run source =
      (.ok (.val (Source.intWrap t (-x-1))),source) ∧
    (value t (.simple (.local (ti k)))).evalT target =
      .ok (integerValue t (t.wrap (-x-1)) (t.wrap_mem (-x-1))) ∧
    IntValueRel t (Source.intWrap t (-x-1) : Source.Val E.layout (.int t))
      (integerValue t (t.wrap (-x-1)) (t.wrap_mem (-x-1))) := by
  obtain ⟨sign,bits,valid⟩ := t
  cases sign with
  | false => exact UnsignedComplement.local_transport bits valid G F fuel source target si ti family k x hx read
  | true => exact SignedComplement.local_transport bits valid G F fuel source target si ti family k x hx read

end Solidity.Lowering.G16.Complement

/-- info: 'Solidity.Lowering.G16.Complement.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.Complement.transport

namespace Solidity.Lowering.G16.UnsignedBitwise
open Solidity.Lowering.V07

inductive Op where
  | and | or | xor
  deriving DecidableEq

def sourceOp : Op → Source.BinOp
  | .and => .bitAnd | .or => .bitOr | .xor => .bitXor

def result : Op → Nat → Nat → Nat
  | .and => (· &&& ·) | .or => (· ||| ·) | .xor => (· ^^^ ·)

def value {C : Contract} {Γ : Ctx} : Op → Val C Γ .uint → Val C Γ .uint → Val C Γ .uint
  | .and, a, b => .binop .band rfl rfl a b
  | .or, a, b => .binop .bor rfl rfl a b
  | .xor, a, b => .binop .bxor rfl rfl a b

private theorem result_lt (op : Op) {bits x y : Nat} (hx : x < 2^bits) (hy : y < 2^bits) :
    result op x y < 2^bits := by
  cases op with
  | and => exact Nat.and_lt_two_pow x hy
  | or => exact Nat.or_lt_two_pow hx hy
  | xor => exact Nat.xor_lt_two_pow hx hy

private theorem range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (n : Nat) (h : n < 2^bits) :
    (UnsignedNarrowing.ty bits valid).lo ≤ (n : Int) ∧
      (n : Int) ≤ (UnsignedNarrowing.ty bits valid).hi := by
  change 0 ≤ (n : Int) ∧ (n : Int) ≤ ((2^bits-1 : Nat) : Int)
  have positive : 0 < 2^bits := Nat.two_pow_pos bits
  omega

private theorem source_result {D : Source.Layout} (checked : Bool) (op : Op)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x y : Nat) (hx : x < 2^bits) (hy : y < 2^bits) :
    Source.binVal checked (sourceOp op)
      (.int (x : Int) (range bits valid x hx) : Source.Val D (.int (UnsignedNarrowing.ty bits valid)))
      (.int (y : Int) (range bits valid y hy)) =
      .ok (.int (result op x y : Int) (range bits valid _ (result_lt op hx hy))) := by
  have wrapped := UnsignedNarrowing.wrap_of_range bits valid (result op x y : Int)
    (range bits valid _ (result_lt op hx hy))
  cases op <;> change Except.ok (Source.intWrap _ _) = _ <;>
    simp only [Source.intWrap,result,Source.Int.bitAnd,Source.Int.bitOr,Source.Int.bitXor,Int.ofNat_eq_coe] at wrapped ⊢ <;> simp only [wrapped]

private def wordResult : Op → PrimTy.uint.Denote → PrimTy.uint.Denote → Option PrimTy.uint.Denote
  | .and => BinOp.evalT .band rfl
  | .or => BinOp.evalT .bor rfl
  | .xor => BinOp.evalT .bxor rfl

private theorem value_step {C : Contract} {Γ : Ctx} (target : State C Γ)
    (op : Op) (a b : Val C Γ .uint) (x y : PrimTy.uint.Denote)
    (left : a.evalT target = .ok x) (right : b.evalT target = .ok y) :
    (value op a b).evalT target = TRes.ofOpt (wordResult op x y) := by
  cases op <;> rw [value,Val.evalT,left,right] <;> rfl

private def nativeOp : Op → BinOp
  | .and => .band | .or => .bor | .xor => .bxor

private theorem arithmetic_result (op : Op) (x y : Nat) :
    BinOp.arithInt (nativeOp op) (x : Int) (y : Int) = some (result op x y : Int) := by
  cases op <;> exact congrArg some (Semantics.uintBitwise_natCast _ x y)

private theorem ofInt_run (z : Int) (h : PrimTy.uint.inRange z = true) :
    PrimTy.uint.ofInt? z = some ⟨z,h⟩ := by
  simp only [PrimTy.ofInt?,dif_pos h]

private theorem word_step (op : Op) (x y : PrimTy.uint.Denote) :
    wordResult op x y = (BinOp.arithInt (nativeOp op) x.val y.val).bind PrimTy.uint.ofInt? := by
  cases op <;> rfl

private theorem word_of_arithmetic (op : Op) (x y : PrimTy.uint.Denote)
    (z : Int) (h : PrimTy.uint.inRange z = true)
    (computed : BinOp.arithInt (nativeOp op) x.val y.val = some z) :
    wordResult op x y = some ⟨z,h⟩ := by
  rw [word_step,computed]
  simpa only [Option.bind_some] using ofInt_run z h

private theorem word_run (op : Op) (x y : Nat)
    (hx : PrimTy.uint.inRange (x : Int) = true) (hy : PrimTy.uint.inRange (y : Int) = true)
    (hr : PrimTy.uint.inRange (result op x y : Int) = true) :
    wordResult op ⟨(x : Int),hx⟩ ⟨(y : Int),hy⟩ = some ⟨(result op x y : Int),hr⟩ := by
  exact word_of_arithmetic op ⟨(x : Int),hx⟩ ⟨(y : Int),hy⟩
    (result op x y : Int) hr (arithmetic_result op x y)

private theorem value_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (op : Op) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (a b : Val C Γ .uint) (x y : Nat) (hx : x < 2^bits) (hy : y < 2^bits)
    (left : a.evalT target = .ok (integerValue (UnsignedNarrowing.ty bits valid) (x : Int) (range bits valid x hx)))
    (right : b.evalT target = .ok (integerValue (UnsignedNarrowing.ty bits valid) (y : Int) (range bits valid y hy))) :
    (value op a b).evalT target = .ok
      (integerValue (UnsignedNarrowing.ty bits valid) (result op x y : Int)
        (range bits valid _ (result_lt op hx hy))) := by
  rw [value_step target op a b _ _ left right]
  have run := word_run op x y (integer_range (UnsignedNarrowing.ty bits valid) (x : Int) (range bits valid x hx))
    (integer_range (UnsignedNarrowing.ty bits valid) (y : Int) (range bits valid y hy))
    (integer_range (UnsignedNarrowing.ty bits valid) (result op x y : Int) (range bits valid _ (result_lt op hx hy)))
  change TRes.ofOpt (wordResult op ⟨(x : Int),_⟩ ⟨(y : Int),_⟩) = _
  rw [run]
  rfl

/-- All three unsigned bitwise operators at every valid width, in either frame and pipeline. Only pure locals are covered; signed/bytes operands, effects and frontend association remain open. -/
theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (op : Op)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (a b : Source.Idx srcΓ (.int (UnsignedNarrowing.ty bits valid)))
    (c d : Idx Γ (.val .uint)) (x y : Nat) (hx : x < 2^bits) (hy : y < 2^bits)
    (readA : source.1.get a = .int (x : Int) (range bits valid x hx))
    (readB : source.1.get b = .int (y : Int) (range bits valid y hy))
    (nativeA : TEnv.get c target.env = integerValue (UnsignedNarrowing.ty bits valid) (x : Int) (range bits valid x hx))
    (nativeB : TEnv.get d target.env = integerValue (UnsignedNarrowing.ty bits valid) (y : Int) (range bits valid y hy)) :
    (Source.evalE G F (fuel+3) (.binary (sourceOp op) (.local a) (.local b))).run source =
      (.ok (.val (.int (result op x y : Int) (range bits valid _ (result_lt op hx hy)))),source) ∧
    (value op (.simple (.local c)) (.simple (.local d))).evalT target =
      .ok (integerValue (UnsignedNarrowing.ty bits valid) (result op x y : Int)
        (range bits valid _ (result_lt op hx hy))) := by
  refine ⟨?_,value_run target op bits valid _ _ x y hx hy
    (congrArg Except.ok nativeA) (congrArg Except.ok nativeB)⟩
  have pair := source_local_pair G F fuel source (UnsignedNarrowing.ty bits valid)
    a b (x : Int) (y : Int) (range bits valid x hx) (range bits valid y hy) readA readB
  have computed := source_result (D := E.layout) F.checked op bits valid x y hx hy
  have notLogical : (decide (sourceOp op = .and) || decide (sourceOp op = .or)) = false := by
    cases op <;> rfl
  rw [Source.evalE]
  simp only [notLogical,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,pair]
  change (do let v ← Source.EM.lift (Source.binVal F.checked (sourceOp op)
                 (.int (x : Int) (range bits valid x hx)) (.int (y : Int) (range bits valid y hy)))
             pure (Source.RVal.val v)).run source = _
  rw [computed]
  rfl

end Solidity.Lowering.G16.UnsignedBitwise

/-- info: 'Solidity.Lowering.G16.UnsignedBitwise.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.UnsignedBitwise.transport

namespace Solidity.Lowering.G16.UnsignedBitwise
open Solidity.Lowering.V07

def captureRight (p : Roadmap.Pipeline) (x y : Nat) : Nat := if p = .legacy then y else x

private theorem captureRight_lt (p : Roadmap.Pipeline) {bits x y : Nat}
    (hx : x < 2^bits) (hy : y < 2^bits) : captureRight p x y < 2^bits := by
  cases p
  · exact hy
  · exact hx

def assignmentOperand {C : Contract} {Γ : Ctx} (op : Op) (p : Roadmap.Pipeline)
    (i a : Idx Γ (.val .uint)) : DeferredSource.Operand C Γ (.prim .uint) :=
  ⟨.val .uint :: .val .uint :: Γ,assignReadPrefix p i a,
    .val (value op (.simple (.local .here)) (.simple (.local (.there .here))))⟩

private theorem assignment_run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (op : Op) (p : Roadmap.Pipeline) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (i a : Idx Γ (.val .uint))
    (x y : Nat) (hx : x < 2^bits) (hy : y < 2^bits)
    (readA : TEnv.get a target.env = integerValue (UnsignedNarrowing.ty bits valid) (x : Int) (range bits valid x hx))
    (readI : TEnv.get i target.env = integerValue (UnsignedNarrowing.ty bits valid) (y : Int) (range bits valid y hy)) :
    (assignmentOperand op p i a).run target =
      .ok (⟨target.setLocal i (integerValue (UnsignedNarrowing.ty bits valid) (x : Int) (range bits valid x hx)),List.prefix_refl _⟩,
        .prim (integerValue (UnsignedNarrowing.ty bits valid) (result op x (captureRight p x y) : Int)
          (range bits valid _ (result_lt op hx (captureRight_lt p hx hy))))) := by
  let t := UnsignedNarrowing.ty bits valid
  let assigned := integerValue t (x : Int) (range bits valid x hx)
  let selected := integerValue t (captureRight p x y : Int) (range bits valid _ (captureRight_lt p hx hy))
  let reached : State C (.val .uint :: .val .uint :: Γ) := ((target.setLocal i assigned).push selected).push assigned
  have chosen : (if p = .legacy then integerValue t (y : Int) (range bits valid y hy) else assigned) = selected := by
    cases p <;> rfl
  have capturedRun := assign_read_prefix_run p target i a assigned
    (integerValue t (y : Int) (range bits valid y hy)) readA readI
  rw [chosen] at capturedRun
  have evaluated := value_run reached op bits valid (.simple (.local .here))
    (.simple (.local (.there .here))) x (captureRight p x y) hx (captureRight_lt p hx hy) rfl rfl
  cases p <;> unfold assignmentOperand DeferredSource.Operand.run <;>
    rw [capturedRun] <;>
    change (do
    let v ← (Src.val (value op (.simple (.local .here)) (.simple (.local (.there .here)))) :
      Src C (.val .uint :: .val .uint :: Γ) (.prim .uint)).valueT reached
    pure ((⟨target.setLocal i assigned,List.prefix_refl _⟩ : Out C target.H Γ),v)) = _ <;>
    simp only [Src.valueT,evaluated] <;> rfl

private theorem source_from_pair {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source mid : Source.EMState E srcΓ)
    (op : Op) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (a b : Source.RExpr E srcΓ (.int (UnsignedNarrowing.ty bits valid)))
    (x y : Nat) (hx : x < 2^bits) (hy : y < 2^bits)
    (pair : (Source.evalPair G F fuel a b).run source =
      (.ok (.val (.int (x : Int) (range bits valid x hx)),.val (.int (y : Int) (range bits valid y hy))),mid)) :
    (Source.evalE G F (fuel+1) (.binary (sourceOp op) a b)).run source =
      (.ok (.val (.int (result op x y : Int) (range bits valid _ (result_lt op hx hy)))),mid) := by
  have notLogical : (decide (sourceOp op = .and) || decide (sourceOp op = .or)) = false := by
    cases op <;> rfl
  have computed := source_result (D := E.layout) F.checked op bits valid x y hx hy
  rw [Source.evalE]
  simp only [notLogical,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,pair]
  change (do let v ← Source.EM.lift (Source.binVal F.checked (sourceOp op)
                (.int (x : Int) (range bits valid x hx)) (.int (y : Int) (range bits valid y hy)))
             pure (Source.RVal.val v)).run mid = _
  rw [computed]
  rfl

/-- All unsigned bitwise assignment/read captures derive pipeline order and named writes; arbitrary effects and frontend association remain open. -/
theorem assignment_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (op : Op)
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (i a : Source.Idx srcΓ (.int (UnsignedNarrowing.ty bits valid)))
    (c d : Idx Γ (.val .uint)) (x y : Nat) (hx : x < 2^bits) (hy : y < 2^bits)
    (readA : source.1.get a = .int (x : Int) (range bits valid x hx))
    (readI : source.1.get i = .int (y : Int) (range bits valid y hy))
    (nativeA : TEnv.get d target.env = integerValue (UnsignedNarrowing.ty bits valid) (x : Int) (range bits valid x hx))
    (nativeI : TEnv.get c target.env = integerValue (UnsignedNarrowing.ty bits valid) (y : Int) (range bits valid y hy)) :
    (Source.evalE G F (fuel+4) (.binary (sourceOp op) (.assign (.local i) (.local a)) (.local i))).run source =
      (.ok (.val (.int (result op x (captureRight G.pipeline x y) : Int)
          (range bits valid _ (result_lt op hx (captureRight_lt G.pipeline hx hy))))),
        (source.1.set i (.int (x : Int) (range bits valid x hx)),source.2)) ∧
    (assignmentOperand op G.pipeline c d).run target =
      .ok (⟨target.setLocal c (integerValue (UnsignedNarrowing.ty bits valid) (x : Int) (range bits valid x hx)),List.prefix_refl _⟩,
        .prim (integerValue (UnsignedNarrowing.ty bits valid) (result op x (captureRight G.pipeline x y) : Int)
          (range bits valid _ (result_lt op hx (captureRight_lt G.pipeline hx hy))))) := by
  refine ⟨?_,assignment_run target op G.pipeline bits valid c d x y hx hy nativeA nativeI⟩
  have pair := source_assign_read_pair G F fuel source i a
    (.int (x : Int) (range bits valid x hx)) (.int (y : Int) (range bits valid y hy)) readA readI
  by_cases order : G.pipeline = .legacy
  · simp only [order,if_true,captureRight] at pair ⊢
    exact source_from_pair G F (fuel+3) source _ op bits valid _ _ x y hx hy pair
  · simp only [order,if_false,captureRight] at pair ⊢
    exact source_from_pair G F (fuel+3) source _ op bits valid _ _ x x hx hx pair

/-- info: 'Solidity.Lowering.G16.UnsignedBitwise.assignment_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms assignment_transport
end UnsignedBitwise
