import Solidity.Backend.Scalar.Casts
import Solidity.Backend.Scalar.Comparisons
import Solidity.Semantics.Run

/-!
# Closed intrinsic Val certificates

The existing intrinsic `Val` and its original evaluation remain unchanged.
A certificate is uniform over every typed state, so generated code cannot
specialize a local/environment/storage read by evaluating the source first.
This initial compositional interface covers literals and certified operators;
read/location/heap/call integration and generic short-circuit control stay open.
-/
namespace Solidity.Backend.Scalar

variable {C : Contract} {Γ : Ctx} {p : PrimTy}

/-- A source expression and real instruction slice agree uniformly over states. -/
structure ClosedCertificate (e : Val C Γ p) where
  value : p.Denote
  code : Program
  source : ∀ σ : State C Γ, e.evalT σ = .ok value
  target : ∀ tail : Stack, run code tail = some (encodeValue p value :: tail)

/-- Typed numeric literal selection carries the original intrinsic range proof. -/
def numericLiteral (p : PrimTy) (n : Int) (h : p.inRange n = true) :
    ClosedCertificate (C := C) (Γ := Γ) (.simple (.lit n h)) where
  value := PrimTy.ofLit p n h
  code := literal p (PrimTy.ofLit p n h)
  source := fun _ => rfl
  target := literal_correct p (PrimTy.ofLit p n h)

def boolLiteral (b : Bool) :
    ClosedCertificate (C := C) (Γ := Γ) (.simple (.bool b)) where
  value := b
  code := literal .bool b
  source := fun _ => rfl
  target := literal_correct .bool b

/-- Successful intrinsic unary operations compose with a closed operand.
The result witness is a source operation equation, not an assumed target fact. -/
def ClosedCertificate.unary {e : Val C Γ p} (a : ClosedCertificate e)
    {op : UnOp} {h : op.accepts p = true} (c : UnaryCertificate op p h)
    (v : (op.ret p).Denote) (hv : op.evalT h a.value = some v) :
    ClosedCertificate (.unop op h rfl e) where
  value := v
  code := a.code ++ c.code
  source := by
    intro σ
    simp only [Val.evalT, a.source σ, bind, Except.bind, hv, TRes.ofOpt]
  target := by
    intro tail
    apply run_comp (a.target tail)
    rw [c.correct, hv]
    rfl

/-- Binary composition preserves operand order: the right value is pushed first.
This interface requires the exact existing source short-circuit test to decline;
separate control compilation must handle the short-circuiting branch. -/
def ClosedCertificate.binary {e f : Val C Γ p}
    (a : ClosedCertificate e) (b : ClosedCertificate f)
    {op : BinOp} {h : op.accepts p = true} (c : BinaryCertificate op p h)
    (v : (op.ret p).Denote) (hv : op.evalT h a.value b.value = some v)
    (hs : op.shortT a.value = none) : ClosedCertificate (.binop op h rfl e f) where
  value := v
  code := b.code ++ a.code ++ c.code
  source := by
    intro σ
    simp only [Val.evalT, a.source σ, bind, Except.bind, hs, b.source σ, hv, TRes.ofOpt]
  target := by
    intro tail
    apply run_comp (p := b.code ++ a.code) (q := c.code)
    · exact run_comp (b.target tail) (a.target (encodeValue p b.value :: tail))
    · rw [c.correct, hv]
      rfl

/-- The exported certificate also pins exact bytes through Backend.encode. -/
def ClosedCertificate.bytes {e : Val C Γ p} (c : ClosedCertificate e) : List UInt8 :=
  Backend.encode c.code

def negatedTrue : ClosedCertificate (C := C) (Γ := Γ)
    (.unop .not rfl rfl (.simple (.bool true))) :=
  (boolLiteral true).unary booleanNot false rfl

/-- A source/target combination regression, uniform over every typed state. -/
theorem negatedTrue_source (σ : State C Γ) :
    (Val.unop .not rfl rfl (.simple (.bool true))).evalT σ = .ok false :=
  (negatedTrue (C := C) (Γ := Γ)).source σ

theorem negatedTrue_target (tail : Stack) :
    run (negatedTrue (C := C) (Γ := Γ)).code tail = some (encodeValue .bool false :: tail) :=
  (negatedTrue (C := C) (Γ := Γ)).target tail

/-- The literal PUSH32 and ISZERO bytes are observable through the real encoder. -/
theorem negatedTrue_bytes : (negatedTrue (C := C) (Γ := Γ)).bytes =
    0x7f :: (List.replicate 31 0 ++ [1, 0x15]) := by
  change Backend.encode (literal .bool true ++ booleanNot.code) = _
  decide +kernel

/-- info: 'Solidity.Backend.Scalar.ClosedCertificate.unary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClosedCertificate.unary
/-- info: 'Solidity.Backend.Scalar.ClosedCertificate.binary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClosedCertificate.binary
/-- info: 'Solidity.Backend.Scalar.negatedTrue_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms negatedTrue_source
/-- info: 'Solidity.Backend.Scalar.negatedTrue_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms negatedTrue_target

end Solidity.Backend.Scalar
