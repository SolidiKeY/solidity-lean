import Solidity.Backend.Scalar.ArithmeticWidths
import Solidity.Backend.Scalar.Select

/-! Width cleanup composes with every admitted pure intrinsic constructor,
including shifts, bitwise operations and wrapping powers. The source operand
and result types remain the original intrinsic dependent types. -/
namespace Solidity.Backend.Scalar

theorem BinaryCertificate.unsignedWidth_correct {op : BinOp} {p : PrimTy}
    {h : op.accepts p = true} (c : BinaryCertificate op p h) (w : Fin 32)
    (a b : p.Denote) (tail : Stack) :
    run (c.code ++ unsignedCode w) (encodeValue p a::encodeValue p b::tail) =
      (op.evalT h a b).map (fun v => unsignedClean w (encodeValue (op.ret p) v)::tail) := by
  rw [run_append, c.correct]
  cases hv : op.evalT h a b with
  | none => rfl
  | some v =>
    simp only [Option.map_some, Option.bind_some]
    exact unsigned_correct w (encodeValue (op.ret p) v) tail

theorem BinaryCertificate.signedWidth_correct {op : BinOp} {p : PrimTy}
    {h : op.accepts p = true} (c : BinaryCertificate op p h) (w : Fin 32)
    (a b : p.Denote) (tail : Stack) :
    run (c.code ++ signedCode w) (encodeValue p a::encodeValue p b::tail) =
      (op.evalT h a b).map (fun v => signedClean w (encodeValue (op.ret p) v)::tail) := by
  rw [run_append, c.correct]
  cases hv : op.evalT h a b with
  | none => rfl
  | some v =>
    simp only [Option.map_some, Option.bind_some]
    exact signed_correct w (encodeValue (op.ret p) v) tail

theorem UnaryCertificate.unsignedWidth_correct {op : UnOp} {p : PrimTy}
    {h : op.accepts p = true} (c : UnaryCertificate op p h) (w : Fin 32)
    (a : p.Denote) (tail : Stack) :
    run (c.code ++ unsignedCode w) (encodeValue p a::tail) =
      (op.evalT h a).map (fun v => unsignedClean w (encodeValue (op.ret p) v)::tail) := by
  rw [run_append, c.correct]
  cases hv : op.evalT h a with
  | none => rfl
  | some v =>
    simp only [Option.map_some, Option.bind_some]
    exact unsigned_correct w (encodeValue (op.ret p) v) tail

theorem UnaryCertificate.signedWidth_correct {op : UnOp} {p : PrimTy}
    {h : op.accepts p = true} (c : UnaryCertificate op p h) (w : Fin 32)
    (a : p.Denote) (tail : Stack) :
    run (c.code ++ signedCode w) (encodeValue p a::tail) =
      (op.evalT h a).map (fun v => signedClean w (encodeValue (op.ret p) v)::tail) := by
  rw [run_append, c.correct]
  cases hv : op.evalT h a with
  | none => rfl
  | some v =>
    simp only [Option.map_some, Option.bind_some]
    exact signed_correct w (encodeValue (op.ret p) v) tail

#print axioms BinaryCertificate.unsignedWidth_correct
#print axioms BinaryCertificate.signedWidth_correct
#print axioms UnaryCertificate.unsignedWidth_correct
#print axioms UnaryCertificate.signedWidth_correct
end Solidity.Backend.Scalar
