import Solidity.Lowering.V07.Scalar
import Solidity.Source.Eval
import Solidity.Semantics.Run

/-! Constructor argument-frame preparation for two integer local arguments.
Source parameter order and intrinsic innermost-first frame order are deliberately
different. This consumer does not assert whole-constructor, profile, physical
frame, world or fetched-byte preservation. Identity-conversion admission is
explicit; all executions use the existing typed evaluators. -/
namespace Solidity.Backend.Executable.ConstructorLocalArguments
open Solidity Lowering.V07
variable {E : Source.Env} {C : Contract} {Γ : Ctx} {tail : Source.RCtx}

def sourceArgs (a b : Source.IntTy)
    (ha : (Source.STy.int a).implicit E.isBase E.mapFree (.int a) = true)
    (hb : (Source.STy.int b).implicit E.isBase E.mapFree (.int b) = true) :
    Source.RConvArgs E (.int a :: .int b :: tail) [.int a,.int b] :=
  .cons (.local .here) ha (.cons (.local (.there .here)) hb .nil)

def targetArgs (a b : Source.IntTy)
    (left : Idx Γ (.val (integerPrim a))) (right : Idx Γ (.val (integerPrim b))) :
    Args C Γ [.val (integerPrim b),.val (integerPrim a)] :=
  .snoc (.snoc .nil (integerPrim a) (.user "arg0") (.simple (.local left)))
    (integerPrim b) (.user "arg1") (.simple (.local right))

/-- Actual converted Source arguments preserve every caller observation. The
remaining caller locals may contain references and populated memory objects. -/
theorem source_actual (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (a b : Source.IntTy)
    (ha : (Source.STy.int a).implicit E.isBase E.mapFree (.int a) = true)
    (hb : (Source.STy.int b).implicit E.isBase E.mapFree (.int b) = true)
    (x y : Int) (hx : a.lo ≤ x ∧ x ≤ a.hi) (hy : b.lo ≤ y ∧ y ≤ b.hi)
    (rest : Source.Locals E.layout tail) (s : Source.St E) :
    (Source.evalConvArgs G F (fuel+3) (sourceArgs a b ha hb)).run
      (.cons (.int x hx) (.cons (.int y hy) rest),s) =
      (.ok (.cons (.int x hx) (.cons (.int y hy) .nil)),
        (.cons (.int x hx) (.cons (.int y hy) rest),s)) := by
  simp only [sourceArgs, Source.evalConvArgs, Source.evalE, Source.convRV, dite_true]
  rfl

/-- Existing intrinsic Args evaluates declaration order, yielding a frame with
its last parameter innermost. Only initial local reads are premises. -/
theorem target_actual (a b : Source.IntTy) (s : State C Γ)
    (i : Idx Γ (.val (integerPrim a))) (j : Idx Γ (.val (integerPrim b)))
    (x : (integerPrim a).Denote) (y : (integerPrim b).Denote)
    (hx : TEnv.get i s.env = x) (hy : TEnv.get j s.env = y) :
    (targetArgs a b i j).evalT s = .ok (y,(x,())) := by
  change (do
    let u ← (Except.ok (TEnv.get i s.env))
    let v ← (Except.ok (TEnv.get j s.env))
    pure (v,(u,()))) = _
  rw [hx,hy]
  rfl

end Solidity.Backend.Executable.ConstructorLocalArguments
