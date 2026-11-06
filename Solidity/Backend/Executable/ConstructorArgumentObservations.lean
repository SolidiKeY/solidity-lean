import Solidity.Backend.Executable.ConstructorLocalArguments

/-! Numeric observations of the exact two-argument executions. Full Source
state preservation is supplied separately by source_actual, not replaced by
these projections. No profile, constructor body or physical target claim. -/
namespace Solidity.Backend.Executable.ConstructorArgumentObservations
open Solidity Lowering.V07 ConstructorLocalArguments

def sourceKeys {D : Source.Layout} {a b : Source.IntTy}
    (vs : Source.Vals D [.int a,.int b]) : List (Option Int) :=
  match vs with | .cons x (.cons y .nil) => [x.key,y.key]

def targetKeys {C : Contract} {H : List RefTy} {a b : Source.IntTy}
    (env : TEnv C H [.val (integerPrim b),.val (integerPrim a)]) : List (Option Int) :=
  [PrimTy.num? env.2.1,PrimTy.num? env.1]

/-- Successful numeric projection only: error carriers stay distinct, and the
complete Source post-state is still given by source_actual. -/
theorem successful_numeric_agreement :
∀ {E : Solidity.Source.Env} {C : Solidity.Contract} {Γ : Solidity.Ctx} {tail : Solidity.Source.RCtx}
 (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (fuel : Nat)
 (a b : Solidity.Source.IntTy)
 (ha : (Solidity.Source.STy.int a).implicit E.isBase E.mapFree (.int a) = true)
 (hb : (Solidity.Source.STy.int b).implicit E.isBase E.mapFree (.int b) = true)
 (x y : Int) (hx : a.lo ≤ x ∧ x ≤ a.hi) (hy : b.lo ≤ y ∧ y ≤ b.hi)
 (rest : Solidity.Source.Locals E.layout tail) (s : Solidity.Source.St E)
 (target : Solidity.State C Γ)
 (i : Solidity.Idx Γ (.val (Solidity.Lowering.V07.integerPrim a)))
 (j : Solidity.Idx Γ (.val (Solidity.Lowering.V07.integerPrim b)))
 (hi : Solidity.TEnv.get i target.env = Solidity.Lowering.V07.integerValue a x hx)
 (hj : Solidity.TEnv.get j target.env = Solidity.Lowering.V07.integerValue b y hy),
 (((Solidity.Source.evalConvArgs G F (fuel+3)
  (Solidity.Backend.Executable.ConstructorLocalArguments.sourceArgs a b ha hb)).run
  (.cons (.int x hx) (.cons (.int y hy) rest),s)).1.toOption.map
  Solidity.Backend.Executable.ConstructorArgumentObservations.sourceKeys) =
 (((Solidity.Backend.Executable.ConstructorLocalArguments.targetArgs a b i j).evalT target).toOption.map
  Solidity.Backend.Executable.ConstructorArgumentObservations.targetKeys) := by
  intro E C Γ tail G F fuel a b ha hb x y hx hy rest s target i j hi hj
  rw [ConstructorLocalArguments.source_actual,
    ConstructorLocalArguments.target_actual a b target i j _ _ hi hj]
  change some [some x,some y] = some [PrimTy.num? (integerValue a x hx),PrimTy.num? (integerValue b y hy)]
  rw [integer_observe,integer_observe]
end Solidity.Backend.Executable.ConstructorArgumentObservations
