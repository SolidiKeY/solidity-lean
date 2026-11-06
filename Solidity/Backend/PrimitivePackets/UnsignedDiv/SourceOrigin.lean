import Solidity.Backend.PrimitivePackets.UnsignedDiv.Data
import Solidity.Source.Eval

/-! Actual independent Source-local evaluation. Both pipeline orders read the
same operands; the complete local tail and source state are retained, including
on error. A horizon is an observation bound, not EVM gas. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedDiv

variable {E : Source.Env} {Γ : Source.RCtx}

private theorem lift_result (l : Source.Locals E.layout Γ) (s : Source.St E)
    (r : Source.R (Source.Val E.layout (.int Source.IntTy.u256))) :
    ((do let v ← Source.EM.lift r; pure (Source.RVal.val v)) :
      Source.EM E Γ (Source.RVal E.layout (.int Source.IntTy.u256))).run (l, s) =
      (r.map Source.RVal.val, (l, s)) := by
  cases r <;> rfl

theorem source_div_origin (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (a d : Uint) (tail : Source.Locals E.layout Γ) (s : Source.St E) :
    (Source.evalE G F (n + 3) (sourceDiv E Γ)).run (sourceLocals a d tail, s) =
      ((Source.intBin (D := E.layout) Source.IntTy.u256 F.checked .div a.val d.val).map
        Source.RVal.val, (sourceLocals a d tail, s)) := by
  cases hp : G.pipeline <;>
    simp only [sourceDiv, Source.evalE, Source.evalPair, hp]
  all_goals
    change ((Source.EM.lift
      (Source.intBin (D := E.layout) Source.IntTy.u256 F.checked .div a.val d.val) >>= fun v =>
      pure (Source.RVal.val v)) : Source.EM E (sourceContext Γ)
        (Source.RVal E.layout (.int Source.IntTy.u256))).run (sourceLocals a d tail, s) = _
    exact lift_result _ _ _

theorem source_mod_origin (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (a d : Uint) (tail : Source.Locals E.layout Γ) (s : Source.St E) :
    (Source.evalE G F (n + 3) (sourceMod E Γ)).run (sourceLocals a d tail, s) =
      ((Source.intBin (D := E.layout) Source.IntTy.u256 F.checked .mod a.val d.val).map
        Source.RVal.val, (sourceLocals a d tail, s)) := by
  cases hp : G.pipeline <;>
    simp only [sourceMod, Source.evalE, Source.evalPair, hp]
  all_goals
    change ((Source.EM.lift
      (Source.intBin (D := E.layout) Source.IntTy.u256 F.checked .mod a.val d.val) >>= fun v =>
      pure (Source.RVal.val v)) : Source.EM E (sourceContext Γ)
        (Source.RVal E.layout (.int Source.IntTy.u256))).run (sourceLocals a d tail, s) = _
    exact lift_result _ _ _

end Solidity.Backend.PrimitivePackets.UnsignedDiv
