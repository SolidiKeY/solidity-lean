import Solidity.Yul.World.EffectfulEmitEntry

/-! Actual source known self-call: registration/balance/depth are explicit.
This is not a precompile, physical, compiler or universal-call certificate. -/
namespace Solidity.Yul.World.EffectfulEmitSelfCall
open Solidity.Source
open Solidity.Roadmap (Bytes Word Address Outcome)
open Solidity.Yul.World.EffectfulEmitSource
open Solidity.Yul.World.EffectfulEmitFunction
open Solidity.Yul.World.EffectfulEmitDispatch

theorem actual {indexed anonymous} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) []) (value : Word)
    (normal : F.static=false) (depth : F.depth<1024)
    (registered : (s.2.ex.world.accounts F.this).code=some 0)
    (funds : value.val ≤ (s.2.ex.world.accounts F.this).balance.val) :
    (Source.callAddr (glob G) F 10 F.this value (input G) false).run s=
      (.ok (.revert (EffectfulEmitRevert.data G)),s) := by
  have selected : (Source.instanceAt (glob G) F.this).run s=(.ok (some "Finite"),s) := by
    simp only [Source.instanceAt,Source.Hoare.run_bind,ReturningCall.run_st,registered,ReturningCall.run_pure]
    rfl
  have notDeep : ¬F.depth≥1024 := Nat.not_le.mpr depth
  simp only [Source.callAddr,notDeep,if_false,normal,Bool.false_and,Bool.false_eq_true,
    Source.Hoare.run_bind,ReturningCall.run_pure,selected,ReturningCall.run_mark,
    ReturningCall.run_st,if_true,funds,decide_true,Bool.not_true,Bool.false_or]
  rw [EffectfulEmitEntry.actual]

end Solidity.Yul.World.EffectfulEmitSelfCall
