import Solidity.Backend.PrimitivePackets.Comparisons.Selected

/-! Actual Source to public-selected physical machine agreement. Initial local
contents and the existing StateRepr are the representation assumptions. No
execution, selected certificate or poststate is supplied by the caller. -/
namespace Solidity.Backend.PrimitivePackets.Comparisons
open Lowering.V07 Evm Evm.Memory

theorem selected_run {C : Contract} {Γ : Ctx} (state : State C Γ)
    (o : Order) (signed : Bool) (a b : Idx Γ (.val (prim signed)))
    (x y : Int) (hx : (ty signed).lo≤x ∧ x≤(ty signed).hi)
    (hy : (ty signed).lo≤y ∧ y≤(ty signed).hi)
    (left : TEnv.get a state.env = integerValue (ty signed) x hx)
    (right : TEnv.get b state.env = integerValue (ty signed) y hy)
    {L base frame : Nat} {F : Frag Γ} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L base frame F state addresses machine) :
    run (selected (C:=C) base F o signed a b).code machine =
      .ok (machine.push (.val (bword (result o x y)))) 0 := by
  have simulation := (selected (C:=C) base F o signed a b).cert.correct represented
  rw [intrinsic_run state o signed a b x y hx hy left right] at simulation
  rcases simulation with ⟨v,w,same,word,executed⟩ | ⟨impossible,_⟩
  · cases same
    exact word ▸ executed
  · cases impossible

theorem agreement {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (source : Source.EMState E srcΓ)
    (state : State C Γ) (o : Order) (signed : Bool)
    (sa sb : Source.Idx srcΓ (.int (ty signed))) (a b : Idx Γ (.val (prim signed)))
    (x y : Int) (hx : (ty signed).lo≤x ∧ x≤(ty signed).hi)
    (hy : (ty signed).lo≤y ∧ y≤(ty signed).hi)
    (sourceLeft : source.1.get sa = .int x hx) (sourceRight : source.1.get sb = .int y hy)
    (targetLeft : TEnv.get a state.env = integerValue (ty signed) x hx)
    (targetRight : TEnv.get b state.env = integerValue (ty signed) y hy)
    {L base frame : Nat} {fragment : Frag Γ} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L base frame fragment state addresses machine) :
    (Source.evalE G F (n+3) (expression o signed sa sb)).run source =
      (.ok (.val (.bool (result o x y))),source) ∧
    compileVal base fragment (value (C:=C) o signed a b) = some (selected (C:=C) base fragment o signed a b) ∧
    run (selected (C:=C) base fragment o signed a b).code machine =
      .ok (machine.push (.val (bword (result o x y)))) 0 :=
  ⟨source_run G F n source o signed sa sb x y hx hy sourceLeft sourceRight,
    public_selection base fragment o signed a b,
    selected_run state o signed a b x y hx hy targetLeft targetRight represented⟩

#print axioms selected_run
#print axioms agreement
end Solidity.Backend.PrimitivePackets.Comparisons
