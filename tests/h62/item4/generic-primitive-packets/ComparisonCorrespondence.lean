import Solidity.Backend.PrimitivePackets.Comparisons.Controls
import Solidity.Backend.PrimitivePackets.SignedMod.Controls

/-! Regression: signed/unsigned relational comparisons must use the matching
ordering and Boolean result while preserving populated caller memory and every
saved stack. All four orders and both signedness cases have constructed physical
inputs and actual public selection/Source execution. No arbitrary heap/world,
session/gas or fetched-EVM adequacy or frozen-original fidelity is inferred. -/
namespace H62.PrimitivePackets.ComparisonCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory Solidity.Lowering.V07
open Solidity.Backend.PrimitivePackets.Comparisons
open Solidity.Backend.PrimitivePackets.Comparisons.Controls (word word_repr)

abbrev Γ (signed : Bool) : Ctx := .val (prim signed) :: .val (prim signed) :: CompileExamples.Γ
def frag (signed : Bool) : Frag (Γ signed) :=
  ((Frag.init CompileExamples.Γ).push (.val (prim signed)) .ok).push (.val (prim signed)) .ok

def target (signed : Bool) (x y : Int) (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi)
    (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi) : State CompileExamples.C (Γ signed) :=
  (CompileExamples.σ.push (t := .val (prim signed)) (integerValue (ty signed) y hy)).push
    (t := .val (prim signed)) (integerValue (ty signed) x hx)
def machine (signed : Bool) (x y : Int) (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi)
    (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi) : Machine :=
  writeMachine (writeMachine CompileExamples.machine 4 (word signed y hy)) 5 (word signed x hx)

theorem initial (signed : Bool) (x y : Int) (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi)
    (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi) :
    StateRepr 1 0 8 (frag signed) (target signed x y hx hy) CompileExamples.base
      (machine signed x y hx hy) :=
  (Solidity.Backend.PrimitivePackets.SignedMod.Controls.initial8.consVal
    (integerValue (ty signed) y hy) (word signed y hy) (word_repr signed y hy) (by change 5 ≤ 8; decide)).consVal
    (integerValue (ty signed) x hx) (word signed x hx) (word_repr signed x hx) (by change 6 ≤ 8; decide)

def source {E : Source.Env} {Δ : Source.RCtx} (signed : Bool) (x y : Int)
    (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi) (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    Source.EMState E (.int (ty signed) :: .int (ty signed) :: Δ) :=
  (.cons (.int x hx) (.cons (.int y hy) tail),state)

def code (o : Order) (signed : Bool) :=
  (selected (C := CompileExamples.C) 0 (frag signed) o signed .here (.there .here)).code

theorem joint {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat) (o : Order) (signed : Bool)
    (x y : Int) (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi) (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) (saved : List Word) :
    (Source.evalE G fr (fuel+3) (expression o signed .here (.there .here))).run
      (source signed x y hx hy tail state) =
      (.ok (.val (.bool (result o x y))),source signed x y hx hy tail state) ∧
    compileVal 0 (frag signed) (value (C := CompileExamples.C) o signed .here (.there .here)) =
      some (selected 0 (frag signed) o signed .here (.there .here)) ∧
    run (code o signed) {machine signed x y hx hy with stack := saved} =
      .ok ({machine signed x y hx hy with stack := saved}.push (.val (bword (result o x y)))) 0 ∧
    StateRepr 1 0 8 (frag signed) (target signed x y hx hy) CompileExamples.base
      ({machine signed x y hx hy with stack := saved}.push (.val (bword (result o x y)))) := by
  have h := agreement G fr fuel (source signed x y hx hy tail state) (target signed x y hx hy)
    o signed .here (.there .here) .here (.there .here) x y hx hy rfl rfl rfl rfl
    ((initial signed x y hx hy).stack saved)
  exact ⟨h.1,h.2.1,h.2.2,((initial signed x y hx hy).stack saved).push _⟩

theorem reject_all_refuted (o : Order) (signed : Bool) (x y : Int)
    (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi) (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi)
    (saved : List Word) :
    run (code o signed) {machine signed x y hx hy with stack := saved} ≠ .revert := by
  have h := selected_run (target signed x y hx hy) o signed .here (.there .here)
    x y hx hy rfl rfl ((initial signed x y hx hy).stack saved)
  unfold code
  rw [h]
  intro same
  cases same

theorem low_fuel {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (o : Order) (signed : Bool) (x y : Int)
    (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi) (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.evalE G fr 0 (expression o signed .here (.there .here))).run
      (source signed x y hx hy tail state) =
      (.error .timeout,source signed x y hx hy tail state) := rfl

#print axioms initial
#print axioms joint
#print axioms reject_all_refuted
#print axioms low_fuel
end H62.PrimitivePackets.ComparisonCorrespondence
