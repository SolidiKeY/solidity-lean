import Solidity.Backend.PrimitivePackets.SignedSub.Controls

/-! Regression: unchecked signed subtraction wraps rather than refusing signed
overflow, while preserving populated caller memory and every saved stack.
Actual Source locals and physical inputs are constructed; neither execution
nor compiler selection is a premise. This does not assert checked subtraction,
arbitrary heap/world/session/gas or fetched-EVM adequacy. -/
namespace H62.PrimitivePackets.UncheckedSignedSubCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory Solidity.Lowering.V07
open Solidity.Backend.PrimitivePackets.SignedSub
open Solidity.Backend.PrimitivePackets.SignedSub.Controls (target machine represented frag ti)

def source {E : Source.Env} {Δ : Source.RCtx} (x y : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    Source.EMState E (.int ty :: .int ty :: Δ) :=
  (.cons (.int x hx) (.cons (.int y hy) tail),state)

def si {Δ : Source.RCtx} : Bool → Source.Idx (.int ty :: .int ty :: Δ) (.int ty)
  | false => .here
  | true => .there .here

theorem family {E : Source.Env} {Δ : Source.RCtx} (x y : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    IntegerLocalFamily ty si ti (source x y hx hy tail state).1 (target x y hx hy).env := by
  constructor
  · intro k; cases k <;> exact integer_related _ _ _
  · intro k l; cases k <;> cases l <;> rfl

def code := (selected (C := Solidity.Backend.PrimitivePackets.SignedSub.Controls.C)
  1 frag (ti false) (ti true)).code

theorem joint {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (x y : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) (saved : List Word) :
    compileVal 1 frag (value (C := Solidity.Backend.PrimitivePackets.SignedSub.Controls.C)
      (ti false) (ti true)) = some (selected 1 frag (ti false) (ti true)) ∧
    (Source.evalE G {fr with checked := false} (fuel+3)
      (.binary .sub (.local .here) (.local (.there .here)))).run (source x y hx hy tail state) =
      (.ok (.val (Source.intWrap ty (x-y))),source x y hx hy tail state) ∧
    run code {machine x y with stack := saved} =
      .ok ({machine x y with stack := saved}.push (.val (sword (ty.wrap (x-y))))) 0 ∧
    StateRepr 1 1 64 frag (target x y hx hy)
      Solidity.Backend.PrimitivePackets.SignedSub.Controls.Seed.bases
      ({machine x y with stack := saved}.push (.val (sword (ty.wrap (x-y))))) := by
  have h := execution G fr fuel (source x y hx hy tail state) (target x y hx hy)
    si ti (family x y hx hy tail state) false true x y hx hy rfl rfl
    1 1 64 frag Solidity.Backend.PrimitivePackets.SignedSub.Controls.Seed.bases
    (machine x y) (represented x y hx hy)
  exact ⟨selection 1 frag (ti false) (ti true),h.1,h.2 saved⟩

theorem reject_all_refuted (x y : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi) (saved : List Word) :
    run code {machine x y with stack := saved} ≠ .revert := by
  have runs := (joint (Source.SemanticsExamples.G0 .legacy) Source.SemanticsExamples.F0 0
    x y hx hy .nil Source.SemanticsExamples.s0 saved).2.2.1
  rw [runs]
  intro h
  cases h

theorem low_fuel {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (x y : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.evalE G {fr with checked := false} 0
      (.binary .sub (.local .here) (.local (.there .here)))).run (source x y hx hy tail state) =
      (.error .timeout,source x y hx hy tail state) := rfl

#print axioms family
#print axioms joint
#print axioms reject_all_refuted
#print axioms low_fuel
end H62.PrimitivePackets.UncheckedSignedSubCorrespondence
