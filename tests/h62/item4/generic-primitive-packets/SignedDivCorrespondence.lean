import Solidity.Backend.PrimitivePackets.SignedDiv.Controls

/-! Regression: signed division truncates toward zero, rejects zero in both
modes, and distinguishes checked minimum divided by minus one panic from unchecked wrap. Actual
Source locals and populated target memory are constructed; public compilation
and every saved stack are retained. This is primitive content correspondence,
not a whole-world/session/gas or fetched-EVM adequacy claim. -/
namespace H62.PrimitivePackets.SignedDivCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory
open Solidity.Backend.PrimitivePackets.SignedDiv

def source {E : Source.Env} {Δ : Source.RCtx} (a b : PrimTy.int.Denote)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    Source.EMState E (.int T :: .int T :: Δ) :=
  (.cons (sourceValue a) (.cons (sourceValue b) tail), state)

def code (checked : Bool) := (selected (C := Solidity.Backend.PrimitivePackets.SignedDiv.Controls.P) 0 Solidity.Backend.PrimitivePackets.SignedDiv.Controls.F checked .here (.there .here)).code

theorem selection (checked : Bool) :
    compileVal 0 Solidity.Backend.PrimitivePackets.SignedDiv.Controls.F (expression (C := Solidity.Backend.PrimitivePackets.SignedDiv.Controls.P) checked .here (.there .here)) =
      some (selected (C := Solidity.Backend.PrimitivePackets.SignedDiv.Controls.P) 0 Solidity.Backend.PrimitivePackets.SignedDiv.Controls.F checked .here (.there .here)) :=
  public_selection 0 Solidity.Backend.PrimitivePackets.SignedDiv.Controls.F checked .here (.there .here)

theorem ordinary {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (tail : Source.Locals E.layout Δ) (state : Source.St E)
    (a b : PrimTy.int.Denote) (nonzero : b.val ≠ 0)
    (normal : ¬ (a.val = -((2^255 : Nat) : Int) ∧ b.val = -1)) (saved : List Word) :
    (Source.evalE G fr (fuel+3) (.binary .div (.local .here) (.local (.there .here)))).run
      (source a b tail state) =
      (.ok (.val (sourceValue (quotient a b nonzero normal))), source a b tail state) ∧
    run (code fr.checked) {Solidity.Backend.PrimitivePackets.SignedDiv.Controls.machine a b with stack := saved} =
      .ok ({Solidity.Backend.PrimitivePackets.SignedDiv.Controls.machine a b with stack := saved}.push (.val (sword (a.val.tdiv b.val)))) 0 := by
  obtain ⟨src,w,repr,runs⟩ := ordinary_execution G fr fuel (source a b tail state)
    (Solidity.Backend.PrimitivePackets.SignedDiv.Controls.target a b) .here (.there .here) .here (.there .here) a b rfl rfl rfl rfl
    nonzero normal (Solidity.Backend.PrimitivePackets.SignedDiv.Controls.initial a b) saved
  have same := Solidity.Backend.PrimitivePackets.SignedDiv.Controls.word_unique (quotient a b nonzero normal) w repr
  rw [same] at runs
  exact ⟨src,runs⟩

theorem zero {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (tail : Source.Locals E.layout Δ) (state : Source.St E)
    (a b : PrimTy.int.Denote) (hz : b.val = 0) (saved : List Word) :
    (Source.evalE G fr (fuel+3) (.binary .div (.local .here) (.local (.there .here)))).run
      (source a b tail state) =
      (.error (.revert (Source.panicData .divZero)), source a b tail state) ∧
    run (code fr.checked) {Solidity.Backend.PrimitivePackets.SignedDiv.Controls.machine a b with stack := saved} = .revert :=
  zero_execution G fr fuel (source a b tail state) (Solidity.Backend.PrimitivePackets.SignedDiv.Controls.target a b)
    .here (.there .here) .here (.there .here) a b rfl rfl rfl rfl hz (Solidity.Backend.PrimitivePackets.SignedDiv.Controls.initial a b) saved

theorem exceptional {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (tail : Source.Locals E.layout Δ) (state : Source.St E)
    (a b : PrimTy.int.Denote) (minimum : a.val = -((2^255 : Nat) : Int))
    (minusOne : b.val = -1) (saved : List Word) :
    (Source.evalE G {fr with checked := true} (fuel+3)
      (.binary .div (.local .here) (.local (.there .here)))).run (source a b tail state) =
      (.error (.revert (Source.panicData .arithmetic)), source a b tail state) ∧
    run (code true) {Solidity.Backend.PrimitivePackets.SignedDiv.Controls.machine a b with stack := saved} = .revert ∧
    (Source.evalE G {fr with checked := false} (fuel+3)
      (.binary .div (.local .here) (.local (.there .here)))).run (source a b tail state) =
      (.ok (.val (sourceValue Backend.Scalar.minimumInt)), source a b tail state) ∧
    run (code false) {Solidity.Backend.PrimitivePackets.SignedDiv.Controls.machine a b with stack := saved} =
      .ok ({Solidity.Backend.PrimitivePackets.SignedDiv.Controls.machine a b with stack := saved}.push
        (.val (sword Backend.Scalar.minimumInt.val))) 0 := by
  obtain ⟨sc,tc,su,w,repr,runs⟩ := overflow_execution G fr fuel (source a b tail state)
    (Solidity.Backend.PrimitivePackets.SignedDiv.Controls.target a b) .here (.there .here) .here (.there .here) a b rfl rfl rfl rfl
    minimum minusOne (Solidity.Backend.PrimitivePackets.SignedDiv.Controls.initial a b) saved
  rw [Solidity.Backend.PrimitivePackets.SignedDiv.Controls.word_unique Backend.Scalar.minimumInt w repr] at runs
  exact ⟨sc,tc,su,runs⟩

theorem low_fuel {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (a b : PrimTy.int.Denote)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.evalE G fr 0 (.binary .div (.local .here) (.local (.there .here)))).run
      (source a b tail state) = (.error .timeout, source a b tail state) := rfl

theorem truncation (checked : Bool) (saved : List Word) :
    run (code checked) {Solidity.Backend.PrimitivePackets.SignedDiv.Controls.machine Solidity.Backend.PrimitivePackets.SignedDiv.Controls.negSeven Solidity.Backend.PrimitivePackets.SignedDiv.Controls.two with stack := saved} =
      .ok ({Solidity.Backend.PrimitivePackets.SignedDiv.Controls.machine Solidity.Backend.PrimitivePackets.SignedDiv.Controls.negSeven Solidity.Backend.PrimitivePackets.SignedDiv.Controls.two with stack := saved}.push (.val (sword (-3)))) 0 :=
  (ordinary (Source.SemanticsExamples.G0 .legacy)
    {Source.SemanticsExamples.F0 with checked := checked} 0 .nil Source.SemanticsExamples.s0
    Solidity.Backend.PrimitivePackets.SignedDiv.Controls.negSeven Solidity.Backend.PrimitivePackets.SignedDiv.Controls.two (by decide) (by decide) saved).2

theorem reject_all_refuted (checked : Bool) (saved : List Word) :
    run (code checked) {Solidity.Backend.PrimitivePackets.SignedDiv.Controls.machine Solidity.Backend.PrimitivePackets.SignedDiv.Controls.negSeven Solidity.Backend.PrimitivePackets.SignedDiv.Controls.two with stack := saved} ≠ .revert := by
  rw [truncation checked saved]
  intro h
  cases h

#print axioms truncation
#print axioms reject_all_refuted
#print axioms selection
#print axioms ordinary
#print axioms zero
#print axioms exceptional
#print axioms low_fuel
end H62.PrimitivePackets.SignedDivCorrespondence
