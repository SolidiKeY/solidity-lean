import Solidity.Backend.PrimitivePackets.SignedCast.Agreement
import Solidity.Backend.PrimitivePackets.SignedDiv.Controls

/-! Regression: explicit signed casts must wrap at the destination width even
in checked frames, preserve populated caller memory and every saved stack, and
match actual independent Source local evaluation. All legal source/destination
widths remain quantified. No heap/world/session/gas or fetched-EVM adequacy is
inferred, and the compiler's conditional is not described as SIGNEXTEND code. -/
namespace H62.PrimitivePackets.SignedCastCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory Solidity.Lowering.V07
open Solidity.Backend.PrimitivePackets.SignedCast

abbrev native (fromBits : Nat) (hf : Valid fromBits) (x : Int)
    (hx : (ty fromBits hf).lo ≤ x ∧ x ≤ (ty fromBits hf).hi) := integerValue (ty fromBits hf) x hx
abbrev spare := Solidity.Backend.PrimitivePackets.SignedDiv.Controls.zero
abbrev machine (fromBits : Nat) (hf : Valid fromBits) (x : Int)
    (hx : (ty fromBits hf).lo ≤ x ∧ x ≤ (ty fromBits hf).hi) :=
  Solidity.Backend.PrimitivePackets.SignedDiv.Controls.machine (native fromBits hf x hx) spare

def code (bits : Nat) (ht : Valid bits) :=
  (selected (C := Solidity.Backend.PrimitivePackets.SignedDiv.Controls.P) bits ht 0
    Solidity.Backend.PrimitivePackets.SignedDiv.Controls.F .here).code

theorem execute (fromBits bits : Nat) (hf : Valid fromBits) (ht : Valid bits)
    (x : Int) (hx : (ty fromBits hf).lo ≤ x ∧ x ≤ (ty fromBits hf).hi) (saved : List Word) :
    run (code bits ht) {machine fromBits hf x hx with stack := saved} =
      .ok ({machine fromBits hf x hx with stack := saved}.push (.val (sword ((ty bits ht).wrap x)))) 0 := by
  obtain ⟨word,repr,runs⟩ := target_success fromBits bits hf ht
    (Solidity.Backend.PrimitivePackets.SignedDiv.Controls.target (native fromBits hf x hx) spare)
    .here x hx rfl (Solidity.Backend.PrimitivePackets.SignedDiv.Controls.initial _ _) saved
  rw [Solidity.Backend.PrimitivePackets.SignedDiv.Controls.word_unique _ word repr] at runs
  exact runs

def source {E : Source.Env} {Δ : Source.RCtx} (fromBits : Nat) (hf : Valid fromBits)
    (x : Int) (hx : (ty fromBits hf).lo ≤ x ∧ x ≤ (ty fromBits hf).hi)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    Source.EMState E (.int (ty fromBits hf) :: Δ) := (.cons (.int x hx) tail,state)

theorem joint {E : Source.Env} {Δ : Source.RCtx}
    (fromBits bits : Nat) (hf : Valid fromBits) (ht : Valid bits)
    (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (x : Int) (hx : (ty fromBits hf).lo ≤ x ∧ x ≤ (ty fromBits hf).hi)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) (saved : List Word) :
    compileVal 0 Solidity.Backend.PrimitivePackets.SignedDiv.Controls.F
      (value (C := Solidity.Backend.PrimitivePackets.SignedDiv.Controls.P) bits .here) =
      some (selected bits ht 0 Solidity.Backend.PrimitivePackets.SignedDiv.Controls.F .here) ∧
    (Source.evalE G fr (fuel+2) (.convExplicit (τ := .int (ty bits ht))
      (.local .here) (SignedWidthCasts.allowed fromBits hf E bits ht))).run (source fromBits hf x hx tail state) =
      (.ok (.val (Source.intWrap (ty bits ht) x)),source fromBits hf x hx tail state) ∧
    run (code bits ht) {machine fromBits hf x hx with stack := saved} =
      .ok ({machine fromBits hf x hx with stack := saved}.push (.val (sword ((ty bits ht).wrap x)))) 0 :=
  ⟨public_selection bits ht 0 Solidity.Backend.PrimitivePackets.SignedDiv.Controls.F .here,
    source_success fromBits bits hf ht G fr fuel (source fromBits hf x hx tail state) .here x hx rfl,
    execute fromBits bits hf ht x hx saved⟩

theorem reject_all_refuted (fromBits bits : Nat) (hf : Valid fromBits) (ht : Valid bits)
    (x : Int) (hx : (ty fromBits hf).lo ≤ x ∧ x ≤ (ty fromBits hf).hi) (saved : List Word) :
    run (code bits ht) {machine fromBits hf x hx with stack := saved} ≠ .revert := by
  rw [execute]
  intro h
  cases h

theorem sign_boundary (saved : List Word) :
    run (code 8 (by decide)) {machine 16 (by decide) 128 (by decide) with stack := saved} =
      .ok ({machine 16 (by decide) 128 (by decide) with stack := saved}.push (.val (sword (-128)))) 0 := by
  have ran := execute 16 8 (by decide) (by decide) 128 (by decide) saved
  have wrap : (ty 8 (by decide)).wrap 128 = -128 := by decide
  rw [wrap] at ran
  exact ran

theorem negative_wrap (saved : List Word) :
    run (code 8 (by decide)) {machine 16 (by decide) (-129) (by decide) with stack := saved} =
      .ok ({machine 16 (by decide) (-129) (by decide) with stack := saved}.push (.val (sword 127))) 0 := by
  have ran := execute 16 8 (by decide) (by decide) (-129) (by decide) saved
  have wrap : (ty 8 (by decide)).wrap (-129) = 127 := by decide
  rw [wrap] at ran
  exact ran

#print axioms execute
#print axioms joint
#print axioms reject_all_refuted
#print axioms sign_boundary
#print axioms negative_wrap
end H62.PrimitivePackets.SignedCastCorrespondence
