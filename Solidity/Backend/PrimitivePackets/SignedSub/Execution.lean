import Solidity.Lowering.V07.SignedWordSubtraction
import Solidity.Backend.Passes.ValueCertificate

/-! Unchecked int256 local subtraction selected by the public value compiler.
Initial Source/local and machine representation are required; neither a desired
Source run, compiled certificate nor desired poststate is an input. This is the
intrinsic instruction interpreter, not deployed-bytecode/native adequacy. -/
namespace Solidity.Backend.PrimitivePackets.SignedSub
open Evm Evm.Memory Solidity.Lowering.V07
abbrev ty := SignedWordSubtraction.ty

def value {C : Contract} {Γ : Ctx} (a b : Idx Γ (.val .int)) : Val C Γ .int :=
  SignedWordSubtraction.subValue (.simple (.local a)) (.simple (.local b))

def selected {C : Contract} {Γ : Ctx} (base : Nat) (frag : Frag Γ)
    (a b : Idx Γ (.val .int)) : CompiledVal (C := C) base frag (value a b) :=
  (Memory.compileVal base frag (value a b)).get (by rfl)

theorem selection {C : Contract} {Γ : Ctx} (base : Nat) (frag : Frag Γ)
    (a b : Idx Γ (.val .int)) :
    Memory.compileVal (C := C) base frag (value a b) = some (selected (C := C) base frag a b) := by rfl

theorem emitted_code {C : Contract} {Γ : Ctx} (base : Nat) (frag : Frag Γ)
    (a b : Idx Γ (.val .int)) :
    (selected (C := C) base frag a b).code =
      [.mload (cellOf base a), .mload (cellOf base b), .swap 1, .sub] := by rfl

private theorem int_word_unique {v : PrimTy.int.Denote} {left right : Word}
    (a : ReprV .int v left) (b : ReprV .int v right) : left = right := by
  obtain ⟨x, rfl, hx⟩ := a
  obtain ⟨y, rfl, hy⟩ := b
  have same : x = y := Fin.ext (sgn_inj x.isLt y.isLt (hx.symm.trans hy))
  exact congrArg Word.val same

/-- Source computes its own wrapped result in either pipeline and retains its
state. The selected emitted code retains all caller machine fields and an
arbitrary saved stack; its exact output word has the signed result's canonical
representation. -/
theorem execution {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (frame : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int ty)) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily ty si ti source.1 target.env)
    (a b : ι) (x y : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi)
    (readA : source.1.get (si a) = .int x hx) (readB : source.1.get (si b) = .int y hy)
    (L base frameLimit : Nat) (frag : Frag Γ) (addresses : Nat → Fin W) (m : Machine)
    (represented : StateRepr L base frameLimit frag target addresses m) :
    (Source.evalE G {frame with checked := false} (fuel+3)
      (.binary .sub (.local (si a)) (.local (si b)))).run source =
        (.ok (.val (Source.intWrap ty (x-y))), source) ∧
    ∀ tail : List Word,
      run (selected (C := C) base frag (ti a) (ti b)).code {m with stack := tail} =
        .ok (({m with stack := tail} : Machine).push (.val (sword (ty.wrap (x-y))))) 0 ∧
      StateRepr L base frameLimit frag target addresses
        (({m with stack := tail} : Machine).push (.val (sword (ty.wrap (x-y))))) := by
  obtain ⟨sourceRun, valueRun, _⟩ := SignedWordSubtraction.locals_transport
    G frame fuel source target si ti family a b x y hx hy readA readB
  refine ⟨sourceRun, ?_⟩
  intro tail
  obtain ⟨word, hw, targetRun⟩ := Passes.value_success_tail
    (selected (C := C) base frag (ti a) (ti b)) represented valueRun tail
  have canonical := int_word_unique hw (ReprV.int_word
    (integerValue ty (ty.wrap (x-y)) (ty.wrap_mem (x-y))))
  cases canonical
  exact ⟨targetRun, (represented.stack tail).push _⟩

theorem source_horizon_zero {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (frame : Source.Fr) (source : Source.EMState E Γ)
    (a b : Source.Idx Γ (.int ty)) :
    (Source.evalE G {frame with checked := false} 0
      (.binary .sub (.local a) (.local b))).run source = (.error .timeout, source) := by rfl

/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selection
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.emitted_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms emitted_code
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms execution
/-- info: 'Solidity.Backend.PrimitivePackets.SignedSub.source_horizon_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_horizon_zero
end Solidity.Backend.PrimitivePackets.SignedSub
