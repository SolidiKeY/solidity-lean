import Solidity.Backend.InternalFlow.RuntimeFrameV3EffectfulScalarSource
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarSourceCheckLaws

/-! Source authentication for the existing write-then-recursion family.
The supplied syntax, including every quoted recursive child, is checked.
The source quotation index is not a new runtime cutoff. No target run,
approved-domain provenance or compiler instance is assumed or supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulSourceCheck
open RecursiveSource ScalarRecursiveSource
abbrev A := EffectfulScalarSource.A

/-- Recognize the actual parameter write, not a write to an arbitrary alias. -/
def checkWrite {C : Contract} (statement : Stmt C (Frame A) (Frame A)) :
 Option (PLift (statement=EffectfulScalarSource.write)) :=
 match statement with
 | .assignMem (.index .dyn (.var (.there (.there .here)) _) (.simple (.lit index _)))
     (.val (.simple (.lit value _))) =>
   if hi : index=0 then
     if hv : value=37 then some ⟨by simp only [EffectfulScalarSource.write,hi,hv]⟩ else none
   else none
 | _ => none

/-- Inspect the leading effect and delegate the entire supplied recursive
    quotation to the already checked scalar-family recognizer. -/
def check {C : Contract} (depth : Nat) (program : Prog C (Frame A) (Frame A)) :
 Option (PLift (program=EffectfulScalarSource.body depth)) :=
 match program with
 | .cons (.assignMem location value) rest => do
   let effect ← checkWrite (.assignMem location value)
   let tail ← ScalarSourceCheck.check A rfl depth rest
   pure ⟨by rw [effect.down,tail.down];rfl⟩
 | _ => none


theorem write_complete {C : Contract} :
 checkWrite (EffectfulScalarSource.write (C:=C))=some ⟨rfl⟩ := by rfl

/-- Every quotation index is recognized. No source depth is selected or
    replaced, and the complete existing recursive child checker is used. -/
theorem complete {C : Contract} (depth : Nat) :
 check (C:=C) depth (EffectfulScalarSource.body depth)=some ⟨rfl⟩ := by
 simp only [check,EffectfulScalarSource.body,EffectfulScalarSource.write,checkWrite,
   ScalarSourceCheck.complete,bind,Option.bind,pure,dif_pos True.intro]

/-- A consumer can share the exact already-checked effect and tail equations
    instead of independently normalizing a second complete body. -/
theorem checked_cons {C : Contract} (depth : Nat)
 (location : MLoc C (Frame A) (.prim .uint)) (value : MSrc C (Frame A) (.prim .uint))
 (rest : Prog C (Frame A) (Frame A))
 (effect : Stmt.assignMem location value=EffectfulScalarSource.write)
 (effectRoot : checkWrite (.assignMem location value)=some ⟨effect⟩)
 (tail : rest=ScalarRecursiveSource.body A rfl depth)
 (tailRoot : ScalarSourceCheck.check A rfl depth rest=some ⟨tail⟩) :
 check depth (.cons (.assignMem location value) rest)=some ⟨by rw [effect,tail];rfl⟩ := by
 simp only [check,effectRoot,tailRoot,bind,Option.bind,pure]

end Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulSourceCheck

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulSourceCheck.write_complete' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulSourceCheck.write_complete

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulSourceCheck.complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulSourceCheck.complete

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulSourceCheck.checked_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulSourceCheck.checked_cons
