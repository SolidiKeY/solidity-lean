import Solidity.Calculus.Core.SoundControl
import Solidity.Calculus.Core.SoundMem

/-!
# Every arm of `Stmt.step` but the blocks is sound

The dispatch over `Stmt.step`'s constructors (`Calculus/Core/Step.lean`):
each statement's rule is sound in the shape of
`Calculus/Core/SoundKit.lean` (`Stmt.StepSound`), by its arm's theorem in
`Calculus/Core/SoundLocal.lean`, `SoundControl.lean`, `SoundStore.lean`,
`SoundMem.lean`, `SoundArms.lean`, `SoundUpdates.lean` and
`Calculus/Core/Logic.lean`.  Two facts come from the call arms of
`Calculus/Core/Blocks.lean` and are premises here: the arms of the calls,
`try` and loops themselves (`Stmt.IsBlockArm`), and that a block weakened
under a captured `if` condition runs as before (`WkRuns`).
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

/-- The statements whose rules `Calculus/Core/Blocks.lean` gives: calls,
`try`, loops. -/
def Stmt.IsBlockArm {Γ Γ' : Ctx} : Stmt C Γ Γ' → Prop
  | .call .. => True
  | .tryCall .. => True
  | .loop .. => True
  | _ => False

/-- **The rule of every statement is sound**, given the block arms and the
run of a weakened block. -/
theorem Stmt.stepSound (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ')
    (hwk : ∀ σ : State C Γ, WkRuns σ (.val .bool))
    (hb : s.IsBlockArm → Stmt.StepSound k m s) : Stmt.StepSound k m s := by
  intro σ p hp
  cases s with
  | assign l r => exact assignStep_sound σ k l r p hp
  | rebind i r => exact rebindStep_sound σ k i r p hp
  | assignLocal i v => exact localStep_sound σ k i v p hp
  | declLocal q x init =>
    cases init with
    | none => cases hp; exact fun ω κ φ h _ => Stmt.step_sound_valueDeclSkip q x σ ω κ φ h
    | some e => cases hp; exact fun ω κ φ h _ => Stmt.step_sound_localValueDeclInitDrop x e σ ω κ φ h
  | declStorage R x init =>
    cases init with
    | none => cases hp; exact fun ω κ φ h _ => Stmt.step_sound_storageLocalDeclSkip R x σ ω κ φ h
    | some r => cases hp; exact sound_declStorageInit σ x r
  | opAssign op hop hp' l r => exact opStep_sound σ k op hop hp' l r p hp
  | incDec op hp' l => exact incStep_sound σ k op hp' l p hp
  | assignIncDec i op hp' l hs => cases hp; exact sound_assignIncDec σ i op hp' l hs
  | push b v hd => exact pushStep_sound σ k b v hd p hp
  | pop b => exact popStep_sound σ k b p hp
  | transfer r a => exact transferStep_sound σ k r a p hp
  | send pv r a => exact sendStep_sound σ k pv r a p hp
  | declMem R x init hd hm =>
    cases init with
    | none => cases hp; exact sound_declMemFresh σ R x hd hm
    | some r => cases hp; exact sound_declMemInit σ x r hd hm
  | rebindMem i r => exact rebindMemStep_sound σ k i r p hp
  | assignFromMem l q => exact assignFromMemStep_sound σ k l q p hp
  | assignMem l r => exact assignMemStep_sound σ k l r p hp
  | delete l => exact deleteStep_sound σ k l p hp
  | deleteMem q hd => exact deleteMemStep_sound σ k q hd p hp
  | assignNew l n h => cases hp; exact sound_assignNew σ k l n h
  | ite c thn els => exact iteStep_sound σ k (hwk σ) c thn els p hp
  | require c => exact requireStep_sound σ k c p hp
  | assert c => exact assertStep_sound σ k c p hp
  | revert => cases m <;> cases hp <;> exact fun ω κ φ h _ => Stmt.step_sound_revert σ ω κ φ h
  | call f args ret body => exact hb trivial σ p hp
  | tryCall call rets ok err code pnc other => exact hb trivial σ p hp
  | loop a c body => exact hb trivial σ p hp
  | block body => cases hp; exact fun ω κ φ h _ => Stmt.step_sound_block body σ ω κ φ h

end Solidity.Core
