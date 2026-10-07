import Solidity.Calculus.Core.SoundControl
import Solidity.Calculus.Core.SoundMem
import Solidity.Calculus.Core.SoundCalls
import Solidity.Calculus.Core.SoundLoops

/-!
# Every arm of `Stmt.step` is sound

The dispatch over `Stmt.step`'s constructors (`Calculus/Core/Step.lean`):
each statement's rule is sound in the shape of
`Calculus/Core/SoundKit.lean` (`Stmt.StepSound`), by its arm's theorem in
`Calculus/Core/SoundLocal.lean`, `SoundControl.lean`, `SoundStore.lean`,
`SoundMem.lean`, `SoundArms.lean`, `SoundUpdates.lean`,
`Calculus/Core/Logic.lean`, and for the arms of `Calculus/Core/Blocks.lean`
`SoundCalls.lean` (calls), `SoundBlocks.lean` (`try`) and `SoundLoops.lean`
(loops).  A captured `if` condition's branches, weakened under its local,
run as before (`WkRuns`) by `Calculus/Core/RunWk.lean`'s `Prog.run_wk` at
`up`.
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

/-- **A block weakened under one local runs as before** (`Prog.run_wk` at
`up`, the local's value the lift's background). -/
theorem WkRuns.of_run_wk {Γ : Ctx} (σ : State C Γ) (t : LTy) : WkRuns σ t := fun P w =>
  let d : Env C (t :: Γ) := (w, σ.env)
  WkRel.eq_lifted (d := d) (WkRel.drop (Prog.wk_over P up) (Prog.run_wk P up d σ))

/-- **The rule of every statement is sound.** -/
theorem Stmt.stepSound (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') :
    Stmt.StepSound k m s := by
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
  | ite c thn els => exact iteStep_sound σ k (WkRuns.of_run_wk σ _) c thn els p hp
  | require c => exact requireStep_sound σ k c p hp
  | assert c => exact assertStep_sound σ k c p hp
  | revert => cases m <;> cases hp <;> exact fun ω κ φ h _ => Stmt.step_sound_revert σ ω κ φ h
  | call f args ret body => exact Stmt.stepSound_call k m f args ret body σ p hp
  | tryCall call rets ok err code pnc other =>
    exact Stmt.stepSound_tryCall k m call rets ok err code pnc other σ p hp
  | loop a c body => exact Stmt.stepSound_loop k m a c body σ p hp
  | block body => cases hp; exact fun ω κ φ h _ => Stmt.step_sound_block body σ ω κ φ h

end Solidity.Core
