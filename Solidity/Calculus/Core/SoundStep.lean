import Solidity.Calculus.Core.SoundControl
import Solidity.Calculus.Core.SoundMem
import Solidity.Calculus.Core.SoundStore

/-!
# Every arm of `Stmt.step` but the blocks is sound

The dispatch over `Stmt.step`'s constructors (`Calculus/Core/Step.lean`),
over the typed state (`Premise.Sound`): each statement's rule by its arm's
theorem in `Calculus/Core/SoundArms.lean`, `SoundStore.lean`,
`SoundMem.lean`, `SoundLocal.lean`, `SoundControl.lean`.  The arms of
`Calculus/Core/Blocks.lean` (calls, `try`, loops: `Stmt.isBlockArm`) are
`SoundCalls.lean`'s and `SoundLoops.lean`'s.

**No condition.**  Decisions 15 and 16 took two away (a push at the bound
is exhausted, which both modalities accept; no struct repeats a member name,
so every copy is on the bridge), and 17' the last: `T memory mv = r;`'s
hidden binder ranges over an unset `mv` too, from which the premise's
`mv = r;` runs as the declaration does, whatever `r` allocates
(`sound_declMemInit`).  `Calculus/Core/Sound.lean` assembles the blocks'
arms with these.
-/

namespace Solidity.Core
open Solidity (Modality)

variable {C : Contract}

/-- The statements whose rules are `Calculus/Core/Blocks.lean`'s: calls,
`try`, loops. -/
def Stmt.isBlockArm : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Bool
  | _, _, .call .. | _, _, .tryCall .. | _, _, .loop .. => true
  | _, _, _ => false

/-- **The rule of every statement but a block's is sound over the typed
state.** -/
theorem Stmt.stepSound_arms (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ')
    (hb : s.isBlockArm = false) : Stmt.StepSound k m s := by
  intro σ p hp
  cases s with
  | assign l r => exact assignStep_sound σ k l r p hp
  | rebind i r => exact rebindStep_sound σ k i r p hp
  | assignLocal i v => exact localStep_sound σ k i v p hp
  | declLocal q x init =>
    cases init with
    | none => cases hp; exact sound_valueDeclSkip σ q x
    | some e => cases hp; exact sound_localValueDeclInitDrop σ x e
  | declStorage R x init =>
    cases init with
    | none => cases hp; exact sound_storageLocalDeclSkip σ R x
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
  | ite c thn els => exact iteStep_sound σ k c thn els p hp
  | require c => exact requireStep_sound σ k c p hp
  | assert c => exact assertStep_sound σ k c p hp
  | revert => cases m <;> cases hp <;> exact sound_revert σ
  | call => cases hb
  | tryCall => cases hb
  | loop => cases hb
  | block body => cases hp; exact sound_block σ body

end Solidity.Core
