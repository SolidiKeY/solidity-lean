import Solidity.Calculus.Core.TSoundControl
import Solidity.Calculus.Core.TSoundMem
import Solidity.Calculus.Core.TSoundStore

/-!
# Every arm of `Stmt.step` but the blocks is sound over the typed state

The dispatch over `Stmt.step`'s constructors (`Calculus/Core/Step.lean`),
as `Calculus/Core/SoundStep.lean`'s `Stmt.stepSound`, read over the typed
state (`Premise.TSound`): each statement's rule by its arm's theorem in
`Calculus/Core/TSoundArms.lean`, `TSoundStore.lean`, `TSoundMem.lean`,
`TSoundLocal.lean`, `TSoundControl.lean`.  The arms of
`Calculus/Core/Blocks.lean` (calls, `try`, loops: `Stmt.isBlockArm`) are the
`tsoundB` lane's.

**One condition** (`Stmt.TArmOk`, `Calculus/Core/TSoundKit.lean`), where
the typed reading of a rule fails: `T memory mv = r;` under the box has a
reference of its type in the heap.  Its hidden binder is universal there
(decision 12), vacuous over a heap typing with no object of the type, while
`r` may allocate one.  An alias `T memory mv = mp;` needs none
(`tsound_declMemAlias`): the object `mp` names is one, and a halt reading
it closes the box.  Decisions 15 and 16 took the other two away: a push at
the bound is exhausted, which both modalities accept, and no struct repeats
a member name, so every copy is on the bridge.  `Calculus/Core/TSound.lean`
assembles the blocks' arms with these.

A `new` meets no condition of its own (`tsound_assignNew` compares typed
runs): it unfolds to `T memory mv = new T(n); l = mv;`, and the condition
falls on the first step.
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
state**, where the statement meets its arm's condition. -/
theorem Stmt.tstepSound_arms (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ')
    (hb : s.isBlockArm = false) : Stmt.TStepSound k m s := by
  intro σ p hp hok
  cases s with
  | assign l r => exact assignStep_tsound σ k l r p hp
  | rebind i r => exact rebindStep_tsound σ k i r p hp
  | assignLocal i v => exact localStep_tsound σ k i v p hp
  | declLocal q x init =>
    cases init with
    | none => cases hp; exact tsound_valueDeclSkip σ q x
    | some e => cases hp; exact tsound_localValueDeclInitDrop σ x e
  | declStorage R x init =>
    cases init with
    | none => cases hp; exact tsound_storageLocalDeclSkip σ R x
    | some r => cases hp; exact tsound_declStorageInit σ x r
  | opAssign op hop hp' l r => exact opStep_tsound σ k op hop hp' l r p hp
  | incDec op hp' l => exact incStep_tsound σ k op hp' l p hp
  | assignIncDec i op hp' l hs => cases hp; exact tsound_assignIncDec σ i op hp' l hs
  | push b v hd => exact pushStep_tsound σ k b v hd p hp
  | pop b => exact popStep_tsound σ k b p hp
  | transfer r a => exact transferStep_tsound σ k r a p hp
  | send pv r a => exact sendStep_tsound σ k pv r a p hp
  | declMem R x init hd hm =>
    cases init with
    | none => cases hp; exact tsound_declMemFresh σ R x hd hm
    | some r =>
      cases r with
      | alias b => cases hp; exact tsound_declMemAlias σ x b hd hm
      | copy q hm' => cases hp; exact tsound_declMemInit σ x (.copy q hm') hd hm hok
      | newArr n h => cases hp; exact tsound_declMemInit σ x (.newArr n h) hd hm hok
  | rebindMem i r => exact rebindMemStep_tsound σ k i r p hp
  | assignFromMem l q => exact assignFromMemStep_tsound σ k l q p hp
  | assignMem l r => exact assignMemStep_tsound σ k l r p hp
  | delete l => exact deleteStep_tsound σ k l p hp
  | deleteMem q hd => exact deleteMemStep_tsound σ k q hd p hp
  | assignNew l n h => cases hp; exact tsound_assignNew σ k l n h
  | ite c thn els => exact iteStep_tsound σ k c thn els p hp
  | require c => exact requireStep_tsound σ k c p hp
  | assert c => exact assertStep_tsound σ k c p hp
  | revert => cases m <;> cases hp <;> exact tsound_revert σ
  | call => cases hb
  | tryCall => cases hb
  | loop => cases hb
  | block body => cases hp; exact tsound_block σ body

end Solidity.Core
