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

**Three conditions** (`Stmt.TArmOk`), each where the typed reading of a rule
fails, for the lead (`docs/intrinsic.md`, "Left for the lead" and the W2.5
`tsoundA` section):

* a storage copy (`l = sp;`, `l = mp;`, `new` into storage) is on the
  bridge only at a type whose members have distinct names (`Src.bridgeOk`,
  `Ty.nodupS`): the update is `Update.lean`'s, which copies by name, and
  the typed run copies by position;
* a push (`b.push(v);`, `lsv = b.push();`) does not diverge under the
  diamond: at `2^256 - 1` elements the typed run diverges
  (`Storage.full`), and the rule's update, `Update.lean`'s unbounded
  `pushAt`, ends in a storage no typed state erases to, read vacuously;
* `T memory mv = r;` under the box has a reference of its type in the
  heap: its hidden binder is universal there (decision 12), vacuous over
  a heap typing with no object of the type, while `r` may allocate one.
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

/-- The statements whose rules are `Calculus/Core/Blocks.lean`'s: calls,
`try`, loops. -/
def Stmt.isBlockArm : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Bool
  | _, _, .call .. | _, _, .tryCall .. | _, _, .loop .. => true
  | _, _, _ => false

/-- **What an arm asks of the statement** for its rule to be sound over the
typed state in `σ` under `m` (the module docstring's three conditions);
`True` for every other statement. -/
def Stmt.TArmOk (m : Modality) : {Γ Γ' : Ctx} → TState C Γ → Stmt C Γ Γ' → Prop
  | _, _, _, .assign _ r => r.bridgeOk = true
  | _, _, _, .assignFromMem (R := R) _ _ => (Ty.ref R).nodupS = true
  | _, _, σ, .push b v hd => m = .diamond → (Stmt.trun σ (.push b v hd)).NoDiv
  | _, _, σ, .rebind i r => m = .diamond → (Stmt.trun σ (.rebind i r)).NoDiv
  | _, _, σ, .declMem R _ (some _) _ _ => m = .box → Nonempty ((LTy.mem R).TDenote C σ.H)
  | _, _, _, _ => True

/-- **The rule of every statement but a block's is sound over the typed
state**, where the statement meets its arm's condition. -/
theorem Stmt.tstepSound_arms (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ')
    (hb : s.isBlockArm = false) (σ : TState C Γ) (p : Premise C Γ Γ')
    (hp : s.step k m = some p) (hok : s.TArmOk m σ) : Premise.TSound m s p σ := by
  cases s with
  | assign l r => exact assignStep_tsound σ k l r hok p hp
  | rebind i r => exact rebindStep_tsound σ k i r hok p hp
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
  | push b v hd => exact pushStep_tsound σ k b v hd hok p hp
  | pop b => exact popStep_tsound σ k b p hp
  | transfer r a => exact transferStep_tsound σ k r a p hp
  | send pv r a => exact sendStep_tsound σ k pv r a p hp
  | declMem R x init hd hm =>
    cases init with
    | none => cases hp; exact tsound_declMemFresh σ R x hd hm
    | some r => cases hp; exact tsound_declMemInit σ x r hd hm hok
  | rebindMem i r => exact rebindMemStep_tsound σ k i r p hp
  | assignFromMem l q => exact assignFromMemStep_tsound σ k l q hok p hp
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
