import Solidity.Yul.World.CreationRules

/-! # Address-selected constructor consumer
The selected address uses the actual old creator nonce or the actual loaded
initcode hash. This is post-early-admission plumbing, not a complete CREATE
semantics: funding/depth/resources, late collision, allocation/lifecycle,
value transfer and code-deposit outcomes remain real producer obligations.
-/
namespace Solidity.Yul.World
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Fixed)
variable {D : Layout} {L T : Address → SPath → STy}

/-- None selects CREATE; Some salt selects CREATE2. Both reuse the approved raw
address definitions. Nonce is intrinsically bounded, never silently truncated. -/
def selectCreationAddress (F : Fixed) (creator : Address) (nonce : Fin (2^64))
    (salt : Option Word) (initcode : Bytes) : Address :=
  match salt with
  | none => createAddress F creator nonce
  | some salt => create2Address F creator salt initcode

theorem selected_create (F : Fixed) (creator : Address) (nonce : Fin (2^64)) (initcode : Bytes) :
    selectCreationAddress F creator nonce none initcode = createAddress F creator nonce := rfl

theorem selected_create2 (F : Fixed) (creator : Address) (nonce : Fin (2^64))
    (salt : Word) (initcode : Bytes) :
    selectCreationAddress F creator nonce (some salt) initcode = create2Address F creator salt initcode := rfl

/-- The caller must already have passed actual early opcode admission. Nonce
cap is additionally checked here. Raw bytes are loaded once, used for CREATE2
selection and passed unchanged as CODE; constructor calldata stays empty.
Late collision/code-deposit/failure classification are not inferred from None. -/
def addressedCreation {Memory : Type} (F : Fixed) (salt : Option Word) (port : BytePort Memory)
    (invoke : InitcodePort D L T) (entry : ObservedEffects D L T) (memory : Memory)
    (parent : CallFrame) (gas value offset size : Word) : Option (CompletedCreation D L T) :=
  if parent.static then none else
  if hn : (entry.effects.execution.world.accounts parent.this).nonce < 2^64-1 then do
    let code ← port.load memory offset size
    let allocated := selectCreationAddress F parent.this
      ⟨(entry.effects.execution.world.accounts parent.this).nonce, Nat.lt_trans hn (by decide)⟩ salt code
    let prepared ← prepareCreation entry parent.this
    let frame := constructorFrame prepared.effects.execution parent allocated value
    let answer ← invoke prepared gas frame code
    pure ⟨answer.outcome,finishCreation prepared frame answer,rfl⟩
  else none

theorem addressedCreation_static {Memory : Type} (F : Fixed) (salt : Option Word) (port : BytePort Memory)
    (invoke : InitcodePort D L T) (entry : ObservedEffects D L T) (memory : Memory)
    (parent : CallFrame) (gas value offset size : Word) (h : parent.static = true) :
    addressedCreation F salt port invoke entry memory parent gas value offset size = none := by
  simp only [addressedCreation,h,↓reduceIte]

theorem addressedCreation_cap {Memory : Type} (F : Fixed) (salt : Option Word) (port : BytePort Memory)
    (invoke : InitcodePort D L T) (entry : ObservedEffects D L T) (memory : Memory)
    (parent : CallFrame) (gas value offset size : Word)
    (hn : ¬ (entry.effects.execution.world.accounts parent.this).nonce < 2^64-1) :
    addressedCreation F salt port invoke entry memory parent gas value offset size = none := by
  cases hs : parent.static <;> simp only [addressedCreation,hs,hn,Bool.false_eq_true,↓reduceIte,dite_false]

theorem addressedCreation_exact {Memory : Type} (F : Fixed) (salt : Option Word) (port : BytePort Memory)
    (invoke : InitcodePort D L T) (entry : ObservedEffects D L T) (memory : Memory)
    (parent : CallFrame) (gas value offset size : Word) (code : Bytes)
    (prepared : ObservedEffects D L T) (answer : FrameAnswer D L T)
    (hs : parent.static = false)
    (hn : (entry.effects.execution.world.accounts parent.this).nonce < 2^64-1)
    (hl : port.load memory offset size = some code)
    (hp : prepareCreation entry parent.this = some prepared)
    (hi : invoke prepared gas (constructorFrame prepared.effects.execution parent
      (selectCreationAddress F parent.this
        ⟨(entry.effects.execution.world.accounts parent.this).nonce, Nat.lt_trans hn (by decide)⟩ salt code) value) code = some answer) :
    addressedCreation F salt port invoke entry memory parent gas value offset size =
      some ⟨answer.outcome,finishCreation prepared (constructorFrame prepared.effects.execution parent
        (selectCreationAddress F parent.this
          ⟨(entry.effects.execution.world.accounts parent.this).nonce, Nat.lt_trans hn (by decide)⟩ salt code) value) answer,rfl⟩ := by
  simp only [addressedCreation,hs,Bool.false_eq_true,↓reduceIte,hn,dite_true,hl,hp,hi,bind,Option.bind_some,pure]

namespace AddressedRules
open Solidity.Yul.World.AdapterRules (Configuration Box)
variable {Memory : Type}

def Step (F : Fixed) (salt : Option Word) (port : BytePort Memory) (invoke : InitcodePort D L T)
    (parent : CallFrame) (gas value offset size : Word) (outcome : Solidity.Roadmap.Outcome)
    (before after : Configuration Memory D L T) : Prop :=
  ∃ result, addressedCreation F salt port invoke before.observed before.memory parent gas value offset size = some result ∧
    result.initialization = outcome ∧ after.observed = result.observed ∧ after.memory = before.memory

/-- Lean-only normal-return rule for the actual address-selected function.
Preparation and selection are part of that function, not a producer assumption. -/
theorem addressed_rule (F : Fixed) (salt : Option Word) (port : BytePort Memory)
    (invoke : InitcodePort D L T) (parent : CallFrame) (gas value offset size : Word)
    (before : Configuration Memory D L T) (result : CompletedCreation D L T)
    (h : addressedCreation F salt port invoke before.observed before.memory parent gas value offset size = some result) :
    Box (Step F salt port invoke parent gas value offset size result.initialization)
      (fun after => after.observed = result.observed ∧ after.memory = before.memory ∧
        after.observed.effects.returndata = createReturnData result.initialization) before := by
  intro after hs
  obtain ⟨r,hr,_,he,hm⟩ := hs
  rw [h] at hr
  cases Option.some.inj hr
  refine ⟨he,hm,?_⟩
  rw [he]
  exact result.returndata_eq

end AddressedRules
end Solidity.Yul.World
