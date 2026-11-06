import Solidity.Lowering.V08.Controls

/-! Exact successful result reflection for the existing intrinsic callable.
Injectivity is an explicit observation premise, not a source/ABI/body adequacy
assumption. The complete returned World and value are retained. -/
namespace Solidity.Lowering.V08.CallableReflection
open Solidity.ContractWorld
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

theorem success_iff {α β : Type} (world : World contracts) {k : K}
    (self : Handle k) (entry : Entry (contracts k) α) (context : Context)
    (observe : α → β) (injective : ∀ a b, observe a = observe b → a = b)
    (next : World contracts) (value : α) :
    world.call self (observeEntry entry observe) context = .ok (next,observe value) ↔
      world.call self entry context = .ok (next,value) := by
  rw [call_observeEntry]
  cases result : world.call self entry context with
  | error halt =>
    constructor <;> intro impossible <;> cases impossible
  | ok pair =>
    obtain ⟨actualWorld,actualValue⟩ := pair
    simp only [Except.map,Except.ok.injEq,Prod.mk.injEq]
    constructor
    · intro ⟨sameWorld,sameValue⟩
      exact ⟨sameWorld,injective actualValue value sameValue⟩
    · intro ⟨sameWorld,sameValue⟩
      exact ⟨sameWorld,congrArg observe sameValue⟩

def tagged (bytes : List UInt8) : Nat × List UInt8 := (bytes.length,bytes)

theorem tagged_injective (a b : List UInt8) (same : tagged a = tagged b) : a = b :=
  congrArg Prod.snd same

/-- Real installed, funded entry: persistent/transient writes and complete bytes. -/
def funded : TRes (Option (Int × Int × Int × Int) × (Nat × List UInt8)) := do
  let world ← Controls.setup
  let (next,value) ← world.call (⟨Controls.self⟩ : Handle ())
    (observeEntry Controls.entry tagged) Controls.paidCtx
  pure (Controls.observe next,value)

theorem funded_complete : funded.toOption =
    some (some (93,7,3,9),(2,[0xab,0xcd])) := by decide +kernel

/-- Application preserves the exact World, not merely the listed vector. -/
theorem funded_reflection (world next : World Controls.catalog) :
    world.call (⟨Controls.self⟩ : Handle ()) (observeEntry Controls.entry tagged)
      Controls.paidCtx = .ok (next,(2,[0xab,0xcd])) ↔
    world.call (⟨Controls.self⟩ : Handle ()) Controls.entry Controls.paidCtx =
      .ok (next,[0xab,0xcd]) :=
  success_iff world _ _ _ tagged tagged_injective next [0xab,0xcd]

def alternative : Entry Controls.Cell (List UInt8) :=
  { Controls.entry with result := fun _ => .ok [0xab,0xce] }

def lossyAlternative : TRes (Option (Int × Int × Int × Int) × Nat) := do
  let world ← Controls.setup
  let (next,value) ← world.call (⟨Controls.self⟩ : Handle ())
    (observeEntry alternative List.length) Controls.paidCtx
  pure (Controls.observe next,value)

def exactAlternative : TRes (Option (Int × Int × Int × Int) × List UInt8) := do
  let world ← Controls.setup
  let (next,value) ← world.call (⟨Controls.self⟩ : Handle ()) alternative Controls.paidCtx
  pure (Controls.observe next,value)

/-- Same actual body/payment and length observation hide distinct return bytes. -/
theorem lossy_equal : Controls.extendedObservation.toOption = lossyAlternative.toOption := by
  decide +kernel

theorem exact_distinct : Controls.paidObservation.toOption ≠ exactAlternative.toOption := by
  decide +kernel

theorem lossy_inputs :
    ([0xab,0xcd] : List UInt8).length = ([0xab,0xce] : List UInt8).length ∧
    ([0xab,0xcd] : List UInt8) ≠ [0xab,0xce] := by decide +kernel

theorem wrong_payment : funded.toOption ≠
    some (some (86,14,3,9),(2,[0xab,0xcd])) := by decide +kernel

#print axioms success_iff
#print axioms tagged_injective
#print axioms funded_complete
#print axioms funded_reflection
#print axioms lossy_equal
#print axioms exact_distinct
#print axioms lossy_inputs
#print axioms wrong_payment
end Solidity.Lowering.V08.CallableReflection
