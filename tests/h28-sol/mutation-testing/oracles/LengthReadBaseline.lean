import Solidity.Calculus.Rules
import Solidity.Calculus.SoundLocal

/-! The production `storageLengthRead_unfold_rightFst` at every instance: the
receiver captured once, its length read through the alias.  Its soundness is
the production `sound_lenCapture` (`Calculus/SoundLocal.lean`). -/
namespace H28.LengthReadBaseline
open Solidity

/-- The production premise. -/
def original {C : Contract} {Γ : Ctx} (k : Nat) {p : PrimTy} (v : Idx Γ (.val p)) {E : Ty}
    (nsp : SPath C Γ (.array E)) (hp : p = .uint) : Premise C Γ Γ :=
  .captureSP (Var.fresh "sp" k) nsp (.assignLocal v.there (.len (.alias .here) hp))

/-- The production rule has exactly this premise. -/
theorem source_link {C : Contract} {Γ : Ctx} (k : Nat) (m : Modality) {p : PrimTy}
    (v : Idx Γ (.val p)) {E : Ty} (nsp : SPath C Γ (.array E)) (hp : p = .uint)
    (hs : nsp.isSimple = false) :
    Taclet C k m (.assignLocal v (.len nsp hp)) (original k v nsp hp) :=
  .storageLengthRead_unfold_rightFst hs

/-- The production premise is sound in every state. -/
theorem sound_all {C : Contract} {Γ : Ctx} (k : Nat) (m : Modality) {p : PrimTy}
    (v : Idx Γ (.val p)) {E : Ty} (nsp : SPath C Γ (.array E)) (hp : p = .uint) :
    ∀ σ : State C Γ, Premise.Sound m (.assignLocal v (.len nsp hp)) (original k v nsp hp) σ :=
  fun σ => (sound_lenCapture σ v nsp hp (Var.fresh "sp" k)).sound

theorem input_inhabited : Nonempty (State ({ vars := [] } : Contract) []) := ⟨.init _⟩

#print axioms source_link
#print axioms sound_all
#print axioms input_inhabited
set_option pp.fullNames true
#check @source_link
#check @sound_all
end H28.LengthReadBaseline
