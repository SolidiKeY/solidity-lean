import Solidity.Calculus.Rules
import Solidity.Calculus.SoundLocal

/-! The census mutant `storageLengthRead_unfold_rightFst.receiver-reevaluated.1`
(`⟨[ T storage sp = nsp; v = nsp.length; ]⟩` in place of `… v = sp.length;`)
survives, and soundly: a storage path is a value with no effect (`SPath`,
`Val`, `Syntax/Scoped.lean`), so reading `nsp` again, under the captured
alias, gives the length the capture saw.  This is a universal proof that the
mutated premise is sound in every state, for every receiver, local and fresh
index; it is a certified survivor, not a kill. -/
namespace H28.LengthReevalSound
open Solidity

/-- The mutated constructor's premise, as it elaborates. -/
def mutated {C : Contract} {Γ : Ctx} (k : Nat) {p : PrimTy} (v : Idx Γ (.val p)) {E : Ty}
    (nsp : SPath C Γ (.array E)) (hp : p = .uint) : Premise C Γ Γ :=
  .captureSP (Var.fresh "sp" k) nsp (.assignLocal v.there (.len nsp.up hp))

/-- The witness is about the actual mutated production rule. -/
theorem source_link_all {C : Contract} {Γ : Ctx} (k : Nat) (m : Modality) {p : PrimTy}
    (v : Idx Γ (.val p)) {E : Ty} (nsp : SPath C Γ (.array E)) (hp : p = .uint)
    (hs : nsp.isSimple = false) :
    Taclet C k m (.assignLocal v (.len nsp hp)) (mutated k v nsp hp) :=
  .storageLengthRead_unfold_rightFst hs

/-- What the mutated premise asks of the run holds in every state. -/
theorem runs_all {C : Contract} {Γ : Ctx} (k : Nat) (m : Modality) {p : PrimTy}
    (v : Idx Γ (.val p)) {E : Ty} (nsp : SPath C Γ (.array E)) (hp : p = .uint)
    (σ : State C Γ) :
    Premise.Runs m (.assignLocal v (.len nsp hp)) (mutated k v nsp hp) σ := by
  subst hp
  refine Premise.sound_captureSPPushed σ (fun q hq => TRun.assignLocal_pushT σ (t := .alias _)
      (some q) v _ (.len nsp rfl) ?_) (fun h hh => ?_)
  · exact Val.evalT_up σ _ (.len nsp rfl)
  · show (TRun.assignLocal v _ σ).map _ = _
    simp only [TRun.assignLocal, Val.evalT, hh]; rfl

/-- **The mutant is sound**: in every state, for every instance. -/
theorem sound_all {C : Contract} {Γ : Ctx} (k : Nat) (m : Modality) {p : PrimTy}
    (v : Idx Γ (.val p)) {E : Ty} (nsp : SPath C Γ (.array E)) (hp : p = .uint) :
    ∀ σ : State C Γ, Premise.Sound m (.assignLocal v (.len nsp hp)) (mutated k v nsp hp) σ :=
  fun σ => (runs_all k m v nsp hp σ).sound

/-- The universal certificate has a concrete inhabited input. -/
theorem input_inhabited : Nonempty (State ({ vars := [] } : Contract) []) := ⟨.init _⟩

#print axioms source_link_all
#print axioms runs_all
#print axioms sound_all
#print axioms input_inhabited
set_option pp.fullNames true
#check @source_link_all
#check @sound_all
#check @input_inhabited
end H28.LengthReevalSound
