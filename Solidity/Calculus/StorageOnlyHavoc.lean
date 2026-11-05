import Solidity.Calculus.ExactRun
import Solidity.Calculus.CallbackHolds
import Solidity.Calculus.Proves

/-! Storage-preserving havoc expressed entirely with existing intrinsic
updates/formulas. Ledger and self balance remain universally quantified.
No callback execution restriction or source/native adequacy is assumed. -/
namespace Solidity
namespace StorageOnlyHavoc
variable {C : Contract} {Γ : Ctx}

def save (name : Var) : Upd C Γ (.old :: Γ) :=
  Upd.decl .nil name (.store (.app0 .storage))
def restore : Upd C (.old :: Γ) Γ :=
  (Upd.pop .nil (.push .refl)).snoc (.storage (.pvS .here))

theorem save_lands (name : Var) (σ : State C Γ) :
    (save name).Lands σ σ.globG (σ.push (t := .old) σ.storage) :=
  Upd.lands_decl (Upd.lands_nil σ) name rfl

theorem restore_lands (σ : State C Γ) (st : Storage C) (net : Ledger)
    (balance : PrimTy.uint.Denote) :
    (restore : Upd C (.old :: Γ) Γ).Lands
      ((σ.push (t := .old) σ.storage).havoc st net balance)
      (((σ.push (t := .old) σ.storage).havoc st net balance).globG.withStorage σ.storage)
      (σ.havoc σ.storage net balance) :=
  Upd.lands_snoc_storage
    (Upd.lands_pop_nil (.push .refl) ((σ.push (t := .old) σ.storage).havoc st net balance)) rfl

end StorageOnlyHavoc

/-- A derived typed formula, with no new Fml constructor or interpretation. -/
def Fml.havocStorageKept {C : Contract} {Γ : Ctx} (name : Var) (φ : Fml C Γ) : Fml C Γ :=
  .upd .box (StorageOnlyHavoc.save name)
    (.havoc (.upd .box StorageOnlyHavoc.restore φ))


/-- Exact storage-only nondeterminism: every ledger and self balance remains
possible. The snapshot is evaluated before havoc and does not escape scope. -/
theorem holds_havocStorageKept {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (name : Var) (φ : Fml C Γ) :
    holds σ (φ.havocStorageKept name) ↔
      ∀ (net : Ledger) (balance : PrimTy.uint.Denote),
        holds (σ.havoc σ.storage net balance) φ := by
  change (StorageOnlyHavoc.save name).afterT .box σ
    (fun τ => holds τ (.havoc (.upd .box StorageOnlyHavoc.restore φ))) ↔ _
  rw [Upd.afterT_lands_iff (StorageOnlyHavoc.save_lands name σ)]
  change (∀ (st : Storage C) (net : Ledger) (balance : PrimTy.uint.Denote),
    StorageOnlyHavoc.restore.afterT .box
      ((σ.push (t := .old) σ.storage).havoc st net balance) (holds · φ)) ↔ _
  constructor
  · intro all net balance
    exact (Upd.afterT_lands_iff
      (StorageOnlyHavoc.restore_lands σ σ.storage net balance) .box (holds · φ)).mp
        (all σ.storage net balance)
  · intro all st net balance
    exact (Upd.afterT_lands_iff
      (StorageOnlyHavoc.restore_lands σ st net balance) .box (holds · φ)).mpr
        (all net balance)


/-- Callback interpretation of exactly the same derived intrinsic formula. -/
theorem holdsC_havocStorageKept {C : Contract} {Γ : Ctx}
    (I : Fml C []) (pay : Bool) (σ : State C Γ) (name : Var) (φ : Fml C Γ) :
    holdsC I pay σ (φ.havocStorageKept name) ↔
      ∀ (net : Ledger) (balance : PrimTy.uint.Denote),
        holdsC I pay (σ.havoc σ.storage net balance) φ := by
  change (StorageOnlyHavoc.save name).afterT .box σ
    (fun τ => holdsC I pay τ (.havoc (.upd .box StorageOnlyHavoc.restore φ))) ↔ _
  rw [Upd.afterT_lands_iff (StorageOnlyHavoc.save_lands name σ)]
  change (∀ (st : Storage C) (net : Ledger) (balance : PrimTy.uint.Denote),
    StorageOnlyHavoc.restore.afterT .box
      ((σ.push (t := .old) σ.storage).havoc st net balance) (holdsC I pay · φ)) ↔ _
  constructor
  · intro all net balance
    exact (Upd.afterT_lands_iff
      (StorageOnlyHavoc.restore_lands σ σ.storage net balance) .box (holdsC I pay · φ)).mp
        (all σ.storage net balance)
  · intro all st net balance
    exact (Upd.afterT_lands_iff
      (StorageOnlyHavoc.restore_lands σ st net balance) .box (holdsC I pay · φ)).mpr
        (all net balance)

/-- Existing sequent constructors, with storage snapshot scoped and popped. -/
def Hyps.havocStorageKept {C : Contract} {Γ₀ Γ : Ctx}
    (H : Hyps C Γ₀ Γ) (name : Var) : Hyps C Γ₀ Γ :=
  ((H.upd .box (StorageOnlyHavoc.save name)).havoc).upd .box StorageOnlyHavoc.restore

theorem Hyps.wrap_havocStorageKept {C : Contract} {Γ₀ Γ : Ctx}
    (H : Hyps C Γ₀ Γ) (name : Var) (φ : Fml C Γ) :
    (H.havocStorageKept name).wrap φ = H.wrap (φ.havocStorageKept name) := rfl

end Solidity
