import Solidity.Source.Preservation.Encoding
import Solidity.Source.StmtProgress

/-! Memory-preservation combinators for the joint fragment induction.
`MemPres` is preservation on success AND every halt, never a progress claim.
-/
namespace Solidity.Source.Preservation
open EM
variable {E : Env} {Γ : RCtx} {α β : Type}

def MemPres (m : EM E Γ α) : Prop :=
  ∀ H, Hoare (MemOK E H) m (fun _ y => MemOK E H y) (fun _ y => MemOK E H y)

namespace MemPres

theorem pure' (a : α) : MemPres (pure a : EM E Γ α) := fun _ => Hoare.pure' fun _ h => h
theorem halt' (e : Halt) : MemPres (halt e : EM E Γ α) := fun _ => Hoare.halt' fun _ h => h
theorem lift' (r : R α) : MemPres (lift r : EM E Γ α) := by
  intro H
  exact Hoare.lift' fun _ h => by cases r <;> exact h

theorem bind {m : EM E Γ α} {k : α → EM E Γ β} (hm : MemPres m)
    (hk : ∀ a, MemPres (k a)) : MemPres (m >>= k) :=
  fun H => Hoare.bind (hm H) fun a => hk a H

theorem locals' : MemPres (locals : EM E Γ (Locals E.layout Γ)) :=
  fun _ => Hoare.locals' fun _ h => h

theorem subNil (m : EM E [] α) (hm : MemPres m) :
    MemPres (sub .nil m : EM E Γ (α × Locals E.layout []))  := fun _ =>
  Hoare.conseq (sub_mem .nil m hm) (fun _ h => ⟨h, trivial⟩)
    (fun _ _ h => h) (fun _ _ h => h)

theorem getV' {t : STy} (v : RVal E.layout t) : MemPres (getV v : EM E Γ _) := lift' _
theorem readAt' (F : Fr) (p : SPath) (t : STy) : MemPres (readAt F p t : EM E Γ _) :=
  fun _ => readAt_keep F p t

theorem writeLoc' (F : Fr) (n : Nat) {t : STy} (hl : t.loc? = none)
    (loc : Loc E.layout Γ t) (v : Val E.layout t) : MemPres (writeLoc F n loc v)  := fun _ =>
  Hoare.conseq (writeLoc_memOK F n loc v)
    (fun _ h => ⟨h, Val.refOK_of_loc hl v⟩) (fun _ _ h => h) (fun _ _ h => h)

theorem readLoc' (F : Fr) {t : STy} (loc : Loc E.layout Γ t) (hl : LocOK loc) :
    MemPres (readLoc F loc) := by
  cases loc with
  | «local» i => exact bind locals' fun _ => pure' _
  | stor p => simp only [readLoc, if_neg (Bool.eq_false_iff.mp hl.1)]; exact readAt' F p t
  | mem _ _ => exact hl.elim
  | memByte _ _ => exact hl.elim
  | cd _ => exact hl.elim
  | cdBytes _ _ => exact hl.elim
  | cdString _ _ => exact hl.elim
  | cdArray _ _ => exact hl.elim
  | cdFixedArray _ _ => exact hl.elim

theorem keyStep' (F : Fr) (n : Nat) {t : STy} (v : RVal E.layout t) :
    MemPres (keyStep F n v : EM E Γ _) := by
  unfold keyStep
  split
  · intro H; exact Hoare.bind (bytesOfRV_mem F n _) fun _ => Hoare.pure' fun _ h => h
  · intro H; exact Hoare.bind (bytesOfRV_mem F n _) fun _ => Hoare.pure' fun _ h => h
  · intro H; exact Hoare.bind (bytesOfRV_mem F n _) fun _ => Hoare.pure' fun _ h => h
  · split
    · exact pure' _
    · exact halt' _
  · exact halt' _

end MemPres

#print axioms MemPres.subNil
#print axioms MemPres.writeLoc'
#print axioms MemPres.keyStep'
end Solidity.Source.Preservation
