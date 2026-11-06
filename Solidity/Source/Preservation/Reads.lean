import Solidity.Source.Preservation.Combinators

/-! Reads retain every state invariant, including on their existing halts.
These results do not assert readability or admit new expression fragments. -/
namespace Solidity.Source.Preservation
open EM
variable {E : Env} {Γ : RCtx}

theorem storRef_keep {P : EMState E Γ → Prop} (t : STy) (p : SPath) :
    Hoare P (storRef t p) (fun _ y => P y) (fun _ y => P y) := by
  unfold storRef
  exact Hoare.dite' (fun _ => Hoare.pure' fun _ h => h) (fun _ => Hoare.halt' fun _ h => h)

theorem memElem_keep {P : EMState E Γ → Prop} (a i : Nat) (t : STy) :
    Hoare P (memElem a i t) (fun _ y => P y) (fun _ y => P y) := by
  unfold memElem
  refine Hoare.bind (heapObj_get (a := a) fun _ h _ => h) fun ⟨s, d⟩ => ?_
  cases d with
  | array n hn xs =>
    refine Hoare.dite' (fun hi => ?_) (fun _ => Hoare.lift' fun _ h => h.1)
    exact Hoare.dite' (fun he => Hoare.lift' fun _ h => by cases (he ▸ xs ⟨i, hi⟩).asVal <;> exact h.1) (fun _ => Hoare.halt' fun _ h => h.1)
  | struct fs =>
    exact Hoare.bind (Hoare.lift' fun y h => by cases fs.nth i t <;> exact h.1) fun x =>
      Hoare.lift' fun y h => by cases x.asVal <;> exact h
  | _ => exact Hoare.halt' fun _ h => h.1

theorem readLoc_keep {P : EMState E Γ → Prop} (F : Fr) {t : STy} (loc : Loc E.layout Γ t) :
    Hoare P (readLoc F loc) (fun _ y => P y) (fun _ y => P y) := by
  cases loc with
  | «local» i => exact Hoare.bind (Hoare.locals' fun _ h => h) fun _ => Hoare.pure' fun _ h => h
  | stor p =>
    simp only [readLoc]
    exact Hoare.ite' (fun _ => storRef_keep t p) (fun _ => readAt_keep F p t)
  | mem a i => exact memElem_keep a i t
  | memByte a i =>
    simp only [readLoc]
    refine Hoare.bind (heapBytes_keep a) fun bs => ?_
    split
    · exact Hoare.pure' fun _ h => h
    · exact Hoare.lift' fun _ h => h
  | cd off => exact Hoare.lift' fun y h => by cases decodeWord E.layout (cdWordAt F off) t <;> exact h

theorem MemPres.readLoc_all (F : Fr) {t : STy} (loc : Loc E.layout Γ t) :
    MemPres (readLoc F loc) := fun _ => readLoc_keep F loc

theorem MemPres.storRef' (t : STy) (p : SPath) : MemPres (storRef t p : EM E Γ _) :=
  fun _ => storRef_keep t p

#print axioms readLoc_keep
end Solidity.Source.Preservation
