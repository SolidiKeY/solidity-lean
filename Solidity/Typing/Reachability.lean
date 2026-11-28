import Solidity.Typing.HeredRun


namespace Solidity

open Semantics (structDef lookupBy setBy nodupKeysB)

variable {C : Contract}


def canonH : Hered where
  arr _ _ := True
  fix _ _ := True
  map _ := fun {V} m d => nodupKeysB m.toList = true ∧ d = SVal.dflt V

abbrev SVal.Canon {T : Ty} (v : SVal T) : Prop := v.All canonH

abbrev Storage.Canon (st : Storage C) : Prop := st.All canonH

theorem SVal.dflt_canon (T : Ty) : (SVal.dflt T).Canon :=
  SVal.dflt_all (P := canonH) (fun _ => trivial) (fun _ _ => trivial)
    (fun _ _ => ⟨by rw [SMap.toList_nil]; rfl, rfl⟩) T

theorem canonH_run : HeredRun canonH (fun _ => True) where
  save _ _ _ _ _ _ _ _ := trivial
  map _ _ _ _ _ h := ⟨by rw [SMap.toList_ofList]; exact nodupKeysB_setBy' h.1, h.2⟩
  strip _ _ _ _ := trivial
  del _ _ _ _ := trivial
  ov _ _ _ _ _ _ _ _ _ := trivial
  push _ _ _ _ _ _ _ _ _ := trivial
  pop _ _ _ _ _ _ _ _ _ := trivial
  dflt := SVal.dflt_canon
  plain v _ h := SVal.all_mono' (P := canonH) (Q := plainH) (fun _ _ _ _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ h => h.elim) v h

theorem Storage.init_canon : (Storage.init C).Canon :=
  SFields.dflt_all (P := canonH) (fun _ => trivial) (fun _ _ => trivial)
    (fun _ _ => ⟨by rw [SMap.toList_nil]; rfl, rfl⟩) C.vars


abbrev canonInv (C : Contract) : RunInv C := heredInv C canonH

theorem Prog.run_canon {Γ Γ' : Ctx} (P : Prog C Γ Γ') {σ : State C Γ} {o : Out C σ.H Γ'}
    (hσ : (canonInv C).HoldsT σ) (h : P.run σ = .ok o) : o.st.storage.Canon :=
  Prog.run_all canonH_run (fun _ => trivial) P hσ h


def Reachable (C : Contract) (st : Storage C) : Prop :=
  ∃ (Γ' : Ctx) (P : Prog C [] Γ') (o : Out C (State.init C).H Γ'),
    P.run (State.init C) = .ok o ∧ o.st.storage = st

theorem heredInv.init {P : Hered} (h : (Storage.init C).All P) :
    (heredInv C P).HoldsT (State.init C) :=
  ⟨h, trivial⟩

theorem Reachable.all {P : Hered} {G : Ty → Prop} (hP : HeredRun P G)
    (hG : ∀ {U : Ty}, SRef C U → G U) (hi : (Storage.init C).All P) {st : Storage C}
    (h : Reachable C st) : st.All P := by
  obtain ⟨Γ', P', o, hrun, rfl⟩ := h
  exact Prog.run_all hP hG P' (heredInv.init hi) hrun

theorem reachable_canon {st : Storage C} (h : Reachable C st) : st.Canon :=
  Reachable.all canonH_run (fun _ => trivial) Storage.init_canon h


section Witnesses

def Balances : Contract := contract!{ mapping(uint => uint) balances; }

def Balances.five : Storage Balances :=
  .cons (.map .nil (.prim (PrimTy.ofLit .uint 5 rfl))) .nil

def Balances.dup : Storage Balances :=
  .cons (.map (.cons (PrimTy.ofLit .uint 1 rfl) (.prim (PrimTy.ofLit .uint 0 rfl))
    (.cons (PrimTy.ofLit .uint 1 rfl) (.prim (PrimTy.ofLit .uint 1 rfl)) .nil))
    (.prim (PrimTy.dflt .uint))) .nil

theorem map_default_not_reachable : ¬ Reachable Balances Balances.five := by
  intro h
  have hc := reachable_canon h
  simp only [Balances.five, SFields.All, SVal.All] at hc
  have hd := hc.1.1.2
  rw [SVal.dflt_prim] at hd
  cases hd

theorem map_dup_key_not_reachable : ¬ Reachable Balances Balances.dup := by
  intro h
  have hc := reachable_canon h
  simp only [Balances.dup, SFields.All, SVal.All] at hc
  exact absurd hc.1.1.1 (by simp only [SMap.toList]; decide)

end Witnesses

end Solidity
