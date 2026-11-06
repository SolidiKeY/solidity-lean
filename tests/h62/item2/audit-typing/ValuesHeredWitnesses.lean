import tests.h62.item2.«audit-typing».ValuesDefaultsWitnesses

namespace H62.AuditTyping.ValuesHeredWitnesses
open Solidity
open H62.AuditTyping.ValuesDefaultsWitnesses (truthH)

def monoTruth : truthH.Mono truthH (fun _ => True) where
  gs := fun _ _ _ _ => True.intro
  ga := fun _ _ => True.intro
  gf := fun _ _ _ => True.intro
  gm := fun _ _ _ => True.intro
  arr := fun _ _ _ _ _ => True.intro
  fix := fun _ _ _ _ => True.intro
  map := fun _ _ _ _ => True.intro

def truthB : HeredB where
  arr := fun _ _ => true
  fix := fun _ _ => true
  map := fun _ {_} _ _ => true

def decidesTruth : truthB.Decides truthH where
  arr := fun _ _ => ⟨fun _ => True.intro, fun _ => rfl⟩
  fix := fun _ _ => ⟨fun _ => True.intro, fun _ => rfl⟩
  map := fun _ {_} _ _ => ⟨fun _ => True.intro, fun _ => rfl⟩

theorem val_mono : ∃ (P Q : Hered) (G : Ty → Prop), ∃ (_hm : P.Mono Q G),
    ∃ (T : Ty) (v : SVal T), ∃ (_g : G T) (_hq : v.All Q), True :=
  ⟨truthH, truthH, fun _ => True, monoTruth, .prim .bool, .prim false,
    True.intro, by simp only [SVal.All_prim], True.intro⟩

theorem fields_mono : ∃ (P Q : Hered) (G : Ty → Prop), ∃ (_hm : P.Mono Q G),
    ∃ (fs : List (Solidity.Name × Ty)) (x : SFields fs),
    ∃ (_g : ∀ nt ∈ fs, G nt.2) (_hq : x.All Q), True :=
  ⟨truthH, truthH, fun _ => True, monoTruth, [("x", .prim .bool)],
    .cons (.prim false) .nil, fun _ _ => True.intro,
    by simp only [SFields.All_cons, SVal.All_prim, SFields.All_nil, true_and], True.intro⟩

theorem list_mono : ∃ (P Q : Hered) (G : Ty → Prop), ∃ (_hm : P.Mono Q G),
    ∃ (E : Ty) (l : SList E), ∃ (_g : G E) (_hq : l.All Q), True :=
  ⟨truthH, truthH, fun _ => True, monoTruth, .prim .bool,
    .cons (.prim false) .nil, True.intro, by simp only [SList.All_cons, SVal.All_prim, SList.All_nil, true_and], True.intro⟩

theorem vec_mono : ∃ (P Q : Hered) (G : Ty → Prop), ∃ (_hm : P.Mono Q G),
    ∃ (E : Ty) (n : Nat) (l : SVec E n), ∃ (_g : G E) (_hq : l.All Q), True :=
  ⟨truthH, truthH, fun _ => True, monoTruth, .prim .bool, 1,
    .cons (.prim false) .nil, True.intro, by simp only [SVec.All_cons, SVal.All_prim, SVec.All_nil, true_and], True.intro⟩

theorem map_mono : ∃ (P Q : Hered) (G : Ty → Prop), ∃ (_hm : P.Mono Q G),
    ∃ (K : PrimTy) (V : Ty) (m : SMap K V), ∃ (_g : G V) (_hq : m.All Q), True :=
  ⟨truthH, truthH, fun _ => True, monoTruth, .bool, .prim .bool,
    .cons false (.prim false) .nil, True.intro, by simp only [SMap.All_cons, SVal.All_prim, SMap.All_nil, true_and], True.intro⟩

theorem val_decides : ∃ (P : Hered) (B : HeredB), ∃ (_hb : B.Decides P),
    ∃ (T : Ty) (_v : SVal T), True :=
  ⟨truthH, truthB, decidesTruth, .prim .bool, .prim false, True.intro⟩

theorem fields_decides : ∃ (P : Hered) (B : HeredB), ∃ (_hb : B.Decides P),
    ∃ (fs : List (Solidity.Name × Ty)) (_x : SFields fs), True :=
  ⟨truthH, truthB, decidesTruth, [("x", .prim .bool)], .cons (.prim false) .nil, True.intro⟩

theorem list_decides : ∃ (P : Hered) (B : HeredB), ∃ (_hb : B.Decides P),
    ∃ (E : Ty) (_l : SList E), True :=
  ⟨truthH, truthB, decidesTruth, .prim .bool, .cons (.prim false) .nil, True.intro⟩

theorem vec_decides : ∃ (P : Hered) (B : HeredB), ∃ (_hb : B.Decides P),
    ∃ (E : Ty) (n : Nat) (_l : SVec E n), True :=
  ⟨truthH, truthB, decidesTruth, .prim .bool, 1, .cons (.prim false) .nil, True.intro⟩

theorem map_decides : ∃ (P : Hered) (B : HeredB), ∃ (_hb : B.Decides P),
    ∃ (K : PrimTy) (V : Ty) (_m : SMap K V), True :=
  ⟨truthH, truthB, decidesTruth, .bool, .prim .bool, .cons false (.prim false) .nil, True.intro⟩

-- A reject-all node test cannot supply the same global decision certificate.
def rejectB : HeredB where
  arr := fun _ _ => false
  fix := fun _ _ => false
  map := fun _ {_} _ _ => false

theorem reject_node_test_not_decides : ¬ rejectB.Decides truthH := by
  intro h
  have bad : false = true := (h.fix (.prim .bool) 0).mpr True.intro
  cases bad

-- The actual global Mono capability can exist while no value input meets G T.
def falseG : Ty → Prop := fun _ => False

def monoFalseG : truthH.Mono truthH falseG where
  gs := fun _ h _ _ => h
  ga := fun _ h => h
  gf := fun _ _ h => h
  gm := fun _ _ h => h
  arr := fun _ _ _ _ _ => True.intro
  fix := fun _ _ _ _ => True.intro
  map := fun _ _ _ _ => True.intro

theorem capability_without_feasible_input :
    ∃ (P Q : Hered) (G : Ty → Prop) (_hm : P.Mono Q G),
      ¬ (∃ (T : Ty) (v : SVal T), G T ∧ v.All Q) := by
  refine ⟨truthH, truthH, falseG, monoFalseG, ?_⟩
  intro h
  obtain ⟨_T, _v, hG, _hAll⟩ := h
  exact hG

-- Do not overgeneralize the value boundary: empty field lists have no
-- member requiring G, so their universal member condition remains feasible.
theorem empty_fields_feasible : ∃ (fs : List (Solidity.Name × Ty)) (x : SFields fs),
    (∀ nt ∈ fs, falseG nt.2) ∧ x.All truthH := by
  refine ⟨[], .nil, ?_, ?_⟩
  · intro _nt h
    cases h
  · simp only [SFields.All_nil]

end H62.AuditTyping.ValuesHeredWitnesses
