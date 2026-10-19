import Solidity.Typing.Constructibility

/-!
# What the tests of `wt(storage)` decide

`SVal.Canon`, `SVal.Tight` (`Typing/Reachability.lean`, `Typing/Tight.lean`)
are propositions; `wt(storage)` (`Calculus/Problem.lean`)
asks them as tests the kernel evaluates (`Semantics/StorageWt.lean`:
`SVal.allB B`, a fold of node tests `B : HeredB`).  Here each test decides
its `Hered`'s node conditions clause for clause (`SVal.allB_iff`,
`Typing/Values.lean`):
`Storage.shapeB` is canonical and tight.
-/

namespace Solidity

open Semantics (structDef lookupBy setBy nodupKeysB)

variable {C : Contract}

/-! ## The three tests -/

theorem canonHB_decides : canonHB.Decides canonH :=
  ⟨fun _ _ => by simp only [canonHB, canonH],
    fun _ _ => by simp only [canonHB, canonH],
    fun _ _ m d => by simp only [canonHB, canonH, Bool.and_eq_true, SVal.beq_iff]⟩

theorem SVal.canonB_iff {T : Ty} (v : SVal T) : v.allB canonHB = true ↔ v.Canon :=
  SVal.allB_iff canonHB_decides v

theorem SList.toList_isEmpty {E : Ty} (sh : SList E) : sh.toList.isEmpty = true ↔ sh = .nil := by
  cases sh with
  | nil => simp only [SList.toList_nil, List.isEmpty_nil]
  | cons v rest => simp only [SList.toList_cons, List.isEmpty_cons, Bool.false_eq_true,
      reduceCtorEq]

theorem SMap.toList_isEmpty {K : PrimTy} {V : Ty} (m : SMap K V) : m.toList.isEmpty = true ↔ m = .nil := by
  cases m with
  | nil => simp only [SMap.toList_nil, List.isEmpty_nil]
  | cons k v rest => simp only [SMap.toList_cons, List.isEmpty_cons, Bool.false_eq_true,
      reduceCtorEq]

theorem tightHB_arr {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) :
    tightHB.arr e sh = true ↔ tightH.arr e sh := by
  show ((E.defaultOkS || (n == 0 && sh.toList.isEmpty)) &&
    (!E.isPrimitive || sh.toList.all fun w => w.beq (SVal.dflt E))) = true ↔
    ((E.defaultOkS = false → n = 0 ∧ sh = .nil) ∧
      (E.isPrimitive = true → ∀ w ∈ sh.toList, w = SVal.dflt E))
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, SList.toList_isEmpty,
    Bool.not_eq_true', List.all_eq_true, SVal.beq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun hd => ?_, fun hp => ?_⟩
    · rcases h1 with h | h
      · rw [hd] at h; exact nomatch h
      · exact h
    · rcases h2 with h | h
      · rw [hp] at h; exact nomatch h
      · exact h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · cases hd : E.defaultOkS
      · exact Or.inr (h1 hd)
      · exact Or.inl rfl
    · cases hp : E.isPrimitive
      · exact Or.inl rfl
      · exact Or.inr (h2 hp)

theorem tightHB_decides : tightHB.Decides tightH :=
  ⟨tightHB_arr, fun _ _ => by simp only [tightHB, tightH],
    fun _ _ _ _ => by simp only [tightHB, tightH]⟩

theorem SVal.tightB_iff {T : Ty} (v : SVal T) : v.allB tightHB = true ↔ v.Tight :=
  SVal.allB_iff tightHB_decides v

theorem Storage.shapeB_iff (st : Storage C) : st.shapeB = true ↔ st.Canon ∧ st.Tight := by
  simp only [Storage.shapeB, Bool.and_eq_true]
  rw [SFields.allB_iff canonHB_decides st, SFields.allB_iff tightHB_decides st]

end Solidity
