import Solidity.Calculus.DecisionNumericCoverage

/-! # Decidable source syntax for the existing literal-linear uint grammar
The recognizer returns a derivation on the original intrinsic term. It does not
consult a decision verdict, Covered, lowering or a semantic validity oracle.
-/
namespace Solidity

/-- Extend the existing predicate to other intrinsic sorts as false. -/
def Tm.UIntLinearAt {C : Contract} {Γ : Ctx} : {s : Srt} → Tm C Γ s → Prop
  | .val .uint, t => t.UIntLinear
  | _, _ => False

/-- A direct uint literal carries equality with the original intrinsically sorted term. -/
def Tm.UIntLiteralAt {C : Contract} {Γ : Ctx} : {s : Srt} → Tm C Γ s → Type
  | .val .uint, t => {v : PrimTy.uint.Denote // t = Tm.app0 (.lit v)}
  | _, _ => PEmpty

def Tm.uintLiteralEvidence {C : Contract} {Γ : Ctx} {s : Srt}
    (t : Tm C Γ s) : Option t.UIntLiteralAt := by
  apply @Tm.casesOn C Γ (fun s t => Option t.UIntLiteralAt) s t
  · intros; exact none
  · intros; exact none
  · intros; exact none
  · intros; exact none
  · intros; exact none
  · intro s o
    apply @Op0.casesOn C (fun s o => Option (Tm.app0 (Γ := Γ) o).UIntLiteralAt) s o
    · intro p v
      cases p with
      | uint => exact some ⟨v, rfl⟩
      | bool | int => exact none
    all_goals intros; exact none
  all_goals intros; exact none

/-- Generalized operator dispatch; only primitive type/operator and Option are matched. -/
def Tm.uintBinaryEvidence {C : Contract} {Γ : Ctx} {A B S : Srt}
    (o : Op2 C A B S) :
    (a : Tm C Γ A) → (b : Tm C Γ B) → Option (PLift a.UIntLinearAt) →
      Option (PLift b.UIntLinearAt) → Option (PLift (Tm.app2 o a b).UIntLinearAt) := by
  apply @Op2.casesOn C
    (fun A B S o => (a : Tm C Γ A) → (b : Tm C Γ B) →
      Option (PLift a.UIntLinearAt) → Option (PLift b.UIntLinearAt) →
        Option (PLift (Tm.app2 o a b).UIntLinearAt)) A B S o
  · intro op p h a b ha hb
    cases p with
    | bool | int => exact none
    | uint =>
      cases op with
      | add => exact do
        let x ← ha
        let y ← hb
        pure ⟨.add x.down y.down⟩
      | sub => exact do
        let x ← ha
        let y ← hb
        pure ⟨.sub x.down y.down⟩
      | mul =>
        exact match a.uintLiteralEvidence with
        | some ⟨v, hv⟩ => hb.map (fun y => ⟨by rw [hv]; exact Tm.UIntLinear.mulL v y.down⟩)
        | none => match b.uintLiteralEvidence with
          | some ⟨v, hv⟩ => ha.map (fun x => ⟨by rw [hv]; exact Tm.UIntLinear.mulR v x.down⟩)
          | none => none
      | _ => exact none
  all_goals intros; exact none

/-- Syntactic evidence, using generalized-index casesOn and structural recursion. -/
def Tm.uintLinearEvidence {C : Contract} {Γ : Ctx} {s : Srt}
    (t : Tm C Γ s) : Option (PLift t.UIntLinearAt) := by
  apply @Tm.casesOn C Γ (fun s t => Option (PLift t.UIntLinearAt)) s t
  · intro p i
    cases p with
    | uint => exact some ⟨.local i⟩
    | bool | int => exact none
  · intros; exact none
  · intros; exact none
  · intros; exact none
  · intros; exact none
  · intro s o
    apply @Op0.casesOn C (fun s o => Option (PLift (Tm.app0 (Γ := Γ) o).UIntLinearAt)) s o
    · intro p v
      cases p with
      | uint => exact some ⟨.lit v⟩
      | bool | int => exact none
    all_goals intros; exact none
  · intros; exact none
  · intro A B S o a b
    exact Tm.uintBinaryEvidence o a b a.uintLinearEvidence b.uintLinearEvidence
  · intros; exact none
  · intros; exact none
termination_by structural t

/-- This Boolean is entirely a check of source constructors. -/
def Tm.uintLinearShape {C : Contract} {Γ : Ctx} (t : Tm C Γ (.val .uint)) : Bool :=
  t.uintLinearEvidence.isSome

theorem Tm.uintLinearShape_sound {C : Contract} {Γ : Ctx}
    (t : Tm C Γ (.val .uint)) (h : t.uintLinearShape = true) : t.UIntLinear := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  exact v.down

/-- Every derivation in the existing grammar is accepted by the source check. -/
theorem Tm.uintLinearShape_complete {C : Contract} {Γ : Ctx}
    {t : Tm C Γ (.val .uint)} (h : t.UIntLinear) : t.uintLinearShape = true := by
  induction h with
  | «local» i => rfl
  | lit v => rfl
  | add ha hb iha ihb =>
    obtain ⟨va, ea⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨vb, eb⟩ := Option.isSome_iff_exists.mp ihb
    change (Option.bind _ _).isSome = true
    rw [ea]
    change (Option.bind _ _).isSome = true
    rw [eb]
    rfl
  | sub ha hb iha ihb =>
    obtain ⟨va, ea⟩ := Option.isSome_iff_exists.mp iha
    obtain ⟨vb, eb⟩ := Option.isSome_iff_exists.mp ihb
    change (Option.bind _ _).isSome = true
    rw [ea]
    change (Option.bind _ _).isSome = true
    rw [eb]
    rfl
  | mulL v hb ihb =>
    dsimp only [Tm.uintLinearShape, Tm.uintLinearEvidence, Tm.uintBinaryEvidence,
      Tm.uintLiteralEvidence]
    rw [Option.isSome_map]
    exact ihb
  | mulR v ha iha =>
    cases ha <;> first
      | rfl
      | (change (Option.map _ _).isSome = true
         rw [Option.isSome_map]
         exact iha)

theorem Tm.uintLinearShape_iff {C : Contract} {Γ : Ctx}
    (t : Tm C Γ (.val .uint)) : t.uintLinearShape = true ↔ t.UIntLinear :=
  ⟨t.uintLinearShape_sound, Tm.uintLinearShape_complete⟩

/-- Constructive decidability of the original grammar, with no classical instance. -/
instance {C : Contract} {Γ : Ctx} (t : Tm C Γ (.val .uint)) : Decidable t.UIntLinear :=
  decidable_of_iff (t.uintLinearShape = true) t.uintLinearShape_iff

namespace Decide

/-- Executable source checks feed the existing constructive coverage bridge. -/
theorem uintShapePrefix_Covered {C : Contract} (name : Var)
    (a b : Tm C [.val .uint] (.val .uint))
    (ha : a.uintLinearShape = true) (hb : b.uintLinearShape = true)
    (hs : a.size + b.size ≤ 71) : (primitivePrefixEq name a b).Covered = true :=
  uintPrefix_Covered name (a.uintLinearShape_sound ha) (b.uintLinearShape_sound hb) hs

/-- The accepted source class has certified results under the unchanged hash premise. -/
theorem uintShapePrefix_certified {C : Contract} (name : Var)
    (a b : Tm C [.val .uint] (.val .uint))
    (ha : a.uintLinearShape = true) (hb : b.uintLinearShape = true)
    (hs : a.size + b.size ≤ 71) :
    (decideGoal (primitivePrefixEq name a b) = .proved ∧ Fml.ValidH (primitivePrefixEq name a b)) ∨
      ∃ σ : State C [], decideGoal (primitivePrefixEq name a b) = .refuted σ ∧
        ¬ Fml.holdsH σ (primitivePrefixEq name a b) :=
  uintPrefix_certified name (a.uintLinearShape_sound ha) (b.uintLinearShape_sound hb) hs

end Decide
end Solidity
