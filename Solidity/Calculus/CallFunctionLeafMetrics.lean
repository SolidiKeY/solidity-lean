import Solidity.Calculus.CallFunctionLeaf

/-! # Formula-context depth of call-family leaves
This measures contexts at every Fml/update boundary; programs and internal
intermediate update contexts are outside this metric. The owned emitter's
updates have only their recorded single-result boundary or a bulk drop.
It is not a byte count of kernel expressions or total annotation volume.
-/
namespace Solidity.CallFunctionLeaf
variable {C : Contract} {Γ Δ : Ctx}

/-- Largest actual formula context, including guards and result binders. -/
def contextPeak : {Δ : Ctx} → Fml C Δ → Nat
  | Δ, .tt => Δ.length
  | Δ, .eq _ _ => Δ.length
  | Δ, .wellFormed _ => Δ.length
  | Δ, .not φ => max Δ.length (contextPeak φ)
  | Δ, .and φ ψ => max Δ.length (max (contextPeak φ) (contextPeak ψ))
  | Δ, .imp φ ψ => max Δ.length (max (contextPeak φ) (contextPeak ψ))
  | Δ, .upd _ _ φ => max Δ.length (contextPeak φ)
  | Δ, .modal _ _ _ φ => max Δ.length (contextPeak φ)
  | Δ, .havoc φ => max Δ.length (contextPeak φ)
  | Δ, .all _ _ φ => max Δ.length (contextPeak φ)
  | Δ, .bind _ _ _ φ => max Δ.length (contextPeak φ)
  | Δ, .anon _ φ => max Δ.length (contextPeak φ)
  | Δ, .allocAll _ _ φ => max Δ.length (contextPeak φ)
  | Δ, .grow φ => max Δ.length (contextPeak φ)

/-- Halt observations introduce no new context. -/
theorem contextPeak_haltPost (m : Modality) :
    contextPeak (haltPost (C := C) (Δ := Δ) m) = Δ.length := by
  cases m <;> simp only [haltPost, contextPeak, Nat.max_self]

/-- The terminal introduces only its one fresh result position. -/
theorem contextPeak_terminal (m : Modality) (resultName : Var) (h : Ext Γ Δ)
    (j : Idx Γ (.val .uint)) (fn : Idx Δ .oldNet) (x : Idx Δ (.val .uint))
    (φ : Fml C Γ) :
    contextPeak (terminal m resultName h j fn x φ) =
      max (Δ.length + 1) (contextPeak φ) := by
  simp only [terminal, contextPeak, CallFunctionGraph.equalZ, contextPeak_haltPost,
    List.length_cons]
  omega

/-- Composition definitions include both their input and result positions. -/
theorem contextPeak_compose (inputName resultName : Var)
    (first second next : Idx Δ .oldNet) :
    contextPeak (CallFunctionGraph.compose (C := C) inputName resultName first second next) =
      Δ.length + 2 := by
  simp only [CallFunctionGraph.compose, CallFunctionGraph.equalZ, contextPeak,
    List.length_cons]
  omega

/-- A bound on actual emitted formula contexts, separate from tmSize. -/
theorem contextPeak_stages (m : Modality) (inputName resultName : Var)
    (j : Idx Γ (.val .uint)) (φ : Fml C Γ) (k : Nat)
    (h : Ext Γ Δ) (fn : Idx Δ .oldNet) (x : Idx Δ (.val .uint)) :
    contextPeak (stages m inputName resultName j φ k h fn x) ≤
      max (Δ.length + k + 2) (contextPeak φ) := by
  induction k generalizing Δ with
  | zero =>
    simp only [stages, contextPeak_terminal, Nat.add_zero]
    omega
  | succ k ih =>
    simp only [stages, contextPeak, contextPeak_compose, List.length_cons]
    have hb : contextPeak (stages m inputName resultName j φ k (.push h) .here x.there) ≤
        max ((LTy.oldNet :: Δ).length + k + 2) (contextPeak φ) :=
      ih (.push h) .here x.there
    simp only [List.length_cons] at hb
    omega

/-- The operational base includes its new table, input and captured result. -/
theorem contextPeak_base (inputName resultName : Var)
    (t : Tm C (.val .uint :: Γ) (.val .uint)) :
    contextPeak (CallFunctionOperationalBase.clause inputName resultName t) = Γ.length + 3 := by
  simp only [CallFunctionOperationalBase.clause, CallFunctionOperationalBase.atInput,
    CallFunctionOperationalBase.returnedEq, CallFunctionOperationalBase.failedEq,
    CallFunctionGraph.equalZ, contextPeak, List.length_cons]
  omega

/-- The complete leaf has a linearly bounded actual formula-context peak. -/
theorem contextPeak_leaf (m : Modality) (tableName inputName resultName : Var)
    (t : Tm C (.val .uint :: Γ) (.val .uint)) (k : Nat)
    (j x : Idx Γ (.val .uint)) (φ : Fml C Γ) :
    contextPeak (leaf m tableName inputName resultName t k j x φ) ≤
      max (Γ.length + k + 3) (contextPeak φ) := by
  simp only [leaf, contextPeak, contextPeak_base, List.length_cons]
  have hb : contextPeak (stages m inputName resultName j φ k (.push .refl)
      (.here : Idx (.oldNet :: Γ) .oldNet) x.there) ≤
      max ((LTy.oldNet :: Γ).length + k + 2) (contextPeak φ) :=
    contextPeak_stages m inputName resultName j φ k
      (.push .refl) (.here : Idx (.oldNet :: Γ) .oldNet) x.there
  simp only [List.length_cons] at hb
  omega

end Solidity.CallFunctionLeaf
