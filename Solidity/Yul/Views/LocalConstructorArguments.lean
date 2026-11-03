import Solidity.Yul.Views.StructConstructorFields

namespace Solidity.Yul.Views

/-- Checked inspection of the ACTUAL typed owner expression. No duplicate AST,
execution engine, or admission rule. Unsupported shapes produce preparation None. -/
def localConstructorValue {E Γ τ} (locals : Source.Locals E.layout Γ) (expr : Source.RExpr E Γ τ) :
    Option (Source.Val E.layout τ) := by
  cases expr with
  | «local» index => exact some (locals.get index)
  | _ => exact none

/-- Parameter-list recursion over actual typed arguments. Indexed constructor
elimination is explicit; only type-identity local conversions are recognized. -/
def localConstructorValues {E Γ} (locals : Source.Locals E.layout Γ) :
    (ps : List Source.STy) → Source.RConvArgs E Γ ps → Option (Source.Vals E.layout ps)
  | [], args => by cases args; exact some .nil
  | τ::ps, args => by
    cases args with
    | @cons σ _ _ expr conversion rest =>
      exact if same : σ=τ then
        (localConstructorValue locals expr).bind (fun value =>
          (localConstructorValues locals ps rest).map (fun values => .cons (same ▸ value) values))
      else none

theorem localConstructorValue_run {E Γ τ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (expr : Source.RExpr E Γ τ) (value : Source.Val E.layout τ)
    (step : localConstructorValue s.1 expr=some value) :
    (Source.evalE G F (n+1) expr).run s=(.ok (.val value),s) := by
  cases expr with
  | «local» index => cases step; rfl
  | _ => cases step

theorem localConstructorValue_valid {E Γ τ} (H : Source.HeapTy) (locals : Source.Locals E.layout Γ)
    (expr : Source.RExpr E Γ τ) (value : Source.Val E.layout τ)
    (step : localConstructorValue locals expr=some value) (ok : Source.LocalsOK E H locals) : value.RefOK E H := by
  cases expr with
  | «local» index => cases step; exact Source.LocalsOK.get locals index ok
  | _ => cases step

/-- Every successful checked extraction is valid against the ACTUAL old locals
heap typing. No returned-value/ref-coverage law is supplied as a premise. -/
theorem localConstructorValues_valid {E Γ} (H : Source.HeapTy) (locals : Source.Locals E.layout Γ)
    (ok : Source.LocalsOK E H locals) (ps : List Source.STy) (args : Source.RConvArgs E Γ ps)
    (values : Source.Vals E.layout ps) (step : localConstructorValues locals ps args=some values) :
    Source.RValsOK E H values.toR := by
  induction ps with
  | nil => cases args; cases step; trivial
  | cons τ ps ih =>
    cases args with
    | @cons σ _ _ expr conversion rest =>
      dsimp only [localConstructorValues] at step
      split at step
      · rename_i same
        subst σ
        obtain ⟨head,one,tail⟩ := Option.bind_eq_some_iff.mp step
        obtain ⟨vs,ready,same⟩ := Option.map_eq_some_iff.mp tail
        cases same
        exact ⟨localConstructorValue_valid H locals expr head one ok,ih rest vs ready⟩
      · cases step

theorem constructorConv_identity_run {E Γ τ} (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (value : Source.Val E.layout τ) :
    (Source.convRV F n τ (.val value)).run s=(.ok (.val value),s) := by
  unfold Source.convRV
  rw [dif_pos rfl]
  rfl

/-- Universal source-run coverage for every successfully checked local list.
The horizon is derived from the ACTUAL list length, never a new cap. -/
theorem localConstructorValues_run {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (ps : List Source.STy) (args : Source.RConvArgs E Γ ps)
    (values : Source.Vals E.layout ps) (step : localConstructorValues s.1 ps args=some values) :
    (Source.evalConvArgs G F (n+ps.length+1) args).run s=(.ok values,s) := by
  induction ps with
  | nil => cases args; cases step; rfl
  | cons τ ps ih =>
    cases args with
    | @cons σ _ _ expr conversion rest =>
      dsimp only [localConstructorValues] at step
      split at step
      · rename_i same
        subst σ
        obtain ⟨head,one,tail⟩ := Option.bind_eq_some_iff.mp step
        obtain ⟨vs,ready,same⟩ := Option.map_eq_some_iff.mp tail
        cases same
        have headRun := localConstructorValue_run G F (n+ps.length) s expr head one
        have tailRun := ih rest vs ready
        change (Source.evalConvArgs G F ((n+ps.length+1)+1) (.cons expr conversion rest)).run s= _
        rw [Source.evalConvArgs,Source.Hoare.run_bind,headRun]
        simp only []
        rw [Source.Hoare.run_bind,constructorConv_identity_run]
        simp only []
        rw [Source.Hoare.run_bind]
        change (do
          let tail ← Source.evalConvArgs G F (n+ps.length+1) rest
          pure (Source.Vals.cons head tail)).run s = _
        rw [Source.Hoare.run_bind,tailRun]
        rfl
      · cases step

end Solidity.Yul.Views
