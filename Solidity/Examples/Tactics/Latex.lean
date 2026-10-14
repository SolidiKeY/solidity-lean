import Solidity.Tools.Latex
import Solidity.Calculus.Surface

/-! LaTeX export of scoped formulas and kernel-checked derivations. -/

namespace Solidity.Examples.Tactics.Latex

open scoped Solidity.Scoped
local instance : InContract := ⟨StandardExample⟩

section
variable (m : Modality) (φ : Post StandardExample [])

/-- `alice.age = 0;` becomes the storage update, before the remaining program. -/
theorem write : dl![m]{ ⟨[ alice.age = 0; alice.age = 1; ]⟩ φ }
    ~[storageFieldWriteSave]~>
      dl![m]{ { storage := save(storage, alice.age, 0) } ⟨[ alice.age = 1; ]⟩ φ } := by
  sol_chain

/-- info: \langle [ alice.age = 0 ; ] \rangle \varphi -/
#guard_msgs in #latex dl![m]{ ⟨[ alice.age = 0; ]⟩ φ }
/-- info: \{ storage := save ( storage , alice.age , 0 ) \} \langle [ alice.age = 1 ; ] \rangle \varphi -/
#guard_msgs in
#latex dl![m]{ { storage := save(storage, alice.age, 0) } ⟨[ alice.age = 1; ]⟩ φ }
/-- info: \begin{aligned} &\langle [ alice.age = 0 ; alice.age = 1 ; ] \rangle \varphi \\  &\overset{\mathrm{storageFieldWriteSave}}{\rightsquigarrow} \{ storage := save ( storage , alice.age , 0 ) \} \langle [ alice.age = 1 ; ] \rangle \varphi \end{aligned} -/
#guard_msgs in
#latex_decl write

end

/-- info: [ alice.age = 0 ; ] \mathit{true} -/
#guard_msgs in #latex dl!{ [ alice.age = 0; ] true }
/-- info: \{ storage := save ( storage , alice.age , 0 ) \} ( \mathit{true} \land \mathit{true} ) -/
#guard_msgs in #latex dl!{ { storage := save(storage, alice.age, 0) } (true ∧ true) }
/-- info: \forall n : \mathbb{N},\ n = n -/
#guard_msgs in #latex (∀ n : Nat, n = n)

/-- `#latex_decl` retains assumptions instead of presenting a conditional
derivation as unconditional. -/
theorem conditional (_h : 1 = 1) : 2 = 2 := by rfl
/-- info: (1 = 1) \implies 2 = 2 -/
#guard_msgs in #latex_decl conditional

/-- info: \forall uint x ; \langle x = 0 ; \rangle x = 0 -/
#guard_msgs in #latex dl!{ ∀ uint x; ⟨ x = 0; ⟩ x == 0 }

/-- info: \models [ alice.age = 0 ; ] \mathit{true} -/
#guard_msgs in #latex (Valid dl!{ [ alice.age = 0; ] true })

/-- info: \Longrightarrow [ alice.age = 0 ; ] \mathit{true} -/
#guard_msgs in #latex (⊢ dl!{ [ alice.age = 0; ] true })

-- Quoted identifiers must not become TeX comments or control sequences.
/-- info: "\\varphi{}x\\%\\&\\#\\$\\_" -/
#guard_msgs in #eval Solidity.Latex.identLatex "φx%&#$_"

/-- info: "x_{12}" -/
#guard_msgs in #eval Solidity.Latex.identLatex "x₁₂"

/-- error: LaTeX export needs a notation printer for this Lean escape -/
#guard_msgs in
run_cmd Lean.Elab.Command.runTermElabM fun _ => do
  let _ ← Solidity.Latex.syntaxLatex (← `(dl_fml| ‹True›))
  pure ()

end Solidity.Examples.Tactics.Latex
