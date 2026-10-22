import Solidity.Tools.LatexSolkey
import Solidity.Calculus.Surface
import Solidity.Examples.Chains.FixedLength

/-! LaTeX export of scoped formulas, judgements, kernel-checked chains and
generated derivations, in both backends (`docs/latex.md`).  The solc fixture
copies a fixed-length array into a dynamic one: its line holds the typed
adapter `Op1.fixedCopy`, which the `macros` backend prints as its source
alone, as KeY does.  Its derivations are pinned up to where the strategy
stops (`past := false`); the worked chain of the same copy
(`Examples/Chains/FixedLength.lean`) is pinned whole, to `true`. -/

solc_import "../../../tests/solc/FixedLength.ast.json" hash 0x4b6286ff2769dc0f as Solc.Latex.C

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

/-- A read resolved past the program by a law: its side line names the
instance and the law's side conditions. -/
theorem readBack (ψ : Post StandardExample [.val .uint]) :
    dl![m]{ { storage := save(storage, alice.age, 42) } ⟨[ v = alice.age; ]⟩ ψ }
    ~*> dl![m]{ { storage := save(storage, alice.age, 42) } { v := find(storage, alice.age) } ψ }
    ~[sequentialToParallel]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖
        v := find(save(storage, alice.age, 42), alice.age) } ψ }
    ~[findOnSave]~> dl![m]{ { storage := save(storage, alice.age, 42) ‖ v := 42 } ψ } := by
  sol_chain

/-- info: \langle[\texttt{alice.age = 0;}]\rangle \varphi -/
#guard_msgs in
#latex dl![m]{ ⟨[ alice.age = 0; ]⟩ φ }
/-- info: \begin{aligned}
&\langle[\texttt{alice.age = 0; alice.age = 1;}]\rangle \varphi \\
&\overset{\mathsf{storageFieldWriteSave}}{\rightsquigarrow}\ \{\mathit{storage} \mathrel{:=} \mathit{save}(\mathit{storage}, \mathit{alice}.\mathit{age}, 0)\}\langle[\texttt{alice.age = 1;}]\rangle \varphi
\end{aligned} -/
#guard_msgs in
#latex_decl write
/-- info: \begin{aligned}
&\dlbothf{alice.age = 0; alice.age = 1;}{\varphi} \\
&\rightsquigarrow\ \{\storage \upd \save(\storage, \pField{\mathit{alice}}{\mathit{age}}, 0)\}\dlbothf{alice.age = 1;}{\varphi}
\end{aligned} -/
#guard_msgs in
#latex_decl (macros := true) write
/-- info: \begin{aligned}
&\langle[\texttt{alice.age = 0; alice.age = 1;}]\rangle \varphi \\
&\rightsquigarrow\ \{\mathit{storage} \mathrel{:=} \mathit{save}(\mathit{storage}, \mathit{alice}.\mathit{age}, 0)\}\langle[\texttt{alice.age = 1;}]\rangle \varphi && (\mathsf{storageFieldWriteSave})
\end{aligned} -/
#guard_msgs in
#latex_decl (labels := tag) write
/-- info: \begin{aligned}
&\forall \mathsf{uint}\,\mathit{v};\ \{\storage \upd \save(\storage, \pField{\mathit{alice}}{\mathit{age}}, 42)\}\dlbothf{v = alice.age;}{\psi} \\
&\rightsquigarrow^{*}\ \forall \mathsf{uint}\,\mathit{v};\ \{\storage \upd \save(\storage, \pField{\mathit{alice}}{\mathit{age}}, 42)\}\{\mathit{v} \upd \TFind{\intS}(\storage, \pField{\mathit{alice}}{\mathit{age}})\}\psi \\
&\rightsquigarrow\ \forall \mathsf{uint}\,\mathit{v};\ \{\storage \upd \save(\storage, \pField{\mathit{alice}}{\mathit{age}}, 42) \parallel \\
&\qquad \mathit{v} \upd \TFind{\intS}(\save(\storage, \pField{\mathit{alice}}{\mathit{age}}, 42), \pField{\mathit{alice}}{\mathit{age}})\}\psi \\
&\TFind{\intS}(\save(\storage, \pField{\mathit{alice}}{\mathit{age}}, 42), \pField{\mathit{alice}}{\mathit{age}}) \rightsquigarrow 42\qquad (\mathit{hasSeg}(\pField{\mathit{alice}}{\mathit{age}})) \\
&\rightsquigarrow\ \forall \mathsf{uint}\,\mathit{v};\ \{\storage \upd \save(\storage, \pField{\mathit{alice}}{\mathit{age}}, 42) \parallel \mathit{v} \upd 42\}\psi
\end{aligned} -/
#guard_msgs in
#latex_decl (macros := true) readBack

end

/-- info: [\texttt{alice.age = 0;}]\mathit{true} -/
#guard_msgs in
#latex dl!{ [ alice.age = 0; ] true }
/-- info: \dlboxf{alice.age = 0;}{\mathit{true}} -/
#guard_msgs in
#latex_expr (macros := true) dl!{ [ alice.age = 0; ] true }
/-- info: \{\mathit{storage} \mathrel{:=} \mathit{save}(\mathit{storage}, \mathit{alice}.\mathit{age}, 0)\}(\mathit{true} \land \mathit{true}) -/
#guard_msgs in
#latex dl!{ { storage := save(storage, alice.age, 0) } (true ∧ true) }
/-- info: \forall n : \mathbb{N},\ n = n -/
#guard_msgs in
#latex (∀ n : Nat, n = n)

/-- `#latex_decl` retains assumptions instead of presenting a conditional
derivation as unconditional. -/
theorem conditional (_h : 1 = 1) : 2 = 2 := by rfl
/-- info: (1 = 1) \implies 2 = 2 -/
#guard_msgs in
#latex_decl conditional

/-- info: \forall \mathsf{uint}\,\mathit{x};\ \langle \texttt{x = 0;}\rangle \mathit{x} = 0 -/
#guard_msgs in
#latex dl!{ ∀ uint x; ⟨ x = 0; ⟩ x == 0 }
/-- info: \forall \mathsf{uint}\,\mathit{x};\ \dlf{x = 0;}{(\mathit{x} = 0)} -/
#guard_msgs in
#latex_expr (macros := true) dl!{ ∀ uint x; ⟨ x = 0; ⟩ x == 0 }
/-- info: \models [\texttt{alice.age = 0;}]\mathit{true} -/
#guard_msgs in
#latex (Fml.Valid dl!{ [ alice.age = 0; ] true })
/-- info: \Longrightarrow [\texttt{alice.age = 0;}]\mathit{true} -/
#guard_msgs in
#latex (⊢ dl!{ [ alice.age = 0; ] true })

-- A line longer than the width breaks onto `\qquad` rows.
/-- info: \begin{aligned}
&\{\mathit{storage} \mathrel{:=} \mathit{save}(\mathit{save}(\mathit{storage}, \mathit{alice}.\mathit{age}, 1), \mathit{bob}.\mathit{age}, 2)\} \\
&\qquad \langle \texttt{alice.age = 3;}\rangle \mathit{find}_{\mathsf{int}}(\mathit{storage}, \mathit{alice}.\mathit{age}) = 3
\end{aligned} -/
#guard_msgs in
#latex_expr (width := 60)
  dl!{ { storage := save(save(storage, alice.age, 1), bob.age, 2) } ⟨ alice.age = 3; ⟩ alice.age == 3 }
/-- info: \begin{aligned}
&\{\storage \upd \save(\save(\storage, \pField{\mathit{alice}}{\mathit{age}}, 1), \pField{\mathit{bob}}{\mathit{age}}, \\
&\qquad 2)\}\dlf{alice.age = 3;}{(\TFind{\intS}(\storage, \pField{\mathit{alice}}{\mathit{age}}) = 3)}
\end{aligned} -/
#guard_msgs in
#latex_expr (macros := true) (width := 60)
  dl!{ { storage := save(save(storage, alice.age, 1), bob.age, 2) } ⟨ alice.age = 3; ⟩ alice.age == 3 }

/-- info: \begin{aligned}
&\dlboxf{alice.age = 42; uint v = alice.age;}{(\mathit{v} = 42)} \\
&\rightsquigarrow\ \{\storage \upd \save(\storage, \pField{\mathit{alice}}{\mathit{age}}, 42)\}\dlboxf{uint v = alice.age;}{(\mathit{v} = 42)} && (\ruleName{storageFieldWriteSave}) \\
&\rightsquigarrow^{*}\ \{\storage \upd \save(\storage, \pField{\mathit{alice}}{\mathit{age}}, 42)\}\{\mathit{v} \upd \TFind{\intS}(\storage, \pField{\mathit{alice}}{\mathit{age}})\}\mathit{v} = 42
\end{aligned} -/
#guard_msgs in
#latex_derivation (macros := true) (past := false) (labels := tag)
  dl!{ [ alice.age = 42; uint v = alice.age; ] v == 42 }

-- Regressions: code that `\lstinline` cannot take (`&&`), and a decrement's `−`.
/-- info: \forall \mathsf{bool}\,\mathit{b};\ \langle \texttt{b = b \&\& true;}\rangle \mathit{true} -/
#guard_msgs in
#latex_expr (macros := true) dl!{ ∀ bool b; ⟨ b = b && true; ⟩ true }
/-- info: \forall \mathsf{uint}\,\mathit{x};\ \dlboxf{x--;}{\mathit{true}} -/
#guard_msgs in
#latex_expr (macros := true) dl!{ ∀ uint x; [ x−−; ] true }

-- `fixedCopy`: written in the plain backend, its source alone in the macros one.
/-- info: \mathit{wt}(\mathit{storage}) \rightarrow \langle \texttt{uint x; d2 = d1; x = d2.length; assert(x == 9);}\rangle \mathit{true} -/
#guard_msgs in
#latex_obligation Solc.Latex.C.f
/-- info: \wellformed{\storage} \rightarrow \dlf{uint x; d2 = d1; x = d2.length; assert(x == 9);}{\mathit{true}} -/
#guard_msgs in
#latex_obligation (macros := true) Solc.Latex.C.f
/-- info: \begin{aligned}
&\Gamma = \{\mathit{wt}(\mathit{storage})\}\\[4pt]
&\langle \texttt{uint x; d2 = d1; x = d2.length; assert(x == 9);}\rangle \mathit{true} \\
&\rightsquigarrow^{*}\ \{\mathit{x} \mathrel{:=} 0\}\langle \texttt{d2 = d1; x = d2.length; assert(x == 9);}\rangle \mathit{true} \\
&\overset{\mathsf{storageFixedCopySave}}{\rightsquigarrow}\ \{\mathit{x} \mathrel{:=} 0\}\{\mathit{storage} \mathrel{:=} \mathit{save}(\mathit{storage}, \mathit{d2}, \mathit{fixedCopy}(\mathit{find}_{\mathsf{Struct}}(\mathit{storage}, \mathit{d1})))\} \\
&\qquad \langle \texttt{x = d2.length; assert(x == 9);}\rangle \mathit{true} \\
&\overset{\mathsf{storageLengthRead}}{\rightsquigarrow}\ \{\mathit{x} \mathrel{:=} 0\}\{\mathit{storage} \mathrel{:=} \mathit{save}(\mathit{storage}, \mathit{d2}, \mathit{fixedCopy}(\mathit{find}_{\mathsf{Struct}}(\mathit{storage}, \mathit{d1})))\} \\
&\qquad \{\mathit{x} \mathrel{:=} \mathit{find}_{\mathsf{int}}(\mathit{storage}, \mathit{d2}.\mathit{length})\}\langle \texttt{assert(x == 9);}\rangle \mathit{true} \\
&\rightsquigarrow^{*}\ \{\mathit{x} \mathrel{:=} 0\}\{\mathit{storage} \mathrel{:=} \mathit{save}(\mathit{storage}, \mathit{d2}, \mathit{fixedCopy}(\mathit{find}_{\mathsf{Struct}}(\mathit{storage}, \mathit{d1})))\} \\
&\qquad \{\mathit{x} \mathrel{:=} \mathit{find}_{\mathsf{int}}(\mathit{storage}, \mathit{d2}.\mathit{length})\}\{\mathit{se1} \mathrel{:=} \mathit{x} = 9\}((\mathit{se1} = \mathit{true} \rightarrow \mathit{true}) \land \mathit{se1} = \mathit{true})
\end{aligned} -/
#guard_msgs in
#latex_derivation (past := false) Solc.Latex.C.f
/-- info: \begin{aligned}
&\Gamma = \{\wellformed{\storage}\}\\[4pt]
&\dlf{uint x; d2 = d1; x = d2.length; assert(x == 9);}{\mathit{true}} \\
&\rightsquigarrow^{*}\ \{\mathit{x} \upd 0\}\dlf{d2 = d1; x = d2.length; assert(x == 9);}{\mathit{true}} \\
&\rightsquigarrow\ \{\mathit{x} \upd 0\}\{\storage \upd \save(\storage, \mathit{d2}, \TFind{\Struct}(\storage, \mathit{d1}))\} \\
&\qquad \dlf{x = d2.length; assert(x == 9);}{\mathit{true}} \\
&\rightsquigarrow\ \{\mathit{x} \upd 0\}\{\storage \upd \save(\storage, \mathit{d2}, \TFind{\Struct}(\storage, \mathit{d1}))\} \\
&\qquad \{\mathit{x} \upd \TFind{\intS}(\storage, \pField{\mathit{d2}}{\lengthField})\}\dlf{assert(x == 9);}{\mathit{true}} \\
&\rightsquigarrow^{*}\ \{\mathit{x} \upd 0\}\{\storage \upd \save(\storage, \mathit{d2}, \TFind{\Struct}(\storage, \mathit{d1}))\} \\
&\qquad \{\mathit{x} \upd \TFind{\intS}(\storage, \pField{\mathit{d2}}{\lengthField})\}\{\mathit{se1} \upd \mathit{x} = 9\}((\mathit{se1} = \mathit{true} \rightarrow \mathit{true}) \land \mathit{se1} = \mathit{true})
\end{aligned} -/
#guard_msgs in
#latex_derivation (macros := true) (past := false) Solc.Latex.C.f
/-- info: \begin{aligned}
&\wellformed{\storage} \rightarrow \dlf{uint x; d2 = d1; x = d2.length; assert(x == 9);}{\mathit{true}} \\
&\rightsquigarrow^{*}\ \wellformed{\storage} \rightarrow \{\mathit{x} \upd 0\}\dlf{d2 = d1; x = d2.length; assert(x == 9);}{\mathit{true}} \\
&\overset{\ruleName{storageFixedCopySave}}{\rightsquigarrow}\ \wellformed{\storage} \rightarrow \{\mathit{x} \upd 0\}\{\storage \upd \save(\storage, \mathit{d2}, \TFind{\Struct}(\storage, \mathit{d1}))\} \\
&\qquad \dlf{x = d2.length; assert(x == 9);}{\mathit{true}} \\
&\overset{\ruleName{storageLengthRead}}{\rightsquigarrow}\ \wellformed{\storage} \rightarrow \{\mathit{x} \upd 0\}\{\storage \upd \save(\storage, \mathit{d2}, \TFind{\Struct}(\storage, \mathit{d1}))\} \\
&\qquad \{\mathit{x} \upd \TFind{\intS}(\storage, \pField{\mathit{d2}}{\lengthField})\}\dlf{assert(x == 9);}{\mathit{true}} \\
&\overset{\ruleName{assertConditionCapture}}{\rightsquigarrow}\ \wellformed{\storage} \rightarrow \{\mathit{x} \upd 0\}\{\storage \upd \save(\storage, \mathit{d2}, \TFind{\Struct}(\storage, \mathit{d1}))\} \\
&\qquad \{\mathit{x} \upd \TFind{\intS}(\storage, \pField{\mathit{d2}}{\lengthField})\}\dlf{bool se1 = x == 9; assert(se1);}{\mathit{true}} \\
&\overset{\ruleName{localValueDeclInitDrop}}{\rightsquigarrow}\ \wellformed{\storage} \rightarrow \{\mathit{x} \upd 0\}\{\storage \upd \save(\storage, \mathit{d2}, \TFind{\Struct}(\storage, \mathit{d1}))\} \\
&\qquad \{\mathit{x} \upd \TFind{\intS}(\storage, \pField{\mathit{d2}}{\lengthField})\}\dlf{se1 = x == 9; assert(se1);}{\mathit{true}} \\
&\overset{\ruleName{binopAssignment}}{\rightsquigarrow}\ \wellformed{\storage} \rightarrow \{\mathit{x} \upd 0\}\{\storage \upd \save(\storage, \mathit{d2}, \TFind{\Struct}(\storage, \mathit{d1}))\} \\
&\qquad \{\mathit{x} \upd \TFind{\intS}(\storage, \pField{\mathit{d2}}{\lengthField})\}\{\mathit{se1} \upd \mathit{x} = 9\}\dlf{assert(se1);}{\mathit{true}} \\
&\overset{\ruleName{assertSimple}}{\rightsquigarrow}\ \wellformed{\storage} \rightarrow \{\mathit{x} \upd 0\}\{\storage \upd \save(\storage, \mathit{d2}, \TFind{\Struct}(\storage, \mathit{d1}))\} \\
&\qquad \{\mathit{x} \upd \TFind{\intS}(\storage, \pField{\mathit{d2}}{\lengthField})\}\{\mathit{se1} \upd \mathit{x} = 9\}((\mathit{se1} = \mathit{true} \rightarrow \mathit{true}) \land \mathit{se1} = \mathit{true})
\end{aligned} -/
#guard_msgs in
#latex_derivation (macros := true) (past := false) (labels := over) (collapse := [valueDeclSkip])
  (premise := false) Solc.Latex.C.f

-- Quoted identifiers must not become TeX comments or control sequences.
/-- info: "\\varphi{}x\\%\\&\\#\\$\\_" -/
#guard_msgs in
#eval Solidity.Latex.identLatex "φx%&#$_"
/-- info: "x_{12}" -/
#guard_msgs in
#eval Solidity.Latex.identLatex "x₁₂"

-- Every constructor of the signature, the terms and the updates has a spelling.
-- The worked chain of a fixed array copied to a dynamic one, kernel-checked,
-- in the macros backend: the side line is `lenOnSaveFixedCopy`'s instance.
/--
info: \begin{aligned}
&\dlf{d2 = d1; x = d2.length;}{(\mathit{x} = 9)} \\
&\rightsquigarrow\ \{\storage \upd \save(\storage, \mathit{d2}, \TFind{\Struct}(\storage, \mathit{d1}))\}\dlf{x = d2.length;}{(\mathit{x} = 9)} \\
&\rightsquigarrow\ \{\storage \upd \save(\storage, \mathit{d2}, \TFind{\Struct}(\storage, \mathit{d1}))\}\{\mathit{x} \upd \TFind{\intS}(\storage, \pField{\mathit{d2}}{\lengthField})\}\mathit{x} = 9 \\
&\rightsquigarrow\ \{\storage \upd \save(\storage, \mathit{d2}, \TFind{\Struct}(\storage, \mathit{d1})) \parallel \\
&\qquad \mathit{x} \upd \TFind{\intS}(\save(\storage, \mathit{d2}, \TFind{\Struct}(\storage, \mathit{d1})), \pField{\mathit{d2}}{\lengthField})\}\mathit{x} = 9 \\
&\TFind{\intS}(\save(\storage, \mathit{d2}, \TFind{\Struct}(\storage, \mathit{d1})), \pField{\mathit{d2}}{\lengthField}) \rightsquigarrow 9 \\
&\rightsquigarrow\ \{\storage \upd \save(\storage, \mathit{d2}, \TFind{\Struct}(\storage, \mathit{d1})) \parallel \mathit{x} \upd 9\}\mathit{x} = 9 \\
&\rightsquigarrow\ 9 = 9 \\
&\rightsquigarrow\ \mathit{true}
\end{aligned}
-/
#guard_msgs in
#latex_decl (macros := true) Solidity.Examples.Chains.FixedLength.CopyLength.chain

/-- info: [] -/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do Lean.logInfo m!"{← Solidity.Latex.uncovered}"

-- A symbol with no spelling prints as `\mathsf{…}` and warns.
/--
warning: LaTeX export: no LaTeX spelling for Nat.succ: printed as \mathsf
---
info: \mathsf{succ}
-/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.logInfo (← Solidity.Latex.runRM {} (Solidity.Latex.symOf ``Nat.succ))

-- A link surrounds only the operator (and its sort), never its arguments.
/-- info: \hyperlink{formula:findPathRule}{\mathit{find}_{\mathsf{int}}}(\mathit{storage}, \mathit{alice}.\mathit{age}) = 42 -/
#guard_msgs in
#latex_expr (width := 300) (definitions := [(find, "formula:findPathRule")])
  dl!{ find(storage, alice.age) = 42 }

/-- info: \hyperlink{formula:findPathRule}{\TFind{\intS}}(\storage, \pField{\mathit{alice}}{\mathit{age}}) = 42 -/
#guard_msgs in
#latex_expr (macros := true) (width := 300) (definitions := [(find, "formula:findPathRule")])
  dl!{ find(storage, alice.age) = 42 }

/-- info: \hyperlink{definition:find}{\find}(\storage, \pField{\mathit{alice}}{\mathit{age}}) = 42 -/
#guard_msgs in
#latex_expr (macros := true) (sorts := false) (width := 300)
  (definitions := [(find, "definition:find")]) dl!{ find(storage, alice.age) = 42 }

section
#latex_definition_targets [(select, "formula:selectOnStoreRule")]

/-- info: \TFind{\intS}(\hyperlink{formula:selectOnStoreRule}{\TSelect{\Struct}}(\storage, \mathit{alice}), \mathit{age}) = 42 -/
#guard_msgs in
#latex_expr (macros := true) (width := 300) dl!{ find(select(storage, alice), age) = 42 }

-- An explicit empty map disables inherited links for this export.
/-- info: \TFind{\intS}(\TSelect{\Struct}(\storage, \mathit{alice}), \mathit{age}) = 42 -/
#guard_msgs in
#latex_expr (macros := true) (width := 300) (definitions := [])
  dl!{ find(select(storage, alice), age) = 42 }
end

-- Definition maps are scoped; leaving the section restores the default.
/-- info: \TFind{\intS}(\TSelect{\Struct}(\storage, \mathit{alice}), \mathit{age}) = 42 -/
#guard_msgs in
#latex_expr (macros := true) (width := 300) dl!{ find(select(storage, alice), age) = 42 }

/-- error: duplicate definition symbol find -/
#guard_msgs in
#latex_definition_targets [(find, "definition:find"), (find, "other:find")]

/-- error: definition destination must be nonempty and contain only ASCII letters, digits, :, _, ., / or - -/
#guard_msgs in
#latex_expr (definitions := [(find, "bad}target")]) dl!{ true }

set_option hygiene false in
run_elab do
  let first ← Lean.Elab.Term.elabTerm (← `(dl!{
    find(select(save(storage, alice.age, 42), alice), age) = 42 })) none
  let opts : Solidity.Latex.Options := { width := 45 }
  let linked := { opts with definitions := [("find", "def:find"), ("select", "def:select"), ("save", "def:save")] }
  let before ← Solidity.Latex.runRM opts (Solidity.Latex.fml [] first)
  let after ← Solidity.Latex.runRM linked (Solidity.Latex.fml [] first)
  unless before.width == after.width && (before.lines 45).size == (after.lines 45).size do
    throwError "definition links changed layout widths or wrapping"
  let tex := after.flat
  unless (tex.splitOn "\\hyperlink{").length == 4 do
    throwError "nested find/select/save heads were missed or linked twice"

run_elab do
  let opts : Solidity.Latex.Options := { definitions := [("find", "def:find")] }
  for ctor in [``Op2.find, ``Op2.findIn, ``Op2.sfind, ``Op2.sfindIn, ``Op2.len] do
    let text ← Solidity.Latex.runRM opts (Solidity.Latex.symOf ctor)
    unless text.startsWith "\\hyperlink{def:find}" do
      throwError "typed find variant lost its definition target"

-- These paper macros hide operator heads; links expose them without changing
-- their layout measure or the netSelect macro's always-present sort.
run_elab do
  let plain : Solidity.Latex.Options := { backend := .macros, sorts := false }
  let linked := { plain with definitions := [("select", "def:select"), ("at", "def:at"), ("atMap", "def:atMap")] }
  let arg := Solidity.Latex.Doc.ident "a"
  let before ← Solidity.Latex.runRM plain (Solidity.Latex.netSelectDoc arg)
  let after ← Solidity.Latex.runRM linked (Solidity.Latex.netSelectDoc arg)
  unless before.width == after.width && after.flat.startsWith "\\hyperlink{def:select}{\\TSelect{\\intS}}" do
    throwError "linking netSelect changed its sort or layout"
  for map in [false, true] do
    let before ← Solidity.Latex.runRM plain (Solidity.Latex.indexDoc arg arg map)
    let after ← Solidity.Latex.runRM linked (Solidity.Latex.indexDoc arg arg map)
    let target := if map then "def:atMap" else "def:at"
    unless before.width == after.width && (after.flat.splitOn ("\\hyperlink{" ++ target ++ "}")).length == 2 do
      throwError "an indexed path changed layout or lost its operator link"

/-- info: \hyperlink{def:wt}{\wellformedSym}(\storage) -/
#guard_msgs in
#latex_expr (macros := true) (definitions := [(wt, "def:wt")]) dl!{ wt(storage) }

/-- info: \forall \_n : \mathbb{N},\ \models \hyperlink{def:find}{\mathit{find}_{\mathsf{int}}}(\mathit{storage}, \mathit{alice}.\mathit{age}) = 42 -/
#guard_msgs in
#latex_expr (width := 300) (definitions := [(find, "def:find")])
  (∀ _n : Nat, Fml.Valid dl!{ find(storage, alice.age) = 42 })

section
#latex_definition_targets [(find, "def:find")]
/-- info: \forall \_n : \mathbb{N},\ \models \mathit{find}_{\mathsf{int}}(\mathit{storage}, \mathit{alice}.\mathit{age}) = 42 -/
#guard_msgs in
#latex_expr (width := 300) (definitions := [])
  (∀ _n : Nat, Fml.Valid dl!{ find(storage, alice.age) = 42 })
end

end Solidity.Examples.Tactics.Latex
