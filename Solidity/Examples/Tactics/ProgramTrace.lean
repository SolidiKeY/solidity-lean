import Solidity.Tools.ProgramTrace
import Solidity.Calculus.Surface
import Solidity.Examples.Chains.Storage

/-! Regression checks for the document API: separate captures, arbitrary
parameters, exact read continuations, bounded failure and kernel submission.
These inspect the actual generated pairs, not just the printed labels. -/

set_option hygiene false

namespace Solidity.Examples.Tactics.ProgramTrace

open Lean Elab Command Meta Solidity.ProgramTrace
open scoped Solidity.Scoped
local instance : InContract := ⟨StandardExample⟩

/-- info: \begin{aligned}
&[\texttt{alice.age = 0;}]\mathit{true} \\
&\overset{\mathsf{storageFieldWriteSave}}{\rightsquigarrow}\ \{\mathit{storage} \mathrel{:=} \mathit{save}(\mathit{storage}, \mathit{alice}.\mathit{age}, 0)\}\mathit{true}
\end{aligned} -/
#guard_msgs in
#latex_program (past := false) dl!{ [ alice.age = 0; ] true }

run_elab do
  let first ← Term.elabTerm (← `(dl!{ [ alice.account.balance = 10; ] true })) none
  let trace ← generate first false
  let captures := trace.steps.filter (·.rule.startsWith "capture")
  unless captures.map (·.rule) == #["captureStorageFieldValue", "captureStorageFieldReceiver"] do
    throwError "field captures were bundled or reordered"
  unless trace.steps[0]!.line != trace.steps[1]!.line do
    throwError "capture refinement did not introduce distinct intermediate formulas"
  let _ ← trace.check

section
local instance : InContract := ⟨TestSuite⟩

run_elab do
  let first ← Term.elabTerm (← `(dl!{ ∀ uint i; [ basketA.items[i] = i; ] true })) none
  let trace ← generate first false
  unless (trace.steps.filter (·.rule.startsWith "capture")).map (·.rule) ==
      #["captureValue", "captureStorageReceiver", "captureStorageIndex"] do
    throwError "indexed captures were bundled or reordered"
  let _ ← trace.check

run_elab do
  let first ← Term.elabTerm (← `(dl!{ [ Basket memory b; b.items[0] = 7; ] true })) none
  let trace ← generate first false
  unless (trace.steps.filter (·.rule.startsWith "capture")).map (·.rule) ==
      #["captureMemoryValue", "captureMemoryReceiver", "captureMemoryIndex"] do
    throwError "memory captures were bundled or reordered"
  let _ ← trace.check
end

run_elab do
  for input in #[← `(dl!{ true → [ alice.account.balance = 10; ] true }),
      ← `(dl!{ [ if (true) { alice.account.balance = 10; } else { alice.age = 1; }; ] true })] do
    let first ← Term.elabTerm input none
    let trace ← generate first false
    unless (trace.steps.filter (·.rule == "captureStorageFieldValue")).size == 1 do
      throwError "capture under a precondition or branch was skipped"
    let _ ← trace.check

run_elab do
  let terminal ← Term.elabTerm (← `(dl!{ true })) none
  let _ ← generate terminal true 0 0
  let pair ← Term.elabTerm (← `(dl!{ { storage := save(storage, alice.age, 1) }
    { storage := save(storage, alice.age, 2) } true })) none
  let terminal ← Term.elabTerm (← `(dl!{ true })) none
  let precondition ← mkAppM ``Fml.imp #[terminal, pair]
  for first in #[pair, precondition] do
    let trace ← generate first true 0 1
    unless trace.steps.map (·.rule) == #["sequentialToParallel2", "shadowedStorageUpdate"] do
      throwError "composition bundled shadow removal or exceeded an exact budget: {trace.steps.map (·.rule)}\n{← Latex.exprLatex first}"
    let _ ← trace.check

run_elab do
  let first ← Term.elabTerm (← `(dl!{ ∀ uint v;
    { storage := save(storage, alice.age, 42) } [ v = alice.age; ] v == 42 })) none
  let trace ← (← generate first).continueWith #[`findOnSave]
  unless trace.steps.back!.rule == "findOnSave" do throwError "read continuation was omitted"
  let checked ← trace.check
  let json ← trace.toJson checked
  unless (json.getObjValAs? String "relation").toOption == some "Fml.Leads" do
    throwError "JSON lost its semantic boundary"
  unless (json.getObjValAs? (Array Json) "steps").toOption.map (·.size) == some trace.steps.size do
    throwError "JSON dropped a checked step"

/-- error: read law 1/1 (findOnSave) does not apply; applicable requested laws: []
current endpoint:
\{\mathit{storage} \mathrel{:=} \mathit{save}(\mathit{storage}, \mathit{alice}.\mathit{age}, 0)\}\mathit{true} -/
#guard_msgs in
#latex_program reads [findOnSave] dl!{ [ alice.age = 0; ] true }

/-- error: elementary program trace exceeded 0 steps -/
#guard_msgs in
run_elab do
  let first ← Term.elabTerm (← `(dl!{ [ alice.age = 0; ] true })) none
  let _ ← generate first false 0

section
variable (m : Modality) (φ : Post StandardExample [])

/-- info: \begin{aligned}
&\langle[\texttt{alice.age = 0;}]\rangle \varphi \\
&\overset{\mathsf{storageFieldWriteSave}}{\rightsquigarrow}\ \{\mathit{storage} \mathrel{:=} \mathit{save}(\mathit{storage}, \mathit{alice}.\mathit{age}, 0)\}\varphi
\end{aligned} -/
#guard_msgs in
#latex_program (past := false) dl![m]{ ⟨[ alice.age = 0; ]⟩ φ }
end

-- A theorem's parameters are retained; its concrete setup is not discarded.
-- File output and JSON are exercised by the script-level smoke check.
run_elab do
  let info ← getConstInfo ``Solidity.Examples.Chains.Storage.AgeWrite.chain
  forallTelescope info.type fun params body => do
    let some (first, _) ← Latex.chainSteps? body | throwError "expected a chain"
    let trace ← generate first
    let _ ← trace.check params info.levelParams

end Solidity.Examples.Tactics.ProgramTrace
