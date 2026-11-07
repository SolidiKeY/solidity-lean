import Solidity.Frontend.Checked.Prec
import Solidity.Yul.BlockTyping
import Solidity.Yul.DeclarationScope

/-!
# Concrete closed-root syntax certificate

This composes original-source shape, complete declaration traversal, placement
and the constructed closed-root typing judgement. It deliberately makes NO
admission claim: outside-Solidity namespace provenance, actual solc externalReferences at each
occurrence (even one that also names a Yul parameter), flags/memory safety,
tier/effect policy and intrinsic statement extraction remain obligations.
The external-reference context is empty; open Solidity bindings are unsupported.
-/
namespace Solidity.Yul.ClosedSyntax
open Solidity.Source (Syn)
open Solidity.Frontend.Checked

def rootEnv : BlockTyping.Env [] 0 := ⟨[], []⟩
def rootControl : Control := ⟨false, false⟩

structure Checked (outside : List String) (body : Syn (.list .yulStmt)) where
  shape : body.prec = true
  finalNames : List String
  declarations : DeclarationScope.BlockD outside [] body finalNames
  placement : Placement.Derivation Placement.rootContext body
  typing : BlockTyping.BlockD rootEnv rootControl body

inductive Error where
  | grammar | shape | declarations | placement (reason : Placement.Error) | typing
  deriving DecidableEq, Repr

def check (outside : List String) (body : Syn (.list .yulStmt)) :
    Except Error (Checked outside body) :=
  if shape : body.prec = true then
    match DeclarationScope.checkBlock outside [] body with
    | none => .error .declarations
    | some ⟨finalNames, declarations⟩ =>
      match Placement.checkBlock body with
      | .error reason => .error (.placement reason)
      | .ok placement =>
        match BlockTyping.checkBlock rootEnv rootControl body with
        | none => .error .typing
        | some typing => .ok ⟨shape, finalNames, declarations, placement, typing⟩
  else .error .shape

/-- Final concrete static composition, with empty initial Yul local/function
tables, not arbitrary incoherent caller tables. Outside Solidity names retain
their explicit real provenance obligation. This does not certify solc occurrence
attachment: reading an own Yul parameter named after a Solidity local can still
be refused6578 by the pinned compiler. No policy/execution theorem follows. -/
theorem Checked.complete {outside body} (p : Checked outside body) :
    check outside body = .ok p := by
  cases p with
  | mk shape finalNames declarations placement typing =>
      unfold check
      rw [dif_pos shape, declarations.complete]
      change (match Placement.check Placement.rootContext body with
        | .error reason => .error (.placement reason)
        | .ok dp => match BlockTyping.checkBlock rootEnv rootControl body with
          | none => .error .typing
          | some dt => .ok ⟨shape, finalNames, declarations, dp, dt⟩ : Except Error (Checked outside body)) = _
      rw [placement.complete, typing.complete]

/-- At fixed original syntax and supplied outside names, completeness
determines the whole certificate. This does not prove namespace provenance. -/
theorem Checked.unique {outside body} (first second : Checked outside body) :
    first = second := by
  exact Except.ok.inj (first.complete.symm.trans second.complete)

/-- Final declaration names are fixed by the original syntax and outside names,
rather than being an independent choice made by the certificate supplier. -/
theorem Checked.finalNames_unique {outside body} (first second : Checked outside body) :
    first.finalNames = second.finalNames := by
  exact congrArg Checked.finalNames (Except.ok.inj (first.complete.symm.trans second.complete))

theorem check_iff (outside : List String) (body : Syn (.list .yulStmt)) :
    (check outside body).toOption.isSome = true ↔ Nonempty (Checked outside body) := by
  constructor
  · intro h
    cases hc : check outside body with
    | error reason => simp only [hc, Except.toOption, Option.isSome] at h; cases h
    | ok p => exact ⟨p⟩
  · rintro ⟨p⟩
    rw [p.complete]
    rfl

end Solidity.Yul.ClosedSyntax
