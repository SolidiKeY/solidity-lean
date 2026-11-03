import Solidity.Yul.BlockTyping
import Solidity.Yul.DeclarationParse

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

structure Parsed (outside : List String) (src : Bytes) where
  parsed : AssemblyParse src
  checked : Checked outside parsed.body

def parse (outside : List String) (src : Bytes) : Except Error (Parsed outside src) :=
  match parseAssembly src with
  | none => .error .grammar
  | some parsed => (check outside parsed.body).map (fun checked => ⟨parsed, checked⟩)

theorem Parsed.complete {outside src} (p : Parsed outside src) :
    parse outside src = .ok p := by
  cases p with
  | mk parsed checked =>
      unfold parse
      rw [parsed.complete]
      change (check outside parsed.body).map
        (fun d => (⟨parsed, d⟩ : Parsed outside src)) = _
      rw [checked.complete]
      rfl

theorem parse_iff (outside : List String) (src : Bytes) :
    (parse outside src).toOption.isSome = true ↔ Nonempty (Parsed outside src) := by
  constructor
  · intro h
    cases hc : parse outside src with
    | error reason => simp only [hc, Except.toOption, Option.isSome] at h; cases h
    | ok p => exact ⟨p⟩
  · rintro ⟨p⟩
    rw [p.complete]
    rfl

end Solidity.Yul.ClosedSyntax
