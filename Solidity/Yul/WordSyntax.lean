import Solidity.Yul.BlockExtract
import Solidity.Yul.ClosedSyntax
import Solidity.Yul.WordPolicy
import Solidity.Yul.WordCoverage

/-!
# Concrete checked-syntax to closed-word program composition

This prepares an ACTUAL intrinsic Yul Program and its interpreter profile from
the original grammar, constructed static checking, extraction and real tier-A
policy check. It is NOT Solidity assembly admission. Outside-name provenance,
solc occurrence metadata, memory-safe flags/doc comments, Source state/session,
dirty-word pipelines and compiler correspondence remain separate obligations.
In particular flags are preserved, not admitted, by the parser wrapper.
-/
namespace Solidity.Yul.WordSyntax
open Solidity.Source (Syn)
open Solidity.Frontend.Checked
open Solidity.Yul.Closed

structure Prepared (outside : List String) (body : Syn (.list .yulStmt)) where
  checkedSyntax : ClosedSyntax.Checked outside body
  policy : Policy.StmtP .A checkedSyntax.typing.code

inductive Error where
  | input (reason : ClosedSyntax.Error)
  | policy (reason : Refusal)
  deriving Repr

def prepare (outside : List String) (body : Syn (.list .yulStmt)) :
    Except Error (Prepared outside body) :=
  match ClosedSyntax.check outside body with
  | .error reason => .error (.input reason)
  | .ok checked =>
    match h : Policy.checkStmt .A checked.typing.code with
    | .error reason => .error (.policy reason)
    | .ok () => .ok ⟨checked, (Policy.stmt_iff .A checked.typing.code).mp h⟩

theorem Prepared.complete {outside body} (p : Prepared outside body) :
    prepare outside body = .ok p := by
  cases p with
  | mk checked policy =>
      unfold prepare
      rw [checked.complete]
      change (match h : Policy.checkStmt .A checked.typing.code with
        | .error reason => .error (.policy reason)
        | .ok () => .ok ⟨checked, (Policy.stmt_iff .A checked.typing.code).mp h⟩ :
        Except Error (Prepared outside body)) = _
      split
      · next reason failed =>
          have bad := failed.symm.trans ((Policy.stmt_iff .A checked.typing.code).mpr policy)
          cases bad
      · rfl

theorem prepare_iff (outside : List String) (body : Syn (.list .yulStmt)) :
    (prepare outside body).toOption.isSome = true ↔ Nonempty (Prepared outside body) := by
  constructor
  · intro h
    cases hc : prepare outside body with
    | error reason => simp only [hc, Except.toOption, Option.isSome] at h; cases h
    | ok p => exact ⟨p⟩
  · rintro ⟨p⟩
    rw [p.complete]
    rfl

/-- The interpreter profile is derived from the actual successful policy.
There is no assumed model/closure agreement or caller-success premise. -/
def Prepared.program {outside body} (p : Prepared outside body) :
    Logic.Program [] ClosedSyntax.rootControl 0 :=
  ⟨p.checkedSyntax.typing.code,
    stmt_policy_words _ (fun _ index => by cases index) p.policy⟩

def emptyModel : Logic.Model [] := ⟨.nil, True.intro⟩

def Prepared.run {outside body} (p : Prepared outside body) (fuel : Nat) :
    Option (Outcome ClosedSyntax.rootControl 0) :=
  evalStmt fuel emptyModel.environment emptyModel.words p.program.code p.program.words Fin.elim0

/-- Concrete ONE-STEP calculus composition for this ACTUAL emitted program.
No RuleExists hypothesis, dispatcher/normalizer, logical completeness or
Source/G51 composition is claimed. -/
theorem Prepared.rule_exists {outside body} (p : Prepared outside body)
    (mode : Solidity.Modality) (post : Flow ClosedSyntax.rootControl → Logic.Fml 0) :
    ∃ premise, Nonempty (Logic.Rule (.modal mode emptyModel p.program post) premise) :=
  Logic.program_rule_exists mode emptyModel p.program post

theorem Prepared.rule_sound {outside body} (p : Prepared outside body)
    (mode : Solidity.Modality) (post : Flow ClosedSyntax.rootControl → Logic.Fml 0) :
    ∃ premise : Logic.Fml 0, ∀ vars,
      (.modal mode emptyModel p.program post : Logic.Fml 0).holds vars ↔ premise.holds vars :=
  Logic.sound_program_rule_exists mode emptyModel p.program post

end Solidity.Yul.WordSyntax
