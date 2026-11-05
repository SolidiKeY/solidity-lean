import Solidity.Yul.WordRules

/-! Concrete ONE-STEP rule existence for every CLOSED word Program constructor.
This supplies one-step program/term rules, not a dispatcher/normalizer or Source/G51
composition. Program carries the actual closed interpreter word profile. -/
namespace Solidity.Yul.Logic
open Solidity.Yul.Closed
open Solidity (Modality)

theorem program_rule_exists {F c n} (mode : Modality) (model : Model F)
    (program : Program F c n) (post : Flow c → Fml n) :
    ∃ premise, Nonempty (Rule (.modal mode model program post) premise) := by
  rcases program with ⟨code,words⟩
  cases code with
  | skip => exact ⟨_,⟨.yulSkip mode model post⟩⟩
  | seq first second =>
    exact ⟨_,⟨.yulSequence mode model ⟨first,words.1⟩ ⟨second,words.2⟩ post⟩⟩
  | assign targets expression =>
    exact ⟨_,⟨.yulAssign mode model targets ⟨expression,words.2⟩ post⟩⟩
  | discard expression =>
    exact ⟨_,⟨.yulDiscard mode model ⟨expression,words⟩ post⟩⟩
  | let_ count expression body =>
    exact ⟨_,⟨.yulLet mode model ⟨expression,words.1⟩ ⟨body,words.2⟩ post⟩⟩
  | zero count body =>
    exact ⟨_,⟨.yulZero mode model count ⟨body,words⟩ post⟩⟩
  | if_ condition body =>
    exact ⟨_,⟨.yulIf mode model ⟨condition,words.1⟩ ⟨body,words.2⟩ post⟩⟩
  | switch condition arms fallback =>
    exact ⟨_,⟨.yulSwitch mode model ⟨condition,words.1⟩ arms words.2.1 ⟨fallback,words.2.2⟩ post⟩⟩
  | for_ pre condition step body =>
    exact ⟨_,⟨.yulFor mode model ⟨pre,words.1⟩ ⟨condition,words.2.1⟩
      ⟨step,words.2.2.1⟩ ⟨body,words.2.2.2⟩ post⟩⟩
  | leave => exact ⟨_,⟨.yulLeave mode model post⟩⟩
  | break_ => exact ⟨_,⟨.yulBreak mode model post⟩⟩
  | continue_ => exact ⟨_,⟨.yulContinue mode model post⟩⟩
  | functions signatures bodies rest =>
    exact ⟨_,⟨.yulFunctionScope mode model signatures bodies words.1 ⟨rest,words.2⟩ post⟩⟩

/-- Genuine constructor coverage plus actual soundness, not a parameterized
assumption that every program has a rule. No termination claim is made. -/
theorem sound_program_rule_exists {F c n} (mode : Modality) (model : Model F)
    (program : Program F c n) (post : Flow c → Fml n) :
    ∃ premise : Fml n, ∀ vars, (.modal mode model program post : Fml n).holds vars ↔ premise.holds vars := by
  rcases program_rule_exists mode model program post with ⟨premise,⟨rule⟩⟩
  exact ⟨premise,rule.sound⟩


/-- Concrete ONE-STEP rule existence for every CLOSED typed expression form.
The empty external context makes the external constructor impossible. -/
theorem term_rule_exists {F n r} (mode : Modality) (model : Model F)
    (term : Term F n r) (post : Values r → Fml n) :
    ∃ premise, Nonempty (Rule (.termModal mode model term post) premise) := by
  rcases term with ⟨code,words⟩
  cases code with
  | literal value => exact ⟨_,⟨.yulLiteral mode model value post⟩⟩
  | «local» position => exact ⟨_,⟨.yulLocal mode model position post⟩⟩
  | external reference => cases reference.index
  | builtin builtin args =>
    let admitted := (checkWordBuiltin builtin).get words.1
    exact ⟨_,⟨.yulBuiltin mode model builtin admitted (fun i => ⟨args i,words.2 i⟩) post⟩⟩
  | call function args =>
    exact ⟨_,⟨.yulCall mode model function (fun i => ⟨args i,words i⟩) post⟩⟩

theorem sound_term_rule_exists {F n r} (mode : Modality) (model : Model F)
    (term : Term F n r) (post : Values r → Fml n) :
    ∃ premise : Fml n, ∀ vars, (.termModal mode model term post : Fml n).holds vars ↔ premise.holds vars := by
  rcases term_rule_exists mode model term post with ⟨premise,⟨rule⟩⟩
  exact ⟨premise,rule.sound⟩

end Solidity.Yul.Logic
