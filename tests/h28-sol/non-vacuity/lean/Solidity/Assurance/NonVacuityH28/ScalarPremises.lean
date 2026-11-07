import Solidity.Assurance.NonVacuityH28.Calculus
import Solidity.Calculus.ExactRun

/-! True semantic rule antecedents with actual updates, guards and frames.
The terminal revert case is intentionally not a successful landing. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
variable (C : Contract)

abbrev FlagCtx : Ctx := [.val .bool]
def flagState (b : Bool) : State C FlagCtx := (State.init C).push b

def setFlag : Stmt C FlagCtx FlagCtx := .assignLocal .here (.simple (.bool true))
def flagAssert : Prog C FlagCtx FlagCtx := .cons (.assert (.simple (.local .here))) .nil

def flagUpdate : Upd C FlagCtx FlagCtx :=
  .snoc .nil (.local .here (.val (Simple.lower (.bool true))))

theorem flag_step : (setFlag C).step 0 .diamond = .update (flagUpdate C) := rfl

theorem flag_lands (b : Bool) :
    (flagUpdate C).Lands (flagState C b) (flagState C b).globG
      ((flagState C b).setLocal .here true) :=
  Upd.lands_snoc_local (Upd.lands_nil _) .here rfl

theorem flag_source (b : Bool) :
    Prog.run (flagState C b) (.cons (setFlag C) (flagAssert C)) =
      .ok ⟨(flagState C b).setLocal .here true, List.prefix_refl _⟩ := rfl

theorem flag_changed : TEnv.get .here (flagState C false).env = false ∧
    TEnv.get .here ((flagState C false).setLocal .here true).env = true := ⟨rfl, rfl⟩

theorem flag_update_antecedent (b : Bool) :
    holds (flagState C b) ((Premise.update (flagUpdate C)).fml .diamond (flagAssert C) .nil .tt) := by
  rw [Premise.fml_update]
  change (flagUpdate C).afterT .diamond (flagState C b)
    (fun τ => holds τ (.modal .diamond (flagAssert C) .nil .tt))
  exact (Upd.afterT_lands_iff (flag_lands C b) .diamond
    (fun τ => holds τ (.modal .diamond (flagAssert C) .nil .tt))).2 ⟨True.intro, nofun⟩

theorem flag_rule_application (b : Bool) :
    holds (flagState C b) (.modal .diamond (.cons (setFlag C) (flagAssert C)) .nil .tt) :=
  Main.rule_sound (Main.rule_of_step (flag_step C)) (flagState C b)
    (flagAssert C) .nil .tt (flag_update_antecedent C b)

/-- The guard is read at an actual Bool local, under both valuations. -/
def flagRequire : Stmt C FlagCtx FlagCtx := .require (.simple (.local .here))
def trueRest : Prog C FlagCtx FlagCtx := .cons (.assert (.simple (.bool true))) .nil

theorem flag_require_source_true :
    Prog.run (flagState C true) (.cons (flagRequire C) (trueRest C)) =
      .ok ⟨flagState C true, List.prefix_refl _⟩ := rfl

theorem flag_require_source_false :
    Prog.run (flagState C false) (.cons (flagRequire C) (trueRest C)) = .error .revert := rfl

theorem flag_split_antecedent (b : Bool) :
    holds (flagState C b) (((flagRequire C).step 0 .box).fml .box (trueRest C) .nil .tt) := by
  constructor
  · intro _
    intro τ _
    exact ⟨True.intro, nofun⟩
  · intro _
    exact ⟨True.intro, nofun⟩

theorem flag_split_application (b : Bool) :
    holds (flagState C b) (.modal .box (.cons (flagRequire C) (trueRest C)) .nil .tt) :=
  Main.rule_sound (Main.rule_exists 0 .box (flagRequire C)) (flagState C b)
    (trueRest C) .nil .tt (flag_split_antecedent C b)

def initializedFlag : Stmt C [] FlagCtx :=
  .declLocal .bool (.user "flag") (some (.simple (.bool true)))

theorem flag_binding_step : (initializedFlag C).step 0 .diamond =
    .bind (.user "flag") (.val .bool) (.cons (setFlag C) .nil) := rfl

/-- The hidden binder is universal, even under the diamond. Its replacement
sets the flag before the nonempty observed assertion, for EVERY initial Bool. -/
theorem flag_binding_antecedent :
    holds (State.init C) (((initializedFlag C).step 0 .diamond).fml
      .diamond (flagAssert C) .nil .tt) := by
  change ∀ b : Bool, holds (flagState C b)
    (.modal .diamond (.cons (setFlag C) .nil) (.seq (flagAssert C) .nil) .tt)
  intro b
  exact ⟨True.intro, nofun⟩

theorem flag_binding_source :
    Prog.run (State.init C) (.cons (initializedFlag C) (flagAssert C)) =
      .ok ⟨(State.init C).push (t := .val .bool) true, List.prefix_refl _⟩ := rfl

theorem flag_binding_application :
    holds (State.init C) (.modal .diamond (.cons (initializedFlag C) (flagAssert C)) .nil .tt) :=
  Main.rule_sound (Main.rule_exists 0 .diamond (initializedFlag C)) (State.init C)
    (flagAssert C) .nil .tt (flag_binding_antecedent C)

def revertingStatement : Stmt C [] [] := .revert

theorem revert_done_true :
    (revertingStatement C).step 0 .box = .done true ∧
    holds (State.init C) (((revertingStatement C).step 0 .box).fml .box (assertion C) .nil .tt) :=
  ⟨rfl, True.intro⟩

theorem revert_rule_application :
    holds (State.init C) (.modal .box (.cons (revertingStatement C) (assertion C)) .nil .tt) :=
  Main.rule_sound (Main.rule_exists 0 .box (revertingStatement C)) (State.init C)
    (assertion C) .nil .tt (revert_done_true C).2

end Solidity.Assurance.NonVacuityH28
