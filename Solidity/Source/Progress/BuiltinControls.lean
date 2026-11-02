import Solidity.Source.Progress.BuiltinStatements
import Solidity.Source.Progress.Controls
import Solidity.Source.Preservation.EncodingVariantControls

/-! Typed source builtin/event nodes (one `require` argument node is built
directly) and exact interpreter observations.
The checked-call consumer is nonempty. Refusal controls stay outside admission.
-/
namespace Solidity.Source.Progress.BuiltinControls
open Preservation.AllocationControls
open EM

def requireSyn (b : Bool) : Syn .expr :=
  .call (.ident "require") (.positional (.cons (.lit (.bool b)) .nil))
def requireTyped (b : Bool) : Typed ctx (requireSyn b) (.tuple []) :=
  .builtinCall rfl rfl (.cons (.bool b) .nil) rfl
def assertionSyn (b : Bool) : Syn .expr :=
  .call (.ident "assert") (.positional (.cons (.lit (.bool b)) .nil))
def assertionTyped (b : Bool) : Typed ctx (assertionSyn b) (.tuple []) :=
  .builtinCall rfl rfl (.cons (.bool b) .nil) rfl

def hashSyn : Syn .expr := .call (.ident "keccak256")
  (.positional (.cons (.lit (.str [7,9])) .nil))
def hashTyped : Typed ctx hashSyn .bytes32 :=
  .builtinCall rfl rfl (.cons (.str _) .nil) rfl

def initial : St E := Preservation.CallerReferenceControls.original

theorem require_true (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 (requireTyped true).toR).run (.cons (.bool false) .nil, initial) =
      (.ok RVal.unit, (.cons (.bool false) .nil, initial)) := by cases p <;> rfl

theorem require_false (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 (requireTyped false).toR).run (.cons (.bool false) .nil, initial) =
      (.error (.revert []), (.cons (.bool false) .nil, initial)) := by cases p <;> rfl

theorem assert_false (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 (assertionTyped false).toR).run (.cons (.bool false) .nil, initial) =
      (.error (.revert (panicData .assert)), (.cons (.bool false) .nil, initial)) := by cases p <;> rfl

theorem hash_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 hashTyped.toR).run (.cons (.bool false) .nil, initial) =
      (.ok (.val (mkBytes (n := 32) (h := by decide) (wordBytes (fixed.hash [7,9])))),
        (.cons (.bool false) .nil, {initial with heap :=
          (initial.heap.alloc ⟨.bytes .memory, .bytes [7,9]⟩).1})) := by
  cases p <;> rfl

theorem missing_head (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalBuiltin (glob p fixed) frame 10 .require (.nil : RArgs E [.bool] []) (.tuple [])).run
      (.cons (.bool false) .nil, initial) =
        (.error (.stuck "builtin"), (.cons (.bool false) .nil, initial)) := by cases p <;> rfl

theorem excluded_gasleft {E : Env} {Γ : RCtx} {C : Decl → Prop}
    {ts : List STy} (args : RArgs E Γ ts) (t : STy) :
    ¬ BuiltinFragment C .gasleft args t := by intro h; cases h <;> simp_all only [reduceCtorEq, or_self]

theorem wrong_hash_observation (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 hashTyped.toR).run (.cons (.bool false) .nil, initial) ≠
      (.error (.revert []), (.cons (.bool false) .nil, initial)) := by
  rw [hash_run]
  intro h
  cases h

open Solidity.Lowering.P9 in
/-- A builtin whose argument really calls an admitted nonempty program. -/
theorem checked_call_argument (fixed : Roadmap.Fixed) (n : Nat) :
    NS (evalE (Solidity.Lowering.P9.glob fixed) caller n
      (.builtin .require (.cons protectedCall .nil) rfl)) :=
  checked_builtin resolution (Solidity.Lowering.P9.glob fixed) "P9"
    AdmissionControls.truth_accepted rfl (Controls.admitted fixed) caller rfl n
    .require (.cons protectedCall .nil) (.tuple []) rfl
    (.require _ (.cons (.checked _ Controls.fragment trivial) .nil))

open Solidity.Lowering.P9 in
/-- The public statement adapter consumes the actual nonempty call catalogue. -/
theorem checked_call_statement (fixed : Roadmap.Fixed) (n : Nat) :
    NS (execS (Solidity.Lowering.P9.glob fixed) caller (n+1) 0 none
      (.expr (R := []) (M := false) (k := .body)
        (.builtin .require (.cons protectedCall .nil) rfl))
      (.cons (.bool false) .nil)) :=
  checked_builtin_statement resolution (Solidity.Lowering.P9.glob fixed) "P9"
    AdmissionControls.truth_accepted rfl (Controls.admitted fixed) caller rfl n 0 none
    .require (.cons protectedCall .nil) (.tuple []) rfl
    (.require _ (.cons (.checked _ Controls.fragment trivial) .nil))
    (.cons (.bool false) .nil)

def eventUnit : Syn .unit := .unit (.cons (.contract false "Events" .none .nil
  (.cons (.event "Flag" (.cons (.eventParam (.elem .bool) false (some "v")) .nil) false) .nil)) .nil)
def eventCtx : Ctx := {env := eventUnit.env, scope := some "Events", locals := []}
def eventLocals : List (String × STy) := [("flag", .bool)]
def eventSyn : Syn (.stmt .body) := .emit (.ident "Flag") (.positional (.cons (.ident "flag") .nil))
def eventTyped : StmtD (k := .body) eventCtx eventLocals eventSyn eventLocals :=
  .emit (.cons (.loc rfl rfl) .nil) rfl
def eventStmt : RStmt eventUnit.env [] false .body [.bool] [.bool] := eventTyped.toR
def eventDecl : Decl := ⟨.event, "Flag", some "Events", false,
  .event "Flag" (.cons (.eventParam (.elem .bool) false (some "v")) .nil) false⟩
def eventGlob (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : Glob eventUnit.env :=
  ⟨Source.progOf eventUnit.env, p, fixed, fun _ => ⟨0, by decide⟩, fun _ _ => true,
    fun _ => .answer (.success []), ⟨0, by decide⟩⟩
def eventFrame (static : Bool) : Fr := {frame with contract := "Events", static := static}
def eventArgs : RConvArgs eventUnit.env [.bool] [.bool] := .cons (.local .here) rfl .nil

theorem event_eq : eventStmt = .emit eventDecl rfl eventArgs := rfl

theorem event_progress (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (static : Bool) (n : Nat)
    (l : Locals eventUnit.env.layout [.bool]) :
    NS (execS (eventGlob p fixed) (eventFrame static) (n+1) 0 none eventStmt l) := by
  rw [event_eq]
  exact execS_emit_ns _ _ n 0 none eventDecl rfl eventArgs l rfl
    (Source.evalConvArgs_ns _ _ eventArgs n ⟨rfl, rfl, .inl rfl, trivial⟩ ⟨trivial, trivial⟩)

def eventResolution := Source.resolveUnit {pipeline := .legacy} eventUnit

theorem event_elaborates : (Source.elaborate eventResolution).isSome = true := by
  have hb : (Source.elabBaseArgs eventResolution.env "Events").isSome = true :=
    Solidity.Lowering.P9.InferenceCuts.base_some _ _
      (by rw [show eventResolution.env.inheritOf "Events" = .nil from rfl, Syn.inheritList]) rfl
  have he : Source.elaborates eventResolution.env = true := by
    change ((true && true) &&
      ((Source.elabBaseArgs eventResolution.env "Events").isSome && true)) = true
    rw [hb]
    rfl
  simp only [Source.elaborate, he, ↓reduceIte, Option.isSome_some]

theorem event_catalogue (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    Solidity.Lowering.P9.WholeProgram.checkFunctions eventResolution (eventGlob p fixed) "Events" = true := rfl

/-- Consume checked_emit with an actual event-only elaborated source unit.
The function catalogue is empty; the emitted Boolean and locals are inhabited. -/
theorem checked_event (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (static : Bool)
    (n : Nat) (l : Locals eventUnit.env.layout [.bool]) :
    NS (execS (eventGlob p fixed) (eventFrame static) (n+1) 0 none eventStmt l) := by
  rw [event_eq]
  exact checked_emit eventResolution (eventGlob p fixed) "Events"
    event_elaborates rfl (event_catalogue p fixed) (eventFrame static) rfl n 0 none
    eventDecl rfl eventArgs l rfl ⟨rfl, rfl, .inl rfl, trivial⟩ ⟨trivial, trivial⟩

theorem event_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (s : St eventUnit.env) :
    (execS (eventGlob p fixed) (eventFrame false) 10 0 none eventStmt (.cons (.bool true) .nil)).run
      (.nil, s) =
      (.ok (.normal (.cons (.bool true) .nil)), (.nil,
        {s with logs := ((eventFrame false).this,
          (eventGlob p fixed).selector (sigOf eventUnit.env.layout "Flag" [.bool]) ++ encoded) :: s.logs})) := by
  cases p <;> rfl

theorem event_static (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (s : St eventUnit.env) :
    (execS (eventGlob p fixed) (eventFrame true) 10 0 none eventStmt (.cons (.bool true) .nil)).run
      (.nil, s) =
      (.error (.revert []), (.nil, s)) := by cases p <;> rfl

#print axioms checked_event
#print axioms checked_call_statement
#print axioms checked_call_argument
#print axioms hash_run
#print axioms event_progress
#print axioms event_run
#print axioms event_static
end Solidity.Source.Progress.BuiltinControls
