import Solidity.Lowering.P8.EntryRoots

/-! Inhabited intrinsic entry-selection controls with a supplied Program.
These are not parser/elaboration, source execution or EVM witnesses. The
fixed hash is deliberately constant; no cryptographic adequacy is asserted. -/
namespace Solidity.Lowering.P8.EntryRootControls
open Source

def functionDecl : Decl := ⟨.function, "entry", some "C", false,
  .function (.ident "entry") .nil (some .pub) none .nil false none .nil
    (.some (.block .nil))⟩
def receiveDecl : Decl := ⟨.receive, "receive", some "C", false,
  .receive true true .nil false none (.some (.block .nil))⟩
def fallbackDecl : Decl := ⟨.fallback, "fallback", some "C", false,
  .fallback .fbNoParams true none .nil false none (.some (.block .nil))⟩
def contractDecl : Decl := ⟨.contract, "C", none, true,
  .contract false "C" .none .nil
    (.cons functionDecl.node (.cons receiveDecl.node (.cons fallbackDecl.node .nil)))⟩
def env : Env := ⟨[contractDecl, functionDecl, receiveDecl, fallbackDecl]⟩
def body : RBody env := {
  ps := [], rs := [], inModifier := false, locals := [], out := []
  items := .stmt (.expr (.magic .block "timestamp" rfl)) .nil }
def program : Program env := {
  body := fun _ => some body, consts := fun _ => none
  inits := fun _ => [], ctor := fun _ => none, ctorLocals := fun _ => []
  baseArgs := fun _ => [], contracts := ["C"] }
def fixed : Roadmap.Fixed := {
  evm := {keccak := fun _ => 0, keccak_lt := fun _ => by decide +kernel
          precompile := fun _ _ => none, precompileGas := fun _ _ => 0}
  ledger := fun bal _ a => bal a, regionLen := 1, rootSlots := 1 }
def global : Glob env := {
  prog := program, pipeline := .legacy, fixed := fixed
  balance0 := fun _ => ⟨0, by decide +kernel⟩, hasCode := fun _ _ => false
  callee := fun _ => .answer (.success []), timestamp := ⟨0, by decide +kernel⟩ }
def frame : Fr := {
  this := ⟨0, by decide +kernel⟩, sender := ⟨1, by decide +kernel⟩
  value := ⟨0, by decide +kernel⟩, static := false, contract := "C" }
def absent : Glob env := {global with prog := {program with body := fun _ => none}}

abbrev Controls : Prop :=
  global.pickFn frame [0, 0, 0, 0] = some functionDecl ∧
  global.pickFn frame [1, 0, 0, 0] = none ∧
  absent.pickFn frame [0, 0, 0, 0] = none ∧
  global.pickFn {frame with contract := "Absent"} [0, 0, 0, 0] = none ∧
  env.special "C" .receive = some receiveDecl ∧
  env.special "C" .fallback = some fallbackDecl ∧
  env.special "Absent" .receive = none ∧
  env.special "C" .modifier = none
/-- Eight actual selector observations, including retained refusals. -/
theorem selectors : Controls := by decide

/-- Selected bodies carry a real observation; this is not an execution proof. -/
theorem populated_body : Frontend.Admission.bodyObservations body =
    [Frontend.Admission.ObservationSite.magic .block "timestamp"] := rfl

/-- info: 'Solidity.Lowering.P8.EntryRootControls.selectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selectors
/-- info: 'Solidity.Lowering.P8.EntryRootControls.populated_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms populated_body
end Solidity.Lowering.P8.EntryRootControls
