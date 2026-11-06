import Solidity.Lowering.V07.BooleanComparisons
import Solidity.Lowering.V07.P12Controls

namespace Solidity.Lowering.V07.BooleanComparisonControls
open BooleanComparisons
open Source.SemanticsExamples
open P12Controls (C E SrcCtx TgtCtx mapping BindingRel bool_reflect)
open MixedAssignmentControls (globals)

def source (old assigned : Bool) : Source.EMState E SrcCtx :=
  (.cons (.bool old) (.cons (.bool assigned) MixedAssignmentControls.source.1),MixedAssignmentControls.source.2)
def target (old assigned : Bool) : State C TgtCtx :=
  (MixedAssignmentControls.target.push (t := .val .bool) assigned).push (t := .val .bool) old

theorem initial (old assigned : Bool) : mapping.Related BindingRel (source old assigned).1 (target old assigned).env := by
  intro τ i
  cases i with
  | here => rfl
  | there i => cases i with
    | here => rfl
    | there i => exact P12Controls.initial (.there (.there i))

def commute_client (ne : Bool) := answer_commutes ne true false
def source_value_client (ne : Bool) := source_value (D := E.layout) ne false true
def value_client (ne : Bool) := value_run (target false true) ne
  (.simple (.local .here)) (.simple (.local (.there .here))) false true rfl rfl
def pair_client (p : Roadmap.Pipeline) (checked ne : Bool) (fuel : Nat) :=
  source_from_pair (globals p) {F0 with checked := checked} (fuel+2) (source false true) (source false true) ne
    (.local .here) (.local (.there .here)) false true
    (source_pure_pair (globals p) {F0 with checked := checked} (fuel+1) (source false true)
      (.local .here) (.local (.there .here)) (.val (.bool false)) (.val (.bool true)) rfl rfl)
def assignment_client (p : Roadmap.Pipeline) (checked ne : Bool) (fuel : Nat) :=
  source_assignment (globals p) {F0 with checked := checked} fuel (source false true) ne
    .here (.there .here) true false rfl rfl
def tail_client (ne : Bool) := tail_run (target false true) ne .here (.there .here) false true rfl rfl
def swap_client (ne : Bool) := tail_swap_run (target false true) ne .here (.there .here)
def pass_client (ne : Bool) (p : Roadmap.Pipeline) := pass_exact (C := C) (Γ := TgtCtx) ne p .here (.there .here)
def code_client (ne : Bool) (p : Roadmap.Pipeline) := code_run (target false true) ne p .here (.there .here) true false rfl rfl
def operand_client (ne : Bool) (p : Roadmap.Pipeline) := operand_run (target false true) ne p .here (.there .here) true false rfl rfl
def capture_client (right left result : Bool) :
    (mapping.wk (Thin.drop (Thin.drop (Thin.drop Thin.refl)))).Related BindingRel
      (source false true).1 ((((target false true).push (t := .val .bool) right).push
        (t := .val .bool) left).push (t := .val .bool) result).env :=
  capture_relation mapping (target false true) BindingRel (source false true).1
    (initial false true) right left result

def transport_client (p : Roadmap.Pipeline) (checked ne : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel (source false true) (target false true)
    mapping BindingRel (initial false true) bool_reflect ne .here (.there .here) .here (.there .here) rfl rfl

def self_alias_client (p : Roadmap.Pipeline) (checked ne : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel (source false true) (target false true)
    mapping BindingRel (initial false true) bool_reflect ne .here .here .here .here rfl rfl

def equal_content_client (p : Roadmap.Pipeline) (checked ne : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel (source true true) (target true true)
    mapping BindingRel (initial true true) bool_reflect ne .here (.there .here) .here (.there .here) rfl rfl

def extension_client (ne : Bool) (p : Roadmap.Pipeline) := DeferredSource.Operand.run_wk
  (operand ne p .here (.there .here)) (Thin.drop (t := .val .bool) Thin.refl)
  (target false true) (true,(target false true).env)

def binder_client (p : Roadmap.Pipeline) (checked ne : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel
    (Source.Locals.cons (.bool true) (source false true).1,(source false true).2)
    ((target false true).push (t := .val .bool) true)
    (mapping.cons .bool (.val .bool)) BindingRel
    (ContextMap.related_cons mapping BindingRel (source false true).1 (target false true).env
      (initial false true) .bool (.val .bool) (.bool true) true rfl) bool_reflect ne
    (.there .here) (.there (.there .here)) (.there .here) (.there (.there .here)) rfl rfl

def live_client := P12Controls.live_memory_and_storage
def world_client (p : Roadmap.Pipeline) (checked ne : Bool) :=
  congrArg (fun result => result.2.2) (transport_client p checked ne 0).1
def glob_client (ne : Bool) (p : Roadmap.Pipeline) :=
  congrArg (fun result => result.toOption.map (fun out => out.1.st.glob)) (operand_client ne p)

def check (p : Roadmap.Pipeline) (checked ne old assigned : Bool) : Bool :=
  let src := source old assigned
  let tgt := target old assigned
  let sr := (Source.evalE (globals p) {F0 with checked := checked} 4
    (.compare (sourceOp ne) (.assign (.local .here) (.local (.there .here))) (.local .here))).run src
  let tr := (operand ne p .here (.there .here)).run tgt
  match sr.1,tr,(code ne p .here (.there .here)).run tgt with
  | .ok (.val (.bool v)),.ok (out,.prim w),.ok captures =>
      v == answer ne assigned (if p = .legacy then old else assigned) && w == v &&
      TEnv.get .here captures.st.env == v && TEnv.get (.there .here) captures.st.env == assigned &&
      TEnv.get (.there (.there .here)) captures.st.env == (if p = .legacy then old else assigned) &&
      (match sr.2.1.get .here,sr.2.1.get (.there .here) with
       | .bool i,.bool a => i == assigned && a == assigned) &&
      TEnv.get .here out.st.env == assigned && TEnv.get (.there .here) out.st.env == assigned
  | _,_,_ => false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  [false,true].all fun ne => [false,true].all fun old => [false,true].all fun assigned => check p checked ne old assigned))

def observed (ne : Bool) (p : Roadmap.Pipeline) : Option (Bool × Bool × Bool × Bool × Bool) := do
  let out ← (code ne p .here (.there .here)).run (target false true) |>.toOption
  let done ← (operand ne p .here (.there .here)).run (target false true) |>.toOption
  let .prim result := done.2
  pure (TEnv.get .here out.st.env,TEnv.get (.there .here) out.st.env,
    TEnv.get (.there (.there .here)) out.st.env,result,TEnv.get .here done.1.st.env)

/-- info: [some (false, true, false, false, true),
 some (true, true, true, true, true),
 some (true, true, false, true, true),
 some (false, true, true, false, true)] -/
#guard_msgs in
#eval IO.println (reprStr [observed false .legacy,observed false .viaIR,observed true .legacy,observed true .viaIR])

-- Captured scalar equality commutes; reordering effectful Source expressions does not.
def reordered (ne : Bool) (p : Roadmap.Pipeline) : Option (Bool × Bool × Bool) := do
  let (result,out) := (Source.evalE (globals p) F0 4
    (.compare (sourceOp ne) (.local .here) (.assign (.local .here) (.local (.there .here))))).run (source false true)
  let .ok (.val (.bool v)) := result | none
  let .bool i := out.1.get .here
  let .bool a := out.1.get (.there .here)
  pure (v,i,a)
/-- info: [some (true, true, true), some (false, true, true), some (false, true, true), some (true, true, true)] -/
#guard_msgs in
#eval IO.println (reprStr [reordered false .legacy,reordered false .viaIR,reordered true .legacy,reordered true .viaIR])

def capturedSwap (ne : Bool) : DeferredSource.Operand C TgtCtx (.prim .bool) :=
  ⟨_,(assignReadPrefix .legacy .here (.there .here)).join (tail ne (.there .here) .here),
    .val (.simple (.local .here))⟩
def uncaptured (ne : Bool) : DeferredSource.Operand C TgtCtx (.prim .bool) :=
  ⟨_,(assignReadPrefix .legacy .here (.there .here)).join (tail ne .here (.there (.there .here))),
    .val (.simple (.local .here))⟩
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([false,true].all fun ne =>
  match (operand ne .legacy .here (.there .here)).run (target false true),
      (capturedSwap ne).run (target false true),(uncaptured ne).run (target false true) with
  | .ok (out,.prim v),.ok (swapped,.prim w),.ok (wrong,.prim z) =>
      v == w && v != z && TEnv.get .here out.st.env && TEnv.get .here swapped.st.env && TEnv.get .here wrong.st.env
  | _,_,_ => false))

-- After dropping first, the same-typed caller binding is true, not the false result.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  match (code false .legacy .here (.there .here)).run (target false true) with
  | .ok out =>
      match (Val.simple (.local .here) : Val C TgtCtx .bool).evalT
        (out.st.drop (code (C := C) false .legacy .here (.there .here)).ext) with
      | .ok b => b
      | _ => false
  | _ => false))
end Solidity.Lowering.V07.BooleanComparisonControls

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.initial

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.commute_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.commute_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.source_value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.source_value_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.value_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.pair_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.pair_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.assignment_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.tail_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.tail_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.swap_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.swap_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.pass_client' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.pass_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.code_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.code_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.operand_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.operand_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.capture_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.capture_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.transport_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.self_alias_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.self_alias_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.equal_content_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.equal_content_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.extension_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.binder_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.binder_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.live_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.live_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.world_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.world_client

/-- info: 'Solidity.Lowering.V07.BooleanComparisonControls.glob_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.BooleanComparisonControls.glob_client
