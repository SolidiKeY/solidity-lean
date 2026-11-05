import Solidity.Lowering.V08.LocalCallableTransport
import Solidity.Lowering.V07.ConditionalAssignments

/-! Actual conditional-argument Source calls and a published intrinsic argument
operand. Initial typed context/value alignment derives reached local alignment;
no target callee/body/heap/frame compiler relation or admission is assumed.
Sufficient quotation indices below describe this syntax, not a profile cutoff. -/
namespace Solidity.Lowering.V08.ConditionalCallable
open Solidity Source
open Solidity.Lowering.V07
variable {E : Source.Env} {srcΓ : Source.RCtx}

def arguments (t : Source.IntTy) (ci ca : Source.Idx srcΓ .bool)
    (i a j b : Source.Idx srcΓ (.int t)) : Source.RConvArgs E srcΓ [.int t] :=
  .cons (.cond (.assign (.local ci) (.local ca))
    (.assign (.local i) (.local a)) (.assign (.local j) (.local b)))
    (IntegerCallable.implicit_identity t) .nil

/-- Reads concern concrete initial locals after the explicit condition write,
not an assumed evaluation or desired whole-program preservation equation. -/
theorem argument_actual (g : Source.Glob E) (f : Source.Fr) (extra : Nat)
    (t : Source.IntTy) (ci ca : Source.Idx srcΓ .bool)
    (i a j b : Source.Idx srcΓ (.int t)) (locals : Source.Locals E.layout srcΓ)
    (state : Source.St E) (choice : Bool) (n : Int) (bound : t.lo ≤ n ∧ n ≤ t.hi)
    (conditionRead : locals.get ca = .bool choice)
    (selectedRead : (locals.set ci (.bool choice)).get (if choice then a else b) = .int n bound) :
    (Source.evalConvArgs g f (extra+16) (arguments t ci ca i a j b)).run (locals,state) =
      (.ok (.cons (.int n bound) .nil),
        ConditionalAssignments.sourceAfter (locals,state) ci choice i a j b) := by
  simp only [arguments,Source.evalConvArgs,IntegerCallable.conversion_identity,
    Source.Hoare.run_bind,ConditionalAssignments.source_run g f (extra+12)
      (locals,state) ci ca choice i a j b conditionRead,selectedRead]
  rfl

/-- The callee's local subframe is actually executed and discarded. The
condition and selected-branch caller writes survive in the exact returned
locals; the ENTIRE Source.St, including heap and journals, is unchanged. -/
theorem source_expression (g : Source.Glob E) (f : Source.Fr) (decl : Source.Decl)
    (t : Source.IntTy) (selected : IntegerCallable.Inputs g f decl t) (extra : Nat)
    (ci ca : Source.Idx srcΓ .bool) (i a j b : Source.Idx srcΓ (.int t))
    (locals : Source.Locals E.layout srcΓ) (state : Source.St E)
    (choice : Bool) (n : Int) (bound : t.lo ≤ n ∧ n ≤ t.hi)
    (conditionRead : locals.get ca = .bool choice)
    (selectedRead : (locals.set ci (.bool choice)).get (if choice then a else b) = .int n bound) :
    (Source.evalE g f (extra+17)
      (.call decl selected.signature (arguments t ci ca i a j b))).run (locals,state) =
      (.ok (.val (.int n bound)),
        ConditionalAssignments.sourceAfter (locals,state) ci choice i a j b) := by
  exact SourceCallable.expression_complete g f (extra+16) decl selected.signature
    (arguments t ci ca i a j b) locals
    (ConditionalAssignments.sourceAfter (locals,state) ci choice i a j b).1
    (.cons (.int n bound) .nil) (.val (.int n bound)) state state state
    (argument_actual g f extra t ci ca i a j b locals state choice n bound
      conditionRead selectedRead)
    (IntegerCallable.source_call g f decl t selected (extra+4) state n bound)

/-- The actual published target operand captures the condition and selected
assignment before dropping its two temporary locals. Read hypotheses are
concrete typed reads, not an assumed target execution. -/
theorem target_argument {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (ci ca : Idx Γ (.val .bool))
    (i a j b : Idx Γ (.val (integerPrim t))) (choice : Bool)
    (n : Int) (bound : t.lo ≤ n ∧ n ≤ t.hi)
    (conditionRead : TEnv.get ca target.env = choice)
    (selectedRead : TEnv.get (if choice then a else b) (TEnv.set ci choice target.env) =
      integerValue t n bound) :
    (ConditionalAssignments.operand ci ca i a j b).run target =
      .ok (⟨ConditionalAssignments.targetAfter target ci choice i a j b,
        List.prefix_refl _⟩,.prim (integerValue t n bound)) := by
  simpa only [selectedRead] using
    ConditionalAssignments.operand_run target ci ca choice i a j b conditionRead

/-- Initial independent value alignment discharges the complete conditional
argument relation. The actual Source call then returns that argument and keeps
the reached caller locals. This concludes no target callee/body/heap relation. -/
theorem transport_context {C : Contract} {Γ : Ctx}
    (g : Source.Glob E) (f : Source.Fr) (decl : Source.Decl)
    (t : Source.IntTy) (selected : IntegerCallable.Inputs g f decl t) (extra : Nat)
    (locals : Source.Locals E.layout srcΓ) (source : Source.St E) (target : State C Γ)
    (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (initial : m.Related R locals target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (c : Bool), R .bool (.val .bool) v c → v = .bool c)
    (ci ca : Source.Idx srcΓ .bool) (i a j b : Source.Idx srcΓ (.int t))
    (tci tca : Idx Γ (.val .bool)) (ti ta tj tb : Idx Γ (.val (integerPrim t)))
    (mapCI : m.slot ci = ⟨.val .bool,tci⟩) (mapCA : m.slot ca = ⟨.val .bool,tca⟩)
    (mapI : m.slot i = ⟨.val (integerPrim t),ti⟩) (mapA : m.slot a = ⟨.val (integerPrim t),ta⟩)
    (mapJ : m.slot j = ⟨.val (integerPrim t),tj⟩) (mapB : m.slot b = ⟨.val (integerPrim t),tb⟩)
    (choice : Bool) (n : Int) (bound : t.lo ≤ n ∧ n ≤ t.hi)
    (conditionRead : locals.get ca = .bool choice)
    (selectedRead : (locals.set ci (.bool choice)).get (if choice then a else b) = .int n bound) :
    (Source.evalE g f (extra+17)
      (.call decl selected.signature (arguments t ci ca i a j b))).run (locals,source) =
      (.ok (.val (.int n bound)),ConditionalAssignments.sourceAfter (locals,source) ci choice i a j b) ∧
    (ConditionalAssignments.operand tci tca ti ta tj tb).run target =
      .ok (⟨ConditionalAssignments.targetAfter target tci choice ti ta tj tb,List.prefix_refl _⟩,
        .prim (TEnv.get (if choice then ta else tb) (TEnv.set tci choice target.env))) ∧
    R (.int t) (.val (integerPrim t)) (.int n bound)
      (TEnv.get (if choice then ta else tb) (TEnv.set tci choice target.env)) ∧
    m.Related R (ConditionalAssignments.sourceAfter (locals,source) ci choice i a j b).1
      (ConditionalAssignments.targetAfter target tci choice ti ta tj tb).env := by
  have reflected : locals.get ca = .bool (TEnv.get tca target.env) :=
    boolReflect _ _ (ContextMap.value_at m R locals target.env initial ca tca mapCA)
  have same : TEnv.get tca target.env = choice := Source.Val.bool.inj (reflected.symm.trans conditionRead)
  have argument := ConditionalAssignments.transport g f (extra+12) (locals,source) target m R initial
    boolReflect ci ca i a j b tci tca ti ta tj tb mapCI mapCA mapI mapA mapJ mapB
  dsimp only at argument
  rw [same,selectedRead] at argument
  exact ⟨source_expression g f decl t selected extra ci ca i a j b locals source choice n bound
    conditionRead selectedRead,argument.2.1,argument.2.2.1,argument.2.2.2⟩


namespace Controls
open SignedCallableControls
abbrev ctx : Source.RCtx := [.bool,.bool,.int t,.int t,.int t]
def destination : Source.Idx ctx (.int t) := .there (.there .here)
def left : Source.Idx ctx (.int t) := .there (.there (.there .here))
def right : Source.Idx ctx (.int t) := .there (.there (.there (.there .here)))
def locals (choice : Bool) : Source.Locals SignedCallableControls.E.layout ctx :=
  .cons (.bool (!choice)) (.cons (.bool choice)
    (.cons (.int 0 (by decide +kernel)) (.cons (.int (-7) (by decide +kernel))
      (.cons (.int 11 (by decide +kernel)) .nil))))
def chosen (choice : Bool) : Int := if choice then -7 else 11
theorem chosen_bound (choice : Bool) : t.lo ≤ chosen choice ∧ chosen choice ≤ t.hi := by
  cases choice <;> decide +kernel

def expression (p : Roadmap.Pipeline) : Source.RExpr SignedCallableControls.E ctx (.int t) :=
  .call declaration (inputs p).signature
    (arguments t .here (.there .here) destination left destination right)

/-- Both branches and pipelines retain the original populated balances,
code/nonce/storage/transients, two heap objects, ordered logs/events and fnLocals,
by exact machine equality rather than a smaller observation projection. -/
theorem inhabited (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) (choice : Bool) :
    (Source.evalE (global p) frame (extra+17) (expression p)).run
      (locals choice,populated bytes) =
      (.ok (.val (.int (chosen choice) (chosen_bound choice))),
        ConditionalAssignments.sourceAfter (locals choice,populated bytes)
          .here choice destination left destination right) := by
  exact source_expression (global p) frame declaration t (inputs p) extra
    .here (.there .here) destination left destination right
    (locals choice) (populated bytes) choice (chosen choice) (chosen_bound choice)
    rfl (by cases choice <;> rfl)

/-- Selecting the other branch changes the full returned typed value; no
hash inequality, ABI observation or admission assumption is used. -/
theorem wrong_branch (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) (choice : Bool) :
    (Source.evalE (global p) frame (extra+17) (expression p)).run
      (locals choice,populated bytes) ≠
      (.ok (.val (.int (chosen (!choice)) (chosen_bound (!choice)))),
        ConditionalAssignments.sourceAfter (locals choice,populated bytes)
          .here choice destination left destination right) := by
  rw [inhabited]
  cases choice <;> intro wrong <;> cases wrong

abbrev TargetCtx : Ctx := [.val .uint,.val .bool,.val .bool,
  .val (integerPrim t),.val (integerPrim t),.val (integerPrim t)]

def slots : ContextMap ctx TargetCtx :=
  (((((ContextMap.empty.cons (.int t) (.val (integerPrim t))).cons
    (.int t) (.val (integerPrim t))).cons (.int t) (.val (integerPrim t))).cons
    .bool (.val .bool)).cons .bool (.val .bool)).wk (Thin.drop .refl)

def target {C : Contract} (base : State C []) (choice : Bool) : State C TargetCtx :=
  (((((base.push (t:=.val (integerPrim t)) (integerValue t 11 (by decide +kernel))).push
    (t:=.val (integerPrim t)) (integerValue t (-7) (by decide +kernel))).push
    (t:=.val (integerPrim t)) (integerValue t 0 (by decide +kernel))).push
    (t:=.val .bool) choice).push (t:=.val .bool) (!choice)).push
    (t:=.val .uint) EffectfulCallableArgument.live

def tci : Idx TargetCtx (.val .bool) := .there .here
def tca : Idx TargetCtx (.val .bool) := .there (.there .here)
def ti : Idx TargetCtx (.val (integerPrim t)) := .there (.there (.there .here))
def ta : Idx TargetCtx (.val (integerPrim t)) := .there (.there (.there (.there .here)))
def tb : Idx TargetCtx (.val (integerPrim t)) := .there (.there (.there (.there (.there .here))))

theorem initial_alignment {C : Contract} (base : State C []) (choice : Bool) :
    slots.Related AssignedCallableContext.Values (locals choice) (target base choice).env := by
  intro τ index
  cases index with
  | here => rfl
  | there index => cases index with
    | here => rfl
    | there index => cases index with
      | here => exact integer_related t 0 (by decide +kernel)
      | there index => cases index with
        | here => exact integer_related t (-7) (by decide +kernel)
        | there index => cases index with
          | here => exact integer_related t 11 (by decide +kernel)
          | there index => cases index


theorem context_client {C : Contract} (base : State C []) (p : Roadmap.Pipeline)
    (extra : Nat) (bytes : Roadmap.Bytes) (choice : Bool) :
    (Source.evalE (global p) frame (extra+17) (expression p)).run (locals choice,populated bytes) =
      (.ok (.val (.int (chosen choice) (chosen_bound choice))),
        ConditionalAssignments.sourceAfter (locals choice,populated bytes)
          .here choice destination left destination right) ∧
    (ConditionalAssignments.operand tci tca ti ta ti tb).run (target base choice) =
      .ok (⟨ConditionalAssignments.targetAfter (target base choice) tci choice ti ta ti tb,
        List.prefix_refl _⟩,.prim (integerValue t (chosen choice) (chosen_bound choice))) ∧
    slots.Related AssignedCallableContext.Values
      (ConditionalAssignments.sourceAfter (locals choice,populated bytes)
        .here choice destination left destination right).1
      (ConditionalAssignments.targetAfter (target base choice) tci choice ti ta ti tb).env := by
  have actual := transport_context (global p) frame declaration t (inputs p) extra
    (locals choice) (populated bytes) (target base choice) slots AssignedCallableContext.Values
    (initial_alignment base choice) (fun _ _ relation => relation)
    .here (.there .here) destination left destination right tci tca ti ta ti tb
    rfl rfl rfl rfl rfl rfl choice (chosen choice) (chosen_bound choice)
    rfl (by cases choice <;> rfl)
  have value : TEnv.get (if choice then ta else tb) (TEnv.set tci choice (target base choice).env) =
      integerValue t (chosen choice) (chosen_bound choice) := by cases choice <;> rfl
  rw [value] at actual
  exact ⟨actual.1,actual.2.1,actual.2.2.2⟩


theorem wrong_context_snapshot {C : Contract} (base : State C []) :
    ¬ slots.Related AssignedCallableContext.Values (locals false)
      (ConditionalAssignments.targetAfter (target base false) tci false ti ta ti tb).env := by
  intro wrong
  have value := wrong (.here : Source.Idx ctx .bool)
  change Source.Val.bool true = .bool false at value
  cases value


theorem skipped_branch_write {C : Contract} (base : State C []) :
    ¬ slots.Related AssignedCallableContext.Values ((locals true).set .here (.bool true))
      (ConditionalAssignments.targetAfter (target base true) tci true ti ta ti tb).env := by
  intro wrong
  have value := wrong destination
  change some (0 : Int) = some (-7 : Int) at value
  cases value


def observe {C : Contract} (state : State C TargetCtx) :
    Option Int × Bool × Bool × Option Int × Option Int × Option Int :=
  (PrimTy.num? (TEnv.get (.here : Idx TargetCtx (.val .uint)) state.env),
    TEnv.get tci state.env,TEnv.get tca state.env,
    PrimTy.num? (TEnv.get ti state.env),PrimTy.num? (TEnv.get ta state.env),PrimTy.num? (TEnv.get tb state.env))

theorem target_vector {C : Contract} (base : State C []) (choice : Bool) :
    ((ConditionalAssignments.operand tci tca ti ta ti tb).run (target base choice)).toOption.map
      (fun result => observe result.1.st) =
      some (some 42,choice,choice,some (chosen choice),some (-7),some 11) := by
  rw [ConditionalAssignments.operand_run (target base choice) tci tca choice ti ta ti tb rfl]
  cases choice <;> rfl


theorem retained_state (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) (choice : Bool) :
    ((Source.evalE (global p) frame (extra+17) (expression p)).run (locals choice,populated bytes)).2.2 =
      populated bytes := by
  rw [inhabited]
  rfl

theorem payload_clients (p : Roadmap.Pipeline) (choice : Bool) :
    ∀ bytes ∈ [[],[0,255,128],List.replicate 33 129],
      (Source.evalE (global p) frame 17 (expression p)).run (locals choice,populated bytes) =
        (.ok (.val (.int (chosen choice) (chosen_bound choice))),
          ConditionalAssignments.sourceAfter (locals choice,populated bytes)
            .here choice destination left destination right) := by
  exact fun bytes _ => inhabited p 0 bytes choice

/-- A low-horizon timeout retains the already completed conditional argument
writes. It is not an automatic rollback of the caller or a transaction end. -/
theorem reached_timeout (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (choice : Bool) :
    (Source.evalE (global p) frame 5 (expression p)).run (locals choice,populated bytes) =
      (.error .timeout,ConditionalAssignments.sourceAfter (locals choice,populated bytes)
        .here choice destination left destination right) := by
  cases choice <;> rfl

/-- Static Source frames still permit local argument writes and this pure
selected echo body. No storage write or external-call static admission follows. -/
theorem static_execution (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) (choice : Bool) :
    (Source.evalE (global p) {frame with static := true} (extra+17) (expression p)).run
    (locals choice,populated bytes) =
    (.ok (.val (.int (chosen choice) (chosen_bound choice))),
      ConditionalAssignments.sourceAfter (locals choice,populated bytes)
        .here choice destination left destination right) := by
  exact source_expression (global p) {frame with static := true} declaration t
    ⟨(inputs p).member,(inputs p).kind,(inputs p).signature,rfl⟩ extra
    .here (.there .here) destination left destination right
    (locals choice) (populated bytes) choice (chosen choice) (chosen_bound choice)
    rfl (by cases choice <;> rfl)


theorem zero_horizon (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (choice : Bool) :
    (Source.evalE (global p) frame 0 (expression p)).run (locals choice,populated bytes) =
      (.error .timeout,(locals choice,populated bytes)) := by rfl
end Controls
end Solidity.Lowering.V08.ConditionalCallable

/-- info: 'Solidity.Lowering.V08.ConditionalCallable.argument_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.argument_actual
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.source_expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.source_expression
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.target_argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.target_argument
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.transport_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.transport_context
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.Controls.chosen_bound' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.Controls.chosen_bound
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.Controls.inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.Controls.inhabited
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.Controls.wrong_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.Controls.wrong_branch
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.Controls.initial_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.Controls.initial_alignment
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.Controls.context_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.Controls.context_client
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.Controls.wrong_context_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.Controls.wrong_context_snapshot
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.Controls.skipped_branch_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.Controls.skipped_branch_write
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.Controls.target_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.Controls.target_vector
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.Controls.retained_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.Controls.retained_state
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.Controls.payload_clients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.Controls.payload_clients
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.Controls.zero_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.Controls.zero_horizon
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.Controls.reached_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.Controls.reached_timeout
/-- info: 'Solidity.Lowering.V08.ConditionalCallable.Controls.static_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.ConditionalCallable.Controls.static_execution
