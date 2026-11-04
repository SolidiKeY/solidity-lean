import Solidity.Source.SemanticsExamples
import Solidity.Source.FailureEventLaws

/-! H16 actual initcode-frame controls. The intrinsic constructor's state
initializer calls an explicit environment receiver, receives an ABI word and
writes the decoded value. Fixed hash and strategy are explicit fixture inputs;
no compiler/EVM, root transaction ordinal or post-fee funding theorem is claimed. -/
namespace Solidity.Source.FailureExecution.ConstructorControls
open EM SemanticsExamples

/-- Fixture structural equality only; execution is still the actual interpreter. -/
private instance {α : Type} [DecidableEq α] : DecidableEq (Except Halt α) := fun a b =>
  match a,b with
  | .error x,.error y => decidable_of_iff (x=y) (by constructor <;> intro h <;> cases h <;> rfl)
  | .ok x,.ok y => decidable_of_iff (x=y) (by constructor <;> intro h <;> cases h <;> rfl)
  | .error _,.ok _ => isFalse (by intro h; cases h)
  | .ok _,.error _ => isFalse (by intro h; cases h)

def stateNode : Syn (.part false) := .stateVar Solidity.Source.Examples.u256 none none none false "x" .none
def readNode : Syn (.part false) :=
  .function (.ident "read") .nil (some .external) none .nil false none pUint .none
def unit : Syn .unit := .unit
  (.cons (.contract false "C" .none .nil (.cons stateNode
    (.cons (.constructor .nil .nil false none (.block .nil)) .nil)))
  (.cons (.interface "I" .nil (.cons readNode .nil)) .nil))
def E : Env := unit.env
def stateDecl : Decl := ⟨.stateVar,"x",some "C",false,stateNode⟩
def reader : Decl := ⟨.function,"read",some "I",false,readNode⟩
theorem variable_type : stateDecl.varTy E = some uint := by decide
theorem reader_signature : reader.fnSig E = some ([],[uint]) := by decide

def initializer : RExpr E [] uint := .extCall
  (.convExplicit (τ := .contract ⟨none,"I"⟩) (.addressLit [9]) (by decide))
  reader reader_signature (.conv (.const (Q.ofInt 0)) (.inl (by decide))) .nil

def program : Program E where
  body _ := none
  consts _ := none
  inits c := if c = "C" then [⟨stateDecl,uint,variable_type,initializer⟩] else []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := ["C"]

def prior : Roadmap.Event := .answer (.success [0xA1]) none
def input : St E := { St.init E with
  ex := (St.init E).ex.apply (.account user fun a => { a with nonce := 17 })
  heap := (Heap.empty.alloc ⟨.bytes .memory,Data.bytes [0xDE,0xAD]⟩).1
  events := [prior]
  logs := [(user,[0xAA,0xBB])]
  fnLocals := ⟨[.bool],.cons (.bool true) .nil⟩ }

def global (pipeline : Roadmap.Pipeline) : Glob E :=
  ⟨program,pipeline,toyFixed,fun _ => word 0,fun _ _ => true,
    fun _ => .answer (.success (wordBytes (word 42))),word 0⟩
def points (cut : Option Nat) : Roadmap.Evm.FailurePoints where
  tx _ := .runs 257 none
  frame _ := cut

def run (pipeline : Roadmap.Pipeline) (cut : Option Nat) (fuel : Nat := 20) :=
  (deploy (plan := some (points cut)) (global pipeline) fuel "C" thisC user (word 0) []).run
    (L0 E,input)

def value (s : St E) : Option Int :=
  match (s.ex.world.accounts thisC).storage.read stateDecl.path with
  | some (.int n _) => some n
  | _ => none

theorem uncut_value (pipeline : Roadmap.Pipeline) : value (run pipeline none).2.2 = some 42 := by
  cases pipeline <;> decide +kernel

theorem uncut_frames (pipeline : Roadmap.Pipeline) :
    (run pipeline none).2.2.resource.nextFrame = 1 := by cases pipeline <;> decide +kernel

theorem cut0_revert (pipeline : Roadmap.Pipeline) :
    (run pipeline (some 0)).1 = .ok (.revert []) := by cases pipeline <;> decide +kernel

theorem cut1_revert (pipeline : Roadmap.Pipeline) :
    (run pipeline (some 1)).1 = .ok (.revert []) := by cases pipeline <;> decide +kernel

theorem cut2_revert (pipeline : Roadmap.Pipeline) :
    (run pipeline (some 2)).1 = .ok (.revert []) := by cases pipeline <;> decide +kernel

def callEvent : Roadmap.Event := .call ext (word 0) (selOf "read()") false
def answerEvent : Roadmap.Event := .answer (.success (wordBytes (word 42))) none

theorem cut1_root_state (pipeline : Roadmap.Pipeline) :
    let s := (run pipeline (some 1)).2.2
    value s = some 0 ∧ s.events = [prior,callEvent] ∧
      s.ex.journal.length = 1 ∧ (s.ex.world.accounts user).nonce = 17 ∧
      (s.ex.world.accounts thisC).nonce = 0 ∧ s.resource.nextFrame = 1 ∧
      s.resource.frames.isEmpty = true ∧ s.resource.pending.isNone = true ∧
      s.heap.next = 0 := by
  cases pipeline <;> decide +kernel

theorem cut2_events (pipeline : Roadmap.Pipeline) :
    (run pipeline (some 2)).2.2.events = [prior,callEvent,answerEvent] := by
  cases pipeline <;> decide +kernel

theorem uncut_events (pipeline : Roadmap.Pipeline) :
    (run pipeline none).2.2.events = [prior,callEvent,answerEvent] := by
  cases pipeline <;> decide +kernel

def prefund : Account E.layout (E.lay thisC) :=
  ⟨word 0,1,none,Storage.empty⟩

theorem cut0_world_rollback (pipeline : Roadmap.Pipeline) :
    (run pipeline (some 0)).2.2.ex = input.ex := by
  change (input.ex.apply (.account thisC (fun _ => prefund))).undo = input.ex
  exact ExecState.undo_apply input.ex _

/-- A separate nonempty constructor body exercises runCtorBody/runMods, not
just the initializer hook. The explicit initializer is now in its body. -/
def body : RBody E := ⟨[],[],false,[],[],
  .stmt (.expr (.assign (.state stateDecl variable_type rfl) initializer)) .nil,[]⟩
def bodyProgram : Program E := { program with
  inits := fun _ => []
  ctor := fun c => if c = "C" then some body else none }
def bodyGlobal (pipeline : Roadmap.Pipeline) : Glob E :=
  { global pipeline with prog := bodyProgram }
def runBody (pipeline : Roadmap.Pipeline) (cut : Option Nat) :=
  (deploy (plan := some (points cut)) (bodyGlobal pipeline) 20 "C" thisC user (word 0) []).run
    (L0 E,input)

theorem body_uncut (pipeline : Roadmap.Pipeline) :
    (runBody pipeline none).1 = .ok (.success []) ∧ value (runBody pipeline none).2.2 = some 42 := by
  cases pipeline <;> decide +kernel

theorem body_cut1 (pipeline : Roadmap.Pipeline) :
    (runBody pipeline (some 1)).1 = .ok (.revert []) ∧
      (runBody pipeline (some 1)).2.2.events = [prior,callEvent] ∧
      value (runBody pipeline (some 1)).2.2 = some 0 := by
  cases pipeline <;> decide +kernel

def ancestorPlan : Roadmap.Evm.FailurePoints where
  tx _ := .runs 257 none
  frame i := if i = 0 then some 1 else none

def ancestorInput : St E := { input with resource := Cursor.empty.enterFrame ancestorPlan }
def runAncestor (pipeline : Roadmap.Pipeline) :=
  (deploy (plan := some ancestorPlan) (global pipeline) 20 "C" thisC user (word 0) []).run
    (L0 E,ancestorInput)

theorem ancestor_stop_propagates (pipeline : Roadmap.Pipeline) :
    let result := runAncestor pipeline
    result.1 = .error (.revert []) ∧ result.2.2.events = [prior,callEvent] ∧
      result.2.2.resource.nextFrame = 2 ∧ result.2.2.resource.frames.length = 1 ∧
      result.2.2.resource.pending.map (fun stop => (stop.isFrame 0,stop.isRequest 0)) = some (true,false) ∧
      result.2.2.ex.journal.length = 1 ∧ (result.2.2.ex.world.accounts thisC).nonce = 0 := by
  cases pipeline <;> decide +kernel

def requestPlan : Roadmap.Evm.FailurePoints where
  tx _ := .runs 257 (some 1)
  frame _ := none

def requestInput : St E :=
  { input with resource := (Cursor.empty.enterRequest requestPlan rfl).2 }
def runRequest (pipeline : Roadmap.Pipeline) :=
  (deploy (plan := some requestPlan) (global pipeline) 20 "C" thisC user (word 0) []).run
    (L0 E,requestInput)

theorem request_stop_propagates (pipeline : Roadmap.Pipeline) :
    let result := runRequest pipeline
    result.1 = .error (.revert []) ∧ result.2.2.events = [prior,callEvent] ∧
      result.2.2.resource.nextRequest = 1 ∧ result.2.2.resource.nextFrame = 1 ∧
      result.2.2.resource.frames.isEmpty = true ∧
      result.2.2.resource.pending.map (fun stop => (stop.isRequest 0,stop.isFrame 0)) = some (true,false) ∧
      result.2.2.ex.journal.length = 1 ∧ (result.2.2.ex.world.accounts thisC).nonce = 0 := by
  cases pipeline <;> decide +kernel

end Solidity.Source.FailureExecution.ConstructorControls

/-- info: 'Solidity.Source.runInits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.runInits

/-- info: 'Solidity.Source.giveArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.giveArgs

/-- info: 'Solidity.Source.collectArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.collectArgs

/-- info: 'Solidity.Source.runCtorBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.runCtorBody

/-- info: 'Solidity.Source.construct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.construct

/-- info: 'Solidity.Source.deploy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.deploy

/-- info: 'Solidity.Source.FailureExecution.ConstructorControls.variable_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.ConstructorControls.variable_type

/-- info: 'Solidity.Source.FailureExecution.ConstructorControls.reader_signature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.ConstructorControls.reader_signature

/-- info: 'Solidity.Source.FailureExecution.ConstructorControls.uncut_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.ConstructorControls.uncut_value

/-- info: 'Solidity.Source.FailureExecution.ConstructorControls.uncut_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.ConstructorControls.uncut_frames

/-- info: 'Solidity.Source.FailureExecution.ConstructorControls.cut0_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.ConstructorControls.cut0_revert

/-- info: 'Solidity.Source.FailureExecution.ConstructorControls.cut1_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.ConstructorControls.cut1_revert

/-- info: 'Solidity.Source.FailureExecution.ConstructorControls.cut2_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.ConstructorControls.cut2_revert

/-- info: 'Solidity.Source.FailureExecution.ConstructorControls.cut1_root_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.ConstructorControls.cut1_root_state

/-- info: 'Solidity.Source.FailureExecution.ConstructorControls.cut2_events' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.ConstructorControls.cut2_events

/-- info: 'Solidity.Source.FailureExecution.ConstructorControls.uncut_events' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.ConstructorControls.uncut_events

/-- info: 'Solidity.Source.FailureExecution.ConstructorControls.cut0_world_rollback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.ConstructorControls.cut0_world_rollback

/-- info: 'Solidity.Source.FailureExecution.ConstructorControls.body_uncut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.ConstructorControls.body_uncut

/-- info: 'Solidity.Source.FailureExecution.ConstructorControls.body_cut1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.ConstructorControls.body_cut1

/-- info: 'Solidity.Source.FailureExecution.ConstructorControls.ancestor_stop_propagates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.ConstructorControls.ancestor_stop_propagates

/-- info: 'Solidity.Source.FailureExecution.ConstructorControls.request_stop_propagates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.ConstructorControls.request_stop_propagates
