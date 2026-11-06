import Solidity.Lowering.V07.SourceReads
import Solidity.Lowering.V08.SourcePayableDeploymentControls

/-! A hand-written scalar `Cell` constructor fixture over the V07 scalar relation
(`admitted_construct` does not use the admission premises; it re-wraps
`selected_construct`).
Typed constructor-selection and frame INPUT certificates are independent of its
execution conclusions. No canonical admission/body/heap/runtime proof is inferred. -/
namespace Solidity.Lowering.V08.ConstructorScalarTransport
open Solidity Source
open Solidity.Lowering.V07

def savedSyntax : Syn (.part false) :=
  .stateVar Source.Examples.u256 none none none false "saved" .none
def params : Syn (.list .param) := .cons (.param Source.Examples.u256 none (some "n")) .nil
def unit : Syn .unit := .unit (.cons (.contract false "Cell" .none .nil
  (.cons savedSyntax (.cons (.constructor params .nil true none (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.assign .assign (.ident "saved") (.ident "n"))))) .nil))) .nil))) .nil)
def E : Source.Env := unit.env
def savedDecl : Source.Decl := ⟨.stateVar,"saved",some "Cell",false,savedSyntax⟩
def body : Source.RBody E :=
  ⟨[.int Source.IntTy.u256],[],false,[.int Source.IntTy.u256],[.int Source.IntTy.u256],
    .stmt (.expr (.assign (.state savedDecl rfl rfl) (.local .here))) .nil,[]⟩
def program : Source.Program E :=
  {body:=fun _ => none,consts:=fun _ => none,inits:=fun _ => [],
    ctor:=fun c => if c="Cell" then some body else none,
    ctorLocals:=fun _ => [.int Source.IntTy.u256],baseArgs:=fun _ => [],contracts:=["Cell"]}

/-- A producer must select this exact intrinsic Source program; no run equality
or preservation theorem is a field. Canonical resolution/admission is separate. -/
structure ConstructorSelection (g : Source.Glob E) : Prop where
  selected : g.prog = program

/-- Exact frame input agreement, not a post-state or body-preservation axiom. -/
structure FrameInputs (f : Source.Fr) (self : ContractWorld.Address) (c : ContractWorld.Context) : Prop where
  address : f.this.val = self.1.1.toNat
  sender : f.sender.val = c.sender.1.1.toNat
  value : f.value.val = c.value.1.toNat
  static : f.static = c.isStatic

def word (n : Nat) (h : n < 2^256 := by decide +kernel) : Roadmap.Word := ⟨n,h⟩
def global (p : Roadmap.Pipeline) : Source.Glob E :=
  {prog:=program,pipeline:=p,fixed:=Source.SemanticsExamples.toyFixed,
    balance0:=fun _ => word 93,hasCode:=fun _ _ => false,
    callee:=fun _ => .answer (.success []),timestamp:=word 0}
def frame : Source.Fr :=
  {this:=SourcePayableDeploymentControls.self,sender:=SourcePayableDeploymentControls.sender,
    value:=word 7,static:=false,contract:="Cell"}
abbrev range (n : Int) := Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi
def locals (n : Int) (h : range n) : Source.Locals E.layout [.int Source.IntTy.u256] :=
  .cons (.int n h) .nil

def initial (bytes : Roadmap.Bytes) : Source.St E :=
  {Source.St.init E with
    ex:=(Source.St.init E).ex.run [
      .account frame.sender (fun a => {a with balance:=word 93,nonce:=3}),
      .account frame.this (fun a => {a with balance:=word 12,nonce:=1})]
    heap:=(Source.Heap.empty.alloc ⟨.bytes .memory,.bytes bytes⟩).1
    events:=[.call frame.sender (word 7) bytes false]
    logs:=[(frame.this,bytes),(frame.sender,[0,255])]
    fnLocals:=⟨[.bool],.cons (.bool true) .nil⟩}
def written (bytes : Roadmap.Bytes) (n : Int) (h : range n) : Source.St E :=
  {initial bytes with ex:=(initial bytes).ex.apply (.account frame.this
    (fun a => {a with storage:=a.storage.write savedDecl.path (.int n h)}))}

theorem selected (p : Roadmap.Pipeline) : ConstructorSelection (global p) := ⟨rfl⟩

theorem source_construct (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes)
    (n : Int) (h : range n) :
    (Source.construct (global p) frame (extra+8) "Cell" (locals n h)).run
      (Source.L0 E,initial bytes) = (.ok (),(Source.L0 E,written bytes n h)) := by
  cases p <;> rfl

def selectedLocals (g : Source.Glob E) (selection : ConstructorSelection g)
    (n : Int) (h : range n) : Source.Locals E.layout (g.prog.ctorLocals "Cell") :=
  (show [.int Source.IntTy.u256] = g.prog.ctorLocals "Cell" from by rw [selection.selected]; rfl) ▸ locals n h

theorem selected_construct (g : Source.Glob E) (selection : ConstructorSelection g)
    (extra : Nat) (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    (Source.construct g frame (extra+8) "Cell" (selectedLocals g selection n h)).run
      (Source.L0 E,initial bytes) = (.ok (),(Source.L0 E,written bytes n h)) := by
  rcases g with ⟨prog,p,fixed,balance0,hasCode,callee,timestamp⟩
  rcases selection with ⟨selected⟩
  dsimp only at selected
  subst prog
  cases p <;> rfl

/-- P8 consumer input: actual approved SourceSpec meaning at its EXISTING
program carrier. No execution equality, new admission bound or target
preservation is assumed. Whether P8 supplies this carrier/binding stays open. -/
structure AdmissionInputs (S : Roadmap.SourceSpec) (resolved : S.Resolved)
    (artifact : Roadmap.Artifact) (g : Source.Glob E) : Prop where
  wellFormed : S.WellFormed resolved
  inProfile : S.InProfile resolved
  programType : S.lang.Prog = Source.SrcProg E
  bound : g.prog = (Eq.mp programType (S.meaning resolved wellFormed inProfile artifact)).prog
  selected : (Eq.mp programType (S.meaning resolved wellFormed inProfile artifact)).prog = program

theorem admitted_construct (S : Roadmap.SourceSpec) (resolved : S.Resolved)
    (artifact : Roadmap.Artifact) (g : Source.Glob E) (inputs : AdmissionInputs S resolved artifact g)
    (extra : Nat) (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    (Source.construct g frame (extra+8) "Cell"
      (selectedLocals g ⟨inputs.bound.trans inputs.selected⟩ n h)).run
      (Source.L0 E,initial bytes) = (.ok (),(Source.L0 E,written bytes n h)) :=
  selected_construct g _ extra bytes n h

/-- The constructor argument's scalar relation is supplied by the REAL V07 law. -/
theorem argument_related (n : Int) (h : range n) :
    IntValueRel Source.IntTy.u256 (.int n h : Source.Val E.layout (.int Source.IntTy.u256))
      (integerValue Source.IntTy.u256 n h) := integer_related _ _ _

def Cell : Contract := contract!{ uint saved; constructor(uint n) payable { saved = n; } }
def catalog : Unit → Contract := fun _ => Cell
def targetInitial : ContractWorld.World catalog := ContractWorld.World.empty catalog
  (fun a => if a=Controls.sender then ⟨93,by decide +kernel⟩
    else if a=Controls.self then ⟨5,by decide +kernel⟩ else ⟨0,by decide +kernel⟩)
def targetBody (n : Int) (h : range n) : Prog Cell [] [] :=
  .cons (.assign (.root "saved" rfl)
    (.val (.simple (.lit n (integer_range Source.IntTy.u256 n h))))) .nil
def targetContext : ContractWorld.Context :=
  {sender:=Controls.sender,mode:=.ordinary ⟨7,by decide +kernel⟩}
def targetRun (n : Int) (h : range n) := targetInitial.create () Controls.self (targetBody n h) targetContext

theorem frame_inputs : FrameInputs frame Controls.self targetContext := ⟨rfl,rfl,rfl,rfl⟩

def targetObservation (n : Int) (h : range n) : Option (Nat × Option Int × Bool) := do
  let (world,ref) ← (targetRun n h).toOption
  let store ← world.storage? ref
  let .prim value ← store.find (SRef.ofRoot "saved" rfl)
  pure ((world.balance Controls.self).1.toNat,PrimTy.num? value,(world.accounts Controls.self).isSome)

def entered : State Cell [] :=
  {storage:=Storage.init Cell,H:=[],heap:=Heap.empty,env:=(),
    selfBalance:=⟨12,by decide +kernel⟩,net:=[(Controls.sender.1,7)],
    tx:=targetContext.tx targetInitial Controls.self}
def targetStore (n : Int) (h : range n) : Storage Cell :=
  ((Storage.init Cell).write (SRef.ofRoot "saved" rfl)
    (.prim (integerValue Source.IntTy.u256 n h))).getD (Storage.init Cell)
def targetWritten (n : Int) (h : range n) : State Cell [] := {entered with storage:=targetStore n h}
def targetNext (n : Int) (h : range n) : ContractWorld.World catalog :=
  {targetInitial with
    accounts:=fun a => if a=Controls.self then some ⟨(),targetStore n h⟩ else none
    funds:=fun a => if a=Controls.self then ⟨12,by decide +kernel⟩ else
      if a=Controls.sender then ⟨86,by decide +kernel⟩ else targetInitial.funds a}

theorem entry_actual : targetInitial.enter (k:=()) Controls.self targetContext (Storage.init Cell) true =
    .ok entered := by rfl

theorem body_actual (n : Int) (h : range n) :
    (targetBody n h).run entered = .ok ⟨targetWritten n h,List.prefix_refl _⟩ := by
  unfold targetBody
  rfl

theorem settlement_actual :
    ContractWorld.settle targetInitial.funds Controls.self [(Controls.sender.1,7)] =
      .ok (fun a => if a=Controls.sender then ⟨86,by decide +kernel⟩ else targetInitial.funds a) := by
  have different : Controls.sender.1 ≠ Controls.self.1 := by decide +kernel
  have address : ContractWorld.Address.ofWord? Controls.sender.1 = some Controls.sender := by decide +kernel
  have balance : PrimTy.ofInt? .uint ((targetInitial.funds Controls.sender).1 - 7) =
      some (show PrimTy.uint.Denote from ⟨86,by decide +kernel⟩) := by decide +kernel
  unfold ContractWorld.settle
  rw [ContractWorld.settle.go.eq_2]
  rw [if_neg (show ¬ (Controls.sender.1 ∈ ([] : List ContractWorld.Word) ∨
    Controls.sender.1 = Controls.self.1) from fun h => h.elim List.not_mem_nil different)]
  rw [address]
  have someAddress : TRes.ofOpt (some Controls.sender) = Except.ok Controls.sender := rfl
  rw [someAddress]
  change (do
    let value ← TRes.ofOpt (PrimTy.ofInt? .uint ((targetInitial.funds Controls.sender).1 - 7))
    pure (fun a => if a=Controls.sender then value else targetInitial.funds a)) = _
  rw [balance]
  rfl

theorem finish_actual (n : Int) (h : range n) :
    targetInitial.finish (k:=()) Controls.self (targetWritten n h) = .ok (targetNext n h) := by
  unfold ContractWorld.World.finish
  rw [show (targetWritten n h).net = [(Controls.sender.1,7)] from rfl,settlement_actual]
  rfl

theorem creation_actual (n : Int) (h : range n) :
    targetRun n h = .ok (targetNext n h,⟨Controls.self⟩) := by
  change (do
    let state ← targetInitial.enter (k:=()) Controls.self targetContext (Storage.init Cell) true
    let output ← (targetBody n h).run state
    let next ← targetInitial.finish (k:=()) Controls.self output.st
    pure (next,(⟨Controls.self⟩ : ContractWorld.Handle ()))) = _
  rw [entry_actual]
  simp only [bind,Except.bind,body_actual,finish_actual]
  rfl

theorem target_created (n : Int) (h : range n) :
    targetObservation n h = some (12,some n,true) := by
  unfold targetObservation
  rw [creation_actual]
  rfl

def sourceObservation (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    Option (Nat × Option Int) := do
  let result := (Source.construct (global p) frame 8 "Cell" (locals n h)).run
    (Source.L0 E,initial bytes)
  match result.1 with
  | .ok () =>
    let value ← (result.2.2.ex.world.accounts frame.this).storage.read savedDecl.path
    pure ((result.2.2.ex.world.accounts frame.this).balance,value.key)
  | _ => none

/-- Shared numeric balance/value observation only. Target installation is
proved separately; Source.construct does not install code. -/
theorem constructor_value_transport (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes)
    (n : Int) (h : range n) : sourceObservation p bytes n h = (targetObservation n h).map (fun x => (x.1,x.2.1)) := by
  unfold sourceObservation
  rw [source_construct p 0 bytes,target_created]
  rfl

theorem retained_machine (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    (written bytes n h).heap = (initial bytes).heap ∧
    (written bytes n h).events = (initial bytes).events ∧
    (written bytes n h).logs = (initial bytes).logs ∧
    (written bytes n h).fnLocals = (initial bytes).fnLocals ∧
    (written bytes n h).ex.journal.length = 3 := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem wrong_argument (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    sourceObservation p bytes 7 (by decide +kernel) ≠ (targetObservation 8 (by decide +kernel)).map (fun x => (x.1,x.2.1)) := by
  rw [constructor_value_transport,target_created,target_created]
  intro wrong
  cases wrong

theorem timeout (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    (Source.construct (global p) frame 0 "Cell" (locals n h)).run (Source.L0 E,initial bytes) =
      (.error .timeout,(Source.L0 E,initial bytes)) := by cases p <;> rfl

/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.admitted_construct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms admitted_construct
/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.settlement_actual' depends on axioms: [propext] -/
#guard_msgs in
#print axioms settlement_actual
/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.entry_actual' depends on axioms: [propext] -/
#guard_msgs in
#print axioms entry_actual
/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.body_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms body_actual
/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.finish_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms finish_actual
/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.creation_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms creation_actual
/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.selected_construct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected_construct
/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms selected
/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.source_construct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_construct
/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.argument_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms argument_related
/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.frame_inputs' does not depend on any axioms -/
#guard_msgs in
#print axioms frame_inputs
/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.target_created' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_created
/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.constructor_value_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms constructor_value_transport
/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.retained_machine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms retained_machine
/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.wrong_argument' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_argument
/-- info: 'Solidity.Lowering.V08.ConstructorScalarTransport.timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms timeout
end Solidity.Lowering.V08.ConstructorScalarTransport
