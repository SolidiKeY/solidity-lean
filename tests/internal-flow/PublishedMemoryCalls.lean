import tests.«internal-flow».AxiomReports
import Solidity.Backend.InternalFlow.TargetObservation
import Solidity.Backend.InternalFlow.PublishedDirectCalls
import Solidity.Backend.InternalFlow.SharedCallPrefix
import Solidity.Evm.Compiler
import Solidity.Syntax.Splice

/-! Inhabited consumer controls; elaboration is confined to this test fixture. -/
namespace Solidity.Backend.InternalFlow.PublishedDirectCalls.Checks
open Evm Evm.Memory

def C : Contract := contract!{
  function escape(uint[] memory a) returns (uint[] memory r) {
    uint[] memory owned = new uint[](2);
    owned[0] = 33;
    r = owned;
    a = new uint[](1);
    a[0] = 44;
  }
  function fail() { require(false); }
}
local instance : InContract := ⟨C⟩
def bases : Nat → Fin W := fun _ => wmod 0
def initial : State C [] := State.init C
def machine : Machine :=
  {Machine.init with stack := [w[77]], mem := fun a =>
    if a = 0 then w[256] else if a = 127 then w[99] else w[0]}

theorem noRef {R : RefTy} (r : HRef [] R) : False := by cases r.get?

/-- The public state and allocator inputs have the same concrete witness. -/
theorem initial_repr : StateRepr 1 1 128 (Frag.init []) initial bases machine ∧
    StructAllocatorRepr initial.heap bases 128 (wmod 256) machine := by
  have hh : HeapRepr initial.heap bases 128 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hs : StructHeapRepr initial.heap bases 128 machine :=
    ⟨fun r => (noRef r).elim, fun r => (noRef r).elim, fun r => (noRef r).elim⟩
  have hx : StructArraySeparated initial.heap bases := fun _ r => (noRef r).elim
  have hc : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos ⟨0, W_pos⟩)
      (Machine.init (fun _ => 0) ⟨0, W_pos⟩) := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
  refine ⟨⟨?_, hh, ?_, by decide, hs, hx, ?_⟩, ⟨⟨hh, ?_, fun r => (noRef r).elim⟩, hs, hx,
    fun r => (noRef r).elim⟩⟩
  · refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
    · intro p i; nomatch i
    · intro R i hi; nomatch i
    · intro R i hi; nomatch i
  · intro R i; nomatch i
  · intro s f R r hf; exact (noRef r).elim
  · refine ⟨by decide, by decide, rfl, ?_⟩
    intro a ha
    change 256 ≤ a at ha
    simp only [machine]
    split <;> rename_i he
    · omega
    · split <;> rename_i he
      · omega
      · rfl


def source : Prog C [] [.mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .val .uint] := (sol{
  uint marker = 42;
  uint[] memory xs = new uint[](2);
  xs[0] = 7; xs[1] = 11;
  uint[] memory same = xs;
  uint[] memory escaped = escape(xs);
  require(xs[0] == 7 && xs[1] == 11 && same[0] == 7 &&
    escaped[0] == 33 && escaped.length == 2 && marker == 42);
} : Prog C [] _)

def producer : Calls.Program 1 (Frag.init []) source :=
  (Calls.compile 1 (Frag.init []) source).get (by decide +kernel)
attribute [irreducible] producer

def compiled : Compiler.Compilation 1 (Frag.init []) source :=
  (Compiler.compile 1 (Frag.init []) source).get (by decide +kernel)
attribute [irreducible] compiled

private theorem actual_get {α : Type} (result : TRes α)
    (h : result.toOption.isSome = true) : result = .ok (result.toOption.get h) := by
  cases result with
  | error e => cases h
  | ok value => rfl

def output : Solidity.Out C [] [.mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .mem (.array (.prim .uint)), .val .uint] :=
  (source.run initial).toOption.get (by decide +kernel)

theorem actual_execution : source.run initial = .ok output :=
  actual_get (source.run initial) (by decide +kernel)

theorem exact_cost : producer.cost initial = 9 := by decide +kernel

theorem target_endpoint : ∃ m' base', Evm.run producer.code machine = .ok m' 0 ∧
    StateRepr 1 1 128 producer.frag output.st base' m' ∧ m'.stack = machine.stack ∧
    BaseExtends initial.H bases base' ∧
    GrowsAllocator 1 128 (producer.cost initial) initial bases machine output.st base' m' :=
  program_endpoint producer initial_repr.1 (by decide +kernel)
    (.inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩) output actual_execution

theorem unified_input : compiled.Input 1 128 bases initial machine := by
  apply (compiled.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem unified_agreement : compiled.Agrees 1 128 bases initial machine :=
  compiled.correct unified_input

def words (out : Evm.Out) (addresses : List Nat) : Option (List Nat) := do
  match out with
  | .ok m _ => (m.stack ++ addresses.map m.mem).mapM fun w => match w with
    | .val v => some v.val
    | .slot _ => none
  | _ => none

theorem ordered_target : words (Evm.run producer.code machine)
    [0,127,1,2,3,4,5,6,256,257,258,259,260,261,262,263,264] =
    some [77,265,99,42,256,256,256,260,260,2,7,11,0,2,33,0,1,44] := by decide +kernel

theorem source_identities :
    (output.st.H.length, output.st.env.1.map (fun r => r.id),
      output.st.env.2.1.map (fun r => r.id),
      output.st.env.2.2.1.map (fun r => r.id), output.st.env.2.2.2.2.2.1.1) =
    (4, some 2, some 2, some 0, 42) := by decide +kernel

theorem caller_frame_insufficient : ¬ 1 + producer.need ≤ 5 := by decide +kernel

theorem wrong_alias : words (Evm.run producer.code machine) [2,3,6] ≠
    some [77,260,256,256] := by
  have full := ordered_target
  generalize execution : Evm.run producer.code machine = out at full ⊢
  cases out with
  | revert => cases full
  | fault => cases full
  | ok m skip =>
    have snapshot := numeric_stack_cells m [0, 127, 1, 2, 3, 4, 5, 6, 256, 257, 258, 259, 260, 261, 262, 263, 264] [77] [265, 99, 42, 256, 256, 256, 260, 260, 2, 7, 11, 0, 2, 33, 0, 1, 44] rfl full
    have selected := congrArg (fun xs => [ xs[3]!, xs[4]!, xs[7]! ]) snapshot.2
    change [m.mem 2,m.mem 3,m.mem 6] = [observedWord 256,observedWord 256,observedWord 260] at selected
    change (m.stack ++ [m.mem 2,m.mem 3,m.mem 6]).mapM
      (fun w => match w with | Evm.Word.val v => some v.val | .slot _ => none) ≠ _
    rw [snapshot.1,selected]
    decide

theorem wrong_scalar : words (Evm.run producer.code machine) [1] ≠
    some [77,33] := by
  have full := ordered_target
  generalize execution : Evm.run producer.code machine = out at full ⊢
  cases out with
  | revert => cases full
  | fault => cases full
  | ok m skip =>
    have snapshot := numeric_stack_cells m [0, 127, 1, 2, 3, 4, 5, 6, 256, 257, 258, 259, 260, 261, 262, 263, 264] [77] [265, 99, 42, 256, 256, 256, 260, 260, 2, 7, 11, 0, 2, 33, 0, 1, 44] rfl full
    have selected := congrArg (fun xs => [ xs[2]! ]) snapshot.2
    change [m.mem 1] = [observedWord 42] at selected
    change (m.stack ++ [m.mem 1]).mapM
      (fun w => match w with | Evm.Word.val v => some v.val | .slot _ => none) ≠ _
    rw [snapshot.1,selected]
    decide

def failed : Prog C [] [.val .uint] := (sol{ uint marker = 42; fail(); } : Prog C [] _)
def failedProducer : Calls.Program 1 (Frag.init []) failed :=
  (Calls.compile 1 (Frag.init []) failed).get (by decide +kernel)
attribute [irreducible] failedProducer

theorem actual_failure : failed.run initial = .error .revert := rfl

theorem failure_target : Evm.run failedProducer.code machine = .revert := by
  rcases failedProducer.sound initial_repr.1 (by decide +kernel)
      (.inl (by decide +kernel)) with ⟨o,m,base,hs,_⟩ | ⟨_,ht⟩
  · rw [actual_failure] at hs
    contradiction
  · exact ht

def bytesFailure : Prog C [] [] := .cons (.revertData [.bytes [7]]) .nil

theorem payload_refused : (Calls.compile 1 (Frag.init []) bytesFailure).isSome = false :=
  by decide +kernel

abbrev A : RefTy := .array (.prim .uint)
abbrev Caller : Ctx := [.mem A, .mem A, .val .uint]
abbrev Input : Ctx := [.mem A, .mem A]
abbrev Final : Ctx := [.mem A, .mem A, .mem A, .val .uint]
def callerPrefix : Prog C [] Caller := (sol{
  uint marker = 42;
  uint[] memory xs = new uint[](2);
  xs[0] = 7; xs[1] = 11;
  uint[] memory same = xs;
} : Prog C [] Caller)
private def s0 : Stmt C [] [.val .uint] := .declLocal .uint (.user "marker") (some (.simple (.lit 42 rfl)))
private def s1 : Stmt C [.val .uint] [.mem A,.val .uint] := .declMem A (.user "xs") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl
private def s2 : Stmt C [.mem A,.val .uint] [.mem A,.val .uint] := .assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl))) (.val (.simple (.lit 7 rfl)))
private def s3 : Stmt C [.mem A,.val .uint] [.mem A,.val .uint] := .assignMem (.index .dyn (.var .here rfl) (.simple (.lit 1 rfl))) (.val (.simple (.lit 11 rfl)))
private def s4 : Stmt C [.mem A,.val .uint] Caller := .declMem A (.user "same") (some (.alias (.var .here rfl))) rfl rfl
private def h0 : CompiledStmt 1 (Frag.init []) s0 := ⟨_,_,.declare _ (.user "marker") _ _ (.core _ rfl)⟩
private def h1 : CompiledStmt 1 h0.frag s1 := ⟨_,_,.allocate _ .uint (.user "xs") (.lit 2 rfl) (by decide) rfl⟩
private def h2 : CompiledStmt 1 h1.frag s2 := ⟨_,_,.write _ .here rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩
private def h3 : CompiledStmt 1 h2.frag s3 := ⟨_,_,.write _ .here rfl _ _ _ _ (.core _ rfl) (.core _ rfl)⟩
private def h4 : CompiledStmt 1 h3.frag s4 := ⟨_,_,.declareAlias _ (.user "same") .here rfl⟩
private theorem h0_selected : Memory.compileStmt 1 (Frag.init []) s0 = some h0 := by rfl
private theorem h1_selected : Memory.compileStmt 1 h0.frag s1 = some h1 := by rfl
private theorem h2_selected : Memory.compileStmt 1 h1.frag s2 = some h2 := by rfl
private theorem h3_selected : Memory.compileStmt 1 h2.frag s3 = some h3 := by rfl
private theorem h4_selected : Memory.compileStmt 1 h3.frag s4 = some h4 := by rfl
private def done : CompiledProg 1 h4.frag (.nil : Prog C Caller Caller) := ⟨_,[],.nil _⟩
def prefixConstructed : CompiledProg 1 (Frag.init []) callerPrefix :=
 SharedCallPrefix.attach h0 (SharedCallPrefix.attach h1 (SharedCallPrefix.attach h2 (SharedCallPrefix.attach h3 (SharedCallPrefix.attach h4 done))))
theorem selected_constructed : Memory.compileProg 1 (Frag.init []) callerPrefix = some prefixConstructed := by
 exact SharedCallPrefix.compile_attach h0 _ h0_selected
  (SharedCallPrefix.compile_attach h1 _ h1_selected (SharedCallPrefix.compile_attach h2 _ h2_selected
   (SharedCallPrefix.compile_attach h3 _ h3_selected (SharedCallPrefix.compile_attach h4 _ h4_selected rfl))))
theorem selected_public : Calls.compile 1 (Frag.init []) callerPrefix = some (Calls.plain prefixConstructed) := by
 change (Memory.compileProg 1 (Frag.init []) callerPrefix).map Calls.plain = _
 rw [selected_constructed]
 rfl
def prefixProducer : Calls.Program 1 (Frag.init []) callerPrefix :=
  (Calls.compile 1 (Frag.init []) callerPrefix).get (by decide +kernel)
theorem prefix_constructor_eq : prefixProducer = Calls.plain prefixConstructed := by
 unfold prefixProducer
 exact SharedCallPrefix.get_some _ (by decide +kernel) _ selected_public

/-- Exact public admission and fields remain linked to the explicit checked
constructor data. The public compiler evidence is retained, not hidden. -/
theorem prefix_public_fields :
 (Calls.compile 1 (Frag.init []) callerPrefix).map
   (fun p => (p.code,p.frag,p.need,p.cost)) =
 some (prefixProducer.code,prefixProducer.frag,prefixProducer.need,prefixProducer.cost) := by
 rw [selected_public,prefix_constructor_eq]
 rfl

theorem prefix_getter (h : (Calls.compile 1 (Frag.init []) callerPrefix).isSome = true) :
 (Calls.compile 1 (Frag.init []) callerPrefix).get h = prefixProducer :=
 (SharedCallPrefix.get_some _ h _ selected_public).trans prefix_constructor_eq.symm

attribute [irreducible] prefixProducer
def caller : Solidity.Out C [] Caller := (callerPrefix.run initial).toOption.get (by decide +kernel)
def arguments : Args C Caller [.mem A] :=
  .snocMemory .nil A (.user "a") (.var (.there .here) rfl)
def values : TEnv C caller.st.H [.mem A] :=
  (arguments.evalT caller.st).toOption.get (by decide +kernel)
def ret : CallRet Caller [.mem A] Final := .mem A (.user "returned") rfl rfl
def body : Prog C Input (.mem A :: Input) :=
  .cons (.declMem A (.user "owned") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl)
    (.cons (.rebindMem (.there .here) (.alias (.var .here rfl))) .nil)
def expanded : Calls.Program 1 prefixProducer.frag
    (Calls.expandMem arguments A (.user "returned") rfl rfl body) :=
  (Calls.compile 1 prefixProducer.frag
    (Calls.expandMem arguments A (.user "returned") rfl rfl body)).get (by decide +kernel)
attribute [irreducible] expanded
def callProducer : Calls.Statement 1 prefixProducer.frag
    (.call "direct" arguments ret body) :=
  Calls.memoryReturn "direct" arguments A (.user "returned") rfl rfl body expanded
attribute [irreducible] callProducer
def entry : Solidity.Out C caller.st.H Input := ret.enterT (caller.st.withEnv values)
def bodyOutput : Solidity.Out C entry.st.H (.mem A :: Input) :=
  (body.runR entry.st).toOption.get (by decide +kernel)
def exported : Solidity.Out C caller.st.H Final :=
  ⟨bodyOutput.st.withEnv (ret.leaveT
    (TEnv.wk (entry.ext.trans bodyOutput.ext) Caller caller.st.env)
    (TEnv.take [.mem A] (TEnv.drop body.ext bodyOutput.st.env))), entry.ext.trans bodyOutput.ext⟩

theorem nonempty_caller : caller.st.H.length = 1 ∧
    (caller.st.env.1.map (fun r => r.id), caller.st.env.2.1.map (fun r => r.id),
     caller.st.env.2.2.1.1) = (some 0, some 0, 42) := by decide +kernel

theorem evaluated_alias : values.1.map (fun r => r.id) = some 0 := by decide +kernel

theorem composed_cost : prefixProducer.cost initial = 3 ∧ callProducer.cost caller.st = 4 :=
  by decide +kernel

/-- The intermediate representation is produced, not hypothesized. The second
BaseExtends ranges over the inhabited nonempty caller heap. Capacity is passed
through the published GrowsAllocator.nextInput law. -/
theorem nonempty_call_endpoint :
    ∃ m₁ base₁ m₂ base₂,
      Evm.run prefixProducer.code machine = .ok m₁ 0 ∧
      StateRepr 1 1 128 prefixProducer.frag caller.st base₁ m₁ ∧
      Evm.run callProducer.code m₁ = .ok m₂ 0 ∧
      StateRepr 1 1 128 callProducer.frag exported.st base₂ m₂ ∧
      m₂.stack = m₁.stack ∧ BaseExtends caller.st.H base₁ base₂ ∧
      GrowsAllocator 1 128 (callProducer.cost caller.st) caller.st base₁ m₁ exported.st base₂ m₂ := by
  have hp : callerPrefix.run initial = .ok caller :=
    actual_get (callerPrefix.run initial) (by decide +kernel)
  have whole : AllocationInput 1 128
      (prefixProducer.cost initial + callProducer.cost caller.st) initial bases machine :=
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩
  have firstCapacity : AllocationInput 1 128 (prefixProducer.cost initial) initial bases machine :=
    whole.of_le (Nat.le_add_right _ _)
  obtain ⟨m₁, base₁, ht, hr, hk, he, ha⟩ :=
    program_endpoint prefixProducer initial_repr.1 (by decide +kernel) firstCapacity caller hp
  obtain ⟨m₂, base₂, ht₂, hr₂, hk₂, he₂, ha₂⟩ :=
    call_endpoint "direct" arguments ret body callProducer caller.st values (actual_get (arguments.evalT caller.st) (by decide +kernel))
      bodyOutput (actual_get (body.runR entry.st) (by decide +kernel)) hr (by decide +kernel) (ha.nextInput whole)
  exact ⟨m₁, base₁, m₂, base₂, ht, hr, ht₂, hr₂, hk₂, he₂, ha₂⟩

theorem boundary_ordered_target : words
    (Evm.run (prefixProducer.code ++ callProducer.code) machine)
    [0,127,1,2,3,4,256,257,258,259,260,261,262] =
    some [77,263,99,42,256,256,260,2,7,11,0,2,0,0] := by decide +kernel

theorem boundary_export :
    (exported.st.H.length, exported.st.env.1.map (fun r => r.id),
      exported.st.env.2.1.map (fun r => r.id),
      exported.st.env.2.2.1.map (fun r => r.id), exported.st.env.2.2.2.1.1) =
    (3, some 2, some 0, some 0, 42) := by decide +kernel

theorem payload_source : bytesFailure.run initial = .error (.revertWith [7]) := rfl

theorem memory_path : compiled.isMemoryCalls = true ∧ compiled.usesMemory = true ∧
    compiled.isMemory = false := by decide +kernel

/-- Independently constructed data is the actual selected prefix, so the
SAME populated caller/call/export endpoint is retained. No midpoint is assumed. -/
theorem constructed_endpoint :
    ∃ m₁ base₁ m₂ base₂,
      Evm.run (Calls.plain prefixConstructed).code machine = .ok m₁ 0 ∧
      StateRepr 1 1 128 (Calls.plain prefixConstructed).frag caller.st base₁ m₁ ∧
      Evm.run callProducer.code m₁ = .ok m₂ 0 ∧
      StateRepr 1 1 128 callProducer.frag exported.st base₂ m₂ ∧
      m₂.stack = m₁.stack ∧ BaseExtends caller.st.H base₁ base₂ ∧
      GrowsAllocator 1 128 (callProducer.cost caller.st) caller.st base₁ m₁ exported.st base₂ m₂ := by
 rw [← prefix_constructor_eq]
 exact nonempty_call_endpoint

/-- The complete pre-existing ordered target observation, including private
physical cells, is unchanged by selecting the explicit constructor prefix. -/
theorem constructed_ordered (addresses : List Nat) :
 words (Evm.run ((Calls.plain prefixConstructed).code ++ callProducer.code) machine) addresses =
 words (Evm.run (prefixProducer.code ++ callProducer.code) machine) addresses := by
 rw [← prefix_constructor_eq]

#print_checked_axioms noRef,
  initial_repr,
  actual_execution,
  exact_cost,
  target_endpoint,
  unified_input,
  unified_agreement,
  ordered_target,
  source_identities,
  caller_frame_insufficient,
  wrong_alias,
  wrong_scalar,
  actual_failure,
  failure_target,
  payload_refused,
  nonempty_caller,
  evaluated_alias,
  composed_cost,
  nonempty_call_endpoint,
  boundary_ordered_target,
  boundary_export,
  payload_source,
  memory_path,
  statement_endpoint,
  call_endpoint,
  statement_revert,
  program_endpoint
#print axioms Solidity.Backend.InternalFlow.PublishedDirectCalls.Checks.constructed_endpoint
#print axioms Solidity.Backend.InternalFlow.PublishedDirectCalls.Checks.constructed_ordered
#print axioms Solidity.Backend.InternalFlow.PublishedDirectCalls.Checks.prefix_constructor_eq
#print axioms Solidity.Backend.InternalFlow.PublishedDirectCalls.Checks.selected_constructed
#print axioms Solidity.Backend.InternalFlow.PublishedDirectCalls.Checks.selected_public
#print axioms Solidity.Backend.InternalFlow.PublishedDirectCalls.Checks.prefix_public_fields
#print axioms Solidity.Backend.InternalFlow.PublishedDirectCalls.Checks.prefix_getter
end Solidity.Backend.InternalFlow.PublishedDirectCalls.Checks
