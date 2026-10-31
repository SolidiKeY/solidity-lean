import Solidity.Backend.InternalFlow.PublishedDirectCalls
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
    some [77,260,256,256] := by decide +kernel

theorem wrong_scalar : words (Evm.run producer.code machine) [1] ≠
    some [77,33] := by decide +kernel

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
def prefixProducer : Calls.Program 1 (Frag.init []) callerPrefix :=
  (Calls.compile 1 (Frag.init []) callerPrefix).get (by decide +kernel)
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

#print axioms noRef
#print axioms initial_repr
#print axioms actual_execution
#print axioms exact_cost
#print axioms target_endpoint
#print axioms unified_input
#print axioms unified_agreement
#print axioms ordered_target
#print axioms source_identities
#print axioms caller_frame_insufficient
#print axioms wrong_alias
#print axioms wrong_scalar
#print axioms actual_failure
#print axioms failure_target
#print axioms payload_refused
#print axioms nonempty_caller
#print axioms evaluated_alias
#print axioms composed_cost
#print axioms nonempty_call_endpoint
#print axioms boundary_ordered_target
#print axioms boundary_export
#print axioms payload_source
#print axioms memory_path
#print axioms statement_endpoint
#print axioms call_endpoint
#print axioms statement_revert
#print axioms program_endpoint
end Solidity.Backend.InternalFlow.PublishedDirectCalls.Checks
