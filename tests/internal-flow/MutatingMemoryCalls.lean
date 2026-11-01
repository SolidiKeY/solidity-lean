import tests.«internal-flow».AxiomReports
import Solidity.Backend.InternalFlow.TargetObservation
import Solidity.Backend.InternalFlow.PublishedDirectCalls
import Solidity.Evm.Compiler
import Solidity.Calculus.RunFrameMem
import Solidity.Syntax.Splice

/-! Actual mutation through an older caller reference, return of that same
reference, private parameter rebinding, and subsequent caller alias use. -/
namespace Solidity.Backend.InternalFlow.MutatingCallChecks
open Evm Evm.Memory PublishedDirectCalls

def C : Contract := contract!{
  function mutate(uint[] memory a) returns (uint[] memory r) {
    a[0] = 19; r = a;
    a = new uint[](2); a[0] = 99; a[1] = 101;
  }
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

private theorem actual_get {α : Type} (result : TRes α)
    (h : result.toOption.isSome = true) : result = .ok (result.toOption.get h) := by
  cases result with
  | error e => cases h
  | ok value => rfl

abbrev A : RefTy := .array (.prim .uint)
abbrev Caller : Ctx := [.mem A, .mem A, .mem A, .val .uint]
abbrev Input : Ctx := [.mem A, .mem A]
abbrev Final : Ctx := [.mem A, .mem A, .mem A, .mem A, .val .uint]
def callerPrefix : Prog C [] Caller := (sol{
  uint marker = 42;
  uint[] memory xs = new uint[](2); xs[0] = 7; xs[1] = 11;
  uint[] memory same = xs;
  uint[] memory other = new uint[](3);
  other[0] = 23; other[1] = 29; other[2] = 31;
} : Prog C [] Caller)
def prefixProducer : Calls.Program 1 (Frag.init []) callerPrefix :=
  (Calls.compile 1 (Frag.init []) callerPrefix).get (by decide +kernel)
attribute [irreducible] prefixProducer
def caller : Solidity.Out C [] Caller := (callerPrefix.run initial).toOption.get (by decide +kernel)
def arguments : Args C Caller [.mem A] :=
  .snocMemory .nil A (.user "a") (.var (.there (.there .here)) rfl)
def values : TEnv C caller.st.H [.mem A] :=
  (arguments.evalT caller.st).toOption.get (by decide +kernel)
def ret : CallRet Caller [.mem A] Final := .mem A (.user "returned") rfl rfl

def write {Γ : Ctx} (i : Idx Γ (.mem A)) (index value : Simple C Γ .uint) : Stmt C Γ Γ :=
  .assignMem (.index .dyn (.var i rfl) (.simple index))
    (.val (.simple value))

def body : Prog C Input Input :=
  .cons (write (.there .here) (.lit 0 rfl) (.lit 19 rfl))
    (.cons (.rebindMem .here (.alias (.var (.there .here) rfl)))
      (.cons (.rebindMem (.there .here) (.newArr (.lit 2 rfl) rfl))
        (.cons (write (.there .here) (.lit 0 rfl) (.lit 99 rfl)) (.cons (write (.there .here) (.lit 1 rfl) (.lit 101 rfl)) .nil))))
def expanded : Calls.Program 1 prefixProducer.frag
    (Calls.expandMem arguments A (.user "returned") rfl rfl body) :=
  (Calls.compile 1 prefixProducer.frag
    (Calls.expandMem arguments A (.user "returned") rfl rfl body)).get (by decide +kernel)
attribute [irreducible] expanded
def callProducer : Calls.Statement 1 prefixProducer.frag (.call "mutate" arguments ret body) :=
  Calls.memoryReturn "mutate" arguments A (.user "returned") rfl rfl body expanded
attribute [irreducible] callProducer
def entry : Solidity.Out C caller.st.H Input := ret.enterT (caller.st.withEnv values)
def bodyOutput : Solidity.Out C entry.st.H Input :=
  (body.runR entry.st).toOption.get (by decide +kernel)
def exported : Solidity.Out C caller.st.H Final :=
  ⟨bodyOutput.st.withEnv (ret.leaveT (TEnv.wk (entry.ext.trans bodyOutput.ext) Caller caller.st.env)
    (TEnv.take [.mem A] (TEnv.drop body.ext bodyOutput.st.env))), entry.ext.trans bodyOutput.ext⟩
def nextUse : Prog C Final Final := .cons (write .here (.lit 1 rfl) (.lit 37 rfl)) .nil
def nextProducer : Calls.Program 1 callProducer.frag nextUse :=
  (Calls.compile 1 callProducer.frag nextUse).get (by decide +kernel)
attribute [irreducible] nextProducer
def finalOutput : Solidity.Out C exported.st.H Final :=
  (nextUse.run exported.st).toOption.get (by decide +kernel)


theorem actual_prefix : callerPrefix.run initial = .ok caller :=
  actual_get (callerPrefix.run initial) (by decide +kernel)
theorem actual_arguments : arguments.evalT caller.st = .ok values :=
  actual_get (arguments.evalT caller.st) (by decide +kernel)
theorem actual_body : body.runR entry.st = .ok bodyOutput :=
  actual_get (body.runR entry.st) (by decide +kernel)
theorem actual_call : (Stmt.call "mutate" arguments ret body).run caller.st = .ok exported :=
  InternalFlow.call_return arguments ret body.ext body.runR caller.st values actual_arguments bodyOutput actual_body
theorem actual_next : nextUse.run exported.st = .ok finalOutput := by
  unfold finalOutput
  exact actual_get (nextUse.run exported.st) (by decide +kernel)

def StageRepr (hp : Solidity.Out C [] Caller) (he : Solidity.Out C hp.st.H Final)
    (hn : Solidity.Out C he.st.H Final) (m₁ m₂ m₃ : Machine)
    (base₁ base₂ base₃ : Nat → Fin W) : Prop :=
  StateRepr 1 1 128 prefixProducer.frag hp.st base₁ m₁ ∧
  StateRepr 1 1 128 callProducer.frag he.st base₂ m₂ ∧
  StateRepr 1 1 128 nextProducer.frag hn.st base₃ m₃

/-- All intermediate representations come from real executions. -/
theorem represented_stages : ∃ m₁ base₁ m₂ base₂ m₃ base₃,
    Evm.run prefixProducer.code machine = .ok m₁ 0 ∧
    Evm.run callProducer.code m₁ = .ok m₂ 0 ∧
    Evm.run nextProducer.code m₂ = .ok m₃ 0 ∧
    StageRepr caller exported finalOutput m₁ m₂ m₃ base₁ base₂ base₃ ∧
    m₁.stack = machine.stack ∧ m₂.stack = m₁.stack ∧ m₃.stack = m₂.stack ∧
    BaseExtends caller.st.H base₁ base₂ ∧ BaseExtends exported.st.H base₂ base₃ ∧
    GrowsAllocator 1 128 (callProducer.cost caller.st) caller.st base₁ m₁ exported.st base₂ m₂ := by
  have whole : AllocationInput 1 128
      (prefixProducer.cost initial + callProducer.cost caller.st) initial bases machine :=
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩
  obtain ⟨m₁,base₁,ht₁,hr₁,hk₁,he₁,ha₁⟩ := program_endpoint prefixProducer initial_repr.1
    (by decide +kernel) (whole.of_le (Nat.le_add_right _ _)) caller actual_prefix
  have callRoom : 1 + callProducer.need ≤ 128 := by decide +kernel
  have callSpace : AllocationInput 1 128 (callProducer.cost caller.st) caller.st base₁ m₁ :=
    GrowsAllocator.nextInput (C := C) (Γ := []) (Δ := Caller) (b := 1) (frame := 128)
      (head := prefixProducer.cost initial) (tail := callProducer.cost caller.st)
      (σ := initial) (τ := caller.st) (base := bases) (base' := base₁)
      (m := machine) (m' := m₁) ha₁ whole
  obtain ⟨m₂,base₂,ht₂,hr₂,hk₂,he₂,ha₂⟩ :=
    statement_endpoint (L := 1) (frame := 128) (σ := caller.st) (base := base₁) (m := m₁)
      callProducer hr₁ callRoom callSpace exported actual_call
  have nextRoom : 1 + nextProducer.need ≤ 128 := by decide +kernel
  have nextSpace : AllocationInput 1 128 (nextProducer.cost exported.st) exported.st base₂ m₂ :=
    .inl (by decide +kernel)
  obtain ⟨m₃,base₃,ht₃,hr₃,hk₃,he₃,ha₃⟩ :=
    program_endpoint (L := 1) (frame := 128) (σ := exported.st) (base := base₂) (m := m₂)
      nextProducer hr₂ nextRoom nextSpace finalOutput actual_next
  exact ⟨m₁,base₁,m₂,base₂,m₃,base₃,ht₁,ht₂,ht₃,⟨hr₁,hr₂,hr₃⟩,hk₁,hk₂,hk₃,he₂,he₃,ha₂⟩

def complete : Prog C [] Final := callerPrefix.join (.cons (.call "mutate" arguments ret body) nextUse)
def compiled : Compiler.Compilation 1 (Frag.init []) complete :=
  (Compiler.compile 1 (Frag.init []) complete).get (by decide +kernel)
attribute [irreducible] compiled

theorem unified_input : compiled.Input 1 128 bases initial machine := by
  apply (compiled.memoryCalls_input (by decide +kernel) 1 128 bases initial machine).mpr
  exact ⟨initial_repr.1, by decide +kernel,
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩⟩
theorem unified_agreement : compiled.Agrees 1 128 bases initial machine :=
  compiled.correct unified_input

def arrayObject {H : HTy} (hp : Heap H) (id : Nat) : Option (List Int) :=
  if h : H[id]? = some A then
    let r : HRef H A := ⟨id, h⟩
    some ((hp.len r .dyn : Int) :: (MObj.elems .dyn (hp.get r)).map (fun v => v.1))
  else none

def contents {Γ : Ctx} (σ : State C Γ) : Option (List (List Int)) :=
  (List.range σ.H.length).mapM (arrayObject σ.heap)
def identity {H : HTy} (r : Option (HRef H A)) : Option Nat := r.map (fun r => r.id)

theorem source_prefix : (contents caller.st,
    identity caller.st.env.1, identity caller.st.env.2.1, identity caller.st.env.2.2.1,
    caller.st.env.2.2.2.1.1) =
    (some [[2,7,11],[3,23,29,31]], some 1, some 0, some 0, 42) := by decide +kernel

theorem source_entry : (contents entry.st, identity entry.st.env.1, identity entry.st.env.2.1) =
    (some [[2,7,11],[3,23,29,31],[0]], some 2, some 0) := by decide +kernel

theorem source_body : (contents bodyOutput.st, identity bodyOutput.st.env.1, identity bodyOutput.st.env.2.1) =
    (some [[2,19,11],[3,23,29,31],[0],[2,99,101]], some 0, some 3) := by decide +kernel

theorem source_export : (contents exported.st, identity exported.st.env.1,
    identity exported.st.env.2.1, identity exported.st.env.2.2.1,
    identity exported.st.env.2.2.2.1, exported.st.env.2.2.2.2.1.1) =
    (some [[2,19,11],[3,23,29,31],[0],[2,99,101]], some 0, some 1, some 0, some 0, 42) := by decide +kernel

theorem source_next : (contents finalOutput.st, identity finalOutput.st.env.1,
    identity finalOutput.st.env.2.1, identity finalOutput.st.env.2.2.1,
    identity finalOutput.st.env.2.2.2.1, finalOutput.st.env.2.2.2.2.1.1) =
    (some [[2,19,37],[3,23,29,31],[0],[2,99,101]], some 0, some 1, some 0, some 0, 42) := by decide +kernel

def words (out : Evm.Out) (addresses : List Nat) : Option (List Nat) := do
  match out with
  | .ok m _ => (m.stack ++ addresses.map m.mem).mapM fun w => match w with
    | .val v => some v.val
    | .slot _ => none
  | _ => none

theorem target_prefix : words (Evm.run prefixProducer.code machine)
    [0,127,1,2,3,4,256,257,258,259,260,261,262] =
    some [77,263,99,42,256,256,259,2,7,11,3,23,29,31] := by decide +kernel

theorem target_private_body : words (Evm.run (prefixProducer.code ++ expanded.code) machine)
    [0,127,1,2,3,4,5,6,256,257,258,259,260,261,262,263,264,265,266] =
    some [77,267,99,42,256,256,259,264,256,2,19,11,3,23,29,31,0,2,99,101] := by decide +kernel

theorem target_export : words (Evm.run (prefixProducer.code ++ callProducer.code) machine)
    [0,127,1,2,3,4,5,256,257,258,259,260,261,262,263,264,265,266] =
    some [77,267,99,42,256,256,259,256,2,19,11,3,23,29,31,0,2,99,101] := by decide +kernel

theorem target_next : words (Evm.run (prefixProducer.code ++ callProducer.code ++ nextProducer.code) machine)
    [0,127,1,2,3,4,5,256,257,258,259,260,261,262,263,264,265,266] =
    some [77,267,99,42,256,256,259,256,2,19,37,3,23,29,31,0,2,99,101] := by decide +kernel

theorem exact_frame_cost :
    [prefixProducer.need, callProducer.need, nextProducer.need, compiled.requiredFrame,
      prefixProducer.cost initial, callProducer.cost caller.st, nextProducer.cost exported.st,
      compiled.allocationCost initial] = [4,6,5,6,7,4,0,11] := by decide +kernel

theorem wrong_same_typed_identity : identity exported.st.env.1 ≠ some 1 := by
  rw [show identity exported.st.env.1 = some 0 from congrArg (fun x => x.2.1) source_export]
  decide

theorem missing_callee_mutation : contents exported.st ≠
    some [[2,7,11],[3,23,29,31],[0],[2,99,101]] := by
  rw [show contents exported.st = some [[2,19,11],[3,23,29,31],[0],[2,99,101]] from congrArg Prod.fst source_export]
  decide

theorem unrelated_object_mutation : contents finalOutput.st ≠
    some [[2,19,37],[3,19,29,31],[0],[2,99,101]] := by
  rw [show contents finalOutput.st = some [[2,19,37],[3,23,29,31],[0],[2,99,101]] from congrArg Prod.fst source_next]
  decide

theorem private_rebind_escape : identity exported.st.env.1 ≠ some 3 := by
  rw [show identity exported.st.env.1 = some 0 from congrArg (fun x => x.2.1) source_export]
  decide

theorem wrong_composed_cost : compiled.allocationCost initial ≠ 12 := by
  rw [show compiled.allocationCost initial = 11 from congrArg (fun xs => xs[7]!) exact_frame_cost]
  decide

theorem mutator_not_withinM : Prog.withinM .view body = false := rfl

private theorem some_ref_of_id {H : HTy} (v : Option (HRef H A)) (r : HRef H A)
    (h : v.map (fun s => s.id) = some r.id) : v = some r := by
  cases v with
  | none => cases h
  | some s =>
    have same : s.id = r.id := Option.some.inj h
    have eq : s = r := by cases s; cases r; cases same; rfl
    exact congrArg some eq

def older : HRef caller.st.H A := ⟨0, by decide +kernel⟩
def unrelated : HRef caller.st.H A := ⟨1, by decide +kernel⟩

/-- The actual mutated contents are represented at the unchanged old address;
the distinct object's unchanged contents come from source_export, not Keeps. -/
theorem represented_old_objects : ∃ m₁ base₁ m₂ base₂,
    Evm.run prefixProducer.code machine = .ok m₁ 0 ∧
    Evm.run callProducer.code m₁ = .ok m₂ 0 ∧
    m₂.stack = m₁.stack ∧
    StateRepr 1 1 128 prefixProducer.frag caller.st base₁ m₁ ∧
    StateRepr 1 1 128 callProducer.frag exported.st base₂ m₂ ∧
    m₂.mem (cellOf 1 (Idx.here : Idx Final (.mem A))) = .val (base₁ older.id) ∧
    m₂.mem (cellOf 1 (Idx.there (Idx.there Idx.here) : Idx Final (.mem A))) = .val (base₁ older.id) ∧
    ArrayRepr exported.st.heap (older.wk exported.ext) (base₁ older.id) m₂ ∧
    ArrayRepr exported.st.heap (unrelated.wk exported.ext) (base₁ unrelated.id) m₂ := by
  obtain ⟨m₁,base₁,m₂,base₂,m₃,base₃,ht₁,ht₂,ht₃,hr,hk₁,hk₂,hk₃,he₂,he₃,ha₂⟩ := represented_stages
  have returned : TEnv.get (.here : Idx Final (.mem A)) exported.st.env = some (older.wk exported.ext) :=
    some_ref_of_id (TEnv.get (.here : Idx Final (.mem A)) exported.st.env) (older.wk exported.ext) (by decide +kernel)
  have shared : TEnv.get (.there (.there .here) : Idx Final (.mem A)) exported.st.env = some (older.wk exported.ext) :=
    some_ref_of_id (TEnv.get (.there (.there .here) : Idx Final (.mem A)) exported.st.env) (older.wk exported.ext) (by decide +kernel)
  exact ⟨m₁,base₁,m₂,base₂,ht₁,ht₂,hk₂,hr.1,hr.2.1,
    old_alias_at_entry_address exported hr.2.1 he₂ older .here returned,
    old_alias_at_entry_address exported hr.2.1 he₂ older (.there (.there .here)) shared,
    old_array_at_entry_address exported hr.2.1 he₂ older,
    old_array_at_entry_address exported hr.2.1 he₂ unrelated⟩

theorem public_target_next : words (Evm.run compiled.code machine)
    [0,127,1,2,3,4,5,256,257,258,259,260,261,262,263,264,265,266] =
    some [77,267,99,42,256,256,259,256,2,19,37,3,23,29,31,0,2,99,101] := by decide +kernel

theorem complete_source_observations : (complete.run initial).toOption.map (fun o => contents o.st) =
    some (some [[2,19,37],[3,23,29,31],[0],[2,99,101]]) := by decide +kernel

theorem complete_source_identities : (complete.run initial).toOption.map (fun o =>
    [identity o.st.env.1, identity o.st.env.2.1, identity o.st.env.2.2.1,
      identity o.st.env.2.2.2.1, some o.st.env.2.2.2.2.1.1.toNat]) =
    some [some 0,some 1,some 0,some 0,some 42] := by decide +kernel

theorem complete_success : (complete.run initial).halt? = none := by decide +kernel

theorem wrong_target_return : words (Evm.run compiled.code machine) [5] ≠ some [77,259] := by
  have full := public_target_next
  generalize execution : Evm.run compiled.code machine = out at full ⊢
  cases out with
  | revert => cases full
  | fault => cases full
  | ok m skip =>
    have snapshot := numeric_stack_cells m [0, 127, 1, 2, 3, 4, 5, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266] [77] [267, 99, 42, 256, 256, 259, 256, 2, 19, 37, 3, 23, 29, 31, 0, 2, 99, 101] rfl full
    have selected := congrArg (fun xs => [ xs[6]! ]) snapshot.2
    change [m.mem 5] = [observedWord 256] at selected
    change (m.stack ++ [m.mem 5]).mapM
      (fun w => match w with | Evm.Word.val v => some v.val | .slot _ => none) ≠ _
    rw [snapshot.1,selected]
    decide

theorem missing_target_mutation : words (Evm.run compiled.code machine) [257] ≠ some [77,7] := by
  have full := public_target_next
  generalize execution : Evm.run compiled.code machine = out at full ⊢
  cases out with
  | revert => cases full
  | fault => cases full
  | ok m skip =>
    have snapshot := numeric_stack_cells m [0, 127, 1, 2, 3, 4, 5, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266] [77] [267, 99, 42, 256, 256, 259, 256, 2, 19, 37, 3, 23, 29, 31, 0, 2, 99, 101] rfl full
    have selected := congrArg (fun xs => [ xs[8]! ]) snapshot.2
    change [m.mem 257] = [observedWord 19] at selected
    change (m.stack ++ [m.mem 257]).mapM
      (fun w => match w with | Evm.Word.val v => some v.val | .slot _ => none) ≠ _
    rw [snapshot.1,selected]
    decide

theorem unrelated_target_mutation : words (Evm.run compiled.code machine) [260] ≠ some [77,19] := by
  have full := public_target_next
  generalize execution : Evm.run compiled.code machine = out at full ⊢
  cases out with
  | revert => cases full
  | fault => cases full
  | ok m skip =>
    have snapshot := numeric_stack_cells m [0, 127, 1, 2, 3, 4, 5, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266] [77] [267, 99, 42, 256, 256, 259, 256, 2, 19, 37, 3, 23, 29, 31, 0, 2, 99, 101] rfl full
    have selected := congrArg (fun xs => [ xs[11]! ]) snapshot.2
    change [m.mem 260] = [observedWord 23] at selected
    change (m.stack ++ [m.mem 260]).mapM
      (fun w => match w with | Evm.Word.val v => some v.val | .slot _ => none) ≠ _
    rw [snapshot.1,selected]
    decide

theorem private_target_escape : words (Evm.run compiled.code machine) [5] ≠ some [77,264] := by
  have full := public_target_next
  generalize execution : Evm.run compiled.code machine = out at full ⊢
  cases out with
  | revert => cases full
  | fault => cases full
  | ok m skip =>
    have snapshot := numeric_stack_cells m [0, 127, 1, 2, 3, 4, 5, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266] [77] [267, 99, 42, 256, 256, 259, 256, 2, 19, 37, 3, 23, 29, 31, 0, 2, 99, 101] rfl full
    have selected := congrArg (fun xs => [ xs[6]! ]) snapshot.2
    change [m.mem 5] = [observedWord 256] at selected
    change (m.stack ++ [m.mem 5]).mapM
      (fun w => match w with | Evm.Word.val v => some v.val | .slot _ => none) ≠ _
    rw [snapshot.1,selected]
    decide

theorem wrong_target_cursor : words (Evm.run compiled.code machine) [0] ≠ some [77,268] := by
  have full := public_target_next
  generalize execution : Evm.run compiled.code machine = out at full ⊢
  cases out with
  | revert => cases full
  | fault => cases full
  | ok m skip =>
    have snapshot := numeric_stack_cells m [0, 127, 1, 2, 3, 4, 5, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266] [77] [267, 99, 42, 256, 256, 259, 256, 2, 19, 37, 3, 23, 29, 31, 0, 2, 99, 101] rfl full
    have selected := congrArg (fun xs => [ xs[0]! ]) snapshot.2
    change [m.mem 0] = [observedWord 267] at selected
    change (m.stack ++ [m.mem 0]).mapM
      (fun w => match w with | Evm.Word.val v => some v.val | .slot _ => none) ≠ _
    rw [snapshot.1,selected]
    decide


/-- Observation through the actual published typed value evaluation. -/
def observeRead {Γ : Ctx} (σ : State C Γ) (i : Idx Γ (.mem A))
    (index : Simple C Γ .uint) : Option Int :=
  ((Val.readMem (.index .dyn (.var i rfl) (.simple index)) : Val C Γ .uint).evalT σ).toOption.map (fun v => v.1)

theorem prefix_alias_reads :
    [observeRead caller.st (.there (.there .here)) (.lit 0 rfl),
     observeRead caller.st (.there .here) (.lit 0 rfl),
     observeRead caller.st .here (.lit 0 rfl)] = [some 7,some 7,some 23] := by decide +kernel

theorem private_body_reads :
    [observeRead bodyOutput.st .here (.lit 0 rfl),
     observeRead bodyOutput.st (.there .here) (.lit 0 rfl),
     observeRead bodyOutput.st (.there .here) (.lit 1 rfl)] = [some 19,some 99,some 101] := by decide +kernel

theorem exported_alias_reads :
    [observeRead exported.st .here (.lit 0 rfl),
     observeRead exported.st (.there .here) (.lit 0 rfl),
     observeRead exported.st (.there (.there .here)) (.lit 0 rfl),
     observeRead exported.st (.there (.there (.there .here))) (.lit 0 rfl)] =
    [some 19,some 23,some 19,some 19] := by decide +kernel

theorem next_alias_reads :
    [observeRead finalOutput.st .here (.lit 1 rfl),
     observeRead finalOutput.st (.there .here) (.lit 1 rfl),
     observeRead finalOutput.st (.there (.there .here)) (.lit 1 rfl),
     observeRead finalOutput.st (.there (.there (.there .here))) (.lit 1 rfl)] =
    [some 37,some 29,some 37,some 37] := by decide +kernel
#print_checked_axioms noRef,
  initial_repr,
  actual_prefix,
  actual_arguments,
  actual_body,
  actual_call,
  actual_next,
  represented_stages,
  unified_input,
  unified_agreement,
  source_prefix,
  source_entry,
  source_body,
  source_export,
  source_next,
  target_prefix,
  target_private_body,
  target_export,
  target_next,
  exact_frame_cost,
  wrong_same_typed_identity,
  missing_callee_mutation,
  unrelated_object_mutation,
  private_rebind_escape,
  wrong_composed_cost,
  mutator_not_withinM,
  represented_old_objects,
  public_target_next,
  complete_source_observations,
  complete_source_identities,
  complete_success,
  wrong_target_return,
  missing_target_mutation,
  unrelated_target_mutation,
  private_target_escape,
  wrong_target_cursor,
  prefix_alias_reads,
  private_body_reads,
  exported_alias_reads,
  next_alias_reads,
  old_alias_at_entry_address,
  old_array_at_entry_address
end Solidity.Backend.InternalFlow.MutatingCallChecks
