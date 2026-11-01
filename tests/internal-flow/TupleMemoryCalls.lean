import tests.«internal-flow».AxiomReports
import Solidity.Backend.InternalFlow.TargetObservation
import Solidity.Backend.InternalFlow.TuplePrograms
import Solidity.Evm.Compiler
import Solidity.Calculus.RunFrameMem
import Solidity.Syntax.Splice

/-! A real three-result direct call. Binders is primitive-only, while arguments,
caller aliases and private body objects use the published typed memory model. -/
namespace Solidity.Backend.InternalFlow.TupleCallChecks
open Evm Evm.Memory PublishedDirectCalls TupleCalls

def C : Contract := contract!{
  function triple(uint[] memory a, uint seed) returns (uint lo, uint hi, bool flag) {
    a[0] = 19; lo = seed - 25; hi = lo + 12; flag = hi > lo;
    uint[] memory scratch = new uint[](2); a = scratch; a[0] = 99; a[1] = 101;
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
abbrev Params : Ctx := [.val .uint, .mem A]
abbrev Results : Ctx := [.val .bool, .val .uint, .val .uint]
abbrev Input : Ctx := Results ++ Params
abbrev BodyCtx : Ctx := .mem A :: Input
abbrev Final : Ctx := Results ++ Caller
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
def arguments : Args C Caller Params :=
  .snoc (.snocMemory .nil A (.user "a") (.var (.there (.there .here)) rfl))
    .uint (.user "seed") (.simple (.local (.there (.there (.there .here)))))
def values : TEnv C caller.st.H Params := (arguments.evalT caller.st).toOption.get (by decide +kernel)
def binders : Binders Results :=
  .snoc (.snoc (.snoc .nil .uint (.user "lo")) .uint (.user "hi")) .bool (.user "flag")
def ret : CallRet Caller Results Final := .rets binders
def write {Γ : Ctx} (i : Idx Γ (.mem A)) (index value : Simple C Γ .uint) : Stmt C Γ Γ :=
  .assignMem (.index .dyn (.var i rfl) (.simple index))
    (.val (.simple value))

def body : Prog C Input BodyCtx :=
  .cons (write (.there (.there (.there (.there .here)))) (.lit 0 rfl) (.lit 19 rfl))
    (.cons (.assignLocal (.there (.there .here))
      (.binop .sub rfl rfl (.simple (.local (.there (.there (.there .here))))) (.simple (.lit 25 rfl))))
    (.cons (.assignLocal (.there .here)
      (.binop .add rfl rfl (.simple (.local (.there (.there .here)))) (.simple (.lit 12 rfl))))
    (.cons (.assignLocal .here
      (.binop .gt rfl rfl (.simple (.local (.there .here))) (.simple (.local (.there (.there .here))))))
    (.cons (.declMem A (.user "scratch") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl)
    (.cons (.rebindMem (.there (.there (.there (.there (.there .here))))) (.alias (.var .here rfl)))
    (.cons (write (.there (.there (.there (.there (.there .here))))) (.lit 0 rfl) (.lit 99 rfl))
    (.cons (write (.there (.there (.there (.there (.there .here))))) (.lit 1 rfl) (.lit 101 rfl)) .nil)))))))

def expanded : Calls.Program 1 prefixProducer.frag (expand arguments binders body) :=
  (Calls.compile 1 prefixProducer.frag (expand arguments binders body)).get (by decide +kernel)
attribute [irreducible] expanded
def callProducer : Calls.Statement 1 prefixProducer.frag (.call "triple" arguments ret body) :=
  tupleReturn "triple" arguments binders body expanded
attribute [irreducible] callProducer
def entry : Solidity.Out C caller.st.H Input := ret.enterT (caller.st.withEnv values)
def bodyOutput : Solidity.Out C entry.st.H BodyCtx := (body.runR entry.st).toOption.get (by decide +kernel)
def exported : Solidity.Out C caller.st.H Final :=
  ⟨bodyOutput.st.withEnv (ret.leaveT (TEnv.wk (entry.ext.trans bodyOutput.ext) Caller caller.st.env)
    (TEnv.take Results (TEnv.drop body.ext bodyOutput.st.env))), entry.ext.trans bodyOutput.ext⟩
def nextUse : Prog C Final Final :=
  .cons (.require (.simple (.local .here)))
    (.cons (.assignLocal (.there (.there (.there (.there (.there (.there .here))))))
      (.binop .add rfl rfl
        (.binop .mul rfl rfl (.simple (.local (.there (.there .here)))) (.simple (.lit 100 rfl)))
        (.simple (.local (.there .here)))))
      (.cons (write (.there (.there (.there (.there (.there .here))))) (.lit 1 rfl)
        (.local (.there (.there .here)))) .nil))
def nextProducer : Calls.Program 1 callProducer.frag nextUse :=
  (Calls.compile 1 callProducer.frag nextUse).get (by decide +kernel)
attribute [irreducible] nextProducer
def finalOutput : Solidity.Out C exported.st.H Final := (nextUse.run exported.st).toOption.get (by decide +kernel)

theorem actual_prefix : callerPrefix.run initial = .ok caller := actual_get (callerPrefix.run initial) (by decide +kernel)
theorem actual_arguments : arguments.evalT caller.st = .ok values := actual_get (arguments.evalT caller.st) (by decide +kernel)
theorem actual_body : body.runR entry.st = .ok bodyOutput := actual_get (body.runR entry.st) (by decide +kernel)
theorem actual_call : (Stmt.call "triple" arguments ret body).run caller.st = .ok exported :=
  InternalFlow.call_return arguments ret body.ext body.runR caller.st values actual_arguments bodyOutput actual_body
theorem actual_next : nextUse.run exported.st = .ok finalOutput := actual_get (nextUse.run exported.st) (by decide +kernel)

theorem public_refusal : (Compiler.compile 1 prefixProducer.frag
    (.cons (.call "triple" arguments ret body) .nil)).isSome = false := by decide +kernel

def ownedProgram : Calls.Program 1 prefixProducer.frag (.cons (.call "triple" arguments ret body) nextUse) :=
  Calls.cons callProducer nextProducer
attribute [irreducible] ownedProgram
/-- This checked certificate is NOT claimed to be returned by Compiler.compile. -/
def checked : Compiler.Compilation 1 prefixProducer.frag (.cons (.call "triple" arguments ret body) nextUse) :=
  .memoryCalls ownedProgram (by decide +kernel)
attribute [irreducible] checked

theorem exact_frame_cost : [prefixProducer.need,expanded.need,callProducer.need,nextProducer.need,
    checked.requiredFrame,prefixProducer.cost initial,callProducer.cost caller.st,nextProducer.cost exported.st,
    checked.allocationCost caller.st] = [4,10,10,7,10,7,3,0,3] := by decide +kernel

/-- Prefix execution actually produces the tuple-call input representation. -/
theorem represented_stages : ∃ m₁ base₁ m₂ base₂ m₃ base₃,
    Evm.run prefixProducer.code machine = .ok m₁ 0 ∧
    Evm.run callProducer.code m₁ = .ok m₂ 0 ∧ Evm.run nextProducer.code m₂ = .ok m₃ 0 ∧
    StateRepr 1 1 128 prefixProducer.frag caller.st base₁ m₁ ∧
    StateRepr 1 1 128 callProducer.frag exported.st base₂ m₂ ∧
    StateRepr 1 1 128 nextProducer.frag finalOutput.st base₃ m₃ ∧
    m₁.stack = machine.stack ∧ m₂.stack = m₁.stack ∧ m₃.stack = m₂.stack ∧
    BaseExtends caller.st.H base₁ base₂ ∧ BaseExtends exported.st.H base₂ base₃ ∧
    checked.Input 1 128 base₁ caller.st m₁ ∧ checked.Agrees 1 128 base₁ caller.st m₁ := by
  have prefixCost : prefixProducer.cost initial = 7 := congrArg (fun xs => xs[5]!) exact_frame_cost
  have callCost : callProducer.cost caller.st = 3 := congrArg (fun xs => xs[6]!) exact_frame_cost
  have wholeCost : ownedProgram.cost caller.st = 3 := by
    have h : checked.allocationCost caller.st = 3 := congrArg (fun xs => xs[8]!) exact_frame_cost
    delta checked at h
    exact h
  have prefixNeed : prefixProducer.need = 4 := congrArg (fun xs => xs[0]!) exact_frame_cost
  have callNeed : callProducer.need = 10 := congrArg (fun xs => xs[2]!) exact_frame_cost
  have nextNeed : nextProducer.need = 7 := congrArg (fun xs => xs[3]!) exact_frame_cost
  have nextCost : nextProducer.cost exported.st = 0 := congrArg (fun xs => xs[7]!) exact_frame_cost
  have checkedNeed : checked.requiredFrame = 10 := congrArg (fun xs => xs[4]!) exact_frame_cost
  have whole : AllocationInput 1 128
      (prefixProducer.cost initial + ownedProgram.cost caller.st) initial bases machine :=
    .inr ⟨by decide, wmod 256, initial_repr.2, by rw [prefixCost,wholeCost]; decide +kernel⟩
  obtain ⟨m₁,base₁,ht₁,hr₁,hk₁,he₁,ha₁⟩ := program_endpoint prefixProducer initial_repr.1
    (by rw [prefixNeed]; decide) (whole.of_le (Nat.le_add_right _ _)) caller actual_prefix
  have ownedSpace : AllocationInput 1 128 (ownedProgram.cost caller.st) caller.st base₁ m₁ :=
    GrowsAllocator.nextInput (C := C) (Γ := []) (Δ := Caller) (b := 1) (frame := 128)
      (head := prefixProducer.cost initial) (tail := ownedProgram.cost caller.st)
      (σ := initial) (τ := caller.st) (base := bases) (base' := base₁) (m := machine) (m' := m₁) ha₁ whole
  have callSpace : AllocationInput 1 128 (callProducer.cost caller.st) caller.st base₁ m₁ :=
    ownedSpace.of_le (by rw [callCost,wholeCost]; exact Nat.le_refl _)
  have room : 1 + callProducer.need ≤ 128 := by rw [callNeed]; decide
  obtain ⟨m₂,base₂,ht₂,hr₂,hk₂,he₂,ha₂⟩ := statement_endpoint
    (L := 1) (frame := 128) (σ := caller.st) (base := base₁) (m := m₁)
    callProducer hr₁ room callSpace exported actual_call
  have nextRoom : 1 + nextProducer.need ≤ 128 := by rw [nextNeed]; decide
  have nextSpace : AllocationInput 1 128 (nextProducer.cost exported.st) exported.st base₂ m₂ := .inl nextCost
  obtain ⟨m₃,base₃,ht₃,hr₃,hk₃,he₃,ha₃⟩ := program_endpoint
    (L := 1) (frame := 128) (σ := exported.st) (base := base₂) (m := m₂)
    nextProducer hr₂ nextRoom nextSpace finalOutput actual_next
  have hi : checked.Input 1 128 base₁ caller.st m₁ := by
    apply (checked.memoryCalls_input (by decide +kernel) 1 128 base₁ caller.st m₁).mpr
    refine ⟨hr₁, by rw [checkedNeed]; decide, ?_⟩
    have hc : checked.allocationCost caller.st = ownedProgram.cost caller.st := by delta checked; rfl
    rw [hc]
    exact ownedSpace
  exact ⟨m₁,base₁,m₂,base₂,m₃,base₃,ht₁,ht₂,ht₃,hr₁,hr₂,hr₃,hk₁,hk₂,hk₃,he₂,he₃,hi,checked.correct hi⟩

def arrayObject {H : HTy} (hp : Heap H) (id : Nat) : Option (List Int) :=
  if h : H[id]? = some A then
    let r : HRef H A := ⟨id, h⟩
    some ((hp.len r .dyn : Int) :: (MObj.elems .dyn (hp.get r)).map (fun v => v.1))
  else none

def contents {Γ : Ctx} (σ : State C Γ) : Option (List (List Int)) :=
  (List.range σ.H.length).mapM (arrayObject σ.heap)
def identity {H : HTy} (r : Option (HRef H A)) : Option Nat := r.map (fun r => r.id)
def words (out : Evm.Out) (addresses : List Nat) : Option (List Nat) := do
  match out with
  | .ok m _ => (m.stack ++ addresses.map m.mem).mapM fun w => match w with
    | .val v => some v.val
    | .slot _ => none
  | _ => none

def resultValues (σ : State C Final) : List Int :=
  [cond (σ.env.1 : Bool) (1:Int) 0, σ.env.2.1.1, σ.env.2.2.1.1, σ.env.2.2.2.2.2.2.1.1]
def callerAliases (σ : State C Final) : List (Option Nat) :=
  [identity σ.env.2.2.2.1, identity σ.env.2.2.2.2.1, identity σ.env.2.2.2.2.2.1]

theorem argument_order : (values.1.1, identity values.2.1) = (42, some 0) := by decide +kernel

theorem source_prefix : (contents caller.st,
    [identity caller.st.env.1, identity caller.st.env.2.1, identity caller.st.env.2.2.1], caller.st.env.2.2.2.1.1) =
    (some [[2,7,11],[3,23,29,31]], [some 1,some 0,some 0], 42) := by decide +kernel

theorem source_entry : (contents entry.st,
    [cond (entry.st.env.1 : Bool) (1:Int) 0, entry.st.env.2.1.1, entry.st.env.2.2.1.1, entry.st.env.2.2.2.1.1],
    identity entry.st.env.2.2.2.2.1) =
    (some [[2,7,11],[3,23,29,31]], [0,0,0,42], some 0) := by
  have heap : contents caller.st = some [[2,7,11],[3,23,29,31]] := congrArg Prod.fst source_prefix
  have seed : values.1.1 = 42 := congrArg Prod.fst argument_order
  have alias : identity values.2.1 = some 0 := congrArg Prod.snd argument_order
  change (contents caller.st,[0,0,0,values.1.1],identity values.2.1) = _
  rw [heap,seed,alias]

theorem source_body : (contents bodyOutput.st,
    [identity bodyOutput.st.env.1, identity bodyOutput.st.env.2.2.2.2.2.1],
    [cond (bodyOutput.st.env.2.1 : Bool) (1:Int) 0, bodyOutput.st.env.2.2.1.1,
      bodyOutput.st.env.2.2.2.1.1, bodyOutput.st.env.2.2.2.2.1.1]) =
    (some [[2,19,11],[3,23,29,31],[2,99,101]], [some 2,some 2], [1,29,17,42]) := by decide +kernel

theorem source_export : (contents exported.st, resultValues exported.st, callerAliases exported.st) =
    (some [[2,19,11],[3,23,29,31],[2,99,101]], [1,29,17,42], [some 1,some 0,some 0]) := by decide +kernel

theorem source_next : (contents finalOutput.st, resultValues finalOutput.st, callerAliases finalOutput.st) =
    (some [[2,19,17],[3,23,29,31],[2,99,101]], [1,29,17,1729], [some 1,some 0,some 0]) := by decide +kernel

theorem heap_sizes : [caller.st.H.length,entry.st.H.length,bodyOutput.st.H.length,exported.st.H.length,finalOutput.st.H.length] =
    [2,2,3,3,3] := by decide +kernel

theorem target_prefix : words (Evm.run prefixProducer.code machine)
    [0,127,1,2,3,4,256,257,258,259,260,261,262] =
    some [77,263,99,42,256,256,259,2,7,11,3,23,29,31] := by decide +kernel

theorem target_body : words (Evm.run (prefixProducer.code ++ expanded.code) machine)
    [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262,263,264,265] =
    some [77,266,99,42,256,256,259,263,42,17,29,1,263,2,19,11,3,23,29,31,2,99,101] := by decide +kernel

/-- The same complete certificate, now shared rather than recompiling its body. -/
theorem actualCallConstruction : callProducer = TupleCalls.tupleReturn "triple" arguments binders body expanded := by
  delta callProducer
  rfl

theorem actualSelectorResult :
    compileTuple 1 prefixProducer.frag (.call "triple" arguments ret body) = some callProducer := by
  have compiled : Calls.compile 1 prefixProducer.frag (TupleCalls.expand arguments binders body) = some expanded := by
    delta expanded
    exact (Option.some_get _).symm
  delta callProducer
  exact TupleCalls.compileTuple_success prefixProducer.frag "triple" arguments binders body expanded compiled


theorem actualExpandedTarget : ∃ m : Evm.Machine,
    Evm.run (prefixProducer.code ++ expanded.code) machine = .ok m 0 := by
  obtain ⟨m₁,base₁,m₂,base₂,m₃,base₃,hp,hc,hn,r₁,r₂,r₃,k₁,k₂,k₃,e₂,e₃,hi,agrees⟩ := represented_stages
  have input := (checked.memoryCalls_input (by decide +kernel) 1 128 base₁ caller.st m₁).mp hi
  have copiedNeed : callProducer.need = expanded.need := congrArg (fun p => p.need) actualCallConstruction
  have need : expanded.need = 10 := copiedNeed.symm.trans (congrArg (fun xs => xs[2]!) exact_frame_cost)
  have room : 1 + expanded.need ≤ 128 := by rw [need]; decide
  have copiedCost : callProducer.cost caller.st = expanded.cost caller.st :=
    congrArg (fun p => p.cost caller.st) actualCallConstruction
  have small : callProducer.cost caller.st = 3 := congrArg (fun xs => xs[6]!) exact_frame_cost
  have large : checked.allocationCost caller.st = 3 := congrArg (fun xs => xs[8]!) exact_frame_cost
  have fits : expanded.cost caller.st ≤ checked.allocationCost caller.st := by
    rw [← copiedCost,small,large]
    exact Nat.le_refl _
  have capacity := input.2.2.of_le fits
  rcases expanded.sound r₁ room capacity with ⟨out,m,base,hs,ht,repr,stack,bases,allocator⟩ | ⟨hs,ht⟩
  · exact ⟨m,(Evm.run_append_ok hp).trans ht⟩
  · have observed := target_body
    rw [Evm.run_append_ok hp,ht] at observed
    cases observed

theorem target_export : words (Evm.run (prefixProducer.code ++ callProducer.code) machine)
    [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262,263,264,265] =
    some [77,266,99,42,256,256,259,17,29,1,29,1,263,2,19,11,3,23,29,31,2,99,101] := by
  obtain ⟨m,executed⟩ := actualExpandedTarget
  have full := target_body
  rw [executed] at full
  have snapshot := numeric_stack_cells m [0, 127, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265] [77] [266, 99, 42, 256, 256, 259, 263, 42, 17, 29, 1, 263, 2, 19, 11, 3, 23, 29, 31, 2, 99, 101] rfl full
  have h0 := congrArg (fun xs => xs[0]!) snapshot.2
  change m.mem 0 = observedWord 266 at h0
  have h1 := congrArg (fun xs => xs[1]!) snapshot.2
  change m.mem 127 = observedWord 99 at h1
  have h2 := congrArg (fun xs => xs[2]!) snapshot.2
  change m.mem 1 = observedWord 42 at h2
  have h3 := congrArg (fun xs => xs[3]!) snapshot.2
  change m.mem 2 = observedWord 256 at h3
  have h4 := congrArg (fun xs => xs[4]!) snapshot.2
  change m.mem 3 = observedWord 256 at h4
  have h5 := congrArg (fun xs => xs[5]!) snapshot.2
  change m.mem 4 = observedWord 259 at h5
  have h8 := congrArg (fun xs => xs[8]!) snapshot.2
  change m.mem 7 = observedWord 17 at h8
  have h9 := congrArg (fun xs => xs[9]!) snapshot.2
  change m.mem 8 = observedWord 29 at h9
  have h10 := congrArg (fun xs => xs[10]!) snapshot.2
  change m.mem 9 = observedWord 1 at h10
  have h11 := congrArg (fun xs => xs[11]!) snapshot.2
  change m.mem 10 = observedWord 263 at h11
  have h12 := congrArg (fun xs => xs[12]!) snapshot.2
  change m.mem 256 = observedWord 2 at h12
  have h13 := congrArg (fun xs => xs[13]!) snapshot.2
  change m.mem 257 = observedWord 19 at h13
  have h14 := congrArg (fun xs => xs[14]!) snapshot.2
  change m.mem 258 = observedWord 11 at h14
  have h15 := congrArg (fun xs => xs[15]!) snapshot.2
  change m.mem 259 = observedWord 3 at h15
  have h16 := congrArg (fun xs => xs[16]!) snapshot.2
  change m.mem 260 = observedWord 23 at h16
  have h17 := congrArg (fun xs => xs[17]!) snapshot.2
  change m.mem 261 = observedWord 29 at h17
  have h18 := congrArg (fun xs => xs[18]!) snapshot.2
  change m.mem 262 = observedWord 31 at h18
  have h19 := congrArg (fun xs => xs[19]!) snapshot.2
  change m.mem 263 = observedWord 2 at h19
  have h20 := congrArg (fun xs => xs[20]!) snapshot.2
  change m.mem 264 = observedWord 99 at h20
  have h21 := congrArg (fun xs => xs[21]!) snapshot.2
  change m.mem 265 = observedWord 101 at h21
  have code : callProducer.code = expanded.code ++ TupleCalls.exportCode 1 Caller Params binders :=
    congrArg (fun p => p.code) actualCallConstruction
  rw [code,← List.append_assoc,Evm.run_append_ok executed]
  simp only [words, run, Caller, Params, binders, TupleCalls.exportCode, cell, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.add_zero, List.nil_append, List.cons_append,
      exec_cons_zero, Out.bind, Instr.step, Machine.next, h8, snapshot.1, List.map_cons, List.map_nil,
      exec, upd, Nat.reduceEqDiff, ↓reduceIte, h9, h10, reduceCtorEq, h0, h1, h2, h3, h4, h5,
      Nat.succ_ne_self, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, List.mapM_cons,
      List.mapM_nil, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
  decide +kernel

theorem target_next : words (Evm.run (prefixProducer.code ++ callProducer.code ++ nextProducer.code) machine)
    [0,127,1,2,3,4,5,6,7,256,257,258,259,260,261,262,263,264,265] =
    some [77,266,99,1729,256,256,259,17,29,1,2,19,17,3,23,29,31,2,99,101] := by decide +kernel

theorem checked_target_next : words (Evm.run (prefixProducer.code ++ checked.code) machine)
    [0,127,1,2,3,4,5,6,7,256,257,258,259,260,261,262,263,264,265] =
    some [77,266,99,1729,256,256,259,17,29,1,2,19,17,3,23,29,31,2,99,101] := by
  have code : checked.code = callProducer.code ++ nextProducer.code := by
    unfold checked ownedProgram
    rfl
  rw [code, ← List.append_assoc]
  exact target_next


theorem wrong_same_typed_order : resultValues exported.st ≠ [1,17,29,42] := by
  rw [show resultValues exported.st = [1,29,17,42] from congrArg (fun x => x.2.1) source_export]
  decide

theorem wrong_destination : words (Evm.run (prefixProducer.code ++ callProducer.code) machine) [1,5,6,7] ≠
    some [77,17,42,29,1] := by
  have full := target_export
  generalize execution : Evm.run (prefixProducer.code ++ callProducer.code) machine = out at full ⊢
  cases out with
  | revert => cases full
  | fault => cases full
  | ok m skip =>
    have snapshot := numeric_stack_cells m
      [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262,263,264,265] [77] [266,99,42,256,256,259,17,29,1,29,1,263,2,19,11,3,23,29,31,2,99,101] rfl full
    have selected := congrArg (fun xs => [xs[2]!,xs[6]!,xs[7]!,xs[8]!]) snapshot.2
    change [m.mem 1,m.mem 5,m.mem 6,m.mem 7] = [observedWord 42,observedWord 17,observedWord 29,observedWord 1] at selected
    change (m.stack ++ [m.mem 1,m.mem 5,m.mem 6,m.mem 7]).mapM
      (fun w => match w with | Evm.Word.val v => some v.val | .slot _ => none) ≠ _
    rw [snapshot.1,selected]
    decide

theorem wrong_private_escape : callerAliases exported.st ≠ [some 1,some 2,some 2] := by
  rw [show callerAliases exported.st = [some 1,some 0,some 0] from congrArg (fun x => x.2.2) source_export]
  decide

theorem wrong_old_contents : contents exported.st ≠
    some [[2,7,11],[3,23,29,31],[2,99,101]] := by
  rw [show contents exported.st = some [[2,19,11],[3,23,29,31],[2,99,101]] from congrArg Prod.fst source_export]
  decide

theorem wrong_unrelated_contents : contents finalOutput.st ≠
    some [[2,19,17],[3,19,29,31],[2,99,101]] := by
  rw [show contents finalOutput.st = some [[2,19,17],[3,23,29,31],[2,99,101]] from congrArg Prod.fst source_next]
  decide

theorem wrong_cost : prefixProducer.cost initial + checked.allocationCost caller.st ≠ 11 := by
  have h : prefixProducer.cost initial + checked.allocationCost caller.st = 10 :=
    congrArg (fun xs => xs[5]! + xs[8]!) exact_frame_cost
  rw [h]
  decide

theorem wrong_cursor : words (Evm.run (prefixProducer.code ++ checked.code) machine) [0] ≠ some [77,267] := by
  have full := checked_target_next
  generalize execution : Evm.run (prefixProducer.code ++ checked.code) machine = out at full ⊢
  cases out with
  | revert => cases full
  | fault => cases full
  | ok m skip =>
    have snapshot := numeric_stack_cells m
      [0,127,1,2,3,4,5,6,7,256,257,258,259,260,261,262,263,264,265] [77] [266,99,1729,256,256,259,17,29,1,2,19,17,3,23,29,31,2,99,101] rfl full
    have selected := congrArg (fun xs => xs[0]!) snapshot.2
    change m.mem 0 = observedWord 266 at selected
    change (m.stack ++ [m.mem 0]).mapM
      (fun w => match w with | Evm.Word.val v => some v.val | .slot _ => none) ≠ _
    rw [snapshot.1,selected]
    decide

/-- A real successful wrong-order execution, not a failed Input premise. -/
def badHighFirst : List Instr := [.mload 9,.mstore 7,.mload 8,.mstore 6,.mload 7,.mstore 5]
theorem overlapping_order_countercontrol : words
    (Evm.run (prefixProducer.code ++ expanded.code ++ badHighFirst) machine) [5,6,7] =
    some [77,1,29,1] := by
  obtain ⟨m,executed⟩ := actualExpandedTarget
  have full := target_body
  rw [executed] at full
  have snapshot := numeric_stack_cells m
    [0,127,1,2,3,4,5,6,7,8,9,10,256,257,258,259,260,261,262,263,264,265]
    [77] [266,99,42,256,256,259,263,42,17,29,1,263,2,19,11,3,23,29,31,2,99,101] rfl full
  have high : m.mem 8 = observedWord 29 := congrArg (fun xs => xs[9]!) snapshot.2
  have flag : m.mem 9 = observedWord 1 := congrArg (fun xs => xs[10]!) snapshot.2
  rw [Evm.run_append_ok executed]
  simp only [words,badHighFirst,Evm.run,Evm.exec,Evm.Instr.step,Evm.Out.bind,
    Evm.Machine.next,Evm.upd,snapshot.1,high,flag,List.map_cons,List.map_nil,
    Nat.reduceEqDiff,reduceIte]
  decide +kernel

theorem mutator_not_withinM : Prog.withinM .view body = false := rfl

theorem public_refusal_unchanged : (Calls.compile 1 prefixProducer.frag
    (.cons (.call "triple" arguments ret body) nextUse)).isSome = false := by decide +kernel


/-- Failure before any body allocation still has exact bare-revert semantics;
no failed State or rollback conclusion is extracted. -/
def failedBody : Prog C Input BodyCtx := .cons .revert body
def failedExpanded : Calls.Program 1 prefixProducer.frag (expand arguments binders failedBody) :=
  (Calls.compile 1 prefixProducer.frag (expand arguments binders failedBody)).get (by decide +kernel)
attribute [irreducible] failedExpanded
def failedProducer : Calls.Statement 1 prefixProducer.frag (.call "failedTuple" arguments ret failedBody) :=
  tupleReturn "failedTuple" arguments binders failedBody failedExpanded
attribute [irreducible] failedProducer

theorem tuple_failure_source : (Stmt.call "failedTuple" arguments ret failedBody).run caller.st = .error .revert :=
  InternalFlow.call_body_failure arguments ret failedBody.ext failedBody.runR caller.st values actual_arguments .revert rfl

theorem unreachable_allocation_cost : failedProducer.cost caller.st = 0 := by decide +kernel

theorem tuple_failure_target : ∃ m₁ base₁,
    Evm.run prefixProducer.code machine = .ok m₁ 0 ∧
    StateRepr 1 1 128 prefixProducer.frag caller.st base₁ m₁ ∧
    Evm.run failedProducer.code m₁ = .revert := by
  have capacity : AllocationInput 1 128 (prefixProducer.cost initial) initial bases machine :=
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩
  obtain ⟨m₁,base₁,ht,hr,hk,he,ha⟩ := program_endpoint prefixProducer initial_repr.1
    (by decide +kernel) capacity caller actual_prefix
  have room : 1 + failedProducer.need ≤ 128 := by decide +kernel
  have noCost : AllocationInput 1 128 (failedProducer.cost caller.st) caller.st base₁ m₁ :=
    .inl unreachable_allocation_cost
  exact ⟨m₁,base₁,ht,hr,statement_revert (L := 1) (frame := 128) (σ := caller.st)
    (base := base₁) (m := m₁) failedProducer hr room noCost tuple_failure_source⟩

theorem owned_selector_admits : (compileTuple 1 prefixProducer.frag
    (.call "triple" arguments ret body)).isSome = true := by
  rw [actualSelectorResult]
  rfl

def refusedBody : Prog C Input Input := .cons (.revertData [.bytes [7]]) .nil

theorem owned_selector_refuses_data : (compileTuple 1 prefixProducer.frag
    (.call "tupleBytes" arguments ret refusedBody)).isSome = false := by decide +kernel

theorem refused_source_class : (Stmt.call "tupleBytes" arguments ret refusedBody).run caller.st =
    .error (.revertWith [7]) :=
  InternalFlow.call_body_failure arguments ret refusedBody.ext refusedBody.runR caller.st values
    actual_arguments (.revertWith [7]) rfl

theorem zero_parameter_copy_control : words
    (Evm.run (prefixProducer.code ++ callProducer.code ++ exportCode 1 Caller [] binders) machine) [0,1,5,6,7] =
    some [77,266,42,17,29,1] := by decide +kernel

theorem empty_tuple_selector : (compileTuple 1 prefixProducer.frag
    (.call "emptyTuple" arguments (.rets .nil) (Prog.nil : Prog C Params Params))).isSome = true := by decide +kernel
#print_checked_axioms noRef,
  initial_repr,
  actual_prefix,
  actual_arguments,
  actual_body,
  actual_call,
  actual_next,
  public_refusal,
  represented_stages,
  argument_order,
  source_prefix,
  source_entry,
  source_body,
  source_export,
  source_next,
  heap_sizes,
  target_prefix,
  target_body,
  target_export,
  target_next,
  checked_target_next,
  exact_frame_cost,
  wrong_same_typed_order,
  wrong_destination,
  wrong_private_escape,
  wrong_old_contents,
  wrong_unrelated_contents,
  wrong_cost,
  wrong_cursor,
  overlapping_order_countercontrol,
  mutator_not_withinM,
  public_refusal_unchanged,
  tuple_failure_source,
  unreachable_allocation_cost,
  tuple_failure_target,
  owned_selector_admits,
  owned_selector_refuses_data,
  refused_source_class,
  zero_parameter_copy_control,
  empty_tuple_selector,
  TupleCalls.expand_runSt,
  TupleCalls.expand_runR,
  TupleCalls.tuple_entry,
  TupleCalls.compact,
  TupleCalls.tupleReturn,
  TupleCalls.compileTuple,
  TupleCalls.no_memory_binder,
  TupleCalls.no_storage_binder
end Solidity.Backend.InternalFlow.TupleCallChecks


namespace Solidity.Backend.InternalFlow.TupleCallChecks.Composed
open Evm Evm.Memory PublishedDirectCalls TupleCalls

-- The inner call evaluates the outer parameter frame, not a synthetic input.
def innerArgs : Args C Input Params :=
  .snoc (.snocMemory .nil A (.user "a") (.var (.there (.there (.there (.there .here)))) rfl))
    .uint (.user "seed") (.simple (.local (.there (.there (.there .here)))))
def innerCall : Stmt C Input (Results ++ Input) :=
  .call "innerTriple" innerArgs (.rets binders) body

def transfer : Prog C (Results ++ Input) (Results ++ Input) :=
  .cons (.assignLocal (.there (.there (.there (.there (.there .here)))))
    (.simple (.local (.there (.there .here)))))
  (.cons (.assignLocal (.there (.there (.there (.there .here))))
    (.binop .add rfl rfl (.simple (.local (.there .here))) (.simple (.lit 1 rfl))))
  (.cons (.assignLocal (.there (.there (.there .here))) (.simple (.local .here))) .nil))
def nestedBody : Prog C Input BodyCtx :=
  .cons (.block (.cons innerCall transfer))
  (.cons (.declMem A (.user "outerPrivate") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl)
  (.cons (.rebindMem (.there (.there (.there (.there (.there .here))))) (.alias (.var .here rfl)))
  (.cons (write .here (.lit 0 rfl) (.lit 55 rfl)) .nil)))
def outerCall : Stmt C Caller Final := .call "outerTriple" arguments ret nestedBody
def exported : Solidity.Out C caller.st.H Final :=
  (outerCall.run caller.st).toOption.get (by decide +kernel)
def used : Solidity.Out C exported.st.H Final :=
  (nextUse.run exported.st).toOption.get (by decide +kernel)
def scopeProgram : Prog C Caller Caller :=
  .cons (.ite (.simple (.bool true))
    (.cons (.block (.cons outerCall nextUse)) .nil) (.cons .revert .nil)) .nil
theorem source_outer : outerCall.run caller.st = .ok exported :=
  actual_get (outerCall.run caller.st) (by decide +kernel)
theorem source_used : nextUse.run exported.st = .ok used :=
  actual_get (nextUse.run exported.st) (by decide +kernel)

theorem scope_run_state : scopeProgram.runSt caller.st =
    .ok (used.st.drop (Ext.append Caller Results)) := by
  rw [scopeProgram,Prog.runSt_single,Stmt.runSt_ite]
  change ((Prog.cons (Stmt.block (.cons outerCall nextUse)) .nil).runSt caller.st).map _ = _
  rw [Prog.runSt_single,Stmt.runSt_block,Prog.runSt_cons]
  change ((((outerCall.run caller.st).map (·.st)).bind (fun σ => nextUse.runSt σ)).map _).map _ = _
  rw [source_outer]
  change (((nextUse.run exported.st).map (·.st)).map _).map _ = _
  rw [source_used]
  rfl

theorem scope_has_output : (scopeProgram.run caller.st).toOption.isSome = true := by
  cases execution : scopeProgram.run caller.st with
  | error halt =>
    have state := scope_run_state
    change (scopeProgram.run caller.st).map (·.st) = _ at state
    rw [execution] at state
    cases state
  | ok out => rfl

def unwound : Solidity.Out C caller.st.H Caller :=
  (scopeProgram.run caller.st).toOption.get scope_has_output
def suffix : Prog C Caller Caller :=
  .cons (.assignLocal (.there (.there (.there .here)))
    (.binop .add rfl rfl (.simple (.local (.there (.there (.there .here))))) (.simple (.lit 5 rfl))))
  (.cons (write (.there (.there .here)) (.lit 1 rfl) (.local (.there (.there (.there .here))))) .nil)
def final : Solidity.Out C unwound.st.H Caller :=
  (suffix.run unwound.st).toOption.get (by decide +kernel)
def program : Prog C Caller Caller := .cons (.block scopeProgram) suffix

def outerProducer : Calls.Program 1 prefixProducer.frag (.cons outerCall .nil) :=
  (TuplePrograms.compile 1 prefixProducer.frag (.cons outerCall .nil)).get (by decide +kernel)
attribute [irreducible] outerProducer
def scopedProducer : Calls.Program 1 prefixProducer.frag scopeProgram :=
  (TuplePrograms.compile 1 prefixProducer.frag scopeProgram).get (by decide +kernel)
attribute [irreducible] scopedProducer
def suffixProducer : Calls.Program 1 scopedProducer.frag suffix :=
  (TuplePrograms.compile 1 scopedProducer.frag suffix).get (by decide +kernel)
attribute [irreducible] suffixProducer
def producer : Calls.Program 1 prefixProducer.frag program :=
  (TuplePrograms.compile 1 prefixProducer.frag program).get (by decide +kernel)
attribute [irreducible] producer

theorem source_scoped : scopeProgram.run caller.st = .ok unwound :=
  actual_get (scopeProgram.run caller.st) scope_has_output
theorem scope_state_drop : unwound.st = used.st.drop (Ext.append Caller Results) := by
  have actual : scopeProgram.runSt caller.st = .ok unwound.st := by
    change (scopeProgram.run caller.st).map _ = _
    rw [source_scoped]
    rfl
  exact Except.ok.inj (actual.symm.trans scope_run_state)

theorem source_suffix : suffix.run unwound.st = .ok final :=
  actual_get (suffix.run unwound.st) (by decide +kernel)
theorem source_program : program.run caller.st = .ok ⟨final.st, unwound.ext.trans final.ext⟩ := by
  have hb : (Stmt.block scopeProgram).run caller.st = .ok unwound := by
    change (scopeProgram.run caller.st).map _ = _
    rw [source_scoped]
    rfl
  rw [program, Prog.run_cons_ok hb, source_suffix]
  rfl

def callerObs (σ : State C Caller) : List (Option Nat) × Int :=
  ([identity σ.env.1,identity σ.env.2.1,identity σ.env.2.2.1],σ.env.2.2.2.1.1)

theorem ordered_export : (contents exported.st,resultValues exported.st,callerAliases exported.st) =
    (some [[2,19,11],[3,23,29,31],[2,99,101],[1,55]], [1,30,17,42], [some 1,some 0,some 0]) := by decide +kernel
theorem ordered_used : (contents used.st,resultValues used.st,callerAliases used.st) =
    (some [[2,19,17],[3,23,29,31],[2,99,101],[1,55]], [1,30,17,1730], [some 1,some 0,some 0]) := by decide +kernel
theorem ordered_unwind : (contents unwound.st,callerObs unwound.st) =
    (some [[2,19,17],[3,23,29,31],[2,99,101],[1,55]], ([some 1,some 0,some 0],1730)) := by
  rw [scope_state_drop]
  exact congrArg (fun x => (x.1,(x.2.2,x.2.1[3]!))) ordered_used
theorem ordered_final : (contents final.st,callerObs final.st) =
    (some [[2,19,1735],[3,23,29,31],[2,99,101],[1,55]], ([some 1,some 0,some 0],1735)) := by decide +kernel

theorem traversal_and_refusal :
    (TuplePrograms.height program, (Calls.compile 1 prefixProducer.frag program).isSome,
      (TuplePrograms.compile 1 prefixProducer.frag program).isSome) = (2,false,true) := by decide +kernel

-- Actual protected source/target midpoint, obtained only by running the prefix.
theorem represented : ∃ m₁ base₁ m₂ base₂ m₃ base₃,
    Evm.run prefixProducer.code machine = .ok m₁ 0 ∧
    Evm.run scopedProducer.code m₁ = .ok m₂ 0 ∧
    Evm.run suffixProducer.code m₂ = .ok m₃ 0 ∧
    StateRepr 1 1 128 prefixProducer.frag caller.st base₁ m₁ ∧
    StateRepr 1 1 128 scopedProducer.frag unwound.st base₂ m₂ ∧
    StateRepr 1 1 128 suffixProducer.frag final.st base₃ m₃ ∧
    m₁.stack = machine.stack ∧ m₂.stack = m₁.stack ∧ m₃.stack = m₂.stack ∧
    BaseExtends caller.st.H base₁ base₂ ∧ BaseExtends unwound.st.H base₂ base₃ := by
  have whole : AllocationInput 1 128
      (prefixProducer.cost initial + scopedProducer.cost caller.st) initial bases machine :=
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩
  obtain ⟨m₁,base₁,ht₁,hr₁,hk₁,he₁,ha₁⟩ := program_endpoint prefixProducer initial_repr.1
    (by decide +kernel) (whole.of_le (Nat.le_add_right _ _)) caller actual_prefix
  have space : AllocationInput 1 128 (scopedProducer.cost caller.st) caller.st base₁ m₁ :=
    ha₁.nextInput whole
  obtain ⟨m₂,base₂,ht₂,hr₂,hk₂,he₂,ha₂⟩ := program_endpoint
    (L := 1) (frame := 128) (σ := caller.st) (base := base₁) (m := m₁)
    scopedProducer hr₁ (by decide +kernel) space unwound source_scoped
  have combined : AllocationInput 1 128
      (scopedProducer.cost caller.st + suffixProducer.cost unwound.st) caller.st base₁ m₁ := by
    simpa only [show suffixProducer.cost unwound.st = 0 from by decide +kernel, Nat.add_zero] using space
  have nextSpace : AllocationInput 1 128 (suffixProducer.cost unwound.st) unwound.st base₂ m₂ :=
    ha₂.nextInput combined
  obtain ⟨m₃,base₃,ht₃,hr₃,hk₃,he₃,ha₃⟩ := program_endpoint
    (L := 1) (frame := 128) (σ := unwound.st) (base := base₂) (m := m₂)
    suffixProducer hr₂ (by decide +kernel) nextSpace final source_suffix
  exact ⟨m₁,base₁,m₂,base₂,m₃,base₃,ht₁,ht₂,ht₃,hr₁,hr₂,hr₃,hk₁,hk₂,hk₃,he₂,he₃⟩


def innerValues : TEnv C entry.st.H Params :=
  (innerArgs.evalT entry.st).toOption.get (by decide +kernel)
def innerEntry : Solidity.Out C entry.st.H Input :=
  (CallRet.rets (Γ := Input) binders).enterT (entry.st.withEnv innerValues)
def innerBodyOutput : Solidity.Out C innerEntry.st.H BodyCtx :=
  (body.run innerEntry.st).toOption.get (by decide +kernel)
def innerExport : Solidity.Out C entry.st.H (Results ++ Input) :=
  (innerCall.run entry.st).toOption.get (by decide +kernel)
def transferred : Solidity.Out C innerExport.st.H (Results ++ Input) :=
  (transfer.run innerExport.st).toOption.get (by decide +kernel)
def outerBodyOutput : Solidity.Out C entry.st.H BodyCtx :=
  (nestedBody.run entry.st).toOption.get (by decide +kernel)

theorem nested_entry_order : (innerValues.1.1,identity innerValues.2.1,
    contents innerEntry.st) = (42,some 0,some [[2,7,11],[3,23,29,31]]) := by decide +kernel
theorem nested_body_order : (contents innerBodyOutput.st,
    [identity innerBodyOutput.st.env.1,identity innerBodyOutput.st.env.2.2.2.2.2.1]) =
    (some [[2,19,11],[3,23,29,31],[2,99,101]],[some 2,some 2]) := by decide +kernel
theorem nested_export_order : (contents innerExport.st,
    [cond (innerExport.st.env.1 : Bool) (1:Int) 0,innerExport.st.env.2.1.1,innerExport.st.env.2.2.1.1,
     cond (innerExport.st.env.2.2.2.1 : Bool) (1:Int) 0,
     innerExport.st.env.2.2.2.2.1.1,innerExport.st.env.2.2.2.2.2.1.1]) =
    (some [[2,19,11],[3,23,29,31],[2,99,101]],[1,29,17,0,0,0]) := by decide +kernel
theorem nested_transfer_order :
    [cond (transferred.st.env.1 : Bool) (1:Int) 0,transferred.st.env.2.1.1,transferred.st.env.2.2.1.1,
     cond (transferred.st.env.2.2.2.1 : Bool) (1:Int) 0,
     transferred.st.env.2.2.2.2.1.1,transferred.st.env.2.2.2.2.2.1.1] = [1,29,17,1,30,17] := by decide +kernel
theorem nested_heap_sizes :
    [caller.st.H.length,entry.st.H.length,innerEntry.st.H.length,innerBodyOutput.st.H.length,
     innerExport.st.H.length,outerBodyOutput.st.H.length,exported.st.H.length,unwound.st.H.length,final.st.H.length] =
    [2,2,2,3,3,4,4,4,4] := by decide +kernel

def expandedProducer : Calls.Program 1 prefixProducer.frag (expand arguments binders nestedBody) :=
  (TuplePrograms.compile 1 prefixProducer.frag (expand arguments binders nestedBody)).get (by decide +kernel)
attribute [irreducible] expandedProducer

theorem exact_cost_frame : [outerProducer.need,expandedProducer.need,scopedProducer.need,suffixProducer.need,
    producer.need,outerProducer.cost caller.st,scopedProducer.cost caller.st,suffixProducer.cost unwound.st,
    producer.cost caller.st] = [15,15,15,4,15,5,5,0,5] := by decide +kernel

theorem actualExpandedSelection : TuplePrograms.compile 1 prefixProducer.frag (expand arguments binders nestedBody) = some expandedProducer := by
  delta expandedProducer
  exact (Option.some_get _).symm
theorem actualOuterConstruction : outerProducer =
    Calls.cons (tupleReturn "outerTriple" arguments binders nestedBody expandedProducer)
      (Calls.nil 1 (tupleReturn "outerTriple" arguments binders nestedBody expandedProducer).frag) := by
  have selected := TuplePrograms.compile_tuple_nil_success prefixProducer.frag "outerTriple"
    arguments binders nestedBody expandedProducer
    (Option.isNone_iff_eq_none.mp (by decide +kernel))
    (Option.isNone_iff_eq_none.mp (by decide +kernel)) (by decide +kernel) actualExpandedSelection
  have actual : TuplePrograms.compile 1 prefixProducer.frag (.cons outerCall .nil) = some outerProducer := by
    delta outerProducer
    exact (Option.some_get _).symm
  exact Option.some.inj (actual.symm.trans selected)
theorem actualExpandedCost : expandedProducer.cost caller.st = 5 := by
  have same : outerProducer.cost caller.st = expandedProducer.cost caller.st := by
    rw [actualOuterConstruction]
    rfl
  exact same.symm.trans (congrArg (fun xs => xs[5]!) exact_cost_frame)

theorem target_body : words (Evm.run (prefixProducer.code ++ expandedProducer.code) machine)
    [0,127,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,256,257,258,259,260,261,262,263,264,265,266,267] =
    some [77,268,99,42,256,256,259,266,42,17,30,1,266,29,1,29,1,263,2,19,11,3,23,29,31,2,99,101,1,55] := by decide +kernel
theorem actualExpandedTarget : ∃ m : Evm.Machine,
    Evm.run (prefixProducer.code ++ expandedProducer.code) machine = .ok m 0 := by
  have pc : prefixProducer.cost initial = 7 := congrArg (fun xs => xs[5]!) exact_frame_cost
  have pn : prefixProducer.need = 4 := congrArg (fun xs => xs[0]!) exact_frame_cost
  have capacity : AllocationInput 1 128
      (prefixProducer.cost initial + expandedProducer.cost caller.st) initial bases machine :=
    .inr ⟨by decide, wmod 256, initial_repr.2, by rw [pc,actualExpandedCost]; decide⟩
  obtain ⟨m₁,base₁,hp,repr,stack,bases,allocator⟩ := program_endpoint prefixProducer
    initial_repr.1 (by rw [pn]; decide) (capacity.of_le (Nat.le_add_right _ _)) caller actual_prefix
  have room : 1 + expandedProducer.need ≤ 128 := by
    have hn : expandedProducer.need = 15 := congrArg (fun xs => xs[1]!) exact_cost_frame
    rw [hn]; decide
  have reached := allocator.nextInput capacity
  rcases expandedProducer.sound repr room reached with
    ⟨out,m,base,hs,ht,repr',stack',bases',allocator'⟩ | ⟨hs,ht⟩
  · exact ⟨m,(Evm.run_append_ok hp).trans ht⟩
  · have observed := target_body
    rw [Evm.run_append_ok hp,ht] at observed
    cases observed



theorem target_export : words (Evm.run (prefixProducer.code ++ outerProducer.code) machine)
    [0,127,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,256,257,258,259,260,261,262,263,264,265,266,267] =
    some [77,268,99,42,256,256,259,17,30,1,30,1,266,29,1,29,1,263,2,19,11,3,23,29,31,2,99,101,1,55] := by
  obtain ⟨m,executed⟩ := actualExpandedTarget
  have full := target_body
  rw [executed] at full
  have snapshot := numeric_stack_cells m [0, 127, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267] [77] [268, 99, 42, 256, 256, 259, 266, 42, 17, 30, 1, 266, 29, 1, 29, 1, 263, 2, 19, 11, 3, 23, 29, 31, 2, 99, 101, 1, 55] rfl full
  have h0 : m.mem 0 = observedWord 268 := congrArg (fun xs => xs[0]!) snapshot.2
  have h1 : m.mem 127 = observedWord 99 := congrArg (fun xs => xs[1]!) snapshot.2
  have h2 : m.mem 1 = observedWord 42 := congrArg (fun xs => xs[2]!) snapshot.2
  have h3 : m.mem 2 = observedWord 256 := congrArg (fun xs => xs[3]!) snapshot.2
  have h4 : m.mem 3 = observedWord 256 := congrArg (fun xs => xs[4]!) snapshot.2
  have h5 : m.mem 4 = observedWord 259 := congrArg (fun xs => xs[5]!) snapshot.2
  have h8 : m.mem 7 = observedWord 17 := congrArg (fun xs => xs[8]!) snapshot.2
  have h9 : m.mem 8 = observedWord 30 := congrArg (fun xs => xs[9]!) snapshot.2
  have h10 : m.mem 9 = observedWord 1 := congrArg (fun xs => xs[10]!) snapshot.2
  have h11 : m.mem 10 = observedWord 266 := congrArg (fun xs => xs[11]!) snapshot.2
  have h12 : m.mem 11 = observedWord 29 := congrArg (fun xs => xs[12]!) snapshot.2
  have h13 : m.mem 12 = observedWord 1 := congrArg (fun xs => xs[13]!) snapshot.2
  have h14 : m.mem 13 = observedWord 29 := congrArg (fun xs => xs[14]!) snapshot.2
  have h15 : m.mem 14 = observedWord 1 := congrArg (fun xs => xs[15]!) snapshot.2
  have h16 : m.mem 15 = observedWord 263 := congrArg (fun xs => xs[16]!) snapshot.2
  have h17 : m.mem 256 = observedWord 2 := congrArg (fun xs => xs[17]!) snapshot.2
  have h18 : m.mem 257 = observedWord 19 := congrArg (fun xs => xs[18]!) snapshot.2
  have h19 : m.mem 258 = observedWord 11 := congrArg (fun xs => xs[19]!) snapshot.2
  have h20 : m.mem 259 = observedWord 3 := congrArg (fun xs => xs[20]!) snapshot.2
  have h21 : m.mem 260 = observedWord 23 := congrArg (fun xs => xs[21]!) snapshot.2
  have h22 : m.mem 261 = observedWord 29 := congrArg (fun xs => xs[22]!) snapshot.2
  have h23 : m.mem 262 = observedWord 31 := congrArg (fun xs => xs[23]!) snapshot.2
  have h24 : m.mem 263 = observedWord 2 := congrArg (fun xs => xs[24]!) snapshot.2
  have h25 : m.mem 264 = observedWord 99 := congrArg (fun xs => xs[25]!) snapshot.2
  have h26 : m.mem 265 = observedWord 101 := congrArg (fun xs => xs[26]!) snapshot.2
  have h27 : m.mem 266 = observedWord 1 := congrArg (fun xs => xs[27]!) snapshot.2
  have h28 : m.mem 267 = observedWord 55 := congrArg (fun xs => xs[28]!) snapshot.2
  have code : outerProducer.code = expandedProducer.code ++ exportCode 1 Caller Params binders := by
    rw [actualOuterConstruction]
    change (expandedProducer.code ++ exportCode 1 Caller Params binders) ++ [] = _
    exact List.append_nil _
  rw [code,← List.append_assoc,Evm.run_append_ok executed]
  simp only [words, run, Caller, Params, binders, TupleCalls.exportCode, cell, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.add_zero, List.nil_append, List.cons_append,
    exec_cons_zero, Out.bind, Instr.step, Machine.next, snapshot.1, List.map_cons, List.map_nil,
    exec, upd, Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq, Nat.succ_ne_self,
    List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    h0, h1, h2, h3, h4, h5, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
  decide +kernel
theorem target_unwind : words (Evm.run (prefixProducer.code ++ scopedProducer.code) machine)
    [0,127,1,2,3,4,5,6,7,256,257,258,259,260,261,262,263,264,265,266,267] =
    some [77,268,99,1730,256,256,259,17,30,1,2,19,17,3,23,29,31,2,99,101,1,55] := by decide +kernel
theorem target_final : words (Evm.run (prefixProducer.code ++ producer.code) machine)
    [0,127,1,2,3,4,5,6,7,256,257,258,259,260,261,262,263,264,265,266,267] =
    some [77,268,99,1735,256,256,259,17,30,1,2,19,1735,3,23,29,31,2,99,101,1,55] := by decide +kernel


def checked : Compiler.Compilation 1 prefixProducer.frag program :=
  .memoryCalls producer (by decide +kernel)
attribute [irreducible] checked

theorem checked_input_endpoint : ∃ m₁ base₁,
    Evm.run prefixProducer.code machine = .ok m₁ 0 ∧
    checked.Input 1 128 base₁ caller.st m₁ ∧ checked.Agrees 1 128 base₁ caller.st m₁ := by
  have whole : AllocationInput 1 128
      (prefixProducer.cost initial + producer.cost caller.st) initial bases machine :=
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩
  obtain ⟨m₁,base₁,ht,hr,hk,he,ha⟩ := program_endpoint prefixProducer initial_repr.1
    (by decide +kernel) (whole.of_le (Nat.le_add_right _ _)) caller actual_prefix
  have space : AllocationInput 1 128 (producer.cost caller.st) caller.st base₁ m₁ := ha.nextInput whole
  have hi : checked.Input 1 128 base₁ caller.st m₁ := by
    apply (checked.memoryCalls_input (by decide +kernel) 1 128 base₁ caller.st m₁).mpr
    refine ⟨hr, by decide +kernel, ?_⟩
    have hc : checked.allocationCost caller.st = producer.cost caller.st := by decide +kernel
    rw [hc]
    exact space
  exact ⟨m₁,base₁,ht,hi,checked.correct hi⟩

theorem wrong_order : resultValues exported.st ≠ [1,17,30,42] := by
  rw [show resultValues exported.st = [1,30,17,42] from congrArg (fun x => x.2.1) ordered_export]
  decide +kernel
theorem wrong_private_alias : callerAliases exported.st ≠ [some 1,some 2,some 3] := by
  rw [show callerAliases exported.st = [some 1,some 0,some 0] from congrArg (fun x => x.2.2) ordered_export]
  decide +kernel
theorem wrong_old_contents : contents final.st ≠
    some [[2,7,1735],[3,23,29,31],[2,99,101],[1,55]] := by
  rw [show contents final.st = some [[2,19,1735],[3,23,29,31],[2,99,101],[1,55]] from congrArg Prod.fst ordered_final]
  decide +kernel
theorem wrong_unrelated : contents final.st ≠
    some [[2,19,1735],[3,19,29,31],[2,99,101],[1,55]] := by
  rw [show contents final.st = some [[2,19,1735],[3,23,29,31],[2,99,101],[1,55]] from congrArg Prod.fst ordered_final]
  decide +kernel
theorem wrong_frame_cost : (producer.need,producer.cost caller.st) ≠ (10,3) := by
  have hn : producer.need = 15 := congrArg (fun xs => xs[4]!) exact_cost_frame
  have hc : producer.cost caller.st = 5 := congrArg (fun xs => xs[8]!) exact_cost_frame
  rw [hn,hc]
  decide +kernel
theorem wrong_cursor : words (Evm.run (prefixProducer.code ++ producer.code) machine) [0] ≠
    some [77,266] := by
  have full := target_final
  generalize execution : Evm.run (prefixProducer.code ++ producer.code) machine = out at full ⊢
  cases out with
  | revert => cases full
  | fault => cases full
  | ok m skip =>
    have snapshot := numeric_stack_cells m
      [0,127,1,2,3,4,5,6,7,256,257,258,259,260,261,262,263,264,265,266,267] [77] [268,99,1735,256,256,259,17,30,1,2,19,1735,3,23,29,31,2,99,101,1,55] rfl full
    have selected := congrArg (fun xs => xs[0]!) snapshot.2
    change m.mem 0 = observedWord 268 at selected
    change (m.stack ++ [m.mem 0]).mapM
      (fun w => match w with | Evm.Word.val v => some v.val | .slot _ => none) ≠ _
    rw [snapshot.1,selected]
    decide
theorem wrong_overlap : words (Evm.run
    (prefixProducer.code ++ expandedProducer.code ++ badHighFirst) machine) [5,6,7] =
    some [77,1,30,1] := by
  obtain ⟨m,executed⟩ := actualExpandedTarget
  have full := target_body
  rw [executed] at full
  have snapshot := numeric_stack_cells m
    [0,127,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,256,257,258,259,260,261,262,263,264,265,266,267]
    [77] [268,99,42,256,256,259,266,42,17,30,1,266,29,1,29,1,263,2,19,11,3,23,29,31,2,99,101,1,55] rfl full
  have high : m.mem 8 = observedWord 30 := congrArg (fun xs => xs[9]!) snapshot.2
  have flag : m.mem 9 = observedWord 1 := congrArg (fun xs => xs[10]!) snapshot.2
  rw [Evm.run_append_ok executed]
  simp only [words,badHighFirst,Evm.run,Evm.exec,Evm.Instr.step,Evm.Out.bind,
    Evm.Machine.next,Evm.upd,snapshot.1,high,flag,List.map_cons,List.map_nil,
    Nat.reduceEqDiff,reduceIte]
  decide +kernel

-- A nested bare failure skips both export layers, the outer allocation and suffix.
def failingInner : Stmt C Input (Results ++ Input) :=
  .call "failedInner" innerArgs (.rets binders) failedBody
def failingBody : Prog C Input BodyCtx :=
  .cons (.block (.cons failingInner transfer))
  (.cons (.declMem A (.user "unreachable") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl) .nil)
def failingCall : Stmt C Caller Final := .call "failedOuter" arguments ret failingBody
def failingProgram : Prog C Caller Caller :=
  .cons (.block (.cons failingCall nextUse)) suffix
def failingProducer : Calls.Program 1 prefixProducer.frag failingProgram :=
  (TuplePrograms.compile 1 prefixProducer.frag failingProgram).get (by decide +kernel)
attribute [irreducible] failingProducer

theorem nested_failure_source : failingProgram.run caller.st = .error .revert := by
  have h : (match failingProgram.run caller.st with
      | .error .revert => true | _ => false) = true := by decide +kernel
  cases hx : failingProgram.run caller.st with
  | error e => cases e <;> simp only [hx, Bool.false_eq_true] at h <;> rfl
  | ok o => simp only [hx, Bool.false_eq_true] at h
theorem unreachable_cost : (failingProducer.allocates,failingProducer.cost caller.st) = (true,0) := by decide +kernel
theorem nested_failure_target : Evm.run (prefixProducer.code ++ failingProducer.code) machine = .revert := by
  have capacity : AllocationInput 1 128 (prefixProducer.cost initial) initial bases machine :=
    .inr ⟨by decide, wmod 256, initial_repr.2, by decide +kernel⟩
  obtain ⟨m₁,base₁,ht,hr,hk,he,ha⟩ := program_endpoint prefixProducer initial_repr.1
    (by decide +kernel) capacity caller actual_prefix
  have noCost : AllocationInput 1 128 (failingProducer.cost caller.st) caller.st base₁ m₁ :=
    .inl (congrArg Prod.snd unreachable_cost)
  rw [run_append_ok ht]
  exact TuplePrograms.program_revert (L := 1) (frame := 128) (σ := caller.st) (base := base₁) (m := m₁)
    failingProducer hr (by decide +kernel) noCost nested_failure_source

theorem data_refusal : (TuplePrograms.compile 1 prefixProducer.frag
    (.cons (.call "data" arguments ret refusedBody) .nil)).isSome = false := by decide +kernel

def storageResult : Stmt C Caller (.alias A :: Caller) :=
  .call "storage" (.nil : Args C Caller []) (.storage A (.user "r")) (.nil : Prog C [.alias A] [.alias A])
theorem storage_refusal : (TuplePrograms.compile 1 prefixProducer.frag
    (.cons storageResult .nil)).isSome = false := by decide +kernel

def recursive : Stmt C Caller Final :=
  .callRec "recursive" 2 arguments ret (fun _ => .nil)
theorem recursion_refusal : (TuplePrograms.compile 1 prefixProducer.frag
    (.cons recursive .nil)).isSome = false := by decide +kernel

#print_checked_axioms source_outer,
  source_used,
  source_scoped,
  source_suffix,
  source_program,
  ordered_export,
  ordered_used,
  ordered_unwind,
  ordered_final,
  traversal_and_refusal,
  represented,
  nested_entry_order,
  nested_body_order,
  nested_export_order,
  nested_transfer_order,
  nested_heap_sizes,
  target_body,
  target_export,
  target_unwind,
  target_final,
  exact_cost_frame,
  checked_input_endpoint,
  wrong_order,
  wrong_private_alias,
  wrong_old_contents,
  wrong_unrelated,
  wrong_frame_cost,
  wrong_cursor,
  wrong_overlap,
  nested_failure_source,
  unreachable_cost,
  nested_failure_target,
  data_refusal,
  storage_refusal,
  recursion_refusal,
  TuplePrograms.compile,
  TuplePrograms.program_revert

end Solidity.Backend.InternalFlow.TupleCallChecks.Composed

namespace Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard
open Evm Evm.Memory PublishedDirectCalls TupleCalls

def output : Solidity.Out C caller.st.H Caller :=
  ⟨exported.st.drop (Ext.append Caller Results), exported.ext⟩
def statement : Stmt C Caller Caller := .block (.cons outerCall .nil)
def checked : Calls.Statement 1 prefixProducer.frag statement :=
  TupleCalls.Scoped.statement "outerTriple" arguments binders nestedBody expandedProducer

theorem source : statement.run caller.st = .ok output := by
  change ((Prog.cons outerCall .nil).run caller.st).map _ = _
  rw [Prog.run_cons_ok source_outer, Prog.run_nil]
  rfl

theorem full_source : (contents output.st, callerObs output.st) =
    (some [[2,19,11],[3,23,29,31],[2,99,101],[1,55]], ([some 1,some 0,some 0],42)) := by
  exact congrArg (fun x => (x.1,(x.2.2,x.2.1[3]!))) ordered_export

theorem expanded_source :
    (Stmt.block (expand arguments binders nestedBody)).runSt caller.st = .ok output.st := by
  apply (TupleCalls.Scoped.scoped_tuple_expansion "outerTriple" arguments binders nestedBody caller.st).symm.trans
  change (statement.run caller.st).map _ = _
  rw [source]; rfl

theorem fields : checked.code = expandedProducer.code ∧ checked.need = 15 ∧
    checked.cost caller.st = 5 := by
  refine ⟨rfl,?_,actualExpandedCost⟩
  exact congrArg (fun xs => xs[1]!) exact_cost_frame

theorem target : ∃ m₁ base₁ m₂ base₂,
    Evm.run prefixProducer.code machine = .ok m₁ 0 ∧
    Evm.run checked.code m₁ = .ok m₂ 0 ∧
    StateRepr 1 1 128 prefixProducer.frag caller.st base₁ m₁ ∧
    StateRepr 1 1 128 checked.frag output.st base₂ m₂ ∧
    m₁.stack = machine.stack ∧ m₂.stack = m₁.stack ∧
    BaseExtends caller.st.H base₁ base₂ ∧
    GrowsAllocator 1 128 5 caller.st base₁ m₁ output.st base₂ m₂ := by
  have pc : prefixProducer.cost initial = 7 := congrArg (fun xs => xs[5]!) exact_frame_cost
  have pn : prefixProducer.need = 4 := congrArg (fun xs => xs[0]!) exact_frame_cost
  have capacity : AllocationInput 1 128
      (prefixProducer.cost initial + checked.cost caller.st) initial bases machine :=
    .inr ⟨by decide, wmod 256, initial_repr.2, by rw [pc,fields.2.2]; decide⟩
  have reached := TupleCalls.Scoped.program_statement_endpoint prefixProducer checked initial_repr.1
    (by rw [pn]; decide) (by rw [fields.2.1]; decide) caller output capacity actual_prefix source
  simpa only [fields.2.2] using reached


/-- Every physical cell remains observed; dropping locals does not erase memory. -/
theorem full_target : words (Evm.run (prefixProducer.code ++ checked.code) machine)
    [0,127,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,256,257,258,259,260,261,262,263,264,265,266,267] =
    some [77,268,99,42,256,256,259,266,42,17,30,1,266,29,1,29,1,263,2,19,11,3,23,29,31,2,99,101,1,55] := by
  rw [fields.1]
  exact target_body

theorem actual_extension : output.ext = exported.ext := rfl

theorem wrong_caller : callerObs output.st ≠ ([some 1,some 0,some 0],17) := by
  rw [show callerObs output.st = ([some 1,some 0,some 0],42) from congrArg Prod.snd full_source]
  decide

theorem private_does_not_escape : callerObs output.st ≠ ([some 1,some 2,some 0],42) := by
  rw [show callerObs output.st = ([some 1,some 0,some 0],42) from congrArg Prod.snd full_source]
  decide

theorem wrong_contents : contents output.st ≠
    some [[2,7,11],[3,23,29,31],[2,99,101],[1,55]] := by
  rw [show contents output.st = some [[2,19,11],[3,23,29,31],[2,99,101],[1,55]] from congrArg Prod.fst full_source]
  decide

theorem wrong_cost : checked.cost caller.st ≠ 0 := by
  rw [fields.2.2]
  decide

theorem bare_failure :
    (Stmt.block (.cons (.call "failedTuple" arguments ret failedBody) .nil)).runSt caller.st =
      .error .revert := by
  rw [Stmt.runSt_block,Prog.runSt_single]
  change (((Stmt.call "failedTuple" arguments ret failedBody).run caller.st).map (·.st)).map
    (State.drop (Ext.append Caller Results)) = _
  rw [tuple_failure_source]
  rfl



end Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard

/--
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.actualSelectorResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.actualCallConstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.actualExpandedTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.actualExpandedSelection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.actualOuterConstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.actualExpandedCost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.actualExpandedTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.full_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.expanded_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.full_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.actual_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.wrong_caller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.private_does_not_escape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.wrong_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.wrong_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.bare_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.scope_run_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.scope_has_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
---
info: 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.scope_state_drop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print_checked_axioms Solidity.Backend.InternalFlow.TupleCallChecks.actualSelectorResult, Solidity.Backend.InternalFlow.TupleCallChecks.actualCallConstruction, Solidity.Backend.InternalFlow.TupleCallChecks.actualExpandedTarget, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.actualExpandedSelection, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.actualOuterConstruction, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.actualExpandedCost, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.actualExpandedTarget, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.source, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.full_source, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.expanded_source, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.fields, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.target, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.full_target, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.actual_extension, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.wrong_caller, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.private_does_not_escape, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.wrong_contents, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.wrong_cost, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.bare_failure, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.scope_run_state, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.scope_has_output, Solidity.Backend.InternalFlow.TupleCallChecks.Composed.scope_state_drop
