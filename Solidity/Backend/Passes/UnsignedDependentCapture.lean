import Solidity.Backend.PrimitivePackets.UnsignedDiv.Composition
import Solidity.Backend.Passes.MappedTail
import Solidity.Backend.Passes.ValueCertificate

/-! Capture a quotient, then evaluate the next remainder at the ACTUAL new
context: (a/d) % a. Arithmetic stays in the published unsigned producer. -/
namespace Solidity.Backend.Passes.UnsignedDependentCapture
open Evm Evm.Memory Evm.Compiler Backend.PrimitivePackets.UnsignedDiv
variable {C : Contract} {Γ : Ctx}

def first (name : Var) : Prog C (modelContext Γ) (.val .uint :: modelContext Γ) :=
  .cons (.declLocal .uint name (some (modelDiv C Γ))) .nil
def second (name : Var) : Prog C (.val .uint :: modelContext Γ) (.val .uint :: .val .uint :: modelContext Γ) :=
  .cons (.declLocal .uint name (some (modelMod C (.val .uint :: Γ)))) .nil
def program (qname rname : Var) := (first (C := C) (Γ := Γ) qname).join (second (C := C) rname)
def firstCode (b : Nat) (F : Frag (modelContext Γ)) (name : Var) : CompiledProg b F (first (C := C) name) :=
  (compileProg b F (first name)).get (by rfl)
def secondCode (b : Nat) (F : Frag (modelContext Γ)) (qname rname : Var) :
    CompiledProg b (firstCode (C := C) b F qname).frag (second (C := C) rname) :=
  (compileProg b (firstCode (C := C) b F qname).frag (second (C := C) rname)).get (by rfl)
def code (b : Nat) (F : Frag (modelContext Γ)) (qname rname : Var) :
    CompiledProg b F (program (C := C) qname rname) :=
  (compileProg b F (program qname rname)).get (by rfl)

theorem public_selection (b : Nat) (F : Frag (modelContext Γ)) (qname rname : Var) :
    compileProg (C := C) b F (program qname rname) = some (code (C := C) b F qname rname) := rfl

theorem code_join (b : Nat) (F : Frag (modelContext Γ)) (qname rname : Var) :
    (code (C := C) b F qname rname).code =
      (firstCode (C := C) b F qname).code ++ (secondCode (C := C) b F qname rname).code := rfl

theorem first_emitted (b : Nat) (F : Frag (modelContext Γ)) (name : Var) :
    (firstCode (C := C) b F name).code =
      (selectedDiv (C := C) b F).code ++ [.mstore (cell (b+(modelContext Γ).length))] := rfl

theorem second_emitted (b : Nat) (F : Frag (modelContext Γ)) (qname rname : Var) :
    (secondCode (C := C) b F qname rname).code =
      (selectedMod (C := C) (Γ := .val .uint :: Γ) b (firstCode (C := C) b F qname).frag).code ++
      [.mstore (cell (b+((modelContext Γ).length+1)))] := rfl

theorem declare_source {Δ : Ctx} {p : PrimTy} (e : Val C Δ p) (name : Var)
    (state : State C Δ) (v : p.Denote) (evaluated : e.evalT state = .ok v) :
    (Prog.cons (.declLocal p name (some e)) .nil).run state =
      .ok ⟨state.push (t := .val p) v,List.prefix_refl _⟩ := by
  have step : (Stmt.declLocal p name (some e)).run state =
      .ok ⟨state.push (t := .val p) v,List.prefix_refl _⟩ := by
    change TRun.declLocal p (some e) state = _
    simp only [TRun.declLocal,evaluated,bind,Except.bind,pure,Except.pure]
  rw [Prog.run_cons_ok step]
  rfl

theorem first_input {b L frame : Nat} {F : Frag (modelContext Γ)} (name : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+((modelContext Γ).length+1) ≤ frame) :
    (Compilation.memory (firstCode (C := C) b F name)).Input L frame base state machine := by
  refine ⟨represented,?_,Or.inl rfl⟩
  change b+max (max (modelContext Γ).length (max ((modelContext Γ).length+1) 0))
    ((modelContext Γ).length+1) ≤ frame
  omega

theorem actual_link {b L frame : Nat} {F : Frag (modelContext Γ)} (qname rname : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (capacity : b+((modelContext Γ).length+2) ≤ frame) :
    MappedBoundaryLink (.memory (firstCode (C := C) b F qname)) (.memory (secondCode (C := C) b F qname rname))
      L frame base state machine := by
  apply memory_nonallocating_mapped_link
  · change b+max (max ((modelContext Γ).length+1) (max ((modelContext Γ).length+2) 0))
      ((modelContext Γ).length+2) ≤ frame
    omega
  · rfl

theorem whole_input {b L frame : Nat} {F : Frag (modelContext Γ)} (qname rname : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+((modelContext Γ).length+2) ≤ frame) :
    (Compilation.memory (code (C := C) b F qname rname)).Input L frame base state machine := by
  refine ⟨represented,?_,Or.inl rfl⟩
  change b+max (max (modelContext Γ).length (max ((modelContext Γ).length+1) 0))
    (max (max ((modelContext Γ).length+1) (max ((modelContext Γ).length+2) 0))
      ((modelContext Γ).length+2)) ≤ frame
  omega

theorem compose_mapped {b L frame : Nat} {F : Frag (modelContext Γ)} (qname rname : Var)
    {state : State C (modelContext Γ)} {base midBase outBase : Nat → Fin W}
    {machine mid final : Machine} (q r : Uint)
    (left : MappedOutput (.memory (firstCode (C := C) b F qname)) L frame base state machine
      (state.push (t := .val .uint) q) mid midBase)
    (right : MappedOutput (.memory (secondCode (C := C) b F qname rname)) L frame midBase
      (state.push (t := .val .uint) q) mid
      ((state.push (t := .val .uint) q).push (t := .val .uint) r) final outBase) :
    MappedOutput (.memory (code (C := C) b F qname rname)) L frame base state machine
      ((state.push (t := .val .uint) q).push (t := .val .uint) r) final outBase := by
  refine ⟨right.1,?_,?_⟩
  · intro R ref
    exact (right.2.1 ref).trans (left.2.1 ref)
  · exact GrowsAllocator.comp left.2.2 right.2.2

/-- The real quotient, canonical machine and selected map are fixed before
all saved tails. Each tail has its actual full prefix output and transported
second Input at that tail's reached machine. -/
theorem reached_prefix {b L frame : Nat} {F : Frag (modelContext Γ)} (qname rname : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+((modelContext Γ).length+2) ≤ frame) (nonzero : state.env.2.1.val ≠ 0) :
    ∃ q : Uint, q.val = state.env.1.val.tdiv state.env.2.1.val ∧
      (first qname).run state = .ok ⟨state.push (t := .val .uint) q,List.prefix_refl _⟩ ∧
      ∃ (mid : Machine) (midBase : Nat → Fin W), mid.stack = [] ∧ ∀ tail,
        run (firstCode (C := C) b F qname).code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
        MappedOutput (.memory (firstCode (C := C) b F qname)) L frame base state {machine with stack := tail}
          (state.push (t := .val .uint) q) {mid with stack := tail} midBase ∧
        (Compilation.memory (secondCode (C := C) b F qname rname)).Input L frame midBase
          (state.push (t := .val .uint) q) {mid with stack := tail} := by
  obtain ⟨q,value,qval⟩ := div_result state.env.1 state.env.2.1 nonzero
  have evaluated : (modelDiv C Γ).evalT state = .ok q := by rw [div_eval,value]; rfl
  have source := declare_source (modelDiv C Γ) qname state q evaluated
  have room : b+((modelContext Γ).length+1) ≤ frame := by omega
  obtain ⟨mid,midBase,_,empty,allRuns⟩ := compilation_success_shared_mapped
    (.memory (firstCode (C := C) b F qname)) (first_input qname represented room) rfl source
  refine ⟨q,qval,source,mid,midBase,empty,?_⟩
  intro tail
  have mapped := (allRuns tail).2
  rw [(firstCode (C := C) b F qname).cert.pushes_zero,Nat.add_zero] at mapped
  exact ⟨(allRuns tail).1,mapped,
    actual_link qname rname capacity _ _ _ source (allRuns tail).1 mapped⟩

/-- Successful second capture uses the reached quotient and original numerator,
not a replacement operand context or stale initial representation. -/
theorem success {b L frame : Nat} {F : Frag (modelContext Γ)} (qname rname : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+((modelContext Γ).length+2) ≤ frame)
    (divisor : state.env.2.1.val ≠ 0) (numerator : state.env.1.val ≠ 0) :
    ∃ (q r : Uint), q.val = state.env.1.val.tdiv state.env.2.1.val ∧
      r.val = q.val.tmod state.env.1.val ∧
      (program qname rname).run state =
        .ok ⟨(state.push (t := .val .uint) q).push (t := .val .uint) r,List.prefix_refl _⟩ ∧
      ∃ (mid final : Machine) (midBase outBase : Nat → Fin W),
        mid.stack = [] ∧ final.stack = [] ∧ ∀ tail,
        run (firstCode (C := C) b F qname).code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
        MappedOutput (.memory (firstCode (C := C) b F qname)) L frame base state {machine with stack := tail}
          (state.push (t := .val .uint) q) {mid with stack := tail} midBase ∧
        (Compilation.memory (secondCode (C := C) b F qname rname)).Input L frame midBase
          (state.push (t := .val .uint) q) {mid with stack := tail} ∧
        run (secondCode (C := C) b F qname rname).code {mid with stack := tail} = .ok {final with stack := tail} 0 ∧
        MappedOutput (.memory (secondCode (C := C) b F qname rname)) L frame midBase
          (state.push (t := .val .uint) q) {mid with stack := tail}
          ((state.push (t := .val .uint) q).push (t := .val .uint) r) {final with stack := tail} outBase ∧
        run (code (C := C) b F qname rname).code {machine with stack := tail} = .ok {final with stack := tail} 0 ∧
        MappedOutput (.memory (code (C := C) b F qname rname)) L frame base state {machine with stack := tail}
          ((state.push (t := .val .uint) q).push (t := .val .uint) r) {final with stack := tail} outBase := by
  obtain ⟨q,qval,firstSource,mid,midBase,midEmpty,firstRuns⟩ := reached_prefix qname rname represented capacity divisor
  obtain ⟨r,value,rval⟩ := mod_result q state.env.1 numerator
  have evaluated : (modelMod C (.val .uint :: Γ)).evalT (state.push (t := .val .uint) q) = .ok r := by
    rw [mod_eval]
    change TRes.ofOpt (BinOp.mod.evalT rfl q state.env.1) = .ok r
    rw [value]
    rfl
  have secondSource : (second (C := C) (Γ := Γ) rname).run (state.push (t := .val .uint) q) =
      .ok ⟨(state.push (t := .val .uint) q).push (t := .val .uint) r,List.prefix_refl _⟩ :=
    declare_source (modelMod C (.val .uint :: Γ)) rname (state.push (t := .val .uint) q) r evaluated
  obtain ⟨final,outBase,_,finalEmpty,secondRuns⟩ := compilation_success_shared_mapped
    (.memory (secondCode (C := C) b F qname rname)) (firstRuns []).2.2 rfl secondSource
  refine ⟨q,r,qval,rval,?_,mid,final,midBase,outBase,midEmpty,finalEmpty,?_⟩
  · rw [program,DeferredSource.join_run]
    simp only [TRun.seq,firstSource,secondSource,Except.map]
  · intro tail
    have mapped := (secondRuns tail).2
    rw [(secondCode (C := C) b F qname rname).cert.pushes_zero,Nat.add_zero] at mapped
    refine ⟨(firstRuns tail).1,(firstRuns tail).2.1,(firstRuns tail).2.2,
      secondRuns tail |>.1,mapped,?_,compose_mapped qname rname q r (firstRuns tail).2.1 mapped⟩
    rw [code_join,run_append_ok (firstRuns tail).1]
    exact (secondRuns tail).1

/-- Independent Source expressions use the SAME actual selected quotient and
remainder witnesses, including the reached extended operand locals. This does
not assert Source declaration lowering or Source/model heap agreement. -/
theorem component_origins {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (sourceTail : Source.Locals E.layout Δ) (sourceState : Source.St E)
    {b L frame : Nat} {F : Frag (modelContext Γ)} (qname rname : Var)
    {state : State C (modelContext Γ)} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+((modelContext Γ).length+2) ≤ frame)
    (divisor : state.env.2.1.val ≠ 0) (numerator : state.env.1.val ≠ 0) :
    let actual := success qname rname represented capacity divisor numerator
    let q := actual.choose
    let r := actual.choose_spec.choose
    type_of% actual.choose_spec.choose_spec ∧
    (Source.evalE G fr (fuel+3) (sourceDiv E Δ)).run
      (sourceLocals state.env.1 state.env.2.1 sourceTail,sourceState) =
      (.ok (.val (sourceUInt E.layout q)),(sourceLocals state.env.1 state.env.2.1 sourceTail,sourceState)) ∧
    (Source.evalE G fr (fuel+3) (sourceMod E (.int Source.IntTy.u256 :: Δ))).run
      (sourceLocals q state.env.1 (.cons (sourceUInt E.layout state.env.2.1) sourceTail),sourceState) =
      (.ok (.val (sourceUInt E.layout r)),
        (sourceLocals q state.env.1 (.cons (sourceUInt E.layout state.env.2.1) sourceTail),sourceState)) := by
  let actual := success qname rname represented capacity divisor numerator
  have exactSpec := actual.choose_spec.choose_spec
  refine ⟨exactSpec,?_,?_⟩
  · rw [source_div_origin,source_div_result E.layout fr.checked _ _ _ divisor exactSpec.1]
    rfl
  · rw [source_mod_origin,source_mod_result E.layout fr.checked _ _ _ numerator exactSpec.2.1]
    rfl

/-- info: 'Solidity.Backend.Passes.UnsignedDependentCapture.declare_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms declare_source
/-- info: 'Solidity.Backend.Passes.UnsignedDependentCapture.first_emitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_emitted
/-- info: 'Solidity.Backend.Passes.UnsignedDependentCapture.second_emitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms second_emitted
/-- info: 'Solidity.Backend.Passes.UnsignedDependentCapture.component_origins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms component_origins
/-- info: 'Solidity.Backend.Passes.UnsignedDependentCapture.whole_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms whole_input
/-- info: 'Solidity.Backend.Passes.UnsignedDependentCapture.compose_mapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compose_mapped
/-- info: 'Solidity.Backend.Passes.UnsignedDependentCapture.public_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_selection
/-- info: 'Solidity.Backend.Passes.UnsignedDependentCapture.code_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms code_join
/-- info: 'Solidity.Backend.Passes.UnsignedDependentCapture.first_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms first_input
/-- info: 'Solidity.Backend.Passes.UnsignedDependentCapture.actual_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actual_link
/-- info: 'Solidity.Backend.Passes.UnsignedDependentCapture.reached_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reached_prefix
/-- info: 'Solidity.Backend.Passes.UnsignedDependentCapture.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms success
end Solidity.Backend.Passes.UnsignedDependentCapture
