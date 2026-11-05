import Solidity.Backend.PrimitivePackets.SignedDiv.Execution
import Solidity.Backend.Passes.CapturedValueStability
import Solidity.Backend.Passes.MappedTail

/-! Consume the published signed-division family, then capture its value before
mutating the old divisor. Arithmetic/guard/Source-expression proofs remain owned
by the primitive producer. No Source statement lowering is claimed. -/
namespace Solidity.Backend.Passes.SignedDivisionCapture
open Evm Evm.Memory Evm.Compiler Backend.PrimitivePackets
variable {C : Contract} {Γ : Ctx}

def update : Val C (.val .int :: Γ) .int := .simple (.lit 0 (by decide))
def program (checked : Bool) (i j : Idx Γ (.val .int)) (x : Var) : Prog C Γ (.val .int :: Γ) :=
  CapturedValueStability.program x (Backend.PrimitivePackets.SignedDiv.expression checked i j) j update

theorem selectable (b : Nat) (F : Frag Γ) (checked : Bool)
    (i j : Idx Γ (.val .int)) (x : Var) :
    (Memory.compileProg (C := C) b F (program checked i j x)).isSome = true := by
  cases checked <;> rfl

def code (b : Nat) (F : Frag Γ) (checked : Bool) (i j : Idx Γ (.val .int)) (x : Var) :
    CompiledProg b F (program (C := C) checked i j x) :=
  (Memory.compileProg b F (program checked i j x)).get (selectable b F checked i j x)

theorem public_selection (b : Nat) (F : Frag Γ) (checked : Bool)
    (i j : Idx Γ (.val .int)) (x : Var) :
    Memory.compileProg (C := C) b F (program checked i j x) = some (code (C := C) b F checked i j x) :=
  (Option.some_get _).symm

def zero : PrimTy.int.Denote := ⟨0,by decide⟩
def result (state : State C Γ) (j : Idx Γ (.val .int)) (v : PrimTy.int.Denote) :
    Solidity.Out C state.H (.val .int :: Γ) :=
  ⟨(state.push (t := .val .int) v).setLocal (.there j) zero,List.prefix_refl _⟩
def reader (b : Nat) (F : Frag Γ) (checked : Bool) (i j : Idx Γ (.val .int)) (x : Var) :
    CompiledVal b (code (C := C) b F checked i j x).frag (.simple (.local .here) : Val C _ .int) :=
  (Memory.compileVal b (code (C := C) b F checked i j x).frag (.simple (.local .here))).get (by rfl)

theorem reader_public (b : Nat) (F : Frag Γ) (checked : Bool)
    (i j : Idx Γ (.val .int)) (x : Var) :
    Memory.compileVal b (code (C := C) b F checked i j x).frag
      (.simple (.local .here) : Val C (.val .int :: Γ) .int) =
      some (reader (C := C) b F checked i j x) := (Option.some_get _).symm

theorem input {b L frame : Nat} {F : Frag Γ} (checked : Bool)
    (i j : Idx Γ (.val .int)) (x : Var)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) :
    (Compilation.memory (code (C := C) b F checked i j x)).Input L frame base state machine := by
  refine ⟨represented,?_,?_⟩
  · change b + max (max Γ.length (max (Γ.length+1) 0))
      (max (max (Γ.length+1) (max (Γ.length+1) 0)) (Γ.length+1)) ≤ frame
    omega
  · cases checked <;> exact .inl rfl

theorem source (checked : Bool) (i j : Idx Γ (.val .int)) (x : Var)
    (state : State C Γ) (v : PrimTy.int.Denote)
    (evaluated : (SignedDiv.expression checked i j).evalT state = .ok v) :
    (program checked i j x).run state = .ok (result state j v) :=
  CapturedValueStability.source x (SignedDiv.expression checked i j) j update state v zero evaluated rfl

/-- The public whole-program recognizer supplies the actual prefix, map and
captured quotient. Clearing the old divisor cannot change the captured word. -/
theorem shared {b L frame : Nat} {F : Frag Γ} (checked : Bool)
    (i j : Idx Γ (.val .int)) (x : Var)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame)
    (v : PrimTy.int.Denote)
    (evaluated : (SignedDiv.expression checked i j).evalT state = .ok v) :
    ∃ (canonical : Machine) (selected : Nat → Fin W) (word : Word),
      canonical.stack = [] ∧ ReprV .int v word ∧ ∀ tail,
      (Compilation.memory (code (C := C) b F checked i j x)).Input L frame base state {machine with stack := tail} ∧
      run (code (C := C) b F checked i j x).code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      MappedOutput (.memory (code (C := C) b F checked i j x)) L frame base state {machine with stack := tail}
        (result state j v).st {canonical with stack := tail} selected ∧
      run (reader (C := C) b F checked i j x).code {canonical with stack := tail} =
        .ok ({canonical with stack := tail}.push word) 0 ∧
      run ((code (C := C) b F checked i j x).code ++ (reader (C := C) b F checked i j x).code) {machine with stack := tail} =
        .ok ({canonical with stack := tail}.push word) 0 := by
  let actual := code (C := C) b F checked i j x
  obtain ⟨canonical,selected,_,empty,runs⟩ := compilation_success_shared_mapped
    (.memory actual) (input checked i j x represented capacity) (by rfl)
    (source checked i j x state v evaluated)
  have mapped := (runs []).2
  rw [actual.cert.pushes_zero,Nat.add_zero] at mapped
  have captured : (Val.simple (.local .here) : Val C (.val .int :: Γ) .int).evalT (result state j v).st =
      .ok v := rfl
  obtain ⟨word,repr,reads⟩ := CapturedValueStability.value_shared _ (reader (C := C) b F checked i j x)
    mapped.1 v captured
  refine ⟨canonical,selected,word,empty,repr,?_⟩
  intro tail
  have full := (runs tail).2
  rw [actual.cert.pushes_zero,Nat.add_zero] at full
  have emitted : run actual.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 :=
    (runs tail).1
  refine ⟨compilation_input_stack (.memory actual) (input checked i j x represented capacity) tail,
    emitted,full,reads tail,?_⟩
  rw [run_append_ok emitted]
  exact reads tail

theorem ordinary_value (checked : Bool) (i j : Idx Γ (.val .int)) (state : State C Γ)
    (a d : PrimTy.int.Denote) (left : TEnv.get i state.env = a) (right : TEnv.get j state.env = d)
    (nonzero : d.val ≠ 0) (ordinary : ¬ (a.val = -((2^255:Nat):Int) ∧ d.val = -1)) :
    (SignedDiv.expression checked i j).evalT state = .ok (SignedDiv.quotient a d nonzero ordinary) := by
  rw [SignedDiv.expression_run state checked i j a d left right,
    SignedDiv.intrinsic_ordinary a d nonzero ordinary]
  cases checked <;> simp only [Bool.false_eq_true,if_false,if_true,ordinary,TRes.ofOpt]

/-- Actual independent Source local arithmetic is supplied by the published
producer; the new native capture/update execution is derived here. -/
theorem ordinary {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat) (src : Source.EMState E srcΓ)
    (state : State C Γ) (si sj : Source.Idx srcΓ (.int SignedDiv.T))
    (i j : Idx Γ (.val .int)) (checked : Bool) (x : Var)
    (a d : PrimTy.int.Denote)
    (sl : src.1.get si = SignedDiv.sourceValue a) (sr : src.1.get sj = SignedDiv.sourceValue d)
    (tl : TEnv.get i state.env = a) (tr : TEnv.get j state.env = d)
    (nonzero : d.val ≠ 0) (regular : ¬ (a.val = -((2^255:Nat):Int) ∧ d.val = -1))
    {b L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) :
    let v := SignedDiv.quotient a d nonzero regular
    (Source.evalE G {SF with checked := checked} (fuel+3)
      (.binary .div (.local si) (.local sj))).run src =
      (.ok (.val (SignedDiv.sourceValue v)),src) ∧
    (program checked i j x).run state = .ok (result state j v) ∧ type_of%
      (shared checked i j x represented capacity v (ordinary_value checked i j state a d tl tr nonzero regular)) := by
  have published := SignedDiv.ordinary_execution G {SF with checked := checked} fuel src state si sj i j
    a d sl sr tl tr nonzero regular represented []
  have value := ordinary_value checked i j state a d tl tr nonzero regular
  exact ⟨published.1,source checked i j x state _ value,shared checked i j x represented capacity _ value⟩

theorem rejected {b L frame : Nat} {F : Frag Γ} (checked : Bool)
    (i j : Idx Γ (.val .int)) (x : Var)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame)
    (failed : (SignedDiv.expression checked i j).evalT state = .error .revert) (tail : List Word) :
    (program checked i j x).run state = .error .revert ∧
    run ((code (C := C) b F checked i j x).code ++ (reader (C := C) b F checked i j x).code)
      {machine with stack := tail} = .revert := by
  have declaration : (Stmt.declLocal .int x (some (SignedDiv.expression checked i j))).run state = .error .revert := by
    change TRun.declLocal .int (some (SignedDiv.expression checked i j)) state = _
    simp only [TRun.declLocal,failed,bind,Except.bind]
  have native : (program checked i j x).run state = .error .revert :=
    Prog.run_cons_error declaration
  have emitted : run (code (C := C) b F checked i j x).code {machine with stack := tail} = .revert :=
    (compilation_revert_iff (.memory (code (C := C) b F checked i j x))
      (compilation_input_stack _ (input checked i j x represented capacity) tail) (by rfl)).mpr (.inl native)
  exact ⟨native,run_append_revert emitted⟩

end Solidity.Backend.Passes.SignedDivisionCapture

/-- info: 'Solidity.Backend.Passes.SignedDivisionCapture.selectable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCapture.selectable

/-- info: 'Solidity.Backend.Passes.SignedDivisionCapture.public_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCapture.public_selection

/-- info: 'Solidity.Backend.Passes.SignedDivisionCapture.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCapture.input

/-- info: 'Solidity.Backend.Passes.SignedDivisionCapture.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCapture.source

/-- info: 'Solidity.Backend.Passes.SignedDivisionCapture.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCapture.shared

/-- info: 'Solidity.Backend.Passes.SignedDivisionCapture.ordinary_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCapture.ordinary_value

/-- info: 'Solidity.Backend.Passes.SignedDivisionCapture.ordinary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCapture.ordinary

/-- info: 'Solidity.Backend.Passes.SignedDivisionCapture.rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCapture.rejected

/-- info: 'Solidity.Backend.Passes.SignedDivisionCapture.reader_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedDivisionCapture.reader_public
