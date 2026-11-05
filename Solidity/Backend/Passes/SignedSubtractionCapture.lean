import Solidity.Backend.PrimitivePackets.SignedSub.Execution
import Solidity.Backend.Passes.CapturedValueStability
import Solidity.Backend.Passes.MappedTail

/-! Capture the public unchecked int256 subtraction result before changing the
old subtrahend. Wrapping arithmetic and Source expression evaluation remain the
published producer's work; this adds no arithmetic or replacement semantics. -/
namespace Solidity.Backend.Passes.SignedSubtractionCapture
open Evm Evm.Memory Evm.Compiler Backend.PrimitivePackets Solidity.Lowering.V07
variable {C : Contract} {Γ : Ctx}

def update : Val C (.val .int :: Γ) .int := .simple (.lit 0 (by decide))
def program (i j : Idx Γ (.val .int)) (x : Var) : Prog C Γ (.val .int :: Γ) :=
  CapturedValueStability.program x (SignedSub.value i j) j update

theorem selectable (b : Nat) (F : Frag Γ) (i j : Idx Γ (.val .int)) (x : Var) :
    (Memory.compileProg (C := C) b F (program i j x)).isSome = true := rfl

def code (b : Nat) (F : Frag Γ) (i j : Idx Γ (.val .int)) (x : Var) :
    CompiledProg b F (program (C := C) i j x) :=
  (Memory.compileProg b F (program i j x)).get (selectable b F i j x)

theorem public_selection (b : Nat) (F : Frag Γ) (i j : Idx Γ (.val .int)) (x : Var) :
    Memory.compileProg (C := C) b F (program i j x) = some (code (C := C) b F i j x) :=
  (Option.some_get _).symm

theorem emitted_code (b : Nat) (F : Frag Γ) (i j : Idx Γ (.val .int)) (x : Var) :
    (code (C := C) b F i j x).code =
      [.mload (cellOf b i),.mload (cellOf b j),.swap 1,.sub,
        .mstore (cell (b+Γ.length)),.push w[0],.mstore (cellOf b (.there (u := .val .int) j))] := rfl

def zero : PrimTy.int.Denote := ⟨0,by decide⟩
def result (state : State C Γ) (j : Idx Γ (.val .int)) (v : PrimTy.int.Denote) :
    Solidity.Out C state.H (.val .int :: Γ) :=
  ⟨(state.push (t := .val .int) v).setLocal (.there j) zero,List.prefix_refl _⟩
def reader (b : Nat) (F : Frag Γ) (i j : Idx Γ (.val .int)) (x : Var) :
    CompiledVal b (code (C := C) b F i j x).frag (.simple (.local .here) : Val C (.val .int :: Γ) .int) :=
  (Memory.compileVal b (code (C := C) b F i j x).frag (.simple (.local .here))).get (by rfl)

theorem reader_public (b : Nat) (F : Frag Γ) (i j : Idx Γ (.val .int)) (x : Var) :
    Memory.compileVal b (code (C := C) b F i j x).frag
      (.simple (.local .here) : Val C (.val .int :: Γ) .int) = some (reader (C := C) b F i j x) :=
  (Option.some_get _).symm

theorem input {b L frame : Nat} {F : Frag Γ} (i j : Idx Γ (.val .int)) (x : Var)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) :
    (Compilation.memory (code (C := C) b F i j x)).Input L frame base state machine := by
  refine ⟨represented,?_,.inl rfl⟩
  change b + max (max Γ.length (max (Γ.length+1) 0))
    (max (max (Γ.length+1) (max (Γ.length+1) 0)) (Γ.length+1)) ≤ frame
  omega

theorem source (i j : Idx Γ (.val .int)) (x : Var) (state : State C Γ) (v : PrimTy.int.Denote)
    (evaluated : (SignedSub.value i j).evalT state = .ok v) :
    (program i j x).run state = .ok (result state j v) :=
  CapturedValueStability.source x (SignedSub.value i j) j update state v zero evaluated rfl

/-- The original represented frame and real public compiler derive the actual
captured state/map before all saved tails. No arithmetic preservation premise. -/
theorem shared {b L frame : Nat} {F : Frag Γ} (i j : Idx Γ (.val .int)) (x : Var)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) (v : PrimTy.int.Denote)
    (evaluated : (SignedSub.value i j).evalT state = .ok v) :
    ∃ (canonical : Machine) (selected : Nat → Fin W) (word : Word),
      canonical.stack = [] ∧ ReprV .int v word ∧ ∀ tail,
      (Compilation.memory (code (C := C) b F i j x)).Input L frame base state {machine with stack := tail} ∧
      run (code (C := C) b F i j x).code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      MappedOutput (.memory (code (C := C) b F i j x)) L frame base state {machine with stack := tail}
        (result state j v).st {canonical with stack := tail} selected ∧
      run (reader (C := C) b F i j x).code {canonical with stack := tail} = .ok ({canonical with stack := tail}.push word) 0 ∧
      run ((code (C := C) b F i j x).code ++ (reader (C := C) b F i j x).code) {machine with stack := tail} =
        .ok ({canonical with stack := tail}.push word) 0 := by
  let actual := code (C := C) b F i j x
  obtain ⟨canonical,selected,_,empty,runs⟩ := compilation_success_shared_mapped
    (.memory actual) (input i j x represented capacity) (by rfl) (source i j x state v evaluated)
  have mapped := (runs []).2
  rw [actual.cert.pushes_zero,Nat.add_zero] at mapped
  have captured : (Val.simple (.local .here) : Val C (.val .int :: Γ) .int).evalT (result state j v).st = .ok v := rfl
  obtain ⟨word,repr,reads⟩ := CapturedValueStability.value_shared _ (reader (C := C) b F i j x) mapped.1 v captured
  refine ⟨canonical,selected,word,empty,repr,?_⟩
  intro tail
  have full := (runs tail).2
  rw [actual.cert.pushes_zero,Nat.add_zero] at full
  have emitted : run actual.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 := (runs tail).1
  refine ⟨compilation_input_stack (.memory actual) (input i j x represented capacity) tail,
    emitted,full,reads tail,?_⟩
  rw [run_append_ok emitted]
  exact reads tail

/-- Producer Source and native arithmetic are independently established; this
consumer adds public capture/update compilation, not Source assignment lowering. -/
theorem application {E : Source.Env} {srcΓ : Source.RCtx} {ι : Type}
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat) (src : Source.EMState E srcΓ)
    (state : State C Γ) (si : ι → Source.Idx srcΓ (.int SignedSub.ty)) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily SignedSub.ty si ti src.1 state.env) (a d : ι)
    (x y : Int) (hx : SignedSub.ty.lo ≤ x ∧ x ≤ SignedSub.ty.hi)
    (hy : SignedSub.ty.lo ≤ y ∧ y ≤ SignedSub.ty.hi)
    (sl : src.1.get (si a) = .int x hx) (sr : src.1.get (si d) = .int y hy) (name : Var)
    {b L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine) (capacity : b+(Γ.length+1) ≤ frame) :
    let v := integerValue SignedSub.ty (SignedSub.ty.wrap (x-y)) (SignedSub.ty.wrap_mem (x-y))
    (Source.evalE G {SF with checked := false} (fuel+3)
      (.binary .sub (.local (si a)) (.local (si d)))).run src =
      (.ok (.val (Source.intWrap SignedSub.ty (x-y))),src) ∧
    (program (ti a) (ti d) name).run state = .ok (result state (ti d) v) ∧ type_of%
      (shared (ti a) (ti d) name represented capacity v
        (SignedWordSubtraction.locals_transport G SF fuel src state si ti family a d x y hx hy sl sr).2.1) := by
  have published := SignedSub.execution G SF fuel src state si ti family a d x y hx hy sl sr L b frame F base machine represented
  have native := (SignedWordSubtraction.locals_transport G SF fuel src state si ti family a d x y hx hy sl sr).2.1
  exact ⟨published.1,source (ti a) (ti d) name state _ native,shared (ti a) (ti d) name represented capacity _ native⟩

end Solidity.Backend.Passes.SignedSubtractionCapture

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCapture.selectable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCapture.selectable

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCapture.public_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCapture.public_selection

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCapture.emitted_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCapture.emitted_code

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCapture.reader_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCapture.reader_public

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCapture.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCapture.input

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCapture.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCapture.source

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCapture.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCapture.shared

/-- info: 'Solidity.Backend.Passes.SignedSubtractionCapture.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedSubtractionCapture.application
