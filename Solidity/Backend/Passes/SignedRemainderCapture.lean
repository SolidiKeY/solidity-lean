import Solidity.Backend.PrimitivePackets.SignedMod.Selection
import Solidity.Backend.Passes.CapturedValueStability

/-! Capture a publicly selected signed remainder before zeroing the old divisor.
The producer retains the arithmetic, Source origin and numeric guard contract;
this adds an actual typed pass application, not opcode or ABI adequacy. -/
namespace Solidity.Backend.Passes.SignedRemainderCapture
open Evm Evm.Memory Evm.Compiler Backend.PrimitivePackets
variable {C : Contract} {Γ : Ctx}

def update : Val C (.val .int :: Γ) .int := .simple (.lit 0 (by decide))
def program (i j : Idx Γ (.val .int)) (name : Var) : Prog C Γ (.val .int :: Γ) :=
  CapturedValueStability.program name (SignedMod.expression i j) j update

theorem selectable (b : Nat) (F : Frag Γ) (i j : Idx Γ (.val .int)) (name : Var) :
    (Memory.compileProg (C := C) b F (program i j name)).isSome = true := rfl

def code (b : Nat) (F : Frag Γ) (i j : Idx Γ (.val .int)) (name : Var) :
    CompiledProg b F (program (C := C) i j name) :=
  (Memory.compileProg b F (program i j name)).get (selectable b F i j name)

def whole (b : Nat) (F : Frag Γ) (i j : Idx Γ (.val .int)) (name : Var) :
    Compilation b F (program (C := C) i j name) := .memory (code b F i j name)

def updateCode (b : Nat) (F : Frag Γ) : CompiledVal b (F.push (.val .int) .ok) (update (C := C)) :=
  (Memory.compileVal b (F.push (.val .int) .ok) update).get (by rfl)

theorem public_selection (b : Nat) (F : Frag Γ) (i j : Idx Γ (.val .int)) (name : Var) :
    Memory.compileProg (C := C) b F (program i j name) = some (code b F i j name) :=
  (Option.some_get _).symm

theorem whole_eq (b : Nat) (F : Frag Γ) (i j : Idx Γ (.val .int)) (name : Var) :
    whole (C := C) b F i j name = CapturedValueStability.compiled name (SignedMod.expression i j)
      (SignedMod.selected b F i j) j update (updateCode b F) := rfl

def zero : PrimTy.int.Denote := ⟨0,by decide⟩
def result (state : State C Γ) (j : Idx Γ (.val .int)) (v : PrimTy.int.Denote) :
    Solidity.Out C state.H (.val .int :: Γ) :=
  ⟨(state.push (t := .val .int) v).setLocal (.there j) zero,List.prefix_refl _⟩

def reader (b : Nat) (F : Frag Γ) (i j : Idx Γ (.val .int)) (name : Var) :
    CompiledVal b (code (C := C) b F i j name).frag (.simple (.local .here) : Val C (.val .int :: Γ) .int) :=
  (Memory.compileVal b (code (C := C) b F i j name).frag (.simple (.local .here))).get (by rfl)

theorem reader_public (b : Nat) (F : Frag Γ) (i j : Idx Γ (.val .int)) (name : Var) :
    Memory.compileVal b (code (C := C) b F i j name).frag
      (.simple (.local .here) : Val C (.val .int :: Γ) .int) = some (reader b F i j name) :=
  (Option.some_get _).symm

theorem value_nonzero (state : State C Γ) (i j : Idx Γ (.val .int)) (x y : Int)
    (hx : SignedMod.Range x) (hy : SignedMod.Range y) (nonzero : y ≠ 0)
    (left : TEnv.get i state.env = SignedMod.lower x hx)
    (right : TEnv.get j state.env = SignedMod.lower y hy) :
    (SignedMod.expression i j).evalT state =
      .ok (SignedMod.lower (x.tmod y) (SignedMod.remainder_range x y hy nonzero)) := by
  have l : (Val.simple (.local i) : Val C Γ .int).evalT state = .ok (SignedMod.lower x hx) := congrArg Except.ok left
  have r : (Val.simple (.local j) : Val C Γ .int).evalT state = .ok (SignedMod.lower y hy) := congrArg Except.ok right
  rw [SignedMod.expression,StatefulValues.binary_source (op := .mod) l r rfl,SignedMod.target_nonzero x y hx hy nonzero]
  rfl

/-- Physical capture/readback, using the public whole program and fixed actual
base map for every tail. No guessed post-state or arithmetic implementation. -/
theorem physical {b L frame : Nat} {F : Frag Γ} (i j : Idx Γ (.val .int)) (name : Var)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) (v : PrimTy.int.Denote)
    (evaluated : (SignedMod.expression i j).evalT state = .ok v) :
    ∃ captured updated, ReprV .int v captured ∧ ReprV .int zero updated ∧ ∀ tail,
      let cm := writeMachine {machine with stack := tail} (cell (b+Γ.length)) captured
      let em := writeMachine cm (cellOf b (.there (u := .val .int) j)) updated
      (whole (C := C) b F i j name).Input L frame base state {machine with stack := tail} ∧
      run (whole (C := C) b F i j name).code {machine with stack := tail} = .ok em 0 ∧
      MappedOutput (whole (C := C) b F i j name) L frame base state {machine with stack := tail}
        (result state j v).st em base ∧
      run (reader (C := C) b F i j name).code em = .ok (em.push captured) 0 ∧
      run ((whole (C := C) b F i j name).code ++ (reader (C := C) b F i j name).code)
        {machine with stack := tail} = .ok (em.push captured) 0 := by
  obtain ⟨captured,updated,cr,ur,runs⟩ := CapturedValueStability.execution name (SignedMod.expression i j)
    (SignedMod.selected b F i j) j update (updateCode b F) represented capacity v zero evaluated rfl
  refine ⟨captured,updated,cr,ur,?_⟩
  intro tail
  have h := runs tail
  have emitted : run (whole (C := C) b F i j name).code {machine with stack := tail} =
      .ok (writeMachine (writeMachine {machine with stack := tail} (cell (b+Γ.length)) captured)
        (cellOf b (.there (u := .val .int) j)) updated) 0 := h.2.2.2.2.1
  refine ⟨h.1,emitted,h.2.2.2.1,h.2.2.2.2.2,?_⟩
  rw [run_append_ok emitted]
  exact h.2.2.2.2.2

/-- Original numeric zero-test/body capacities stay explicit. This conjunction
keeps the numeric guarded component separate from symbolic pass execution. -/
theorem application {E : Source.Env} {srcΓ : Source.RCtx}
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat) (src : Source.EMState E srcΓ) (state : State C Γ)
    (si sj : Source.Idx srcΓ (.int SignedMod.ty)) (i j : Idx Γ (.val .int)) (name : Var)
    (x y : Int) (hx : SignedMod.Range x) (hy : SignedMod.Range y) (nonzero : y ≠ 0)
    (sl : src.1.get si = .int x hx) (sr : src.1.get sj = .int y hy)
    (tl : TEnv.get i state.env = SignedMod.lower x hx) (tr : TEnv.get j state.env = SignedMod.lower y hy)
    {b L frame : Nat} {F : Frag Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine) (capacity : b+(Γ.length+1) ≤ frame)
    (saved : List (Fin W))
    (testCapacity : Backend.Scalar.stackBound (Backend.Scalar.zeroTest ⟨1,by decide⟩) ((saved.length+2:Nat):Int) = true)
    (bodyCapacity : Backend.Scalar.stackBound [.op .SMOD] ((saved.length+2:Nat):Int) = true) :
    type_of% (SignedMod.selected_remainder G SF fuel src state si sj i j x y hx hy sl sr tl tr
      b L frame F base machine represented saved testCapacity bodyCapacity) ∧ type_of%
    (physical i j name represented capacity
      (SignedMod.lower (x.tmod y) (SignedMod.remainder_range x y hy nonzero))
      (value_nonzero state i j x y hx hy nonzero tl tr)) :=
  ⟨SignedMod.selected_remainder G SF fuel src state si sj i j x y hx hy sl sr tl tr
      b L frame F base machine represented saved testCapacity bodyCapacity,
    physical i j name represented capacity _ (value_nonzero state i j x y hx hy nonzero tl tr)⟩

theorem input {b L frame : Nat} {F : Frag Γ} (i j : Idx Γ (.val .int)) (name : Var)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine) (capacity : b+(Γ.length+1) ≤ frame) :
    (whole (C := C) b F i j name).Input L frame base state machine :=
  CapturedValueStability.input name (SignedMod.expression i j) (SignedMod.selected b F i j)
    j update (updateCode b F) represented capacity

theorem value_zero (state : State C Γ) (i j : Idx Γ (.val .int)) (x : Int)
    (hx : SignedMod.Range x) (hz : SignedMod.Range 0)
    (left : TEnv.get i state.env = SignedMod.lower x hx)
    (right : TEnv.get j state.env = SignedMod.lower 0 hz) :
    (SignedMod.expression i j).evalT state = .error .revert := by
  have l : (Val.simple (.local i) : Val C Γ .int).evalT state = .ok (SignedMod.lower x hx) := congrArg Except.ok left
  have r : (Val.simple (.local j) : Val C Γ .int).evalT state = .ok (SignedMod.lower 0 hz) := congrArg Except.ok right
  simp only [SignedMod.expression,StatefulValues.binary_source (op := .mod) l r rfl,SignedMod.target_zero x hx hz,TRes.ofOpt]

theorem rejected {b L frame : Nat} {F : Frag Γ} (i j : Idx Γ (.val .int)) (name : Var)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine) (capacity : b+(Γ.length+1) ≤ frame)
    (failed : (SignedMod.expression i j).evalT state = .error .revert) (tail : List Word) :
    (program i j name).run state = .error .revert ∧
    run ((whole (C := C) b F i j name).code ++ (reader (C := C) b F i j name).code)
      {machine with stack := tail} = .revert := by
  have declaration : (Stmt.declLocal .int name (some (SignedMod.expression i j))).run state = .error .revert := by
    change TRun.declLocal .int (some (SignedMod.expression i j)) state = _
    simp only [TRun.declLocal,failed,bind,Except.bind]
  have native : (program i j name).run state = .error .revert := Prog.run_cons_error declaration
  have target := (compilation_revert_iff (whole b F i j name)
    (compilation_input_stack _ (input i j name represented capacity) tail) (by rfl)).mpr (.inl native)
  exact ⟨native,run_append_revert target⟩

end Solidity.Backend.Passes.SignedRemainderCapture

/-- info: 'Solidity.Backend.Passes.SignedRemainderCapture.selectable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCapture.selectable

/-- info: 'Solidity.Backend.Passes.SignedRemainderCapture.public_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCapture.public_selection

/-- info: 'Solidity.Backend.Passes.SignedRemainderCapture.whole_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCapture.whole_eq

/-- info: 'Solidity.Backend.Passes.SignedRemainderCapture.reader_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCapture.reader_public

/-- info: 'Solidity.Backend.Passes.SignedRemainderCapture.value_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCapture.value_nonzero

/-- info: 'Solidity.Backend.Passes.SignedRemainderCapture.physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCapture.physical

/-- info: 'Solidity.Backend.Passes.SignedRemainderCapture.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCapture.application

/-- info: 'Solidity.Backend.Passes.SignedRemainderCapture.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCapture.input

/-- info: 'Solidity.Backend.Passes.SignedRemainderCapture.value_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCapture.value_zero

/-- info: 'Solidity.Backend.Passes.SignedRemainderCapture.rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.Passes.SignedRemainderCapture.rejected
