import Solidity.Backend.Passes.WidthApplication
import Solidity.Backend.Passes.CapturedValueStability

/-! Publicly selected low-bit cleanup, captured before clearing its operand.
The existing typed mask expression and published scalar cleanup law are used;
this is not a frontend cast-expansion or physical bytecode adequacy theorem. -/
namespace Solidity.Backend.Passes.UnsignedWidthCapture
open Evm Evm.Memory Evm.Compiler Backend.Scalar
variable {C : Contract} {Γ : Ctx}

def operand (i : Idx Γ (.val .uint)) : Val C Γ .uint := .simple (.local i)
def expression (w : Fin 32) (i : Idx Γ (.val .uint)) : Val C Γ .uint :=
  WidthApplication.expression w (operand i)
def selected (b : Nat) (F : Frag Γ) (w : Fin 32) (i : Idx Γ (.val .uint)) :
    CompiledVal b F (expression (C := C) w i) :=
  (Memory.compileVal b F (expression w i)).get (by rfl)
def update : Val C (.val .uint :: Γ) .uint := .simple (.lit 0 (by decide))
def zero : PrimTy.uint.Denote := ⟨0,by decide⟩
def program (w : Fin 32) (i : Idx Γ (.val .uint)) (name : Var) :=
  CapturedValueStability.program name (expression (C := C) w i) i update
def code (b : Nat) (F : Frag Γ) (w : Fin 32) (i : Idx Γ (.val .uint)) (name : Var) :
    CompiledProg b F (program (C := C) w i name) :=
  (Memory.compileProg b F (program w i name)).get (by rfl)
def whole (b : Nat) (F : Frag Γ) (w : Fin 32) (i : Idx Γ (.val .uint)) (name : Var) :=
  Compilation.memory (code (C := C) b F w i name)
def updateCode (b : Nat) (F : Frag Γ) : CompiledVal b (F.push (.val .uint) .ok) (update (C := C)) :=
  (Memory.compileVal b (F.push (.val .uint) .ok) update).get (by rfl)

theorem public_value (b : Nat) (F : Frag Γ) (w : Fin 32) (i : Idx Γ (.val .uint)) :
    Memory.compileVal (C := C) b F (expression w i) = some (selected (C := C) b F w i) := by rfl

theorem public_program (b : Nat) (F : Frag Γ) (w : Fin 32) (i : Idx Γ (.val .uint)) (name : Var) :
    Memory.compileProg (C := C) b F (program w i name) = some (code (C := C) b F w i name) := by rfl

theorem emitted (b : Nat) (F : Frag Γ) (w : Fin 32) (i : Idx Γ (.val .uint)) (name : Var) :
    (code (C := C) b F w i name).code =
      [.push (.val (wmod (toWord (WidthApplication.maskValue w).val))), .mload (cellOf b i), .and,
       .mstore (cell (b+Γ.length)), .push w[0], .mstore (cellOf b (.there (u := .val .uint) i))] := by rfl

theorem whole_eq (b : Nat) (F : Frag Γ) (w : Fin 32) (i : Idx Γ (.val .uint)) (name : Var) :
    whole (C := C) b F w i name = CapturedValueStability.compiled name (expression w i)
      (selected b F w i) i update (updateCode b F) := by rfl

def reader (b : Nat) (F : Frag Γ) (w : Fin 32) (i : Idx Γ (.val .uint)) (name : Var) :
    CompiledVal b (code (C := C) b F w i name).frag
      (.simple (.local .here) : Val C (.val .uint :: Γ) .uint) :=
  (Memory.compileVal b (code (C := C) b F w i name).frag (.simple (.local .here))).get (by rfl)
theorem reader_public (b : Nat) (F : Frag Γ) (w : Fin 32) (i : Idx Γ (.val .uint)) (name : Var) :
    Memory.compileVal b (code (C := C) b F w i name).frag
      (.simple (.local .here) : Val C (.val .uint :: Γ) .uint) = some (reader b F w i name) := by rfl
theorem reader_emitted (b : Nat) (F : Frag Γ) (w : Fin 32) (i : Idx Γ (.val .uint)) (name : Var) :
    (reader (C := C) b F w i name).code = [.mload (cell (b+Γ.length))] := by rfl

/-- The actual local read derives the cleanup result; no desired evaluation,
word, compiled value or execution is an input premise. -/
theorem native (w : Fin 32) (i : Idx Γ (.val .uint)) (state : State C Γ) :
    ∃ v, (expression w i).evalT state = .ok v ∧
      encodeValue .uint v = unsignedClean w (encodeValue .uint (TEnv.get i state.env)) :=
  WidthApplication.source w (operand i) state rfl

/-- Actual source result is correlated with the scalar owner's cleanup and
with original Input, stage executions, full mapped state and captured readback.
The two physical words are chosen before all arbitrary saved tails. -/
theorem application {b L frame : Nat} {F : Frag Γ} (w : Fin 32) (i : Idx Γ (.val .uint)) (name : Var)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) :
    ∃ v, (expression w i).evalT state = .ok v ∧
      encodeValue .uint v = unsignedClean w (encodeValue .uint (TEnv.get i state.env)) ∧
      (program w i name).run state =
        .ok ⟨(state.push (t := .val .uint) v).setLocal (.there i) zero,List.prefix_refl _⟩ ∧
      (∀ saved, Backend.Scalar.run (unsignedCode w) (encodeValue .uint (TEnv.get i state.env) :: saved) =
        some (encodeValue .uint v :: saved)) ∧
      Backend.decode (Backend.encode (unsignedCode w)) = some (unsignedCode w) ∧
      ∃ captured updated, ReprV .uint v captured ∧ ReprV .uint zero updated ∧ ∀ tail,
        let cm := writeMachine {machine with stack := tail} (cell (b+Γ.length)) captured
        let em := writeMachine cm (cellOf b (.there (u := .val .uint) i)) updated
        (whole (C := C) b F w i name).Input L frame base state {machine with stack := tail} ∧
        Evm.run ((selected (C := C) b F w i).code ++ [.mstore (cell (b+Γ.length))])
          {machine with stack := tail} = .ok cm 0 ∧
        Evm.run ((updateCode (C := C) b F).code ++ [.mstore (cellOf b (.there (u := .val .uint) i))]) cm = .ok em 0 ∧
        MappedOutput (whole (C := C) b F w i name) L frame base state {machine with stack := tail}
          ((state.push (t := .val .uint) v).setLocal (.there i) zero) em base ∧
        Evm.run (whole (C := C) b F w i name).code {machine with stack := tail} = .ok em 0 ∧
        Evm.run [.mload (cell (b+Γ.length))] em = .ok (em.push captured) 0 := by
  obtain ⟨v,evaluated,encoded⟩ := native w i state
  refine ⟨v,evaluated,encoded,?_,?_,WidthApplication.bytes w,?_⟩
  · exact CapturedValueStability.source name (expression w i) i update state v zero evaluated rfl
  · intro saved
    rw [encoded]
    exact unsigned_correct w _ saved
  · rw [whole_eq]
    exact CapturedValueStability.execution name (expression w i) (selected b F w i) i update
      (updateCode b F) represented capacity v zero evaluated rfl

/-- Out-of-width inputs are successfully cleaned, not rejected. -/
theorem never_reverts {b L frame : Nat} {F : Frag Γ} (w : Fin 32) (i : Idx Γ (.val .uint)) (name : Var)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) (tail : List Evm.Word) :
    Evm.run (whole (C := C) b F w i name).code {machine with stack := tail} ≠ .revert := by
  obtain ⟨v,_,_,_,_,_,captured,updated,_,_,runs⟩ := application w i name represented capacity
  rw [(runs tail).2.2.2.2.1]
  intro bad
  cases bad

/-- info: 'Solidity.Backend.Passes.UnsignedWidthCapture.reader_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reader_public
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCapture.reader_emitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reader_emitted
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCapture.public_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_value
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCapture.public_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_program
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCapture.emitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms emitted
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCapture.whole_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms whole_eq
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCapture.native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms native
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCapture.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms application
/-- info: 'Solidity.Backend.Passes.UnsignedWidthCapture.never_reverts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms never_reverts
end Solidity.Backend.Passes.UnsignedWidthCapture
