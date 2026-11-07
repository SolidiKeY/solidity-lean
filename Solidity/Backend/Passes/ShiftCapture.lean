import Solidity.Backend.PrimitivePackets.Shifts.General
import Solidity.Backend.Passes.ValueReflection
import Solidity.Backend.Passes.CapturedValueStability

/-! Public shift selection followed by capture and old-count mutation.
The producer owns the arithmetic and source expression semantics; this adapter
reflects the actual selected run and transports its typed state through capture. -/
namespace Solidity.Backend.Passes.ShiftCapture
open Evm Evm.Memory Evm.Compiler
open Backend.PrimitivePackets.Shifts
variable {C : Contract} {Γ : Ctx}

def update : Val C (.val .uint :: Γ) .uint := .simple (.lit 0 (by decide))
def zero : PrimTy.uint.Denote := ⟨0,by decide⟩
def program (left : Bool) (i j : Idx Γ (.val .uint)) (name : Var) :
    Prog C Γ (.val .uint :: Γ) :=
  CapturedValueStability.program name (General.target left i j) j update

def code (b : Nat) (left : Bool) (i j : Idx Γ (.val .uint)) (name : Var) :
    CompiledProg b (Frag.init Γ) (program (C := C) left i j name) :=
  (compileProg b (Frag.init Γ) (program left i j name)).get (by cases left <;> rfl)
def whole (b : Nat) (left : Bool) (i j : Idx Γ (.val .uint)) (name : Var) :
    Compilation b (Frag.init Γ) (program (C := C) left i j name) :=
  .memory (code b left i j name)
def updateCode (b : Nat) :
    CompiledVal b ((Frag.init Γ).push (.val .uint) .ok) (update (C := C)) :=
  (compileVal b ((Frag.init Γ).push (.val .uint) .ok) update).get (by rfl)

theorem public_selection (b : Nat) (left : Bool) (i j : Idx Γ (.val .uint)) (name : Var) :
    compileProg (C := C) b (Frag.init Γ) (program left i j name) =
      some (code b left i j name) := (Option.some_get _).symm

theorem emitted (b : Nat) (left : Bool) (i j : Idx Γ (.val .uint)) (name : Var) :
    (code (C := C) b left i j name).code =
      [.mload (cellOf b i),.mload (cellOf b j),if left then .shl else .shr,
       .mstore (cell (b+Γ.length)),.push w[0],.mstore (cellOf b (.there (u := .val .uint) j))] := by
  cases left <;> rfl

theorem whole_eq (b : Nat) (left : Bool) (i j : Idx Γ (.val .uint)) (name : Var) :
    whole (C := C) b left i j name =
      CapturedValueStability.compiled name (General.target left i j)
        (General.selected b left i j) j update (updateCode b) := by
  cases left <;> rfl

def reader (b : Nat) (left : Bool) (i j : Idx Γ (.val .uint)) (name : Var) :
    CompiledVal b (code (C := C) b left i j name).frag
      (.simple (.local .here) : Val C (.val .uint :: Γ) .uint) :=
  (compileVal b (code (C := C) b left i j name).frag (.simple (.local .here))).get (by cases left <;> rfl)
theorem reader_public (b : Nat) (left : Bool) (i j : Idx Γ (.val .uint)) (name : Var) :
    compileVal b (code (C := C) b left i j name).frag
      (.simple (.local .here) : Val C (.val .uint :: Γ) .uint) = some (reader b left i j name) :=
  (Option.some_get _).symm
theorem reader_emitted (b : Nat) (left : Bool) (i j : Idx Γ (.val .uint)) (name : Var) :
    (reader (C := C) b left i j name).code = [.mload (cell (b+Γ.length))] := by
  cases left <;> rfl

/-- Actual runtime cells and full typed input derive an intrinsic evaluation.
No desired value evaluation or selected-code execution is an input premise. -/
theorem native {b L frame : Nat} (left : Bool) (i j : Idx Γ (.val .uint))
    (x k : Fin W) {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame (Frag.init Γ) state base machine)
    (value : machine.mem (cellOf b i) = .val x)
    (amount : machine.mem (cellOf b j) = .val k) :
    ∃ v, (General.target (C := C) left i j).evalT state = .ok v ∧
      ReprV .uint v (.val (resultWord left x k)) :=
  ValueReflection.success (General.selected b left i j) _ represented
    (General.runtime_execution b left i j x k machine value amount)

/-- Full actual captured output and readback, sharing words before all tails. -/
theorem physical {b L frame : Nat} (left : Bool) (i j : Idx Γ (.val .uint)) (name : Var)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) (v : PrimTy.uint.Denote)
    (evaluated : (General.target (C := C) left i j).evalT state = .ok v) :
    ∃ captured updated, ReprV .uint v captured ∧ ReprV .uint zero updated ∧ ∀ tail,
      let cm := writeMachine {machine with stack := tail} (cell (b+Γ.length)) captured
      let em := writeMachine cm (cellOf b (.there (u := .val .uint) j)) updated
      (whole (C := C) b left i j name).Input L frame base state {machine with stack := tail} ∧
      run ((General.selected (C := C) b left i j).code ++ [.mstore (cell (b+Γ.length))])
        {machine with stack := tail} = .ok cm 0 ∧
      run ((updateCode (C := C) (Γ := Γ) b).code ++ [.mstore (cellOf b (.there (u := .val .uint) j))]) cm = .ok em 0 ∧
      MappedOutput (whole (C := C) b left i j name) L frame base state {machine with stack := tail}
        ((state.push (t := .val .uint) v).setLocal (.there j) zero) em base ∧
      run (whole (C := C) b left i j name).code {machine with stack := tail} = .ok em 0 ∧
      run [.mload (cell (b+Γ.length))] em = .ok (em.push captured) 0 := by
  rw [whole_eq]
  exact CapturedValueStability.execution name (General.target left i j)
    (General.selected b left i j) j update (updateCode b) represented capacity v zero evaluated rfl

theorem application {b L frame : Nat} (left : Bool) (i j : Idx Γ (.val .uint)) (name : Var)
    (x k : Fin W) {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b+(Γ.length+1) ≤ frame)
    (value : machine.mem (cellOf b i) = .val x)
    (amount : machine.mem (cellOf b j) = .val k) :
    let v := (native left i j x k represented value amount).choose
    (General.target (C := C) left i j).evalT state = .ok v ∧
      ReprV .uint v (.val (resultWord left x k)) ∧
      (program left i j name).run state =
        .ok ⟨(state.push (t := .val .uint) v).setLocal (.there j) zero,List.prefix_refl _⟩ ∧
      type_of% (physical left i j name represented capacity v
        ((native left i j x k represented value amount).choose_spec.1)) := by
  let evidence := native left i j x k represented value amount
  let v := evidence.choose
  have evaluated := evidence.choose_spec.1
  exact ⟨evaluated,evidence.choose_spec.2,
    CapturedValueStability.source name (General.target left i j) j update state v zero evaluated rfl,
    physical left i j name represented capacity v evaluated⟩

/-- info: 'Solidity.Backend.Passes.ShiftCapture.reader_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reader_public
/-- info: 'Solidity.Backend.Passes.ShiftCapture.reader_emitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reader_emitted
/-- info: 'Solidity.Backend.Passes.ShiftCapture.public_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_selection
/-- info: 'Solidity.Backend.Passes.ShiftCapture.emitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms emitted
/-- info: 'Solidity.Backend.Passes.ShiftCapture.whole_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms whole_eq
/-- info: 'Solidity.Backend.Passes.ShiftCapture.native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms native
/-- info: 'Solidity.Backend.Passes.ShiftCapture.physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physical
/-- info: 'Solidity.Backend.Passes.ShiftCapture.application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms application
end Solidity.Backend.Passes.ShiftCapture
