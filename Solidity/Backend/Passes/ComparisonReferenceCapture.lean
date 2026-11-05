import Solidity.Backend.PrimitivePackets.Comparisons.Agreement
import Solidity.Backend.Passes.ConditionalReferenceCapture

/-! A publicly selected runtime comparison chooses an actual reference and
captures it. Scalar arithmetic stays in its producer; source comparison
agreement alone does not assert Source reference-statement lowering. -/
namespace Solidity.Backend.Passes.ComparisonReferenceCapture
open Evm Evm.Memory Evm.Compiler
open Backend.PrimitivePackets
variable {C : Contract} {Γ : Ctx} {R : RefTy}

def program (order : Comparisons.Order) (signed : Bool)
    (i j : Idx Γ (.val (Comparisons.prim signed))) (name : Var)
    (dst yes no : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) :
    Prog C Γ (.mem R :: Γ) :=
  ConditionalReferenceCapture.program name (Comparisons.value order signed i j) dst yes no hm

def code (b : Nat) (F : Frag Γ) (order : Comparisons.Order) (signed : Bool)
    (i j : Idx Γ (.val (Comparisons.prim signed))) (name : Var)
    (dst yes no : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) :
    CompiledProg b F (program (C := C) order signed i j name dst yes no hm) :=
  ConditionalReferenceCapture.compiledProgram name (Comparisons.value order signed i j)
    (Comparisons.selected b F order signed i j) dst yes no hm

def whole (b : Nat) (F : Frag Γ) (order : Comparisons.Order) (signed : Bool)
    (i j : Idx Γ (.val (Comparisons.prim signed))) (name : Var)
    (dst yes no : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) :
    Compilation b F (program (C := C) order signed i j name dst yes no hm) :=
  .memory (code b F order signed i j name dst yes no hm)

theorem public_selection (b : Nat) (F : Frag Γ) (order : Comparisons.Order) (signed : Bool)
    (i j : Idx Γ (.val (Comparisons.prim signed))) (name : Var)
    (dst yes no : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) :
    compileProg (C := C) b F (program order signed i j name dst yes no hm) =
      some (code b F order signed i j name dst yes no hm) := by
  cases R with
  | array elem =>
      cases elem <;>
        dsimp only [program,ConditionalReferenceCapture.program,ConditionalReferenceCapture.arm,
          Memory.compileProg,Memory.compileStmt]
      all_goals rw [Comparisons.public_selection]; rfl
  | struct n =>
      dsimp only [program,ConditionalReferenceCapture.program,ConditionalReferenceCapture.arm,
        Memory.compileProg,Memory.compileStmt]
      rw [Comparisons.public_selection]
      rfl
  | fixed elem n =>
      dsimp only [program,ConditionalReferenceCapture.program,ConditionalReferenceCapture.arm,
        Memory.compileProg,Memory.compileStmt]
      rw [Comparisons.public_selection]
      rfl
  | mapping key elem =>
      dsimp only [program,ConditionalReferenceCapture.program,ConditionalReferenceCapture.arm,
        Memory.compileProg,Memory.compileStmt]
      rw [Comparisons.public_selection]
      rfl

theorem whole_eq (b : Nat) (F : Frag Γ) (order : Comparisons.Order) (signed : Bool)
    (i j : Idx Γ (.val (Comparisons.prim signed))) (name : Var)
    (dst yes no : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) :
    whole (C := C) b F order signed i j name dst yes no hm =
      ConditionalReferenceCapture.compiled name (Comparisons.value order signed i j)
        (Comparisons.selected b F order signed i j) dst yes no hm := rfl

/-- The reached alias application needs the original frame plus exactly one
fresh local; it does not need an allocator or a guessed final relation. -/
theorem input {b L frame : Nat} {F : Frag Γ} (order : Comparisons.Order) (signed : Bool)
    (i j : Idx Γ (.val (Comparisons.prim signed))) (name : Var)
    (dst yes no : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) :
    (whole (C := C) b F order signed i j name dst yes no hm).Input L frame base state machine := by
  refine ⟨represented,?_,Or.inl ?_⟩
  · change b + frameNeedProg (program order signed i j name dst yes no hm) ≤ frame
    change b + max
      (max Γ.length (max Γ.length (max
        (max (max Γ.length (max Γ.length 0)) Γ.length)
        (max (max Γ.length (max Γ.length 0)) Γ.length))))
      (max (max Γ.length (max (Γ.length+1) 0)) (Γ.length+1)) ≤ frame
    omega
  · exact allocationCostProg_zero _ rfl state

/-- Actual public selection, scalar evaluation and typed pointer representation
supply the real references, full selected map and all-tail capture execution. -/
theorem execution {b L frame : Nat} {F : Frag Γ} (order : Comparisons.Order) (signed : Bool)
    (i j : Idx Γ (.val (Comparisons.prim signed))) (name : Var)
    (dst yes no : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame) (x y : Int)
    (hx : (Comparisons.ty signed).lo ≤ x ∧ x ≤ (Comparisons.ty signed).hi)
    (hy : (Comparisons.ty signed).lo ≤ y ∧ y ≤ (Comparisons.ty signed).hi)
    (left : TEnv.get i state.env = Lowering.V07.integerValue (Comparisons.ty signed) x hx)
    (right : TEnv.get j state.env = Lowering.V07.integerValue (Comparisons.ty signed) y hy) :
    ∃ yr nr : HRef state.H R,
      TEnv.get yes state.env = some yr ∧ TEnv.get no state.env = some nr ∧
      (program order signed i j name dst yes no hm).run state =
        .ok ⟨(state.setLocal dst (some (if Comparisons.result order x y then yr else nr))).push
          (t := .mem R) (some (if Comparisons.result order x y then yr else nr)),List.prefix_refl _⟩ ∧
      ∃ (canonical : Machine) (outBase : Nat → Fin W), canonical.stack = [] ∧ ∀ tail,
        (whole (C := C) b F order signed i j name dst yes no hm).Input L frame base state {machine with stack := tail} ∧
        run (whole (C := C) b F order signed i j name dst yes no hm).code {machine with stack := tail} =
          .ok {canonical with stack := tail} 0 ∧
        MappedOutput (whole (C := C) b F order signed i j name dst yes no hm) L frame base state
          {machine with stack := tail}
          ((state.setLocal dst (some (if Comparisons.result order x y then yr else nr))).push
            (t := .mem R) (some (if Comparisons.result order x y then yr else nr)))
          {canonical with stack := tail} outBase ∧
        outBase yr.id = base yr.id ∧ outBase nr.id = base nr.id ∧
        canonical.mem (cell (b+Γ.length)) =
          .val (base (if Comparisons.result order x y then yr else nr).id) := by
  have admitted := input order signed i j name dst yes no hm represented capacity
  rw [whole_eq] at admitted ⊢
  exact ConditionalReferenceCapture.execution name (Comparisons.value order signed i j)
    (Comparisons.selected b F order signed i j) dst yes no hm admitted _
    (Comparisons.intrinsic_run state order signed i j x y hx hy left right)

/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCapture.public_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_selection
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCapture.whole_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms whole_eq
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCapture.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms input
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCapture.execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms execution
end Solidity.Backend.Passes.ComparisonReferenceCapture
