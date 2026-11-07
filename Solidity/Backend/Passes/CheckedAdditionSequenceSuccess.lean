import Solidity.Backend.Passes.CheckedAdditionReachedOverflow

/-! Successful counterpart for the same public two-capture program. Both
actual boundary maps and machines precede all saved tails. Arithmetic remains
with the published CheckedAdd producer; Source declaration lowering is open. -/
namespace Solidity.Backend.Passes.CheckedAdditionSequenceSuccess
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open Solidity.Backend.PrimitivePackets
open CheckedAdditionReachedOverflow (program selected public_selection code_sequence)
variable {C : Contract} {Γ : Ctx}

theorem intrinsic_success (first second : Var) (a b : Idx Γ (.val .uint))
    (state : State C Γ) (v w : PrimTy.uint.Denote)
    (firstValue : (CheckedAdd.value a b).evalT state = .ok v)
    (secondValue : (CheckedAdd.value .here (.there a)).evalT
      (state.push (t:=.val .uint) v) = .ok w) :
    (program first second a b).run state =
      .ok ⟨(state.push (t:=.val .uint) v).push (t:=.val .uint) w,List.prefix_refl _⟩ := by
  have firstRun := CheckedAdditionCapture.intrinsic_success first a b state v firstValue
  have secondRun := CheckedAdditionCapture.intrinsic_success second .here (.there a) _ w secondValue
  rw [program,DeferredSource.join_run]
  simp only [TRun.seq,firstRun,secondRun,Except.map]

/-- The second representation and Input come from the first actual mapped
output. Both selected maps remain visible; no equality is inferred from Rep. -/
theorem success {offset L frame : Nat} {F : Frag Γ} (first second : Var)
    (a b : Idx Γ (.val .uint)) (state : State C Γ)
    {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L offset frame F state base machine)
    (capacity : offset+(Γ.length+2) ≤ frame)
    (x y : Int) (hx : CheckedAdd.U.lo ≤ x ∧ x ≤ CheckedAdd.U.hi)
    (hy : CheckedAdd.U.lo ≤ y ∧ y ≤ CheckedAdd.U.hi)
    (ha : TEnv.get a state.env = integerValue CheckedAdd.U x hx)
    (hb : TEnv.get b state.env = integerValue CheckedAdd.U y hy)
    (fits : CheckedAdd.U.lo ≤ x+y ∧ x+y ≤ CheckedAdd.U.hi)
    (fitsAgain : CheckedAdd.U.lo ≤ (x+y)+x ∧ (x+y)+x ≤ CheckedAdd.U.hi) :
    let left := Compilation.memory (CheckedAdditionCapture.selected offset F first a b)
    let right := Compilation.memory (CheckedAdditionCapture.selected offset
      (F.push (.val .uint) .ok) second .here (.there a))
    let next := state.push (t:=.val .uint) (integerValue CheckedAdd.U (x+y) fits)
    let last := next.push (t:=.val .uint) (integerValue CheckedAdd.U ((x+y)+x) fitsAgain)
    Memory.compileProg offset F (program (C:=C) first second a b) =
      some (selected (C:=C) offset F first second a b) ∧
    (program first second a b).run state = .ok ⟨last,List.prefix_refl _⟩ ∧
    ∃ (middle final : Machine) (middleBase finalBase : Nat → Fin W),
      middle.stack = [] ∧ final.stack = [] ∧ ∀ tail,
      left.Input L frame base state {machine with stack := tail} ∧
      run left.code {machine with stack := tail} = .ok {middle with stack := tail} 0 ∧
      MappedOutput left L frame base state {machine with stack := tail}
        next {middle with stack := tail} middleBase ∧
      right.Input L frame middleBase next {middle with stack := tail} ∧
      run right.code {middle with stack := tail} = .ok {final with stack := tail} 0 ∧
      MappedOutput right L frame middleBase next {middle with stack := tail}
        last {final with stack := tail} finalBase ∧
      run (selected (C:=C) offset F first second a b).code {machine with stack := tail} =
        .ok {final with stack := tail} 0 := by
  dsimp only
  have firstValue := CheckedAdd.value_success state a b x y hx hy ha hb fits
  have secondValue := CheckedAdd.value_success
    (state.push (t:=.val .uint) (integerValue CheckedAdd.U (x+y) fits))
    .here (.there a) (x+y) x fits hx rfl ha fitsAgain
  have firstRun := CheckedAdditionCapture.intrinsic_success first a b state _ firstValue
  have secondRun := CheckedAdditionCapture.intrinsic_success second .here (.there a) _ _ secondValue
  have firstInput := CheckedAdditionCapture.input first a b represented (by omega)
  obtain ⟨middle,middleBase,firstEmpty,middleStack,firstTails⟩ :=
    compilation_success_shared_mapped (.memory (CheckedAdditionCapture.selected offset F first a b))
      firstInput (by rfl) firstRun
  have firstMapped := (firstTails []).2
  change MappedOutput _ L _ _ _ _ _ _ _ at firstMapped
  have secondInput := CheckedAdditionCapture.input second .here (.there a) firstMapped.1
    (by simpa only [List.length_cons] using capacity)
  obtain ⟨final,finalBase,secondEmpty,finalStack,secondTails⟩ :=
    compilation_success_shared_mapped (.memory (CheckedAdditionCapture.selected offset
      (F.push (.val .uint) .ok) second .here (.there a))) secondInput (by rfl) secondRun
  refine ⟨public_selection offset F first second a b,
    intrinsic_success first second a b state _ _ firstValue secondValue,
    middle,final,middleBase,finalBase,middleStack,finalStack,?_⟩
  intro tail
  obtain ⟨leftRun,leftMapped⟩ := firstTails tail
  obtain ⟨rightRun,rightMapped⟩ := secondTails tail
  change MappedOutput _ L _ _ _ _ _ _ _ at leftMapped rightMapped
  have reachedInput := CheckedAdditionCapture.input second .here (.there a) leftMapped.1
    (by simpa only [List.length_cons] using capacity)
  refine ⟨CheckedAdditionCapture.input first a b (represented.stack tail) (by omega),
    leftRun,leftMapped,reachedInput,rightRun,rightMapped,?_⟩
  simp only [Compilation.code] at leftRun rightRun
  rw [code_sequence,run_append_ok leftRun]
  exact rightRun

/-- With the first sum representable, the SAME selected program reverts
exactly when its reached second checked sum is out of range. -/
theorem guard_exact {offset L frame : Nat} {F : Frag Γ} (first second : Var)
    (a b : Idx Γ (.val .uint)) (state : State C Γ)
    {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L offset frame F state base machine)
    (capacity : offset+(Γ.length+2) ≤ frame)
    (x y : Int) (hx : CheckedAdd.U.lo ≤ x ∧ x ≤ CheckedAdd.U.hi)
    (hy : CheckedAdd.U.lo ≤ y ∧ y ≤ CheckedAdd.U.hi)
    (ha : TEnv.get a state.env = integerValue CheckedAdd.U x hx)
    (hb : TEnv.get b state.env = integerValue CheckedAdd.U y hy)
    (fits : CheckedAdd.U.lo ≤ x+y ∧ x+y ≤ CheckedAdd.U.hi) :
    ((program first second a b).run state = .error .revert ↔
      ¬ (CheckedAdd.U.lo ≤ (x+y)+x ∧ (x+y)+x ≤ CheckedAdd.U.hi)) ∧
    ∀ tail, (run (selected (C:=C) offset F first second a b).code
      {machine with stack := tail} = .revert ↔
      ¬ (CheckedAdd.U.lo ≤ (x+y)+x ∧ (x+y)+x ≤ CheckedAdd.U.hi)) := by
  by_cases h : CheckedAdd.U.lo ≤ (x+y)+x ∧ (x+y)+x ≤ CheckedAdd.U.hi
  · obtain ⟨_,sourceRun,middle,final,middleBase,finalBase,_,_,allTails⟩ :=
      success first second a b state represented capacity x y hx hy ha hb fits h
    constructor
    · constructor
      · intro failed
        rw [sourceRun] at failed
        cases failed
      · intro impossible
        exact False.elim (impossible h)
    · intro tail
      rcases allTails tail with ⟨_,_,_,_,_,_,targetRun⟩
      constructor
      · intro failed
        rw [failed] at targetRun
        cases targetRun
      · intro impossible
        exact False.elim (impossible h)
  · obtain ⟨_,_,_,sourceRun,middle,middleBase,_,allTails⟩ :=
      CheckedAdditionReachedOverflow.reached first second a b state represented capacity
        x y hx hy ha hb fits h
    constructor
    · exact ⟨fun _ => h,fun _ => sourceRun⟩
    · intro tail
      rcases allTails tail with ⟨_,_,_,_,_,targetRun⟩
      exact ⟨fun _ => h,fun _ => targetRun⟩

#print axioms guard_exact
#print axioms intrinsic_success
#print axioms success
end Solidity.Backend.Passes.CheckedAdditionSequenceSuccess
