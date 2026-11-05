import Solidity.Backend.Passes.CheckedAdditionCapture
import Solidity.Backend.Passes.Sequence

/-! A successful checked-add capture followed by a genuinely reached second
checked-add overflow. This is intrinsic/memory-compiler terminal transport;
Source declaration lowering and public failure/session adequacy remain open. -/
namespace Solidity.Backend.Passes.CheckedAdditionReachedOverflow
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open Solidity.Backend.PrimitivePackets
variable {C : Contract} {Γ : Ctx}

def program (first second : Var) (a b : Idx Γ (.val .uint)) :
    Prog C Γ (.val .uint :: .val .uint :: Γ) :=
  (CheckedAdditionCapture.program first a b).join
    (CheckedAdditionCapture.program second .here (.there a))

def selected (offset : Nat) (F : Frag Γ) (first second : Var)
    (a b : Idx Γ (.val .uint)) : CompiledProg offset F (program (C:=C) first second a b) :=
  ⟨(F.push (.val .uint) .ok).push (.val .uint) .ok,
    ((CheckedAdd.selected (C:=C) offset F a b).code ++ [.mstore (cell (offset+Γ.length))]) ++
      (((CheckedAdd.selected (C:=C) offset (F.push (.val .uint) .ok) .here (.there a)).code ++
        [.mstore (cell (offset+(Γ.length+1)))]) ++ []),
    .cons (.declare F first (CheckedAdd.value a b) _ (CheckedAdd.selected offset F a b).cert)
      (.cons (.declare (F.push (.val .uint) .ok) second (CheckedAdd.value .here (.there a)) _
        (CheckedAdd.selected offset (F.push (.val .uint) .ok) .here (.there a)).cert)
        (.nil _))⟩
theorem public_selection (offset : Nat) (F : Frag Γ) (first second : Var)
    (a b : Idx Γ (.val .uint)) :
    Memory.compileProg offset F (program (C:=C) first second a b) =
      some (selected (C:=C) offset F first second a b) := by
  rfl

theorem code_sequence (offset : Nat) (F : Frag Γ) (first second : Var)
    (a b : Idx Γ (.val .uint)) :
    (selected (C:=C) offset F first second a b).code =
      (CheckedAdditionCapture.selected (C:=C) offset F first a b).code ++
      (CheckedAdditionCapture.selected (C:=C) offset (F.push (.val .uint) .ok)
        second .here (.there a)).code := by
  simp only [selected,CheckedAdditionCapture.selected,List.append_nil,List.length_cons]

/-- The successful prefix chooses its actual machine and map before all tails.
The second Input is derived from that full mapped output, not postulated. -/
theorem reached {offset L frame : Nat} {F : Frag Γ} (first second : Var)
    (a b : Idx Γ (.val .uint)) (state : State C Γ)
    {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L offset frame F state base machine)
    (capacity : offset+(Γ.length+2) ≤ frame)
    (x y : Int) (hx : CheckedAdd.U.lo ≤ x ∧ x ≤ CheckedAdd.U.hi)
    (hy : CheckedAdd.U.lo ≤ y ∧ y ≤ CheckedAdd.U.hi)
    (ha : TEnv.get a state.env = integerValue CheckedAdd.U x hx)
    (hb : TEnv.get b state.env = integerValue CheckedAdd.U y hy)
    (fits : CheckedAdd.U.lo ≤ x+y ∧ x+y ≤ CheckedAdd.U.hi)
    (outside : ¬ (CheckedAdd.U.lo ≤ (x+y)+x ∧ (x+y)+x ≤ CheckedAdd.U.hi)) :
    let left := Compilation.memory (CheckedAdditionCapture.selected offset F first a b)
    let right := Compilation.memory (CheckedAdditionCapture.selected offset
      (F.push (.val .uint) .ok) second .here (.there a))
    let next := state.push (t:=.val .uint) (integerValue CheckedAdd.U (x+y) fits)
    Memory.compileProg offset F (program (C:=C) first second a b) =
      some (selected (C:=C) offset F first second a b) ∧
    (CheckedAdditionCapture.program first a b).run state =
      .ok ⟨next,List.prefix_refl _⟩ ∧
    (CheckedAdditionCapture.program second .here (.there a)).run next = .error .revert ∧
    (program first second a b).run state = .error .revert ∧
    ∃ (canonical : Machine) (outBase : Nat → Fin W), canonical.stack = [] ∧ ∀ tail,
      left.Input L frame base state {machine with stack := tail} ∧
      run left.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      MappedOutput left L frame base state {machine with stack := tail}
        next {canonical with stack := tail} outBase ∧
      right.Input L frame outBase next {canonical with stack := tail} ∧
      run right.code {canonical with stack := tail} = .revert ∧
      run (selected (C:=C) offset F first second a b).code {machine with stack := tail} = .revert := by
  dsimp only
  have leftInput := CheckedAdditionCapture.input first a b represented (by omega)
  have firstValue := CheckedAdd.value_success state a b x y hx hy ha hb fits
  have firstRun := CheckedAdditionCapture.intrinsic_success first a b state _ firstValue
  have secondValue := CheckedAdd.value_overflow
    (state.push (t:=.val .uint) (integerValue CheckedAdd.U (x+y) fits))
    .here (.there a) (x+y) x fits hx rfl ha outside
  have secondRun := CheckedAdditionCapture.intrinsic_revert second .here (.there a) _ secondValue
  have wholeRun : (program first second a b).run state = .error .revert := by
    rw [program,DeferredSource.join_run]
    simp only [TRun.seq,firstRun,secondRun,Except.map]
  obtain ⟨canonical,outBase,emptyRun,emptyStack,allTails⟩ :=
    compilation_success_shared_mapped (.memory (CheckedAdditionCapture.selected offset F first a b))
      leftInput (by rfl) firstRun
  refine ⟨public_selection offset F first second a b,firstRun,secondRun,wholeRun,
    canonical,outBase,emptyStack,?_⟩
  intro tail
  obtain ⟨prefixRun,prefixMapped⟩ := allTails tail
  change MappedOutput _ L _ _ _ _ _ _ _ at prefixMapped
  have suffixInput := CheckedAdditionCapture.input second (.here) (.there a)
    prefixMapped.1 (by simpa only [List.length_cons] using capacity)
  have suffixRun := (compilation_revert_iff
    (.memory (CheckedAdditionCapture.selected offset (F.push (.val .uint) .ok)
      second .here (.there a))) suffixInput (by rfl)).mpr (Or.inl secondRun)
  refine ⟨CheckedAdditionCapture.input first a b (represented.stack tail) (by omega),
    prefixRun,prefixMapped,suffixInput,suffixRun,?_⟩
  simp only [Compilation.code] at prefixRun suffixRun
  rw [code_sequence,run_append_ok prefixRun]
  exact suffixRun

#print axioms reached
end Solidity.Backend.Passes.CheckedAdditionReachedOverflow
