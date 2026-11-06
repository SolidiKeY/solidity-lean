import Solidity.Backend.Passes.SignedWidthCapture

/-! The actual capture/edit/guard order. The old local is changed only after
capture; the fresh local remains the original value. Internal typed symbolic
execution only, not Source frontend or ABI adequacy. -/
namespace Solidity.Backend.Passes.CaptureMutation
open Backend.Scalar
variable {C : Contract} {Γ : Ctx}

def eight : Fin 32 := ⟨0, by decide⟩
def old : Val C (.val .int :: Γ) .int := .simple (.local .here)
def oldCode (b : Nat) (F : Evm.Frag (.val .int :: Γ)) :
    Evm.Memory.CompiledVal b F (old : Val C _ .int) := ⟨_,.core _ rfl⟩
def replacement : Val C (.val .int :: .val .int :: Γ) .int := .simple (.lit 128 rfl)
def selected (stale : Bool) : Val C (.val .int :: .val .int :: Γ) .int :=
  .simple (.local (if stale then .there .here else .here))
def selectedCode (b : Nat) (F : Evm.Frag (.val .int :: .val .int :: Γ)) (stale : Bool) :
    Evm.Memory.CompiledVal b F (selected stale : Val C _ .int) :=
  ⟨_,.core _ (by cases stale <;> rfl)⟩

def program (x : Var) (stale : Bool) :
    Prog C (.val .int :: Γ) (.val .int :: .val .int :: Γ) :=
  .cons (.declLocal .int x (some old))
    (.cons (.assignLocal (.there .here) replacement)
      (.cons (.require (SignedWidthGuard.condition eight (selected stale))) .nil))

def compiled (b : Nat) (F : Evm.Frag (.val .int :: Γ)) (x : Var) (stale : Bool) :
    Evm.Compiler.Compilation b F (program x stale : Prog C _ _) :=
  let FF := F.push (.val .int) .ok
  let guard := SignedWidthGuard.compiled eight (selected stale) (selectedCode b FF stale)
  .memory ⟨FF,
    ((oldCode b F).code ++ [.mstore (Evm.cell (b+(.val .int :: Γ).length))]) ++
      (([.push (.val (Evm.sword 128))] ++ [.mstore (Evm.cellOf b
        ((.there .here) : Idx (.val .int :: .val .int :: Γ) (.val .int)))]) ++
        ((guard.code ++ Evm.assertTop) ++ [])),
    .cons (.declare F x old _ (oldCode b F).cert)
      (.cons (.assign FF (.there .here) replacement _ (.core _ rfl))
        (.cons (.require FF _ _ guard.cert) (.nil FF)))⟩

def captured (state : State C Γ) :=
  (state.push (t := .val .int) (⟨127,rfl⟩ : PrimTy.int.Denote)).push
    (t := .val .int) (⟨127,rfl⟩ : PrimTy.int.Denote)
def edited (state : State C Γ) :=
  (captured state).setLocal (.there .here) (⟨128,rfl⟩ : PrimTy.int.Denote)

theorem source (state : State C Γ) (x : Var) (stale : Bool) :
    (program x stale).run (state.push (t := .val .int) (⟨127,rfl⟩ : PrimTy.int.Denote)) =
      if stale then .error .revert else .ok ⟨edited state,List.prefix_refl _⟩ := by
  have declaration : (Stmt.declLocal .int x (some old)).run
      (state.push (t := .val .int) (⟨127,rfl⟩ : PrimTy.int.Denote)) =
      .ok ⟨captured state,List.prefix_refl _⟩ := rfl
  have assignment : (Stmt.assignLocal (.there .here) replacement).run (captured state) =
      .ok ⟨edited state,List.prefix_refl _⟩ := rfl
  rw [program,Prog.run_cons_ok declaration,Prog.run_cons_ok assignment]
  cases stale
  · exact SignedWidthGuard.require_source eight (selected false) (edited state) ⟨127,rfl⟩ rfl
  · exact SignedWidthGuard.require_source eight (selected true) (edited state) ⟨128,rfl⟩ rfl

theorem input {b L frame : Nat} {F : Evm.Frag (.val .int :: Γ)}
    (state : State C Γ) {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (represented : Evm.Memory.StateRepr L b frame F
      (state.push (t := .val .int) (⟨127,rfl⟩ : PrimTy.int.Denote)) base machine)
    (capacity : b+(Γ.length+2) ≤ frame) (x : Var) (stale : Bool) :
    (compiled b F x stale).Input L frame base
      (state.push (t := .val .int) (⟨127,rfl⟩ : PrimTy.int.Denote)) machine := by
  refine ⟨represented,?_,Or.inl rfl⟩
  change b + max (max (Γ.length+1) (max (Γ.length+2) 0))
    (max (max (Γ.length+2) (max (Γ.length+2) 0))
      (max (max (Γ.length+2) (max (Γ.length+2) 0)) (Γ.length+2))) ≤ frame
  omega

/-- Capture's actual word and map are fixed before ALL saved tails. The
assignment prefix really executes before either guard; no failure machine
is invented for the stale branch. -/
theorem execution {b L frame : Nat} {F : Evm.Frag (.val .int :: Γ)}
    (state : State C Γ) {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (represented : Evm.Memory.StateRepr L b frame F
      (state.push (t := .val .int) (⟨127,rfl⟩ : PrimTy.int.Denote)) base machine)
    (capacity : b+(Γ.length+2) ≤ frame) (x : Var) :
    ∃ word, Evm.ReprV .int ⟨127,rfl⟩ word ∧ ∀ tail,
      let cm := Evm.Memory.writeMachine {machine with stack := tail}
        (Evm.cell (b+Γ.length+1)) word
      let em := Evm.Memory.writeMachine cm
        (Evm.cellOf b ((.there .here) : Idx (.val .int :: .val .int :: Γ) (.val .int)))
        (.val (Evm.sword 128))
      Evm.run ((oldCode (C := C) b F).code ++
        [.mstore (Evm.cell (b+Γ.length+1))]) {machine with stack := tail} = .ok cm 0 ∧
      Evm.run ([.push (.val (Evm.sword 128))] ++
        [.mstore (Evm.cellOf b ((.there .here) : Idx (.val .int :: .val .int :: Γ) (.val .int)))])
        cm = .ok em 0 ∧
      Evm.Memory.StateRepr L b frame (F.push (.val .int) .ok) (edited state) base em ∧
      (∀ stale, (SignedWidthGuard.requireStage eight (selected stale)
        (selectedCode (C := C) b (F.push (.val .int) .ok) stale)).Input L frame base (edited state) em) ∧
      (∀ stale, Evm.run (compiled (C := C) b F x stale).code {machine with stack := tail} =
        if stale then .revert else .ok em 0) := by
  obtain ⟨word,repr,tails⟩ := SignedWidthCapture.execution_shared eight x old (oldCode b F)
    represented ⟨127,rfl⟩ rfl (by simpa only [List.length_cons] using capacity)
  refine ⟨word,repr,?_⟩
  intro tail
  obtain ⟨_,captureRun,reached,_,_,_⟩ := tails tail
  have editRepr := reached.setVal (p := .int) (.there .here) ⟨128,rfl⟩ _
    (Evm.ReprV.int_word _)
  have editRun : Evm.run ([.push (.val (Evm.sword 128))] ++
      [.mstore (Evm.cellOf b ((.there .here) : Idx (.val .int :: .val .int :: Γ) (.val .int)))])
      (Evm.Memory.writeMachine {machine with stack := tail} (Evm.cell (b+Γ.length+1)) word) =
      .ok (Evm.Memory.writeMachine
        (Evm.Memory.writeMachine {machine with stack := tail} (Evm.cell (b+Γ.length+1)) word)
        (Evm.cellOf b ((.there .here) : Idx (.val .int :: .val .int :: Γ) (.val .int)))
        (.val (Evm.sword 128))) 0 := rfl
  refine ⟨captureRun,editRun,editRepr,?_,?_⟩
  · intro stale
    exact SignedWidthGuard.require_input eight (selected stale) _ editRepr (by
      simpa only [List.length_cons] using capacity)
  · intro stale
    change Evm.run ((_ ++ _) ++ ((_ ++ _) ++ _)) _ = _
    rw [Evm.run_append_ok captureRun]
    simp only [List.length_cons,Nat.add_assoc] at editRun ⊢
    rw [Evm.run_append_ok editRun]
    cases stale
    · exact SignedWidthGuard.require_target eight (selected false) _ editRepr ⟨127,rfl⟩ rfl tail
    · exact SignedWidthGuard.require_target eight (selected true) _ editRepr ⟨128,rfl⟩ rfl tail

end Solidity.Backend.Passes.CaptureMutation
/-- info: 'Solidity.Backend.Passes.CaptureMutation.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.CaptureMutation.source
/-- info: 'Solidity.Backend.Passes.CaptureMutation.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.CaptureMutation.input
/-- info: 'Solidity.Backend.Passes.CaptureMutation.execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.CaptureMutation.execution

namespace Solidity.Backend.Passes.CaptureMutation
variable {C : Contract} {Γ : Ctx}

/-- Complete original Inputs and full accepted output at the actual unchanged
map. Allocator preservation follows both actual local writes. -/
theorem mapped_success {b L frame : Nat} {F : Evm.Frag (.val .int :: Γ)}
    (state : State C Γ) {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (represented : Evm.Memory.StateRepr L b frame F
      (state.push (t := .val .int) (⟨127,rfl⟩ : PrimTy.int.Denote)) base machine)
    (capacity : b+(Γ.length+2) ≤ frame) (x : Var) :
    ∃ word, Evm.ReprV .int ⟨127,rfl⟩ word ∧ ∀ tail,
      let em := Evm.Memory.writeMachine
        (Evm.Memory.writeMachine {machine with stack := tail} (Evm.cell (b+Γ.length+1)) word)
        (Evm.cellOf b ((.there .here) : Idx (.val .int :: .val .int :: Γ) (.val .int)))
        (.val (Evm.sword 128))
      (∀ stale, (compiled b F x stale).Input L frame base
        (state.push (t := .val .int) (⟨127,rfl⟩ : PrimTy.int.Denote)) {machine with stack := tail}) ∧
      MappedOutput (compiled b F x false) L frame base
        (state.push (t := .val .int) (⟨127,rfl⟩ : PrimTy.int.Denote))
        {machine with stack := tail} (edited state) em base ∧
      (∀ stale, Evm.run (compiled (C := C) b F x stale).code {machine with stack := tail} =
        if stale then .revert else .ok em 0) := by
  obtain ⟨word,repr,tails⟩ := execution state represented capacity x
  refine ⟨word,repr,?_⟩
  intro tail
  obtain ⟨captureRun,editRun,reached,guardInput,target⟩ := tails tail
  refine ⟨fun stale => input state (represented.stack tail) capacity x stale,
    ⟨reached,Evm.Memory.BaseExtends.refl base,?_⟩,target⟩
  intro cursor hb allocator space
  have first := allocator.localWrite (b+Γ.length+1) (by omega) (by omega) word
  exact first.localWrite _ (Nat.lt_of_lt_of_le hb (Evm.le_lvl b (.there .here)))
    (by simpa only [Evm.cellOf] using
      Nat.lt_of_lt_of_le (Evm.lvl_lt b
        ((.there .here) : Idx (.val .int :: .val .int :: Γ) (.val .int))) (by
          simpa only [List.length_cons] using capacity))
    (.val (Evm.sword 128))

/-- The actual initial-to-terminal programs discriminate ordinary revert
from success. Neither panic nor divergence is introduced by the stale read. -/
theorem terminal {b L frame : Nat} {F : Evm.Frag (.val .int :: Γ)}
    (state : State C Γ) {base : Nat → Fin Evm.W} {machine : Evm.Machine}
    (represented : Evm.Memory.StateRepr L b frame F
      (state.push (t := .val .int) (⟨127,rfl⟩ : PrimTy.int.Denote)) base machine)
    (capacity : b+(Γ.length+2) ≤ frame) (x : Var) (stale : Bool) (tail : List Evm.Word) :
    (Evm.run (compiled (C := C) b F x stale).code {machine with stack := tail} = .revert ↔
      (program x stale).run
        (state.push (t := .val .int) (⟨127,rfl⟩ : PrimTy.int.Denote)) = .error .revert) ∧
    (program x stale).run
        (state.push (t := .val .int) (⟨127,rfl⟩ : PrimTy.int.Denote)) ≠ .error .panic ∧
    (program x stale).run
        (state.push (t := .val .int) (⟨127,rfl⟩ : PrimTy.int.Denote)) ≠ .error .diverge ∧
    Evm.run (compiled (C := C) b F x stale).code {machine with stack := tail} ≠ .fault := by
  obtain ⟨word,_,tails⟩ := execution state represented capacity x
  obtain ⟨_,_,_,_,target⟩ := tails tail
  rw [source,target stale]
  cases stale <;> simp only [Bool.false_eq_true,if_false,if_true,reduceCtorEq,iff_self]
  all_goals exact ⟨trivial,(by intro h; cases h),(by intro h; cases h),(by intro h; cases h)⟩

end Solidity.Backend.Passes.CaptureMutation
/-- info: 'Solidity.Backend.Passes.CaptureMutation.mapped_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.CaptureMutation.mapped_success
/-- info: 'Solidity.Backend.Passes.CaptureMutation.terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.CaptureMutation.terminal
