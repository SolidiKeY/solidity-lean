import Solidity.Backend.Passes.MemoryScopeBoundary
import Solidity.Backend.Passes.AssignmentMultiplicationControls

namespace Solidity.Backend.Passes.MemoryScopeBoundary.Controls
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open AssignmentMultiplicationPass.Controls (C Γ F target bases machine i a after)

def bodyProgram (p : Roadmap.Pipeline) := assignReadPrefix (C := C) p i a
def body (p : Roadmap.Pipeline) := AssignmentMultiplicationPass.Controls.compiled p
def outerCode (p : Roadmap.Pipeline) := MemoryScopeBoundary.compiled (body p)
def prefixOut (p : Roadmap.Pipeline) : Solidity.Out C target.H (.val .uint :: .val .uint :: Γ) :=
  ⟨AssignmentSubtractionPass.reached p target .u8 i 255 1 (by decide) (by decide), List.prefix_refl _⟩
def post (p : Roadmap.Pipeline) : State C Γ := (prefixOut p).st.drop (bodyProgram p).ext

theorem prefix_source (p : Roadmap.Pipeline) : (bodyProgram p).run target = .ok (prefixOut p) :=
  assign_read_prefix_run p target i a _ _ rfl rfl

theorem scoped_source (p : Roadmap.Pipeline) :
    (program (bodyProgram p)).run target = .ok (⟨post p, List.prefix_refl _⟩ : Solidity.Out C target.H Γ) :=
  source_success (prefix_source p)

theorem dropped_context (p : Roadmap.Pipeline) :
    post p = target.setLocal i (integerValue .u8 255 (by decide)) := by
  cases p <;> rfl

theorem scoped_accepted (p : Roadmap.Pipeline) :
    Memory.compileProg 1 F (program (bodyProgram p)) = some (outerCode p) := by
  cases p <;> rfl

def suffix : Prog C Γ (.val .uint :: Γ) :=
  .cons (.declLocal .uint (.user "reused") (some (.simple (.lit 42 (by decide))))) .nil

def right (p : Roadmap.Pipeline) : CompiledProg 1 (outerCode p).frag suffix :=
  (Memory.compileProg 1 (outerCode p).frag suffix).get (by cases p <;> decide +kernel)

theorem suffix_source (p : Roadmap.Pipeline) : suffix.run (post p) =
    .ok (⟨(post p).push (t := .val .uint) (integerValue .u256 42 (by decide)), List.prefix_refl _⟩ :
      Solidity.Out C (post p).H (.val .uint :: Γ)) := rfl

theorem suffix_run (p : Roadmap.Pipeline) (m : Machine) (tail : List Word) :
    run (right p).code {m with stack := tail} =
      .ok (writeMachine {m with stack := tail} (cell 4) w[42]) 0 := by
  cases p <;> rfl

theorem reached (p : Roadmap.Pipeline) :
    ∃ selected : Nat → Fin W, ∀ tail,
      MappedOutput (.memory (outerCode p)) 1 64 bases target {machine with stack := tail}
        (post p) {after p with stack := tail} selected ∧
      (Compilation.memory (right p)).Input 1 64 selected (post p) {after p with stack := tail} ∧
      run ((outerCode p).code ++ (right p).code) {machine with stack := tail} =
        .ok (writeMachine {after p with stack := tail} (cell 4) w[42]) 0 := by
  obtain ⟨canonical,selected,empty,runs⟩ := shared (body p)
    (AssignmentMultiplicationPass.Controls.input p) (by cases p <;> rfl) (prefix_source p)
  have ce : {canonical with stack := []} = canonical := by cases canonical; cases empty; rfl
  have same : canonical = after p := by
    have h := (Evm.Out.ok.inj ((runs []).1.symm.trans
      (AssignmentMultiplicationPass.Controls.prefix_run p))).1
    exact ce.symm.trans h
  subst canonical
  refine ⟨selected,?_⟩
  intro tail
  have out := (runs tail).2.2
  refine ⟨out, ⟨out.1, ?_, ?_⟩, ?_⟩
  · cases p <;> decide +kernel
  · exact .inl (allocationCostProg_zero suffix rfl (post p))
  · exact (run_append_ok (c₂ := (right p).code) (runs tail).2.1).trans (suffix_run p (after p) tail)

theorem joined_source (p : Roadmap.Pipeline) :
    ((program (bodyProgram p)).join suffix).run target =
      .ok (⟨(post p).push (t := .val .uint) (integerValue .u256 42 (by decide)), List.prefix_refl _⟩ :
        Solidity.Out C target.H (.val .uint :: Γ)) := by
  rw [DeferredSource.join_run]
  simp only [TRun.seq, scoped_source, suffix_source, Except.map]

theorem completed (p : Roadmap.Pipeline) :
    ∃ (selected next : Nat → Fin W), ∀ tail,
      MappedOutput (.memory (outerCode p)) 1 64 bases target {machine with stack := tail}
        (post p) {after p with stack := tail} selected ∧
      (Compilation.memory (right p)).Input 1 64 selected (post p) {after p with stack := tail} ∧
      MappedOutput (.memory (right p)) 1 64 selected (post p) {after p with stack := tail}
        ((post p).push (t := .val .uint) (integerValue .u256 42 (by decide)))
        (writeMachine {after p with stack := tail} (cell 4) w[42]) next ∧
      run ((outerCode p).code ++ (right p).code) {machine with stack := tail} =
        .ok (writeMachine {after p with stack := tail} (cell 4) w[42]) 0 := by
  obtain ⟨selected,first⟩ := reached p
  obtain ⟨canonical,next,run,empty,second⟩ := compilation_success_shared_mapped (.memory (right p))
    (first []).2.1 rfl (suffix_source p)
  have same : canonical = writeMachine {after p with stack := []} (cell 4) w[42] :=
    (Evm.Out.ok.inj (run.symm.trans (suffix_run p (after p) []))).1
  subst canonical
  refine ⟨selected,next,?_⟩
  intro tail
  have represented := (second tail).2
  rw [(right p).cert.pushes_zero, Nat.add_zero] at represented
  exact ⟨(first tail).1,(first tail).2.1,represented,(first tail).2.2⟩

def cells : List Nat := [0,1,2,3,4,5,6,16,63,128,129,130]
theorem complete_observations (p : Roadmap.Pipeline) (tail : List Word) :
    (cells.map (writeMachine {after p with stack := w[77] :: tail} (cell 4) w[42]).mem,
      (writeMachine {after p with stack := w[77] :: tail} (cell 4) w[42]).stack) =
      ([w[130],w[128],w[255],w[255],w[42],w[255],w[0],w[20],w[99],w[1],w[0],w[0]],
        w[77] :: tail) := by
  apply Prod.ext
  · change cells.map (writeMachine (after p) (cell 4) w[42]).mem =
      [w[130],w[128],w[255],w[255],w[42],w[255],w[0],w[20],w[99],w[1],w[0],w[0]]
    cases p <;> unfold cells AssignmentMultiplicationPass.Controls.after <;> decide +kernel
  · rfl

def wrongSuffix : Prog C (.val .uint :: .val .uint :: Γ) (.val .uint :: .val .uint :: .val .uint :: Γ) :=
  .cons (.declLocal .uint (.user "wrong_context") (some (.simple (.lit 42 (by decide))))) .nil
def wrong (p : Roadmap.Pipeline) : CompiledProg 1 (body p).frag wrongSuffix :=
  (Memory.compileProg 1 (body p).frag wrongSuffix).get (by cases p <;> decide +kernel)
theorem wrong_run (p : Roadmap.Pipeline) (m : Machine) (tail : List Word) :
    run (wrong p).code {m with stack := tail} =
      .ok (writeMachine {m with stack := tail} (cell 6) w[42]) 0 := by
  cases p <;> rfl

theorem scope_run (p : Roadmap.Pipeline) (tail : List Word) :
    run (outerCode p).code {machine with stack := tail} = .ok {after p with stack := tail} 0 := by
  have h := compilation_tail_exact (.memory (outerCode p))
    (MemoryScopeBoundary.input (body p) (AssignmentMultiplicationPass.Controls.input p))
    (by cases p <;> rfl) tail
  change run (outerCode p).code {machine with stack := tail} =
    replaceOutStack tail (run (outerCode p).code {machine with stack := []}) at h
  simp only [outerCode, MemoryScopeBoundary.code, body] at h ⊢
  rw [AssignmentMultiplicationPass.Controls.prefix_run] at h
  exact h

theorem wrong_joined (p : Roadmap.Pipeline) (tail : List Word) :
    run ((outerCode p).code ++ (wrong p).code) {machine with stack := tail} =
      .ok (writeMachine {after p with stack := tail} (cell 6) w[42]) 0 :=
  (run_append_ok (c₂ := (wrong p).code) (scope_run p tail)).trans (wrong_run p (after p) tail)

theorem wrong_context_cell (p : Roadmap.Pipeline) :
    (writeMachine (after p) (cell 6) w[42]).mem (cell 4) ≠
      (writeMachine (after p) (cell 4) w[42]).mem (cell 4) := by
  cases p <;> unfold AssignmentMultiplicationPass.Controls.after <;> decide +kernel

theorem old_private_word_not_cleared (p : Roadmap.Pipeline) :
    (after p).mem (cell 5) = w[255] := by
  cases p <;> unfold AssignmentMultiplicationPass.Controls.after <;> decide +kernel

def failProgram (p : Roadmap.Pipeline) : Prog C Γ (.val .uint :: .val .uint :: Γ) :=
  (bodyProgram p).join (.cons .revert .nil)
def failBody (p : Roadmap.Pipeline) : CompiledProg 1 F (failProgram p) :=
  (Memory.compileProg 1 F (failProgram p)).get (by cases p <;> decide +kernel)
def failOuter (p : Roadmap.Pipeline) := MemoryScopeBoundary.compiled (failBody p)

theorem reached_source_revert (p : Roadmap.Pipeline) :
    (program (failProgram p)).run target = .error .revert := by
  apply (source_error .revert).mpr
  cases p <;> rfl

theorem failing_code (p : Roadmap.Pipeline) :
    (failOuter p).code = (outerCode p).code ++ [.revert] := by
  cases p <;> rfl

theorem reached_target_revert (p : Roadmap.Pipeline) (tail : List Word) :
    run (failOuter p).code {machine with stack := tail} = .revert := by
  rw [failing_code]
  exact (run_append_ok (c₂ := [.revert]) (scope_run p tail)).trans rfl

end Solidity.Backend.Passes.MemoryScopeBoundary.Controls
