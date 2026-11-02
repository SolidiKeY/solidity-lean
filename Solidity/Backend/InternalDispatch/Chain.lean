import Solidity.Backend.InternalDispatch.Agreement

/-! Finite typed guard/call plans. Each branch uses the equality whose actual
machine step is proved in Table.eq_step. P1 owns physical calls/frames and the
coordinator owns final control-flow/bytecode integration; neither is fabricated. -/
namespace Solidity.Backend.InternalDispatch
open Source
variable {E : Source.Env} {ps rs : List STy} {qualifier : Option Source.Mutability}

def Table.code (t : Table E ps rs qualifier) : List (Fin t.size) := List.finRange t.size

def Table.runArms (t : Table E ps rs qualifier)
    {global : Source.Glob E} {frame : Source.Fr} {horizon : Nat}
    (frames : ObservationModel E ps rs qualifier global frame horizon)
    (word : Fin Evm.W) (state : frames.State) : List (Fin t.size) → Option frames.Result
  | [] => none
  | i :: rest => if word = t.tag i then some (frames.invoke (t.candidate i) state)
      else t.runArms frames word state rest

theorem Table.runArms_tag (t : Table E ps rs qualifier)
    {global : Source.Glob E} {frame : Source.Fr} {horizon : Nat}
    (frames : ObservationModel E ps rs qualifier global frame horizon)
    (state : frames.State) (i : Fin t.size) (arms : List (Fin t.size)) (member : i ∈ arms) :
    t.runArms frames (t.tag i) state arms = some (frames.invoke (t.candidate i) state) := by
  induction arms with
  | nil => cases member
  | cons j rest ih =>
    by_cases same : i = j
    · subst j
      simp only [Table.runArms, ite_true]
    · have different : t.tag i ≠ t.tag j := fun h => same (t.tag_injective h)
      simp only [Table.runArms, if_neg different]
      apply ih
      rcases List.mem_cons.mp member with equal | tail
      · exact False.elim (same equal)
      · exact tail

theorem Table.runArms_none (t : Table E ps rs qualifier)
    {global : Source.Glob E} {frame : Source.Fr} {horizon : Nat}
    (frames : ObservationModel E ps rs qualifier global frame horizon)
    (word : Fin Evm.W) (state : frames.State) (arms : List (Fin t.size))
    (absent : ∀ i ∈ arms, word ≠ t.tag i) : t.runArms frames word state arms = none := by
  induction arms with
  | nil => rfl
  | cons i rest ih =>
    simp only [Table.runArms, if_neg (absent i List.mem_cons_self)]
    exact ih fun j hj => absent j (List.mem_cons_of_mem _ hj)

theorem Table.tag_of_decode (t : Table E ps rs qualifier) (word : Fin Evm.W)
    (i : Fin t.size) (selected : t.decode word = some i) : word = t.tag i := by
  unfold Table.decode at selected
  split at selected
  · rename_i h
    have equality := congrArg Fin.val (Option.some.inj selected)
    apply Fin.ext
    change word.val = i.val + 1
    change word.val - 1 = i.val at equality
    omega
  · cases selected

/-- Compiling all finite candidates, in table order, agrees with canonical
word decoding on *all* words, including zero and foreign tags. -/
theorem Table.code_agrees (t : Table E ps rs qualifier)
    {global : Source.Glob E} {frame : Source.Fr} {horizon : Nat}
    (frames : ObservationModel E ps rs qualifier global frame horizon)
    (word : Fin Evm.W) (state : frames.State) :
    t.runArms frames word state t.code = t.execute frames word state := by
  cases selected : t.decode word with
  | none =>
    rw [Table.execute, selected, Option.map_none]
    apply t.runArms_none
    intro i _ equal
    rw [equal, t.decode_tag] at selected
    cases selected
  | some i =>
    have wordEq := t.tag_of_decode word i selected
    have member : i ∈ t.code := by
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    rw [wordEq, t.runArms_tag frames state i t.code member]
    simp only [Table.execute, t.decode_tag, Option.map_some]

/-- Whole typed dispatch, not just one guard, inherits the actual source-call
observation promised by the generic independent Source observation model. -/
theorem Table.compiled_correct (t : Table E ps rs qualifier)
    {global : Source.Glob E} {frame : Source.Fr} {horizon : Nat}
    (frames : ObservationModel E ps rs qualifier global frame horizon)
    (value : Source.Val E.layout (.fn false ps rs qualifier)) (word : Fin Evm.W)
    (represented : t.Rep value word) (args : Source.Vals E.layout ps)
    (source : Source.St E) (target : frames.State) (input : frames.input args source target) :
    ∃ i : Fin t.size, ∃ result : frames.Result,
      functionName value = some (t.candidate i).identity ∧
      t.runArms frames word target t.code = some result ∧
      frames.output (sourceCall global frame horizon (t.candidate i) args source) result := by
  rw [t.code_agrees]
  exact t.execute_correct frames value word represented args source target input

#print axioms Table.code_agrees
#print axioms Table.compiled_correct
end Solidity.Backend.InternalDispatch
