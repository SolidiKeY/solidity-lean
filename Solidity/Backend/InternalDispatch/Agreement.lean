import Solidity.Backend.InternalDispatch.Typed

/-! P4 independent Source observation model. Frozen P1 is consumed separately in FrozenV1.
No body execution, argument encoding, target frame implementation, or new source
halt policy is postulated as an axiom. An absent tag is protocol refusal only. -/
namespace Solidity.Backend.InternalDispatch
open Source
variable {E : Source.Env} {ps rs : List STy} {qualifier : Option Source.Mutability}

/-- Check the entire dependent signature against an actual environment member. -/
def Candidate.check (d : Source.Decl) (member : d ∈ E.decls) :
    Option (Candidate E ps rs qualifier) :=
  if hs : d.fnSig E = some (ps, rs) then
    if hm : d.fnMut = qualifier then
      if hi : d.fnVis ≠ some .external then some ⟨d, member, hs, hm, hi⟩ else none
    else none
  else none

theorem Candidate.check_complete (d : Source.Decl) (member : d ∈ E.decls)
    (hs : d.fnSig E = some (ps, rs)) (hm : d.fnMut = qualifier)
    (hi : d.fnVis ≠ some .external) :
    Candidate.check (ps := ps) (rs := rs) (qualifier := qualifier) d member =
      some ⟨d, member, hs, hm, hi⟩ := by
  simp only [Candidate.check, dif_pos hs, dif_pos hm, dif_pos hi]

theorem Candidate.check_wrong_signature (d : Source.Decl) (member : d ∈ E.decls)
    (wrong : d.fnSig E ≠ some (ps, rs)) :
    Candidate.check (ps := ps) (rs := rs) (qualifier := qualifier) d member = none := by
  simp only [Candidate.check, dif_neg wrong]

/-- Extraction must cover all same-signature internal declarations. No guessed
points-to subset is silently substituted for this separate proof obligation. -/
def Table.Complete (t : Table E ps rs qualifier) : Prop :=
  ∀ d ∈ E.decls, d.fnSig E = some (ps, rs) → d.fnMut = qualifier →
    d.fnVis ≠ some .external → ∃ i, (t.candidate i).declaration = d

/-- A complete table represents every eligible source declaration, retaining
its full signature. Extraction must still supply the completeness witness. -/
theorem Table.rep_of_complete (t : Table E ps rs qualifier) (complete : t.Complete)
    (d : Source.Decl) (member : d ∈ E.decls)
    (hs : d.fnSig E = some (ps, rs)) (hm : d.fnMut = qualifier)
    (hi : d.fnVis ≠ some .external) :
    ∃ word, t.Rep (.internalFn ⟨d.scope, d.name⟩) word := by
  obtain ⟨i, selected⟩ := complete d member hs hm hi
  refine ⟨t.tag i, i, ?_, rfl⟩
  simp only [functionName, Candidate.identity, selected]

/-- EQ really consumes two arithmetic words, leaves the supplied tail, and
preserves every other machine field. This is a step of the published evaluator. -/
theorem Table.eq_step (t : Table E ps rs qualifier)
    (value : Source.Val E.layout (.fn false ps rs qualifier)) (word : Fin Evm.W)
    (represented : t.Rep value word) (j : Fin t.size)
    (machine : Evm.Machine) (tail : List Evm.Word) :
    Evm.Instr.step .eq { machine with stack := .val word :: .val (t.tag j) :: tail } =
      .ok { machine with stack := .val (Evm.bword
        (decide (functionName value = some (t.candidate j).identity))) :: tail } 0 := by
  have values : (word.val = (t.tag j).val) ↔ word = t.tag j :=
    ⟨fun h => Fin.ext h, congrArg Fin.val⟩
  simp only [Evm.Instr.step, Evm.Machine.next, values, t.guard_agrees value word represented j]

/-- A full result of the independent source call, including timeout/error,
return value, empty outer-local component, heap, persistent/transient state and logs. -/
abbrev SourceObservation (E : Source.Env) (rs : List STy) :=
  Except Source.Halt (Source.RVal E.layout (STy.ret rs)) ×
    (Source.Locals E.layout [] × Source.St E)

def sourceCall (global : Source.Glob E) (frame : Source.Fr) (horizon : Nat)
    (candidate : Candidate E ps rs qualifier) (args : Source.Vals E.layout ps)
    (state : Source.St E) : SourceObservation E rs :=
  (Source.callInternal global frame horizon candidate.declaration args rs).run
    (Source.L0 E, state)

/-- Generic independent Source observation contract, not the frozen P1 interface. Target invocation reads only
its target state; source arguments are related by input, never supplied to the
target evaluator as an oracle. Output relates the complete actual source run. -/
structure ObservationModel (E : Source.Env) (ps rs : List STy)
    (qualifier : Option Source.Mutability) (global : Source.Glob E)
    (frame : Source.Fr) (horizon : Nat) where
  State : Type
  Result : Type
  input : Source.Vals E.layout ps → Source.St E → State → Prop
  output : SourceObservation E rs → Result → Prop
  invoke : Candidate E ps rs qualifier → State → Result
  correct : ∀ candidate args source target, input args source target →
    output (sourceCall global frame horizon candidate args source) (invoke candidate target)

/-- Executable dependent dispatch over a canonical word tag. None means no
candidate; this layer deliberately does not invent the missing source value-
call expression or choose the source/target unassigned-tag halt policy. -/
def Table.execute (t : Table E ps rs qualifier)
    {global : Source.Glob E} {frame : Source.Fr} {horizon : Nat}
    (frames : ObservationModel E ps rs qualifier global frame horizon)
    (word : Fin Evm.W) (state : frames.State) : Option frames.Result :=
  (t.decode word).map (fun i => frames.invoke (t.candidate i) state)

/-- Dispatch selects the identity named by the source function value and lifts
model agreement, retaining all signature indices and the whole source outcome. -/
theorem Table.execute_correct (t : Table E ps rs qualifier)
    {global : Source.Glob E} {frame : Source.Fr} {horizon : Nat}
    (frames : ObservationModel E ps rs qualifier global frame horizon)
    (value : Source.Val E.layout (.fn false ps rs qualifier)) (word : Fin Evm.W)
    (represented : t.Rep value word) (args : Source.Vals E.layout ps)
    (source : Source.St E) (target : frames.State) (input : frames.input args source target) :
    ∃ i : Fin t.size, ∃ result : frames.Result,
      functionName value = some (t.candidate i).identity ∧
      t.execute frames word target = some result ∧
      frames.output (sourceCall global frame horizon (t.candidate i) args source) result := by
  obtain ⟨i, name, rfl⟩ := represented
  refine ⟨i, frames.invoke (t.candidate i) target, name, ?_, frames.correct _ _ _ _ input⟩
  simp only [Table.execute, t.decode_tag, Option.map_some]

theorem Table.execute_zero (t : Table E ps rs qualifier)
    {global : Source.Glob E} {frame : Source.Fr} {horizon : Nat}
    (frames : ObservationModel E ps rs qualifier global frame horizon) (state : frames.State) :
    t.execute frames (Evm.wmod 0) state = none := by
  simp only [Table.execute, t.decode_zero, Option.map_none]

#print axioms Candidate.check_complete
#print axioms Table.eq_step
#print axioms Table.execute_correct
end Solidity.Backend.InternalDispatch
