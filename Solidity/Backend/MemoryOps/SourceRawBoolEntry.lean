import Solidity.Backend.MemoryOps.SourceRawBoolCopy

/-! Actual dynamic entry guard followed by raw Boolean copy. The existing
cdTail order, selector-relative offsets and decoder are unchanged. -/
namespace Solidity.Backend.MemoryOps

theorem raw_bool_frame_word (F : Source.Fr) (selectorBytes data : List UInt8)
    (four : selectorBytes.length=4) (binding : F.cd=selectorBytes++data) (off j : Nat) :
    Source.cdWordAt F (4+off+32*j)=Source.beValue (Source.fitBytes 32 (data.drop (off+32*j))) := by
  first
  | solve | simp only [] | omega
  | unfold Source.cdWordAt
    rw [binding,Nat.add_assoc,←four,List.drop_length_add_append]

/-- No guard/copy success is assumed: both actual operations determine the
complete outcome, with the guard evaluated before any Boolean validation. -/
theorem source_raw_bool_guarded_run {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (data : List UInt8) (i : Nat) (y : Source.EMState E Γ) :
    ((Source.EM.lift (Source.cdTail data i 32)) >>= fun p => Source.cdToMem F SourceBoolArrayTy p.1 p.2).run y=
      match Source.cdTail data i 32 with
      | .error e => (.error e,y)
      | .ok (off,len) => (Source.cdToMem F SourceBoolArrayTy off len).run y := by
  first
  | solve | simp only [] | omega
  | rw [Source.Hoare.run_bind]
    cases guard : Source.cdTail data i 32 with
    | error e => simp only [Source.EM.lift];rfl
    | ok p => simp only [Source.EM.lift];rfl

/-- Initial entry bounds and canonical argument bytes derive the actual guard,
selector-relative copy location, fresh allocation and complete copy result. -/
theorem source_raw_bool_entry_success {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (selectorBytes data : List UInt8) (four : selectorBytes.length=4)
    (binding : F.cd=selectorBytes++data) (i : Nat) (y : Source.EMState E Γ)
    (head : ¬data.length<Source.wordAt data i+32)
    (small : ¬2^64≤Source.wordAt (data.drop (Source.wordAt data i)) 0)
    (span : Source.wordAt data i+32+32*Source.wordAt (data.drop (Source.wordAt data i)) 0≤data.length)
    (canonical : ∀ j,j<Source.wordAt (data.drop (Source.wordAt data i)) 0 →
      let w := Source.beValue (Source.fitBytes 32 (data.drop (Source.wordAt data i+32+32*j)))
      w=0 ∨ w=1) :
    ((Source.EM.lift (Source.cdTail data i 32)) >>= fun p => Source.cdToMem F SourceBoolArrayTy p.1 p.2).run y=
      let off := 4+Source.wordAt data i+32
      let len := Source.wordAt (data.drop (Source.wordAt data i)) 0
      (.ok (.val (.memRef rfl y.2.heap.next)),(y.1,{y.2 with heap :=
        (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory (rawBoolPayload F off len)⟩).1})) := by
  first
  | solve | simp only [] | omega
  | rw [source_raw_bool_guarded_run]
    simp only [Source.cdTail,if_neg head,if_neg small,if_pos span,pure,Except.pure]
    apply source_raw_bool_copy
    intro j hj
    rw [show 4+Source.wordAt data i+32+32*j=4+(Source.wordAt data i+32)+32*j by omega,
      raw_bool_frame_word F selectorBytes data four binding]
    exact canonical j hj

/-- All three entry refusals stop before the copy and preserve initial state.
This is not a refusal theorem for standalone cdToMem. -/
theorem source_raw_bool_entry_refused {E : Source.Env} {Γ : Source.RCtx}
    (F : Source.Fr) (data : List UInt8) (i : Nat) (y : Source.EMState E Γ)
    (refusal : data.length<Source.wordAt data i+32 ∨
      2^64≤Source.wordAt (data.drop (Source.wordAt data i)) 0 ∨
      ¬Source.wordAt data i+32+32*Source.wordAt (data.drop (Source.wordAt data i)) 0≤data.length) :
    Source.cdTail data i 32=.error (.revert []) ∧
    ((Source.EM.lift (Source.cdTail data i 32)) >>= fun p => Source.cdToMem F SourceBoolArrayTy p.1 p.2).run y=
      (.error (.revert []),y) := by
  first
  | solve | simp only [] | omega
  | have rejected : Source.cdTail data i 32=.error (.revert []) := by
      by_cases h : data.length<Source.wordAt data i+32
      · simp only [Source.cdTail,if_pos h]
      · by_cases large : 2^64≤Source.wordAt (data.drop (Source.wordAt data i)) 0
        · simp only [Source.cdTail,if_neg h,if_pos large]
        · have short : ¬Source.wordAt data i+32+32*Source.wordAt (data.drop (Source.wordAt data i)) 0≤data.length :=
            refusal.elim (fun impossible => False.elim (h impossible)) (fun rest => rest.elim (fun impossible => False.elim (large impossible)) id)
          simp only [Source.cdTail,if_neg h,if_neg large,if_neg short]
    exact ⟨rejected,by rw [source_raw_bool_guarded_run,rejected]⟩

/-- info: 'Solidity.Backend.MemoryOps.raw_bool_frame_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_bool_frame_word
/-- info: 'Solidity.Backend.MemoryOps.source_raw_bool_guarded_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_raw_bool_guarded_run
/-- info: 'Solidity.Backend.MemoryOps.source_raw_bool_entry_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_raw_bool_entry_success
/-- info: 'Solidity.Backend.MemoryOps.source_raw_bool_entry_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_raw_bool_entry_refused
end Solidity.Backend.MemoryOps
