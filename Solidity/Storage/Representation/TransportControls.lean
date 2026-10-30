import Solidity.Storage.Representation.Transport

/-! Inhabited finite-run controls, exact source observations and alias refusals. -/
namespace Solidity.Storage.Representation.TransportControls
open Solidity.Hash
private def zero : PrimTy.uint.Denote := ⟨0, by decide⟩
private def one : PrimTy.uint.Denote := ⟨1, by decide⟩
private def seven : PrimTy.uint.Denote := ⟨7, by decide⟩
private def nine : PrimTy.uint.Denote := ⟨9, by decide⟩
private def hash : Pre → Nat
  | .entry k _ => if k = 0 then 4 else 8
  | .data _ => 12
private def preimages : List Pre := [.entry 0 0, .entry 1 0, .data 0]
private def touched : List Loc := [.root 0, .hash 0 (.root 0) 0, .hash 1 (.root 0) 0,
  .data (.root 0) 0, .data (.root 0) 1]

/-- A genuinely inhabited root/mapping/data finite run; H is not globally injective. -/
theorem run : FiniteRun 16 2 1 hash preimages touched := by
  constructor
  · intro p
    cases p with
    | entry k _ => simp only [hash]; split <;> omega
    | data _ => simp only [hash]; omega
  · decide
  · decide
  · decide
  · intro l hl
    simp only [touched, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl <;> simp only [Loc.Bounded] <;> decide
  · intro l hl p hp
    simp only [touched, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl <;>
      simp only [Loc.pres, Loc.word, Nat.zero_mod, List.nil_append,
        List.mem_singleton, List.not_mem_nil] at hp
    all_goals subst p; decide

private def entries : SMap .bool Ty.uint :=
  .cons false (.prim seven) (.cons true (.prim nine) .nil)
private def source : SVal (.ref (.mapping .bool Ty.uint)) := .map entries (.prim zero)
private def words : Store := fun l => if l = .hash 0 (.root 0) 0 then seven else nine

theorem source_represented : ValueRep source (.map .word) (.root 0) words := by
  apply ValueRep.mapping
  · exact .scalar .uint
  · intro k
    cases k <;> simp only [entries, SMap.toList_cons, SMap.toList_nil]
    · exact .scalar seven _ _ rfl
    · exact .scalar nine _ _ rfl

/-- Existing source observations agree with a constructed numeric store. -/
theorem source_word_combination : ∃ m : WordStore,
    Transport 16 hash touched words m ∧
    m (Loc.word 16 hash (.hash 0 (.root 0) 0)) = PrimTy.toWord (source.obs.word (.key false .nil)) ∧
    m (Loc.word 16 hash (.hash 1 (.root 0) 0)) = PrimTy.toWord (source.obs.word (.key true .nil)) := by
  obtain ⟨m, transported, _⟩ := transport_exists run (fun _ => zero) words
  refine ⟨m, transported, ?_, ?_⟩
  · obtain ⟨value, found, represented⟩ := mapping_read source_represented false
    cases value with
    | prim v => exact source_word_observation found represented transported (by decide)
  · obtain ⟨value, found, represented⟩ := mapping_read source_represented true
    cases value with
    | prim v => exact source_word_observation found represented transported (by decide)

/-- A finite sequence preserves covered untouched words and frames all others. -/
theorem sequence_combination : ∃ m : WordStore,
    let m' := [((Loc.hash 0 (.root 0) 0), zero), ((Loc.data (.root 0) 0), seven)].foldl
      (fun store op => writeWord store (Loc.word 16 hash op.1) op.2) m
    m' 4 = zero ∧ m' 8 = nine ∧ m' 12 = seven ∧ m' 15 = zero := by
  let m : WordStore := realize 16 hash (fun _ => zero) words touched
  have transported : Transport 16 hash touched words m :=
    realize_transport _ _ _ (fun a ha b hb eq => run.word_inj ha hb eq)
  have sequence : Transport 16 hash touched
      ([((Loc.hash 0 (.root 0) 0), zero), ((Loc.data (.root 0) 0), seven)].foldl
        (fun store op => write store op.1 op.2) words)
      ([((Loc.hash 0 (.root 0) 0), zero), ((Loc.data (.root 0) 0), seven)].foldl
        (fun store op => writeWord store (Loc.word 16 hash op.1) op.2) m) :=
    transport_sequence run transported _ (by
      intro op member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide)
  refine ⟨m, ?_⟩
  constructor
  · exact sequence (.hash 0 (.root 0) 0) (by decide)
  · constructor
    · exact sequence (.hash 1 (.root 0) 0) (by decide)
    · constructor
      · exact sequence (.data (.root 0) 0) (by decide)
      · rfl

private def arrayValue : SVal (.ref (.array Ty.uint)) :=
  .array (.cons (.prim seven) .nil) (.cons (.prim nine) .nil) (by decide)
private def arrayWords : Store := fun l => if l = .root 0 then one
  else if l = .data (.root 0) 0 then seven else nine

/-- Header and element observations use the same finite numeric store. -/
theorem source_length_combination : ∃ m : WordStore,
    Transport 16 hash touched arrayWords m ∧
    (m (Loc.word 16 hash (.root 0))).val = arrayValue.obs.len .nil ∧
    m (Loc.word 16 hash (.data (.root 0) 0)) = PrimTy.toWord (arrayValue.obs.word (.at zero .nil)) := by
  have represented : ValueRep arrayValue (.darr .word) (.root 0) arrayWords := by
    apply ValueRep.array
    · exact .scalar .uint
    · decide
    · simp only [SVec.toList_cons, SVec.toList_nil, SList.toList_cons, SList.toList_nil,
        List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      decide
    · rfl
    · simp only [SVec.toList_cons, SVec.toList_nil, SList.toList_cons, SList.toList_nil,
        List.cons_append, List.nil_append]
      exact .cons _ _ _ _ _ (.scalar seven _ _ rfl)
        (.cons _ _ _ _ _ (.scalar nine _ _ rfl) (.nil _ _ _))
  obtain ⟨m, transported, _⟩ := transport_exists run (fun _ => zero) arrayWords
  refine ⟨m, transported, ?_, ?_⟩
  · exact source_length_observation (SVal.find_nil arrayValue) represented transported (by decide)
  · apply source_word_observation (v := seven) (w := arrayWords)
    · simp only [arrayValue, SVal.find_at, SVec.toList_cons, SVec.toList_nil,
        SList.toList_cons, SList.toList_nil, List.cons_append, List.nil_append]
      rfl
    · exact .scalar seven _ _ rfl
    · exact transported
    · decide

/-- An actual source mapping save, symbolic write and numeric write commute. -/
theorem source_save_combination : ∃ (changed : SVal (.ref (.mapping .bool Ty.uint)))
    (w : Store) (m : WordStore),
    source.save (.key false .nil) (.prim zero) = some changed ∧
    ValueRep changed (.map .word) (.root 0) w ∧ Transport 16 hash touched w m ∧
    m 4 = zero ∧ m 8 = nine ∧
    m 4 = PrimTy.toWord (changed.obs.word (.key false .nil)) := by
  obtain ⟨m, transported, _⟩ := transport_exists run (fun _ => zero) words
  have fresh : ValueRep (.prim zero) .word (.hash 0 (.root 0) 0) (fun _ => zero) :=
    .scalar zero _ _ rfl
  let changed : SVal (.ref (.mapping .bool Ty.uint)) :=
    .map (.ofList (Semantics.setBy false (.prim zero) entries.toList)) (.prim zero)
  have changedRep : ValueRep changed (.map .word) (.root 0) (write words (.hash 0 (.root 0) 0) zero) := by
    have prepared : ValueRep changed (.map .word) (.root 0)
        (patch words (fun _ => zero) .word (.hash 0 (.root 0) 0)) :=
      mapping_save source_represented false fresh
    rwa [patch_word] at prepared
  have saved : source.save (.key false .nil) (.prim zero) = some changed :=
    mapping_source_save entries (.prim zero) (.prim zero) false
  have next : Transport 16 hash touched (write words (.hash 0 (.root 0) 0) zero)
      (writeWord m (Loc.word 16 hash (.hash 0 (.root 0) 0)) zero) :=
    transport_write run transported _ (by decide) zero
  refine ⟨_, _, _, saved, changedRep, next, ?_, ?_, ?_⟩
  · exact next (.hash 0 (.root 0) 0) (by decide)
  · exact next (.hash 1 (.root 0) 0) (by decide)
  · apply source_word_observation (N := 16) (H := hash) (xs := touched)
      (l := .hash 0 (.root 0) 0) (w := write words (.hash 0 (.root 0) 0) zero)
    · exact SVal.find_save_same source _ _ saved
    · exact .scalar zero _ _ (write_same _ _ _)
    · exact next
    · decide

/-- Failed/default source observations coexist with nonzero numeric garbage. -/
theorem failure_presence_combination : ∃ m : WordStore,
    Transport 16 hash touched arrayWords m ∧ m 14 = nine ∧
    arrayValue.obs.has (.at (⟨2, by decide⟩ : PrimTy.uint.Denote) .nil) = false ∧
    arrayValue.obs.word (.at (⟨2, by decide⟩ : PrimTy.uint.Denote) .nil) = zero := by
  let m : WordStore := realize 16 hash (fun _ => nine) arrayWords touched
  have missing : arrayValue.find (.at (⟨2, by decide⟩ : PrimTy.uint.Denote) .nil) = none := by
    apply array_missing
    simp only [SVec.toList_cons, SVec.toList_nil, SList.toList_cons, SList.toList_nil,
      List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    decide
  refine ⟨m, realize_transport _ _ _ (fun a ha b hb eq => run.word_inj ha hb eq), rfl,
    source_failed_presence missing, ?_⟩
  exact source_failed_word_default missing

/-- Without touched-set coverage an unconstrained read can disagree. -/
theorem uncovered_read_can_disagree : ∃ m : WordStore,
    Transport 16 hash [.hash 0 (.root 0) 0] words m ∧ m 8 = zero ∧ zero ≠ nine := by
  refine ⟨realize 16 hash (fun _ => zero) words [.hash 0 (.root 0) 0], ?_, rfl, ?_⟩
  · apply realize_transport
    intro a ha b hb _
    simp only [List.mem_singleton] at ha hb
    exact ha.trans hb.symm
  · intro eq
    have bad : (0 : Int) = 9 := congrArg Subtype.val eq
    omega

/-- The existing offset-alias counterexample blocks transport without bounds. -/
theorem unbounded_offsets_rejected : ¬ ∃ m : WordStore,
    Transport 16 hash [.data (.root 0) 0] (fun _ => seven) m ∧
    Transport 16 hash [.data (.root 0) 16] (fun _ => nine) m := by
  rintro ⟨m, hx, hy⟩
  have eq : seven = nine := transport_alias_consistent
    (x := .data (.root 0) 0) (y := .data (.root 0) 16) hx hy (by decide) (by decide)
    (Loc.word_data_alias 16 hash (.root 0) (by decide)).2
  have bad : (7 : Int) = 9 := congrArg Subtype.val eq
  omega

/-- Without the region premise a numeric alias cannot represent distinct values. -/
theorem colliding_observations_rejected : ¬ ∃ m : WordStore,
    Transport 16 (fun _ => 0) [.root 0] (fun _ => seven) m ∧
    Transport 16 (fun _ => 0) [.hash 0 (.root 0) 0] (fun _ => nine) m := by
  rintro ⟨m, hx, hy⟩
  have eq : seven = nine := transport_alias_consistent (x := .root 0) (y := .hash 0 (.root 0) 0) hx hy (by decide) (by decide) rfl
  have bad : (7 : Int) = 9 := congrArg Subtype.val eq
  omega

/-- info: 'Solidity.Storage.Representation.transport_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transport_exists
/-- info: 'Solidity.Storage.Representation.transport_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transport_write
/-- info: 'Solidity.Storage.Representation.transport_sequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transport_sequence
/-- info: 'Solidity.Storage.Representation.transport_patch_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transport_patch_frames
/-- info: 'Solidity.Storage.Representation.transport_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transport_extend
/-- info: 'Solidity.Storage.Representation.sequence_outside_frame' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms sequence_outside_frame
/-- info: 'Solidity.Storage.Representation.source_word_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_word_observation
/-- info: 'Solidity.Storage.Representation.source_length_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_length_observation
/-- info: 'Solidity.Storage.Representation.TransportControls.source_word_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_word_combination
/-- info: 'Solidity.Storage.Representation.TransportControls.source_length_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_length_combination
/-- info: 'Solidity.Storage.Representation.TransportControls.source_save_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_save_combination
/-- info: 'Solidity.Storage.Representation.TransportControls.failure_presence_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms failure_presence_combination
/-- info: 'Solidity.Storage.Representation.TransportControls.colliding_observations_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms colliding_observations_rejected
/-- info: 'Solidity.Storage.Representation.TransportControls.unbounded_offsets_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unbounded_offsets_rejected
end Solidity.Storage.Representation.TransportControls
