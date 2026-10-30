import Solidity.Lowering.V08.Transactions

/-! Finite-prefix composition of actual World.transact applications. The fold
accumulates only the existing World and the complete ordered TRes history.
It neither interprets frames nor supplies Source/body/ABI/runtime relations. -/
namespace Solidity.Lowering.V08
open Solidity.ContractWorld
variable {K : Type} {contracts : K → Contract} {α : Type}

abbrev TransactionFrame (contracts : K → Contract) (α : Type) :=
  World contracts → TRes (World contracts × α)

def transactStep (before : World contracts × List (TRes α))
    (frame : TransactionFrame contracts α) : World contracts × List (TRes α) :=
  let next := before.1.transact frame
  (next.1, before.2 ++ [next.2])

/-- Ordinary fold, never a new frame evaluator. Errors remain history entries;
every following transaction still invokes the published boundary operation. -/
def transactPrefix (w : World contracts) (frames : List (TransactionFrame contracts α)) :
    World contracts × List (TRes α) := frames.foldl transactStep (w, [])

theorem transact_step_history (before : World contracts × List (TRes α))
    (history : List (TRes α)) (frame : TransactionFrame contracts α) :
    transactStep (before.1, history ++ before.2) frame =
      ((transactStep before frame).1, history ++ (transactStep before frame).2) := by
  simp only [transactStep, List.append_assoc]

private theorem transact_fold_history (frames : List (TransactionFrame contracts α))
    (before : World contracts × List (TRes α)) (history : List (TRes α)) :
    frames.foldl transactStep (before.1, history ++ before.2) =
      ((frames.foldl transactStep before).1, history ++ (frames.foldl transactStep before).2) := by
  induction frames generalizing before with
  | nil => rfl
  | cons frame frames ih =>
    simp only [List.foldl_cons, transact_step_history]
    exact ih (transactStep before frame)

theorem transact_prefix_nil (w : World contracts) :
    transactPrefix (α := α) w [] = (w, []) := rfl

theorem transact_prefix_cons (w : World contracts) (frame : TransactionFrame contracts α)
    (frames : List (TransactionFrame contracts α)) :
    transactPrefix w (frame :: frames) =
      ((transactPrefix (w.transact frame).1 frames).1,
        (w.transact frame).2 :: (transactPrefix (w.transact frame).1 frames).2) := by
  unfold transactPrefix
  simp only [List.foldl_cons]
  simpa only [List.append_nil, List.cons_append, List.nil_append] using
    (transact_fold_history frames ((w.transact frame).1, []) [(w.transact frame).2])

/-- Complete earlier/append law: the suffix starts at the actually committed
earlier world; every earlier exact result/status stays in its original order. -/
theorem transact_prefix_append (w : World contracts)
    (earlier suffix : List (TransactionFrame contracts α)) :
    transactPrefix w (earlier ++ suffix) =
      ((transactPrefix (transactPrefix w earlier).1 suffix).1,
        (transactPrefix w earlier).2 ++ (transactPrefix (transactPrefix w earlier).1 suffix).2) := by
  unfold transactPrefix
  rw [List.foldl_append]
  simpa only [List.append_nil] using
    (transact_fold_history suffix ((earlier.foldl transactStep (w, [])).1, [])
      (earlier.foldl transactStep (w, [])).2)

theorem transact_prefix_snoc (w : World contracts) (earlier : List (TransactionFrame contracts α))
    (frame : TransactionFrame contracts α) :
    transactPrefix w (earlier ++ [frame]) = transactStep (transactPrefix w earlier) frame := by
  simp only [transactPrefix, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Singleton prefix retains the exact boundary result. -/
theorem transact_prefix_singleton (w : World contracts) (frame : TransactionFrame contracts α) :
    transactPrefix w [frame] = ((w.transact frame).1, [(w.transact frame).2]) := by
  simpa only [transact_prefix_nil, List.nil_append, transactStep] using
    (transact_prefix_snoc w [] frame)

theorem transact_prefix_length (w : World contracts) (frames : List (TransactionFrame contracts α)) :
    (transactPrefix w frames).2.length = frames.length := by
  induction frames generalizing w with
  | nil => rfl
  | cons frame frames ih =>
    simp only [transact_prefix_cons, List.length_cons, ih]

/-- The published operation resets its actual input and output for every halt. -/
theorem transact_output_normalized (w : World contracts) (frame : TransactionFrame contracts α) :
    (w.transact frame).1.resetTransient = (w.transact frame).1 := by
  unfold World.transact
  cases frame w.resetTransient with
  | error halt => exact resetTransient_idem w
  | ok pair => exact resetTransient_idem pair.1

theorem transact_input_reset (w : World contracts) (frame : TransactionFrame contracts α) :
    w.resetTransient.transact frame = w.transact frame := by
  unfold World.transact
  rw [resetTransient_idem]

private theorem transact_fold_normalized (frames : List (TransactionFrame contracts α))
    (before : World contracts × List (TRes α)) (normal : before.1.resetTransient = before.1) :
    (frames.foldl transactStep before).1.resetTransient = (frames.foldl transactStep before).1 := by
  induction frames generalizing before with
  | nil => exact normal
  | cons frame frames ih =>
    simp only [List.foldl_cons]
    exact ih (transactStep before frame) (transact_output_normalized before.1 frame)

/-- Applies at every nonempty finite earlier, with no length/depth bound.
The empty earlier intentionally retains its original possibly dirty world. -/
theorem transact_prefix_normalized (w : World contracts) (first : TransactionFrame contracts α)
    (rest : List (TransactionFrame contracts α)) :
    (transactPrefix w (first :: rest)).1.resetTransient = (transactPrefix w (first :: rest)).1 := by
  unfold transactPrefix
  simp only [List.foldl_cons]
  exact transact_fold_normalized rest (transactStep (w, []) first)
    (transact_output_normalized w first)

theorem transact_prefix_initial_reset (w : World contracts) (first : TransactionFrame contracts α)
    (rest : List (TransactionFrame contracts α)) :
    transactPrefix w.resetTransient (first :: rest) = transactPrefix w (first :: rest) := by
  simp only [transact_prefix_cons, transact_input_reset]

theorem transact_prefix_commit_snoc (w next : World contracts)
    (earlier : List (TransactionFrame contracts α)) (frame : TransactionFrame contracts α) (value : α)
    (ran : frame (transactPrefix w earlier).1.resetTransient = .ok (next, value)) :
    transactPrefix w (earlier ++ [frame]) =
      (next.resetTransient, (transactPrefix w earlier).2 ++ [.ok value]) := by
  rw [transact_prefix_snoc]
  simp only [transactStep, World.transact_commit _ _ _ _ ran]

theorem transact_prefix_failure_snoc (w : World contracts)
    (earlier : List (TransactionFrame contracts α)) (frame : TransactionFrame contracts α) (halt : THalt)
    (failed : frame (transactPrefix w earlier).1.resetTransient = .error halt) :
    transactPrefix w (earlier ++ [frame]) =
      ((transactPrefix w earlier).1.resetTransient, (transactPrefix w earlier).2 ++ [.error halt]) := by
  rw [transact_prefix_snoc]
  simp only [transactStep, World.transact_failure _ _ _ failed]

/-- A failed transaction neither erases earlier statuses nor short-circuits
later transactions. Only its own writes roll back to the preceding reset world. -/
theorem transact_prefix_failure_suffix (w : World contracts)
    (earlier suffix : List (TransactionFrame contracts α)) (frame : TransactionFrame contracts α) (halt : THalt)
    (failed : frame (transactPrefix w earlier).1.resetTransient = .error halt) :
    transactPrefix w ((earlier ++ [frame]) ++ suffix) =
      ((transactPrefix (transactPrefix w earlier).1.resetTransient suffix).1,
        (transactPrefix w earlier).2 ++
          .error halt :: (transactPrefix (transactPrefix w earlier).1.resetTransient suffix).2) := by
  rw [transact_prefix_append w (earlier ++ [frame]) suffix,
    transact_prefix_failure_snoc w earlier frame halt failed]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Pure result extension of an existing frame; world and exact halt retained. -/
def observeTransactionFrame {β : Type} (frame : TransactionFrame contracts α)
    (observation : α → β) : TransactionFrame contracts β := fun w =>
  (frame w).map (fun pair => (pair.1, observation pair.2))

/-- Lift published single-transaction observation transport to every finite
prefix, retaining the entire ordered success/error history and exact world. -/
theorem transact_prefix_observe {β : Type} (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (observation : α → β) :
    transactPrefix w (frames.map (fun frame => observeTransactionFrame frame observation)) =
      ((transactPrefix w frames).1, (transactPrefix w frames).2.map (fun result => result.map observation)) := by
  induction frames generalizing w with
  | nil => rfl
  | cons frame rest ih =>
    have one : w.transact (observeTransactionFrame frame observation) =
        ((w.transact frame).1, (w.transact frame).2.map observation) :=
      transact_observe w frame observation
    simp only [List.map_cons, transact_prefix_cons, one, ih]

/-- Splitting a history uses the world reached by the actual preceding fold. -/
theorem transact_prefix_take_drop (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (i : Nat) :
    transactPrefix w frames =
      ((transactPrefix (transactPrefix w (frames.take i)).1 (frames.drop i)).1,
        (transactPrefix w (frames.take i)).2 ++
          (transactPrefix (transactPrefix w (frames.take i)).1 (frames.drop i)).2) := by
  have split := transact_prefix_append w (frames.take i) (frames.drop i)
  rw [List.take_append_drop] at split
  exact split

/-- Results before the split are independent of all later frames, including
later failures. For out-of-range i, both sides simply retain the whole history. -/
theorem transact_prefix_take_history (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (i : Nat) :
    (transactPrefix w frames).2.take i = (transactPrefix w (frames.take i)).2 := by
  induction frames generalizing w i with
  | nil => simp only [List.take_nil, List.drop_nil, transact_prefix_nil]
  | cons frame rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [transact_prefix_cons, List.take_succ_cons]
      exact congrArg (List.cons (w.transact frame).2) (ih (w.transact frame).1 i)

/-- The history suffix is precisely the suffix's execution at the reached world. -/
theorem transact_prefix_drop_history (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (i : Nat) :
    (transactPrefix w frames).2.drop i =
      (transactPrefix (transactPrefix w (frames.take i)).1 (frames.drop i)).2 := by
  induction frames generalizing w i with
  | nil => simp only [List.take_nil, List.drop_nil, transact_prefix_nil]
  | cons frame rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [transact_prefix_cons, List.take_succ_cons, List.drop_succ_cons]
      exact ih (w.transact frame).1 i

/-- Every valid frame index is also a valid index of the complete result history. -/
theorem transact_prefix_index_bound (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (i : Nat) (valid : i < frames.length) :
    i < (transactPrefix w frames).2.length := by
  rw [transact_prefix_length]
  exact valid

/-- Exact indexed result from the published transaction boundary at the actual
world reached by the earlier frames. No assumed trace preservation premise. -/
theorem transact_prefix_index (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (i : Nat) (valid : i < frames.length) :
    (transactPrefix w frames).2[i]'(transact_prefix_index_bound w frames i valid) =
      ((transactPrefix w (frames.take i)).1.transact frames[i]).2 := by
  induction frames generalizing w i with
  | nil => exact False.elim (Nat.not_lt_zero i valid)
  | cons frame rest ih =>
    cases i with
    | zero => simp only [transact_prefix_cons, List.take_zero, transact_prefix_nil, List.getElem_cons_zero]
    | succ i =>
      simpa only [transact_prefix_cons, List.getElem_cons_succ, List.take_succ_cons] using
        (ih (w.transact frame).1 i (Nat.lt_of_succ_lt_succ valid))

/-- The indexed successful value remains typed and complete. -/
theorem transact_prefix_index_success (w next : World contracts)
    (frames : List (TransactionFrame contracts α)) (i : Nat) (valid : i < frames.length)
    (value : α)
    (ran : frames[i] (transactPrefix w (frames.take i)).1.resetTransient = .ok (next, value)) :
    (transactPrefix w frames).2[i]'(transact_prefix_index_bound w frames i valid) = .ok value ∧
      (transactPrefix w (frames.take (i + 1))).1 = next.resetTransient := by
  constructor
  · rw [transact_prefix_index w frames i valid, World.transact_commit _ _ _ _ ran]
  · rw [List.take_succ_eq_append_getElem valid,
      transact_prefix_commit_snoc w next (frames.take i) frames[i] value ran]

/-- An indexed error keeps its exact halt and rolls back only this transaction,
to the actual preceding reset snapshot; later transactions still execute. -/
theorem transact_prefix_index_failure (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (i : Nat) (valid : i < frames.length)
    (halt : THalt)
    (failed : frames[i] (transactPrefix w (frames.take i)).1.resetTransient = .error halt) :
    (transactPrefix w frames).2[i]'(transact_prefix_index_bound w frames i valid) = .error halt ∧
      (transactPrefix w (frames.take (i + 1))).1 =
        (transactPrefix w (frames.take i)).1.resetTransient := by
  constructor
  · rw [transact_prefix_index w frames i valid, World.transact_failure _ _ _ failed]
  · rw [List.take_succ_eq_append_getElem valid,
      transact_prefix_failure_snoc w (frames.take i) frames[i] halt failed]

/-- Indexed observation extension retains success mapping and exact errors at
the same position, with a bound proved for both actual histories. -/
theorem transact_prefix_index_observe {β : Type} (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (observation : α → β)
    (i : Nat) (valid : i < frames.length) :
    (transactPrefix w (frames.map (fun frame => observeTransactionFrame frame observation))).2[i]'(by
      rw [transact_prefix_length, List.length_map]; exact valid) =
      ((transactPrefix w frames).2[i]'(transact_prefix_index_bound w frames i valid)).map observation := by
  simp only [transact_prefix_observe, List.getElem_map]

/-- A recorded indexed error itself determines the actual frame failure and
its immediate rollback boundary. This converse assumes only the exact observed
history entry, not a whole execution equation or source preservation relation. -/
theorem transact_prefix_failure_of_index (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (i : Nat) (valid : i < frames.length)
    (halt : THalt)
    (observed : (transactPrefix w frames).2[i]'(transact_prefix_index_bound w frames i valid) = .error halt) :
    frames[i] (transactPrefix w (frames.take i)).1.resetTransient = .error halt ∧
      (transactPrefix w (frames.take (i + 1))).1 =
        (transactPrefix w (frames.take i)).1.resetTransient := by
  have result : ((transactPrefix w (frames.take i)).1.transact frames[i]).2 = .error halt :=
    (transact_prefix_index w frames i valid).symm.trans observed
  have failed : frames[i] (transactPrefix w (frames.take i)).1.resetTransient = .error halt := by
    cases ran : frames[i] (transactPrefix w (frames.take i)).1.resetTransient with
    | error actual =>
      simp only [World.transact, ran] at result
      exact congrArg Except.error (Except.error.inj result)
    | ok pair =>
      simp only [World.transact, ran] at result
      cases result
  exact ⟨failed, (transact_prefix_index_failure w frames i valid halt failed).2⟩

/-- Exact error observations characterize actual failure at the reached input. -/
theorem transact_prefix_index_error_iff (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (i : Nat) (valid : i < frames.length)
    (halt : THalt) :
    (transactPrefix w frames).2[i]'(transact_prefix_index_bound w frames i valid) = .error halt ↔
      frames[i] (transactPrefix w (frames.take i)).1.resetTransient = .error halt :=
  ⟨fun observed => (transact_prefix_failure_of_index w frames i valid halt observed).1,
    fun failed => (transact_prefix_index_failure w frames i valid halt failed).1⟩

/-- A successful history entry reconstructs an actual raw next world from the
indexed frame. Only its reset equals the immediate boundary: the raw world may
still contain transient values, and no later/final world equality follows. -/
theorem transact_prefix_success_of_index (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (i : Nat) (valid : i < frames.length)
    (value : α)
    (observed : (transactPrefix w frames).2[i]'(transact_prefix_index_bound w frames i valid) = .ok value) :
    ∃ next : World contracts,
      frames[i] (transactPrefix w (frames.take i)).1.resetTransient = .ok (next, value) ∧
      (transactPrefix w (frames.take (i + 1))).1 = next.resetTransient := by
  have result : ((transactPrefix w (frames.take i)).1.transact frames[i]).2 = .ok value :=
    (transact_prefix_index w frames i valid).symm.trans observed
  have executed : ∃ next : World contracts,
      frames[i] (transactPrefix w (frames.take i)).1.resetTransient = .ok (next, value) := by
    cases ran : frames[i] (transactPrefix w (frames.take i)).1.resetTransient with
    | error halt =>
      simp only [World.transact, ran] at result
      cases result
    | ok pair =>
      rcases pair with ⟨next, actual⟩
      simp only [World.transact, ran] at result
      have same : actual = value := Except.ok.inj result
      subst actual
      exact ⟨next, rfl⟩
  obtain ⟨next, ran⟩ := executed
  exact ⟨next, ran, (transact_prefix_index_success w next frames i valid value ran).2⟩

/-- Success observations characterize the actual raw frame return and its
normalized immediate boundary, without identifying raw and reset worlds. -/
theorem transact_prefix_index_ok_iff (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (i : Nat) (valid : i < frames.length)
    (value : α) :
    (transactPrefix w frames).2[i]'(transact_prefix_index_bound w frames i valid) = .ok value ↔
      ∃ next : World contracts,
        frames[i] (transactPrefix w (frames.take i)).1.resetTransient = .ok (next, value) ∧
        (transactPrefix w (frames.take (i + 1))).1 = next.resetTransient := by
  constructor
  · exact transact_prefix_success_of_index w frames i valid value
  · rintro ⟨next, ran, _⟩
    exact (transact_prefix_index_success w next frames i valid value ran).1

/-- Complete ordered middle history from the genuinely reached prefix world.
No index/length cutoff: take/drop truncate naturally, including empty segments. -/
theorem transact_prefix_segment_history (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (start count : Nat) :
    ((transactPrefix w frames).2.drop start).take count =
      (transactPrefix (transactPrefix w (frames.take start)).1
        ((frames.drop start).take count)).2 := by
  rw [transact_prefix_drop_history, transact_prefix_take_history]

/-- The actual segment endpoint is the corresponding whole-prefix endpoint,
not the initial world or an arbitrary normalized guess. -/
theorem transact_prefix_segment_boundary (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (start count : Nat) :
    (transactPrefix (transactPrefix w (frames.take start)).1
      ((frames.drop start).take count)).1 =
      (transactPrefix w (frames.take (start + count))).1 := by
  have split := congrArg Prod.fst
    (transact_prefix_append w (frames.take start) ((frames.drop start).take count))
  rw [← List.take_add] at split
  exact split.symm

/-- World AND entire result history of every finite middle segment. -/
theorem transact_prefix_segment_complete (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (start count : Nat) :
    transactPrefix (transactPrefix w (frames.take start)).1 ((frames.drop start).take count) =
      ((transactPrefix w (frames.take (start + count))).1,
        ((transactPrefix w frames).2.drop start).take count) :=
  Prod.ext (transact_prefix_segment_boundary w frames start count)
    (transact_prefix_segment_history w frames start count).symm

/-- Valid local frame indices have proved bounds in the corresponding history
slice, irrespective of out-of-range/truncated global segment endpoints. -/
theorem transact_prefix_segment_index_bound (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (start count i : Nat)
    (valid : i < ((frames.drop start).take count).length) :
    i < (((transactPrefix w frames).2.drop start).take count).length := by
  rw [transact_prefix_segment_history, transact_prefix_length]
  exact valid

/-- Two-sided successful observation at any valid local segment index, with
actual raw return and ONLY its normalized immediate local boundary. -/
theorem transact_prefix_segment_ok_iff (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (start count i : Nat)
    (valid : i < ((frames.drop start).take count).length) (value : α) :
    (((transactPrefix w frames).2.drop start).take count)[i]'(transact_prefix_segment_index_bound w frames start count i valid) = .ok value ↔
      ∃ next : World contracts,
        ((frames.drop start).take count)[i]
          (transactPrefix (transactPrefix w (frames.take start)).1
            (((frames.drop start).take count).take i)).1.resetTransient = .ok (next, value) ∧
        (transactPrefix (transactPrefix w (frames.take start)).1
          (((frames.drop start).take count).take (i + 1))).1 = next.resetTransient := by
  simpa only [transact_prefix_segment_history] using
    (transact_prefix_index_ok_iff (transactPrefix w (frames.take start)).1
      ((frames.drop start).take count) i valid value)

/-- Two-sided exact failure at a local segment index; earlier/later statuses
remain untouched and the immediate rollback uses the actual local prefix. -/
theorem transact_prefix_segment_error_iff (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (start count i : Nat)
    (valid : i < ((frames.drop start).take count).length) (halt : THalt) :
    (((transactPrefix w frames).2.drop start).take count)[i]'(transact_prefix_segment_index_bound w frames start count i valid) = .error halt ↔
      ((frames.drop start).take count)[i]
        (transactPrefix (transactPrefix w (frames.take start)).1
          (((frames.drop start).take count).take i)).1.resetTransient = .error halt ∧
      (transactPrefix (transactPrefix w (frames.take start)).1
        (((frames.drop start).take count).take (i + 1))).1 =
        (transactPrefix (transactPrefix w (frames.take start)).1
          (((frames.drop start).take count).take i)).1.resetTransient := by
  constructor
  · intro observed
    have localError : (transactPrefix (transactPrefix w (frames.take start)).1
        ((frames.drop start).take count)).2[i]'(transact_prefix_index_bound _ _ i valid) = .error halt := by
      simpa only [transact_prefix_segment_history] using observed
    exact transact_prefix_failure_of_index _ _ i valid halt localError
  · rintro ⟨failed, _⟩
    have localError := (transact_prefix_index_failure _ _ i valid halt failed).1
    simpa only [transact_prefix_segment_history] using localError

/-- An injective typed observer reflects exact TRes equality, retaining every
THalt and the success/error distinction. No World equality is inferred. -/
theorem result_observe_eq_iff {β : Type} (observation : α → β)
    (injective : ∀ x y, observation x = observation y → x = y) (first second : TRes α) :
    first.map observation = second.map observation ↔ first = second := by
  constructor
  · intro same
    cases first with
    | error halt =>
      cases second with
      | error other => exact congrArg Except.error (Except.error.inj same)
      | ok value => cases same
    | ok value =>
      cases second with
      | error halt => cases same
      | ok other => exact congrArg Except.ok (injective value other (Except.ok.inj same))
  · intro same
    exact congrArg (fun result => result.map observation) same

/-- Reflection of the ENTIRE ordered history, including all exact error data.
Injectivity is a real premise, not inferred from an observed trace. -/
theorem history_observe_eq_iff {β : Type} (observation : α → β)
    (injective : ∀ x y, observation x = observation y → x = y)
    (first second : List (TRes α)) :
    first.map (fun result => result.map observation) =
      second.map (fun result => result.map observation) ↔ first = second :=
  List.map_inj_right (fun x y same => (result_observe_eq_iff observation injective x y).mp same)

/-- Equality of actual observed transaction histories reflects equality of the
original histories only. Initial/final Worlds may differ between the two runs. -/
theorem transact_prefix_observe_reflect_iff {β : Type} (w other : World contracts)
    (first second : List (TransactionFrame contracts α)) (observation : α → β)
    (injective : ∀ x y, observation x = observation y → x = y) :
    (transactPrefix w (first.map (fun frame => observeTransactionFrame frame observation))).2 =
      (transactPrefix other (second.map (fun frame => observeTransactionFrame frame observation))).2 ↔
    (transactPrefix w first).2 = (transactPrefix other second).2 := by
  simp only [transact_prefix_observe]
  exact history_observe_eq_iff observation injective _ _

/-- Actual observed whole-history slices map EVERY ordered result in the
corresponding original segment; empty/truncated segments remain total. -/
theorem transact_prefix_segment_observe_history {β : Type} (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (start count : Nat) (observation : α → β) :
    (((transactPrefix w (frames.map (fun frame => observeTransactionFrame frame observation))).2.drop start).take count) =
      (((transactPrefix w frames).2.drop start).take count).map (fun result => result.map observation) := by
  simp only [transact_prefix_observe, ← List.map_drop, ← List.map_take]

/-- Observing an actual segment retains its reached endpoint and maps the
complete history slice. Its starting world is the genuinely reached prefix. -/
theorem transact_prefix_segment_observe_complete {β : Type} (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (start count : Nat) (observation : α → β) :
    transactPrefix (transactPrefix w (frames.take start)).1
      (((frames.drop start).take count).map (fun frame => observeTransactionFrame frame observation)) =
      ((transactPrefix w (frames.take (start + count))).1,
        (((transactPrefix w frames).2.drop start).take count).map (fun result => result.map observation)) := by
  rw [transact_prefix_observe, transact_prefix_segment_complete]

/-- Injective reflection of an actual observed segment against any complete
candidate history. This implies no equivalence of Source/ABI or world states. -/
theorem transact_prefix_segment_observe_reflect_iff {β : Type} (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (start count : Nat)
    (observation : α → β) (injective : ∀ x y, observation x = observation y → x = y)
    (candidate : List (TRes α)) :
    (((transactPrefix w (frames.map (fun frame => observeTransactionFrame frame observation))).2.drop start).take count) =
      candidate.map (fun result => result.map observation) ↔
      ((transactPrefix w frames).2.drop start).take count = candidate := by
  rw [transact_prefix_segment_observe_history]
  exact history_observe_eq_iff observation injective _ candidate

/-- Subdivide an actual naturally truncated segment into adjacent segments.
The second starts at the genuinely reached first endpoint, including empties. -/
theorem transact_prefix_segment_subdivide (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (start left right : Nat) :
    transactPrefix (transactPrefix w (frames.take start)).1
      ((frames.drop start).take (left + right)) =
      ((transactPrefix (transactPrefix w (frames.take (start + left))).1
          ((frames.drop (start + left)).take right)).1,
        (transactPrefix (transactPrefix w (frames.take start)).1
          ((frames.drop start).take left)).2 ++
        (transactPrefix (transactPrefix w (frames.take (start + left))).1
          ((frames.drop (start + left)).take right)).2) := by
  have split : (frames.drop start).take (left + right) =
      (frames.drop start).take left ++ (frames.drop (start + left)).take right := by
    rw [List.take_add, List.drop_drop]
  rw [split, transact_prefix_append, transact_prefix_segment_boundary]

/-- Ordered whole-history slices subdivide with their natural requested indices,
not a cap or a guessed length-normalized partition. -/
theorem transact_prefix_segment_subdivide_history (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (start left right : Nat) :
    ((transactPrefix w frames).2.drop start).take (left + right) =
      ((transactPrefix w frames).2.drop start).take left ++
        ((transactPrefix w frames).2.drop (start + left)).take right := by
  rw [List.take_add, List.drop_drop]

/-- Actual observed adjacent slices retain the mapped ordered successes/errors.
This forward transport does not need observer injectivity. -/
theorem transact_prefix_segment_subdivide_observe {β : Type} (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (start left right : Nat) (observation : α → β) :
    (((transactPrefix w (frames.map (fun frame => observeTransactionFrame frame observation))).2.drop start).take (left + right)) =
      (((transactPrefix w frames).2.drop start).take left).map (fun result => result.map observation) ++
      (((transactPrefix w frames).2.drop (start + left)).take right).map (fun result => result.map observation) := by
  rw [transact_prefix_segment_observe_history, transact_prefix_segment_subdivide_history, List.map_append]

/-- Reflect BOTH labelled component histories under injectivity. Equality of only
their concatenation cannot identify partition boundaries or arbitrary Worlds. -/
theorem transact_prefix_partition_reflect_iff {β : Type} (w : World contracts)
    (frames : List (TransactionFrame contracts α)) (start left right : Nat)
    (observation : α → β) (injective : ∀ x y, observation x = observation y → x = y)
    (first second : List (TRes α)) :
    ((((transactPrefix w (frames.map (fun frame => observeTransactionFrame frame observation))).2.drop start).take left) =
      first.map (fun result => result.map observation) ∧
     (((transactPrefix w (frames.map (fun frame => observeTransactionFrame frame observation))).2.drop (start + left)).take right) =
      second.map (fun result => result.map observation)) ↔
    (((transactPrefix w frames).2.drop start).take left = first ∧
      ((transactPrefix w frames).2.drop (start + left)).take right = second) :=
  and_congr (transact_prefix_segment_observe_reflect_iff w frames start left observation injective first)
    (transact_prefix_segment_observe_reflect_iff w frames (start + left) right observation injective second)

#print axioms transact_prefix_segment_subdivide
#print axioms transact_prefix_segment_subdivide_history
#print axioms transact_prefix_segment_subdivide_observe
#print axioms transact_prefix_partition_reflect_iff

#print axioms result_observe_eq_iff
#print axioms history_observe_eq_iff
#print axioms transact_prefix_observe_reflect_iff
#print axioms transact_prefix_segment_observe_history
#print axioms transact_prefix_segment_observe_complete
#print axioms transact_prefix_segment_observe_reflect_iff

#print axioms transact_prefix_segment_history
#print axioms transact_prefix_segment_boundary
#print axioms transact_prefix_segment_complete
#print axioms transact_prefix_segment_index_bound
#print axioms transact_prefix_segment_ok_iff
#print axioms transact_prefix_segment_error_iff

#print axioms transact_prefix_success_of_index
#print axioms transact_prefix_index_ok_iff

#print axioms transact_prefix_failure_of_index
#print axioms transact_prefix_index_error_iff

#print axioms transact_prefix_index_observe

#print axioms transact_prefix_take_drop
#print axioms transact_prefix_take_history
#print axioms transact_prefix_drop_history
#print axioms transact_prefix_index_bound
#print axioms transact_prefix_index
#print axioms transact_prefix_index_success
#print axioms transact_prefix_index_failure

#print axioms transact_step_history
#print axioms transact_prefix_nil
#print axioms transact_prefix_cons
#print axioms transact_prefix_append
#print axioms transact_prefix_snoc
#print axioms transact_prefix_singleton
#print axioms transact_prefix_length
#print axioms transact_output_normalized
#print axioms transact_input_reset
#print axioms transact_prefix_normalized
#print axioms transact_prefix_initial_reset
#print axioms transact_prefix_commit_snoc
#print axioms transact_prefix_failure_snoc
#print axioms transact_prefix_failure_suffix

#print axioms transact_prefix_observe
end Solidity.Lowering.V08
