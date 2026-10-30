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
