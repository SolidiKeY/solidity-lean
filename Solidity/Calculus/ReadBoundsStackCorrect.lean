import Solidity.Calculus.ReadBounds

/-! Guards the stack-safe ReadBounds implementation against changed remaining
fuel, traversal or tree-versus-DAG accounting. General equalities retain the
existing counter specifications without new axioms or premises. This proof
module is separate from the ordinary compiled traversal. -/
namespace Solidity.Decide
variable {C : Contract}

private noncomputable def ReadBoundsStack.Task.eval : ReadBoundsStack.Task C → Nat → Option Nat
  | .term t => t.fitsM
  | .formula φ => φ.fitsM

private noncomputable def fitsTasks : List (ReadBoundsStack.Task C) → Nat → Option Nat
  | [], n => some n
  | task :: rest, n => (task.eval n).bind (fitsTasks rest)

private theorem fitsTasks_append (xs ys : List (ReadBoundsStack.Task C)) (n : Nat) :
    fitsTasks (xs ++ ys) n = (fitsTasks xs n).bind (fitsTasks ys) := by
  induction xs generalizing n with
  | nil => rfl
  | cons task rest ih =>
    change (task.eval n).bind (fitsTasks (rest ++ ys)) =
      ((task.eval n).bind (fitsTasks rest)).bind (fitsTasks ys)
    rw [Option.bind_assoc]
    exact congrArg (fun f => (task.eval n).bind f) (funext ih)

private theorem ReadBoundsStack.Task.eval_zero (task : ReadBoundsStack.Task C) : task.eval 0 = none := by
  cases task with
  | term t => cases t <;> rfl
  | formula φ => cases φ <;> rfl

private theorem ReadBoundsStack.Task.eval_succ (task : ReadBoundsStack.Task C) (n : Nat) :
    task.eval (n + 1) = fitsTasks task.children n := by
  cases task with
  | term t =>
    cases t with
    | var | app0 | err => rfl
    | app1 o x | obsW x | obsL x | obsH x =>
      change x.fitsM n = (x.fitsM n).bind some
      exact (Option.bind_fun_some _).symm
    | app2 o x y | index it x y | seq x y | orElse x y =>
      change (x.fitsM n).bind y.fitsM =
        (x.fitsM n).bind (fun m => (y.fitsM m).bind some)
      simp only [Option.bind_fun_some]
    | app3 o x y z =>
      change ((x.fitsM n).bind y.fitsM).bind z.fitsM =
        (x.fitsM n).bind (fun m => (y.fitsM m).bind (fun k => (z.fitsM k).bind some))
      simp only [Option.bind_fun_some, Option.bind_assoc]
    | kite a b t e =>
      change (((a.fitsM n).bind b.fitsM).bind t.fitsM).bind e.fitsM =
        (a.fitsM n).bind (fun m => (b.fitsM m).bind
          (fun k => (t.fitsM k).bind (fun j => (e.fitsM j).bind some)))
      simp only [Option.bind_fun_some, Option.bind_assoc]
  | formula φ =>
    cases φ with
    | tt => rfl
    | eq a b =>
      change (a.fits n).bind b.fits =
        (a.fitsM n).bind (fun m => (b.fitsM m).bind some)
      simp only [LTm.fits_eq_fitsM, Option.bind_fun_some]
    | not φ | all k p φ =>
      change φ.fitsM n = (φ.fitsM n).bind some
      exact (Option.bind_fun_some _).symm
    | and φ ψ | imp φ ψ =>
      change (φ.fitsM n).bind ψ.fitsM =
        (φ.fitsM n).bind (fun m => (ψ.fitsM m).bind some)
      simp only [Option.bind_fun_some]

private theorem ReadBoundsStack.work_eq_tasks (n : Nat) (tasks : List (ReadBoundsStack.Task C)) :
    ReadBoundsStack.work n tasks = fitsTasks tasks n := by
  induction n generalizing tasks with
  | zero =>
    cases tasks with
    | nil => rfl
    | cons task rest =>
      change none = (task.eval 0).bind (fitsTasks rest)
      rw [ReadBoundsStack.Task.eval_zero]
      rfl
  | succ n ih =>
    cases tasks with
    | nil => rfl
    | cons task rest =>
      change ReadBoundsStack.work n (task.children ++ rest) =
        (task.eval (n + 1)).bind (fitsTasks rest)
      rw [ih, fitsTasks_append, ReadBoundsStack.Task.eval_succ]

/-- The compiled tail loop preserves the original remaining-fuel result exactly. -/
theorem LTm.fitsM_eq_fitsStack {s : Srt} (t : LTm C s) : t.fitsM = t.fitsStack := by
  funext n
  change t.fitsM n = ReadBoundsStack.work n [.term t]
  rw [ReadBoundsStack.work_eq_tasks]
  change t.fitsM n = (t.fitsM n).bind some
  exact (Option.bind_fun_some _).symm

/-- Formula traversal preserves node limits, term visits and exhaustion exactly. -/
theorem LFml.fitsM_eq_fitsStack (φ : LFml C) : φ.fitsM = φ.fitsStack := by
  funext n
  change φ.fitsM n = ReadBoundsStack.work n [.formula φ]
  rw [ReadBoundsStack.work_eq_tasks]
  change φ.fitsM n = (φ.fitsM n).bind some
  exact (Option.bind_fun_some _).symm

end Solidity.Decide
