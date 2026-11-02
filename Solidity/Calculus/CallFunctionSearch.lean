import Solidity.Calculus.CallFunctionPlan
import Solidity.Calculus.AllLeft

/-! # Conservative automatic candidates for checked call-family plans
Candidate construction remains intrinsic. It proposes typed subterms and
locals; the existing exact checked plan producer is the only acceptance path.
This module does not change default dispatch or any old fallback verdict.
-/
namespace Solidity.CallFunctionSearch
open CallFunctionPlan
variable {C : Contract} {Γ : Ctx}

/-- Internal optional-search width, not a user option or semantic exclusion. -/
def proposalCap : Nat := 32

/-- A subterm is a candidate only at its actual intrinsic UInt sort. -/
def uintAt : {s : Srt} → Tm C Γ s → List (Tm C Γ (.val .uint))
  | .val .uint, t => [t]
  | _, _ => []

/-- Executable twin of the intrinsic term recursor below. -/
def subtermsM : {s : Srt} → Tm C Γ s → List (Tm C Γ (.val .uint))
  | _, .pvV i => uintAt (.pvV i)
  | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .pvZ _ => []
  | _, .netOf _ a => subtermsM a
  | _, .app0 o => uintAt (.app0 o)
  | _, .app1 o a => (subtermsM a ++ uintAt (.app1 o a)).take proposalCap
  | _, .app2 o a b => (subtermsM a ++ subtermsM b ++ uintAt (.app2 o a b)).take proposalCap
  | _, .app3 o a b c =>
    (subtermsM a ++ subtermsM b ++ subtermsM c ++ uintAt (.app3 o a b c)).take proposalCap

/-- Small inside-first typed proposals, written by the intrinsic recursor. -/
@[implemented_by subtermsM]
def subterms {s : Srt} (t : Tm C Γ s) : List (Tm C Γ (.val .uint)) :=
  Tm.rec (motive := fun _ _ => List (Tm C Γ (.val .uint)))
    (fun i => uintAt (.pvV i)) (fun _ => []) (fun _ => []) (fun _ => [])
    (fun _ _ ih => ih)
    (fun o => uintAt (.app0 o))
    (fun o a ih => (ih ++ uintAt (.app1 o a)).take proposalCap)
    (fun o a b iha ihb => (iha ++ ihb ++ uintAt (.app2 o a b)).take proposalCap)
    (fun o a b c iha ihb ihc =>
      (iha ++ ihb ++ ihc ++ uintAt (.app3 o a b c)).take proposalCap)
    (fun _ => []) t

/-- The executable proposal walk is exactly its intrinsic definition. -/
theorem subterms_eq {s : Srt} (t : Tm C Γ s) : subterms t = subtermsM t := by
  induction t with
  | pvV i => rfl
  | pvP i => rfl
  | pvS i => rfl
  | pvI i => rfl
  | pvZ i => rfl
  | app0 o => rfl
  | netOf i a ih => exact ih
  | app1 o a ih =>
    change (subterms a ++ uintAt (.app1 o a)).take proposalCap = _
    rw [ih]
    rfl
  | app2 o a b iha ihb =>
    change (subterms a ++ subterms b ++ uintAt (.app2 o a b)).take proposalCap = _
    rw [iha, ihb]
    rfl
  | app3 o a b c iha ihb ihc =>
    change (subterms a ++ subterms b ++ subterms c ++ uintAt (.app3 o a b c)).take proposalCap = _
    rw [iha, ihb, ihc]
    rfl

/-- One intrinsic subterm contributes at most one UInt proposal. -/
theorem uintAt_length {s : Srt} (t : Tm C Γ s) : (uintAt t).length ≤ 1 := by
  cases s
  case val p =>
    cases p with
    | bool => exact Nat.zero_le 1
    | uint => exact Nat.le_refl 1
    | int => exact Nat.zero_le 1
  all_goals exact Nat.zero_le 1

/-- The proposal cap limits retained entries, not the recursive traversal,
preliminary variable list, transient allocations or search/checking time. -/
theorem subterms_length {s : Srt} (t : Tm C Γ s) :
    (subterms t).length ≤ proposalCap := by
  induction t with
  | pvV i => exact Nat.le_trans (uintAt_length (.pvV i)) (by decide : 1 ≤ proposalCap)
  | pvP i => exact Nat.zero_le _
  | pvS i => exact Nat.zero_le _
  | pvI i => exact Nat.zero_le _
  | pvZ i => exact Nat.zero_le _
  | netOf i a ih => exact ih
  | app0 o => exact Nat.le_trans (uintAt_length (Γ := Γ) (.app0 o)) (by decide : 1 ≤ proposalCap)
  | app1 o a ih =>
    change ((subterms a ++ uintAt (.app1 o a)).take proposalCap).length ≤ _
    rw [List.length_take]
    exact Nat.min_le_left _ _
  | app2 o a b iha ihb =>
    change ((subterms a ++ subterms b ++ uintAt (.app2 o a b)).take proposalCap).length ≤ _
    rw [List.length_take]
    exact Nat.min_le_left _ _
  | app3 o a b c iha ihb ihc =>
    change ((subterms a ++ subterms b ++ subterms c ++ uintAt (.app3 o a b c)).take proposalCap).length ≤ _
    rw [List.length_take]
    exact Nat.min_le_left _ _

/-- Replace only the proposed old input position by the fresh intrinsic input;
all other original locals are weakened, never substituted into one another. -/
def abstract? (input : Idx Γ (.val .uint)) (candidate : Tm C Γ (.val .uint)) :
    Option (Tm C (.val .uint :: Γ) (.val .uint)) :=
  candidate.substE (SEnv.set input (.pvV .here, false)
    (SEnv.idAt Γ (fun i => i.there)))

/-- Pure literal/value expressions propose actual UInt input positions using
the existing certified typed position lookup. Others refuse this optional route. -/
def inputs? (out : Tm C Γ (.val .uint)) : Option (List (Idx Γ (.val .uint))) := do
  let vars ← out.litVarsS
  return (vars.filterMap (fun v => Idx.valAt? Γ .uint v.2.toNat)).foldl
    (fun acc i => if acc.any (fun j => j.toNat == i.toNat) then acc else acc ++ [i]) []

/-- Automatic typed proposal selection. Every returned plan is still indexed
by the actual old term and carries the checked exact expansion equation.
No claim of cheap checking or automatic default integration is made here. -/
def search? (out : Tm C Γ (.val .uint)) : Option (Plan out) := Id.run do
  let some inputs := inputs? out | return none
  let candidates := subterms out
  let levels := (List.range (Nat.log2 out.size + 1)).reverse
  for input in inputs.take proposalCap do
    for candidate in candidates do
      let some base := abstract? input candidate | continue
      if base.size ≤ 1 then continue
      for level in levels do
        if level = 0 then continue
        if let some plan := checked? base level input out then
          return some plan
  return none

end Solidity.CallFunctionSearch
