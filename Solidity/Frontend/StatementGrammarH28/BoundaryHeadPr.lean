import Solidity.Frontend.StatementGrammarH28.HeadPr

/-! H31 proof-only exclusion of grammar continuation tokens from atom heads.
No original head theorem, producer API or expression uniqueness premise changes. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def boundaryToken : Tok → Bool
  | .kw .else_ | .kw .catch_ | .kw .unchecked => true
  | _ => false

def BoundaryStart (ts : List Tok) : Prop :=
  ∃ t rest, ts = t :: rest ∧ boundaryToken t = false

theorem boundary_start_append {xs : List Tok} (h : BoundaryStart xs) (ys : List Tok) :
    BoundaryStart (xs ++ ys) := by
  obtain ⟨t, rest, he, ht⟩ := h
  subst xs
  exact ⟨t, rest ++ ys, rfl, ht⟩

theorem boundary_start_fixed (t : Tok) (rest : List Tok) (h : boundaryToken t = false) :
    BoundaryStart (t :: rest) := ⟨t, rest, rfl, h⟩

theorem boundary_start_map {α : Type} (f : α → Tok) (xs : List α) (hn : xs ≠ [])
    (hf : ∀ x, boundaryToken (f x) = false) : BoundaryStart (xs.map f) := by
  cases xs with
  | nil => exact False.elim (hn rfl)
  | cons x xs => exact ⟨f x, xs.map f, rfl, hf x⟩

theorem fragsP_boundary_start (mk : Bytes → Tok) (bs : Bytes)
    (hm : ∀ bytes, boundaryToken (mk bytes) = false) :
    PrEnsures (fragsP mk bs) BoundaryStart := by
  unfold fragsP
  apply ensures_bind (P := BoundaryStart)
  intro choice
  cases choice with
  | attrs _ => exact ensures_lift_none _
  | layoutFirst _ => exact ensures_lift_none _
  | frags lens =>
    cases lens with
    | nil => exact ensures_lift_none _
    | cons n ns =>
      apply ensures_bind_checked _ _ (fun cs : List Bytes => cs ≠ []) BoundaryStart
        (lift_post _ _ (fun cs hc => chunks_cons_nonempty bs n ns cs hc))
      intro cs hcs
      exact ensures_pure _ BoundaryStart (boundary_start_map mk cs hcs hm)

theorem litP_boundary_start (l : Lit) : PrEnsures (litP l) BoundaryStart := by
  cases l with
  | str b => exact fragsP_boundary_start _ _ (fun _ => rfl)
  | hexStr b => exact fragsP_boundary_start _ _ (fun _ => rfl)
  | unicodeStr b => exact fragsP_boundary_start _ _ (fun _ => rfl)
  | bool b => exact ensures_pure _ BoundaryStart ⟨_, [], rfl, rfl⟩
  | num n => exact ensures_pure _ BoundaryStart ⟨_, [], rfl, rfl⟩

theorem elem_boundary_start (e : Elem) : BoundaryStart e.toks := by
  cases e <;> exact ⟨_, _, rfl, rfl⟩

theorem path_boundary_start (p : IdPath) : BoundaryStart p.toks := ⟨_, _, rfl, rfl⟩

theorem prefix_boundary_start (op : PrefixOp) : BoundaryStart op.punct := by
  cases op <;> exact ⟨_, _, rfl, rfl⟩

end Solidity.Frontend.StatementGrammarH28
