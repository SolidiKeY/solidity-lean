import Solidity.Frontend.StatementGrammarH28.BalanceAtoms

/-! H31 local leading-token invariants. These observe existing yielded tokens;
no expression uniqueness or producer API change is introduced. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- Fixed statement starts other than contextual identifier revert. -/
def hardStatementToken : Tok → Bool
  | .punct .lbrace => true
  | .kw .if_ | .kw .for_ | .kw .while_ | .kw .do_ | .kw .continue_ | .kw .break_
  | .kw .try_ | .kw .return_ | .kw .emit | .kw .assembly => true
  | _ => false

/-- An inhabited token prefix whose first token cannot be a hard statement start. -/
def SafeStart (ts : List Tok) : Prop :=
  ∃ t rest, ts = t :: rest ∧ hardStatementToken t = false

theorem safe_start_append {xs : List Tok} (h : SafeStart xs) (ys : List Tok) :
    SafeStart (xs ++ ys) := by
  obtain ⟨t, rest, he, ht⟩ := h
  subst xs
  exact ⟨t, rest ++ ys, rfl, ht⟩

theorem safe_start_fixed (t : Tok) (rest : List Tok) (h : hardStatementToken t = false) :
    SafeStart (t :: rest) := ⟨t, rest, rfl, h⟩

theorem safe_start_map {α : Type} (f : α → Tok) (xs : List α) (hn : xs ≠ [])
    (hf : ∀ x, hardStatementToken (f x) = false) : SafeStart (xs.map f) := by
  cases xs with
  | nil => exact False.elim (hn rfl)
  | cons x xs => exact ⟨f x, xs.map f, rfl, hf x⟩

theorem lift_post {α : Type} (o : Option α) (P : α → Prop)
    (hp : ∀ a, o = some a → P a) : PrEnsures (Pr.lift o) P := by
  intro L a M he
  change o.map (fun v => (v, L)) = some (a, M) at he
  obtain ⟨v, hv, eq⟩ := Option.map_eq_some_iff.mp he
  have values : v = a := congrArg Prod.fst eq
  subst a
  exact hp v hv

theorem chunks_cons_nonempty (bs : Bytes) (n : Nat) (ns : List Nat) (cs : List Bytes)
    (h : chunks bs (n :: ns) = some cs) : cs ≠ [] := by
  rw [chunks] at h
  obtain ⟨tail, ht, he⟩ := Option.bind_eq_some_iff.mp h
  split at he
  · have eq : bs.take n :: tail = cs := Option.some.inj he
    rw [← eq]
    intro bad
    cases bad
  · cases he

theorem fragsP_safe_start (mk : Bytes → Tok) (bs : Bytes)
    (hm : ∀ bytes, hardStatementToken (mk bytes) = false) :
    PrEnsures (fragsP mk bs) SafeStart := by
  unfold fragsP
  apply ensures_bind (P := SafeStart)
  intro choice
  cases choice with
  | attrs _ => exact ensures_lift_none _
  | layoutFirst _ => exact ensures_lift_none _
  | frags lens =>
    cases lens with
    | nil => exact ensures_lift_none _
    | cons n ns =>
      apply ensures_bind_checked _ _ (fun cs : List Bytes => cs ≠ []) SafeStart
        (lift_post _ _ (fun cs hc => chunks_cons_nonempty bs n ns cs hc))
      intro cs hcs
      exact ensures_pure _ SafeStart (safe_start_map mk cs hcs hm)

theorem litP_safe_start (l : Lit) : PrEnsures (litP l) SafeStart := by
  cases l with
  | str b => exact fragsP_safe_start _ _ (fun _ => rfl)
  | hexStr b => exact fragsP_safe_start _ _ (fun _ => rfl)
  | unicodeStr b => exact fragsP_safe_start _ _ (fun _ => rfl)
  | bool b => exact ensures_pure _ SafeStart ⟨_, [], rfl, rfl⟩
  | num n => exact ensures_pure _ SafeStart ⟨_, [], rfl, rfl⟩

theorem elem_safe_start (e : Elem) : SafeStart e.toks := by
  cases e <;> exact ⟨_, _, rfl, rfl⟩

theorem path_safe_start (p : IdPath) : SafeStart p.toks := ⟨_, _, rfl, rfl⟩

theorem prefix_safe_start (op : PrefixOp) : SafeStart op.punct := by
  cases op <;> exact ⟨_, _, rfl, rfl⟩

#print axioms safe_start_append
#print axioms safe_start_fixed
#print axioms safe_start_map
#print axioms lift_post
#print axioms chunks_cons_nonempty
#print axioms fragsP_safe_start
#print axioms litP_safe_start
#print axioms elem_safe_start
#print axioms path_safe_start
#print axioms prefix_safe_start
end Solidity.Frontend.StatementGrammarH28
