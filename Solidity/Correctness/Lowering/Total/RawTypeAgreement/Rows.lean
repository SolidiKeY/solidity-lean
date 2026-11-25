import Solidity.Correctness.Lowering.Total.StructRows

/-!
# Generated width rows at an enclosing key

`elabTyW` keys a type's rows by their path below it; `rebase` places them at an enclosing
key. First lookup (`lookupBy_rebase`), nesting (`rebase_nest`), the prefix of every key read
(`readTy_data`), a mapping's key and value rows apart (`Agree.keyRows`, `Agree.valueRows`), and
surrounding rows that are not read (`agree_surround`).
-/
namespace Solidity.Correctness.Lowering.Total.RawTypeAgreement

open Solidity.Semantics (lookupBy)
open ReferenceDecode (leafKeys readTy readRef)
open StructRows (Agree)

/-- Rows keyed by their path below a position, placed at the enclosing key. -/
def rebase (key : Name) (ws : List (String × Nat)) : List (Name × Nat) :=
  ws.map fun r => (key ++ r.1, r.2)

theorem append_left_inj {key a b : String} : key ++ a = key ++ b ↔ a = b :=
  ⟨fun h => String.ext (List.append_cancel_left (as := key.data)
    (by simpa only [String.data_append] using congrArg String.data h)), fun h => h ▸ rfl⟩

/-- **First lookup below a key**: a rebased table is read as the generated one. -/
theorem lookupBy_rebase (key p : String) : ∀ ws : List (String × Nat),
    lookupBy (key ++ p) (rebase key ws) = lookupBy p ws
  | [] => rfl
  | r :: ws => by
      show (if key ++ p = key ++ r.1 then some r.2 else lookupBy (key ++ p) (rebase key ws)) =
        if p = r.1 then some r.2 else lookupBy p ws
      rw [lookupBy_rebase key p ws]
      by_cases e : p = r.1
      · rw [if_pos e, if_pos (append_left_inj.2 e)]
      · rw [if_neg e, if_neg fun h => e (append_left_inj.1 h)]

/-- **Row prefix**: the rows of a nested position are the rows at the nested key. -/
theorem rebase_nest (key q : String) (ws : List (String × Nat)) :
    rebase key (ws.map fun (k, n) => (q ++ k, n)) = rebase (key ++ q) ws := by
  simp [rebase, List.map_map, Function.comp_def, String.append_assoc]

theorem rebase_append (key : Name) (a b : List (String × Nat)) :
    rebase key (a ++ b) = rebase key a ++ rebase key b := List.map_append

theorem lookupBy_append {α : Type} (k : Name) : ∀ l₁ l₂ : List (Name × α),
    lookupBy k (l₁ ++ l₂) = (lookupBy k l₁).or (lookupBy k l₂)
  | [], _ => rfl
  | (k', v) :: l₁, l₂ => by
    rw [List.cons_append, lookupBy, lookupBy]
    by_cases e : k = k'
    · rw [if_pos e, if_pos e]; rfl
    · rw [if_neg e, if_neg e]; exact lookupBy_append k l₁ l₂

theorem lookupBy_absent {α : Type} {k : Name} : ∀ {l : List (Name × α)},
    (∀ r ∈ l, r.1 ≠ k) → lookupBy k l = none
  | [], _ => rfl
  | (k', v) :: l, h => by
    rw [lookupBy, if_neg fun e => h (k', v) List.mem_cons_self e.symm]
    exact lookupBy_absent fun r mr => h r (List.mem_cons_of_mem _ mr)

theorem leafKeys_data {key k : Name} (h : k ∈ leafKeys key) : ∃ suf, k.data = key.data ++ suf := by
  simp only [leafKeys, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> first | exact ⟨_, String.data_append ..⟩ | exact ⟨[], by simp⟩

mutual
/-- **Row prefix of the keys read**: each extends the position. -/
theorem readTy_data : (T : Ty) → (key : Name) → {k : Name} → k ∈ readTy key T →
    ∃ suf, k.data = key.data ++ suf
  | .prim _, _, _, h => leafKeys_data (by simpa only [readTy] using h)
  | .ref R, key, _, h => readRef_data R key (by simpa only [readTy] using h)
theorem readRef_data : (R : RefTy) → (key : Name) → {k : Name} → k ∈ readRef key R →
    ∃ suf, k.data = key.data ++ suf
  | .struct _, _, _, h => by simp [readRef] at h
  | .array T, key, _, h | .fixed T _, key, _, h => by
      obtain ⟨suf, eq⟩ := readTy_data T (key ++ "[]") (by simpa only [readRef] using h)
      exact ⟨'[' :: ']' :: suf, by simpa using eq⟩
  | .mapping _ V, key, _, h => by
      simp only [readRef, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨suf, eq⟩ := leafKeys_data h; exact ⟨'{' :: '}' :: suf, by simpa using eq⟩
      · obtain ⟨suf, eq⟩ := readTy_data V (key ++ "[]") h; exact ⟨'[' :: ']' :: suf, by simpa using eq⟩
end

/-- Rows rebased at one nested key are not read at another that parts from it. -/
theorem lookupBy_apart {q q' k : Name} (sep : ∀ a b : List Char, q.data ++ a ≠ q'.data ++ b)
    (hk : ∃ suf, k.data = q.data ++ suf) (ws : List (String × Nat)) :
    lookupBy k (rebase q' ws) = none := by
  obtain ⟨suf, eq⟩ := hk
  refine lookupBy_absent fun r mr e => ?_
  obtain ⟨r', -, rfl⟩ := List.mem_map.1 mr
  exact sep suf r'.1.data (by rw [← eq, ← e]; simp)

theorem key_value_apart (key : Name) (a b : List Char) :
    (key ++ "{}").data ++ a ≠ (key ++ "[]").data ++ b := by simp [List.append_assoc]

variable {key : Name} {K : PrimTy} {V : Ty} {kw vw : List (String × Nat)} {widths : List (Name × Nat)}

/-- The key rows of a mapping, out of its generated rows. -/
theorem Agree.keyRows (h : Agree (readRef key (.mapping K V)) (rebase key (kw.map (fun (k, n) =>
      ("{}" ++ k, n)) ++ vw.map fun (k, n) => ("[]" ++ k, n))) widths) :
    Agree (leafKeys (key ++ "{}")) (rebase (key ++ "{}") kw) widths := fun k hk => by
  rw [← h k (by simp only [readRef, List.mem_append]; exact .inl hk), rebase_append,
    lookupBy_append, rebase_nest, rebase_nest,
    lookupBy_apart (key_value_apart key) (leafKeys_data hk), Option.or_none]

/-- The value rows of a mapping, out of its generated rows. -/
theorem Agree.valueRows (h : Agree (readRef key (.mapping K V)) (rebase key (kw.map (fun (k, n) =>
      ("{}" ++ k, n)) ++ vw.map fun (k, n) => ("[]" ++ k, n))) widths) :
    Agree (readTy (key ++ "[]") V) (rebase (key ++ "[]") vw) widths := fun k hk => by
  rw [← h k (by simp only [readRef, List.mem_append]; exact .inr hk), rebase_append,
    lookupBy_append, rebase_nest, rebase_nest,
    lookupBy_apart (fun a b e => key_value_apart key b a e.symm) (readTy_data V _ hk), Option.none_or]

/-- **Extension**: surrounding rows whose keys the spelling does not read leave the generated
rows the ones read. -/
theorem agree_surround {keys : List Name} {rows pre post : List (Name × Nat)}
    (free : ∀ r ∈ pre ++ post, r.1 ∉ keys) : Agree keys rows (pre ++ rows ++ post) := fun k hk => by
  have none : ∀ l : List (Name × Nat), (∀ r ∈ l, r ∈ pre ++ post) → lookupBy k l = none :=
    fun l sub => lookupBy_absent fun r mr e => free r (sub r mr) (e ▸ hk)
  rw [lookupBy_append, lookupBy_append, none pre fun r mr => List.mem_append_left _ mr,
    none post fun r mr => List.mem_append_right _ mr, Option.none_or, Option.or_none]

end Solidity.Correctness.Lowering.Total.RawTypeAgreement
