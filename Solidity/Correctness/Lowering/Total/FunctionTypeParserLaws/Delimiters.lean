import Solidity.Syntax.Raw
import Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws.Strings

/-!
# Function-signature parser laws: the two delimiter scanners

`fnParts?` finds the `)` closing the parameters with its local `close`
(depth over `(` `[` / `)` `]`) and splits lists with `splitTop ','` (depth
over `{` `(` `[` / `}` `)` `]`). Both subtract with truncation, so their
depths are additive only on text that never closes below its starting depth.

`splitScan` and `closeScan` follow the two depth counts and refuse exactly
what breaks additivity or a boundary: a closing bracket at depth `0`, and for
`splitScan` a comma at depth `0`. On text they accept, the real scanners step
over it (`splitTop_scan`, `close_scan`); so a comma-joined list of accepted
components splits back (`splitTop_join`) and is closed by the next `)`
(`close_join`). `plain` text (no bracket, no comma) is accepted at any depth.
-/
namespace Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws

open Solidity.Semantics.StructEnc (splitTop)
open Str (sepJoin)

/-- `splitTop`'s depth after `c`. -/
def sdepth (d : Nat) (c : Char) : Nat :=
  if c == '{' || c == '(' || c == '[' then d + 1
  else if c == '}' || c == ')' || c == ']' then d - 1 else d

/-- `fnParts?.close`'s depth after `c`. -/
def cdepth (d : Nat) (c : Char) : Nat :=
  if c == '(' || c == '[' then d + 1 else if c == ')' || c == ']' then d - 1 else d

/-- The depth `splitTop ','` reaches over `l` from depth `d`; `none` at a
comma or a closing bracket met at depth `0`. -/
def splitScan : Nat → List Char → Option Nat
  | d, [] => some d
  | d, c :: cs =>
    if d == 0 && (c == ',' || c == '}' || c == ')' || c == ']') then none
    else splitScan (sdepth d c) cs

/-- The depth `fnParts?.close` reaches over `l` from depth `d`; `none` at a
closing bracket met at depth `0`. -/
def closeScan : Nat → List Char → Option Nat
  | d, [] => some d
  | d, c :: cs =>
    if d == 0 && (c == ')' || c == ']') then none else closeScan (cdepth d c) cs

/-- No bracket and no comma. -/
def plain (l : List Char) : Bool :=
  l.all fun c => !(c == '{' || c == '}' || c == '(' || c == ')' || c == '[' || c == ']' || c == ',')

/-! ## `splitTop` -/

theorem splitTop_scan {d d' : Nat} {c : List Char} (acc rest : List Char)
    (h : splitScan d c = some d') :
    splitTop ',' d acc (c ++ rest) = splitTop ',' d' (c.reverse ++ acc) rest := by
  induction c generalizing d acc with
  | nil => simp [splitScan] at h; simp [h]
  | cons x c ih =>
    simp only [splitScan] at h
    split at h
    · cases h
    · rename_i hx
      have nc : ¬ ((d == 0 && x == ',') = true) := by
        intro e; apply hx; simp at e ⊢; simp [e.1, e.2]
      have := ih (x :: acc) h
      simp only [List.cons_append, splitTop, nc, Bool.false_eq_true, if_false]
      simpa [sdepth] using this

theorem splitScan_append {d d' : Nat} {a : List Char} (b : List Char)
    (h : splitScan d a = some d') : splitScan d (a ++ b) = splitScan d' b := by
  induction a generalizing d with
  | nil => simp [splitScan] at h; simp [h]
  | cons x a ih =>
    simp only [splitScan] at h
    split at h
    · cases h
    · rename_i hx; simp only [List.cons_append, splitScan, if_neg hx]; exact ih h

theorem splitScan_lift {d d' : Nat} {c : List Char} (k : Nat)
    (h : splitScan d c = some d') : splitScan (d + k) c = some (d' + k) := by
  induction c generalizing d with
  | nil => simp [splitScan] at h; simp [splitScan, h]
  | cons x c ih =>
    simp only [splitScan] at h
    split at h
    · cases h
    · rename_i hx
      have hk : ¬ ((d + k == 0 && (x == ',' || x == '}' || x == ')' || x == ']')) = true) := by
        intro e; apply hx; simp at e ⊢; exact ⟨e.1.1, e.2⟩
      have e : sdepth (d + k) x = sdepth d x + k := by
        simp only [sdepth]
        split
        · omega
        · split
          · rename_i hc
            have : d ≠ 0 := by
              intro d0; apply hx; simp at hc ⊢
              rcases hc with (h | h) | h <;> simp [d0, h]
            omega
          · rfl
      simp only [splitScan, if_neg hk, e]
      exact ih h

theorem splitScan_plain {l : List Char} (h : plain l = true) (d : Nat) :
    splitScan d l = some d := by
  induction l generalizing d with
  | nil => rfl
  | cons x l ih =>
    simp only [plain, List.all_cons, Bool.and_eq_true] at h
    have hx := h.1
    have e : sdepth d x = d := by
      simp only [sdepth]; simp at hx; simp [hx]
    have n : ¬ ((d == 0 && (x == ',' || x == '}' || x == ')' || x == ']')) = true) := by
      simp at hx ⊢; simp [hx]
    simp only [splitScan, if_neg n, e]
    exact ih h.2 d

/-- A comma-joined list scans from any positive depth when its components
scan from `0` (a comma is then no boundary). -/
theorem splitScan_join {cs : List (List Char)} (h : ∀ c ∈ cs, splitScan 0 c = some 0) (d : Nat) :
    splitScan (d + 1) (sepJoin [','] cs) = some (d + 1) := by
  have one : ∀ c ∈ cs, splitScan (d + 1) c = some (d + 1) := fun c hc => by
    simpa using splitScan_lift (d + 1) (h c hc)
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    cases cs with
    | nil => simpa [sepJoin] using one a (by simp)
    | cons b r =>
      have ha := one a (by simp)
      have ih' := ih (fun c hc => h c (by simp [hc])) (fun c hc => one c (by simp [hc]))
      simp only [sepJoin, List.append_assoc]
      rw [splitScan_append _ ha]
      simpa [splitScan, sdepth] using ih'

/-- A comma-joined nonempty list of components `splitScan` accepts splits
back into exactly those components. -/
theorem splitTop_join {cs : List (List Char)} (h : ∀ c ∈ cs, splitScan 0 c = some 0)
    (ne : cs ≠ []) : splitTop ',' 0 [] (sepJoin [','] cs) = cs := by
  induction cs with
  | nil => exact absurd rfl ne
  | cons a cs ih =>
    have ha := h a (by simp)
    cases cs with
    | nil =>
      have := splitTop_scan [] [] ha
      simpa [sepJoin, splitTop] using this
    | cons b r =>
      have ih' := ih (fun c hc => h c (by simp [hc])) (by simp)
      have := splitTop_scan [] (',' :: sepJoin [','] (b :: r)) ha
      simp only [sepJoin, List.append_assoc, List.singleton_append]
      rw [this]
      simp [splitTop, ih']

/-! ## `fnParts?.close` -/

theorem close_scan {d d' : Nat} {c : List Char} (acc rest : List Char)
    (h : closeScan d c = some d') :
    fnParts?.close d acc (c ++ rest) = fnParts?.close d' (c.reverse ++ acc) rest := by
  induction c generalizing d acc with
  | nil => simp [closeScan] at h; simp [h]
  | cons x c ih =>
    simp only [closeScan] at h
    split at h
    · cases h
    · rename_i hx
      have nc : ¬ ((x == ')' && d == 0) = true) := by
        intro e; apply hx; simp at e ⊢; simp [e.1, e.2]
      have := ih (x :: acc) h
      simp only [List.cons_append, fnParts?.close, nc, Bool.false_eq_true, if_false]
      simpa [cdepth] using this

theorem closeScan_append {d d' : Nat} {a : List Char} (b : List Char)
    (h : closeScan d a = some d') : closeScan d (a ++ b) = closeScan d' b := by
  induction a generalizing d with
  | nil => simp [closeScan] at h; simp [h]
  | cons x a ih =>
    simp only [closeScan] at h
    split at h
    · cases h
    · rename_i hx; simp only [List.cons_append, closeScan, if_neg hx]; exact ih h

theorem closeScan_lift {d d' : Nat} {c : List Char} (k : Nat)
    (h : closeScan d c = some d') : closeScan (d + k) c = some (d' + k) := by
  induction c generalizing d with
  | nil => simp [closeScan] at h; simp [closeScan, h]
  | cons x c ih =>
    simp only [closeScan] at h
    split at h
    · cases h
    · rename_i hx
      have hk : ¬ ((d + k == 0 && (x == ')' || x == ']')) = true) := by
        intro e; apply hx; simp at e ⊢; exact ⟨e.1.1, e.2⟩
      have e : cdepth (d + k) x = cdepth d x + k := by
        simp only [cdepth]
        split
        · omega
        · split
          · rename_i hc
            have : d ≠ 0 := by
              intro d0; apply hx; simp at hc ⊢; simp [d0, hc]
            omega
          · rfl
      simp only [closeScan, if_neg hk, e]
      exact ih h

theorem closeScan_plain {l : List Char} (h : plain l = true) (d : Nat) :
    closeScan d l = some d := by
  induction l generalizing d with
  | nil => rfl
  | cons x l ih =>
    simp only [plain, List.all_cons, Bool.and_eq_true] at h
    have hx := h.1
    have e : cdepth d x = d := by
      simp only [cdepth]; simp at hx; simp [hx]
    have n : ¬ ((d == 0 && (x == ')' || x == ']')) = true) := by
      simp at hx ⊢; simp [hx]
    simp only [closeScan, if_neg n, e]
    exact ih h.2 d

/-- A comma-joined list scans from any depth when its components scan from `0`. -/
theorem closeScan_join {cs : List (List Char)} (h : ∀ c ∈ cs, closeScan 0 c = some 0) (d : Nat) :
    closeScan d (sepJoin [','] cs) = some d := by
  have one : ∀ c ∈ cs, closeScan d c = some d := fun c hc => by
    simpa using closeScan_lift d (h c hc)
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    cases cs with
    | nil => simpa [sepJoin] using one a (by simp)
    | cons b r =>
      have ha := one a (by simp)
      have ih' := ih (fun c hc => h c (by simp [hc])) (fun c hc => one c (by simp [hc]))
      simp only [sepJoin, List.append_assoc]
      rw [closeScan_append _ ha]
      simpa [closeScan, cdepth] using ih'

/-- Text `closeScan` accepts back to depth `0` is closed by the `)` after it. -/
theorem close_join {p : List Char} (rest : List Char) (h : closeScan 0 p = some 0) :
    fnParts?.close 0 [] (p ++ ')' :: rest) = some (p, rest) := by
  rw [close_scan [] _ h]
  simp [fnParts?.close]

end Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws
