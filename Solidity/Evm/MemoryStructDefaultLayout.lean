import Solidity.Evm.MemoryStructDefault

/-!
# Finite default-allocation sizes

A finite struct expands its fields using the existing decreasing layout rank.
Only primitive dynamic arrays have a child-array representation. Fixed arrays,
reference-element arrays and mappings remain refused, even for empty defaults.
The count includes every child and the parent's minimum one-cell reservation.
-/
namespace Solidity.Evm.Memory
open Semantics

mutual
/-- Cells reserved by a supported finite default; primitives allocate no object. -/
def finiteDefaultCells : Ty → Option Nat
  | .prim _ => some 0
  | .ref (.array (.prim _)) => some 1
  | .ref (.struct s) =>
    (finiteDefaultFieldCells (structDef s)).map (· + structAllocationSize s)
  | .ref (.array (.ref _)) | .ref (.fixed _ _) | .ref (.mapping _ _) => none
termination_by T => (tyRank T, sizeOf T)
decreasing_by
  exact Prod.Lex.left _ _ (structDef_rank_lt _)

/-- Field defaults are allocated left to right before their parent. -/
def finiteDefaultFieldCells : List (Name × Ty) → Option Nat
  | [] => some 0
  | (_, T) :: fs => do
    let head ← finiteDefaultCells T
    let tail ← finiteDefaultFieldCells fs
    pure (head + tail)
termination_by fs => (fieldsRank fs, sizeOf fs)
decreasing_by
  all_goals (apply lex_le_lt
             · simp only [fieldsRank]; omega
             · simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]; omega)
end

/-- Primitive-only layouts retain exactly their existing parent cost. -/
theorem finiteDefaultFieldCells_primitive {fs : List (Name × Ty)}
    (hp : primitiveMembers fs = true) : finiteDefaultFieldCells fs = some 0 := by
  induction fs with
  | nil => rw [finiteDefaultFieldCells]
  | cons fT fs ih =>
    obtain ⟨f, T⟩ := fT
    cases T with
    | prim p =>
      rw [finiteDefaultFieldCells, finiteDefaultCells, ih hp]
      rfl
    | ref R => cases hp

theorem finiteDefaultCells_primitiveStruct {s : Name}
    (hp : primitiveMembers (structDef s) = true) :
    finiteDefaultCells (.ref (.struct s)) = some (structAllocationSize s) := by
  simp only [finiteDefaultCells, finiteDefaultFieldCells_primitive hp, Option.map_some, Nat.zero_add]

/-- Every reached reference allocation has a positive cost, including empty structs. -/
theorem finiteDefaultCells_positive {R : RefTy} {n : Nat}
    (h : finiteDefaultCells (.ref R) = some n) : 0 < n := by
  cases R with
  | array E =>
    cases E with
    | prim p => simp only [finiteDefaultCells, Option.some.injEq] at h; omega
    | ref Q => simp only [finiteDefaultCells, reduceCtorEq] at h
  | fixed E k => simp only [finiteDefaultCells, reduceCtorEq] at h
  | mapping K V => simp only [finiteDefaultCells, reduceCtorEq] at h
  | struct s =>
    rw [finiteDefaultCells] at h
    cases he : finiteDefaultFieldCells (structDef s) with
    | none => rw [he] at h; cases h
    | some children =>
      rw [he] at h
      have hn : children + structAllocationSize s = n := Option.some.inj h
      have hs : 1 ≤ structAllocationSize s := Nat.le_max_left _ _
      omega

/-- Structural field traversal parameterized by the child traversal. -/
def fieldCellsWith (child : Ty → Option Nat) : List (Name × Ty) → Option Nat
  | [] => some 0
  | (_, T) :: fs => do
    let head ← child T
    let tail ← fieldCellsWith child fs
    pure (head + tail)

/-- Executable traversal. The bound is the existing certified layout rank,
not a tunable search or evaluator budget. -/
def finiteDefaultCellsAt : Nat → Ty → Option Nat
  | _, .prim _ => some 0
  | _, .ref (.array (.prim _)) => some 1
  | 0, .ref (.struct _) => none
  | depth + 1, .ref (.struct s) =>
    (fieldCellsWith (finiteDefaultCellsAt depth) (structDef s)).map (· + structAllocationSize s)
  | _, .ref (.array (.ref _)) | _, .ref (.fixed _ _) | _, .ref (.mapping _ _) => none
termination_by structural depth => depth

private theorem member_rank {fs : List (Name × Ty)} {ft : Name × Ty} (h : ft ∈ fs) :
    tyRank ft.2 ≤ fieldsRank fs := by
  induction fs with
  | nil => cases h
  | cons a fs ih =>
    rcases List.mem_cons.mp h with he | ht
    · subst ft; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ht) (Nat.le_max_right _ _)

private theorem fieldCellsWith_eq (fs : List (Name × Ty)) (child : Ty → Option Nat)
    (hh : ∀ ft ∈ fs, child ft.2 = finiteDefaultCells ft.2) :
    fieldCellsWith child fs = finiteDefaultFieldCells fs := by
  induction fs with
  | nil => rw [fieldCellsWith, finiteDefaultFieldCells]
  | cons ft fs ih =>
    rw [fieldCellsWith, finiteDefaultFieldCells, hh ft List.mem_cons_self,
      ih (fun ft hf => hh ft (List.mem_cons_of_mem _ hf))]

/-- The executable traversal exactly matches the rank-decreasing specification. -/
theorem finiteDefaultCellsAt_eq (depth : Nat) (T : Ty) (hr : tyRank T ≤ depth) :
    finiteDefaultCellsAt depth T = finiteDefaultCells T := by
  induction depth generalizing T with
  | zero =>
    cases T with
    | prim p => rw [finiteDefaultCellsAt, finiteDefaultCells]
    | ref R =>
      cases R with
      | array E => cases E <;> rw [finiteDefaultCellsAt, finiteDefaultCells]
      | fixed E n => rw [finiteDefaultCellsAt, finiteDefaultCells]
      | mapping K V => rw [finiteDefaultCellsAt, finiteDefaultCells]
      | struct s => have hp := structRank_pos s; change structRank s ≤ 0 at hr; omega
  | succ depth ih =>
    cases T with
    | prim p => rw [finiteDefaultCellsAt, finiteDefaultCells]
    | ref R =>
      cases R with
      | array E => cases E <;> rw [finiteDefaultCellsAt, finiteDefaultCells]
      | fixed E n => rw [finiteDefaultCellsAt, finiteDefaultCells]
      | mapping K V => rw [finiteDefaultCellsAt, finiteDefaultCells]
      | struct s =>
        rw [finiteDefaultCellsAt, finiteDefaultCells,
          fieldCellsWith_eq (structDef s) _ (by
            intro ft hft
            apply ih ft.2
            have hm := member_rank hft
            have hs := structDef_rank_lt s
            change structRank s ≤ depth + 1 at hr
            omega)]

def finiteDefaultCellsComputed (T : Ty) : Option Nat := finiteDefaultCellsAt (tyRank T) T

theorem finiteDefaultCellsComputed_eq (T : Ty) : finiteDefaultCellsComputed T = finiteDefaultCells T :=
  finiteDefaultCellsAt_eq _ _ (Nat.le_refl _)

end Solidity.Evm.Memory
