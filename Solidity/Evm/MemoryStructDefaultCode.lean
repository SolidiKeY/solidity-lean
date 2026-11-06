import Solidity.Evm.MemoryStructDefaultPlan

/-!
# Executable finite-default layouts and their certificates

The target data is indexed by the original reference type (and field list).
It contains only cost, relative addresses and emitted instructions. Soundness
is transported from DefaultPlan in Prop, so executing the compiler does not
project code through recursively instantiated proof-bearing records.
-/
namespace Solidity.Evm.Memory
open Semantics

structure DefaultCode (R : RefTy) where
  cost : Nat
  root : Nat
  code : List Instr

structure DefaultFieldCode (fs : List (Name × Ty)) where
  cost : Nat
  offsets : Name → Nat
  code : List Instr

def DefaultPlan.data {R : RefTy} (plan : DefaultPlan R) : DefaultCode R :=
  ⟨plan.cost, plan.root, plan.code⟩
def DefaultFieldsPlan.data {fs : List (Name × Ty)} (plan : DefaultFieldsPlan fs) : DefaultFieldCode fs :=
  ⟨plan.cost, plan.offsets, plan.code⟩

def defaultFieldsCodeWith (child : (R : RefTy) → Option (DefaultCode R)) :
    (fs : List (Name × Ty)) → Option (DefaultFieldCode fs)
  | [] => some ⟨0, fun _ => 0, []⟩
  | (_, .prim _) :: fs => (defaultFieldsCodeWith child fs).map (fun tail =>
    ⟨tail.cost, tail.offsets, tail.code⟩)
  | (f, .ref R) :: fs => do
    let head ← child R
    let tail ← defaultFieldsCodeWith child fs
    pure ⟨head.cost + tail.cost,
      fun g => if g = f then head.root else head.cost + tail.offsets g,
      head.code ++ ([.pop] ++ tail.code)⟩

def defaultCodeAt : Nat → (R : RefTy) → Option (DefaultCode R)
  | _, .array (.prim _) => some ⟨1, 0, [.push w[0]] ++ allocateArrayCode⟩
  | 0, .struct _ => none
  | depth + 1, .struct s => (defaultFieldsCodeWith (defaultCodeAt depth) (structDef s)).map
    (fun fields => ⟨fields.cost + structAllocationSize s, fields.cost,
      fields.code ++ (allocateStructCode (structAllocationSize s) ++
        initializeReferenceCode (structDef s) fields.offsets fields.cost 0)⟩)
  | _, .array (.ref _) | _, .fixed _ _ | _, .mapping _ _ => none
termination_by structural depth => depth

def defaultCode? (R : RefTy) : Option (DefaultCode R) := defaultCodeAt (tyRank (.ref R)) R

private theorem defaultFieldsPlanWith_data (fs : List (Name × Ty))
    (child : (R : RefTy) → Option (DefaultPlan R))
    (raw : (R : RefTy) → Option (DefaultCode R))
    (hc : ∀ R, (child R).map DefaultPlan.data = raw R) :
    (defaultFieldsPlanWith child fs).map DefaultFieldsPlan.data = defaultFieldsCodeWith raw fs := by
  induction fs with
  | nil => rfl
  | cons ft fs ih =>
    obtain ⟨f, T⟩ := ft
    cases T with
    | prim p =>
      rw [defaultFieldsPlanWith, defaultFieldsCodeWith, ← ih]
      cases defaultFieldsPlanWith child fs <;> rfl
    | ref R =>
      rw [defaultFieldsPlanWith, defaultFieldsCodeWith, ← hc R, ← ih]
      cases child R <;> cases defaultFieldsPlanWith child fs <;> rfl

/-- Erasing proof fields yields exactly the independent executable traversal. -/
theorem defaultPlanAt_data (depth : Nat) (R : RefTy) :
    (defaultPlanAt depth R).map DefaultPlan.data = defaultCodeAt depth R := by
  induction depth generalizing R with
  | zero =>
    cases R with
    | array E => cases E <;> rfl
    | struct s => rfl
    | fixed E n => rfl
    | mapping K V => rfl
  | succ depth ih =>
    cases R with
    | array E => cases E <;> rfl
    | fixed E n => rfl
    | mapping K V => rfl
    | struct s =>
      rw [defaultPlanAt, defaultCodeAt,
        ← defaultFieldsPlanWith_data (structDef s) (defaultPlanAt depth) (defaultCodeAt depth) ih]
      cases defaultFieldsPlanWith (defaultPlanAt depth) (structDef s) <;> rfl

/-- Every accepted executable layout has the original source allocation certificate. -/
theorem defaultCode_sound {R : RefTy} {data : DefaultCode R} (h : defaultCode? R = some data) :
    finiteDefaultCells (.ref R) = some data.cost ∧ data.root < data.cost ∧
      DefaultPlanSound R data.cost data.root data.code := by
  have he := defaultPlanAt_data (tyRank (.ref R)) R
  change (defaultPlanAt (tyRank (.ref R)) R).map DefaultPlan.data = defaultCode? R at he
  rw [h] at he
  cases hp : defaultPlanAt (tyRank (.ref R)) R with
  | none => rw [hp] at he; cases he
  | some plan =>
    rw [hp] at he
    have hd : plan.data = data := Option.some.inj he
    cases hd
    exact ⟨plan.cells, plan.root_lt, plan.sound⟩

private theorem defaultFieldsCodeWith_cost (fs : List (Name × Ty))
    (child : (R : RefTy) → Option (DefaultCode R)) (count : Ty → Option Nat)
    (hc : ∀ R, (child R).map DefaultCode.cost = count (.ref R))
    (hp : ∀ p, count (.prim p) = some 0) :
    (defaultFieldsCodeWith child fs).map DefaultFieldCode.cost = fieldCellsWith count fs := by
  induction fs with
  | nil => rfl
  | cons ft fs ih =>
    obtain ⟨f,T⟩ := ft
    cases T with
    | prim p =>
      rw [defaultFieldsCodeWith, fieldCellsWith, hp, ← ih]
      cases defaultFieldsCodeWith child fs <;>
        simp only [Option.map, bind, Option.bind, pure, Nat.zero_add]
    | ref R =>
      rw [defaultFieldsCodeWith, fieldCellsWith, ← hc R, ← ih]
      cases child R <;> cases defaultFieldsCodeWith child fs <;> rfl

/-- Executable acceptance and costs exactly follow the finite layout specification. -/
theorem defaultCodeAt_cost (depth : Nat) (R : RefTy) :
    (defaultCodeAt depth R).map DefaultCode.cost = finiteDefaultCellsAt depth (.ref R) := by
  induction depth generalizing R with
  | zero =>
    cases R with
    | array E => cases E <;> rfl
    | struct s => rfl
    | fixed E n => rfl
    | mapping K V => rfl
  | succ depth ih =>
    cases R with
    | array E => cases E <;> rfl
    | fixed E n => rfl
    | mapping K V => rfl
    | struct s =>
      rw [defaultCodeAt, finiteDefaultCellsAt,
        ← defaultFieldsCodeWith_cost (structDef s) (defaultCodeAt depth)
          (finiteDefaultCellsAt depth) ih (fun _ => by cases depth <;> rfl)]
      cases defaultFieldsCodeWith (defaultCodeAt depth) (structDef s) <;> rfl

theorem defaultCode_cost (R : RefTy) :
    (defaultCode? R).map DefaultCode.cost = finiteDefaultCells (.ref R) := by
  rw [← finiteDefaultCellsComputed_eq]
  exact defaultCodeAt_cost _ _

end Solidity.Evm.Memory
