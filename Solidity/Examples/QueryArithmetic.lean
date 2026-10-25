import Solidity.Calculus.QueryArithmetic
import Solidity.Calculus.LinearForms
import Solidity.Calculus.CheckedScalar
import Solidity.Calculus.LinearSyntax
import Solidity.Calculus.TraceReduction
import Solidity.Tools.QueryArithmetic
import Solidity.Examples.ReadRealization

/-!
# Arithmetic chooses dependent-read countervalues

The second `balances` key is the first read's value. Its two occurrences
share a value precisely when that first value equals the initial key.
The complete solver chooses values satisfying that alias implication;
trace realization reconstructs the actual counterstore.
-/

namespace Solidity.Examples.QueryArithmetic

open Solidity.ReadRealization Solidity.Linear Solidity.Linear.ScalarCode
open Solidity.Examples.ReadRealization (Bank balance three debt paused)

def nested : Query Bank Bool :=
  .read three fun k => .read (balance k) fun v => .pure (decide (v = PrimTy.ofLit .uint 17 rfl))

theorem balance_eq (a b : PrimTy.uint.Denote) : balance a = balance b ↔ a = b := by
  constructor
  · intro h
    have he := congrArg (fun r : Ref Bank => r.ref.path.labels) h
    simp only [balance, SRef.index, SRef.append, SRef.ofRoot, Path.append_nil,
      Path.index_map, Path.labels_key, Path.labels_nil, List.cons.injEq,
      and_true] at he
    cases Semantics.Selector.key.inj he
    rfl
  · rintro rfl; rfl

theorem three_prim : three.prim = .uint := rfl
theorem balance_prim (k : PrimTy.uint.Denote) : (balance k).prim = .uint := rfl

theorem alias_consistency (k v : PrimTy.uint.Denote) :
    Assignment.Consistent [⟨three, k⟩, ⟨balance k, v⟩] ↔ (k.val = 3 → k = v) := by
  change Assignment.Consistent
    [⟨⟨.uint, three.ref, three.declared⟩, k⟩,
      ⟨⟨.uint, (balance k).ref, (balance k).declared⟩, v⟩] ↔ _
  rw [Assignment.pair_consistent_typed]
  change (balance (PrimTy.ofLit .uint 3 rfl) = balance k → k = v) ↔ _
  rw [balance_eq]
  have hk : PrimTy.ofLit .uint 3 rfl = k ↔ k.val = 3 :=
    ⟨fun h => (congrArg Subtype.val h).symm, fun h => Subtype.ext h.symm⟩
  rw [hk]

def arithmetic : nested.Arithmetic where
  types := [.uint, .uint]
  layout := fun _ => rfl
  formula := ⟨linear!{ ([1] = 3 → [1, -1] = 0) → [0, 1] = 17 }, by decide +kernel⟩
  correct := by
    rintro ⟨k, v, ⟨⟩⟩
    simp only [TypedFormula.holds, AFml.holds, Lin.eval, Values.codes,
      nested, Query.replay, occurrenceValues]
    simp only [three, balance, ↓reduceDIte, shift, Values.codes, Int.one_mul,
      Int.zero_mul, Int.zero_add, Int.add_zero, encode, decide_eq_true_eq]
    simp only [↓reduceDIte, Assignment.pair_consistent_typed]
    change _ ↔ ((balance (PrimTy.ofLit .uint 3 rfl) = balance k → k = v) → v = PrimTy.ofLit .uint 17 rfl)
    rw [balance_eq]
    have hk0 : 0 ≤ k.val := PrimTy.uint_nonneg k
    have hv0 : 0 ≤ v.val := PrimTy.uint_nonneg v
    have hk : PrimTy.ofLit .uint 3 rfl = k ↔ k.val = 3 :=
      ⟨fun h => (congrArg Subtype.val h).symm, fun h => Subtype.ext h.symm⟩
    have hkv : k = v ↔ k.val = v.val := ⟨congrArg Subtype.val, Subtype.ext⟩
    have hv17 : v = PrimTy.ofLit .uint 17 rfl ↔ v.val = 17 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hk, hkv, hv17]
    omega

def result := arithmetic.verify

/-- info: true -/
#guard_msgs in #eval result.isRight

/-- Compiled arithmetic chooses the values; the kernel checks only their
finite replay and the actual counterstore's query refutation. -/
def counterstore : { st : Storage Bank // nested.runStorage st = false } :=
  query_countermodel[arithmetic]

/-- info: (0, 0) -/
#guard_msgs in #eval ((three.read counterstore.val).val,
  ((balance (three.read counterstore.val)).read counterstore.val).val)

/-- The unguarded false result at `(3,19)` is not a storage countermodel:
both occurrences select `balances[3]`, so the alias premise fails. -/
example : arithmetic.checkCodes [3, 19] = true := by decide +kernel
example : arithmetic.checkCodes [4, 19] = false := by decide +kernel

open Solidity.Decide Solidity.Semantics
open scoped Solidity.Scoped
local instance : InContract := ⟨Bank⟩

def claim : Fml Bank [] := dl!{ balances[balances[3]] == 17 }
def reduction : TraceReduction claim := (traceReduction? claim).get (by decide +kernel)

/-- The solver-selected nested-read counterstore refutes the original
scoped source claim, without a user-supplied occurrence assignment. -/
def sourceCounterstate : { σ : State Bank [] // ¬ holds σ claim } :=
  reduction.countermodelFromQuery (State.init Bank) [] ⟨counterstore.val, counterstore.property⟩

theorem invalid : ¬ Fml.Valid claim := fun h => sourceCounterstate.property (h sourceCounterstate.val)

def aliasLaw : Query Bank Bool :=
  .read three fun k => .read (balance k) fun v =>
    .pure (decide (k.val = 3 → k = v))

def aliasArithmetic : aliasLaw.Arithmetic where
  types := [.uint, .uint]
  layout := fun _ => rfl
  formula := ⟨linear!{ ([1] = 3 → [1, -1] = 0) → ([1] = 3 → [1, -1] = 0) },
    by decide +kernel⟩
  correct := by
    rintro ⟨k, v, ⟨⟩⟩
    simp only [TypedFormula.holds, AFml.holds, imp_self, aliasLaw,
      Query.replay, occurrenceValues, three_prim, balance_prim, ↓reduceDIte,
      decide_eq_true_eq]
    change True ↔ (Assignment.Consistent [⟨three, k⟩, ⟨balance k, v⟩] → k.val = 3 → k = v)
    simp only [alias_consistency, imp_self]

/-- info: true -/
#guard_msgs in #eval aliasArithmetic.verify.isLeft

/-- The positive arithmetic certificate proves the alias law in every
actual storage, including all choices of the dependent key. -/
theorem alias_valid : ∀ st : Storage Bank, aliasLaw.runStorage st = true :=
  aliasArithmetic.valid_iff.mpr (fun _ => id)

def rejectForgedCodes : Lean.Elab.Term.TermElabM Bool :=
  Lean.tryCatchRuntimeEx
    (do
      let _ ← Solidity.Tools.queryCountermodelOfCodes (Lean.mkConst ``arithmetic) [3, 19]
      pure false)
    (fun e => do pure ((← e.toMessageData.toString) == "exact verification: kernel rejected certificate"))

/-- info: true -/
#guard_msgs in #eval rejectForgedCodes

def rejectValidQuery : Lean.Elab.Term.TermElabM Bool :=
  Lean.tryCatchRuntimeEx
    (do
      let _ ← Solidity.Tools.queryCountermodel (Lean.mkConst ``aliasArithmetic)
      pure false)
    (fun e => do pure ((← e.toMessageData.toString) == "query_countermodel: the certified query is valid"))

/-- info: true -/
#guard_msgs in #eval rejectValidQuery

def mixed : Query Bank Bool :=
  .read paused fun b => .read debt fun d => .read three fun k =>
    .read (balance k) fun v => .pure (decide (b = true ∧ d.val = -2 → v = PrimTy.ofLit .uint 17 rfl))

def mixedFormula : AFml :=
  .imp ((Affine.variable 2 |>.eq (.literal 3)).imp
    (Affine.variable 2 |>.eq (.variable 3)))
    (.imp (.and (Affine.variable 0 |>.eq (.literal 1))
      (Affine.variable 1 |>.eq (.literal (((2 ^ 255 : Nat) : Int) - 2))))
      (Affine.variable 3 |>.eq (.literal 17)))

theorem mixed_consistency (b : Bool) (d : PrimTy.int.Denote) (k v : PrimTy.uint.Denote) :
    Assignment.Consistent [⟨paused, b⟩, ⟨debt, d⟩, ⟨three, k⟩, ⟨balance k, v⟩] ↔
      (k.val = 3 → k = v) := by
  have hb : ∀ e ∈ ([⟨debt, d⟩, ⟨three, k⟩, ⟨balance k, v⟩] : Assignment Bank),
      e.1.prim ≠ paused.prim := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      simp only [debt, paused, three, balance, ne_eq, reduceCtorEq, not_false_eq_true]
  have hd : ∀ e ∈ ([⟨three, k⟩, ⟨balance k, v⟩] : Assignment Bank),
      e.1.prim ≠ debt.prim := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;>
      simp only [debt, three, balance, ne_eq, reduceCtorEq, not_false_eq_true]
  rw [Assignment.cons_different_type paused b _ hb,
    Assignment.cons_different_type debt d _ hd, alias_consistency]

def mixedArithmetic : mixed.Arithmetic where
  types := [.bool, .int, .uint, .uint]
  layout := fun _ => rfl
  formula := ⟨mixedFormula, by decide +kernel⟩
  correct := by
    rintro ⟨b, d, k, v, ⟨⟩⟩
    simp only [TypedFormula.holds, mixedFormula, AFml.holds, Affine.holds_eq,
      Affine.eval_variable, Affine.eval_literal, Values.codes, encode_integer,
      integer, offset, mixed, Query.replay, occurrenceValues,
      three_prim, balance_prim, ↓reduceDIte, decide_eq_true_eq]
    change _ ↔ (Assignment.Consistent
      [⟨paused, b⟩, ⟨debt, d⟩, ⟨three, k⟩, ⟨balance k, v⟩] →
        (b = true ∧ d.val = -2 → v = PrimTy.ofLit .uint 17 rfl))
    rw [mixed_consistency]
    have hkv : k = v ↔ k.val = v.val := ⟨congrArg Subtype.val, Subtype.ext⟩
    have hv17 : v = PrimTy.ofLit .uint 17 rfl ↔ v.val = 17 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hkv, hv17]
    have hb : ((if b = true then 1 else 0) : Int) = 1 ↔ b = true := by
      cases b with
      | false => simp only [reduceCtorEq, ↓reduceIte, Int.reduceEq]
      | true => simp only [↓reduceIte]
    have hd : d.val + ((2 ^ 255 : Nat) : Int) = ((2 ^ 255 : Nat) : Int) - 2 ↔
        d.val = -2 := by omega
    simp only [Int.add_zero, hb, hd]

def mixedCounterstore : { st : Storage Bank // mixed.runStorage st = false } :=
  query_countermodel[mixedArithmetic]

/-- info: (true, -2, 7, 3) -/
#guard_msgs in #eval (paused.read mixedCounterstore.val, (debt.read mixedCounterstore.val).val,
  (three.read mixedCounterstore.val).val,
  ((balance (three.read mixedCounterstore.val)).read mixedCounterstore.val).val)

/-- info: 'Solidity.ReadRealization.Query.Arithmetic.valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Query.Arithmetic.valid_iff

/-- info: 'Solidity.Examples.QueryArithmetic.invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms invalid

/-- info: 'Solidity.Examples.QueryArithmetic.mixedCounterstore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mixedCounterstore

end Solidity.Examples.QueryArithmetic
