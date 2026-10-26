import Solidity.Calculus.AliasConstraints
import Solidity.Examples.QueryArithmetic
import Solidity.Examples.QueryReduction

/-!
# Generated alias constraints for dependent reads

The occurrence list records `balances[3]` and `balances[x₀]`, with their
results at typed atoms `x₀` and `x₁`. The path comparison generates their
alias conditions, and the shared checked compiler generates all arithmetic.
Only the source-to-occurrence flattening is still written explicitly here.
-/

namespace Solidity.Examples.AliasConstraints

open Solidity.Decide Solidity.Semantics Solidity.ReadRealization
open Solidity.Linear Solidity.Linear.ScalarCode
open Solidity.Examples.ReadRealization (Bank balance three four)
open Solidity.Examples.QueryArithmetic (nested claim reduction)

def mapPath (key : LTm Bank (.val .uint)) : Decide.SPath Bank (.prim .uint) :=
  ⟨"balances", rfl, .key key .nil⟩

theorem mapPath_eval (g : State Bank []) (ν : AEnv) (key : LTm Bank (.val .uint))
    (k : PrimTy.uint.Denote) (hk : key.eval g ν = some k) :
    (mapPath key).eval g ν = some (balance k).ref := by
  simp only [mapPath, Decide.SPath.eval, TSegs.eval_key, TSegs.eval_nil, hk,
    Option.map_some, Option.bind_some, balance, SRef.index, SRef.append, SRef.ofRoot,
    Path.append_nil, Path.index_map]

def reads : List (SymbolicRead Bank) :=
  [⟨.uint, mapPath (.lit (PrimTy.ofLit .uint 3 rfl)), .var 0⟩,
    ⟨.uint, mapPath (.var 0), .var 1⟩]

def parameters : List Parameter := [⟨.uint, 0⟩, ⟨.uint, 1⟩]
def leaf : LFml Bank := .imp (SymbolicRead.constraints reads)
  (.eq (.var 1) (.lit (PrimTy.ofLit .uint 17 rfl)))

def encoded : StorageEncoding (ps := parameters) leaf :=
  (StorageEncoding.ofFormula? leaf).get (by decide +kernel)

example : encoded.refs = [] := by decide +kernel

def atoms (k v : PrimTy.uint.Denote) : AEnv :=
  (AEnv.dflt.set .uint 0 k).set .uint 1 v

def realized (k v : PrimTy.uint.Denote) :
    List (SymbolicRead.Realized (State.init Bank) (atoms k v)) :=
  [⟨reads[0], ⟨three.ref, three.declared, k,
      mapPath_eval _ _ _ _ rfl, by rfl⟩⟩,
    ⟨reads[1], ⟨(balance k).ref, (balance k).declared, v,
      mapPath_eval _ _ _ _ rfl, by rfl⟩⟩]

theorem generated_consistency (k v : PrimTy.uint.Denote) :
    (SymbolicRead.constraints reads).holds (State.init Bank) (atoms k v) ↔
      Assignment.Consistent [⟨three, k⟩, ⟨balance k, v⟩] :=
  SymbolicRead.constraints_realized_holds (State.init Bank) (atoms k v) (realized k v)

def arithmetic : nested.Arithmetic where
  types := [.uint, .uint]
  layout := fun _ => rfl
  formula := ⟨encoded.lower [], by decide +kernel⟩
  correct := by
    rintro ⟨k, v, ⟨⟩⟩
    have hc := encoded.correct [] (by decide +kernel) (State.init Bank) (atoms k v)
    have ho : Inputs.observe [] parameters [] (State.init Bank) (atoms k v) = (k, v, ()) := rfl
    rw [ho] at hc
    change (encoded.lower []).holds (Values.codes (ps := [.uint, .uint]) (k, v, ())) ↔ _
    rw [hc]
    change ((SymbolicRead.constraints reads).holds (State.init Bank) (atoms k v) →
      v = PrimTy.ofLit .uint 17 rfl) ↔
        (Assignment.Consistent [⟨three, k⟩, ⟨balance k, v⟩] →
          decide (v = PrimTy.ofLit .uint 17 rfl) = true)
    rw [generated_consistency, decide_eq_true_eq]

def counterstore : { st : Storage Bank // nested.runStorage st = false } :=
  query_countermodel[arithmetic]

/-- info: (0, 0) -/
#guard_msgs in #eval ((three.read counterstore.val).val,
  ((balance (three.read counterstore.val)).read counterstore.val).val)

def sourceCounterstate : { σ : State Bank [] // ¬ holds σ claim } :=
  reduction.countermodelFromQuery (State.init Bank) [] ⟨counterstore.val, counterstore.property⟩

/-- Conflicting self-aliases satisfy the generated implication and cannot
be used as arithmetic countermodels. A different location is independent. -/
example : arithmetic.checkCodes [3, 19] = true := by decide +kernel
example : arithmetic.checkCodes [4, 19] = false := by decide +kernel

def mapTerm (key : LTm Bank (.val .uint)) : LTm Bank (.path (.prim .uint)) :=
  .index .map (.app0 (.root "balances" rfl)) key

/-- Existing source path terms enter the same automatic comparison and
checked arithmetic compiler, without manually constructing `SPath`. -/
def sourceAlias : AliasEncoding (ps := parameters)
    (mapTerm (.lit (PrimTy.ofLit .uint 3 rfl))) (mapTerm (.var 0)) :=
  (aliasEncoding? parameters [] _ _).get (by decide +kernel)

example : (sourceAlias.encoding.lower []).check (fun i => ([3, 19] : List Nat)[i]?.getD 0) = true := by decide +kernel
example : (sourceAlias.encoding.lower []).check (fun i => ([4, 19] : List Nat)[i]?.getD 0) = false := by decide +kernel

def checkedKey : LTm Bank (.val .uint) :=
  .app2 (.binop .add rfl) (.var 0) (.lit (PrimTy.ofLit .uint 1 rfl))

def checkedAlias : AliasEncoding (ps := parameters) (mapTerm checkedKey) (mapTerm (.var 1)) :=
  (aliasEncoding? parameters [] _ _).get (by decide +kernel)

example : (checkedAlias.encoding.lower []).check
    (fun i => ([2 ^ 256 - 1, 0] : List Nat)[i]?.getD 0) = false := by decide +kernel
example : (Decide.SPath.view? (LTm.err (C := Bank) (s := .path (.prim .uint)))).isNone = true := by decide +kernel

def failedRead : SymbolicRead Bank := ⟨.uint, mapPath .err, .var 0⟩

/-- Alias soundness requires successful paths; a failed key has no
successful occurrence witness at all. -/
theorem failedRead_no_witness (g : State Bank []) (ν : AEnv) :
    ¬ Nonempty (SymbolicRead.Witness g ν failedRead) := by
  rintro ⟨w⟩
  have h := w.path_eq
  change none = some w.ref at h
  cases h

def failedResult : SymbolicRead Bank :=
  ⟨.uint, mapPath (.lit (PrimTy.ofLit .uint 3 rfl)), .err⟩

theorem failedResult_no_witness (g : State Bank []) (ν : AEnv) :
    ¬ Nonempty (SymbolicRead.Witness g ν failedResult) := by
  rintro ⟨w⟩
  have h := w.result_eq
  change none = some w.value at h
  cases h

example : (SymbolicRead.mk .bool ⟨"paused", rfl, .nil⟩ (.var 0)).constraint reads[0] =
    LFml.tt := rfl

def debtPath : Decide.SPath Bank (.prim .int) := ⟨"debt", rfl, .nil⟩
def pausedPath : Decide.SPath Bank (.prim .bool) := ⟨"paused", rfl, .nil⟩
example : debtPath.alias pausedPath = LFml.ff := rfl

open Solidity.Examples.QueryReduction (Nested)

def agePath (a : LTm Nested (.val .int)) (b : LTm Nested (.val .bool)) :
    Decide.SPath Nested (.prim .uint) :=
  ⟨"people", rfl, .key a (.key b (.field (f := "age") rfl .nil))⟩

def balancePath (a : LTm Nested (.val .int)) (b : LTm Nested (.val .bool)) :
    Decide.SPath Nested (.prim .uint) :=
  ⟨"people", rfl, .key a (.key b
    (.field (f := "account") rfl (.field (f := "balance") rfl .nil)))⟩

def keyParameters : List Parameter := [⟨.int, 0⟩, ⟨.bool, 1⟩, ⟨.int, 2⟩, ⟨.bool, 3⟩]

def nestedAlias := (agePath (.var 0) (.var 1)).alias (agePath (.var 2) (.var 3))
def nestedEncoding : StorageEncoding (ps := keyParameters) nestedAlias :=
  (StorageEncoding.ofFormula? nestedAlias).get (by decide +kernel)

def equalKeys : List Nat := [2 ^ 255 - 2, 1, 2 ^ 255 - 2, 1]
def differentKeys : List Nat := [2 ^ 255 - 2, 1, 2 ^ 255 - 2, 0]

/-- Signed and Boolean mapping keys are compared at their own types. -/
example : (nestedEncoding.lower []).check (fun i => equalKeys[i]?.getD 0) = true := by decide +kernel
example : (nestedEncoding.lower []).check (fun i => differentKeys[i]?.getD 0) = false := by decide +kernel
example : (agePath (.var 0) (.var 1)).alias (balancePath (.var 0) (.var 1)) = LFml.ff := rfl

def threeReads : List (SymbolicRead Bank) := reads ++ [⟨.uint, mapPath (.var 1), .var 2⟩]
def threeParameters : List Parameter := parameters ++ [⟨.uint, 2⟩]
def threeEncoding : StorageEncoding (ps := threeParameters) (SymbolicRead.constraints threeReads) :=
  (StorageEncoding.ofFormula? _).get (by decide +kernel)

/-- The locations are `3,4,3`: only occurrences zero and two alias. -/
example : (threeEncoding.lower []).check (fun i => ([4, 3, 4] : List Nat)[i]?.getD 0) = true := by decide +kernel
example : (threeEncoding.lower []).check (fun i => ([4, 3, 19] : List Nat)[i]?.getD 0) = false := by decide +kernel

def subsetAtoms : AEnv :=
  (atoms (PrimTy.ofLit .uint 4 rfl) (PrimTy.ofLit .uint 3 rfl)).set .uint 2 (PrimTy.ofLit .uint 4 rfl)

def subsetRealized : List (SymbolicRead.Realized (State.init Bank) subsetAtoms) :=
  [⟨threeReads[0], ⟨three.ref, three.declared, PrimTy.ofLit .uint 4 rfl, mapPath_eval _ _ _ _ rfl, rfl⟩⟩,
    ⟨threeReads[1], ⟨four.ref, four.declared, PrimTy.ofLit .uint 3 rfl, mapPath_eval _ _ _ _ rfl, rfl⟩⟩,
    ⟨threeReads[2], ⟨three.ref, three.declared, PrimTy.ofLit .uint 4 rfl, mapPath_eval _ _ _ _ rfl, rfl⟩⟩]

theorem subset_consistent : Assignment.Consistent (subsetRealized.map fun r => r.2.entry) :=
  (SymbolicRead.constraints_realized_holds (State.init Bank) subsetAtoms subsetRealized).mp
    ((threeEncoding.correct [] (by decide +kernel) (State.init Bank) subsetAtoms).mp
      ((AFml.check_iff _ _).mp (by decide +kernel)))

def subsetStorage : Storage Bank := Assignment.realize (subsetRealized.map fun r => r.2.entry)

example : three.read subsetStorage = PrimTy.ofLit .uint 4 rfl := by decide +kernel
example : four.read subsetStorage = PrimTy.ofLit .uint 3 rfl := by decide +kernel

/-- info: 'Solidity.Decide.SymbolicRead.constraints_realized_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SymbolicRead.constraints_realized_holds

/-- info: 'Solidity.Decide.AliasEncoding.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AliasEncoding.correct

/-- info: 'Solidity.Examples.AliasConstraints.sourceCounterstate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sourceCounterstate

/-- info: 'Solidity.Examples.AliasConstraints.subset_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms subset_consistent

end Solidity.Examples.AliasConstraints
