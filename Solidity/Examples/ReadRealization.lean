import Solidity.Calculus.ReadRealization
import Solidity.Calculus.Surface

/-!
# Finite reads are actual typed storage

Two occurrences of `balances[3]` are aliases even when built separately.
Consistent assignments materialize into the interpreter's storage, while
conflicting aliases have no storage representative. Signed and boolean
values participate in the same finite footprint as unsigned mapping reads.
-/

namespace Solidity.Examples.ReadRealization

open Solidity.ReadRealization

def Bank : Contract := contract!{
  mapping(uint => uint) balances;
  int debt;
  bool paused;
}

def balance (k : PrimTy.uint.Denote) : Ref Bank :=
  ⟨.uint, (SRef.ofRoot "balances" rfl).index .map k, by
    change (Path.nil.append (Path.index IndexTy.map k)).Declared
    rw [Path.append_nil, Path.index_map]
    exact .key k .nil⟩

def debt : Ref Bank := ⟨.int, SRef.ofRoot "debt" rfl, .nil⟩
def paused : Ref Bank := ⟨.bool, SRef.ofRoot "paused" rfl, .nil⟩

def three : Ref Bank := balance (PrimTy.ofLit .uint 3 rfl)
def sameThree : Ref Bank := balance (PrimTy.ofLit .uint (1 + 2) (by decide))
def four : Ref Bank := balance (PrimTy.ofLit .uint 4 rfl)

/-- Actual endpoint equality detects the two syntactic occurrences' alias. -/
example : three = sameThree := by decide +kernel

def reads : Assignment Bank :=
  [⟨three, PrimTy.ofLit .uint 7 rfl⟩,
   ⟨sameThree, PrimTy.ofLit .uint 7 rfl⟩,
   ⟨four, PrimTy.ofLit .uint 9 rfl⟩,
   ⟨debt, PrimTy.ofLit .int (-2) rfl⟩,
   ⟨paused, true⟩]

theorem reads_consistent : reads.Consistent :=
  (Assignment.consistentB_iff reads).1 (by decide +kernel)

/-- `balances[3]` really reads `7` from the materialized storage. -/
example : reads.realize.find three.ref = some (.prim (PrimTy.ofLit .uint 7 rfl)) :=
  Assignment.realize_spec reads_consistent List.mem_cons_self

/-- A different key and primitive type retain their independent values. -/
example : reads.realize.find debt.ref = some (.prim (PrimTy.ofLit .int (-2) rfl)) :=
  Assignment.realize_spec reads_consistent
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

example : paused.read reads.realize = true := by decide +kernel
example : four.read reads.realize = PrimTy.ofLit .uint 9 rfl := by decide +kernel

def conflicting : Assignment Bank :=
  [⟨three, PrimTy.ofLit .uint 7 rfl⟩, ⟨sameThree, PrimTy.ofLit .uint 9 rfl⟩]

/-- Inconsistent aliases cannot describe any typed interpreter storage. -/
theorem conflicting_not_realizable :
    ¬ ∃ st : Storage Bank, ∀ (r : Ref Bank) (v : r.Value),
      ⟨r, v⟩ ∈ conflicting → st.find r.ref = some (.prim v) := by
  intro h
  have hc := (Assignment.consistentB_iff conflicting).2
    ((Assignment.realizable_iff conflicting).2 h)
  have hf : conflicting.consistentB = false := by decide +kernel
  rw [hf] at hc
  cases hc

/-- info: 'Solidity.ReadRealization.Assignment.realizable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Assignment.realizable_iff

end Solidity.Examples.ReadRealization
