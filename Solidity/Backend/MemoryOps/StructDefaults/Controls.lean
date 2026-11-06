import Solidity.Backend.MemoryOps.StructDefaults.Nested

namespace Solidity.Backend.MemoryOps.StructDefaults.Controls
open Solidity Source

def declaration : Source.Decl :=
  ⟨.struct, "Pair", none, true,
    .struct "Pair" (.structMember (.elem (.int false 256 (by decide))) "tag")
      (.cons (.structMember (.array (.elem .bool) .none) "child") .nil)⟩
def outerDeclaration : Source.Decl :=
  ⟨.struct, "Outer", none, true,
    .struct "Outer" (.structMember (.userType ⟨"Pair", []⟩) "pair")
      (.cons (.structMember (.elem .bool) "flag") .nil)⟩
def E : Source.Env := ⟨[declaration, outerDeclaration]⟩
def name : Source.DeclName := ⟨none, "Pair"⟩

theorem actual_layout : E.layout.fields name = PairFields := rfl

def initial : Source.St E :=
  ⟨⟨⟨fun _ => Source.Account.empty _⟩, Source.Transient.empty, []⟩,
    (Source.Heap.empty.alloc ⟨.bytes .memory, .bytes [17,23]⟩).1,
    [], [], ⟨[], .nil⟩⟩
def state : Source.EMState E [] := (.nil, initial)

def completed : Source.EMState E [] :=
  ((Source.zeroVal (E := E) (Γ := []) 6 (.struct .memory name)).run state).2

theorem constructed :
    ∃ fs : Source.DataList E.layout (E.layout.fields name),
      (Source.zeroVal (E := E) (Γ := []) 6 (.struct .memory name)).run state =
        (.ok (.memRef rfl 2), (.nil, {initial with heap := pairHeap initial.heap name fs})) ∧
      fs.nth 0 (.int .u256) = .ok (.val (.int 0 Source.IntTy.u256.zero_mem)) ∧
      fs.nth 1 SourceBoolArrayTy = .ok (.val (.memRef rfl 1)) :=
  source_pair_default state name actual_layout 0

theorem observations :
    completed.2.heap.next = 3 ∧
    completed.2.heap.get 0 = some ⟨.bytes .memory, .bytes [17,23]⟩ ∧
    completed.2.heap.get 1 = some ⟨SourceBoolArrayTy, sourceBoolMemory []⟩ ∧
    completed.2.heap.get 3 = none := by
  obtain ⟨fs, evaluated, _, _⟩ := constructed
  unfold completed
  rw [evaluated]
  refine ⟨pairHeap_cursor _ _ _, ?_, pairHeap_child _ _ _, pairHeap_free _ _ _ 3 (by decide)⟩
  exact pairHeap_old initial.heap name fs 0 (by intro h; cases h)

theorem insufficient_fuel :
    (Source.zeroVal (E := E) (Γ := []) 5 (.struct .memory name)).run state =
      (.error .timeout, state) := by rfl

theorem wrong_root_refuted :
    ((Source.zeroVal (E := E) (Γ := []) 6 (.struct .memory name)).run state).1 ≠
      .ok (.memRef rfl 1) := by
  obtain ⟨fs, evaluated, _, _⟩ := constructed
  rw [evaluated]
  intro h
  cases h

def outerName : Source.DeclName := ⟨none, "Outer"⟩
theorem actual_outer_layout :
    E.layout.fields outerName = [.struct .memory name, .bool] := rfl

theorem nested_constructed :
    ∃ ifs : Source.DataList E.layout (E.layout.fields name),
    ∃ ofs : Source.DataList E.layout (E.layout.fields outerName),
      (Source.zeroVal (E := E) (Γ := []) 9 (.struct .memory outerName)).run state =
        (.ok (.memRef rfl 3),
          (.nil, {initial with heap := ((pairHeap initial.heap name ifs).alloc
            ⟨.struct .memory outerName, Source.Data.struct ofs⟩).1})) ∧
      ofs.nth 0 (.struct .memory name) = .ok (.val (.memRef rfl 2)) ∧
      ofs.nth 1 .bool = .ok (.val (.bool false)) :=
  source_nested_default state name outerName actual_layout actual_outer_layout 0

#print axioms nested_constructed
#print axioms constructed
#print axioms observations
#print axioms insufficient_fuel
#print axioms wrong_root_refuted
end Solidity.Backend.MemoryOps.StructDefaults.Controls
