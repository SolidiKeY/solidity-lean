import Solidity.Backend.MemoryCopies.SourceDefaultHorizon

/-! Exact initialized results with added fuel, and a real partial default timeout. -/
namespace Solidity.Backend.MemoryCopies.SourceDefaultHorizonControls
private def declaration : Source.Decl :=
  ⟨.struct,"Node",none,true,.struct "Node"
    (.structMember (.array (.userType ⟨"Node",[]⟩) .none) "children")
    (.cons (.structMember (.array (.elem .bytes) (.some (.lit (.num (.dec 2 0 0))))) "chunks")
      (.cons (.structMember (.elem .string) "label") .nil))⟩
private def E : Source.Env := ⟨[declaration]⟩
private def name : Source.DeclName := ⟨none,"Node"⟩
private def before : Source.EMState E [.bool] :=
  (.cons (.bool true) .nil,
    ⟨⟨⟨fun _ => Source.Account.empty _⟩,Source.Transient.empty,[]⟩,
      (Source.Heap.empty.alloc ⟨.bool,.val (.bool true)⟩).1,[],
      [(⟨13,by decide⟩,[1,2])],⟨[.bool],.cons (.bool false) .nil⟩,Source.FailureExecution.Cursor.empty⟩)
private def fields : SourceFieldsConstruction E (E.layout.fields name) :=
  .cons (dynamicLeaf E (.struct .memory name)).construction.value
    (.cons ((bytesLeaf E).construction.fixed 2).value
      (.cons (stringLeaf E).construction.value (.nil E)))
private def node : SourceConstructionCertificate E (.struct .memory name) rfl := fields.structDefault name
private def scalar : SourceValueConstruction E .bool := .pureDefault (.bool false) rfl
private def long : SourceConstructionCertificate E (.array .memory (.bytes .memory) (some 64)) rfl :=
  (bytesLeaf E).construction.fixed 64
private def observe {type : Source.STy}
    (result : Source.R (Source.Val E.layout type) × Source.EMState E [.bool]) : Option (Nat × Nat) :=
  match result.1 with
  | .ok (.memRef _ root) => some (root,result.2.2.heap.next)
  | _ => none
private def byteContent (heap : Source.Heap E.layout) (root : Nat) : Option (List UInt8) :=
  match heap.get root with
  | some ⟨.bytes .memory,.bytes bytes⟩ => some bytes
  | _ => none
private def stringContent (heap : Source.Heap E.layout) (root : Nat) : Option (List UInt8) :=
  match heap.get root with
  | some ⟨.string .memory,.string bytes⟩ => some bytes
  | _ => none
private def refRoot {type : Source.STy} (data : Source.Data E.layout type) : Option Nat :=
  match data with
  | .val (.memRef _ root) => some root
  | _ => none
private def fixedRefs (heap : Source.Heap E.layout) : Option (List (Option Nat)) :=
  match heap.get 4 with
  | some ⟨.array .memory (.bytes .memory) (some 2),.array count _ values⟩ =>
      some ((List.finRange count).map (fun index => refRoot (values index)))
  | _ => none

theorem certificate_inhabited : SourceDefaultHorizonCertificate E [.bool] := sourceDefaultHorizons E [.bool]

theorem declared_layout : E.layout.fields name =
    [.array .memory (.struct .memory name) none,.array .memory (.bytes .memory) (some 2),.string .memory] := rfl

theorem node_observation :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 16 (.struct .memory name)).run before) = some (6,7) := by decide +kernel

theorem constructor_horizon (slack : Nat) :
    (Source.zeroVal (E := E) (Γ := [.bool]) (16 + slack) (.struct .memory name)).run before =
      (Source.zeroVal 16 (.struct .memory name)).run before := by
  have budget : node.horizon = 16 := by decide +kernel
  simpa only [budget] using node.horizon_exact before slack

theorem fields_horizon (slack : Nat) :
    (Source.zeroFields (E := E) (Γ := [.bool]) (14 + slack) (E.layout.fields name)).run before =
      (Source.zeroFields 14 (E.layout.fields name)).run before := by
  have budget : fields.horizon = 14 := by decide +kernel
  simpa only [budget] using fields.horizon_exact before slack

theorem scalar_default (slack : Nat) :
    (Source.zeroVal (E := E) (Γ := [.bool]) (scalar.horizon + slack) .bool).run before =
      (.ok (.bool false),before) := by
  rw [scalar.horizon_exact before slack]
  rfl

theorem nested_payloads :
    let heap := ((Source.zeroVal (E := E) (Γ := [.bool]) 16 (.struct .memory name)).run before).2.2.heap
    byteContent heap 2 = some [] ∧ byteContent heap 3 = some [] ∧
      fixedRefs heap = some [some 2,some 3] ∧ stringContent heap 5 = some [] := by decide +kernel

theorem long_observation :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 68 (.array .memory (.bytes .memory) (some 64))).run before) =
      some (65,66) := by decide +kernel

theorem long_horizon (slack : Nat) :
    (Source.zeroVal (E := E) (Γ := [.bool]) (68 + slack) (.array .memory (.bytes .memory) (some 64))).run before =
      (Source.zeroVal 68 (.array .memory (.bytes .memory) (some 64))).run before := by
  have budget : long.horizon = 68 := by decide +kernel
  simpa only [budget] using long.horizon_exact before slack

theorem empty_dynamic_default :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 3 (.array .memory (.bytes .memory) none)).run before) =
      some (1,2) := by decide +kernel

theorem storage_refusal :
    (Source.zeroVal (E := E) (Γ := [.bool]) 1 (.bytes .storage)).run before =
      (.error (.stuck "no default value"),before) := rfl

theorem refusal_horizon (slack : Nat) :
    (Source.zeroVal (E := E) (Γ := [.bool]) (1 + slack) (.bytes .storage)).run before =
      (.error (.stuck "no default value"),before) := by
  have finished : ((Source.zeroVal (E := E) (Γ := [.bool]) 1 (.bytes .storage)).run before).1 ≠ .error .timeout := by
    rw [storage_refusal]
    intro impossible
    cases impossible
  exact (zeroVal_horizon 1 slack (.bytes .storage) before finished).trans storage_refusal

theorem partial_timeout :
    let result := (Source.zeroVal (E := E) (Γ := [.bool]) 6 (.struct .memory name)).run before
    result.1 = .error .timeout ∧ result.2.2.heap.next = 2 := ⟨rfl,rfl⟩

theorem timeout_is_not_stable :
    (Source.zeroVal (E := E) (Γ := [.bool]) 6 (.struct .memory name)).run before ≠
      (Source.zeroVal 16 (.struct .memory name)).run before := by
  intro equal
  have observation : observe ((Source.zeroVal (E := E) (Γ := [.bool]) 6 (.struct .memory name)).run before) =
      observe ((Source.zeroVal (E := E) (Γ := [.bool]) 16 (.struct .memory name)).run before) := congrArg observe equal
  have timed : observe ((Source.zeroVal (E := E) (Γ := [.bool]) 6 (.struct .memory name)).run before) = none := by decide +kernel
  rw [timed,node_observation] at observation
  cases observation

theorem old_and_nonheap :
    let result := (Source.zeroVal (E := E) (Γ := [.bool]) 6 (.struct .memory name)).run before
    result.2.2.heap.get 0 = before.2.heap.get 0 ∧ result.2 = (before.1,{before.2 with heap := result.2.2.heap}) := by
  have extension : AllocationExtension before
      ((Source.zeroVal (E := E) (Γ := [.bool]) 6 (.struct .memory name)).run before).2 :=
    zeroVal_allocates 6 (.struct .memory name) before
  exact ⟨extension.old 0 (by change 0 < 1; decide),extension.frame⟩

theorem wrong_root_rejected :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 16 (.struct .memory name)).run before) ≠ some (5,6) := by
  rw [node_observation]
  decide

#print axioms certificate_inhabited
#print axioms declared_layout
#print axioms node_observation
#print axioms constructor_horizon
#print axioms fields_horizon
#print axioms scalar_default
#print axioms nested_payloads
#print axioms long_observation
#print axioms long_horizon
#print axioms empty_dynamic_default
#print axioms storage_refusal
#print axioms refusal_horizon
#print axioms partial_timeout
#print axioms timeout_is_not_stable
#print axioms old_and_nonheap
#print axioms wrong_root_rejected
end Solidity.Backend.MemoryCopies.SourceDefaultHorizonControls
