import Solidity.Backend.MemoryCopies.SourceFields

/-! Declared heterogeneous and dynamically guarded recursive Source structs. -/
namespace Solidity.Backend.MemoryCopies.SourceFieldsControls
private def basketDecl : Source.Decl :=
  ⟨.struct,"Basket",none,true,
    .struct "Basket" (.structMember (.elem (.int false 256 (by decide))) "tag")
      (.cons (.structMember (.array (.elem .bytes) (.some (.lit (.num (.dec 2 0 0))))) "chunks")
        (.cons (.structMember (.elem .string) "label")
          (.cons (.structMember (.array (.elem .bytes) .none) "items") .nil)))⟩
private def nodeDecl : Source.Decl :=
  ⟨.struct,"Node",none,true,
    .struct "Node" (.structMember (.array (.userType ⟨"Node",[]⟩) .none) "children")
      (.cons (.structMember (.elem .bytes) "payload") .nil)⟩
private def E : Source.Env := ⟨[basketDecl,nodeDecl]⟩
private def basketName : Source.DeclName := ⟨none,"Basket"⟩
private def nodeName : Source.DeclName := ⟨none,"Node"⟩
private def initial : Source.St E :=
  ⟨⟨⟨fun _ => Source.Account.empty _⟩,Source.Transient.empty,[]⟩,
    (Source.Heap.empty.alloc ⟨.bool,.val (.bool true)⟩).1,
    [],[(⟨13,by decide⟩,[1,2])],⟨[.bool],.cons (.bool false) .nil⟩⟩
private def before : Source.EMState E [.bool] := (.cons (.bool true) .nil,initial)
private def basketFields : SourceFieldsConstruction E (E.layout.fields basketName) :=
  .cons (.pureDefault (.int 0 Source.IntTy.u256.zero_mem) rfl)
    (.cons ((bytesLeaf E).construction.fixed 2).value
      (.cons (stringLeaf E).construction.value
        (.cons (dynamicLeaf E (.bytes .memory)).construction.value (.nil E))))
private def basket : SourceConstructionCertificate E (.struct .memory basketName) rfl :=
  basketFields.structDefault basketName
private def nodeFields : SourceFieldsConstruction E (E.layout.fields nodeName) :=
  .cons (dynamicLeaf E (.struct .memory nodeName)).construction.value
    (.cons (bytesLeaf E).construction.value (.nil E))
private def node : SourceConstructionCertificate E (.struct .memory nodeName) rfl :=
  nodeFields.structDefault nodeName
private def observe {τ : Source.STy}
    (result : Source.R (Source.Val E.layout τ) × Source.EMState E [.bool]) : Option (Nat × Nat) :=
  match result.1 with
  | .ok (.memRef _ root) => some (root,result.2.2.heap.next)
  | _ => none

theorem declared_layout : E.layout.fields basketName =
    [.int .u256,.array .memory (.bytes .memory) (some 2),.string .memory,
      .array .memory (.bytes .memory) none] := rfl

theorem declared_recursive_layout : E.layout.fields nodeName =
    [.array .memory (.struct .memory nodeName) none,.bytes .memory] := rfl

theorem actual_observation {τ : Source.STy} {memory : τ.loc? = some .memory}
    (constructor : SourceConstructionCertificate E τ memory) (slack : Nat) :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) (constructor.horizon + slack) τ).run before) =
      some (constructor.objects,1 + constructor.objects) := by
  obtain ⟨after,root,data,certificate,frontier,last⟩ := constructor.execution before slack
  rw [certificate.execution]
  change some (root,after.2.heap.next) = _
  change after.2.heap.next = 1 + constructor.objects at frontier
  have identity : root = constructor.objects := by omega
  rw [identity,frontier]

theorem mixed_default :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 18 (.struct .memory basketName)).run before) =
      some (6,7) := actual_observation basket 0

/-- A declared self-reference terminates here because its dynamic array default
is empty. No general recursive graph admission or copy theorem is asserted. -/
theorem recursive_dynamic_default :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 9 (.struct .memory nodeName)).run before) =
      some (3,4) := actual_observation node 0

theorem actual_child_contents :
    let reached := ((Source.zeroVal (E := E) (Γ := [.bool]) 18 (.struct .memory basketName)).run before).2
    reached.2.heap.get 0 = before.2.heap.get 0 ∧
      reached.2.heap.get 1 = some ⟨.bytes .memory,Source.Data.bytes []⟩ ∧
      reached.2.heap.get 2 = some ⟨.bytes .memory,Source.Data.bytes []⟩ ∧
      reached.2.heap.get 4 = some ⟨.string .memory,Source.Data.string []⟩ := ⟨rfl,rfl,rfl,rfl⟩

theorem populated_certificate :
    ∃ after root data, SourceDefaultCertificate 18 (.struct .memory basketName) rfl before after root data ∧
      after = (before.1,{before.2 with heap := after.2.heap}) := by
  obtain ⟨after,root,data,certificate,_,_⟩ := basket.execution before 0
  exact ⟨after,root,data,certificate,certificate.frame⟩

/-- Low horizon retains the already allocated recursive-array child. -/
theorem recursive_timeout :
    let result := (Source.zeroVal (E := E) (Γ := [.bool]) 5 (.struct .memory nodeName)).run before
    result.1 = .error .timeout ∧ result.2.2.heap.next = 2 := ⟨rfl,rfl⟩

theorem wrong_root_rejected :
    observe ((Source.zeroVal (E := E) (Γ := [.bool]) 18 (.struct .memory basketName)).run before) ≠
      some (5,6) := by
  rw [mixed_default]
  decide

#print axioms declared_layout
#print axioms declared_recursive_layout
#print axioms actual_observation
#print axioms mixed_default
#print axioms recursive_dynamic_default
#print axioms actual_child_contents
#print axioms populated_certificate
#print axioms recursive_timeout
#print axioms wrong_root_rejected
end Solidity.Backend.MemoryCopies.SourceFieldsControls
