import Solidity.Yul.Views.InventoryControls

namespace Solidity.Yul.Views.Controls

theorem readJointAlias_known (s : Source.EMState mixedEnv [mixedArrayTy,mixedArrayTy]) (first : Bool) (index horizon root child n : Nat)
    (values : Fin n → Source.Val mixedLayout (.bytes .memory)) (bs : List UInt8)
    (reference : s.1.get (if first then .here else .there .here) = .memRef rfl root)
    (found : s.2.heap.get root = some ⟨mixedArrayTy,dynamicMemberData mixedLayout (.bytes .memory) n values⟩)
    (bound : index<n) (element : values ⟨index,bound⟩ = .memRef rfl child)
    (childFound : s.2.heap.get child = some ⟨.string .memory,.string bs⟩) :
    (readJointAlias first index horizon).run s = (.ok bs,s) := by
  have locals : (Source.EM.locals : Source.EM mixedEnv [mixedArrayTy,mixedArrayTy] _).run s = (.ok s.1,s) := by cases s; rfl
  unfold readJointAlias
  rw [Source.Hoare.run_bind,locals]
  simp only []
  rw [reference,Source.Hoare.run_bind,indexLoc_known s mixedReadFrame root index n (.bytes .memory) _ found bound]
  simp only []
  rw [Source.Hoare.run_bind,readLoc_array_known s mixedReadFrame root index n (.bytes .memory) values found bound]
  simp only []
  rw [element]
  exact heapBytes_known s child bs (Or.inl childFound)

theorem readMixedMemberBytes_known (s : Source.EMState mixedEnv [.bytes .memory,.string .memory,mixedArrayTy,.struct .memory mixedName])
    (member horizon child : Nat) (fs : Source.DataList mixedLayout (mixedLayout.fields mixedName)) (bs : List UInt8)
    (found : s.2.heap.get 3 = some ⟨.struct .memory mixedName,.struct fs⟩)
    (field : fs.nth member (.bytes .memory) = .ok (.val (.memRef rfl child)))
    (childFound : s.2.heap.get child = some ⟨.string .memory,.string bs⟩) :
    (readMixedMemberBytes member horizon).run s = (.ok bs,s) := by
  unfold readMixedMemberBytes
  rw [Source.Hoare.run_bind,readLoc_struct_known s mixedReadFrame 3 member mixedName fs (.bytes .memory) (.memRef rfl child) found field]
  exact heapBytes_known s child bs (Or.inl childFound)

theorem inventory_actual_alias_reads (horizon : Nat) :
    (readJointAlias true 0 horizon).run inventoryAliasAfter = (.ok inventoryNewString,inventoryAliasAfter) ∧
    (readJointAlias false 1 horizon).run inventoryAliasAfter = (.ok inventoryNewString,inventoryAliasAfter) ∧
    (readMixedMemberBytes 2 horizon).run inventoryAfter = (.ok inventoryNewString,inventoryAfter) ∧
    (readMixedMemberBytes 3 horizon).run inventoryAfter = (.ok inventoryNewString,inventoryAfter) := by
  exact ⟨readJointAlias_known inventoryAliasAfter true 0 horizon 4 1 2 inventoryRValues inventoryNewString rfl inventory_cell4 (by decide) rfl inventory_cell1,
    readJointAlias_known inventoryAliasAfter false 1 horizon 4 1 2 inventoryRValues inventoryNewString rfl inventory_cell4 (by decide) rfl inventory_cell1,
    readMixedMemberBytes_known inventoryAfter 2 horizon 1 allChangedFields inventoryNewString inventory_cell3 rfl inventory_cell1,
    readMixedMemberBytes_known inventoryAfter 3 horizon 1 allChangedFields inventoryNewString inventory_cell3 rfl inventory_cell1⟩

theorem inventory_actual_bytes (horizon : Nat) :
    (Source.bytesOfRV (E := mixedEnv) mixedReadFrame horizon (.val (.memRef (τ := .bytes .memory) rfl 0))).run inventoryAfter = (.ok inventoryNewBytes,inventoryAfter) :=
  heapBytes_known inventoryAfter 0 inventoryNewBytes (Or.inr inventory_cell0)

def inventoryUValues : Fin 2 → Source.Val mixedLayout (.int Source.IntTy.u256) :=
  Fin.cases (uintValueOfWord mixedLayout 7) (Fin.cases (uintValueOfWord mixedLayout 42) Fin.elim0)

theorem inventory_cell2 : inventoryRealized.heap.get 2 = some ⟨.array .memory (.int Source.IntTy.u256) (some 2),
    memberArrayData mixedLayout (.int Source.IntTy.u256) (some 2) 2 (fun _ eq => (Option.some.inj eq).symm) inventoryUValues⟩ := rfl

theorem inventory_actual_bytes_and_string (horizon : Nat) :
    (Source.bytesOfRV (E := mixedEnv) mixedReadFrame horizon (.val (.memRef (τ := .bytes .memory) rfl 0))).run inventoryAfter = (.ok inventoryNewBytes,inventoryAfter) ∧
    (Source.readLoc (E := mixedEnv) mixedReadFrame (τ := .int Source.IntTy.u256) (.mem 2 1)).run inventoryAfter =
      (.ok (uintValueOfWord mixedLayout 42),inventoryAfter) := by
  have scalar := readLoc_fixed_known inventoryAfter mixedReadFrame 2 1 2 (.int Source.IntTy.u256) inventoryUValues inventory_cell2 (by decide)
  have value : inventoryUValues ⟨1,by decide⟩ = uintValueOfWord mixedLayout 42 := rfl
  rw [value] at scalar
  exact ⟨inventory_actual_bytes horizon,scalar⟩

end Solidity.Yul.Views.Controls
