import Solidity.Yul.Views.InventoryRealization

namespace Solidity.Yul.Views

theorem heapObj_known {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ) (a : Nat)
    (x : Σ τ,Source.Data E.layout τ) (found : s.2.heap.get a = some x) :
    (Source.heapObj (E := E) (Γ := Γ) a).run s = (.ok x,s) := by
  have state : (Source.EM.st : Source.EM E Γ (Source.St E)).run s = (.ok s.2,s) := by cases s; rfl
  unfold Source.heapObj
  rw [Source.Hoare.run_bind,state]
  simp only []
  rw [found]
  rfl

theorem heapBytes_known {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ) (a : Nat) (bs : List UInt8)
    (found : s.2.heap.get a = some ⟨.string .memory,.string bs⟩ ∨ s.2.heap.get a = some ⟨.bytes .memory,.bytes bs⟩) :
    (Source.heapBytes (E := E) (Γ := Γ) a).run s = (.ok bs,s) := by
  rcases found with found | found
  all_goals rw [Source.heapBytes,Source.Hoare.run_bind,heapObj_known s a _ found]; rfl

theorem indexLoc_known {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ) (F : Source.Fr)
    (a i n : Nat) (τ : Source.STy) (xs : Fin n → Source.Data E.layout τ)
    (found : s.2.heap.get a = some ⟨.array .memory τ none,.array n (fun _ e => nomatch e) xs⟩) (bound : i<n) :
    (Source.indexLoc F (.memRef (τ := .array .memory τ none) rfl a) i).run s = (.ok (.mem a i),s) := by
  unfold Source.indexLoc
  rw [Source.Hoare.run_bind]
  have len : (Source.lengthOf F (.memRef (τ := .array .memory τ none) rfl a) : Source.EM E Γ Nat).run s = (.ok n,s) := by
    unfold Source.lengthOf
    rw [Source.Hoare.run_bind,heapObj_known s a _ found]
    rfl
  rw [len]
  simp only []
  rw [if_pos bound]
  rfl

theorem readLoc_array_known {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ) (F : Source.Fr)
    (a i n : Nat) (τ : Source.STy) (values : Fin n → Source.Val E.layout τ)
    (found : s.2.heap.get a = some ⟨.array .memory τ none,.array n (fun _ e => nomatch e) (fun j => .val (values j))⟩)
    (bound : i<n) : (Source.readLoc F (τ := τ) (.mem a i)).run s = (.ok (values ⟨i,bound⟩),s) := by
  change (Source.memElem a i τ).run s = _
  rw [Source.memElem,Source.Hoare.run_bind,heapObj_known s a _ found]
  simp only []
  rw [dif_pos bound,dif_pos True.intro]
  rfl

theorem readLoc_struct_known {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ) (F : Source.Fr)
    (a i : Nat) (name : Source.DeclName) (fs : Source.DataList E.layout (E.layout.fields name))
    (τ : Source.STy) (v : Source.Val E.layout τ)
    (found : s.2.heap.get a = some ⟨.struct .memory name,.struct fs⟩) (field : fs.nth i τ = .ok (.val v)) :
    (Source.readLoc F (τ := τ) (.mem a i)).run s = (.ok v,s) := by
  change (Source.memElem a i τ).run s = _
  rw [Source.memElem,Source.Hoare.run_bind,heapObj_known s a _ found]
  simp only []
  rw [field]
  rfl

theorem readLoc_fixed_known {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ) (F : Source.Fr)
    (a i n : Nat) (τ : Source.STy) (values : Fin n → Source.Val E.layout τ)
    (found : s.2.heap.get a = some ⟨.array .memory τ (some n),.array n (fun _ eq => (Option.some.inj eq).symm) (fun j => .val (values j))⟩)
    (bound : i<n) : (Source.readLoc F (τ := τ) (.mem a i)).run s = (.ok (values ⟨i,bound⟩),s) := by
  change (Source.memElem a i τ).run s = _
  rw [Source.memElem,Source.Hoare.run_bind,heapObj_known s a _ found]
  simp only []
  rw [dif_pos bound,dif_pos True.intro]
  rfl

end Solidity.Yul.Views
