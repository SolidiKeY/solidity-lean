import Solidity.Backend.MemoryCopies.GuardedDefaultDeclaration
import Solidity.Backend.MemoryCopies.HeapContents
import Solidity.Evm.MemoryObjectArrayExamples

/-! Actual selected declaration bodies, real local bindings and populated
initial ownership. Saturated word-model refusal is not a Source panic claim. -/
namespace Solidity.Backend.MemoryCopies.GuardedDefaultDeclarationControls
open Evm Evm.Memory Semantics

private structure Input where
  contract : Contract
  context : Ctx
  frag : Frag context
  state : State contract context
  base : Nat → Fin W
  machine : Machine
  represented : Objects.StateRepr 1 1 8 frag state base machine
  allocator : Objects.AllocatorRepr state.heap base 8 (wmod 40) machine
private def input : Input := ⟨_,_,_,_,_,_,ObjectArrayExamples.initial_repr,ObjectArrayExamples.initial_allocator⟩
private def chosen (dimensions : List Nat) :
    SelectedCheckedDefault (nestedArrayType (.prim .uint) dimensions) (nested_mapFree (.prim .uint) dimensions) :=
  checkedNestedDefault (.prim .uint) dimensions (nested_mapFree (.prim .uint) dimensions)
private def token : SelectedCheckedDefault (.struct "Token") rfl := selectedCheckedDefault _ rfl rfl
private def declaration {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (child : SelectedCheckedDefault root memory) (defaultable : (Ty.ref root).defaultOkS = true) :
    SelectedDefaultDeclaration (C := input.contract) 1 input.frag root (.user "fresh") defaultable memory :=
  selectedDefaultDeclaration 1 input.frag root (.user "fresh") defaultable memory (by decide)
    (by rw [child.selected]; rfl)
private theorem local_room {root : RefTy} (defaultable : (Ty.ref root).defaultOkS = true)
    (memory : (Ty.ref root).mapFree = true) :
    1 + frameNeedStmt (Stmt.declMem (C := input.contract) (Γ := input.context) root
      (.user "fresh") none defaultable memory) ≤ 8 := by
  change 1 + max 3 (max 4 0) ≤ 8
  decide

private theorem actual_code {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (child : SelectedCheckedDefault root memory) (defaultable : (Ty.ref root).defaultOkS = true) :
    (declaration child defaultable).compiled.code = child.builder.code ++ [.mstore 4] := by
  cases root with
  | array element =>
    have same : child.builder = Objects.DefaultBuilder.empty element memory :=
      Option.some.inj (child.selected.symm.trans rfl)
    rw [same]
    cases element with
    | prim primitive => rfl
    | ref reference => cases reference <;> rfl
  | struct name =>
    simp only [declaration, selectedDefaultDeclaration, Construction.compileStmt,
      Objects.compileStmt, dif_pos (show 0 < 1 by decide), child.selected, Option.bind_some]
    rfl
  | fixed element count =>
    simp only [declaration, selectedDefaultDeclaration, Construction.compileStmt,
      Objects.compileStmt, dif_pos (show 0 < 1 by decide), child.selected, Option.bind_some]
    rfl
  | mapping key value => cases memory

private def observe : Evm.Out → Option (Nat × Nat × List Evm.Word × Nat)
  | .ok machine _ => match machine.mem 4, machine.mem 0, machine.mem 17 with
    | .val root, .val cursor, .val old => some (root.val,cursor.val,machine.stack,old.val)
    | _, _, _ => none
  | _ => none

private theorem observation {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (child : SelectedCheckedDefault root memory) (defaultable : (Ty.ref root).defaultOkS = true)
    (fits : 40 + ReferenceDefaults.defaultCells (.ref root) < W) :
    observe (run (guardedDefaultDeclarationCode (declaration child defaultable)) input.machine) =
      some (40,40 + ReferenceDefaults.defaultCells (.ref root),[w[77]],7) := by
  obtain ⟨base,target,ran,allocated,_,_,shape,below,_⟩ :=
    child.builder.correct input.state.heap input.base 8 (wmod 40) input.machine input.allocator fits
  have stack : target.stack = input.machine.stack := by rw [shape]
  have actualFits : (wmod 40).val + ReferenceDefaults.defaultCells (.ref root) < W := fits
  rw [guarded_default_declaration_run child (declaration child defaultable) input.state input.base
    (wmod 40) input.machine input.allocator, if_pos actualFits, actual_code child defaultable, run_append_ok ran]
  change observe (.ok (writeMachine target 4 (.val (wmod 40))) 0) = _
  simp only [observe, writeMachine, upd, ↓reduceIte]
  rw [allocated.free.cell,below 17 (by decide) (by decide),stack]
  rfl

theorem certificate_inhabited : GuardedDefaultDeclarationCertificate := guardedDefaultDeclaration

theorem selected_body : Construction.compileStmt (C := input.contract) 1 input.frag
    (.declMem (.array (.prim .uint)) (.user "fresh") none rfl rfl) =
      some (declaration (chosen []) rfl).compiled := (declaration (chosen []) rfl).selected

theorem empty_dynamic :
    observe (run (guardedDefaultDeclarationCode (declaration (chosen []) rfl)) input.machine) =
      some (40,41,[w[77]],7) := observation (chosen []) rfl (by decide)

theorem nested_two_three :
    observe (run (guardedDefaultDeclarationCode (declaration (chosen [2,3]) (by decide))) input.machine) =
      some (40,54,[w[77]],7) := observation (chosen [2,3]) (by decide) (by decide)

theorem long_fixed :
    observe (run (guardedDefaultDeclarationCode (declaration (chosen [64]) (by decide))) input.machine) =
      some (40,168,[w[77]],7) := observation (chosen [64]) (by decide) (by decide)

theorem token_default :
    observe (run (guardedDefaultDeclarationCode (declaration token rfl)) input.machine) =
      some (40,41,[w[77]],7) := observation token rfl (by decide)

theorem full_declaration_state :
    ∃ fits, GuardedDefaultDeclarationSuccess (L := 1) (frame := 8)
      (declaration (chosen [2,3]) (by decide)) input.state input.base (wmod 40) input.machine fits :=
  ⟨by decide,guarded_default_declaration_success (chosen [2,3]) _ input.state input.base
    (wmod 40) input.machine input.represented input.allocator (by decide) (local_room _ _) (by decide)⟩

private def emptyChild : SVal (.ref (.array (.prim .uint))) := .array .nil .nil (by decide)
private def expectedChildren : SVal (.ref (nestedArrayType (.prim .uint) [2,3])) :=
  .fixed (SVec.replicate (.fixed (SVec.replicate emptyChild 3)) 2)

theorem full_new_contents :
    ∃ fits, GuardedDefaultDeclarationSuccess (L := 1) (frame := 8)
      (declaration (chosen [2,3]) (by decide)) input.state input.base (wmod 40) input.machine fits ∧
      let grown := input.state.heap.allocDefault (nestedArrayType (.prim .uint) [2,3])
        (nested_mapFree (.prim .uint) [2,3])
      MVal.copyMToSt grown.heap grown.val = expectedChildren := by
  obtain ⟨fits,execution⟩ := full_declaration_state
  refine ⟨fits,execution,?_⟩
  exact ((storageHeapContents (SVal.dflt (.ref (nestedArrayType (.prim .uint) [2,3])))
    (nested_mapFree (.prim .uint) [2,3])).contents input.state.heap).trans (by
      simp only [nestedArrayType, SVal.dflt_fixed, SVal.dflt_array, SVal.strip_fixed,
        SVal.strip_array, SVec.strip_cons, SVec.strip_nil, SVec.replicate, expectedChildren, emptyChild])

theorem unsupported_reference_field :
    (Construction.compileStmt (C := input.contract) 1 input.frag
      (.declMem (.struct "WithChild{items:bool[]}") (.user "fresh") none (by decide) (by decide))).isSome = false := by
  decide +kernel

theorem adapter_is_not_selected_body :
    guardedDefaultDeclarationCode (declaration (chosen []) rfl) ≠
      (declaration (chosen []) rfl).compiled.code := by
  intro same
  have lengths : (defaultCapacityGuard (ReferenceDefaults.defaultCells
      (.ref (nestedArrayType (.prim .uint) [])))).length +
      (declaration (chosen []) rfl).compiled.code.length =
      (declaration (chosen []) rfl).compiled.code.length := by
    simpa only [guardedDefaultDeclarationCode, List.length_append] using congrArg List.length same
  have positive : 0 < (defaultCapacityGuard (ReferenceDefaults.defaultCells
      (.ref (nestedArrayType (.prim .uint) [])))).length := by decide
  omega

private def moved (cursor : Fin W) : Machine := writeMachine input.machine 0 (.val cursor)
private theorem moved_allocator (cursor : Fin W) (above : 40 ≤ cursor.val) :
    Objects.AllocatorRepr input.state.heap input.base 8 cursor (moved cursor) := by
  refine ⟨input.allocator.heap.localWrite 0 (by decide) _,⟨by decide,by omega,rfl,?_⟩,?_⟩
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans
      (input.allocator.free.zero address (by change 40 ≤ address; omega))
  · intro R reference
    have live : (input.base reference.id).val + Objects.cells input.state.heap reference ≤ 40 :=
      input.allocator.live reference
    omega
private theorem moved_represented (cursor : Fin W) :
    Objects.StateRepr 1 1 8 input.frag input.state input.base (moved cursor) := by
  refine ⟨input.represented.core.congrMem ?_, input.represented.heap.localWrite 0 (by decide) _,
    ?_, input.represented.locals⟩
  · intro address lower upper
    exact upd_other _ _ (by change address ≠ 0; omega)
  · intro R index
    obtain ⟨reference,source,word⟩ := input.represented.pointers index
    refine ⟨reference,source,?_⟩
    have lower : 1 ≤ lvl 1 index := le_lvl 1 index
    exact (upd_other _ _ (by change lvl 1 index ≠ 0; omega)).trans word

private theorem saturated_above : 40 ≤ wMax.val := by
  change 40 ≤ W - 1
  have large : 128 < W := by decide
  omega

theorem saturated_refusal :
    Objects.StateRepr 1 1 8 input.frag input.state input.base (moved wMax) ∧
    Objects.AllocatorRepr input.state.heap input.base 8 wMax (moved wMax) ∧
    run (guardedDefaultDeclarationCode (declaration (chosen []) rfl)) (moved wMax) = .revert := by
  refine ⟨moved_represented wMax,moved_allocator wMax saturated_above,?_⟩
  rw [guarded_default_declaration_run (chosen []) (declaration (chosen []) rfl) input.state input.base
    wMax (moved wMax) (moved_allocator wMax saturated_above)]
  apply if_neg
  change ¬ (W - 1) + 1 < W
  have positive : 0 < W := W_pos
  omega

theorem wrong_binding_rejected :
    observe (run (guardedDefaultDeclarationCode (declaration (chosen []) rfl)) input.machine) ≠
      some (16,41,[w[77]],7) := by
  rw [empty_dynamic]
  decide

/--
info: 'Solidity.Backend.MemoryCopies.GuardedDefaultDeclarationControls.certificate_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms certificate_inhabited
/--
info: 'Solidity.Backend.MemoryCopies.GuardedDefaultDeclarationControls.selected_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms selected_body
/--
info: 'Solidity.Backend.MemoryCopies.GuardedDefaultDeclarationControls.empty_dynamic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms empty_dynamic
/--
info: 'Solidity.Backend.MemoryCopies.GuardedDefaultDeclarationControls.nested_two_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nested_two_three
/--
info: 'Solidity.Backend.MemoryCopies.GuardedDefaultDeclarationControls.long_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms long_fixed
/--
info: 'Solidity.Backend.MemoryCopies.GuardedDefaultDeclarationControls.token_default' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms token_default
/--
info: 'Solidity.Backend.MemoryCopies.GuardedDefaultDeclarationControls.full_declaration_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms full_declaration_state
/--
info: 'Solidity.Backend.MemoryCopies.GuardedDefaultDeclarationControls.full_new_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms full_new_contents
/--
info: 'Solidity.Backend.MemoryCopies.GuardedDefaultDeclarationControls.unsupported_reference_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms unsupported_reference_field
/--
info: 'Solidity.Backend.MemoryCopies.GuardedDefaultDeclarationControls.adapter_is_not_selected_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms adapter_is_not_selected_body
/--
info: 'Solidity.Backend.MemoryCopies.GuardedDefaultDeclarationControls.saturated_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms saturated_refusal
/--
info: 'Solidity.Backend.MemoryCopies.GuardedDefaultDeclarationControls.wrong_binding_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms wrong_binding_rejected
end Solidity.Backend.MemoryCopies.GuardedDefaultDeclarationControls
