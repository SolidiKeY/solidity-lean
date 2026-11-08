import Solidity.Backend.MemoryOps.CalldataAgreementChildren
import Solidity.Backend.MemoryOps.CalldataSequenceFixtures

/-! Exact local footprint observations. Actual successful operations provide
bounds; initial interval agreement is derived from target equality, not assumed
as a postcondition. No Source profile or recursive graph semantics is changed. -/
namespace Solidity.Backend.MemoryOps

theorem overwriteSlice_target_eq_iff {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (d : Nat)
    (payload : List (MVal H E)) (hd : d+payload.length ≤ hp.len r a) :
    (overwriteSlice hp r a d payload hd).get r = hp.get r ↔
      ∀ i, i < payload.length → payload[i]? = (MObj.elems a (hp.get r))[d+i]? := by
  constructor
  · intro he i hi
    have h := overwriteSlice_inside hp r a d i payload hd hi
    rw [he] at h
    exact h.symm
  · intro ha
    rw [overwriteSlice_eq_self_of_agrees hp r a d payload hd ha]

set_option backward.isDefEq.respectTransparency false in
theorem boolTransfer_target_eq_iff {D : Source.Layout} {H : HTy} {R : RefTy}
    (c : Source.Calldata D) (off : Nat) (hp : Heap H) (r : HRef H R)
    (a : ArrTy R (.prim .bool)) (s t d : Nat) (out : Heap H)
    (ho : checkedCalldataBools c off hp r a s t d = some out) :
    out.get r = hp.get r ↔ BoolTransferAgrees c off hp r a s t d := by
  obtain ⟨bs,hb,hs,hd,rfl⟩ := boolTransfer_result_lookup c off hp r a s t d out ho
  unfold BoolTransferAgrees
  rw [hb]
  rw [overwriteSlice_target_eq_iff]
  rw [hs.length]
  rfl

/-- The SAME existing immutable table fixes this child's contents at any heap.
No address-injectivity premise is needed to compare the same typed identity. -/
theorem BoolChildRepr.object_eq {D : Source.Layout} {H : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp hq : Heap H}
    {sv : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hi : BoolChildRepr c address hp sv r) (ho : BoolChildRepr c address hq sv r) :
    hq.get r = hp.get r := by
  have hvals : MObj.elems .dyn (hq.get r) = MObj.elems .dyn (hp.get r) := by
    apply List.ext_getElem?
    intro i
    cases he : (MObj.elems .dyn (hp.get r))[i]? with
    | some b => exact (ho.read_iff i b).mp ((hi.read_iff i b).mpr he)
    | none =>
      cases hf : (MObj.elems .dyn (hq.get r))[i]? with
      | none => rfl
      | some b =>
        have hc := (hi.read_iff i b).mp ((ho.read_iff i b).mpr hf)
        rw [he] at hc
        cases hc
  apply Subtype.ext
  simpa only [MObj.elems_dyn] using hvals

theorem BoolChildRepr.at_heap_iff {D : Source.Layout} {H : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hi : BoolChildRepr c address hp sv r) (out : Heap H) :
    BoolChildRepr c address out sv r ↔ out.get r = hp.get r := by
  constructor
  · exact hi.object_eq
  · intro he
    exact ⟨hi.1,by rw [he]; exact hi.2⟩

/-- Exact preservation for an actual aliased Boolean transfer. The immutable
child table and the transfer's source table may differ. -/
theorem BoolChildRepr.alias_transfer_iff {D : Source.Layout} {H : HTy}
    {table : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D BoolChildTy} {child : HRef H BoolChildRef}
    (hi : BoolChildRepr table address hp sv child)
    (c : Source.Calldata D) (off s t d : Nat) (out : Heap H)
    (ho : checkedCalldataBools c off hp child .dyn s t d = some out) :
    BoolChildRepr table address out sv child ↔ BoolTransferAgrees c off hp child .dyn s t d := by
  rw [hi.at_heap_iff out]
  exact boolTransfer_target_eq_iff c off hp child .dyn s t d out ho

/-- The uint step cannot modify the Boolean child. Hence exact alias
preservation depends on the INITIAL actual Boolean interval, even though the
final whole heap can materially differ through the uint operation. -/
theorem BoolChildRepr.mixed_alias_iff {D : Source.Layout} {H : HTy} {Q : RefTy}
    {table : Source.Calldata D} {address : Nat → Nat} {hp : Heap H}
    {sv : Source.Data D BoolChildTy} {child : HRef H BoolChildRef}
    (hi : BoolChildRepr table address hp sv child)
    (c : Source.Calldata D) (off : Nat) (c' : Source.Calldata D) (off' : Nat)
    (s t d : Nat) (q : HRef H Q) (b : ArrTy Q (.prim .uint)) (u v f : Nat)
    (out : Heap H)
    (ho : checkedBoolUintSequence c off c' off' hp child .dyn s t d q b u v f = some out) :
    BoolChildRepr table address out sv child ↔ BoolTransferAgrees c off hp child .dyn s t d := by
  obtain ⟨mid,hfirst,hsecond⟩ := (checkedBoolUintSequence_some_iff c off c' off' hp child .dyn s t d q b u v f out).mp ho
  have hf : out.get child = mid.get child := uintTransfer_frame_or_empty c' off' mid q b u v f out hsecond child
    (Or.inl (bool_uint_transfer_ne child .dyn q b).symm)
  rw [hi.at_heap_iff out,hf]
  exact boolTransfer_target_eq_iff c off hp child .dyn s t d mid hfirst

/-- info: 'Solidity.Backend.MemoryOps.overwriteSlice_target_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overwriteSlice_target_eq_iff
/-- info: 'Solidity.Backend.MemoryOps.boolTransfer_target_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boolTransfer_target_eq_iff
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.object_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms BoolChildRepr.object_eq
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.at_heap_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms BoolChildRepr.at_heap_iff
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.alias_transfer_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.alias_transfer_iff
/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.mixed_alias_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.mixed_alias_iff
namespace ExactAgreementControls
open SequenceFixtures
private abbrev B := BoolChildRef
private abbrev N : RefTy := .array (.prim .uint)
private abbrev H : HTy := [B,N]
private def child : HRef H B := ⟨0,rfl⟩
private def q : HRef H N := ⟨1,rfl⟩
private def values (n : Nat) := [false,true,false] ++ List.replicate n false
set_option backward.isDefEq.respectTransparency false in
private def hp (n : Nat) (hn : n+3 < 2^256) : Heap H :=
  (⟨values n,by simp only [values,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,
   ⟨[zero,seven],by decide⟩,())
private def sv : Source.Data D BoolChildTy := .val (.cdRef rfl 7 0)
private theorem initial (n : Nat) (hn : n+3 < 2^256) :
    BoolChildRepr (bools (values n)) (fun _ => 7) (hp n hn) sv child := by
  refine ⟨rfl,?_⟩
  simp only [MObj.elems_dyn]; rfl
set_option backward.isDefEq.respectTransparency false in
private theorem hcap (n : Nat) (hn : n+3 < 2^256) :
    1+([true] : List Bool).length ≤ (hp n hn).len child .dyn := by
  simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,child,values,
    List.length_append,List.length_cons,List.length_nil,List.length_replicate]
  omega
private def mid (n : Nat) (hn : n+3 < 2^256) := overwriteSlice (hp n hn) child .dyn 1 [true] (hcap n hn)
set_option backward.isDefEq.respectTransparency false in
private theorem reached (n : Nat) (hn : n+3 < 2^256) :
    checkedCalldataBools (bools (values n)) 7 (hp n hn) child .dyn 1 2 1 = some (mid n hn) := by
  have h := checkedCalldataBools_some (bool_repr (values n)) (hp n hn) child .dyn 1 2 1
    ⟨by decide,by simp only [values,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩
    (by simpa only [bool_values,values,List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,List.length_cons,List.length_nil] using hcap n hn)
  simpa only [mid,bool_values,values,List.cons_append,List.nil_append,Nat.reduceSub,
    List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero] using h

/-- Runtime-size inhabited same-content alias: the exact iff is applied to an
actual successful operation and the initial relation comes from its real table. -/
theorem accepted (n : Nat) (hn : n+3 < 2^256) :
    checkedCalldataBools (bools (values n)) 7 (hp n hn) child .dyn 1 2 1 = some (mid n hn) ∧
    BoolChildRepr (bools (values n)) (fun _ => 7) (mid n hn) sv child := by
  refine ⟨reached n hn,?_⟩
  exact ((initial n hn).alias_transfer_iff (bools (values n)) 7 1 2 1 (mid n hn) (reached n hn)).mpr
    ((initial n hn).self_agrees 1 2)

set_option backward.isDefEq.respectTransparency false in
/-- Actual successful wrong-value transfer fails the exact initial-agreement
criterion and the immutable child correspondence, for every runtime tail. -/
theorem rejected (n : Nat) (hn : n+3 < 2^256) :
    ∃ out, checkedCalldataBools (bools [true]) 7 (hp n hn) child .dyn 0 1 0 = some out ∧
      ¬ BoolTransferAgrees (bools [true]) 7 (hp n hn) child .dyn 0 1 0 ∧
      ¬ BoolChildRepr (bools (values n)) (fun _ => 7) out sv child := by
  have hd : 0+([true] : List Bool).length ≤ (hp n hn).len child .dyn := by
    have h := hcap n hn; omega
  let out := overwriteSlice (hp n hn) child .dyn 0 [true] hd
  have ho : checkedCalldataBools (bools [true]) 7 (hp n hn) child .dyn 0 1 0 = some out := by
    have h := checkedCalldataBools_some (bool_repr [true]) (hp n hn) child .dyn 0 1 0 ⟨by decide,by decide⟩
      (by simpa only [bool_values,List.drop_zero,List.take_succ_cons,List.take_zero,
        List.length_cons,List.length_nil,Nat.sub_zero,Nat.zero_add] using hd)
    simpa only [bool_values,List.drop_zero,List.take_succ_cons,List.take_zero,Nat.reduceSub] using h
  have ha : ¬ BoolTransferAgrees (bools [true]) 7 (hp n hn) child .dyn 0 1 0 := by
    intro h
    unfold BoolTransferAgrees at h
    rw [calldataBools_lookup (bool_repr [true])] at h
    have he := h 0 (by decide)
    have hfalse : (MObj.elems .dyn ((hp n hn).get child))[0]? = some false := by
      simp only [MObj.elems_dyn]; rfl
    rw [Nat.add_zero,hfalse] at he
    cases he
  refine ⟨out,ho,ha,?_⟩
  intro hf
  exact ha (((initial n hn).alias_transfer_iff (bools [true]) 7 0 1 0 out ho).mp hf)

set_option backward.isDefEq.respectTransparency false in
/-- Both Boolean values execute: false preserves the original child, true
refutes its correspondence. The actual second uint step changes zero to max,
with complete ordered uint and child outputs, for every intrinsic runtime tail. -/
theorem mixed_actual (n : Nat) (hn : n+3 < 2^256) (value : Bool) :
    ∃ out, checkedBoolUintSequence (bools [value]) 7 (uints [maximum]) 9 (hp n hn)
      child .dyn 0 1 0 q .dyn 0 1 0 = some out ∧
      (BoolChildRepr (bools (values n)) (fun _ => 7) out sv child ↔ value = false) ∧
      (MObj.elems .dyn (out.get q)).map (fun v : U => v.val) = [((2^256-1 : Nat) : Int),7] ∧
      MObj.elems .dyn (out.get child) = [value,true,false] ++ List.replicate n false ∧
      out.get q ≠ (hp n hn).get q := by
  have hd : 0+([value] : List Bool).length ≤ (hp n hn).len child .dyn := by
    have h := hcap n hn; simp only [List.length_cons,List.length_nil] at *; omega
  let first := overwriteSlice (hp n hn) child .dyn 0 [value] hd
  have hfirst : checkedCalldataBools (bools [value]) 7 (hp n hn) child .dyn 0 1 0 = some first := by
    have h := checkedCalldataBools_some (bool_repr [value]) (hp n hn) child .dyn 0 1 0 ⟨by decide,by simp only [List.length_cons,List.length_nil]; omega⟩
      (by simpa only [bool_values,List.drop_zero,List.take_succ_cons,List.take_zero,
        List.length_cons,List.length_nil,Nat.sub_zero,Nat.zero_add] using hd)
    simpa only [bool_values,List.drop_zero,List.take_succ_cons,List.take_zero,Nat.reduceSub] using h
  have hq : first.get q = (hp n hn).get q := overwriteSlice_frame _ child q .dyn 0 [value] hd (by decide)
  have hu : 0+([maximum] : List U).length ≤ first.len q .dyn := by
    rw [overwriteSlice_all_len]; simp only [Heap.len,MObj.elems_dyn,Heap.get,Objs.get,hp,q,List.length_cons,List.length_nil]; omega
  let out := overwriteSlice first q .dyn 0 [maximum] hu
  have ho : checkedBoolUintSequence (bools [value]) 7 (uints [maximum]) 9 (hp n hn)
      child .dyn 0 1 0 q .dyn 0 1 0 = some out := by
    unfold checkedBoolUintSequence
    rw [hfirst]
    have h := checkedCalldataUints_some (uint_repr [maximum]) first q .dyn 0 1 0 ⟨by decide,by decide⟩
      (by simpa only [calldataUint_values,List.drop_zero,List.take_succ_cons,List.take_zero,
        List.length_cons,List.length_nil,Nat.sub_zero,Nat.zero_add] using hu)
    simpa only [Option.bind_some,calldataUint_values,List.drop_zero,List.take_succ_cons,List.take_zero,Nat.reduceSub] using h
  have ha : BoolTransferAgrees (bools [value]) 7 (hp n hn) child .dyn 0 1 0 ↔ value = false := by
    unfold BoolTransferAgrees
    rw [calldataBools_lookup (bool_repr [value])]
    constructor
    · intro h
      have h0 := h 0 (by decide)
      simp only [MObj.elems_dyn] at h0
      exact Option.some.inj h0
    · intro hv
      subst value
      intro i hi
      have he : i = 0 := by omega
      subst i
      simp only [MObj.elems_dyn]; rfl
  have hv : (MObj.elems .dyn (out.get q)).map (fun v : U => v.val) = [((2^256-1 : Nat) : Int),7] := by
    rw [overwriteSlice_elems,hq]
    simp only [MObj.elems_dyn]; rfl
  refine ⟨out,ho,((initial n hn).mixed_alias_iff (bools [value]) 7 (uints [maximum]) 9 0 1 0 q .dyn 0 1 0 out ho).trans ha,hv,?_,?_⟩
  · rw [overwriteSlice_frame first q child .dyn 0 [maximum] hu (by decide),overwriteSlice_elems]
    simp only [MObj.elems_dyn]; rfl
  · intro he
    have h := congrArg (fun obj : MObj H N => (MObj.elems .dyn obj).map (fun v : U => v.val)) he
    rw [hv] at h
    have old : (MObj.elems .dyn ((hp n hn).get q)).map (fun v : U => v.val) = [0,7] := by
      simp only [MObj.elems_dyn]; rfl
    rw [old] at h
    exact (by decide : ([((2^256-1 : Nat) : Int),7] : List Int) ≠ [0,7]) h

/-- info: 'Solidity.Backend.MemoryOps.ExactAgreementControls.mixed_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mixed_actual
/-- info: 'Solidity.Backend.MemoryOps.ExactAgreementControls.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms accepted
/-- info: 'Solidity.Backend.MemoryOps.ExactAgreementControls.rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rejected
end ExactAgreementControls
end Solidity.Backend.MemoryOps
