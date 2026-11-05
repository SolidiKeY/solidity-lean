import Solidity.Calculus.SolkeyAgreementH28.Freshness

/-! Inhabited kernel controls for exactly the selected clauses. -/
namespace Solidity.SolkeyAgreementH28.Controls
open Semantics (structDef)

def z : PrimTy.uint.Denote := PrimTy.dflt .uint
def one : PrimTy.uint.Denote := ⟨1, by decide⟩
def hp : Heap [.array Ty.uint] := (⟨[z], by decide⟩, ())
def hp1 : Heap [.array Ty.uint] := (⟨[one], by decide⟩, ())
def m : Grown [] (fun _ => Unit) := ⟨List.nil_prefix, hp, ()⟩
def m1 : Grown [] (fun _ => Unit) := ⟨List.nil_prefix, hp1, ()⟩
def at0 : MAddrT Ty.uint := .index 0 .dyn z

theorem index_primitive : m.writeT at0 one = some m1 := by with_unfolding_all rfl
theorem index_read_changed : m1.readId at0 = some one ∧ m.readId at0 = some z := by
  exact ⟨by with_unfolding_all rfl, by with_unfolding_all rfl⟩
theorem write_reverse : Fresh m.H' 1 → Fresh m1.H' 1 := (newFromWrite index_primitive 1).2
theorem write_forward : Fresh m1.H' 1 → Fresh m.H' 1 := (newFromWrite index_primitive 1).1
theorem nil_writes : Writes m m := .nil m
theorem nonempty_writes : Writes m m1 := .snoc (.nil m) at0 one index_primitive
theorem overwrite_back : m1.writeT at0 z = some m := by with_unfolding_all rfl
theorem multiple_writes : Writes m m := .snoc nonempty_writes at0 z overwrite_back

def old : HRef [.array Ty.uint] (.array Ty.uint) := ⟨0, rfl⟩
theorem sequence_separation : Fresh m.H' 1 ∧ old.id ≠ 1 :=
  multiple_writes.separate old 1 (Nat.le_refl 1)
theorem allocated_not_fresh : ¬ Fresh m.H' 0 := Nat.not_le_of_lt (by decide : 0 < 1)
theorem threshold_boundary : Fresh m.H' 1 := Nat.le_refl 1
theorem failed_identity : m.writeT (.index 9 .dyn z : MAddrT Ty.uint) one = none := by with_unfolding_all rfl
theorem failed_index : m.writeT (.index 0 .dyn one : MAddrT Ty.uint) one = none := by with_unfolding_all rfl

def tokenHeap : Heap [.struct "Token"] := ((z, ()), ())
def tokenMem : Grown [] (fun _ => Unit) := ⟨List.nil_prefix, tokenHeap, ()⟩
def tokenOne : Grown [] (fun _ => Unit) := { H' := [.struct "Token"], ext := List.nil_prefix, heap := ((one, ()), ()), val := () }
theorem field_primitive : tokenMem.writeT (.field 0 (s := "Token") (f := "value") rfl) one =
    some tokenOne := by with_unfolding_all rfl

def refsHeap : Heap [.struct "Token", .struct "Account"] :=
  ((z, ()), ((z, (⟨0, rfl⟩, ())), ()))
def refs : Grown [] (fun _ => Unit) := ⟨List.nil_prefix, refsHeap, ()⟩
def tokenField : MAddrT (.ref (.struct "Token")) :=
  .field 1 (s := "Account") (f := "token") rfl
theorem field_reference : refs.writeT tokenField 0 = some refs := by with_unfolding_all rfl
theorem failed_reference : refs.writeT tokenField 1 = none := by with_unfolding_all rfl

def refArrHeap : Heap [.struct "Token", .array (.ref (.struct "Token"))] :=
  ((z, ()), (⟨[⟨0, rfl⟩], by decide⟩, ()))
def refArr : Grown [] (fun _ => Unit) := ⟨List.nil_prefix, refArrHeap, ()⟩
theorem index_reference : refArr.writeT (.index 1 .dyn z : MAddrT (.ref (.struct "Token"))) 0 = some refArr := by with_unfolding_all rfl

def fixedHeap : Heap [.fixed Ty.uint 1] := (⟨[z], rfl⟩, ())
def fixedMem : Grown [] (fun _ => Unit) := ⟨List.nil_prefix, fixedHeap, ()⟩
theorem fixed_index : fixedMem.writeT (.index 0 (ArrTy.fixed (n := 1)) z : MAddrT Ty.uint) z = some fixedMem := by with_unfolding_all rfl

def token : SVal (.ref (.struct "Token")) := .struct (.cons (.prim z) .nil)
def emptyArr : SVal (.ref (.array Ty.uint)) := .array .nil .nil (by decide)
def liveArr : SVal (.ref (.array Ty.uint)) := .array (.cons (.prim z) .nil) .nil (by decide)
def emptyFixed : SVal (.ref (.fixed Ty.uint 0)) := .fixed .nil
def liveFixed : SVal (.ref (.fixed Ty.uint 1)) := .fixed (.cons (.prim z) .nil)
def nested : SVal (.ref (.struct "TokenBucket")) :=
  .struct (.cons (.array (.cons token (.cons token .nil)) .nil (by decide)) .nil)
def person : SVal (.ref (.struct "Person")) :=
  .struct (.cons (.struct (.cons (.prim z) (.cons token .nil))) (.cons (.prim z) .nil))

macro "copy_reduce" : tactic => `(tactic|
  simp only [SVal.copyStToM_struct, SFields.copyStToM_cons, SFields.copyStToM_nil,
    SVal.copyStToM_array, SVal.copyStToM_fixed, SVec.copyStToM_cons,
    SVec.copyStToM_nil, SVal.copyStToM_prim])

theorem primitive_no_alloc : ((SVal.prim z).copyStToM hp rfl).H' = [.array Ty.uint] := by
  rw [SVal.copyStToM_prim]
theorem primitive_threshold : Fresh ((SVal.prim z).copyStToM hp rfl).H' 1 ↔ Fresh [.array Ty.uint] 1 := by
  rw [SVal.copyStToM_prim]
theorem empty_array_alloc : (emptyArr.copyStToM hp rfl).val.id = 1 := by
  unfold emptyArr; copy_reduce; rfl
theorem live_array_alloc : (liveArr.copyStToM hp rfl).val.id = 1 := by
  unfold liveArr; copy_reduce; rfl
theorem empty_fixed_alloc : (emptyFixed.copyStToM hp rfl).val.id = 1 := by
  unfold emptyFixed; copy_reduce; rfl
theorem live_fixed_alloc : (liveFixed.copyStToM hp rfl).val.id = 1 := by
  unfold liveFixed; copy_reduce; rfl
theorem token_alloc : (token.copyStToM hp rfl).val.id = 1 := by
  unfold token; copy_reduce; rfl
theorem person_alloc : (person.copyStToM hp rfl).val.id = 3 := by
  unfold person token; copy_reduce; rfl
theorem nested_allocations : (nested.copyStToM hp rfl).H' =
    [.array Ty.uint, .struct "Token", .struct "Token",
     .array (.ref (.struct "Token")), .struct "TokenBucket"] := by
  unfold nested token; copy_reduce; rfl
theorem nested_root : (nested.copyStToM hp rfl).val.id = 4 := by
  unfold nested token; copy_reduce; rfl
theorem nested_mirror : nested.Mirrors (nested.copyStToM hp rfl).heap 1
    (nested.copyStToM hp rfl).val := copy_mirror hp nested rfl
theorem converse_rejected : ¬ (∀ id, Fresh [.array Ty.uint] id →
    Fresh (nested.copyStToM hp rfl).H' id) := copy_not_converse hp nested rfl

def copied := nested.copyStToM hp rfl
/-- A real write on the old array, after four nested allocations. -/
def suffixHeap : Heap copied.H' := (copied.heap.writeAddr
    (.index (old.wk copied.ext) .dyn z) one).getD copied.heap

theorem suffix_write_success : copied.heap.writeAddr (.index (old.wk copied.ext) .dyn z) one =
    some suffixHeap := by
  unfold suffixHeap copied nested token hp old
  copy_reduce
  with_unfolding_all rfl

theorem mixed_suffix : Operations copied.heap (emptyArr.copyStToM suffixHeap rfl).heap :=
  .copy (.write (.nil copied.heap) (.index (old.wk copied.ext) .dyn z) one suffixHeap
    suffix_write_success) emptyArr rfl

theorem copied_witness_survives :
    let root : HRef (emptyArr.copyStToM suffixHeap rfl).H' (.struct "TokenBucket") :=
      HRef.wk mixed_suffix.prefix copied.val
    root.id = copied.val.id ∧ Fresh [.array Ty.uint] root.id ∧
      ¬ Fresh (emptyArr.copyStToM suffixHeap rfl).H' root.id ∧
      (old.wk (copied.ext.trans mixed_suffix.prefix)).id ≠ root.id :=
  copy_then_witness hp nested rfl old mixed_suffix

theorem copy_order : (HRef.wk mixed_suffix.prefix copied.val).id <
    (token.copyStToM (emptyArr.copyStToM suffixHeap rfl).heap rfl).val.id :=
  copies_ordered hp nested rfl mixed_suffix token rfl

theorem map_refusal : (Ty.ref (.mapping .uint Ty.uint)).mapFree ≠ true := by decide

theorem empty_fields_no_alloc :
    (SFields.copyStToM hp .nil (fun _ h => by cases h)).H' = [.array Ty.uint] := by
  rw [SFields.copyStToM_nil]
theorem unknown_struct_refusal : (Ty.ref (.struct "UnknownH28")).mapFree ≠ true := by decide

def fixedRefsHeap : Heap [.struct "Token", .fixed (.ref (.struct "Token")) 1] :=
  ((z, ()), (⟨[⟨0, rfl⟩], rfl⟩, ()))
def fixedRefs : Grown [] (fun _ => Unit) := ⟨List.nil_prefix, fixedRefsHeap, ()⟩
theorem fixed_reference : fixedRefs.writeT
    (.index 1 (ArrTy.fixed (n := 1)) z : MAddrT (.ref (.struct "Token"))) 0 =
    some fixedRefs := by with_unfolding_all rfl

def boolHeap : Heap [.array (.prim .bool)] := (⟨[false], by decide⟩, ())
def boolMem : Grown [] (fun _ => Unit) := ⟨List.nil_prefix, boolHeap, ()⟩
theorem bool_write : boolMem.writeT (.index 0 .dyn z : MAddrT (.prim .bool)) false =
    some boolMem := by with_unfolding_all rfl

def intHeap : Heap [.array (.prim .int)] := (⟨[PrimTy.dflt .int], by decide⟩, ())
def intMem : Grown [] (fun _ => Unit) := ⟨List.nil_prefix, intHeap, ()⟩
theorem int_write : intMem.writeT (.index 0 .dyn z : MAddrT (.prim .int)) (PrimTy.dflt .int) =
    some intMem := by with_unfolding_all rfl

def nestedFixed : SVal (.ref (.fixed (.ref (.struct "TokenBucket")) 1)) :=
  .fixed (.cons nested .nil)
theorem nested_fixed_root : (nestedFixed.copyStToM hp rfl).val.id = 5 := by
  unfold nestedFixed nested token; copy_reduce; rfl

def child : HRef copied.H' (.array (.ref (.struct "Token"))) :=
  copied.heap.field copied.val (f := "tokens") rfl
theorem nested_child_id : child.id = 3 := by
  unfold child copied nested token; copy_reduce; with_unfolding_all rfl

theorem nested_child_survives :
    (HRef.wk mixed_suffix.prefix child).id = 3 ∧
    (old.wk (copied.ext.trans mixed_suffix.prefix)).id ≠
      (HRef.wk mixed_suffix.prefix child).id := by
  change child.id = 3 ∧ 0 ≠ child.id
  rw [nested_child_id]
  exact ⟨rfl, by decide⟩

def expanded : Grown [] (fun _ => Unit) :=
  ⟨List.nil_prefix, (emptyArr.copyStToM hp rfl).heap, ()⟩
theorem writes_cannot_allocate : ¬ Writes m expanded := by
  intro h
  have he := congrArg List.length h.typing
  unfold expanded emptyArr at he
  simp only [SVal.copyStToM_array, SVec.copyStToM_nil] at he
  change 2 = 1 at he
  omega

theorem operations_cannot_shrink : ¬ (@Operations [.array Ty.uint] [] hp ()) := by
  intro h
  have he : 1 ≤ 0 := h.prefix.length_le
  omega

def shadowArray : SVal (.ref (.array (.ref (.struct "Token")))) :=
  .array .nil (.cons token .nil) (by decide)
theorem shadow_not_allocated : (shadowArray.copyStToM hp rfl).H' =
    [.array Ty.uint, .array (.ref (.struct "Token"))] := by
  unfold shadowArray
  copy_reduce
  rfl

end Solidity.SolkeyAgreementH28.Controls

#check @Solidity.SolkeyAgreementH28.Controls.index_primitive
#print axioms Solidity.SolkeyAgreementH28.Controls.index_primitive

#check @Solidity.SolkeyAgreementH28.Controls.index_read_changed
#print axioms Solidity.SolkeyAgreementH28.Controls.index_read_changed

#check @Solidity.SolkeyAgreementH28.Controls.write_reverse
#print axioms Solidity.SolkeyAgreementH28.Controls.write_reverse

#check @Solidity.SolkeyAgreementH28.Controls.write_forward
#print axioms Solidity.SolkeyAgreementH28.Controls.write_forward

#check @Solidity.SolkeyAgreementH28.Controls.nil_writes
#print axioms Solidity.SolkeyAgreementH28.Controls.nil_writes

#check @Solidity.SolkeyAgreementH28.Controls.nonempty_writes
#print axioms Solidity.SolkeyAgreementH28.Controls.nonempty_writes

#check @Solidity.SolkeyAgreementH28.Controls.overwrite_back
#print axioms Solidity.SolkeyAgreementH28.Controls.overwrite_back

#check @Solidity.SolkeyAgreementH28.Controls.multiple_writes
#print axioms Solidity.SolkeyAgreementH28.Controls.multiple_writes

#check @Solidity.SolkeyAgreementH28.Controls.sequence_separation
#print axioms Solidity.SolkeyAgreementH28.Controls.sequence_separation

#check @Solidity.SolkeyAgreementH28.Controls.allocated_not_fresh
#print axioms Solidity.SolkeyAgreementH28.Controls.allocated_not_fresh

#check @Solidity.SolkeyAgreementH28.Controls.threshold_boundary
#print axioms Solidity.SolkeyAgreementH28.Controls.threshold_boundary

#check @Solidity.SolkeyAgreementH28.Controls.failed_identity
#print axioms Solidity.SolkeyAgreementH28.Controls.failed_identity

#check @Solidity.SolkeyAgreementH28.Controls.failed_index
#print axioms Solidity.SolkeyAgreementH28.Controls.failed_index

#check @Solidity.SolkeyAgreementH28.Controls.field_primitive
#print axioms Solidity.SolkeyAgreementH28.Controls.field_primitive

#check @Solidity.SolkeyAgreementH28.Controls.field_reference
#print axioms Solidity.SolkeyAgreementH28.Controls.field_reference

#check @Solidity.SolkeyAgreementH28.Controls.failed_reference
#print axioms Solidity.SolkeyAgreementH28.Controls.failed_reference

#check @Solidity.SolkeyAgreementH28.Controls.index_reference
#print axioms Solidity.SolkeyAgreementH28.Controls.index_reference

#check @Solidity.SolkeyAgreementH28.Controls.fixed_index
#print axioms Solidity.SolkeyAgreementH28.Controls.fixed_index

#check @Solidity.SolkeyAgreementH28.Controls.primitive_no_alloc
#print axioms Solidity.SolkeyAgreementH28.Controls.primitive_no_alloc

#check @Solidity.SolkeyAgreementH28.Controls.primitive_threshold
#print axioms Solidity.SolkeyAgreementH28.Controls.primitive_threshold

#check @Solidity.SolkeyAgreementH28.Controls.empty_array_alloc
#print axioms Solidity.SolkeyAgreementH28.Controls.empty_array_alloc

#check @Solidity.SolkeyAgreementH28.Controls.live_array_alloc
#print axioms Solidity.SolkeyAgreementH28.Controls.live_array_alloc

#check @Solidity.SolkeyAgreementH28.Controls.empty_fixed_alloc
#print axioms Solidity.SolkeyAgreementH28.Controls.empty_fixed_alloc

#check @Solidity.SolkeyAgreementH28.Controls.live_fixed_alloc
#print axioms Solidity.SolkeyAgreementH28.Controls.live_fixed_alloc

#check @Solidity.SolkeyAgreementH28.Controls.token_alloc
#print axioms Solidity.SolkeyAgreementH28.Controls.token_alloc

#check @Solidity.SolkeyAgreementH28.Controls.person_alloc
#print axioms Solidity.SolkeyAgreementH28.Controls.person_alloc

#check @Solidity.SolkeyAgreementH28.Controls.nested_allocations
#print axioms Solidity.SolkeyAgreementH28.Controls.nested_allocations

#check @Solidity.SolkeyAgreementH28.Controls.nested_root
#print axioms Solidity.SolkeyAgreementH28.Controls.nested_root

#check @Solidity.SolkeyAgreementH28.Controls.nested_mirror
#print axioms Solidity.SolkeyAgreementH28.Controls.nested_mirror

#check @Solidity.SolkeyAgreementH28.Controls.converse_rejected
#print axioms Solidity.SolkeyAgreementH28.Controls.converse_rejected

#check @Solidity.SolkeyAgreementH28.Controls.suffix_write_success
#print axioms Solidity.SolkeyAgreementH28.Controls.suffix_write_success

#check @Solidity.SolkeyAgreementH28.Controls.mixed_suffix
#print axioms Solidity.SolkeyAgreementH28.Controls.mixed_suffix

#check @Solidity.SolkeyAgreementH28.Controls.copied_witness_survives
#print axioms Solidity.SolkeyAgreementH28.Controls.copied_witness_survives

#check @Solidity.SolkeyAgreementH28.Controls.copy_order
#print axioms Solidity.SolkeyAgreementH28.Controls.copy_order

#check @Solidity.SolkeyAgreementH28.Controls.map_refusal
#print axioms Solidity.SolkeyAgreementH28.Controls.map_refusal

#check @Solidity.SolkeyAgreementH28.Controls.empty_fields_no_alloc
#print axioms Solidity.SolkeyAgreementH28.Controls.empty_fields_no_alloc

#check @Solidity.SolkeyAgreementH28.Controls.unknown_struct_refusal
#print axioms Solidity.SolkeyAgreementH28.Controls.unknown_struct_refusal

#check @Solidity.SolkeyAgreementH28.Controls.fixed_reference
#print axioms Solidity.SolkeyAgreementH28.Controls.fixed_reference

#check @Solidity.SolkeyAgreementH28.Controls.bool_write
#print axioms Solidity.SolkeyAgreementH28.Controls.bool_write

#check @Solidity.SolkeyAgreementH28.Controls.int_write
#print axioms Solidity.SolkeyAgreementH28.Controls.int_write

#check @Solidity.SolkeyAgreementH28.Controls.nested_fixed_root
#print axioms Solidity.SolkeyAgreementH28.Controls.nested_fixed_root

#check @Solidity.SolkeyAgreementH28.Controls.nested_child_id
#print axioms Solidity.SolkeyAgreementH28.Controls.nested_child_id

#check @Solidity.SolkeyAgreementH28.Controls.nested_child_survives
#print axioms Solidity.SolkeyAgreementH28.Controls.nested_child_survives

#check @Solidity.SolkeyAgreementH28.Controls.writes_cannot_allocate
#print axioms Solidity.SolkeyAgreementH28.Controls.writes_cannot_allocate

#check @Solidity.SolkeyAgreementH28.Controls.operations_cannot_shrink
#print axioms Solidity.SolkeyAgreementH28.Controls.operations_cannot_shrink

#check @Solidity.SolkeyAgreementH28.Controls.shadow_not_allocated
#print axioms Solidity.SolkeyAgreementH28.Controls.shadow_not_allocated
