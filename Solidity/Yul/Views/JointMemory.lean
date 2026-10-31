import Solidity.Yul.Views.MemoryTransport

/-! Constructive joint canonical ordinary-memory preparation. Both actual
objects are decoded from one physical snapshot; real heapPut operations then
run in the selected order. A failed decoder is None, never a source no-op.
Source errors retain their complete Except/state and stop the actual bind. -/
namespace Solidity.Yul.Views

theorem heapPutConcrete_run {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (root : Nat) {τ : Source.STy} (d : Source.Data E.layout τ) (typed : s.2.heap.ty root = some τ) :
    (Source.heapPut root ⟨τ, d⟩ : Source.EM E Γ Unit).run s =
      (.ok (), withSourceHeap s (s.2.heap.write root d typed)) := by
  rcases s with ⟨locals, state⟩
  unfold Source.heapPut
  rw [Source.Hoare.run_bind]
  change (if ht : state.heap.ty root = some τ then
    Source.EM.setSt {state with heap := state.heap.write root d ht} else
    Source.EM.halt (.stuck "memory write type")).run ⟨locals, state⟩ = _
  rw [dif_pos typed]
  rfl

theorem heapPutConcrete_error {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (root : Nat) {τ : Source.STy} (d : Source.Data E.layout τ) (wrong : s.2.heap.ty root ≠ some τ) :
    (Source.heapPut root ⟨τ, d⟩ : Source.EM E Γ Unit).run s = (.error (.stuck "memory write type"), s) := by
  rcases s with ⟨locals, state⟩
  unfold Source.heapPut
  rw [Source.Hoare.run_bind]
  change (if ht : state.heap.ty root = some τ then
    Source.EM.setSt {state with heap := state.heap.write root d ht} else
    Source.EM.halt (.stuck "memory write type")).run ⟨locals, state⟩ = _
  rw [dif_neg wrong]
  rfl

theorem heapPutConcrete_types {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (root : Nat) {τ : Source.STy} (d : Source.Data E.layout τ) :
    ((Source.heapPut root ⟨τ, d⟩ : Source.EM E Γ Unit).run s).2.2.heap.ty = s.2.heap.ty := by
  by_cases typed : s.2.heap.ty root = some τ
  · rw [heapPutConcrete_run s root d typed]
    exact funext (fun a => Source.Heap.write_ty s.2.heap root a d typed)
  · rw [heapPutConcrete_error s root d typed]

theorem heapPutConcrete_MemOK {E : Source.Env} {Γ : Source.RCtx} (H : Source.HeapTy)
    (s : Source.EMState E Γ) (root : Nat) {τ : Source.STy} (d : Source.Data E.layout τ)
    (valid : Source.DataOK E s.2.heap.ty d) (top : Source.Data.Top d) (inner : Source.Data.Inner d)
    (ok : Source.MemOK E H s) : Source.MemOK E H ((Source.heapPut root ⟨τ, d⟩ : Source.EM E Γ Unit).run s).2 := by
  have one := Source.heapPut_ok (E := E) (Γ := Γ) (H := H) root ⟨τ, d⟩ s ⟨ok.1, valid⟩
  have two := Source.heapPut_top (E := E) (Γ := Γ) root ⟨τ, d⟩ s ⟨ok.2.1, top⟩
  have three := Source.heapPut_inner (E := E) (Γ := Γ) root ⟨τ, d⟩ s ⟨ok.2.2, inner⟩
  cases run : (Source.heapPut root ⟨τ, d⟩ : Source.EM E Γ Unit).run s with
  | mk result out => cases result with
    | ok value => exact ⟨by simpa only [run] using one, by simpa only [run] using two, by simpa only [run] using three⟩
    | error e =>
      have em : Source.EMOK E H out ∧ (Source.NotStuck e ∨ out.2.heap.ty root ≠ some τ) := by simpa only [run] using one
      exact ⟨em.1, by simpa only [run] using two, by simpa only [run] using three⟩

def twoHeapPut {E : Source.Env} {Γ : Source.RCtx} (a : Nat) {τ : Source.STy} (x : Source.Data E.layout τ)
    (b : Nat) {σ : Source.STy} (y : Source.Data E.layout σ) : Source.EM E Γ Unit := do
  Source.heapPut a ⟨τ, x⟩
  Source.heapPut b ⟨σ, y⟩

theorem twoHeapPut_run {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (a : Nat) {τ : Source.STy} (x : Source.Data E.layout τ) (b : Nat) {σ : Source.STy} (y : Source.Data E.layout σ)
    (ha : s.2.heap.ty a = some τ) (hb : s.2.heap.ty b = some σ) :
    (twoHeapPut a x b y).run s = (.ok (), withSourceHeap s
      ((s.2.heap.write a x ha).write b y (by rw [Source.Heap.write_ty]; exact hb))) := by
  rw [twoHeapPut, Source.Hoare.run_bind, heapPutConcrete_run s a x ha]
  simp only []
  rw [heapPutConcrete_run _ b y (by change (s.2.heap.write a x ha).ty b = some σ; rw [Source.Heap.write_ty]; exact hb)]
  rfl

theorem twoHeapPut_commute {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (a : Nat) {τ : Source.STy} (x : Source.Data E.layout τ) (b : Nat) {σ : Source.STy} (y : Source.Data E.layout σ)
    (ha : s.2.heap.ty a = some τ) (hb : s.2.heap.ty b = some σ) (distinct : a ≠ b) :
    (twoHeapPut a x b y).run s = (twoHeapPut b y a x).run s := by
  rw [twoHeapPut_run s a x b y ha hb, twoHeapPut_run s b y a x hb ha, heap_writes_commute _ a b x y ha hb distinct]

/-- Every owner H, including complete error results (a failed first put stops;
a failed second put retains the successful caller-prefix write). -/
theorem twoHeapPut_MemOK {E : Source.Env} {Γ : Source.RCtx} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (a : Nat) {τ : Source.STy} (x : Source.Data E.layout τ) (b : Nat) {σ : Source.STy} (y : Source.Data E.layout σ)
    (vx : Source.DataOK E s.2.heap.ty x) (tx : Source.Data.Top x) (ix : Source.Data.Inner x)
    (vy : Source.DataOK E s.2.heap.ty y) (ty : Source.Data.Top y) (iy : Source.Data.Inner y)
    (ok : Source.MemOK E H s) : Source.MemOK E H ((twoHeapPut a x b y).run s).2 := by
  have first := heapPutConcrete_MemOK H s a x vx tx ix ok
  have types := heapPutConcrete_types s a x
  rw [twoHeapPut, Source.Hoare.run_bind]
  cases run : (Source.heapPut a ⟨τ, x⟩ : Source.EM E Γ Unit).run s with
  | mk result out =>
    have good : Source.MemOK E H out := by simpa only [run] using first
    cases result with
    | error e => exact good
    | ok value =>
      have eq : out.2.heap.ty = s.2.heap.ty := by simpa only [run] using types
      exact heapPutConcrete_MemOK H out b y (by rw [eq]; exact vy) ty iy good

/-- Header-preserving fixed or dynamic arrays plus simultaneous declared fields.
The two concrete decodes share one ownership snapshot; no generic law input. -/
def canonicalJointState {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (a : Nat) (name : Source.DeclName)
    (b : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n)
    (reverse : Bool) (m : ByteView) : Option (Except Source.Halt Unit × Source.EMState E Γ) := do
  if arrayLengthChoice k m (p.address b) = n then
    let fs ← decodeCanonicalFields p es (E.layout.fields name) m (p.address a)
    let values ← decodeCanonicalArray p es τ n m (p.address b + arrayPayloadOffset k)
    pure ((if reverse then twoHeapPut b (memberArrayData E.layout τ k n hl values) a (Source.Data.struct (l := .memory) fs)
      else twoHeapPut a (Source.Data.struct (l := .memory) fs) b (memberArrayData E.layout τ k n hl values)).run s)
  else none

theorem canonicalJoint_order {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (a : Nat) (name : Source.DeclName)
    (b : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n)
    (ha : s.2.heap.ty a = some (.struct .memory name)) (hb : s.2.heap.ty b = some (.array .memory τ k))
    (distinct : a ≠ b) (m : ByteView) :
    canonicalJointState s p es a name b τ k n hl false m = canonicalJointState s p es a name b τ k n hl true m := by
  unfold canonicalJointState
  split
  · cases df : decodeCanonicalFields p es (E.layout.fields name) m (p.address a) with
    | none => rfl
    | some fs =>
      cases da : decodeCanonicalArray p es τ n m (p.address b + arrayPayloadOffset k) with
      | none => rfl
      | some values => exact congrArg some (twoHeapPut_commute s a (Source.Data.struct (l := .memory) fs) b (memberArrayData E.layout τ k n hl values) ha hb distinct)
  · rfl

theorem canonicalJoint_MemOK {E : Source.Env} {Γ : Source.RCtx} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (a : Nat) (name : Source.DeclName)
    (b : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n)
    (reverse : Bool) (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : canonicalJointState s p es a name b τ k n hl reverse m = some result) (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  unfold canonicalJointState at step
  split at step
  · cases df : decodeCanonicalFields p es (E.layout.fields name) m (p.address a) with
    | none => rw [df] at step; cases step
    | some fs =>
      cases da : decodeCanonicalArray p es τ n m (p.address b + arrayPayloadOffset k) with
      | none => rw [df, da] at step; cases step
      | some values =>
        rw [df, da] at step
        cases step
        obtain ⟨ws, fields, reads⟩ := decodeCanonicalFields_representation p es _ m _ fs df
        have elems := decodeCanonicalArray_sound p es τ n m _ values da
        have vx : Source.DataOK E s.2.heap.ty (.struct (l := .memory) fs) := .struct fields.dataOK
        have vy : Source.DataOK E s.2.heap.ty (memberArrayData E.layout τ k n hl values) := .array (fun i => .val (elems i).refOK)
        cases reverse
        · exact twoHeapPut_MemOK H s a (Source.Data.struct (l := .memory) fs) b _ vx trivial fields.allVal vy trivial (fun i => ⟨values i, rfl⟩) ok
        · exact twoHeapPut_MemOK H s b _ a (Source.Data.struct (l := .memory) fs) vy trivial (fun i => ⟨values i, rfl⟩) vx trivial fields.allVal ok
  · cases step

theorem canonicalJoint_decoded {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (a : Nat) (name : Source.DeclName)
    (b : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n)
    (m : ByteView) (header : arrayLengthChoice k m (p.address b) = n)
    (fs : Source.DataList E.layout (E.layout.fields name)) (values : Fin n → Source.Val E.layout τ)
    (df : decodeCanonicalFields p es (E.layout.fields name) m (p.address a) = some fs)
    (da : decodeCanonicalArray p es τ n m (p.address b + arrayPayloadOffset k) = some values) :
    canonicalJointState s p es a name b τ k n hl false m = some ((twoHeapPut a (Source.Data.struct (l := .memory) fs)
      b (memberArrayData E.layout τ k n hl values)).run s) := by
  unfold canonicalJointState
  rw [if_pos header, df, da]
  rfl

theorem canonicalJoint_unchanged {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (a : Nat) (name : Source.DeclName) (fs : Source.DataList E.layout (E.layout.fields name))
    (fa : s.2.heap.get a = some ⟨.struct .memory name,.struct fs⟩)
    (ws : List Roadmap.Word) (fields : MemoryFields p fs ws) (supportedFields : ∀ υ ∈ E.layout.fields name, ExtendedMemberType E.layout υ)
    (b : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ x, k = some x → x = n)
    (values : Fin n → Source.Val E.layout τ) (fb : s.2.heap.get b = some ⟨_,memberArrayData E.layout τ k n hl values⟩)
    (words : Fin n → Roadmap.Word) (elems : ∀ i, MemoryElement p (values i) (words i)) (supported : ExtendedMemberType E.layout τ)
    (m : ByteView) (header : arrayLengthChoice k m (p.address b) = n)
    (rf : ∀ i w, ws[i]? = some w → mload m (p.address a + i * 32) = w)
    (ra : ∀ i, mload m (p.address b + arrayPayloadOffset k + i.val * 32) = words i) :
    canonicalJointState s p es a name b τ k n hl false m = some (.ok (),s) := by
  rw [canonicalJoint_decoded s p es a name b τ k n hl m header fs values
    (decodeCanonicalFields_reads p es coverage fields supportedFields m _ rf)
    (decodeCanonicalArray_reads p es coverage τ supported n values words elems m _ ra)]
  have first : (Source.heapPut a ⟨.struct .memory name,.struct fs⟩ : Source.EM E Γ Unit).run s = (.ok (),s) := by
    rw [heapPutConcrete_run s a (.struct fs) (heap_ty_of_get s.2.heap a _ _ fa),
      heap_write_unchanged s.2.heap a _ _ fa, withSourceHeap_unchanged]
  rw [twoHeapPut, Source.Hoare.run_bind, first]
  simp only []
  rw [heapPutConcrete_run s b _ (heap_ty_of_get s.2.heap b _ _ fb),
    heap_write_unchanged s.2.heap b _ _ fb, withSourceHeap_unchanged]

theorem twoHeapPut_second_error {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (a : Nat) {τ : Source.STy} (x : Source.Data E.layout τ) (b : Nat) {σ : Source.STy} (y : Source.Data E.layout σ)
    (ha : s.2.heap.ty a = some τ) (wrong : s.2.heap.ty b ≠ some σ) :
    (twoHeapPut a x b y).run s = (.error (.stuck "memory write type"),withSourceHeap s (s.2.heap.write a x ha)) := by
  rw [twoHeapPut, Source.Hoare.run_bind, heapPutConcrete_run s a x ha]
  simp only []
  exact heapPutConcrete_error _ b y (by change (s.2.heap.write a x ha).ty b ≠ some σ; rw [Source.Heap.write_ty]; exact wrong)

end Solidity.Yul.Views
