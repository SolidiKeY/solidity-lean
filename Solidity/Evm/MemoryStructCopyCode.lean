import Solidity.Evm.MemoryStructCopy
import Solidity.Evm.MemoryRefWrite

/-!
# Loading and initializing copied struct members

All storage members are read before allocation or initialization changes
memory. The checked load plan records each member's real source type. Stores
then consume those words beneath a retained allocation pointer, preserving
the caller's arbitrary stack and every cell outside the written addresses.
-/
namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}

def copyMember {Γ : Ctx} {s : Name} (root : Name)
    (hr : C.rootType root = some (.ref (.struct s))) (f : Name) {p : PrimTy}
    (hf : C.fieldType s f = some (.prim p)) : Val C Γ p :=
  .read (.field (.loc (.root root hr)) f hf)

theorem copyMember_eval {Γ : Ctx} (σ : State C Γ) {s : Name} (root : Name)
    (hr : C.rootType root = some (.ref (.struct s))) (v : SFields (structDef s))
    (hv : σ.storage.get hr = .struct v) (f : Name) {p : PrimTy}
    (hf : C.fieldType s f = some (.prim p)) :
    (copyMember root hr f hf).evalT σ = .ok (v.get hf).view := by
  simp only [copyMember, Val.evalT, Loc.resolveT, SPath.resolveT,
    bind, Except.bind, pure, Except.pure, Storage.find, SRef.field, SRef.append,
    SRef.ofRoot, Path.append, hv, SVal.find_field, SVal.find_nil, TRes.ofOpt]

/-- A load plan checks each lookup and core expression before emitting code. -/
inductive CopyLoads (b : Nat) {Γ : Ctx} (F : Frag Γ) {s : Name} (root : Name)
    (hr : C.rootType root = some (.ref (.struct s))) :
    List (Name × Ty) → List Instr → Prop where
  | nil : CopyLoads b F root hr [] []
  | cons (f : Name) (p : PrimTy) (hf : C.fieldType s f = some (.prim p))
      (he : valIn F (copyMember root hr f hf) = true)
      {fs : List (Name × Ty)} {code : List Instr} (rest : CopyLoads b F root hr fs code) :
      CopyLoads b F root hr ((f, .prim p) :: fs)
        (code ++ Evm.compileVal b (copyMember (Γ := Γ) root hr f hf))

structure CompiledCopyLoads (b : Nat) {Γ : Ctx} (F : Frag Γ) {s : Name} (root : Name)
    (hr : C.rootType root = some (.ref (.struct s))) (fs : List (Name × Ty)) where
  code : List Instr
  cert : CopyLoads b F root hr fs code

def compileCopyLoads (b : Nat) {Γ : Ctx} (F : Frag Γ) {s : Name} (root : Name)
    (hr : C.rootType root = some (.ref (.struct s))) :
    (fs : List (Name × Ty)) → Option (CompiledCopyLoads b F root hr fs)
  | [] => some ⟨[], .nil⟩
  | (f, .prim p) :: fs => do
    if hf : C.fieldType s f = some (.prim p) then
      if he : valIn F (copyMember root hr f hf) = true then
        let rest ← compileCopyLoads b F root hr fs
        pure ⟨_, .cons f p hf he rest.cert⟩
      else none
    else none
  | (_, .ref _) :: _ => none

theorem CopyLoads.member {b : Nat} {Γ : Ctx} {F : Frag Γ} {s : Name} {root : Name}
    {hr : C.rootType root = some (.ref (.struct s))} {fs : List (Name × Ty)} {code : List Instr}
    (plan : CopyLoads b F root hr fs code) {f : Name} (hm : f ∈ fs.map Prod.fst) :
    ∃ p : PrimTy, C.fieldType s f = some (.prim p) := by
  induction plan with
  | nil => cases hm
  | cons g p hf he rest ih =>
    rcases List.mem_cons.mp hm with h | h
    · subst f; exact ⟨p, hf⟩
    · exact ih h

/-- Loaded words retain their field names and their actual typed values. -/
theorem CopyLoads.correct {L b : Nat} {Γ : Ctx} {F : Frag Γ} {s : Name} {root : Name}
    {hr : C.rootType root = some (.ref (.struct s))} {fs : List (Name × Ty)} {code : List Instr}
    (plan : CopyLoads b F root hr fs code) {σ : State C Γ} {m : Machine}
    (h : Sim C L b F σ m) (v : SFields (structDef s)) (hv : σ.storage.get hr = .struct v) :
    ∃ cells : List (Name × Word),
      cells.map Prod.fst = fs.map Prod.fst ∧
      (∀ f w, (f, w) ∈ cells → ∀ {p : PrimTy} (hf : C.fieldType s f = some (.prim p)),
        ReprV p (v.get hf).view w) ∧
      run code m = .ok {m with stack := cells.map Prod.snd ++ m.stack} 0 := by
  induction plan with
  | nil => exact ⟨[], rfl, by simp only [List.not_mem_nil, false_implies, implies_true], rfl⟩
  | cons f p hf he rest ih =>
    obtain ⟨cells, hn, hg, hc⟩ := ih
    have hm : Sim C L b F σ {m with stack := cells.map Prod.snd ++ m.stack} := h.stack _
    have heval := copyMember_eval σ root hr v hv f hf
    rcases val_sim (copyMember root hr f hf) hm he with ⟨x, w, hx, hw, hrun⟩ | ⟨hx, _⟩
    · rw [heval] at hx
      cases hx
      refine ⟨(f, w) :: cells, congrArg (List.cons f) hn, ?_, ?_⟩
      · intro g u hu q hq
        rcases List.mem_cons.mp hu with hu | hu
        · cases hu
          have hp : p = q := by rw [hf] at hq; cases hq; rfl
          cases hp
          exact hw
        · exact hg g u hu hq
      · rw [run_append_ok hc, hrun]
        rfl
    · rw [heval] at hx
      cases hx

def copyStoreCode (s : Name) : List Name → List Instr
  | [] => []
  | f :: fs => [.swap 1, .dup 2] ++ writeFieldCode (fieldOffset (structDef s) f) ++ copyStoreCode s fs

def copyStoreMachine (s : Name) (cursor : Fin W) : List (Name × Word) → Machine → Machine
  | [], m => m
  | (f, w) :: cells, m => copyStoreMachine s cursor cells
      (writeMachine m (cursor.val + fieldOffset (structDef s) f) w)

/-- Initialization consumes exactly its words and retains the allocation pointer. -/
theorem copyStore_run (s : Name) (cursor : Fin W) (cells : List (Name × Word)) (m : Machine)
    (hs : ∀ f w, (f, w) ∈ cells → cursor.val + fieldOffset (structDef s) f < W) :
    run (copyStoreCode s (cells.map Prod.fst))
      {m with stack := .val cursor :: cells.map Prod.snd ++ m.stack} =
      .ok ((copyStoreMachine s cursor cells m).push (.val cursor)) 0 := by
  induction cells generalizing m with
  | nil => rfl
  | cons cell cells ih =>
    obtain ⟨f, w⟩ := cell
    have hstart : run [.swap 1, .dup 2]
        {m with stack := .val cursor :: ((f, w) :: cells).map Prod.snd ++ m.stack} =
        .ok ((({m with stack := cells.map Prod.snd ++ m.stack}).push (.val cursor)).push w |>.push (.val cursor)) 0 := by
      rfl
    rw [List.map_cons, copyStoreCode, List.append_assoc, run_append_ok hstart,
      run_append_ok (writeFieldWord_run _ cursor _ w (hs f w (List.mem_cons_self ..)))]
    exact ih (writeMachine m (cursor.val + fieldOffset (structDef s) f) w)
      (fun g u hu => hs g u (List.mem_cons_of_mem _ hu))

/-- Copy stores cannot disturb cells outside their explicit member addresses. -/
theorem copyStore_other (s : Name) (cursor : Fin W) (cells : List (Name × Word)) (m : Machine)
    (addr : Nat) (ha : ∀ f w, (f, w) ∈ cells → addr ≠ cursor.val + fieldOffset (structDef s) f) :
    (copyStoreMachine s cursor cells m).mem addr = m.mem addr := by
  induction cells generalizing m with
  | nil => rfl
  | cons cell cells ih =>
    obtain ⟨f, w⟩ := cell
    rw [copyStoreMachine, ih _ (fun g u hu => ha g u (List.mem_cons_of_mem _ hu))]
    exact upd_other _ _ (ha f w (List.mem_cons_self ..))

/-- The initializer preserves all machine components except the written memory. -/
theorem copyStore_shape (s : Name) (cursor : Fin W) (cells : List (Name × Word)) (m : Machine) :
    copyStoreMachine s cursor cells m = {m with mem := (copyStoreMachine s cursor cells m).mem} := by
  induction cells generalizing m with
  | nil => rfl
  | cons cell cells ih =>
    obtain ⟨f, w⟩ := cell
    exact ih (writeMachine m (cursor.val + fieldOffset (structDef s) f) w)

/-- A write fold preserves an already represented word when every overwrite agrees. -/
theorem copyStore_preserves (s : Name) (cursor : Fin W) (cells : List (Name × Word)) (m : Machine)
    (addr : Nat) {p : PrimTy} (v : p.Denote) (hm : ReprV p v (m.mem addr))
    (hg : ∀ f w, (f, w) ∈ cells → addr = cursor.val + fieldOffset (structDef s) f → ReprV p v w) :
    ReprV p v ((copyStoreMachine s cursor cells m).mem addr) := by
  induction cells generalizing m with
  | nil => exact hm
  | cons cell cells ih =>
    obtain ⟨f, w⟩ := cell
    apply ih (writeMachine m (cursor.val + fieldOffset (structDef s) f) w)
    · by_cases he : addr = cursor.val + fieldOffset (structDef s) f
      · simpa only [writeMachine, he, upd_same] using hg f w (List.mem_cons_self ..) he
      · simpa only [writeMachine, upd_other _ _ he] using hm
    · exact fun g u hu => hg g u (List.mem_cons_of_mem _ hu)

/-- A loaded member is represented after initialization, even if written repeatedly. -/
theorem copyStore_written (s : Name) (cursor : Fin W) (cells : List (Name × Word)) (m : Machine)
    (addr : Nat) {p : PrimTy} (v : p.Denote)
    (hex : ∃ f w, (f, w) ∈ cells ∧ addr = cursor.val + fieldOffset (structDef s) f)
    (hg : ∀ f w, (f, w) ∈ cells → addr = cursor.val + fieldOffset (structDef s) f → ReprV p v w) :
    ReprV p v ((copyStoreMachine s cursor cells m).mem addr) := by
  induction cells generalizing m with
  | nil => obtain ⟨_, _, h, _⟩ := hex; cases h
  | cons cell cells ih =>
    obtain ⟨f, w⟩ := cell
    by_cases he : addr = cursor.val + fieldOffset (structDef s) f
    · exact copyStore_preserves s cursor cells _ addr v
        (by simpa only [writeMachine, he, upd_same] using hg f w (List.mem_cons_self ..) he)
        (fun g u hu => hg g u (List.mem_cons_of_mem _ hu))
    · apply ih (writeMachine m (cursor.val + fieldOffset (structDef s) f) w)
      · obtain ⟨g, u, hu, haddr⟩ := hex
        rcases List.mem_cons.mp hu with hu | hu
        · cases hu; exact (he haddr).elim
        · exact ⟨g, u, hu, haddr⟩
      · exact fun g u hu => hg g u (List.mem_cons_of_mem _ hu)

/-- The stores represent the actual fresh source payload at every primitive member. -/
theorem copyStore_fields {b : Nat} {Γ : Ctx} {F : Frag Γ} {s : Name} {root : Name}
    {hr : C.rootType root = some (.ref (.struct s))} {code : List Instr}
    (plan : CopyLoads b F root hr (structDef s) code) {H : HTy} (hp : Heap H)
    (v : SFields (structDef s)) (hprim : primitiveMembers (structDef s) = true)
    (hmap : (Ty.ref (.struct s)).mapFree = true) (cursor : Fin W)
    (cells : List (Name × Word)) (m : Machine)
    (hn : cells.map Prod.fst = (structDef s).map Prod.fst)
    (hg : ∀ f w, (f, w) ∈ cells → ∀ {p : PrimTy} (hf : C.fieldType s f = some (.prim p)),
      ReprV p (v.get hf).view w)
    (hs : cursor.val + (structDef s).length < W) :
    StructRepr (hp.alloc (R := .struct s) (copiedFields (structDef s) hprim v)).1
      (hp.alloc (R := .struct s) (copiedFields (structDef s) hprim v)).2 cursor
      (copyStoreMachine s cursor cells m) := by
  refine ⟨by omega, ?_⟩
  intro f p hf
  rw [Heap.field, Heap.get_alloc, MObj.wk, MFields.get_wk]
  change ReprV p (MFields.get (structDef s) (copiedFields (H := H) (structDef s) hprim v) hf) _
  rw [copiedFields_get hp v hprim hmap hf]
  apply copyStore_written s cursor cells m _ (v.get hf).view
  · have hm : f ∈ cells.map Prod.fst := by
      rw [hn]
      exact List.mem_map_of_mem (Semantics.lookupBy_eq_some_mem hf)
    obtain ⟨⟨g, w⟩, hw, he⟩ := List.mem_map.mp hm
    cases he
    exact ⟨g, w, hw, rfl⟩
  · intro g w hw he
    have hmem : g ∈ (structDef s).map Prod.fst := hn ▸ List.mem_map_of_mem hw
    obtain ⟨q, hq⟩ := plan.member hmem
    have hfg : f = g := by
      by_cases hfg : f = g
      · exact hfg
      · have ho := fieldOffset_ne hf hq hfg
        omega
    subst g
    exact hg f w hw hf

end Solidity.Evm.Memory
