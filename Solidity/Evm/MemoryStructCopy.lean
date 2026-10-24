import Solidity.Evm.MemoryStructDefault

/-!
# Primitive-member struct copies

Copying primitive storage members creates one fresh struct object and no
recursive children. Its payload retains the actual unsigned, signed and
Boolean values, rather than the defaults used by construction/deletion.
-/
namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}

def copiedFields {H : HTy} : (fs : List (Name × Ty)) →
    primitiveMembers fs = true → SFields fs → MFields H fs
  | [], _, .nil => ()
  | (_, .prim _) :: fs, h, .cons (.prim v) rest => (v, copiedFields fs h rest)
  | (_, .ref _) :: _, h, _ => by cases h

private theorem copiedFields_cons_eq {H : HTy} (hp : Heap H) (f : Name) (p : PrimTy)
    (v : p.Denote) (fs : List (Name × Ty)) (h : primitiveMembers fs = true) (rest : SFields fs)
    (g : Grown H (MFields · fs))
    (hg : g = ⟨List.prefix_refl H, hp, copiedFields fs h rest⟩) :
    (⟨(List.prefix_refl H).trans g.ext, g.heap, (MVal.wk g.ext (.prim p) v, g.val)⟩ :
      Grown H (MFields · ((f, .prim p) :: fs))) =
      ⟨List.prefix_refl H, hp, copiedFields ((f, .prim p) :: fs) h (.cons (.prim v) rest)⟩ := by
  subst hg
  rfl

theorem copiedFields_copy {H : HTy} (hp : Heap H) {fs : List (Name × Ty)} (v : SFields fs)
    (h : primitiveMembers fs = true) (hm : ∀ fT ∈ fs, fT.2.mapFree = true) :
    v.copyStToM hp hm = ⟨List.prefix_refl H, hp, copiedFields fs h v⟩ := by
  induction fs with
  | nil => cases v; rw [SFields.copyStToM_nil]; rfl
  | cons ft fs ih =>
    obtain ⟨f, T⟩ := ft
    cases T with
    | prim p =>
      cases v with
      | cons value rest =>
        cases value with
        | prim value =>
          rw [SFields.copyStToM_cons, SVal.copyStToM_prim]
          with_unfolding_all exact copiedFields_cons_eq hp f p value fs h rest _ (ih rest h _)
    | ref R => cases h

theorem copiedStruct_alloc {H : HTy} (hp : Heap H) {s : Name}
    (v : SFields (structDef s)) (h : primitiveMembers (structDef s) = true)
    (hm : (Ty.ref (.struct s)).mapFree = true) :
    (SVal.struct v).copyStToM hp hm =
      Grown.alloc (R := .struct s) ⟨List.prefix_refl H, hp, copiedFields (structDef s) h v⟩ := by
  rw [SVal.copyStToM_struct, copiedFields_copy hp v h]

/-- Each member retains the storage value at its Solidity type. -/
theorem copiedFields_get {H : HTy} (hp : Heap H) {s f : Name} {p : PrimTy}
    (v : SFields (structDef s)) (h : primitiveMembers (structDef s) = true)
    (hm : (Ty.ref (.struct s)).mapFree = true)
    (hf : lookupBy f (structDef s) = some (.prim p)) :
    MFields.get (structDef s) (copiedFields (H := H) (structDef s) h v) hf =
      (v.get hf).view := by
  have hh := SFields.copyStToM_get_prim hp v
    (mapFree_structDef s (by simpa only [Ty.mapFree, decide_eq_true_eq] using hm)) hf
  rw [copiedFields_copy hp v h] at hh
  exact hh

private theorem adopt_copy_alloc {Γ : Ctx} {s : Name} (σ : State C Γ)
    (o : MObj σ.H (.struct s)) (g : Grown σ.H (MVal · (.ref (.struct s))))
    (hg : g = Grown.alloc ⟨List.prefix_refl _, σ.heap, o⟩) :
    (⟨(σ.adopt g).1, g.ext, g.val⟩ : Grew C Γ σ.H (HRef · (.struct s))) =
      ⟨(σ.alloc o).1, List.prefix_append _ _, (σ.alloc o).2⟩ := by
  subst hg
  rfl

/-- A resolved storage struct is copied once into one fresh memory object. -/
theorem copiedStruct_rhs {Γ : Ctx} (σ : State C Γ) {s : Name}
    (src : SPath C Γ (.ref (.struct s))) (r : SRef C (.ref (.struct s)))
    (hr : src.resolveT σ = .ok r) (v : SFields (structDef s))
    (hv : σ.storage.find r = some (.struct v))
    (hp : primitiveMembers (structDef s) = true) (hm : (Ty.ref (.struct s)).mapFree = true) :
    (MRhs.copy src hm).evalT σ =
      .ok ⟨(σ.alloc (R := .struct s) (copiedFields (structDef s) hp v)).1,
        List.prefix_append _ _, (σ.alloc (R := .struct s) (copiedFields (structDef s) hp v)).2⟩ := by
  simp only [MRhs.evalT, hr, hv, TRes.ofOpt, bind, Except.bind, pure, Except.pure,
    State.copyStToMG, State.grow]
  congr 1
  with_unfolding_all exact adopt_copy_alloc σ _ _ (copiedStruct_alloc σ.heap v hp hm)

/-- A copied declaration binds the fresh identity and weakens older locals. -/
theorem copiedStruct_decl {Γ : Ctx} (σ : State C Γ) {s : Name}
    (src : SPath C Γ (.ref (.struct s))) (r : SRef C (.ref (.struct s)))
    (hr : src.resolveT σ = .ok r) (v : SFields (structDef s))
    (hv : σ.storage.find r = some (.struct v))
    (hp : primitiveMembers (structDef s) = true) (hm : (Ty.ref (.struct s)).mapFree = true) :
    TRun.declMem (.struct s) (some (.copy src hm)) hm σ =
      .ok ⟨σ.allocPush (R := .struct s) (copiedFields (structDef s) hp v),
        List.prefix_append _ _⟩ := by
  rw [TRun.declMem, copiedStruct_rhs σ src r hr v hv hp hm]
  rfl

/-- Rebinding from storage allocates a new object; prior aliases retain theirs. -/
theorem copiedStruct_rebind {Γ : Ctx} (σ : State C Γ) {s : Name}
    (dst : Idx Γ (.mem (.struct s)))
    (src : SPath C Γ (.ref (.struct s))) (r : SRef C (.ref (.struct s)))
    (hr : src.resolveT σ = .ok r) (v : SFields (structDef s))
    (hv : σ.storage.find r = some (.struct v))
    (hp : primitiveMembers (structDef s) = true) (hm : (Ty.ref (.struct s)).mapFree = true) :
    TRun.rebindMem dst (.copy src hm) σ =
      .ok ⟨(σ.alloc (R := .struct s) (copiedFields (structDef s) hp v)).1.setLocal dst
        (some (σ.alloc (R := .struct s) (copiedFields (structDef s) hp v)).2),
        List.prefix_append _ _⟩ := by
  rw [TRun.rebindMem, copiedStruct_rhs σ src r hr v hv hp hm]
  rfl

/-- Fresh copies preserve every older typed heap object. -/
theorem copiedStruct_keeps {H : HTy} (hp : Heap H) {s : Name}
    (v : SFields (structDef s)) (h : primitiveMembers (structDef s) = true) :
    Heap.Keeps (List.prefix_append H [.struct s]) hp
      (hp.alloc (R := .struct s) (copiedFields (structDef s) h v)).1 :=
  Heap.keeps_alloc hp _

/-- No old reference is the copy's freshly allocated identity. -/
theorem copiedStruct_fresh {H : HTy} (hp : Heap H) {s : Name}
    (v : SFields (structDef s)) (h : primitiveMembers (structDef s) = true)
    {R : RefTy} (r : HRef H R) :
    r.id ≠ (hp.alloc (R := .struct s) (copiedFields (structDef s) h v)).2.id := by
  exact Nat.ne_of_lt r.id_lt

end Solidity.Evm.Memory
