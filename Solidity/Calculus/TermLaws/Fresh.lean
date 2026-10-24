import Solidity.Calculus.TermLaws.Reads

/-!
# Term laws: allocations, copies, the bundle

Fresh allocations, copies between storage and memory, the laws bundled,
premises about closed terms, and the pins.

A piece of `Calculus/TermLaws.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3)

variable {C : Contract} {Γ : Ctx}

/-! ## Fresh allocations

A read below an allocation `addM(m, R)` is answered on the typed heap: the
allocation keeps every older object (`Heap.Keeps`, `SVal.keeps_copyStToM`),
and its fresh object holds the default of `R` at every member and fixed
element (`Heap.dflt_allocDefault`).  An address whose object is older than
the allocation (`Tm.boundedIn`) reads what it read before
(`Tm.readOnAddMFrame_exact`); one at a path below the fresh root
(`Tm.freshPath?`, `Srt.FreshRead`) whose declared type is a primitive reads
its default (`Tm.readOnAddM_exact`). -/

/-- A memory write that returns: its parts, and the heap it leaves. -/
theorem Tm.write_some {σ : State C Γ} {T : Ty} {m : Tm C Γ .mem} {a : Tm C Γ (.addr T)} {v : Tm C Γ (.mv T)}
    {μ' : Grown σ.H (fun _ => Unit)} (h : (Tms.MTerm.write m a v).eval σ = some μ') :
    ∃ (μ : Grown σ.H (fun _ => Unit)) (ad : MAddrT T) (w : MvT T) (ra : MAddr μ.H' T)
      (mv : MVal μ.H' T) (hp : Heap μ.H'), m.eval σ = some μ ∧ a.eval σ = some ad ∧
      v.eval σ = some w ∧ ad.resolve μ.H' = some ra ∧ MvT.toMVal μ.H' T w = some mv ∧
      μ.heap.writeAddr ra mv = some hp ∧ μ' = ⟨μ.ext, hp, ()⟩ := by
  have h : ((m.eval σ).bind fun μ => (a.eval σ).bind fun ad => (v.eval σ).bind fun w =>
      μ.writeT ad w) = some μ' := h
  simp only [Grown.writeT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨μ, hm, ad, ha, w, hv, ra, hra, mv, hmv, hp, hw, rfl⟩ := h
  exact ⟨μ, ad, w, ra, mv, hp, hm, ha, hv, hra, hmv, hw, rfl⟩

theorem Tm.read_evalT {σ : State C Γ} {P : PrimTy} (X : Tm C Γ .mem) (b : Tm C Γ (.addr (.prim P))) :
    (Tms.Term.read X b).eval σ = (X.eval σ).bind fun μ => (b.eval σ).bind fun bd =>
      (bd.resolve μ.H').bind fun rb => μ.heap.readAddr rb := rfl

theorem Tm.iread_evalT {σ : State C Γ} {R : RefTy} (X : Tm C Γ .mem) (b : Tm C Γ (.addr (.ref R))) :
    (Tms.ITerm.read X b).eval σ = (X.eval σ).bind fun μ => (b.eval σ).bind fun bd =>
      ((bd.resolve μ.H').bind fun rb => μ.heap.readAddr rb).bind fun r => some r.id := rfl

/-- At the memory sort: a memory whose heap typing extends `ν`'s. -/
def Srt.Grows {H : HTy} (ν : Grown H (fun _ => Unit)) : (u : Srt) → Option (u.Den C H) → Prop
  | .mem, x => ∀ μ, x = some μ → ν.H' <+: μ.H'
  | _, _ => True

/-- A memory on the spine of a memory term: the term's heap typing extends
the memory's. -/
theorem Tm.onSpineAny_grows {σ : State C Γ} {w : Tm C Γ .mem} {ν : Grown σ.H (fun _ => Unit)}
    (hw : w.eval σ = some ν) {u : Srt} (t : Tm C Γ u) (h : Tm.onSpineAny w t = true) :
    Srt.Grows (C := C) ν u (t.eval σ) := by
  induction t with
  | app1 o x ihx =>
    cases o with
    | addM R hR =>
      intro μ hμ
      simp only [Tm.onSpineAny, Bool.or_eq_true] at h
      simp only [Tm.eval_app1, Op1.eval_eq_evalM, Op1.evalM, Option.map_eq_some_iff] at hμ
      obtain ⟨μ₀, hμ₀, rfl⟩ := hμ
      have h₀ : ν.H' <+: μ₀.H' := by
        rcases h with h | h
        · cases Tm.sigma_eq_of_beqR h
          rw [hw] at hμ₀
          cases hμ₀
          exact List.prefix_refl _
        · exact ihx h μ₀ hμ₀
      exact h₀.trans (μ₀.heap.allocDefault R hR).ext
    | _ => trivial
  | app2 o x y ihx _ =>
    cases o with
    | copySt hT =>
      intro μ hμ
      simp only [Tm.onSpineAny, Bool.or_eq_true] at h
      simp only [Tm.eval_app2, Op2.eval_eq_evalM, Op2.evalM, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at hμ
      obtain ⟨μ₀, hμ₀, v, -, rfl⟩ := hμ
      have h₀ : ν.H' <+: μ₀.H' := by
        rcases h with h | h
        · cases Tm.sigma_eq_of_beqR h
          rw [hw] at hμ₀
          cases hμ₀
          exact List.prefix_refl _
        · exact ihx h μ₀ hμ₀
      exact h₀.trans (v.copyStToM μ₀.heap hT).ext
    | _ => trivial
  | app3 o x y z ihx _ _ =>
    cases o with
    | write =>
      intro μ hμ
      simp only [Tm.onSpineAny, Bool.or_eq_true] at h
      obtain ⟨μ₀, ad, w', ra, mv, hp, hμ₀, -, -, -, -, -, rfl⟩ := Tm.write_some hμ
      rcases h with h | h
      · cases Tm.sigma_eq_of_beqR h
        rw [hw] at hμ₀
        cases hμ₀
        exact List.prefix_refl _
      · exact ihx h μ₀ hμ₀
    | _ => trivial
  | _ => cases u <;> trivial

theorem Tm.onSpine_grows {σ : State C Γ} {t w : Tm C Γ .mem} (h : t.onSpine w = true)
    {μ ν : Grown σ.H (fun _ => Unit)} (ht : t.eval σ = some μ) (hw : w.eval σ = some ν) :
    ν.H' <+: μ.H' := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain rfl := Tm.eq_of_beqR h
    rw [ht] at hw
    cases hw
    exact List.prefix_refl _
  · exact Tm.onSpineAny_grows hw t h μ ht

/-- An identity, or the object of an address, below `n`; other sorts carry
nothing. -/
def Srt.Bnd {H : HTy} (n : Nat) : (u : Srt) → Option (u.Den C H) → Prop
  | .ident _, x => ∀ id, x = some id → id < n
  | .addr _, x => ∀ ad, x = some ad → MAddrT.id ad < n
  | _, _ => True

/-- The identity a term reads is below the heap typing the memory `M`
leaves: a fresh root allocated on `M`'s spine, an identity read out of a
memory on it, a local's; an address is bounded where its object is.
Generic in the sort. -/
def Tm.boundedIn : {u : Srt} → Tm C Γ u → Tm C Γ .mem → Bool
  | _, .app1 (.alloc R h) m₀, M => M.onSpine (.app1 (.addM R h) m₀)
  | _, .app2 (.copy h) m₀ v, M => M.onSpine (.app2 (.copySt h) m₀ v)
  | _, .app2 .iread X _, M => M.onSpine X
  | _, .pvI _, _ => true
  | _, .app1 (.mfield _) i, M => i.boundedIn M
  | _, .app2 (.mat _) i _, M => i.boundedIn M
  | _, _, _ => false

theorem Tm.boundedIn_eval {σ : State C Γ} {M : Tm C Γ .mem} {μ : Grown σ.H (fun _ => Unit)}
    (hM : M.eval σ = some μ) {u : Srt} (t : Tm C Γ u) (h : t.boundedIn M = true) :
    Srt.Bnd (C := C) μ.H'.length u (t.eval σ) := by
  induction t with
  | pvI i =>
    intro id hid
    simp only [Tm.eval, Option.map_eq_some_iff] at hid
    obtain ⟨r, -, rfl⟩ := hid
    exact Nat.lt_of_lt_of_le (HRef.id_lt r) μ.ext.length_le
  | app1 o x ihx =>
    cases o with
    | alloc R hR =>
      intro id hid
      simp only [Tm.boundedIn] at h
      simp only [Tm.eval_app1, Op1.eval_eq_evalM, Op1.evalM, Option.map_eq_some_iff] at hid
      obtain ⟨μ₀, hμ₀, rfl⟩ := hid
      have hA : (Tm.app1 (.addM R hR) x).eval σ = some (μ₀.then (μ₀.heap.allocDefault R hR)) := by
        simp only [Tm.eval_app1, Op1.eval_eq_evalM, Op1.evalM, hμ₀, Option.map_some]
      exact Nat.lt_of_lt_of_le (HRef.id_lt _) (Tm.onSpine_grows h hM hA).length_le
    | mfield hf =>
      intro ad had
      simp only [Tm.boundedIn] at h
      simp only [Tm.eval_app1, Op1.eval_eq_evalM, Op1.evalM, Option.map_eq_some_iff] at had
      obtain ⟨id, hid, rfl⟩ := had
      exact ihx h id hid
    | _ => cases u <;> trivial
  | app2 o x y ihx _ =>
    cases o with
    | copy hR =>
      intro id hid
      simp only [Tm.boundedIn] at h
      simp only [Tm.eval_app2, Op2.eval_eq_evalM, Op2.evalM, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at hid
      obtain ⟨μ₀, hμ₀, v, hv, rfl⟩ := hid
      have hA : (Tm.app2 (.copySt hR) x y).eval σ =
          some (μ₀.then (v.copyStToM μ₀.heap hR)) := by
        simp only [Tm.eval_app2, Op2.eval_eq_evalM, Op2.evalM, hμ₀, hv, Option.bind_eq_bind,
          Option.bind_some]
      exact Nat.lt_of_lt_of_le (HRef.id_lt _) (Tm.onSpine_grows h hM hA).length_le
    | iread =>
      intro id hid
      simp only [Tm.boundedIn] at h
      simp only [Tm.eval_app2, Op2.eval_eq_evalM, Op2.evalM, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at hid
      obtain ⟨μ₀, hμ₀, ad, -, r, -, rfl⟩ := hid
      exact Nat.lt_of_lt_of_le (HRef.id_lt r) (Tm.onSpine_grows h hM hμ₀).length_le
    | mat a =>
      intro ad had
      simp only [Tm.boundedIn] at h
      simp only [Tm.eval_app2, Op2.eval_eq_evalM, Op2.evalM, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at had
      obtain ⟨id, hid, k, -, rfl⟩ := had
      exact ihx h id hid
    | _ => cases u <;> trivial
  | _ => cases u <;> trivial

/-- `addM(m, R)` returns: `m` does, and the allocation is its default. -/
theorem Tm.addM_some {σ : State C Γ} {m : Tm C Γ .mem} {R : RefTy} {hR : (Ty.ref R).mapFree = true}
    {μ₁ : Grown σ.H (fun _ => Unit)} (h : (Tms.MTerm.addM m R hR).eval σ = some μ₁) :
    ∃ μ₀, m.eval σ = some μ₀ ∧ μ₁ = μ₀.then (μ₀.heap.allocDefault R hR) := by
  simp only [Tms.MTerm.addM, Tm.eval_app1, Op1.eval_eq_evalM, Op1.evalM,
    Option.map_eq_some_iff] at h
  obtain ⟨μ₀, h, rfl⟩ := h
  exact ⟨μ₀, h, rfl⟩

/-- A read below an allocation, at an address whose object is older: the
old read, weakened. -/
theorem Tm.readAddM_old {σ : State C Γ} {m : Tm C Γ .mem} {μ₀ : Grown σ.H (fun _ => Unit)}
    (hm : m.eval σ = some μ₀) {T : Ty} {b : Tm C Γ (.addr T)} (h : b.boundedIn m = true)
    (R : RefTy) (hR : (Ty.ref R).mapFree = true) {bd : MAddrT T} (hb : b.eval σ = some bd) :
    ((bd.resolve (μ₀.then (μ₀.heap.allocDefault R hR)).H').bind fun rb =>
        (μ₀.then (μ₀.heap.allocDefault R hR)).heap.readAddr rb) =
      ((bd.resolve μ₀.H').bind fun rb => μ₀.heap.readAddr rb).map
        (MVal.wk (μ₀.heap.allocDefault R hR).ext T) :=
  Grown.read_then_old μ₀ _ (SVal.keeps_copyStToM _ hR μ₀.heap) bd (Tm.boundedIn_eval hm b h bd hb)

theorem Tm.readOnAddMFrame_exact {σ : State C Γ} {m : Tm C Γ .mem} {R : RefTy}
    {hR : (Ty.ref R).mapFree = true} {P : PrimTy} {b : Tm C Γ (.addr (.prim P))}
    (h : b.boundedIn m = true) (hX : (Tms.MTerm.addM m R hR).eval σ ≠ none) :
    (Tms.Term.read (Tms.MTerm.addM m R hR) b).eval σ = (Tms.Term.read m b).eval σ := by
  obtain ⟨μ₁, hX⟩ := Option.ne_none_iff_exists'.1 hX
  obtain ⟨μ₀, hm, rfl⟩ := Tm.addM_some hX
  rw [Tm.read_evalT, Tm.read_evalT, hX, hm, Option.bind_some, Option.bind_some]
  cases hb : b.eval σ with
  | none => rfl
  | some bd =>
    simp only [Option.bind_some]
    rw [Tm.readAddM_old hm h R hR hb]
    exact MVal.map_wk_prim _ _

theorem Tm.readOnAddMFrameIdentity_exact {σ : State C Γ} {m : Tm C Γ .mem} {R : RefTy}
    {hR : (Ty.ref R).mapFree = true} {R' : RefTy} {b : Tm C Γ (.addr (.ref R'))}
    (h : b.boundedIn m = true) (hX : (Tms.MTerm.addM m R hR).eval σ ≠ none) :
    (Tms.ITerm.read (Tms.MTerm.addM m R hR) b).eval σ = (Tms.ITerm.read m b).eval σ := by
  obtain ⟨μ₁, hX⟩ := Option.ne_none_iff_exists'.1 hX
  obtain ⟨μ₀, hm, rfl⟩ := Tm.addM_some hX
  rw [Tm.iread_evalT, Tm.iread_evalT, hX, hm, Option.bind_some, Option.bind_some]
  cases hb : b.eval σ with
  | none => rfl
  | some bd =>
    simp only [Option.bind_some]
    rw [Tm.readAddM_old hm h R hR hb]
    exact MVal.bind_id_map_wk _ _

/-- `M` is `addM(m, R)`. -/
def Tm.isAddM (M m : Tm C Γ .mem) (R : RefTy) : Bool :=
  match M with
  | .app1 (.addM R' _) m' => m'.beqR m && R' == R
  | _ => false

theorem Tm.eq_of_isAddM {M m : Tm C Γ .mem} {R : RefTy} (h : M.isAddM m R = true) :
    ∃ hR, M = Tms.MTerm.addM m R hR := by
  unfold Tm.isAddM at h
  split at h
  · rename_i R' hR' m'
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hm, rfl⟩ := h
    obtain rfl := Tm.eq_of_beqR hm
    exact ⟨hR', rfl⟩
  · cases h

/-- One step of `Tm.freshPath?` at a unary symbol: `freshId(addM(m, R))`
is the root, `i.f` the member `f` below `i`'s path `r`. -/
def Op1.freshStep (m : Tm C Γ .mem) (R : RefTy) {a s : Srt} :
    Op1 C a s → Tm C Γ a → Option (List Semantics.Selector) → Option (List Semantics.Selector)
  | .alloc R' _, x, _ => if x.beqR m && R' == R then some [] else none
  | .mfield (f := f) _, _, r => r.map (· ++ [Semantics.Selector.field f])
  | _, _, _ => none

/-- One step of `Tm.freshPath?` at a binary symbol: `read(addM(m, R), a)`
is what `a` reads (`ry`), `i[k]` (a literal `k`) the element `k` below
`i`'s path `rx`. -/
def Op2.freshStep (m : Tm C Γ .mem) (R : RefTy) {a b s : Srt} :
    Op2 C a b s → Tm C Γ a → Tm C Γ b → Option (List Semantics.Selector) →
      Option (List Semantics.Selector) → Option (List Semantics.Selector)
  | .iread, x, _, _, ry => if x.isAddM m R then ry else none
  | .mat _, _, y, rx, _ => y.uintLit?.bind fun k => rx.map (· ++ [Semantics.Selector.idx k])
  | _, _, _, _, _ => none

/-- The path at which a term reads below the root `addM(m, R)` allocates.
Generic in the sort. -/
def Tm.freshPath? (m : Tm C Γ .mem) (R : RefTy) : {u : Srt} → Tm C Γ u → Option (List Semantics.Selector)
  | _, .app1 o x => o.freshStep m R x (Tm.freshPath? m R x)
  | _, .app2 o x y => o.freshStep m R x y (Tm.freshPath? m R x) (Tm.freshPath? m R y)
  | _, _ => none

/-- What a term at a fresh path `p` below the root of `addM(m, R)` reads, by
sort, in the heap `hp₁` the allocation leaves: an identity is of an object
holding its default, of the type the path declares; an address resolves in
`hp₁` to a slot holding its default, and it reads where the path declares a
type, that type. -/
def Srt.FreshRead {H H₁ : HTy} (hp₁ : Heap H₁) (R : RefTy) (p : List Semantics.Selector) :
    (u : Srt) → Option (u.Den C H) → Prop
  | .ident R', x => (∀ id, x = some id → ∃ r : HRef H₁ R', r.id = id ∧ hp₁.Dflt (.ref R') r) ∧
      (∀ T', (Ty.ref R).memberTy p = some T' → T' = .ref R' ∧ ∃ id, x = some id)
  | .addr T, x => (∀ ad, x = some ad → ∃ ra : MAddr H₁ T, ad.resolve H₁ = some ra ∧
        ∀ v, hp₁.readAddr ra = some v → hp₁.Dflt T v) ∧
      (∀ T', (Ty.ref R).memberTy p = some T' → T' = T ∧
        ∃ ad ra v, x = some ad ∧ ad.resolve H₁ = some ra ∧ hp₁.readAddr ra = some v)
  | _, _ => True

namespace Srt.FreshRead

variable {H H₁ : HTy} {hp₁ : Heap H₁} {R : RefTy}

/-- The root: `freshId(addM(m, R))`. -/
theorem root (r : HRef H₁ R) (hd : hp₁.Dflt (.ref R) r) :
    Srt.FreshRead (C := C) (H := H) hp₁ R [] (.ident R) (some r.id) := by
  refine ⟨fun id hid => ?_, fun T' hT' => ?_⟩
  · cases hid
    exact ⟨r, rfl, hd⟩
  · simp only [Ty.memberTy, Option.some.injEq] at hT'
    exact ⟨hT'.symm, _, rfl⟩

/-- A member `i.f` of an identity `i` at the path `p`. -/
theorem field {p : List Semantics.Selector} {s f : Name} {T : Ty}
    (hf : Semantics.lookupBy f (Semantics.structDef s) = some T) {x : Option Nat}
    (hx : Srt.FreshRead (C := C) (H := H) hp₁ R p (.ident (.struct s)) x) :
    Srt.FreshRead (C := C) (H := H) hp₁ R (p ++ [.field f]) (.addr T)
      (x.map fun id => MAddrT.field id hf) := by
  obtain ⟨ih1, ih2⟩ := hx
  have hres : ∀ r : HRef H₁ (.struct s),
      (MAddrT.field r.id hf).resolve H₁ = some (MAddr.field r hf) := fun r => by
    simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_self, Option.map_some]
  refine ⟨fun ad had => ?_, fun T' hT' => ?_⟩
  · obtain ⟨id, hid, rfl⟩ := Option.map_eq_some_iff.1 had
    obtain ⟨r, rfl, hd⟩ := ih1 id hid
    refine ⟨.field r hf, hres r, fun v hv => ?_⟩
    simp only [Heap.readAddr, Option.some.injEq] at hv
    subst hv
    cases hd with
    | struct _ h => exact h hf
  · obtain ⟨R'', hR''⟩ := Ty.memberTy_snoc_some hT'
    obtain ⟨hR, id, hid⟩ := ih2 _ hR''
    cases hR
    obtain ⟨r, rfl, -⟩ := ih1 _ hid
    rw [Ty.memberTy_append, hR''] at hT'
    simp only [Option.bind_some, Ty.memberTy, Ty.at, hf, Option.some.injEq] at hT'
    exact ⟨hT'.symm, _, _, _, by rw [hid]; rfl, hres r, rfl⟩

/-- An element `i[k]` of an identity `i` at the path `p`, at a literal `k`. -/
theorem index {p : List Semantics.Selector} {R' : RefTy} {E : Ty} (a : ArrTy R' E)
    (k : PrimTy.uint.Denote)
    {x : Option Nat} (hx : Srt.FreshRead (C := C) (H := H) hp₁ R p (.ident R') x) :
    Srt.FreshRead (C := C) (H := H) hp₁ R (p ++ [.idx k]) (.addr E)
      (x.map fun id => MAddrT.index id a k) := by
  obtain ⟨ih1, ih2⟩ := hx
  have hres : ∀ r : HRef H₁ R',
      (MAddrT.index r.id a k).resolve H₁ = some (MAddr.index r a k) := fun r => by
    simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_self, Option.map_some]
  refine ⟨fun ad had => ?_, fun T' hT' => ?_⟩
  · obtain ⟨id, hid, rfl⟩ := Option.map_eq_some_iff.1 had
    obtain ⟨r, rfl, hd⟩ := ih1 id hid
    refine ⟨.index r a k, hres r, fun v hv => ?_⟩
    simp only [Heap.readAddr, Heap.index] at hv
    cases a with
    | dyn =>
      cases hd with
      | array _ h =>
        have hl : (MObj.elems .dyn (hp₁.get r)).length = 0 := h
        simp only [List.length_eq_zero_iff.1 hl, List.getElem?_nil, reduceCtorEq] at hv
    | fixed =>
      cases hd with
      | fixed _ h => exact h v (List.mem_of_getElem? hv)
  · obtain ⟨R'', hR''⟩ := Ty.memberTy_snoc_some hT'
    obtain ⟨hR, id, hid⟩ := ih2 _ hR''
    cases hR
    obtain ⟨r, rfl, -⟩ := ih1 _ hid
    rw [Ty.memberTy_append, hR''] at hT'
    cases a with
    | dyn => simp only [Option.bind_some, Ty.memberTy, Ty.at, Option.bind_none, reduceCtorEq] at hT'
    | @fixed E n =>
      simp only [Option.bind_some, Ty.memberTy, Ty.at] at hT'
      split at hT'
      · rename_i hk
        simp only [Option.bind_some, Option.some.injEq] at hT'
        have hn : (MObj.elems .fixed (hp₁.get r)).length = n := by
          rw [MObj.elems_fixed]
          exact (hp₁.get r : {l : List (MVal H₁ E) // l.length = n}).2
        have hlt : k.1.toNat < (MObj.elems .fixed (hp₁.get r)).length := by omega
        refine ⟨hT'.symm, _, _, (MObj.elems .fixed (hp₁.get r))[k.1.toNat], by rw [hid]; rfl, hres r, ?_⟩
        simp only [Heap.readAddr, Heap.index, hk, if_true, List.getElem?_eq_getElem hlt]
      · simp only [Option.bind_none, reduceCtorEq] at hT'

/-- An identity read out of the fresh memory at an address of the path. -/
theorem iread {p : List Semantics.Selector} {R' : RefTy} {b : Option (MAddrT (.ref R'))}
    (hb : Srt.FreshRead (C := C) (H := H) hp₁ R p (.addr (.ref R')) b) :
    Srt.FreshRead (C := C) (H := H) hp₁ R p (.ident R')
      (b.bind fun bd => ((bd.resolve H₁).bind fun rb => hp₁.readAddr rb).bind
        fun r => some (r : HRef H₁ R').id) := by
  obtain ⟨ih1, ih2⟩ := hb
  refine ⟨fun id hid => ?_, fun T' hT' => ?_⟩
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at hid
    obtain ⟨bd, hbd, r, ⟨ra, hra, hrd⟩, rfl⟩ := hid
    obtain ⟨ra', hra', hd⟩ := ih1 bd hbd
    rw [hra] at hra'
    cases hra'
    exact ⟨r, rfl, hd r hrd⟩
  · obtain ⟨hT, bd, ra, v, hbd, hra, hv⟩ := ih2 T' hT'
    refine ⟨hT, (v : HRef H₁ R').id, ?_⟩
    rw [hbd, Option.bind_some, hra, Option.bind_some, hv, Option.bind_some]

/-- A word read at the path, where the path declares a word: the default. -/
theorem read_prim {p : List Semantics.Selector} {P : PrimTy} {b : Option (MAddrT (.prim P))}
    (hb : Srt.FreshRead (C := C) (H := H) hp₁ R p (.addr (.prim P)) b)
    (hT : (Ty.ref R).memberTy p = some (.prim P)) :
    (b.bind fun bd => (bd.resolve H₁).bind fun rb => hp₁.readAddr rb) = some (PrimTy.dflt P) := by
  obtain ⟨-, bd, ra, v, hbd, hra, hv⟩ := hb.2 _ hT
  obtain ⟨ra', hra', hd⟩ := hb.1 bd hbd
  rw [hra] at hra'
  cases hra'
  rw [hbd, Option.bind_some, hra, Option.bind_some, hv]
  exact congrArg some (hd v hv).prim_eq

end Srt.FreshRead

theorem Tm.freshPath_eval {σ : State C Γ} {m : Tm C Γ .mem} {R : RefTy}
    {hR : (Ty.ref R).mapFree = true} {μ₀ : Grown σ.H (fun _ => Unit)} (hm : m.eval σ = some μ₀)
    {u : Srt} (t : Tm C Γ u) : ∀ {p : List Semantics.Selector}, Tm.freshPath? m R t = some p →
      Srt.FreshRead (C := C) (μ₀.heap.allocDefault R hR).heap R p u (t.eval σ) := by
  induction t with
  | app1 o x ihx =>
    intro p h
    cases o with
    | alloc R' hR' =>
      simp only [Tm.freshPath?, Op1.freshStep] at h
      split at h
      · rename_i hmR
        simp only [Bool.and_eq_true, beq_iff_eq] at hmR
        obtain ⟨hmm, rfl⟩ := hmR
        obtain rfl := Tm.eq_of_beqR hmm
        cases h
        have he : (Tm.app1 (.alloc R' hR') x).eval σ = some (μ₀.heap.allocDefault R' hR).val.id := by
          simp only [Tm.eval_app1, Op1.eval_eq_evalM, Op1.evalM, hm, Option.map_some]
        rw [he]
        exact Srt.FreshRead.root _ (Heap.dflt_allocDefault μ₀.heap R' hR)
      · cases h
    | mfield hf =>
      simp only [Tm.freshPath?, Op1.freshStep, Option.map_eq_some_iff] at h
      obtain ⟨p', hp', rfl⟩ := h
      have he : (Tm.app1 (.mfield hf) x).eval σ = (x.eval σ).map fun id => MAddrT.field id hf := by
        simp only [Tm.eval_app1, Op1.eval_eq_evalM, Op1.evalM]
      rw [he]
      exact Srt.FreshRead.field hf (ihx hp')
    | _ => simp only [Tm.freshPath?, Op1.freshStep, reduceCtorEq] at h
  | app2 o x y ihx ihy =>
    intro p h
    cases o with
    | iread =>
      simp only [Tm.freshPath?, Op2.freshStep] at h
      split at h
      · rename_i hM
        obtain ⟨hR', rfl⟩ := Tm.eq_of_isAddM hM
        have hX : (Tms.MTerm.addM m R hR').eval σ = some (μ₀.then (μ₀.heap.allocDefault R hR)) := by
          simp only [Tms.MTerm.addM, Tm.eval_app1, Op1.eval_eq_evalM, Op1.evalM, hm,
            Option.map_some]
        rw [show Tm.app2 .iread (Tms.MTerm.addM m R hR') y = Tms.ITerm.read _ y from rfl,
          Tm.iread_evalT, hX, Option.bind_some]
        exact Srt.FreshRead.iread (ihy h)
      · cases h
    | mat a =>
      simp only [Tm.freshPath?, Op2.freshStep, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at h
      obtain ⟨k, hk, p', hp', rfl⟩ := h
      have hw := Tm.uintLit?_eval (σ := σ) hk
      have he : (Tm.app2 (.mat a) x y).eval σ = (x.eval σ).map fun id => MAddrT.index id a k := by
        cases hx : x.eval σ with
        | none => exact Tm.eval_app2_none _ x y hx
        | some id =>
          simp only [Tm.eval_app2, Op2.eval_eq_evalM, Op2.evalM, hx, hw, Option.bind_eq_bind,
            Option.bind_some, Option.map_some]
      rw [he]
      exact Srt.FreshRead.index a k (ihx hp')
    | _ => simp only [Tm.freshPath?, Op2.freshStep, reduceCtorEq] at h
  | _ => intro p h; simp only [Tm.freshPath?, reduceCtorEq] at h

theorem Tm.readOnAddM_exact {σ : State C Γ} {m : Tm C Γ .mem} {R : RefTy}
    {hR : (Ty.ref R).mapFree = true} {P : PrimTy} {b : Tm C Γ (.addr (.prim P))}
    (h : (Tm.freshPath? m R b).bind (Ty.ref R).memberTy = some (.prim P))
    (hX : (Tms.MTerm.addM m R hR).eval σ ≠ none) :
    (Tms.Term.read (Tms.MTerm.addM m R hR) b).eval σ =
      (Tm.app0 (.lit (PrimTy.dflt P)) : Tm C Γ (.val P)).eval σ := by
  obtain ⟨μ₁, hX⟩ := Option.ne_none_iff_exists'.1 hX
  obtain ⟨μ₀, hm, rfl⟩ := Tm.addM_some hX
  obtain ⟨p, hp, hT⟩ := Option.bind_eq_some_iff.1 h
  rw [Tm.read_evalT, hX, Option.bind_some]
  exact Srt.FreshRead.read_prim (Tm.freshPath_eval (hR := hR) hm b hp) hT

/-! ## Copies between storage and memory

A member read out of a copy is answered on the typed values: a copy of a
storage struct into memory holds its words (`SVal.copyStToM_field`), a copy
of a memory struct into storage the object's (`MVal.copyMToSt_field`), and
a copy laid over a struct is read member by member
(`SVal.find_overlay_field`). -/

/-- A word laid over a word is the new one. -/
theorem SVal.overlay_prim' {p : PrimTy} (o n : SVal (.prim p)) : o.overlay n = n := by
  cases n; exact SVal.overlay_prim o _

/-- **A member of a struct copy**: the new struct's member laid over the old
one's. -/
theorem SVal.find_overlay_field {s f : Name} {T U : Ty} (o n : SVal (.ref (.struct s)))
    (h : Semantics.lookupBy f (Semantics.structDef s) = some T) (p : Path T U) :
    (o.overlay n).find (.field h p) =
      (n.find (.field h .nil)).bind fun n' => (((SVal.view o : SFields _).get h).overlay n').find p := by
  cases o with
  | struct ofs =>
    cases n with
    | struct nfs =>
      rw [SVal.overlay_struct, SVal.find_field, SFields.get_overlay, SVal.find_field,
        SVal.find_nil, Option.bind_some, SVal.view_struct]

/-- A member read out of a copy of a storage struct: what the storage holds
at the member. -/
theorem Tm.readFromCopyToStorage_exact {σ : State C Γ} {m : Tm C Γ .mem} {s : Tm C Γ .st} {sn f : Name}
    {P : PrimTy} {p : Tm C Γ (.path (.ref (.struct sn)))}
    {hT : (Ty.ref (.struct sn)).mapFree = true} {hf : C.fieldType sn f = some (.prim P)}
    (hX : (Tms.MTerm.copySt m (Tms.SValT.find s p) hT).eval σ ≠ none) :
    (Tms.Term.read (Tms.MTerm.copySt m (Tms.SValT.find s p) hT)
        (Tms.MAddr.field (Tms.ITerm.copy m (Tms.SValT.find s p) hT) f hf)).eval σ =
      (Tms.Term.find s (Tms.PTerm.field p f hf)).eval σ := by
  obtain ⟨μ₁, hX⟩ := Option.ne_none_iff_exists'.1 hX
  simp only [Tms.MTerm.copySt, Tms.SValT.find, Tm.eval_app2, Op2.eval_eq_evalM, Op2.evalM,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hX
  obtain ⟨μ₀, hm, sv, ⟨st, hs, r, hp, hsv⟩, rfl⟩ := hX
  have hv : (Tms.SValT.find s p).eval σ = some sv := by
    simp only [Tms.SValT.find, Tm.eval_app2, Op2.eval_eq_evalM, Op2.evalM, hs, hp, hsv,
      Option.bind_eq_bind, Option.bind_some]
  have hX' : (Tms.MTerm.copySt m (Tms.SValT.find s p) hT).eval σ =
      some (μ₀.then (sv.copyStToM μ₀.heap hT)) := by
    simp only [Tms.MTerm.copySt, Tm.eval_app2, Op2.eval_eq_evalM, Op2.evalM, hm, hv,
      Option.bind_eq_bind, Option.bind_some]
  have hI : (Tms.ITerm.copy m (Tms.SValT.find s p) hT).eval σ =
      some (sv.copyStToM μ₀.heap hT).val.id := by
    simp only [Tms.ITerm.copy, Tm.eval_app2, Op2.eval_eq_evalM, Op2.evalM, hm, hv,
      Option.bind_eq_bind, Option.bind_some]
  have hL : (Tms.Term.read (Tms.MTerm.copySt m (Tms.SValT.find s p) hT)
        (Tms.MAddr.field (Tms.ITerm.copy m (Tms.SValT.find s p) hT) f hf)).eval σ =
      some ((sv.copyStToM μ₀.heap hT).heap.field (sv.copyStToM μ₀.heap hT).val hf) := by
    rw [Tm.read_evalT, hX', Option.bind_some]
    simp only [Tms.MAddr.field, Tm.eval_app1, Op1.eval_eq_evalM, Op1.evalM, hI, Option.map_some,
      Option.bind_some]
    show ((MAddrT.field (sv.copyStToM μ₀.heap hT).val.id hf).resolve
      (sv.copyStToM μ₀.heap hT).H').bind (sv.copyStToM μ₀.heap hT).heap.readAddr = _
    simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_self, Option.map_some,
      Option.bind_some]
    rfl
  rw [hL, SVal.copyStToM_field μ₀.heap sv hT hf]
  simp only [Tms.Term.find, Tms.PTerm.field, Tm.eval_app2, Tm.eval_app1, Op2.eval_eq_evalM,
    Op2.evalM, Op1.eval_eq_evalM, Op1.evalM, hs, hp, Option.map_some, Option.bind_eq_bind,
    Option.bind_some]
  rw [show SRef.field r hf = r.append (.field hf .nil) from rfl, Storage.find_append, hsv,
    Option.bind_some]
  cases sv with
  | struct fs => rw [SVal.find_field, SVal.find_nil, Option.bind_some, SVal.view_struct]

/-- A member read out of a memory struct copied into storage: what the memory
holds at the member. -/
theorem Tm.findOnCopy_exact {σ : State C Γ} {m : Tm C Γ .mem} {s : Tm C Γ .st} {sn f : Name}
    {P : PrimTy} {p : Tm C Γ (.path (.ref (.struct sn)))} {i : Tm C Γ (.ident (.struct sn))}
    {hf : C.fieldType sn f = some (.prim P)}
    (hS : (Tms.STerm.save s p (Tms.SValT.copyMem m i)).eval σ ≠ none) :
    (Tms.Term.find (Tms.STerm.save s p (Tms.SValT.copyMem m i)) (Tms.PTerm.field p f hf)).eval σ =
      (Tms.Term.read m (Tms.MAddr.field i f hf)).eval σ := by
  obtain ⟨st', hS⟩ := Option.ne_none_iff_exists'.1 hS
  have hS' := hS
  simp only [Tms.STerm.save, Tms.SValT.copyMem, Tm.eval_app3, Tm.eval_app2, Op3.eval_eq_evalM,
    Op3.evalM, Op2.eval_eq_evalM, Op2.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at hS
  obtain ⟨st, hs, r, hp, v, ⟨μ, hm, id, hi, ref, href, rfl⟩, hw⟩ := hS
  have hid : ref.id = id := by
    simp only [HRef.ofId?] at href
    split at href
    · cases href; rfl
    · cases href
  simp only [Storage.write, SVal.isPrim, Ty.isPrimitive, Bool.false_eq_true, ite_false,
    Option.bind_eq_bind, Option.bind_eq_some_iff] at hw
  obtain ⟨cur, hcur, hsave⟩ := hw
  have hfind := Storage.find_save_same hsave
  have hR : (Tms.Term.read m (Tms.MAddr.field i f hf)).eval σ = some (μ.heap.field ref hf) := by
    rw [Tm.read_evalT, hm, Option.bind_some]
    simp only [Tms.MAddr.field, Tm.eval_app1, Op1.eval_eq_evalM, Op1.evalM, hi, Option.map_some,
      Option.bind_some]
    show ((MAddrT.field id hf).resolve μ.H').bind μ.heap.readAddr = _
    simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, href, Option.map_some,
      Option.bind_some]
    rfl
  rw [hR]
  simp only [Tms.Term.find, Tms.PTerm.field, Tm.eval_app2, Tm.eval_app1, Op2.eval_eq_evalM,
    Op2.evalM, Op1.eval_eq_evalM, Op1.evalM, hS', hp, Option.map_some, Option.bind_eq_bind,
    Option.bind_some]
  rw [show SRef.field r hf = r.append (.field hf .nil) from rfl, Storage.find_append, hfind,
    Option.bind_some, SVal.find_overlay_field, MVal.copyMToSt_field, Option.bind_some,
    SVal.overlay_prim', SVal.find_nil, Option.bind_some]
  rfl

/-- A law of a memory read, at the value or the identity sort: where the
read returns, the replacement returns the same (`EvalLaw.exact`). -/
inductive EvalLaw {Γ : Ctx} : {u : Srt} → Tm C Γ u → Tm C Γ u → Prop
  /-- **`readOnWrite`**: `read(write(m, a, v), a) ⇝ v` (`Heap.readAddr_writeAddr_same`). -/
  | readOnWrite {m : Tm C Γ .mem} {P : PrimTy} {a : Tm C Γ (.addr (.prim P))} {v : P.Denote} :
      EvalLaw (Tms.Term.read (Tms.MTerm.write m a (Tms.MValT.val (Tms.Term.lit v))) a)
        (Tms.Term.lit v)
  /-- **`readOnWriteFrame`** (solkey's `readOnWrite` `\else`): a write
  leaves every other address,
  `read(write(m, a, v), b) ⇝ read(m, b)` where `a` and `b` never meet
  (`Tm.apart?`, `Heap.readAddr_writeAddr_apart`). -/
  | readOnWriteFrame {m : Tm C Γ .mem} {T : Ty} {a : Tm C Γ (.addr T)} {v : Tm C Γ (.mv T)}
      {P : PrimTy} {b : Tm C Γ (.addr (.prim P))} (h : a.apart? b = true := by rfl) :
      EvalLaw (Tms.Term.read (Tms.MTerm.write m a v) b) (Tms.Term.read m b)
  /-- **`readOnWriteFrameIdentity`**: `readOnWriteFrame` at the identity sort. -/
  | readOnWriteFrameIdentity {m : Tm C Γ .mem} {T : Ty} {a : Tm C Γ (.addr T)}
      {v : Tm C Γ (.mv T)} {R : RefTy} {b : Tm C Γ (.addr (.ref R))}
      (h : a.apart? b = true := by rfl) :
      EvalLaw (Tms.ITerm.read (Tms.MTerm.write m a v) b) (Tms.ITerm.read m b)
  /-- **`readOnWriteIdentity`**: `readOnWrite` at the identity sort,
  `read(write(m, a, ref(i)), a) ⇝ i` (`Heap.readAddr_writeAddr_same`). -/
  | readOnWriteIdentity {m : Tm C Γ .mem} {R : RefTy} {a : Tm C Γ (.addr (.ref R))}
      {i : Tm C Γ (.ident R)} :
      EvalLaw (Tms.ITerm.read (Tms.MTerm.write m a (Tms.MValT.ref i)) a) i
  /-- **`findOnCopy`** (solkey's `findOnCopy` over `findOnSave`): a member
  read out of a memory object copied into storage is read out of memory,
  `find(save(s, p, copyMem(mtSt, m, i)), p.f) ⇝ read(m, i.f)` (`Tm.findOnCopy_exact`). -/
  | findOnCopy {s : Tm C Γ .st} {sn f : Name} {P : PrimTy} {p : Tm C Γ (.path (.ref (.struct sn)))}
      {m : Tm C Γ .mem} {i : Tm C Γ (.ident (.struct sn))} {hf : C.fieldType sn f = some (.prim P)}
      (hl : (f == "length") = false := by rfl) :
      EvalLaw (Tms.Term.find (Tms.STerm.save s p (Tms.SValT.copyMem m i)) (Tms.PTerm.field p f hf))
        (Tms.Term.read m (Tms.MAddr.field i f hf))
  /-- **`findOnCopyIn`**: `findOnCopy` in a storage of members,
  `find(save(select(s, r), q, copyMem(mtSt, m, i)), q.f) ⇝ read(m, i.f)`, where the
  read is the plain one (`Tm.base?`). -/
  | findOnCopyIn {s0 sn f : Name} {P : PrimTy} {S : Tm C Γ (.sts s0)}
      {q : Tm C Γ (.spath s0 (.ref (.struct sn)))} {m : Tm C Γ .mem}
      {i : Tm C Γ (.ident (.struct sn))} {hf : C.fieldType sn f = some (.prim P)}
      {s : Tm C Γ .st} {p : Tm C Γ (.path (.ref (.struct sn)))}
      (hb : (Tm.app2 .findIn (Tm.app3 .saveIn S q (Tms.SValT.copyMem m i))
          (Tm.app1 (.fieldIn hf) q)).base? =
        some (Tms.Term.find (Tms.STerm.save s p (Tms.SValT.copyMem m i)) (Tms.PTerm.field p f hf))
        := by rfl)
      (hl : (f == "length") = false := by rfl) :
      EvalLaw (Tm.app2 .findIn (Tm.app3 .saveIn S q (Tms.SValT.copyMem m i))
          (Tm.app1 (.fieldIn hf) q))
        (Tms.Term.read m (Tms.MAddr.field i f hf))
  /-- **`readFromCopyToStorage`** (solkey's `readFromCopyToStorage` `\then`): a member
  read out of a copy of a storage struct is read out of storage,
  `read(copySt(m, find(s, p)), freshId(copySt(m, find(s, p))).f) ⇝ find(s, p.f)`
  (`Tm.readFromCopyToStorage_exact`). -/
  | readFromCopyToStorage {m : Tm C Γ .mem} {s : Tm C Γ .st} {sn f : Name} {P : PrimTy}
      {p : Tm C Γ (.path (.ref (.struct sn)))} {hT : (Ty.ref (.struct sn)).mapFree = true}
      {hf : C.fieldType sn f = some (.prim P)} (hl : (f == "length") = false := by rfl) :
      EvalLaw (Tms.Term.read (Tms.MTerm.copySt m (Tms.SValT.find s p) hT)
          (Tms.MAddr.field (Tms.ITerm.copy m (Tms.SValT.find s p) hT) f hf))
        (Tms.Term.find s (Tms.PTerm.field p f hf))
  /-- **`readOnAddM`** (solkey's `readOnAddM` `\then`, then `initMember`,
  `initElement`): a primitive member or fixed element of a fresh
  object holds its type's default, `read(addM(m, R), a) ⇝ default`, where `a`
  reads at a path below the fresh root whose declared type is the primitive
  (`Tm.freshPath?`, `Tm.readOnAddM_exact`). -/
  | readOnAddM {m : Tm C Γ .mem} {R : RefTy} {hR : (Ty.ref R).mapFree = true} {P : PrimTy}
      {b : Tm C Γ (.addr (.prim P))}
      (h : (Tm.freshPath? m R b).bind (Ty.ref R).memberTy = some (.prim P) := by rfl) :
      EvalLaw (Tms.Term.read (Tms.MTerm.addM m R hR) b) (Tm.app0 (.lit (PrimTy.dflt P)))
  /-- **`readOnAddMFrame`** (solkey's `readOnAddM` `\else`): an allocation
  leaves every object allocated
  before it, `read(addM(m, R), a) ⇝ read(m, a)` where `a`'s object is older
  than `m` leaves (`Tm.boundedIn`, `Tm.readOnAddMFrame_exact`). -/
  | readOnAddMFrame {m : Tm C Γ .mem} {R : RefTy} {hR : (Ty.ref R).mapFree = true} {P : PrimTy}
      {b : Tm C Γ (.addr (.prim P))} (h : b.boundedIn m = true := by rfl) :
      EvalLaw (Tms.Term.read (Tms.MTerm.addM m R hR) b) (Tms.Term.read m b)
  /-- **`readOnAddMFrameIdentity`**: `readOnAddMFrame` at the identity sort. -/
  | readOnAddMFrameIdentity {m : Tm C Γ .mem} {R : RefTy} {hR : (Ty.ref R).mapFree = true}
      {R' : RefTy} {b : Tm C Γ (.addr (.ref R'))} (h : b.boundedIn m = true := by rfl) :
      EvalLaw (Tms.ITerm.read (Tms.MTerm.addM m R hR) b) (Tms.ITerm.read m b)

section EvalLawSound

variable {Γ : Ctx} {σ : State C Γ}

/-- What a law's left side reads: the memory of a read, or the storage of a
`find`. -/
inductive LawAnchor (C : Contract) (Γ : Ctx) where
  | mem (X : Tm C Γ .mem)
  | st (S : Tm C Γ .st)

/-- The anchor returns. -/
def LawAnchor.Evals (σ : State C Γ) : LawAnchor C Γ → Prop
  | .mem X => X.eval σ ≠ none
  | .st S => S.eval σ ≠ none

/-- The anchor of a read or a `find`. -/
def Op2.anchorArg {a b s : Srt} : Op2 C a b s → Tm C Γ a → Option (LawAnchor C Γ)
  | .read, x => some (.mem x)
  | .iread, x => some (.mem x)
  | .find, x => some (.st x)
  | _, _ => none

/-- The anchor of a read (`read(m, a)`, at either sort, or `find(s, p)`).
Generic in the sort. -/
def Tm.lawAnchor0? {u : Srt} : Tm C Γ u → Option (LawAnchor C Γ)
  | .app2 o x _ => o.anchorArg x
  | _ => none

/-- The anchor of a law's left side: its own, or, for a read in a storage of
members, its plain read's (`Tm.base?`). -/
def Tm.lawAnchor? {u : Srt} (t : Tm C Γ u) : Option (LawAnchor C Γ) :=
  (Tm.lawAnchor0? t).orElse fun _ => t.base?.bind Tm.lawAnchor0?

theorem Tm.lawAnchor0?_eval {u : Srt} {t : Tm C Γ u} {A : LawAnchor C Γ}
    (h : t.lawAnchor0? = some A) (ht : t.eval σ ≠ none) : A.Evals σ := by
  cases t with
  | app2 o x y =>
    cases o <;> simp only [Tm.lawAnchor0?, Op2.anchorArg, Option.some.injEq, reduceCtorEq] at h
    all_goals
      subst h
      exact fun hx => ht (Tm.eval_app2_none _ x y hx)
  | _ => simp only [Tm.lawAnchor0?, reduceCtorEq] at h

theorem Tm.lawAnchor?_eval {u : Srt} {t : Tm C Γ u} {A : LawAnchor C Γ} (h : t.lawAnchor? = some A)
    (ht : t.eval σ ≠ none) : A.Evals σ := by
  unfold Tm.lawAnchor? at h
  cases h0 : Tm.lawAnchor0? t with
  | some A' =>
    rw [h0] at h
    cases h
    exact Tm.lawAnchor0?_eval h0 ht
  | none =>
    rw [h0] at h
    simp only [Option.orElse, Option.bind_eq_some_iff] at h
    obtain ⟨t', hb, ha⟩ := h
    exact Tm.lawAnchor0?_eval ha (by rw [← Tm.base?_eval σ hb]; exact ht)

/-- **A memory law is exact past its write**: the read's memory returns
wherever the read does, and where it returns the two sides return alike. -/
theorem EvalLaw.exact {u : Srt} {t t' : Tm C Γ u} : EvalLaw t t' → ∃ A, t.lawAnchor? = some A ∧
    ∀ σ : State C Γ, A.Evals σ → t.eval σ = t'.eval σ
  | .readOnWrite => ⟨_, rfl, fun σ hX => by
      obtain ⟨μ', hX⟩ := Option.ne_none_iff_exists'.1 hX
      obtain ⟨μ, ad, w, ra, mv, hp, -, ha, hv, hra, hmv, hw, rfl⟩ := Tm.write_some hX
      cases hv
      cases hmv
      rw [Tm.read_evalT, hX, Option.bind_some, ha, Option.bind_some]
      show (ad.resolve μ.H').bind (fun rb => hp.readAddr rb) = _
      rw [hra, Option.bind_some, Heap.readAddr_writeAddr_same hw]
      rfl⟩
  | @EvalLaw.readOnWriteFrame _ _ m T a v P b h => ⟨_, rfl, fun σ hX => by
      obtain ⟨μ', hX⟩ := Option.ne_none_iff_exists'.1 hX
      obtain ⟨μ, ad, w, ra, mv, hp, hm, ha, -, hra, -, hw, rfl⟩ := Tm.write_some hX
      rw [Tm.read_evalT, Tm.read_evalT, hX, hm, Option.bind_some, Option.bind_some]
      cases hb : b.eval σ with
      | none => rfl
      | some bd =>
        simp only [Option.bind_some]
        show (bd.resolve μ.H').bind (fun rb => hp.readAddr rb) = _
        cases hrb : bd.resolve μ.H' with
        | none => rfl
        | some rb =>
          simp only [Option.bind_some]
          exact Heap.readAddr_writeAddr_apart hw (Tm.apart?_resolve σ h ha hb hra hrb)⟩
  | @EvalLaw.readOnWriteFrameIdentity _ _ m T a v R b h => ⟨_, rfl, fun σ hX => by
      obtain ⟨μ', hX⟩ := Option.ne_none_iff_exists'.1 hX
      obtain ⟨μ, ad, w, ra, mv, hp, hm, ha, -, hra, -, hw, rfl⟩ := Tm.write_some hX
      rw [Tm.iread_evalT, Tm.iread_evalT, hX, hm, Option.bind_some, Option.bind_some]
      cases hb : b.eval σ with
      | none => rfl
      | some bd =>
        simp only [Option.bind_some]
        show ((bd.resolve μ.H').bind fun rb => hp.readAddr rb).bind _ = _
        cases hrb : bd.resolve μ.H' with
        | none => rfl
        | some rb =>
          simp only [Option.bind_some]
          rw [Heap.readAddr_writeAddr_apart hw (Tm.apart?_resolve σ h ha hb hra hrb)]⟩
  | @EvalLaw.readOnWriteIdentity _ _ m R a i => ⟨_, rfl, fun σ hX => by
      obtain ⟨μ', hX⟩ := Option.ne_none_iff_exists'.1 hX
      obtain ⟨μ, ad, w, ra, mv, hp, -, ha, hv, hra, hmv, hw, rfl⟩ := Tm.write_some hX
      rw [Tm.iread_evalT, hX, Option.bind_some, ha, Option.bind_some]
      show ((ad.resolve μ.H').bind fun rb => hp.readAddr rb).bind _ = _
      rw [hra, Option.bind_some, Heap.readAddr_writeAddr_same hw, Option.bind_some]
      have hv : i.eval σ = some w := hv
      rw [hv]
      simp only [MvT.toMVal, HRef.ofId?] at hmv
      split at hmv
      · cases hmv; rfl
      · cases hmv⟩
  | .findOnCopy _ => ⟨_, rfl, fun _ hS => Tm.findOnCopy_exact hS⟩
  | .findOnCopyIn hb _ => ⟨.st (Tms.STerm.save _ _ (Tms.SValT.copyMem _ _)),
      by simp only [Tm.lawAnchor?, Option.orElse, hb]; rfl,
      fun σ hS => (Tm.base?_eval σ hb).trans (Tm.findOnCopy_exact hS)⟩
  | .readFromCopyToStorage _ => ⟨_, rfl, fun _ hX => Tm.readFromCopyToStorage_exact hX⟩
  | .readOnAddM h => ⟨_, rfl, fun _ hX => Tm.readOnAddM_exact h hX⟩
  | .readOnAddMFrame h => ⟨_, rfl, fun _ hX => Tm.readOnAddMFrame_exact h hX⟩
  | .readOnAddMFrameIdentity h => ⟨_, rfl, fun _ hX => Tm.readOnAddMFrameIdentity_exact h hX⟩

/-- **A memory law keeps every value its left side returns.** -/
theorem EvalLaw.evalRefines {u : Srt} {t t' : Tm C Γ u} (r : EvalLaw t t') :
    Tm.EvalRefinesAt t t' := fun σ x hx => by
  obtain ⟨X, hX, he⟩ := r.exact
  rw [← he σ (Tm.lawAnchor?_eval hX (by rw [hx]; exact Option.some_ne_none _))]
  exact hx

/-- The memory terms an element writes the memory with. -/
def UpdElem.memTerms {Δ : Ctx} : UpdElem C Γ Δ → List (Tm C Γ .mem)
  | .memory m => [m]
  | _ => []

/-- The right-hand sides of an update's `memory :=` elements. -/
def Upd.memTerms : {Δ : Ctx} → Upd C Γ Δ → List (Tm C Γ .mem)
  | _, .nil => []
  | _, .snoc U e => U.memTerms ++ e.memTerms
  | _, .decl U _ _ => U.memTerms
  | _, .pop U _ => U.memTerms
  | _, .drop U _ => U.memTerms

/-- **A memory write that is an element of an update that reverts nowhere
returns or is out of gas.** -/
theorem Upd.memory_okx {σ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) → U.exhOk σ = true →
    ∀ s ∈ U.memTerms, (s.eval σ).isSome = true ∨ s.exhB σ = true
  | _, .nil, _ => fun _ h => nomatch h
  | _, .snoc U e, h => by
    simp only [Upd.exhOk, Bool.and_eq_true, Bool.or_eq_true] at h
    intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · exact Upd.memory_okx U h.1 s hs
    · cases e with
      | memory s' =>
        simp only [UpdElem.memTerms, List.mem_singleton] at hs
        subst hs
        exact h.2
      | _ => nomatch hs
  | _, .decl U _ _, h => by
    simp only [Upd.exhOk, Bool.and_eq_true] at h
    exact Upd.memory_okx U h.1
  | _, .pop U _, h | _, .drop U _, h => Upd.memory_okx U h

/-- `U` writes the memory with a term on whose spine the memory `w` lies, a
term with no push. -/
def Upd.holdsMem {Δ : Ctx} (U : Upd C Γ Δ) (w : Tm C Γ .mem) : Bool :=
  w.pushFree && U.memTerms.any (·.onSpine w)

theorem Upd.holdsMem_eval {Δ : Ctx} {U : Upd C Γ Δ} {w : Tm C Γ .mem} (h : U.holdsMem w = true)
    (hU : U.exhOk σ = true) : w.eval σ ≠ none := by
  obtain ⟨hp, h⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨S, hS, hs⟩ := List.any_eq_true.1 h
  have hw := Tm.onSpine_okx hs (Upd.memory_okx U hU S hS)
  rw [Tm.exhB_of_pushFree σ w hp] at hw
  intro hn
  rw [hn] at hw
  simp only [Option.isSome_none, Bool.false_eq_true, or_self] at hw

/-- A covered memory law's write is held by the update. -/
def Upd.coversEval {Δ : Ctx} {u : Srt} (U : Upd C Γ Δ) (q : Tm C Γ u × Tm C Γ u) : Bool :=
  match q.1.lawAnchor? with
  | some (.mem X) => U.holdsMem X
  | some (.st S) => U.holdsWrite S
  | none => false

/-- **Wherever a covered update returns, a memory law refines back.** -/
theorem EvalLaw.back {u : Srt} {t t' : Tm C Γ u} (r : EvalLaw t t') {Δ : Ctx} {U : Upd C Γ Δ}
    (hc : U.coversEval (t, t') = true) (hU : U.exhOk σ = true) :
    OLe (t'.eval σ) (t.eval σ) := by
  obtain ⟨A, hA, he⟩ := r.exact
  cases A with
  | mem X =>
    simp only [Upd.coversEval, hA] at hc
    rw [he σ (Upd.holdsMem_eval hc hU)]
    exact OLe.refl _
  | st S =>
    simp only [Upd.coversEval, hA] at hc
    rw [he σ (Upd.holdsWrite_eval hc hU)]
    exact OLe.refl _

end EvalLawSound

/-! ## The laws, bundled -/

/-- A law at an update's right-hand sides, scoped: the right side returns what the
left side does (`fwd`), and wherever an update the check `chk` accepts returns, the
left side returns what the right side does (`back`). -/
structure LawCov (C : Contract) (Γ : Ctx) (u : Srt) (t t' : Tm C Γ u) where
  chk : {Δ : Ctx} → Upd C Γ Δ → Bool
  fwd : Tm.EvalRefinesAt t t'
  back : ∀ {Δ : Ctx} (U : Upd C Γ Δ) (σ : State C Γ), chk U = true →
    U.exhOk σ = true → OLe (t'.eval σ) (t.eval σ)

/-- A literal law, under any update. -/
def LawCov.lit {P : PrimTy} {t t' : Tm C Γ (.val P)} (r : LitLaw t t') : LawCov C Γ (.val P) t t' where
  chk _ := true
  fwd σ := (r.evalEq σ ▸ OLe.refl _)
  back _ σ _ _ := (r.evalEq σ ▸ OLe.refl _)

/-- **`findOnSave` at an update**: the read of a word written, where the
update holds the write. -/
def LawCov.findOnSave {P : PrimTy} (s : Tm C Γ .st) (p : Tm C Γ (.path (.prim P)))
    (w : P.Denote) : LawCov C Γ (.val P) (Tm.findSaveLit s p w) (Tms.Term.lit w) where
  chk U := U.holdsWrite (Tm.saveLit s p w)
  fwd := Tm.findSaveLit_fwd s p w
  back U σ hc hU := by
    obtain ⟨st', hst'⟩ := Option.ne_none_iff_exists'.1 (Upd.holdsWrite_eval hc hU)
    intro x hx
    rw [Tm.findSaveLit_eval_of_save s p w hst']
    exact hx

/-- **`findMemberCons`, under any update**: the two member-wise forms of one
read. -/
def LawCov.findMemberCons {s : Tm C Γ .st} {P : PrimTy} {p : Tm C Γ (.path (.prim P))}
    {r sn : Name} {hr : C.rootType r = some (.ref (.struct sn))}
    {p' : Tm C Γ (.spath sn (.prim P))} (h : p.shift? = some ⟨r, sn, hr, p'⟩) :
    LawCov C Γ (.val P) (Tms.Term.find s p) (.app2 .findIn (Tms.STerm.select s r hr) p') where
  chk _ := true
  fwd σ := Tm.findMemberCons_eval h σ ▸ OLe.refl _
  back _ σ _ _ := Tm.findMemberCons_eval h σ ▸ OLe.refl _

/-- **A term taclet onto a literal, where the update holds the write it
reads back** (`Upd.coversLit`): the read returns wherever the update does,
and the literal is what it returns (`TermTaclet.sound`). -/
def LawCov.covered {P : PrimTy} {t t' : Tm C Γ (.val P)} (r : TermTaclet t t')
    (ht : t'.isLit = true) : LawCov C Γ (.val P) t t' where
  chk U := U.coversLit t
  fwd := Tm.evalRefinesAt_of_theq r.sound ht
  back U σ hc hU := fun x hx => by
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 (Upd.coversLit_eval hc hU)
    rw [Tm.evalRefinesAt_of_theq r.sound ht σ y hy] at hx
    cases hx
    exact hy

/-- **A frame or delete-value law, where the update holds the storage
operation it reads past** (`Upd.coversRef`). -/
def LawCov.ref {P : PrimTy} {t t' : Tm C Γ (.val P)} {r : TermTaclet t t'}
    (hr : TermTaclet.RefLaw r) : LawCov C Γ (.val P) t t' where
  chk U := U.coversRef (t, t')
  fwd := hr.evalRefines
  back _ _ hc hU := hr.back hc hU

/-- **Two member-wise forms of one read, under any update** (`Tm.sameBase`). -/
def LawCov.eqv {u : Srt} {t t' : Tm C Γ u} (h : Tm.sameBase t t' = true) : LawCov C Γ u t t' where
  chk _ := true
  fwd σ := Tm.sameBase_eval h σ ▸ OLe.refl _
  back _ σ _ _ := Tm.sameBase_eval h σ ▸ OLe.refl _

/-- **A memory law, where the update holds the write it reads past**
(`Upd.coversEval`). -/
def LawCov.eval {u : Srt} {t t' : Tm C Γ u} (r : EvalLaw t t') : LawCov C Γ u t t' where
  chk U := U.coversEval (t, t')
  fwd := r.evalRefines
  back _ _ hc hU := r.back hc hU

/-! ## A premise about closed terms, at any scope -/

/-- `KindFreeAt` of closed terms holds at any scope they are read in: a
chain's hypothesis about terms at the empty scope (`st!{ … }`, `pt!{ … }`)
gives a law's premise at an update's scope. -/
theorem Tm.KindFreeAt.ofNil {u : Srt} {T : Ty} {s : Tm C Γ u} {p : Tm C Γ (u.pathAt T)}
    {s₀ : Tm C [] u} {p₀ : Tm C [] (u.pathAt T)} (h : Tm.KindFreeAt s₀ p₀) (hs : s.toNil? = some s₀)
    (hp : p.toNil? = some p₀) : Tm.KindFreeAt s p := by
  cases u with
  | st =>
    intro σ P r
    rw [Tm.denote_toNilS σ s hs, Tm.denote_toNilS σ p hp]
    exact h σ.toNil r
  | sts sn =>
    intro σ P r
    rw [Tm.denote_toNilS σ s hs, Tm.denote_toNilS σ p hp]
    exact h σ.toNil r
  | _ => trivial

/-! ## Pins -/

section Pins

/-- `250 + 10 ⇝ 260`, its range check decided. -/
example : LitLaw (C := StandardExample) (Γ := [])
    (Tms.Term.binop .add .uint (Tms.Term.lit ⟨250, rfl⟩) (Tms.Term.lit ⟨10, rfl⟩))
    (Tms.Term.lit ⟨260, rfl⟩) :=
  .add_literals

/-- The update holding `storage := save(storage, alice.age, 42)` covers the
read of `alice.age` from it. -/
example : (LawCov.findOnSave (Γ := []) (.app0 .storage) Tm.aliceAge ⟨42, rfl⟩).chk
    (Upd.nil.snoc (.storage (Tm.saveLit (.app0 .storage) Tm.aliceAge ⟨42, rfl⟩))) = true := by
  decide +kernel

end Pins

end Solidity
