import Solidity.Calculus.Closer
import Solidity.Calculus.DecideEval
import Solidity.Calculus.TermLaws

/-!
# Reading memory as solkey reads it

The memory clauses of `sol_decide`, each the transcription of the solkey
taclets named on it (`memoryRules.key`, `structMemoryRules.key`;
`docs/lean-key-rule-map.md` has the rows), proved on the typed heap
(`Theory/Typed/Mem.lean`).

A memory term of the reduction is the tree of its writes and allocations,
as the program built it: `write(m, a, v)`, `addM(m, R)` with its root
`alloc(m, R)`, `copySt(m, S)` with its root `copy(m, S)`.  A read
(`read(M, b)`, `iread(M, b)`, `size(M, i)`) walks the tree from the newest
node down (`LTm.memRes`), comparing addresses without running anything:

* **readOnWrite**: the address written reads what was written;
  **readWriteDifferent**: an address apart from it reads below
  (`LTm.apart?`: two members, a member and an element, two literal
  indices of one identity).
* **readAddDifferent**: an address whose object is older than an
  allocation (`LTm.boundedIn`: allocated on the spine below it, or read out
  of a memory there) reads below it; **readAddEqual** with **initMember**
  and **defaultValueInt**/**defaultValueBool**: an address at a member path
  of the fresh root reads its default.
* **readFromCopyToStorage**: a member of a copy of storage reads the
  storage there, its read eliminated as the storage reads are
  (`LTm.elim`).

Each rewrite is an equation of reads (`LTm.memRes_eval`): it keeps what
the term reads in every state, a halting term halting.
-/

namespace Solidity

namespace Decide

open Semantics (lookupBy structDef)

variable {C : Contract}

/-! ## The spine of a memory term -/

section Spine

variable {g : State C []} {ν : AEnv}

theorem LTm.eval_app1_none {a s : Srt} (o : Op1 C a s) (x : LTm C a)
    (hx : x.eval g ν = none) : (LTm.app1 o x).eval g ν = none := by
  rw [LTm.eval_app1, hx]; exact Op1.eval_none g o

theorem LTm.eval_app2_none {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b)
    (hx : x.eval g ν = none) : (LTm.app2 o x y).eval g ν = none := by
  rw [LTm.eval_app2, hx]; exact Op2.eval_none_left g o _

theorem LTm.eval_app3_none {a b c s : Srt} (o : Op3 C a b c s) (x : LTm C a) (y : LTm C b)
    (z : LTm C c) (hx : x.eval g ν = none) : (LTm.app3 o x y z).eval g ν = none := by
  rw [LTm.eval_app3, hx]; exact Op3.eval_none_x g o _ _

/-- `LTm.onSpineAny`'s compiled twin. -/
def LTm.onSpineAnyM {k : Srt} (w : LTm C k) : {u : Srt} → LTm C u → Bool
  | _, .app1 _ x => x.beqR w || LTm.onSpineAnyM w x
  | _, .app2 _ x _ => x.beqR w || LTm.onSpineAnyM w x
  | _, .app3 _ x _ _ => x.beqR w || LTm.onSpineAnyM w x
  | _, _ => false

/-- **`w` is on the spine below `t`**: a symbol's first argument, or one
below it.  Generic in both sorts; by the recursor. -/
@[implemented_by LTm.onSpineAnyM]
def LTm.onSpineAny {k : Srt} (w : LTm C k) {u : Srt} (t : LTm C u) : Bool :=
  @LTm.rec C (fun _ _ => Bool)
    (@fun _ _ => false) (@fun _ _ => false)
    (@fun _ _ _ x ihx => x.beqR w || ihx)
    (@fun _ _ _ _ x _ ihx _ => x.beqR w || ihx)
    (@fun _ _ _ _ _ x _ _ ihx _ _ => x.beqR w || ihx)
    (@fun _ _ _ _ _ _ _ _ => false)
    (@fun _ _ _ => false) (@fun _ _ _ => false) (@fun _ _ _ => false)
    (@fun _ _ _ _ _ _ => false)
    (@fun _ _ _ _ _ => false)
    (@fun _ _ _ _ _ _ _ _ _ _ => false)
    (@fun _ => false) u t

theorem LTm.onSpineAny_eq_onSpineAnyM {k : Srt} (w : LTm C k) {u : Srt} (t : LTm C u) :
    w.onSpineAny t = w.onSpineAnyM t := by
  induction t with
  | app1 o x ih => simp only [LTm.onSpineAnyM, ← ih]; rfl
  | app2 o x y ihx => simp only [LTm.onSpineAnyM, ← ihx]; rfl
  | app3 o x y z ihx => simp only [LTm.onSpineAnyM, ← ihx]; rfl
  | _ => rfl

/-- `w` is `t` or on its spine. -/
def LTm.onSpine {k : Srt} (t w : LTm C k) : Bool := t.beqR w || w.onSpineAny t

/-- At the memory sort: a memory whose heap typing extends `μ`'s. -/
def Srt.GrowsL {H : HTy} (μ : Grown H (fun _ => Unit)) : (u : Srt) → Option (u.Den C H) → Prop
  | .mem, x => ∀ μ', x = some μ' → μ.H' <+: μ'.H'
  | _, _ => True

theorem LTm.onSpineAny_grows {w : LTm C .mem} {μ : Grown g.H (fun _ => Unit)}
    (hw : w.eval g ν = some μ) {u : Srt} (t : LTm C u) (h : w.onSpineAny t = true) :
    Srt.GrowsL (C := C) μ u (t.eval g ν) := by
  induction t with
  | app1 o x ihx =>
    cases o with
    | addM R hR =>
      intro μ' hμ'
      simp only [LTm.onSpineAny, Bool.or_eq_true] at h
      rw [LTm.eval_app1, Op1.eval_eq_evalM] at hμ'
      simp only [Op1.evalM, Option.map_eq_some_iff] at hμ'
      obtain ⟨μ₀, hμ₀, rfl⟩ := hμ'
      have h₀ : μ.H' <+: μ₀.H' := by
        rcases h with h | h
        · cases LTm.sigma_eq_of_beqR h
          rw [hw] at hμ₀
          cases hμ₀
          exact List.prefix_refl _
        · exact ihx h μ₀ hμ₀
      exact h₀.trans (μ₀.heap.allocDefault R hR).ext
    | _ => trivial
  | app2 o x y ihx _ =>
    cases o with
    | copySt hT =>
      intro μ' hμ'
      simp only [LTm.onSpineAny, Bool.or_eq_true] at h
      rw [LTm.eval_app2, Op2.eval_eq_evalM] at hμ'
      simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hμ'
      obtain ⟨μ₀, hμ₀, v, -, rfl⟩ := hμ'
      have h₀ : μ.H' <+: μ₀.H' := by
        rcases h with h | h
        · cases LTm.sigma_eq_of_beqR h
          rw [hw] at hμ₀
          cases hμ₀
          exact List.prefix_refl _
        · exact ihx h μ₀ hμ₀
      exact h₀.trans (v.copyStToM μ₀.heap hT).ext
    | _ => trivial
  | app3 o x y z ihx _ _ =>
    cases o with
    | write =>
      intro μ' hμ'
      simp only [LTm.onSpineAny, Bool.or_eq_true] at h
      rw [LTm.eval_app3, Op3.eval_eq_evalM] at hμ'
      simp only [Op3.evalM, Grown.writeT, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hμ'
      obtain ⟨μ₀, hμ₀, ad, -, w', -, ra, -, mv, -, hp, -, rfl⟩ := hμ'
      rcases h with h | h
      · cases LTm.sigma_eq_of_beqR h
        rw [hw] at hμ₀
        cases hμ₀
        exact List.prefix_refl _
      · exact ihx h μ₀ hμ₀
    | _ => trivial
  | _ => cases u <;> trivial

theorem LTm.onSpine_grows {t w : LTm C .mem} (h : t.onSpine w = true)
    {μ μ' : Grown g.H (fun _ => Unit)} (ht : t.eval g ν = some μ') (hw : w.eval g ν = some μ) :
    μ.H' <+: μ'.H' := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain rfl := LTm.eq_of_beqR h
    rw [ht] at hw
    cases hw
    exact List.prefix_refl _
  · exact LTm.onSpineAny_grows hw t h μ' ht

end Spine

/-! ## Older objects -/

section Bounded

variable {g : State C []} {ν : AEnv}

/-- An identity, or the object of an address, below `n`; other sorts carry
nothing. -/
def Srt.BndL {H : HTy} (n : Nat) : (u : Srt) → Option (u.Den C H) → Prop
  | .ident _, x => ∀ id, x = some id → id < n
  | .addr _, x => ∀ ad, x = some ad → MAddrT.id ad < n
  | _, _ => True

/-- One step of `LTm.boundedIn` at a unary symbol. -/
def Op1.boundStep (M : LTm C .mem) {a s : Srt} : Op1 C a s → LTm C a → Bool → Bool
  | .alloc R h, m₀, _ => M.onSpine (.app1 (.addM R h) m₀)
  | .mfield _, _, ih => ih
  | _, _, _ => false

/-- One step of `LTm.boundedIn` at a binary symbol. -/
def Op2.boundStep (M : LTm C .mem) {a b s : Srt} : Op2 C a b s → LTm C a → LTm C b → Bool → Bool
  | .copy h, m₀, v, _ => M.onSpine (.app2 (.copySt h) m₀ v)
  | .iread, X, _, _ => M.onSpine X
  | .mat _, _, _, ih => ih
  | _, _, _, _ => false

/-- `LTm.boundedIn`'s compiled twin. -/
def LTm.boundedInM : {u : Srt} → LTm C u → LTm C .mem → Bool
  | _, .app1 o x, M => Op1.boundStep M o x (LTm.boundedInM x M)
  | _, .app2 o x y, M => Op2.boundStep M o x y (LTm.boundedInM x M)
  | _, _, _ => false

/-- **The identity a term reads is below the heap typing `M` leaves**: a
fresh root allocated on `M`'s spine, an identity read out of a memory on
it; an address is bounded where its object is.  Generic in the sort; by
the recursor. -/
@[implemented_by LTm.boundedInM]
def LTm.boundedIn {u : Srt} (t : LTm C u) (M : LTm C .mem) : Bool :=
  @LTm.rec C (fun _ _ => Bool)
    (@fun _ _ => false) (@fun _ _ => false)
    (@fun _ _ o x ihx => Op1.boundStep M o x ihx)
    (@fun _ _ _ o x y ihx _ => Op2.boundStep M o x y ihx)
    (@fun _ _ _ _ _ _ _ _ _ _ _ => false)
    (@fun _ _ _ _ _ _ _ _ => false)
    (@fun _ _ _ => false) (@fun _ _ _ => false) (@fun _ _ _ => false)
    (@fun _ _ _ _ _ _ => false)
    (@fun _ _ _ _ _ => false)
    (@fun _ _ _ _ _ _ _ _ _ _ => false)
    (@fun _ => false) u t

theorem LTm.boundedIn_eq_boundedInM (M : LTm C .mem) {u : Srt} (t : LTm C u) :
    t.boundedIn M = t.boundedInM M := by
  induction t with
  | app1 o x ih => simp only [LTm.boundedInM, ← ih]; rfl
  | app2 o x y ihx => simp only [LTm.boundedInM, ← ihx]; rfl
  | _ => rfl

theorem LTm.boundedIn_eval {M : LTm C .mem} {μ : Grown g.H (fun _ => Unit)}
    (hM : M.eval g ν = some μ) {u : Srt} (t : LTm C u) (h : t.boundedIn M = true) :
    Srt.BndL (C := C) μ.H'.length u (t.eval g ν) := by
  induction t with
  | app1 o x ihx =>
    cases o with
    | alloc R hR =>
      intro id hid
      simp only [LTm.boundedIn, Op1.boundStep] at h
      rw [LTm.eval_app1, Op1.eval_eq_evalM] at hid
      simp only [Op1.evalM, Option.map_eq_some_iff] at hid
      obtain ⟨μ₀, hμ₀, rfl⟩ := hid
      have hA : (LTm.app1 (.addM R hR) x).eval g ν =
          some (μ₀.then (μ₀.heap.allocDefault R hR)) := by
        rw [LTm.eval_app1, Op1.eval_eq_evalM]
        simp only [Op1.evalM, hμ₀, Option.map_some]
      exact Nat.lt_of_lt_of_le (HRef.id_lt _) (LTm.onSpine_grows h hM hA).length_le
    | mfield hf =>
      intro ad had
      simp only [LTm.boundedIn, Op1.boundStep] at h
      rw [LTm.eval_app1, Op1.eval_eq_evalM] at had
      simp only [Op1.evalM, Option.map_eq_some_iff] at had
      obtain ⟨id, hid, rfl⟩ := had
      exact ihx h id hid
    | _ => cases u <;> trivial
  | app2 o x y ihx _ =>
    cases o with
    | copy hR =>
      intro id hid
      simp only [LTm.boundedIn, Op2.boundStep] at h
      rw [LTm.eval_app2, Op2.eval_eq_evalM] at hid
      simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hid
      obtain ⟨μ₀, hμ₀, v, hv, rfl⟩ := hid
      have hA : (LTm.app2 (.copySt hR) x y).eval g ν =
          some (μ₀.then (v.copyStToM μ₀.heap hR)) := by
        rw [LTm.eval_app2, Op2.eval_eq_evalM]
        simp only [Op2.evalM, hμ₀, hv, Option.bind_eq_bind, Option.bind_some]
      exact Nat.lt_of_lt_of_le (HRef.id_lt _) (LTm.onSpine_grows h hM hA).length_le
    | iread =>
      intro id hid
      simp only [LTm.boundedIn, Op2.boundStep] at h
      rw [LTm.eval_app2, Op2.eval_eq_evalM] at hid
      simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hid
      obtain ⟨μ₀, hμ₀, ad, -, r, -, rfl⟩ := hid
      exact Nat.lt_of_lt_of_le (HRef.id_lt r) (LTm.onSpine_grows h hM hμ₀).length_le
    | mat a =>
      intro ad had
      simp only [LTm.boundedIn, Op2.boundStep] at h
      rw [LTm.eval_app2, Op2.eval_eq_evalM] at had
      simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at had
      obtain ⟨id, hid, k, -, rfl⟩ := had
      exact ihx h id hid
    | _ => cases u <;> trivial
  | _ => cases u <;> trivial

end Bounded

/-! ## The fresh root -/

section Fresh

variable {g : State C []} {ν : AEnv}

/-- An index literal. -/
def LTm.uintLit? (t : LTm C (.val .uint)) : Option Int := t.litV?.map (·.1)

theorem LTm.uintLit?_eval {t : LTm C (.val .uint)} {k : Int} (h : t.uintLit? = some k) :
    ∃ w, (t.eval g ν : Option PrimTy.uint.Denote) = some w ∧ w.1 = k := by
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨w, LTm.eval_litV? g ν hw, rfl⟩

/-- `M` is `addM(m, R)`. -/
def LTm.isAddM (M m : LTm C .mem) (R : RefTy) : Bool :=
  match M with
  | .app1 o m' => Op1.isAddMStep o m' m R
  | _ => false
where
  /-- At a unary symbol. -/
  Op1.isAddMStep {a : Srt} (o : Op1 C a .mem) (m' : LTm C a) (m : LTm C .mem) (R : RefTy) : Bool :=
    match o, m' with
    | .addM R' _, m' => m'.beqR m && R' == R

theorem LTm.eq_of_isAddM {M m : LTm C .mem} {R : RefTy} (h : M.isAddM m R = true) :
    ∃ hR, M = .app1 (.addM R hR) m := by
  unfold LTm.isAddM at h
  split at h
  · rename_i a o m'
    cases o with
    | addM R' hR' =>
      simp only [LTm.isAddM.Op1.isAddMStep, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hm, rfl⟩ := h
      obtain rfl := LTm.eq_of_beqR hm
      exact ⟨hR', rfl⟩
  · cases h

/-- One step of `LTm.freshPath?` at a unary symbol: `alloc(m, R)` is the
root, `i.f` the member `f` below `i`'s path. -/
def _root_.Solidity.Op1.freshStepL (m : LTm C .mem) (R : RefTy) {a s : Srt} :
    Op1 C a s → LTm C a → Option (List Semantics.Seg) → Option (List Semantics.Seg)
  | .alloc R' _, x, _ => if x.beqR m && R' == R then some [] else none
  | .mfield (f := f) _, _, r => r.map (· ++ [Semantics.Seg.field f])
  | _, _, _ => none

/-- One step of `LTm.freshPath?` at a binary symbol: `iread(addM(m, R), a)`
is what `a` reads, `i[k]` (a literal `k`) the element `k` below `i`'s
path. -/
def _root_.Solidity.Op2.freshStepL (m : LTm C .mem) (R : RefTy) {a b s : Srt} :
    Op2 C a b s → LTm C a → LTm C b → Option (List Semantics.Seg) →
      Option (List Semantics.Seg) → Option (List Semantics.Seg)
  | .iread, x, _, _, ry => if x.isAddM m R then ry else none
  | .mat _, _, y, rx, _ => y.uintLit?.bind fun k => rx.map (· ++ [Semantics.Seg.at k])
  | _, _, _, _, _ => none

/-- `LTm.freshPath?`'s compiled twin. -/
def LTm.freshPathM (m : LTm C .mem) (R : RefTy) : {u : Srt} → LTm C u → Option (List Semantics.Seg)
  | _, .app1 o x => o.freshStepL m R x (LTm.freshPathM m R x)
  | _, .app2 o x y => o.freshStepL m R x y (LTm.freshPathM m R x) (LTm.freshPathM m R y)
  | _, _ => none

/-- **The path at which a term reads below the root `addM(m, R)`
allocates**: KeY's `idC(idp, flds)`.  Generic in the sort; by the
recursor. -/
@[implemented_by LTm.freshPathM]
def LTm.freshPath? (m : LTm C .mem) (R : RefTy) {u : Srt} (t : LTm C u) :
    Option (List Semantics.Seg) :=
  @LTm.rec C (fun _ _ => Option (List Semantics.Seg))
    (@fun _ _ => none) (@fun _ _ => none)
    (@fun _ _ o x ihx => o.freshStepL m R x ihx)
    (@fun _ _ _ o x y ihx ihy => o.freshStepL m R x y ihx ihy)
    (@fun _ _ _ _ _ _ _ _ _ _ _ => none)
    (@fun _ _ _ _ _ _ _ _ => none)
    (@fun _ _ _ => none) (@fun _ _ _ => none) (@fun _ _ _ => none)
    (@fun _ _ _ _ _ _ => none)
    (@fun _ _ _ _ _ => none)
    (@fun _ _ _ _ _ _ _ _ _ _ => none)
    (@fun _ => none) u t

theorem LTm.freshPath?_eq_freshPathM (m : LTm C .mem) (R : RefTy) {u : Srt} (t : LTm C u) :
    LTm.freshPath? m R t = LTm.freshPathM m R t := by
  induction t with
  | app1 o x ih => simp only [LTm.freshPathM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.freshPathM, ← ihx, ← ihy]; rfl
  | _ => rfl

theorem LTm.read_evalT {P : PrimTy} (X : LTm C .mem) (b : LTm C (.addr (.prim P))) :
    ((LTm.app2 .read X b).eval g ν : Option P.Denote) =
      ((X.eval g ν : Option (Grown g.H (fun _ => Unit))).bind fun μ =>
        (b.eval g ν : Option (MAddrT (.prim P))).bind fun bd =>
          (bd.resolve μ.H').bind fun rb => μ.heap.readAddr rb) := rfl

theorem LTm.iread_evalT {R : RefTy} (X : LTm C .mem) (b : LTm C (.addr (.ref R))) :
    ((LTm.app2 .iread X b).eval g ν : Option Nat) =
      ((X.eval g ν : Option (Grown g.H (fun _ => Unit))).bind fun μ =>
        (b.eval g ν : Option (MAddrT (.ref R))).bind fun bd =>
          ((bd.resolve μ.H').bind fun rb => μ.heap.readAddr rb).bind fun r => some r.id) := rfl

theorem LTm.freshPath_eval {m : LTm C .mem} {R : RefTy} {hR : (Ty.ref R).mapFree = true}
    {μ₀ : Grown g.H (fun _ => Unit)} (hm : m.eval g ν = some μ₀) {u : Srt} (t : LTm C u) :
    ∀ {p : List Semantics.Seg}, LTm.freshPath? m R t = some p →
      Srt.FreshRead (C := C) (μ₀.heap.allocDefault R hR).H' (μ₀.allocSt R hR)
        (μ₀.heap.allocDefault R hR).val.id R p u (t.eval g ν) := by
  induction t with
  | app1 o x ihx =>
    intro p h
    cases o with
    | alloc R' hR' =>
      simp only [LTm.freshPath?, Op1.freshStepL] at h
      split at h
      · rename_i hmR
        simp only [Bool.and_eq_true, beq_iff_eq] at hmR
        obtain ⟨hmm, rfl⟩ := hmR
        obtain rfl := LTm.eq_of_beqR hmm
        cases h
        have he : (LTm.app1 (.alloc R' hR') x).eval g ν =
            some (μ₀.heap.allocDefault R' hR).val.id := by
          rw [LTm.eval_app1, Op1.eval_eq_evalM]
          simp only [Op1.evalM, hm, Option.map_some]
        rw [he]
        refine ⟨fun id hid => ?_, fun _ _ => ⟨_, rfl⟩⟩
        cases hid
        exact ⟨rfl, (μ₀.heap.allocDefault R' hR).val.get?⟩
      · cases h
    | mfield hf =>
      simp only [LTm.freshPath?, Op1.freshStepL, Option.map_eq_some_iff] at h
      obtain ⟨p', hp', rfl⟩ := h
      obtain ⟨ih1, ih2⟩ := ihx hp'
      refine ⟨fun ad had => ?_, fun T' hT' => ?_⟩
      · rw [LTm.eval_app1, Op1.eval_eq_evalM] at had
        simp only [Op1.evalM, Option.map_eq_some_iff] at had
        obtain ⟨id, hid, rfl⟩ := had
        obtain ⟨h1, h2⟩ := ih1 id hid
        refine ⟨⟨.field ⟨id, h2⟩ hf, ?_⟩, ?_⟩
        · simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?, h2, dite_true,
            Option.map_some]
        · simp only [Semantics.State.readPath, Semantics.MVal.readPath_snoc] at h1 ⊢
          rw [h1, Semantics.Res.ok_bind']
          rfl
      · obtain ⟨R'', hR''⟩ := Ty.memberTy_snoc_some hT'
        obtain ⟨id, hid⟩ := ih2 _ hR''
        exact ⟨_, by rw [LTm.eval_app1, hid]; rfl⟩
    | _ => simp only [LTm.freshPath?, Op1.freshStepL, reduceCtorEq] at h
  | app2 o x y ihx ihy =>
    intro p h
    cases o with
    | iread =>
      simp only [LTm.freshPath?, Op2.freshStepL] at h
      split at h
      · rename_i hM
        obtain ⟨hR', rfl⟩ := LTm.eq_of_isAddM hM
        obtain ⟨ih1, ih2⟩ := ihy h
        have hX : (LTm.app1 (.addM R hR') m).eval g ν =
            some (μ₀.then (μ₀.heap.allocDefault R hR)) := by
          rw [LTm.eval_app1, Op1.eval_eq_evalM]
          simp only [Op1.evalM, hm, Option.map_some]
        rw [LTm.iread_evalT, hX, Option.bind_some]
        refine ⟨fun id hid => ?_, fun T' hT' => ?_⟩
        · simp only [Option.bind_eq_some_iff, Option.some.injEq] at hid
          obtain ⟨bd, hbd, r, ⟨ra, hra, hrd⟩, rfl⟩ := hid
          obtain ⟨-, hpath⟩ := ih1 bd hbd
          refine ⟨?_, r.get?⟩
          rw [← hpath, ← MAddrT.erase_resolve hra,
            Heap.readAddr_erase (hp := (μ₀.heap.allocDefault R hR).heap) rfl ra]
          have hrd' : (μ₀.heap.allocDefault R hR).heap.readAddr ra = some r := hrd
          rw [hrd']
          rfl
        · obtain ⟨bd, hbd⟩ := ih2 T' hT'
          obtain ⟨⟨ra, hra⟩, hpath⟩ := ih1 bd hbd
          obtain ⟨mv', hmv', -⟩ := (copyStToM_default_readPath p (Grown.allocSt_copy μ₀ R hR)
            (Semantics.State.HeapExt.refl _)).2 T' hT'
          have hrd : readAddr (μ₀.allocSt R hR) ra.erase = .ok mv' := by
            rw [MAddrT.erase_resolve hra, hpath]
            exact hmv'
          rw [Heap.readAddr_erase (hp := (μ₀.heap.allocDefault R hR).heap) rfl ra] at hrd
          cases hx : (μ₀.heap.allocDefault R hR).heap.readAddr ra with
          | none => rw [hx] at hrd; cases hrd
          | some r =>
            refine ⟨r.id, ?_⟩
            rw [hbd, Option.bind_some]
            show ((bd.resolve (μ₀.heap.allocDefault R hR).H').bind fun rb =>
              (μ₀.heap.allocDefault R hR).heap.readAddr rb).bind _ = _
            rw [hra, Option.bind_some, hx, Option.bind_some]
      · cases h
    | mat a =>
      simp only [LTm.freshPath?, Op2.freshStepL, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at h
      obtain ⟨k, hk, p', hp', rfl⟩ := h
      obtain ⟨ih1, ih2⟩ := ihx hp'
      obtain ⟨w, hw, hwk⟩ := LTm.uintLit?_eval (g := g) (ν := ν) hk
      have he : ∀ id, (x.eval g ν : Option Nat) = some id →
          (LTm.app2 (.mat a) x y).eval g ν = some (MAddrT.index id a k) := by
        intro id hid
        rw [LTm.eval_app2, Op2.eval_eq_evalM]
        simp only [Op2.evalM, hid, hw, hwk, Option.bind_eq_bind, Option.bind_some]
      refine ⟨fun ad had => ?_, fun T' hT' => ?_⟩
      · cases hx : (x.eval g ν : Option Nat) with
        | none =>
          rw [LTm.eval_app2_none _ x y hx] at had
          cases had
        | some id =>
          rw [he id hx] at had
          cases had
          obtain ⟨h1, h2⟩ := ih1 id hx
          refine ⟨⟨.index ⟨id, h2⟩ a k, ?_⟩, ?_⟩
          · simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?, h2, dite_true,
              Option.map_some]
          · simp only [Semantics.State.readPath, Semantics.MVal.readPath_snoc] at h1 ⊢
            rw [h1, Semantics.Res.ok_bind']
            rfl
      · obtain ⟨R'', hR''⟩ := Ty.memberTy_snoc_some hT'
        obtain ⟨id, hid⟩ := ih2 _ hR''
        exact ⟨_, he id hid⟩
    | _ => simp only [LTm.freshPath?, Op2.freshStepL, reduceCtorEq] at h
  | _ => intro p h; simp only [LTm.freshPath?, reduceCtorEq] at h

end Fresh

/-! ## Memory terms and addresses, viewed -/

section Views

variable {g : State C []} {ν : AEnv}

/-- A memory term's head: a write, an allocation, a copy from storage. -/
inductive MemV (C : Contract) where
  | write (m : LTm C .mem) {T : Ty} (a : LTm C (.addr T)) (v : LTm C (.mv T))
  | addM (m : LTm C .mem) (R : RefTy) (h : (Ty.ref R).mapFree = true)
  | copySt (m : LTm C .mem) {T : Ty} (h : T.mapFree = true) (S : LTm C (.sv T))
  | other

/-- At a unary symbol. -/
def _root_.Solidity.Op1.memV {a : Srt} (o : Op1 C a .mem) (x : LTm C a) : MemV C :=
  match o, x with
  | .addM R h, x => .addM x R h

/-- At a binary symbol. -/
def _root_.Solidity.Op2.memV {a b : Srt} (o : Op2 C a b .mem) (x : LTm C a) (y : LTm C b) : MemV C :=
  match o, x, y with
  | .copySt h, x, y => .copySt x h y

/-- At a ternary symbol. -/
def _root_.Solidity.Op3.memV {a b c : Srt} (o : Op3 C a b c .mem) (x : LTm C a) (y : LTm C b)
    (z : LTm C c) : MemV C :=
  match o, x, y, z with
  | .write, x, y, z => .write x y z

/-- A memory term's head. -/
def LTm.memView (X : LTm C .mem) : MemV C :=
  match X with
  | .app1 o x => o.memV x
  | .app2 o x y => o.memV x y
  | .app3 o x y z => o.memV x y z
  | _ => .other

theorem LTm.memView_write {X m : LTm C .mem} {T : Ty} {a : LTm C (.addr T)} {v : LTm C (.mv T)}
    (h : X.memView = .write m a v) : X = .app3 .write m a v := by
  cases X with
  | app1 o x => cases o; simp only [LTm.memView, Op1.memV, reduceCtorEq] at h
  | app2 o x y => cases o; simp only [LTm.memView, Op2.memV, reduceCtorEq] at h
  | app3 o x y z =>
    cases o
    simp only [LTm.memView, Op3.memV] at h
    cases h; rfl
  | _ => simp only [LTm.memView, reduceCtorEq] at h

theorem LTm.memView_addM {X m : LTm C .mem} {R : RefTy} {hR : (Ty.ref R).mapFree = true}
    (h : X.memView = .addM m R hR) : X = .app1 (.addM R hR) m := by
  cases X with
  | app1 o x =>
    cases o
    simp only [LTm.memView, Op1.memV] at h
    cases h; rfl
  | app2 o x y => cases o; simp only [LTm.memView, Op2.memV, reduceCtorEq] at h
  | app3 o x y z => cases o; simp only [LTm.memView, Op3.memV, reduceCtorEq] at h
  | _ => simp only [LTm.memView, reduceCtorEq] at h

theorem LTm.memView_copySt {X m : LTm C .mem} {T : Ty} {hT : T.mapFree = true}
    {S : LTm C (.sv T)} (h : X.memView = .copySt m hT S) : X = .app2 (.copySt hT) m S := by
  cases X with
  | app1 o x => cases o; simp only [LTm.memView, Op1.memV, reduceCtorEq] at h
  | app2 o x y =>
    cases o
    simp only [LTm.memView, Op2.memV] at h
    cases h; rfl
  | app3 o x y z => cases o; simp only [LTm.memView, Op3.memV, reduceCtorEq] at h
  | _ => simp only [LTm.memView, reduceCtorEq] at h

/-- An address term's shape. -/
inductive AddrShapeL (C : Contract) where
  | field (f : Name)
  | index (i : (R : RefTy) × LTm C (.ident R)) (k : Option Int)

/-- At a unary symbol. -/
def _root_.Solidity.Op1.addrStepL {a u : Srt} : Op1 C a u → Option (AddrShapeL C)
  | .mfield (f := f) _ => some (.field f)
  | _ => none

/-- At a binary symbol. -/
def _root_.Solidity.Op2.addrStepL {a b u : Srt} : Op2 C a b u → LTm C a → LTm C b →
    Option (AddrShapeL C)
  | .mat _, x, y => some (.index ⟨_, x⟩ y.uintLit?)
  | _, _, _ => none

/-- An address term's shape.  Generic in the sort. -/
def LTm.addrShape? {u : Srt} : LTm C u → Option (AddrShapeL C)
  | .app1 o _ => o.addrStepL
  | .app2 o x y => o.addrStepL x y
  | _ => none

/-- **Two address terms that never meet** (`readWriteDifferent`'s side
condition, decided on the terms): two members, a member and an element, or
two elements of one identity at two literal indices. -/
def LTm.apart? {T U : Ty} (a : LTm C (.addr T)) (b : LTm C (.addr U)) : Bool :=
  match a.addrShape?, b.addrShape? with
  | some (.field f), some (.field g) => f != g
  | some (.field _), some (.index _ _) => true
  | some (.index _ _), some (.field _) => true
  | some (.index i (some k)), some (.index j (some k')) => i.2.beqR j.2 && k != k'
  | _, _ => false

/-- What an address term's shape says of the address it reads. -/
def AddrShapeL.Reads (g : State C []) (ν : AEnv) {T : Ty} : AddrShapeL C → MAddrT T → Prop
  | .field f, ad => ∃ (s : Name) (id : Nat) (h : lookupBy f (structDef s) = some T),
      ad = MAddrT.field id h
  | .index ⟨R, i⟩ k, ad => ∃ (id : Nat) (a : ArrTy R T) (j : Int),
      (i.eval g ν : Option Nat) = some id ∧ ad = MAddrT.index id a j ∧ ∀ k', k = some k' → j = k'

theorem LTm.addrShape?_eval {T : Ty} {a : LTm C (.addr T)} {sh : AddrShapeL C}
    (h : a.addrShape? = some sh) {ad : MAddrT T} (ha : (a.eval g ν : Option (MAddrT T)) = some ad) :
    sh.Reads g ν ad := by
  cases a with
  | app1 o x =>
    cases o <;> simp only [LTm.addrShape?, Op1.addrStepL, reduceCtorEq, Option.some.injEq] at h
    subst h
    rename_i s f hf
    have ha : ((x.eval g ν : Option Nat).map (fun id => MAddrT.field id hf)) = some ad := ha
    obtain ⟨id, -, rfl⟩ := Option.map_eq_some_iff.1 ha
    exact ⟨s, id, hf, rfl⟩
  | app2 o x y =>
    cases o <;> simp only [LTm.addrShape?, Op2.addrStepL, reduceCtorEq, Option.some.injEq] at h
    subst h
    rename_i R arr
    have ha : (((x.eval g ν : Option Nat)).bind fun id =>
        (y.eval g ν : Option PrimTy.uint.Denote).bind fun k => some (MAddrT.index id arr k.1)) =
      some ad := ha
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at ha
    obtain ⟨id, hi, w, hw, rfl⟩ := ha
    refine ⟨id, arr, w.1, hi, rfl, fun k' hk => ?_⟩
    obtain ⟨w', hw', hk'⟩ := LTm.uintLit?_eval (g := g) (ν := ν) hk
    rw [hw] at hw'
    cases hw'
    exact hk'
  | _ => simp only [LTm.addrShape?, reduceCtorEq] at h

/-- Two apart address terms resolve, in one heap typing, to apart
addresses. -/
theorem LTm.apart?_resolve {T U : Ty} {a : LTm C (.addr T)} {b : LTm C (.addr U)}
    (h : a.apart? b = true) {ad : MAddrT T} {bd : MAddrT U}
    (ha : (a.eval g ν : Option (MAddrT T)) = some ad)
    (hb : (b.eval g ν : Option (MAddrT U)) = some bd) : ad.Apart bd := by
  unfold LTm.apart? at h
  split at h
  · rename_i f f' hfa hfb
    obtain ⟨s, id, hf, rfl⟩ := LTm.addrShape?_eval hfa ha
    obtain ⟨s', id', hg, rfl⟩ := LTm.addrShape?_eval hfb hb
    exact .inr (by simpa only [bne_iff_ne, ne_eq] using h)
  · rename_i f i k hfa hfb
    obtain ⟨s, id, hf, rfl⟩ := LTm.addrShape?_eval hfa ha
    obtain ⟨id', arr, j, -, rfl, -⟩ := LTm.addrShape?_eval hfb hb
    trivial
  · rename_i i k f hfa hfb
    obtain ⟨id', arr, j, -, rfl, -⟩ := LTm.addrShape?_eval hfa ha
    obtain ⟨s, id, hf, rfl⟩ := LTm.addrShape?_eval hfb hb
    trivial
  · rename_i i k j k' hfa hfb
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hij, hk⟩ := h
    obtain ⟨R, i⟩ := i
    obtain ⟨R', j⟩ := j
    cases LTm.sigma_eq_of_beqR hij
    obtain ⟨id, arr, n, hi, rfl, hn⟩ := LTm.addrShape?_eval hfa ha
    obtain ⟨id', arr', n', hi', rfl, hn'⟩ := LTm.addrShape?_eval hfb hb
    rw [hi] at hi'
    cases hi'
    refine .inr ?_
    rw [hn k rfl, hn' k' rfl]
    exact hk
  · nomatch h

end Views

/-! ## The laws of a read -/

section Laws

variable {g : State C []} {ν : AEnv}

/-- A read of a word, as `readId` reads it. -/
theorem LTm.read_eval_readId {P : PrimTy} (X : LTm C .mem) (b : LTm C (.addr (.prim P))) :
    ((LTm.app2 .read X b).eval g ν : Option P.Denote) =
      ((X.eval g ν : Option (Grown g.H (fun _ => Unit))).bind fun μ =>
        (b.eval g ν : Option (MAddrT (.prim P))).bind fun bd => μ.readId bd) := by
  rw [LTm.read_evalT]
  cases (X.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ =>
    cases (b.eval g ν : Option (MAddrT (.prim P))) with
    | none => rfl
    | some bd =>
      simp only [Option.bind_some, Grown.readId, Grown.readT, Option.bind_eq_bind]
      cases (bd.resolve μ.H').bind μ.heap.readAddr <;> rfl

/-- A read of an identity, as `readId` reads it. -/
theorem LTm.iread_eval_readId {R : RefTy} (X : LTm C .mem) (b : LTm C (.addr (.ref R))) :
    ((LTm.app2 .iread X b).eval g ν : Option Nat) =
      ((X.eval g ν : Option (Grown g.H (fun _ => Unit))).bind fun μ =>
        (b.eval g ν : Option (MAddrT (.ref R))).bind fun bd => μ.readId bd) := by
  rw [LTm.iread_evalT]
  cases (X.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ =>
    cases (b.eval g ν : Option (MAddrT (.ref R))) with
    | none => rfl
    | some bd =>
      simp only [Option.bind_some, Grown.readId, Grown.readT, Option.bind_eq_bind]
      cases (bd.resolve μ.H').bind μ.heap.readAddr <;> rfl

/-- A write that returns: its memory, address and value, and the memory it
leaves. -/
theorem LTm.write_some {T : Ty} {m : LTm C .mem} {a : LTm C (.addr T)} {v : LTm C (.mv T)}
    {μ' : Grown g.H (fun _ => Unit)}
    (h : ((LTm.app3 .write m a v).eval g ν : Option (Grown g.H (fun _ => Unit))) = some μ') :
    ∃ μ ad w, (m.eval g ν : Option (Grown g.H (fun _ => Unit))) = some μ ∧
      (a.eval g ν : Option (MAddrT T)) = some ad ∧ (v.eval g ν : Option (MvT T)) = some w ∧
      μ.writeT ad w = some μ' := by
  rw [LTm.eval_app3, Op3.eval_eq_evalM] at h
  simp only [Op3.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨μ, hm, ad, ha, w, hv, hw⟩ := h
  exact ⟨μ, ad, w, hm, ha, hv, hw⟩

/-- **readOnWrite**: the address written reads the word written, where the
write returns. -/
theorem LTm.read_write_same {P : PrimTy} (m : LTm C .mem) (a : LTm C (.addr (.prim P)))
    (x : LTm C (.val P)) :
    ((LTm.app2 .read (.app3 .write m a (.app1 .mval x)) a).eval g ν : Option P.Denote) =
      (LTm.seq (.app3 .write m a (.app1 .mval x)) x).eval g ν := by
  rw [LTm.read_eval_readId, LTm.eval_seq]
  cases hW : ((LTm.app3 .write m a (.app1 .mval x)).eval g ν :
      Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ' =>
    obtain ⟨μ, ad, w, hm, ha, hv, hw⟩ := LTm.write_some hW
    rw [Option.bind_some, ha, Option.bind_some, (Grown.writeT_facts hw).1]
    have hx : (x.eval g ν : Option P.Denote) = some w := hv
    rw [Option.bind_some, hx]

/-- **readOnWrite** of an identity. -/
theorem LTm.iread_write_same {R : RefTy} (m : LTm C .mem) (a : LTm C (.addr (.ref R)))
    (t : LTm C (.ident R)) :
    ((LTm.app2 .iread (.app3 .write m a (.app1 .ref t)) a).eval g ν : Option Nat) =
      (LTm.seq (.app3 .write m a (.app1 .ref t)) t).eval g ν := by
  rw [LTm.iread_eval_readId, LTm.eval_seq]
  cases hW : ((LTm.app3 .write m a (.app1 .ref t)).eval g ν :
      Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ' =>
    obtain ⟨μ, ad, w, hm, ha, hv, hw⟩ := LTm.write_some hW
    rw [Option.bind_some, ha, Option.bind_some, (Grown.writeT_facts hw).1]
    have hx : (t.eval g ν : Option Nat) = some w := hv
    rw [Option.bind_some, hx]

/-- **readWriteDifferent**: an address apart from the one written reads
below the write, where it returns. -/
theorem LTm.read_write_apart {T U : Ty} (m : LTm C .mem) (a : LTm C (.addr T)) (v : LTm C (.mv T))
    (b : LTm C (.addr U)) (h : a.apart? b = true) :
    ((LTm.app3 .write m a v).eval g ν : Option (Grown g.H (fun _ => Unit))).bind
        (fun μ => (b.eval g ν : Option (MAddrT U)).bind fun bd => μ.readId bd) =
      ((LTm.app3 .write m a v).eval g ν : Option (Grown g.H (fun _ => Unit))).bind
        (fun _ => (m.eval g ν : Option (Grown g.H (fun _ => Unit))).bind fun μ =>
          (b.eval g ν : Option (MAddrT U)).bind fun bd => μ.readId bd) := by
  cases hW : ((LTm.app3 .write m a v).eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ' =>
    obtain ⟨μ, ad, w, hm, ha, hv, hw⟩ := LTm.write_some hW
    rw [Option.bind_some, Option.bind_some, hm, Option.bind_some]
    cases hb : (b.eval g ν : Option (MAddrT U)) with
    | none => rfl
    | some bd =>
      simp only [Option.bind_some]
      exact (Grown.writeT_facts hw).2 bd (LTm.apart?_resolve h ha hb)

theorem LTm.read_write_apart' {P : PrimTy} {T : Ty} (m : LTm C .mem) (a : LTm C (.addr T))
    (v : LTm C (.mv T)) (b : LTm C (.addr (.prim P))) (h : a.apart? b = true) :
    ((LTm.app2 .read (.app3 .write m a v) b).eval g ν : Option P.Denote) =
      (LTm.seq (.app3 .write m a v) (.app2 .read m b)).eval g ν := by
  rw [LTm.read_eval_readId, LTm.eval_seq, LTm.read_write_apart m a v b h]
  congr 1
  funext _
  rw [LTm.read_eval_readId]

theorem LTm.iread_write_apart' {R : RefTy} {T : Ty} (m : LTm C .mem) (a : LTm C (.addr T))
    (v : LTm C (.mv T)) (b : LTm C (.addr (.ref R))) (h : a.apart? b = true) :
    ((LTm.app2 .iread (.app3 .write m a v) b).eval g ν : Option Nat) =
      (LTm.seq (.app3 .write m a v) (.app2 .iread m b)).eval g ν := by
  rw [LTm.iread_eval_readId, LTm.eval_seq, LTm.read_write_apart m a v b h]
  congr 1
  funext _
  rw [LTm.iread_eval_readId]

/-- **readAddDifferent**: below an allocation, an address whose object is
older reads below it. -/
theorem LTm.read_addM_old {P : PrimTy} (m : LTm C .mem) (R : RefTy)
    (hR : (Ty.ref R).mapFree = true) (b : LTm C (.addr (.prim P))) (h : b.boundedIn m = true) :
    ((LTm.app2 .read (.app1 (.addM R hR) m) b).eval g ν : Option P.Denote) =
      (LTm.app2 .read m b).eval g ν := by
  rw [LTm.read_evalT, LTm.read_evalT, LTm.eval_app1, Op1.eval_eq_evalM]
  cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ₀ =>
    simp only [Op1.evalM, Option.map_some, Option.bind_some]
    cases hb : (b.eval g ν : Option (MAddrT (.prim P))) with
    | none => rfl
    | some bd =>
      simp only [Option.bind_some]
      exact MVal.erase_prim_inj (Grown.readAddM_old μ₀ R hR bd (LTm.boundedIn_eval hm b h bd hb))

theorem LTm.iread_addM_old {R' : RefTy} (m : LTm C .mem) (R : RefTy)
    (hR : (Ty.ref R).mapFree = true) (b : LTm C (.addr (.ref R'))) (h : b.boundedIn m = true) :
    ((LTm.app2 .iread (.app1 (.addM R hR) m) b).eval g ν : Option Nat) =
      (LTm.app2 .iread m b).eval g ν := by
  rw [LTm.iread_evalT, LTm.iread_evalT, LTm.eval_app1, Op1.eval_eq_evalM]
  cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ₀ =>
    simp only [Op1.evalM, Option.map_some, Option.bind_some]
    cases hb : (b.eval g ν : Option (MAddrT (.ref R'))) with
    | none => rfl
    | some bd =>
      simp only [Option.bind_some]
      exact MVal.erase_ref_inj (Grown.readAddM_old μ₀ R hR bd (LTm.boundedIn_eval hm b h bd hb))

/-- **readAddDifferent** below a copy into memory. -/
theorem LTm.read_copySt_old {P : PrimTy} {U : Ty} (m : LTm C .mem) (hU : U.mapFree = true)
    (S : LTm C (.sv U)) (b : LTm C (.addr (.prim P))) (h : b.boundedIn m = true) :
    ((LTm.app2 .read (.app2 (.copySt hU) m S) b).eval g ν : Option P.Denote) =
      (LTm.seq S (.app2 .read m b)).eval g ν := by
  rw [LTm.read_evalT, LTm.eval_seq, LTm.read_evalT, LTm.eval_app2, Op2.eval_eq_evalM]
  cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => cases (S.eval g ν : Option (SVal U)) <;> rfl
  | some μ₀ =>
    cases hS : (S.eval g ν : Option (SVal U)) with
    | none => rfl
    | some v =>
      simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_some]
      cases hb : (b.eval g ν : Option (MAddrT (.prim P))) with
      | none => rfl
      | some bd =>
        simp only [Option.bind_some]
        exact MVal.erase_prim_inj
          (Grown.readCopySt_old μ₀ v hU bd (LTm.boundedIn_eval hm b h bd hb))

theorem LTm.iread_copySt_old {R' : RefTy} {U : Ty} (m : LTm C .mem) (hU : U.mapFree = true)
    (S : LTm C (.sv U)) (b : LTm C (.addr (.ref R'))) (h : b.boundedIn m = true) :
    ((LTm.app2 .iread (.app2 (.copySt hU) m S) b).eval g ν : Option Nat) =
      (LTm.seq S (.app2 .iread m b)).eval g ν := by
  rw [LTm.iread_evalT, LTm.eval_seq, LTm.iread_evalT, LTm.eval_app2, Op2.eval_eq_evalM]
  cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => cases (S.eval g ν : Option (SVal U)) <;> rfl
  | some μ₀ =>
    cases hS : (S.eval g ν : Option (SVal U)) with
    | none => rfl
    | some v =>
      simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_some]
      cases hb : (b.eval g ν : Option (MAddrT (.ref R'))) with
      | none => rfl
      | some bd =>
        simp only [Option.bind_some]
        exact MVal.erase_ref_inj
          (Grown.readCopySt_old μ₀ v hU bd (LTm.boundedIn_eval hm b h bd hb))

/-- **readAddEqual**, **initMember**, **defaultValueInt**: below an
allocation, an address at a member path of the fresh root, of a primitive
type, reads its default, where the memory below returns. -/
theorem LTm.read_addM_fresh {P : PrimTy} (m : LTm C .mem) (R : RefTy)
    (hR : (Ty.ref R).mapFree = true) (b : LTm C (.addr (.prim P)))
    (h : (LTm.freshPath? m R b).bind (Ty.ref R).memberTy = some (.prim P)) :
    ((LTm.app2 .read (.app1 (.addM R hR) m) b).eval g ν : Option P.Denote) =
      (LTm.seq m (.lit (PrimTy.dflt P))).eval g ν := by
  rw [LTm.eval_seq]
  cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none =>
    rw [LTm.read_evalT, LTm.eval_app1, hm, Op1.eval_none]; rfl
  | some μ₀ =>
    obtain ⟨p, hp, hT⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ih1, ih2⟩ := LTm.freshPath_eval (hR := hR) hm b hp
    obtain ⟨bd, hbd⟩ := ih2 _ hT
    obtain ⟨⟨ra, hra⟩, hpath⟩ := ih1 bd hbd
    obtain ⟨mv', hmv', hd⟩ := (copyStToM_default_readPath p (Grown.allocSt_copy μ₀ R hR)
      (Semantics.State.HeapExt.refl _)).2 _ hT
    have hrd : readAddr (μ₀.allocSt R hR) ra.erase = .ok mv' := by
      rw [MAddrT.erase_resolve hra, hpath]
      exact hmv'
    rw [Heap.readAddr_erase (hp := (μ₀.heap.allocDefault R hR).heap) rfl ra] at hrd
    have hX : ((LTm.app1 (.addM R hR) m).eval g ν : Option (Grown g.H (fun _ => Unit))) =
        some (μ₀.then (μ₀.heap.allocDefault R hR)) := by
      rw [LTm.eval_app1, Op1.eval_eq_evalM]
      simp only [Op1.evalM, hm, Option.map_some]
    rw [LTm.read_evalT, hX, Option.bind_some, hbd, Option.bind_some]
    show ((bd.resolve (μ₀.heap.allocDefault R hR).H').bind fun rb =>
      (μ₀.heap.allocDefault R hR).heap.readAddr rb) = some (PrimTy.dflt P)
    rw [hra, Option.bind_some]
    cases hx : (μ₀.heap.allocDefault R hR).heap.readAddr ra with
    | none => rw [hx] at hrd; cases hrd
    | some v =>
      rw [hx] at hrd
      simp only [toRes, Except.ok.injEq] at hrd
      subst hrd
      have hd : Semantics.MVal.prim (PrimTy.erase (p := P) v) = (PrimTy.default P).toMVal := hd
      rw [← PrimTy.erase_dflt] at hd
      have hv : PrimTy.erase (p := P) v = PrimTy.erase (PrimTy.dflt P) := by
        cases P <;> exact Semantics.MVal.prim.inj hd
      rw [PrimTy.erase_injective hv]

end Laws

/-! ## Memory terms that return -/

section Ok

variable {g : State C []} {ν : AEnv}

theorem LTm.onSpineAny_eval {k : Srt} {w : LTm C k} {u : Srt} (t : LTm C u)
    (h : w.onSpineAny t = true) (ht : t.eval g ν ≠ none) : w.eval g ν ≠ none := by
  induction t with
  | app1 o x ihx =>
    have hx : x.eval g ν ≠ none := fun hx => ht (LTm.eval_app1_none o x hx)
    simp only [LTm.onSpineAny, Bool.or_eq_true] at h
    rcases h with h | h
    · cases LTm.sigma_eq_of_beqR h; exact hx
    · exact ihx h hx
  | app2 o x y ihx _ =>
    have hx : x.eval g ν ≠ none := fun hx => ht (LTm.eval_app2_none o x y hx)
    simp only [LTm.onSpineAny, Bool.or_eq_true] at h
    rcases h with h | h
    · cases LTm.sigma_eq_of_beqR h; exact hx
    · exact ihx h hx
  | app3 o x y z ihx _ _ =>
    have hx : x.eval g ν ≠ none := fun hx => ht (LTm.eval_app3_none o x y z hx)
    simp only [LTm.onSpineAny, Bool.or_eq_true] at h
    rcases h with h | h
    · cases LTm.sigma_eq_of_beqR h; exact hx
    · exact ihx h hx
  | _ => simp only [LTm.onSpineAny, Bool.false_eq_true] at h

/-- Where `M` returns, `W` on its spine returns, its heap typing below `M`'s. -/
theorem LTm.onSpine_eval {M W : LTm C .mem} (h : M.onSpine W = true)
    {μ : Grown g.H (fun _ => Unit)} (hM : M.eval g ν = some μ) :
    ∃ ω, W.eval g ν = some ω ∧ ω.H' <+: μ.H' := by
  have hW : W.eval g ν ≠ none := by
    rcases Bool.or_eq_true_iff.mp h with h | h
    · obtain rfl := LTm.eq_of_beqR h; rw [hM]; exact nofun
    · exact LTm.onSpineAny_eval M h (by rw [hM]; exact nofun)
  obtain ⟨ω, hω⟩ := Option.ne_none_iff_exists'.1 hW
  exact ⟨ω, hω, LTm.onSpine_grows h hM hω⟩

/-- A question of returning, about a memory: it returns; an identity in it
returns, an object of its type there; an address in it resolves there. -/
inductive MemQ (C : Contract) where
  | mem (M : LTm C .mem)
  | ident {R : RefTy} (t : LTm C (.ident R)) (M : LTm C .mem)
  | addr {T : Ty} (a : LTm C (.addr T)) (M : LTm C .mem)

/-- What a question says. -/
def MemQ.Holds (g : State C []) (ν : AEnv) : MemQ C → Prop
  | .mem M => (M.eval g ν : Option (Grown g.H (fun _ => Unit))).isSome = true
  | @MemQ.ident _ R t M => ∀ μ, (M.eval g ν : Option (Grown g.H (fun _ => Unit))) = some μ →
      ∃ id, (t.eval g ν : Option Nat) = some id ∧ μ.H'[id]? = some R
  | @MemQ.addr _ T a M => ∀ μ, (M.eval g ν : Option (Grown g.H (fun _ => Unit))) = some μ →
      ∃ ad ra, (a.eval g ν : Option (MAddrT T)) = some ad ∧ ad.resolve μ.H' = some ra ∧
        (μ.heap.readAddr ra).isSome = true ∧ ∀ v, (μ.heap.writeAddr ra v).isSome = true

/-- An identity term's head: an allocation, a copy, a read out of memory. -/
inductive IdentV (C : Contract) where
  | alloc (m : LTm C .mem) (R : RefTy) (h : (Ty.ref R).mapFree = true)
  | copy (m : LTm C .mem) {U : Ty} (h : U.mapFree = true) (S : LTm C (.sv U))
  | iread (X : LTm C .mem) {T : Ty} (b : LTm C (.addr T))
  | other

def _root_.Solidity.Op1.identV {a s : Srt} (o : Op1 C a s) (x : LTm C a) : IdentV C :=
  match o, x with
  | .alloc R h, x => .alloc x R h
  | _, _ => .other

def _root_.Solidity.Op2.identV {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    IdentV C :=
  match o, x, y with
  | .copy h, x, y => .copy x h y
  | .iread, x, y => .iread x y
  | _, _, _ => .other

/-- An identity term's head. -/
def LTm.identView {s : Srt} (t : LTm C s) : IdentV C :=
  match t with
  | .app1 o x => o.identV x
  | .app2 o x y => o.identV x y
  | _ => .other

/-- An address term's object, where it is a member. -/
def _root_.Solidity.Op1.fieldObj {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    Option ((R : RefTy) × LTm C (.ident R)) :=
  match o, x with
  | .mfield _, x => some ⟨_, x⟩
  | _, _ => none

/-- A member address's object. -/
def LTm.fieldObj? {s : Srt} (a : LTm C s) : Option ((R : RefTy) × LTm C (.ident R)) :=
  match a with
  | .app1 o x => o.fieldObj x
  | _ => none

/-- A memory value term's identity, where it writes one. -/
def _root_.Solidity.Op1.refArg {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    Option ((R : RefTy) × LTm C (.ident R)) :=
  match o, x with
  | .ref, x => some ⟨_, x⟩
  | _, _ => none

/-- A copy's source that returns: a fresh array of a length that does. -/
def _root_.Solidity.Op1.svOk {a s : Srt} (o : Op1 C a s) (x : LTm C a) : Bool :=
  match o, x with
  | .newArr _, x => x.retsS
  | _, _ => false

/-- One step of the returning check. -/
def memOkStep (ih : MemQ C → Bool) : MemQ C → Bool
  | .mem M =>
    match M.memView with
    | .write m a v =>
      ih (.mem m) && ih (.addr a m) &&
        (match v with
          | .app1 o x =>
            match o.refArg x with
            | some ⟨_, t⟩ => ih (.ident t m)
            | none => ({} : Facts C).returns (({} : Facts C).nf x)
          | _ => false)
    | .addM m _ _ => ih (.mem m)
    | .copySt m _ S =>
      ih (.mem m) &&
        (match S with
          | .app1 o x => o.svOk x
          | _ => false)
    | .other => M.retsS
  | .ident t M =>
    match t.identView with
    | .alloc m R h => M.onSpine (.app1 (.addM R h) m)
    | .copy m h S => M.onSpine (.app2 (.copySt h) m S)
    | .iread X b => M.onSpine X && ih (.addr b X)
    | .other => false
  | .addr a M =>
    match a.fieldObj? with
    | some ⟨_, t⟩ => ih (.ident t M)
    | none => false

/-- **A memory term that returns, decided on the terms** `n` deep: its
writes land (a member of an object of the memory, its value a word that
returns or an identity there), its copies copy a fresh array.  By the
recursor on the depth. -/
def memOkN (n : Nat) : MemQ C → Bool :=
  Nat.rec (motive := fun _ => MemQ C → Bool) (fun _ => false) (fun _ ih => memOkStep ih) n

theorem retsS_isSome {s : Srt} {t : LTm C s} (h : t.retsS = true) :
    (t.eval g ν).isSome = true := by
  obtain ⟨v, hv⟩ := LTm.retsS_eval (g := g) (ν := ν) h
  rw [hv]; rfl

/-- **What the check accepts returns.** -/
theorem memOkN_sound (n : Nat) : ∀ q : MemQ C, memOkN n q = true → q.Holds g ν := by
  induction n with
  | zero => intro q h; cases h
  | succ n ih =>
    intro q h
    cases q with
    | mem M =>
      show (M.eval g ν : Option (Grown g.H (fun _ => Unit))).isSome = true
      simp only [memOkN, memOkStep] at h
      split at h
      · rename_i m T a v hX
        obtain rfl := LTm.memView_write hX
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hm, ha⟩, hv⟩ := h
        obtain ⟨μ, hμ⟩ := Option.isSome_iff_exists.1 (ih _ hm)
        obtain ⟨ad, ra, had, hra, -, hw⟩ := ih _ ha μ hμ
        have hval : ∃ w mv, (v.eval g ν : Option (MvT T)) = some w ∧
            MvT.toMVal μ.H' T w = some mv := by
          cases v with
          | app1 o x =>
            simp only at hv
            split at hv
            · rename_i R' t hr
              cases o <;> simp only [Op1.refArg, reduceCtorEq, Option.some.injEq] at hr
              obtain ⟨rfl, h⟩ := Sigma.mk.inj hr
              cases h
              obtain ⟨id, hid, hty⟩ := ih _ hv μ hμ
              refine ⟨id, ⟨id, hty⟩, ?_, ?_⟩
              · rw [LTm.eval_app1, hid]; rfl
              · simp only [MvT.toMVal, HRef.ofId?, hty, dite_true]
            · rename_i hr
              cases o <;> simp only [Op1.refArg, reduceCtorEq] at hr
              have hv' := Facts.returns_sound (g := g) (ν := ν) (Facts.ok_empty ν) _ hv
              rw [Facts.nf_eval (Facts.ok_empty ν)] at hv'
              obtain ⟨w, hw'⟩ := Option.isSome_iff_exists.1 hv'
              exact ⟨w, w, by rw [LTm.eval_app1, hw']; rfl, rfl⟩
          | _ => simp only at hv; cases hv
        obtain ⟨w, mv, hvw, hmv⟩ := hval
        obtain ⟨hp, hhp⟩ := Option.isSome_iff_exists.1 (hw mv)
        rw [LTm.eval_app3, hμ, had, hvw, Op3.eval_eq_evalM]
        simp only [Op3.evalM, Grown.writeT, Option.bind_eq_bind, Option.bind_some, hra, hmv, hhp]
        rfl
      · rename_i m R hR hX
        obtain rfl := LTm.memView_addM hX
        obtain ⟨μ, hμ⟩ := Option.isSome_iff_exists.1 (ih _ h)
        rw [LTm.eval_app1, hμ, Op1.eval_eq_evalM]
        rfl
      · rename_i m U hU S hX
        obtain rfl := LTm.memView_copySt hX
        simp only [Bool.and_eq_true] at h
        obtain ⟨hm, hS⟩ := h
        obtain ⟨μ, hμ⟩ := Option.isSome_iff_exists.1 (ih _ hm)
        have hSs : (S.eval g ν : Option (SVal U)).isSome = true := by
          cases S with
          | app1 o x =>
            simp only at hS
            cases o <;> simp only [Op1.svOk, Bool.false_eq_true] at hS
            obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (retsS_isSome (g := g) (ν := ν) hS)
            rw [LTm.eval_app1, hw]; rfl
          | _ => simp only at hS; cases hS
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hSs
        rw [LTm.eval_app2, hμ, hv, Op2.eval_eq_evalM]
        rfl
      · exact retsS_isSome h
    | ident t M =>
      intro μ hμ
      simp only [memOkN, memOkStep] at h
      split at h
      · rename_i m R' hR ht
        cases t with
        | app1 o x =>
          cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht
          simp only [IdentV.alloc.injEq] at ht
          obtain ⟨rfl, rfl⟩ := ht
          obtain ⟨ω, hω, hext⟩ := LTm.onSpine_eval h hμ
          rw [LTm.eval_app1, Op1.eval_eq_evalM] at hω
          simp only [Op1.evalM, Option.map_eq_some_iff] at hω
          obtain ⟨μ₀, hμ₀, rfl⟩ := hω
          refine ⟨(μ₀.heap.allocDefault _ hR).val.id, ?_, ?_⟩
          · rw [LTm.eval_app1, hμ₀, Op1.eval_eq_evalM]; rfl
          · exact HTy.getElem?_of_prefix hext (μ₀.heap.allocDefault _ hR).val.get?
        | app2 o x y => cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq] at ht
        | _ => simp only [LTm.identView, reduceCtorEq] at ht
      · rename_i m U hU S ht
        cases t with
        | app1 o x => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht
        | app2 o x y =>
          cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq] at ht
          simp only [IdentV.copy.injEq] at ht
          obtain ⟨rfl, hU', hS⟩ := ht
          subst hU'
          cases hS
          obtain ⟨ω, hω, hext⟩ := LTm.onSpine_eval h hμ
          rw [LTm.eval_app2, Op2.eval_eq_evalM] at hω
          simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.some.injEq] at hω
          obtain ⟨μ₀, hμ₀, v, hv, rfl⟩ := hω
          refine ⟨(v.copyStToM μ₀.heap hU).val.id, ?_, ?_⟩
          · rw [LTm.eval_app2, hμ₀, hv, Op2.eval_eq_evalM]; rfl
          · exact HTy.getElem?_of_prefix hext (v.copyStToM μ₀.heap hU).val.get?
        | _ => simp only [LTm.identView, reduceCtorEq] at ht
      · rename_i X T b ht
        simp only [Bool.and_eq_true] at h
        obtain ⟨hX, hb⟩ := h
        cases t with
        | app1 o x => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht
        | app2 o x y =>
          cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq] at ht
          simp only [IdentV.iread.injEq] at ht
          obtain ⟨rfl, hT, hb'⟩ := ht
          subst hT
          cases hb'
          obtain ⟨ξ, hξ, hext⟩ := LTm.onSpine_eval hX hμ
          obtain ⟨ad, ra, had, hra, hrd, -⟩ := ih _ hb ξ hξ
          obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hrd
          refine ⟨r.id, ?_, HTy.getElem?_of_prefix hext r.get?⟩
          rw [LTm.iread_evalT, hξ, had, Option.bind_some, Option.bind_some, hra, Option.bind_some,
            hr]
          rfl
        | _ => simp only [LTm.identView, reduceCtorEq] at ht
      · cases h
    | addr a M =>
      intro μ hμ
      simp only [memOkN, memOkStep] at h
      split at h
      · rename_i R t ht
        cases a with
        | app1 o x =>
          cases o <;> simp only [LTm.fieldObj?, Op1.fieldObj, reduceCtorEq, Option.some.injEq] at ht
          obtain ⟨rfl, ht⟩ := Sigma.mk.inj ht
          cases ht
          rename_i s f T hf
          obtain ⟨id, hid, hty⟩ := ih _ h μ hμ
          refine ⟨.field id hf, .field ⟨id, hty⟩ hf, ?_, ?_, rfl, fun _ => rfl⟩
          · rw [LTm.eval_app1, hid]; rfl
          · simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?, hty, dite_true,
              Option.map_some]
        | _ => simp only [LTm.fieldObj?, reduceCtorEq] at ht
      · cases h

end Ok

/-! ## The walk down a memory -/

section Walk

variable {g : State C []} {ν : AEnv}

/-- What a word or identity written is: `mval(x)`'s `x`, `ref(t)`'s `t`. -/
def _root_.Solidity.Op1.mvArg {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    Option ((u : Srt) × LTm C u) :=
  match o, x with
  | .mval, x => some ⟨_, x⟩
  | .ref, x => some ⟨_, x⟩
  | _, _ => none

/-- What a memory value term writes. -/
def LTm.mvArg? {s : Srt} (v : LTm C s) : Option ((u : Srt) × LTm C u) :=
  match v with
  | .app1 o x => o.mvArg x
  | _ => none

/-- **A read of a word, walked down its memory** `n` writes and
allocations deep: `readOnWrite`, `readWriteDifferent`, `readAddDifferent`,
`readAddEqual`.  By the recursor on the depth. -/
def memReadN (n : Nat) : {P : PrimTy} → LTm C .mem → LTm C (.addr (.prim P)) → LTm C (.val P) :=
  Nat.rec (motive := fun _ => {P : PrimTy} → LTm C .mem → LTm C (.addr (.prim P)) → LTm C (.val P))
    (fun X b => .app2 .read X b)
    (fun _ ih {P} X b =>
      match X.memView with
      | .write m a v =>
        if a.beqR b then
          match v.mvArg? with
          | some ⟨_, x⟩ =>
            match x.castTo? with
            | some x' => .seq X x'
            | none => .app2 .read X b
          | none => .app2 .read X b
        else if a.apart? b then .seq X (ih m b)
        else .app2 .read X b
      | .addM m R _ =>
        if b.boundedIn m then ih m b
        else if (LTm.freshPath? m R b).bind (Ty.ref R).memberTy == some (.prim P) then
          .seq m (.lit (PrimTy.dflt P))
        else .app2 .read X b
      | .copySt m _ S =>
        if b.boundedIn m then .seq S (ih m b) else .app2 .read X b
      | .other => .app2 .read X b) n

/-- **A read of an identity, walked down its memory.** -/
def memIReadN (n : Nat) : {R : RefTy} → LTm C .mem → LTm C (.addr (.ref R)) → LTm C (.ident R) :=
  Nat.rec (motive := fun _ => {R : RefTy} → LTm C .mem → LTm C (.addr (.ref R)) → LTm C (.ident R))
    (fun X b => .app2 .iread X b)
    (fun _ ih {R} X b =>
      match X.memView with
      | .write m a v =>
        if a.beqR b then
          match v.mvArg? with
          | some ⟨_, x⟩ =>
            match x.castTo? with
            | some x' => .seq X x'
            | none => .app2 .iread X b
          | none => .app2 .iread X b
        else if a.apart? b then .seq X (ih m b)
        else .app2 .iread X b
      | .addM m _ _ =>
        if b.boundedIn m then ih m b else .app2 .iread X b
      | .copySt m _ S =>
        if b.boundedIn m then .seq S (ih m b) else .app2 .iread X b
      | .other => .app2 .iread X b) n

theorem memReadN_eval (n : Nat) : ∀ {P : PrimTy} (X : LTm C .mem) (b : LTm C (.addr (.prim P))),
    ((memReadN n X b).eval g ν : Option P.Denote) = (LTm.app2 .read X b).eval g ν := by
  induction n with
  | zero => intro P X b; rfl
  | succ n ih =>
    intro P X b
    show (match X.memView with
      | .write m a v =>
        if a.beqR b then
          match v.mvArg? with
          | some ⟨_, x⟩ =>
            match x.castTo? with
            | some x' => .seq X x'
            | none => .app2 .read X b
          | none => .app2 .read X b
        else if a.apart? b then .seq X (memReadN n m b)
        else .app2 .read X b
      | .addM m R _ =>
        if b.boundedIn m then memReadN n m b
        else if (LTm.freshPath? m R b).bind (Ty.ref R).memberTy == some (.prim P) then
          .seq m (.lit (PrimTy.dflt P))
        else .app2 .read X b
      | .copySt m _ S =>
        if b.boundedIn m then .seq S (memReadN n m b) else .app2 .read X b
      | .other => .app2 .read X b : LTm C (.val P)).eval g ν = _
    split
    · rename_i m T a v hX
      obtain rfl := LTm.memView_write hX
      split
      · rename_i hab
        cases LTm.sigma_eq_of_beqR hab
        split
        · rename_i u x hv
          split
          · rename_i x' hx
            cases LTm.castTo?_eq hx
            cases v with
            | app1 o y =>
              cases o <;> simp only [LTm.mvArg?, Op1.mvArg, reduceCtorEq, Option.some.injEq] at hv
              obtain ⟨-, h⟩ := Sigma.mk.inj hv
              cases h
              exact (LTm.read_write_same m _ x').symm
            | _ => simp only [LTm.mvArg?, reduceCtorEq] at hv
          · rfl
        · rfl
      · split
        · rename_i hap
          rw [LTm.read_write_apart' m a v b hap, LTm.eval_seq, LTm.eval_seq, ih]
        · rfl
    · rename_i m R hR hX
      obtain rfl := LTm.memView_addM hX
      split
      · rename_i hb
        rw [ih, LTm.read_addM_old m R hR b hb]
      · split
        · rename_i hf
          exact (LTm.read_addM_fresh m R hR b (beq_iff_eq.1 hf)).symm
        · rfl
    · rename_i m U hU S hX
      obtain rfl := LTm.memView_copySt hX
      split
      · rename_i hb
        rw [LTm.read_copySt_old m hU S b hb, LTm.eval_seq, LTm.eval_seq, ih]
      · rfl
    · rfl

theorem memIReadN_eval (n : Nat) : ∀ {R : RefTy} (X : LTm C .mem) (b : LTm C (.addr (.ref R))),
    ((memIReadN n X b).eval g ν : Option Nat) = (LTm.app2 .iread X b).eval g ν := by
  induction n with
  | zero => intro R X b; rfl
  | succ n ih =>
    intro R X b
    show (match X.memView with
      | .write m a v =>
        if a.beqR b then
          match v.mvArg? with
          | some ⟨_, x⟩ =>
            match x.castTo? with
            | some x' => .seq X x'
            | none => .app2 .iread X b
          | none => .app2 .iread X b
        else if a.apart? b then .seq X (memIReadN n m b)
        else .app2 .iread X b
      | .addM m _ _ =>
        if b.boundedIn m then memIReadN n m b else .app2 .iread X b
      | .copySt m _ S =>
        if b.boundedIn m then .seq S (memIReadN n m b) else .app2 .iread X b
      | .other => .app2 .iread X b : LTm C (.ident R)).eval g ν = _
    split
    · rename_i m T a v hX
      obtain rfl := LTm.memView_write hX
      split
      · rename_i hab
        cases LTm.sigma_eq_of_beqR hab
        split
        · rename_i u x hv
          split
          · rename_i x' hx
            cases LTm.castTo?_eq hx
            cases v with
            | app1 o y =>
              cases o <;> simp only [LTm.mvArg?, Op1.mvArg, reduceCtorEq, Option.some.injEq] at hv
              obtain ⟨-, h⟩ := Sigma.mk.inj hv
              cases h
              exact (LTm.iread_write_same m _ x').symm
            | _ => simp only [LTm.mvArg?, reduceCtorEq] at hv
          · rfl
        · rfl
      · split
        · rename_i hap
          rw [LTm.iread_write_apart' m a v b hap, LTm.eval_seq, LTm.eval_seq, ih]
        · rfl
    · rename_i m R' hR hX
      obtain rfl := LTm.memView_addM hX
      split
      · rename_i hb
        rw [ih, LTm.iread_addM_old m R' hR b hb]
      · rfl
    · rename_i m U hU S hX
      obtain rfl := LTm.memView_copySt hX
      split
      · rename_i hb
        rw [LTm.iread_copySt_old m hU S b hb, LTm.eval_seq, LTm.eval_seq, ih]
      · rfl
    · rfl

end Walk

/-! ## The pass -/

section Pass

variable {g : State C []} {ν : AEnv}

/-- How deep a read walks down a memory. -/
def memFuel : Nat := 64

/-- A binary symbol, its reads of memory walked. -/
def _root_.Solidity.Op2.memRes {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    LTm C s :=
  match o, x, y with
  | .read, X, b => memReadN memFuel X b
  | .iread, X, b => memIReadN memFuel X b
  | o, x, y => .app2 o x y

theorem Op2.memRes_eval {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    (o.memRes x y).eval g ν = (LTm.app2 o x y).eval g ν := by
  cases o
  case read => simp only [Op2.memRes]; exact memReadN_eval _ x y
  case iread => simp only [Op2.memRes]; exact memIReadN_eval _ x y
  all_goals simp only [Op2.memRes]

/-- `LTm.memRes`'s compiled twin. -/
def LTm.memResM : {s : Srt} → LTm C s → LTm C s
  | _, .var k => .var k
  | _, .app0 o => .app0 o
  | _, .app1 o x => .app1 o x.memResM
  | _, .app2 o x y => o.memRes x.memResM y.memResM
  | _, .app3 o x y z => .app3 o x.memResM y.memResM z.memResM
  | _, .index it q i => .index it q.memResM i.memResM
  | _, .obsW q => .obsW q.memResM
  | _, .obsL q => .obsL q.memResM
  | _, .obsH q => .obsH q.memResM
  | _, .seq d a => .seq d.memResM a.memResM
  | _, .orElse a b => .orElse a.memResM b.memResM
  | _, .kite a b t e => .kite a.memResM b.memResM t.memResM e.memResM
  | _, .err => .err

/-- **Every read of memory walked down its memory**, bottom-up.  By the
recursor. -/
@[implemented_by LTm.memResM]
def LTm.memRes {s : Srt} (t : LTm C s) : LTm C s :=
  @LTm.rec C (fun s _ => LTm C s)
    (@fun _ k => .var k) (@fun _ o => .app0 o)
    (@fun _ _ o _ ihx => .app1 o ihx)
    (@fun _ _ _ o _ _ ihx ihy => o.memRes ihx ihy)
    (@fun _ _ _ _ o _ _ _ ihx ihy ihz => .app3 o ihx ihy ihz)
    (@fun _ _ _ it _ _ ihq ihi => .index it ihq ihi)
    (@fun _ _ ih => .obsW ih) (@fun _ _ ih => .obsL ih) (@fun _ _ ih => .obsH ih)
    (@fun _ _ _ _ ihd iha => .seq ihd iha)
    (@fun _ _ _ iha ihb => .orElse iha ihb)
    (@fun _ _ _ _ _ _ iha ihb iht ihe => .kite iha ihb iht ihe)
    (@fun _ => .err) s t

theorem LTm.memRes_eq_memResM {s : Srt} (t : LTm C s) : t.memRes = t.memResM := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih => simp only [LTm.memResM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.memResM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [LTm.memResM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [LTm.memResM, ← ihq, ← ihi]; rfl
  | obsW q ih | obsL q ih | obsH q ih => simp only [LTm.memResM, ← ih]; rfl
  | seq d a ihd iha => simp only [LTm.memResM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [LTm.memResM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [LTm.memResM, ← iha, ← ihb, ← iht, ← ihe]; rfl

/-- **The pass keeps what a term reads.** -/
theorem LTm.memRes_eval {s : Srt} (t : LTm C s) : t.memRes.eval g ν = t.eval g ν := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih =>
    show (LTm.app1 o x.memRes).eval g ν = _
    rw [LTm.eval_app1, LTm.eval_app1, ih]
  | app2 o x y ihx ihy =>
    show (o.memRes x.memRes y.memRes).eval g ν = _
    rw [Op2.memRes_eval, LTm.eval_app2, LTm.eval_app2, ihx, ihy]
  | app3 o x y z ihx ihy ihz =>
    show (LTm.app3 o x.memRes y.memRes z.memRes).eval g ν = _
    rw [LTm.eval_app3, LTm.eval_app3, ihx, ihy, ihz]
  | index it q i ihq ihi =>
    show (LTm.index it q.memRes i.memRes).eval g ν = _
    rw [LTm.eval_index, LTm.eval_index, ihq, ihi]
  | obsW q ih =>
    show (LTm.obsW q.memRes).eval g ν = _
    rw [LTm.eval_obsW, LTm.eval_obsW, ih]
  | obsL q ih =>
    show (LTm.obsL q.memRes).eval g ν = _
    rw [LTm.eval_obsL, LTm.eval_obsL, ih]
  | obsH q ih =>
    show (LTm.obsH q.memRes).eval g ν = _
    rw [LTm.eval_obsH, LTm.eval_obsH, ih]
  | seq d a ihd iha =>
    show (LTm.seq d.memRes a.memRes).eval g ν = _
    rw [LTm.eval_seq, LTm.eval_seq, ihd, iha]
  | orElse a b iha ihb =>
    show (LTm.orElse a.memRes b.memRes).eval g ν = _
    rw [LTm.eval_orElse, LTm.eval_orElse, iha, ihb]
  | kite a b t e iha ihb iht ihe =>
    show (LTm.kite a.memRes b.memRes t.memRes e.memRes).eval g ν = _
    rw [LTm.eval_kite, LTm.eval_kite, iha, ihb, iht, ihe]

/-- `d; a`, the guard dropped where it is a memory that returns
(`memOkN`). -/
def seqMemL {s' s : Srt} (d : LTm C s') (a : LTm C s) : LTm C s :=
  match (d.castTo? : Option (LTm C .mem)) with
  | some M => if memOkN memFuel (.mem M) then a else .seq d a
  | none => .seq d a

theorem seqMemL_eval {s' s : Srt} (d : LTm C s') (a : LTm C s) :
    (seqMemL d a).eval g ν = (LTm.seq d a).eval g ν := by
  unfold seqMemL
  split
  · rename_i M hM
    split
    · rename_i hok
      cases LTm.castTo?_eq hM
      obtain ⟨μ, hμ⟩ := Option.isSome_iff_exists.1
        (memOkN_sound (g := g) (ν := ν) memFuel (.mem _) hok)
      rw [LTm.eval_seq, hμ]; rfl
    · rfl
  · rfl

/-- `LTm.seqMem`'s compiled twin. -/
def LTm.seqMemM : {s : Srt} → LTm C s → LTm C s
  | _, .var k => .var k
  | _, .app0 o => .app0 o
  | _, .app1 o x => .app1 o x.seqMemM
  | _, .app2 o x y => .app2 o x.seqMemM y.seqMemM
  | _, .app3 o x y z => .app3 o x.seqMemM y.seqMemM z.seqMemM
  | _, .index it q i => .index it q.seqMemM i.seqMemM
  | _, .obsW q => .obsW q.seqMemM
  | _, .obsL q => .obsL q.seqMemM
  | _, .obsH q => .obsH q.seqMemM
  | _, .seq d a => seqMemL d.seqMemM a.seqMemM
  | _, .orElse a b => .orElse a.seqMemM b.seqMemM
  | _, .kite a b t e => .kite a.seqMemM b.seqMemM t.seqMemM e.seqMemM
  | _, .err => .err

/-- **Every guard of a memory that returns dropped.**  By the recursor. -/
@[implemented_by LTm.seqMemM]
def LTm.seqMem {s : Srt} (t : LTm C s) : LTm C s :=
  @LTm.rec C (fun s _ => LTm C s)
    (@fun _ k => .var k) (@fun _ o => .app0 o)
    (@fun _ _ o _ ihx => .app1 o ihx)
    (@fun _ _ _ o _ _ ihx ihy => .app2 o ihx ihy)
    (@fun _ _ _ _ o _ _ _ ihx ihy ihz => .app3 o ihx ihy ihz)
    (@fun _ _ _ it _ _ ihq ihi => .index it ihq ihi)
    (@fun _ _ ih => .obsW ih) (@fun _ _ ih => .obsL ih) (@fun _ _ ih => .obsH ih)
    (@fun _ _ _ _ ihd iha => seqMemL ihd iha)
    (@fun _ _ _ iha ihb => .orElse iha ihb)
    (@fun _ _ _ _ _ _ iha ihb iht ihe => .kite iha ihb iht ihe)
    (@fun _ => .err) s t

theorem LTm.seqMem_eval {s : Srt} (t : LTm C s) : t.seqMem.eval g ν = t.eval g ν := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih =>
    show (LTm.app1 o x.seqMem).eval g ν = _
    rw [LTm.eval_app1, LTm.eval_app1, ih]
  | app2 o x y ihx ihy =>
    show (LTm.app2 o x.seqMem y.seqMem).eval g ν = _
    rw [LTm.eval_app2, LTm.eval_app2, ihx, ihy]
  | app3 o x y z ihx ihy ihz =>
    show (LTm.app3 o x.seqMem y.seqMem z.seqMem).eval g ν = _
    rw [LTm.eval_app3, LTm.eval_app3, ihx, ihy, ihz]
  | index it q i ihq ihi =>
    show (LTm.index it q.seqMem i.seqMem).eval g ν = _
    rw [LTm.eval_index, LTm.eval_index, ihq, ihi]
  | obsW q ih =>
    show (LTm.obsW q.seqMem).eval g ν = _
    rw [LTm.eval_obsW, LTm.eval_obsW, ih]
  | obsL q ih =>
    show (LTm.obsL q.seqMem).eval g ν = _
    rw [LTm.eval_obsL, LTm.eval_obsL, ih]
  | obsH q ih =>
    show (LTm.obsH q.seqMem).eval g ν = _
    rw [LTm.eval_obsH, LTm.eval_obsH, ih]
  | seq d a ihd iha =>
    show (seqMemL d.seqMem a.seqMem).eval g ν = _
    rw [seqMemL_eval, LTm.eval_seq, LTm.eval_seq, ihd, iha]
  | orElse a b iha ihb =>
    show (LTm.orElse a.seqMem b.seqMem).eval g ν = _
    rw [LTm.eval_orElse, LTm.eval_orElse, iha, ihb]
  | kite a b t e iha ihb iht ihe =>
    show (LTm.kite a.seqMem b.seqMem t.seqMem e.seqMem).eval g ν = _
    rw [LTm.eval_kite, LTm.eval_kite, iha, ihb, iht, ihe]

/-- `LFml.memRes`'s compiled twin. -/
def LFml.memResM : LFml C → LFml C
  | .tt => .tt
  | .eq a b => .eq a.memRes.seqMem b.memRes.seqMem
  | .not φ => .not φ.memResM
  | .and φ ψ => .and φ.memResM ψ.memResM
  | .imp φ ψ => .imp φ.memResM ψ.memResM
  | .all k p φ => .all k p φ.memResM

/-- **Every read of memory in a formula walked.**  By the recursor. -/
@[implemented_by LFml.memResM]
def LFml.memRes (φ : LFml C) : LFml C :=
  @LFml.rec C (fun _ => LFml C) .tt (@fun _ a b => .eq a.memRes.seqMem b.memRes.seqMem)
    (fun _ ih => .not ih) (fun _ _ ihφ ihψ => .and ihφ ihψ) (fun _ _ ihφ ihψ => .imp ihφ ihψ)
    (fun k p _ ih => .all k p ih) φ

theorem LFml.memRes_eq_memResM (φ : LFml C) : φ.memRes = φ.memResM := by
  induction φ with
  | tt | eq => rfl
  | not φ ih | all k p φ ih => simp only [LFml.memResM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [LFml.memResM, ← ihφ, ← ihψ]; rfl

theorem LFml.memRes_holds (φ : LFml C) : ∀ (ν : AEnv), φ.memRes.holds g ν ↔ φ.holds g ν := by
  induction φ with
  | tt => intro ν; exact Iff.rfl
  | eq a b =>
    intro ν
    show (LFml.eq a.memRes.seqMem b.memRes.seqMem).holds g ν ↔ _
    rw [LFml.holds_eq_iff, LFml.holds_eq_iff, LTm.seqMem_eval, LTm.seqMem_eval, LTm.memRes_eval,
      LTm.memRes_eval]
  | not φ ih => intro ν; exact not_congr (ih ν)
  | and φ ψ ihφ ihψ => intro ν; exact and_congr (ihφ ν) (ihψ ν)
  | imp φ ψ ihφ ihψ => intro ν; exact imp_congr (ihφ ν) (ihψ ν)
  | all k p φ ih => intro ν; exact forall_congr' fun v => ih _

theorem LFml.memRes_valid {φ : LFml C} (h : φ.memRes.Valid) : φ.Valid :=
  fun g ν => (LFml.memRes_holds φ ν).1 (h g ν)

end Pass

/-- **The closer with memory read**: every read of memory walked
(`LFml.memRes`), then `LFml.close`. -/
def LFml.closeMem (φ : LFml C) : Bool := φ.memRes.close

theorem LFml.closeMem_valid {φ : LFml C} (h : φ.closeMem = true) : φ.Valid :=
  LFml.memRes_valid (LFml.close_valid h)

end Decide

end Solidity
