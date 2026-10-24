import Solidity.Calculus.Closer
import Solidity.Calculus.ElimFacts
import Solidity.Calculus.DecideEval
import Solidity.Calculus.TermLaws
import Solidity.Theory.Typed.MemMirror

/-!
# Memory reads: the spine and the objects on it

What an allocation mints, the spine of a memory term, older objects, the
fresh root, memory terms and addresses viewed, and the guards.

A piece of `Calculus/MemRead.lean`, whose docstring describes the whole.
-/

namespace Solidity

namespace Decide

open Semantics (lookupBy structDef)

variable {C : Contract}

/-! ## What an allocation mints, by the heap typing

A copy into memory grows the heap typing by what it allocates alone: the
objects' contents are the value's, their identities past the typing it
starts from.  So two heaps of one typing mint the same identities. -/

mutual
/-- **A copy grows a heap typing the same over any heap of it.** -/
theorem _root_.Solidity.SVal.copyStToM_H' : {T : Ty} → (v : SVal T) → (h : T.mapFree = true) →
    {H₁ H₂ : HTy} → (hp₁ : Heap H₁) → (hp₂ : Heap H₂) → H₁ = H₂ →
    (v.copyStToM hp₁ h).H' = (v.copyStToM hp₂ h).H'
  | _, .prim _, _, _, _, hp₁, hp₂, e => by
    rw [SVal.copyStToM_prim, SVal.copyStToM_prim]; exact e
  | _, .struct fs, _, _, _, hp₁, hp₂, e => by
    rw [SVal.copyStToM_struct, SVal.copyStToM_struct]
    exact congrArg (· ++ [_]) (SFields.copyStToM_H' fs _ hp₁ hp₂ e)
  | _, .array v _ _, _, _, _, hp₁, hp₂, e => by
    rw [SVal.copyStToM_array, SVal.copyStToM_array]
    exact congrArg (· ++ [_]) (SVec.copyStToM_H' v _ hp₁ hp₂ e)
  | _, .fixed v, _, _, _, hp₁, hp₂, e => by
    rw [SVal.copyStToM_fixed, SVal.copyStToM_fixed]
    exact congrArg (· ++ [_]) (SVec.copyStToM_H' v _ hp₁ hp₂ e)
  | _, .map _ _, h, _, _, _, _, _ => by simp only [Ty.mapFree, Bool.false_eq_true] at h

theorem _root_.Solidity.SFields.copyStToM_H' : {fs : List (Name × Ty)} → (x : SFields fs) →
    (h : ∀ fT ∈ fs, fT.2.mapFree = true) → {H₁ H₂ : HTy} → (hp₁ : Heap H₁) → (hp₂ : Heap H₂) →
    H₁ = H₂ → (x.copyStToM hp₁ h).H' = (x.copyStToM hp₂ h).H'
  | _, .nil, _, _, _, hp₁, hp₂, e => by
    rw [SFields.copyStToM_nil, SFields.copyStToM_nil]; exact e
  | _, .cons v rest, _, _, _, hp₁, hp₂, e => by
    rw [SFields.copyStToM_cons, SFields.copyStToM_cons]
    exact SFields.copyStToM_H' rest _ _ _ (SVal.copyStToM_H' v _ hp₁ hp₂ e)

theorem _root_.Solidity.SVec.copyStToM_H' : {E : Ty} → {n : Nat} → (l : SVec E n) →
    (h : E.mapFree = true) → {H₁ H₂ : HTy} → (hp₁ : Heap H₁) → (hp₂ : Heap H₂) → H₁ = H₂ →
    (l.copyStToM hp₁ h).H' = (l.copyStToM hp₂ h).H'
  | _, _, .nil, _, _, _, hp₁, hp₂, e => by
    rw [SVec.copyStToM_nil, SVec.copyStToM_nil]; exact e
  | _, _, .cons v rest, h, _, _, hp₁, hp₂, e => by
    rw [SVec.copyStToM_cons, SVec.copyStToM_cons]
    exact SVec.copyStToM_H' rest h _ _ (SVal.copyStToM_H' v h hp₁ hp₂ e)
end

/-- **A copy of a reference mints the same root over any heap of a
typing**: the root is the identity past what its members allocate. -/
theorem _root_.Solidity.SVal.copyStToM_id_eq {R : RefTy} (v : SVal (.ref R))
    (h : (Ty.ref R).mapFree = true) {H₁ H₂ : HTy} (hp₁ : Heap H₁) (hp₂ : Heap H₂)
    (e : H₁ = H₂) :
    ((v.copyStToM hp₁ h).val : HRef _ R).id = ((v.copyStToM hp₂ h).val : HRef _ R).id := by
  cases v with
  | struct fs =>
    rw [SVal.copyStToM_struct, SVal.copyStToM_struct]
    exact congrArg List.length (SFields.copyStToM_H' fs _ hp₁ hp₂ e)
  | array v sh hn =>
    rw [SVal.copyStToM_array, SVal.copyStToM_array]
    exact congrArg List.length (SVec.copyStToM_H' v _ hp₁ hp₂ e)
  | fixed v =>
    rw [SVal.copyStToM_fixed, SVal.copyStToM_fixed]
    exact congrArg List.length (SVec.copyStToM_H' v _ hp₁ hp₂ e)
  | map => simp only [Ty.mapFree, Bool.false_eq_true] at h

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

/-- `LTm.stripW` at a binary symbol: a copy's memory stripped. -/
def _root_.Solidity.Op2.stripStep {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b)
    (ihx : LTm C a) : LTm C s :=
  match o, ihx with
  | .copySt h, ihx => .app2 (.copySt h) ihx y
  | o, _ => .app2 o x y

/-- `LTm.stripW` at a ternary symbol: a write dropped. -/
def _root_.Solidity.Op3.stripStep {a b c s : Srt} (o : Op3 C a b c s) (x : LTm C a) (y : LTm C b)
    (z : LTm C c) (ihx : LTm C a) : LTm C s :=
  match o, ihx with
  | .write, ihx => ihx
  | o, _ => .app3 o x y z

/-- `LTm.stripW`'s compiled twin. -/
def LTm.stripWM : {s : Srt} → LTm C s → LTm C s
  | _, .app2 o x y => o.stripStep x y x.stripWM
  | _, .app3 o x y z => o.stripStep x y z x.stripWM
  | _, t => t

/-- **A memory without its writes**: the copies on its spine down to the
first node that is neither a write nor a copy (an `addM` is kept with what
is below it), which leave the heap typing a write keeps
(`LTm.stripW_eval`), so an identity minted over it is the one minted over
the memory.  Generic in the sort, the identity off the spine; by the
recursor. -/
@[implemented_by LTm.stripWM]
def LTm.stripW {s : Srt} (t : LTm C s) : LTm C s :=
  @LTm.rec C (fun s _ => LTm C s)
    (@fun _ k => .var k) (@fun _ o => .app0 o)
    (@fun _ _ o x _ => .app1 o x)
    (@fun _ _ _ o x y ihx _ => o.stripStep x y ihx)
    (@fun _ _ _ _ o x y z ihx _ _ => o.stripStep x y z ihx)
    (@fun _ _ _ it q i _ _ => .index it q i)
    (@fun _ q _ => .obsW q) (@fun _ q _ => .obsL q) (@fun _ q _ => .obsH q)
    (@fun _ _ d a _ _ => .seq d a)
    (@fun _ a b _ _ => .orElse a b)
    (@fun _ _ a b t e _ _ _ _ => .kite a b t e)
    (@fun _ => .err) s t

theorem LTm.stripW_eq_stripWM {s : Srt} (t : LTm C s) : t.stripW = t.stripWM := by
  induction t with
  | app2 o x y ihx => simp only [LTm.stripWM, ← ihx]; rfl
  | app3 o x y z ihx => simp only [LTm.stripWM, ← ihx]; rfl
  | _ => rfl

/-- **`w` is on `t`'s spine, up to writes**: on it, or, where `w` has no
write, on the allocations of `t`'s spine (`LTm.stripW`). -/
def LTm.onSpineS {k : Srt} (t w : LTm C k) : Bool :=
  t.onSpine w || (w.stripW.beqR w && t.stripW.onSpine w)

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

/-- At the memory sort: where the first returns, the second returns at
its heap typing. -/
def Srt.SameHL {H : HTy} : (u : Srt) → Option (u.Den C H) → Option (u.Den C H) → Prop
  | .mem, x, y => ∀ μ : Grown H (fun _ => Unit), x = some μ →
      ∃ μ' : Grown H (fun _ => Unit), y = some μ' ∧ μ'.H' = μ.H'
  | _, _, _ => True

theorem Srt.SameHL.refl {H : HTy} : (u : Srt) → (x : Option (u.Den C H)) → Srt.SameHL u x x
  | .mem, _ => fun μ h => ⟨μ, h, rfl⟩
  | .val _, _ | .path _, _ | .st, _ | .sv _, _ | .ident _, _ | .addr _, _ | .mv _, _
  | .sts _, _ | .spath _ _, _ | .kint, _ => trivial

theorem LTm.stripW_sameH {u : Srt} (t : LTm C u) :
    Srt.SameHL (C := C) u (t.eval g ν) (t.stripW.eval g ν) := by
  induction t with
  | app2 o x y ihx _ihy =>
    cases o
    case copySt =>
      rename_i hT
      intro μ hμ
      rw [LTm.eval_app2, Op2.eval_eq_evalM] at hμ
      simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hμ
      obtain ⟨μ₀, hμ₀, v, hv, rfl⟩ := hμ
      obtain ⟨μ₁, h₁, e₁⟩ := ihx μ₀ hμ₀
      refine ⟨μ₁.then (v.copyStToM μ₁.heap hT), ?_, ?_⟩
      · show (LTm.app2 (.copySt hT) x.stripW y).eval g ν = _
        rw [LTm.eval_app2, Op2.eval_eq_evalM]
        simp only [Op2.evalM, h₁, hv, Option.bind_eq_bind, Option.bind_some]
      · exact SVal.copyStToM_H' v hT μ₁.heap μ₀.heap e₁
    all_goals exact Srt.SameHL.refl _ _
  | app3 o x y z ihx _ _ =>
    cases o
    case write =>
      intro μ hμ
      rw [LTm.eval_app3, Op3.eval_eq_evalM] at hμ
      simp only [Op3.evalM, Grown.writeT, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hμ
      obtain ⟨μ₀, hμ₀, ad, -, w', -, ra, -, mv, -, hp, -, rfl⟩ := hμ
      obtain ⟨μ₁, h₁, e₁⟩ := ihx μ₀ hμ₀
      exact ⟨μ₁, h₁, e₁⟩
    all_goals exact Srt.SameHL.refl _ _
  | _ => exact Srt.SameHL.refl _ _

/-- **A memory that returns, without its writes, returns at its heap
typing**: a write keeps the typing (`Grown.writeT`), and a copy grows a
typing by what it allocates alone (`SVal.copyStToM_H'`). -/
theorem LTm.stripW_eval {M : LTm C .mem} {μ : Grown g.H (fun _ => Unit)}
    (h : M.eval g ν = some μ) :
    ∃ μ' : Grown g.H (fun _ => Unit), M.stripW.eval g ν = some μ' ∧ μ'.H' = μ.H' :=
  LTm.stripW_sameH M μ h

/-- **An identity's memory read as a spine node's**: the node's memory, or
it without its writes (`LTm.stripW`), returns where the node's does, at its
heap typing. -/
theorem LTm.base_eval {m' m : LTm C .mem} (h : (m'.beqR m || m'.beqR m.stripW) = true)
    {μ : Grown g.H (fun _ => Unit)} (hm : m.eval g ν = some μ) :
    ∃ μ' : Grown g.H (fun _ => Unit), m'.eval g ν = some μ' ∧ μ'.H' = μ.H' := by
  rcases Bool.or_eq_true_iff.1 h with h | h
  · obtain rfl := LTm.eq_of_beqR h
    exact ⟨μ, hm, rfl⟩
  · obtain rfl := LTm.eq_of_beqR h
    exact LTm.stripW_eval hm

theorem LTm.copy_stripW_eval {m : LTm C .mem} {μ : Grown g.H (fun _ => Unit)}
    (hm : m.eval g ν = some μ) {R : RefTy} (h : (Ty.ref R).mapFree = true)
    (S : LTm C (.sv (.ref R))) :
    (LTm.app2 (.copy h) m.stripW S).eval g ν = (LTm.app2 (.copy h) m S).eval g ν := by
  obtain ⟨μ', h', e⟩ := LTm.stripW_eval hm
  rw [LTm.eval_app2, LTm.eval_app2, Op2.eval_eq_evalM, hm, h']
  simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_some]
  cases (S.eval g ν : Option (SVal (.ref R))) with
  | none => rfl
  | some v =>
    simp only [Option.bind_some]
    exact congrArg some (SVal.copyStToM_id_eq v h μ'.heap μ.heap e)

theorem LTm.onSpineS_grows {t w : LTm C .mem} (h : t.onSpineS w = true)
    {μ μ' : Grown g.H (fun _ => Unit)} (ht : t.eval g ν = some μ') (hw : w.eval g ν = some μ) :
    μ.H' <+: μ'.H' := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact LTm.onSpine_grows h ht hw
  · obtain ⟨μ₁, h₁, e₁⟩ := LTm.stripW_eval ht
    have := LTm.onSpine_grows (Bool.and_eq_true_iff.1 h).2 h₁ hw
    rw [e₁] at this
    exact this

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
  | .copy h, m₀, v, _ => M.onSpineS (.app2 (.copySt h) m₀ v)
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
      exact Nat.lt_of_lt_of_le (HRef.id_lt _) (LTm.onSpineS_grows h hM hA).length_le
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
def LTm.uintLit? (t : LTm C (.val .uint)) : Option PrimTy.uint.Denote := t.litV?

theorem LTm.uintLit?_eval {t : LTm C (.val .uint)} {k : PrimTy.uint.Denote} (h : t.uintLit? = some k) :
    (t.eval g ν : Option PrimTy.uint.Denote) = some k :=
  LTm.eval_litV? g ν h

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
    Op1 C a s → LTm C a → Option (List Semantics.Selector) → Option (List Semantics.Selector)
  | .alloc R' _, x, _ => if x.beqR m && R' == R then some [] else none
  | .mfield (f := f) _, _, r => r.map (· ++ [Semantics.Selector.field f])
  | _, _, _ => none

/-- One step of `LTm.freshPath?` at a binary symbol: `iread(addM(m, R), a)`
is what `a` reads, `i[k]` (a literal `k`) the element `k` below `i`'s
path. -/
def _root_.Solidity.Op2.freshStepL (m : LTm C .mem) (R : RefTy) {a b s : Srt} :
    Op2 C a b s → LTm C a → LTm C b → Option (List Semantics.Selector) →
      Option (List Semantics.Selector) → Option (List Semantics.Selector)
  | .iread, x, _, _, ry => if x.isAddM m R then ry else none
  | .mat _, _, y, rx, _ => y.uintLit?.bind fun k => rx.map (· ++ [Semantics.Selector.idx k])
  | _, _, _, _, _ => none

/-- `LTm.freshPath?`'s compiled twin. -/
def LTm.freshPathM (m : LTm C .mem) (R : RefTy) : {u : Srt} → LTm C u → Option (List Semantics.Selector)
  | _, .app1 o x => o.freshStepL m R x (LTm.freshPathM m R x)
  | _, .app2 o x y => o.freshStepL m R x y (LTm.freshPathM m R x) (LTm.freshPathM m R y)
  | _, _ => none

/-- **The path at which a term reads below the root `addM(m, R)`
allocates**: KeY's `idC(idp, flds)`.  Generic in the sort; by the
recursor. -/
@[implemented_by LTm.freshPathM]
def LTm.freshPath? (m : LTm C .mem) (R : RefTy) {u : Srt} (t : LTm C u) :
    Option (List Semantics.Selector) :=
  @LTm.rec C (fun _ _ => Option (List Semantics.Selector))
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

theorem LTm.freshPath_eval {m : LTm C .mem} {R : RefTy} {hR : (Ty.ref R).mapFree = true}
    {μ₀ : Grown g.H (fun _ => Unit)} (hm : m.eval g ν = some μ₀) {u : Srt} (t : LTm C u) :
    ∀ {p : List Semantics.Selector}, LTm.freshPath? m R t = some p →
      Srt.FreshRead (C := C) (μ₀.heap.allocDefault R hR).heap R p u (t.eval g ν) := by
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
        exact Srt.FreshRead.root _ (Heap.dflt_allocDefault μ₀.heap R' hR)
      · cases h
    | mfield hf =>
      simp only [LTm.freshPath?, Op1.freshStepL, Option.map_eq_some_iff] at h
      obtain ⟨p', hp', rfl⟩ := h
      have he : (LTm.app1 (.mfield hf) x).eval g ν =
          (x.eval g ν : Option Nat).map fun id => MAddrT.field id hf := by
        rw [LTm.eval_app1, Op1.eval_eq_evalM]
        simp only [Op1.evalM]
      rw [he]
      exact Srt.FreshRead.field hf (ihx hp')
    | _ => simp only [LTm.freshPath?, Op1.freshStepL, reduceCtorEq] at h
  | app2 o x y ihx ihy =>
    intro p h
    cases o with
    | iread =>
      simp only [LTm.freshPath?, Op2.freshStepL] at h
      split at h
      · rename_i hM
        obtain ⟨hR', rfl⟩ := LTm.eq_of_isAddM hM
        have hX : (LTm.app1 (.addM R hR') m).eval g ν =
            some (μ₀.then (μ₀.heap.allocDefault R hR)) := by
          rw [LTm.eval_app1, Op1.eval_eq_evalM]
          simp only [Op1.evalM, hm, Option.map_some]
        rw [LTm.iread_evalT, hX, Option.bind_some]
        exact Srt.FreshRead.iread (ihy h)
      · cases h
    | mat a =>
      simp only [LTm.freshPath?, Op2.freshStepL, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at h
      obtain ⟨k, hk, p', hp', rfl⟩ := h
      have hw := LTm.uintLit?_eval (g := g) (ν := ν) hk
      have he : (LTm.app2 (.mat a) x y).eval g ν =
          (x.eval g ν : Option Nat).map fun id => MAddrT.index id a k := by
        cases hx : (x.eval g ν : Option Nat) with
        | none => exact LTm.eval_app2_none _ x y hx
        | some id =>
          rw [LTm.eval_app2, Op2.eval_eq_evalM]
          simp only [Op2.evalM, hx, hw, Option.bind_eq_bind, Option.bind_some, Option.map_some]
      rw [he]
      exact Srt.FreshRead.index a k (ihx hp')
    | _ => simp only [LTm.freshPath?, Op2.freshStepL, reduceCtorEq] at h
  | _ => intro p h; simp only [LTm.freshPath?, reduceCtorEq] at h

end Fresh

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

/-- The memory an identity term is fresh over: an allocation's, a copy's
root's. -/
def LTm.freshOver? {s : Srt} (t : LTm C s) : Option (LTm C .mem) :=
  match t.identView with
  | .alloc m _ _ => some m
  | .copy m _ _ => some m
  | _ => none

theorem LTm.freshOver?_eval {R : RefTy} {t : LTm C (.ident R)} {m : LTm C .mem}
    (h : t.freshOver? = some m) {id : Nat} (ht : (t.eval g ν : Option Nat) = some id) :
    ∃ μ : Grown g.H (fun _ => Unit), m.eval g ν = some μ ∧ μ.H'.length ≤ id := by
  unfold LTm.freshOver? at h
  split at h
  · rename_i m' R' hR ht'
    cases h
    cases t with
    | app1 o x =>
      cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq, IdentV.alloc.injEq] at ht'
      obtain ⟨rfl, -⟩ := ht'
      rw [LTm.eval_app1, Op1.eval_eq_evalM] at ht
      simp only [Op1.evalM, Option.map_eq_some_iff] at ht
      obtain ⟨μ, hμ, rfl⟩ := ht
      exact ⟨μ, hμ, SVal.copyStToM_id_ge _ _ _⟩
    | app2 o x y => cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq] at ht'
    | _ => simp only [LTm.identView, reduceCtorEq] at ht'
  · rename_i m' U hU S ht'
    cases h
    cases t with
    | app1 o x => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht'
    | app2 o x y =>
      cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq, IdentV.copy.injEq] at ht'
      obtain ⟨rfl, rfl, hy⟩ := ht'
      cases eq_of_heq hy
      rw [LTm.eval_app2, Op2.eval_eq_evalM] at ht
      simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ht
      obtain ⟨μ, hμ, v, -, rfl⟩ := ht
      exact ⟨μ, hμ, SVal.copyStToM_id_ge _ _ _⟩
    | _ => simp only [LTm.identView, reduceCtorEq] at ht'
  · cases h

end Views

section Guards

variable {g : State C []} {ν : AEnv}

/-- **A guard around a term**: `if (a == b) then · else err`, or `d; ·`
(`guardL`, `seqMemL`). -/
inductive GFrame (C : Contract) where
  | kite {p : PrimTy} (a b : LTm C (.val p))
  | seq {s : Srt} (d : LTm C s)

/-- The guard holds: its two words are equal, its term returns. -/
def GFrame.Holds (g : State C []) (ν : AEnv) : GFrame C → Prop
  | .kite (p := p) a b => ∃ x, (a.eval g ν : Option p.Denote) = some x ∧
      (b.eval g ν : Option p.Denote) = some x
  | .seq d => (d.eval g ν).isSome = true

/-- The guard around `t`. -/
def GFrame.wrap {s : Srt} : GFrame C → LTm C s → LTm C s
  | .kite a b, t => .kite a b t .err
  | .seq d, t => .seq d t

open Classical in
theorem GFrame.wrap_eval (f : GFrame C) {s : Srt} (t : LTm C s) :
    (f.wrap t).eval g ν = if f.Holds g ν then t.eval g ν else none := by
  cases f with
  | kite a b =>
    rename_i p
    show (LTm.kite a b t .err).eval g ν = _
    rw [LTm.eval_kite]
    by_cases hh : GFrame.Holds g ν (.kite a b)
    · obtain ⟨x, hx, hy⟩ := hh
      have hh : GFrame.Holds g ν (.kite a b) := ⟨x, hx, hy⟩
      rw [if_pos hh, hx, hy]
      simp only [Option.bind_some, if_true]
    · rw [if_neg hh]
      cases ha : (a.eval g ν : Option p.Denote) with
      | none => rfl
      | some x =>
        cases hb : (b.eval g ν : Option p.Denote) with
        | none => rfl
        | some y =>
          have hxy : x ≠ y := fun e => hh ⟨x, ha, e ▸ hb⟩
          simp only [Option.bind_some, hxy, if_false]
          rfl
  | seq d =>
    show (LTm.seq d t).eval g ν = _
    rw [LTm.eval_seq]
    by_cases hh : GFrame.Holds g ν (.seq d)
    · rw [if_pos hh]
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hh
      rw [hw]; rfl
    · rw [if_neg hh]
      cases hd : d.eval g ν with
      | none => rfl
      | some w => exact absurd (show (d.eval g ν).isSome = true by rw [hd]; rfl) hh

/-- Two guards of the same terms. -/
def GFrame.beq : GFrame C → GFrame C → Bool
  | .kite a b, .kite a' b' => a.beqR a' && b.beqR b'
  | .seq d, .seq d' => d.beqR d'
  | _, _ => false

theorem GFrame.eq_of_beq {f f' : GFrame C} (h : f.beq f' = true) : f = f' := by
  cases f with
  | kite a b =>
    cases f' with
    | kite a' b' =>
      simp only [GFrame.beq, Bool.and_eq_true] at h
      obtain ⟨ha, hb⟩ := h
      obtain ⟨hp, ha'⟩ := Sigma.mk.inj (LTm.sigma_eq_of_beqR ha)
      cases hp
      cases eq_of_heq ha'
      cases LTm.eq_of_beqR hb
      rfl
    | seq _ => simp only [GFrame.beq, Bool.false_eq_true] at h
  | seq d =>
    cases f' with
    | kite _ _ => simp only [GFrame.beq, Bool.false_eq_true] at h
    | seq d' =>
      simp only [GFrame.beq] at h
      obtain ⟨hs, hd⟩ := Sigma.mk.inj (LTm.sigma_eq_of_beqR h)
      cases hs
      cases eq_of_heq hd
      rfl

/-- `LTm.peel`'s compiled twin. -/
def LTm.peelM : {s : Srt} → LTm C s → List (GFrame C) × LTm C s
  | _, .kite a b t e =>
    if e.isErr then (.kite a b :: t.peelM.1, t.peelM.2) else ([], .kite a b t e)
  | _, .seq d a => (.seq d :: a.peelM.1, a.peelM.2)
  | _, t => ([], t)

/-- **The guards around a term**, outermost first, and the term inside
them.  By the recursor. -/
@[implemented_by LTm.peelM]
def LTm.peel {s : Srt} (t : LTm C s) : List (GFrame C) × LTm C s :=
  @LTm.rec C (fun s _ => List (GFrame C) × LTm C s)
    (@fun _ k => ([], .var k)) (@fun _ o => ([], .app0 o))
    (@fun _ _ o x _ => ([], .app1 o x))
    (@fun _ _ _ o x y _ _ => ([], .app2 o x y))
    (@fun _ _ _ _ o x y z _ _ _ => ([], .app3 o x y z))
    (@fun _ _ _ it q i _ _ => ([], .index it q i))
    (@fun _ q _ => ([], .obsW q)) (@fun _ q _ => ([], .obsL q)) (@fun _ q _ => ([], .obsH q))
    (@fun _ _ d _ _ iha => (.seq d :: iha.1, iha.2))
    (@fun _ a b _ _ => ([], .orElse a b))
    (@fun _ _ a b t e _ _ iht _ =>
      if e.isErr then (.kite a b :: iht.1, iht.2) else ([], .kite a b t e))
    (@fun _ => ([], .err)) s t

theorem LTm.peel_eq_peelM {s : Srt} (t : LTm C s) : t.peel = t.peelM := by
  induction t with
  | kite a b t e _ _ iht _ =>
    show (if e.isErr then (.kite a b :: t.peel.1, t.peel.2) else ([], .kite a b t e)) = _
    rw [iht]; rfl
  | seq d a _ iha =>
    show (GFrame.seq d :: a.peel.1, a.peel.2) = _
    rw [iha]; rfl
  | _ => rfl

/-- The guards `fs` around `t`, each one. -/
def wrapP {s : Srt} (fs : List (GFrame C)) (t : LTm C s) : LTm C s :=
  fs.foldr (fun f a => f.wrap a) t

open Classical in
theorem wrapP_eval {s : Srt} (fs : List (GFrame C)) (t : LTm C s) :
    (wrapP fs t).eval g ν = if ∀ f ∈ fs, f.Holds g ν then t.eval g ν else none := by
  induction fs with
  | nil => simp only [wrapP, List.foldr_nil, List.not_mem_nil, false_implies, implies_true,
      if_true]
  | cons f fs ih =>
    show (f.wrap (wrapP fs t)).eval g ν = _
    rw [GFrame.wrap_eval, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    by_cases hf : f.Holds g ν
    · simp only [hf, true_and, if_true]
    · simp only [hf, false_and, if_false]

/-- A term is its guards around what they guard. -/
theorem LTm.peel_eval {s : Srt} (t : LTm C s) :
    (wrapP t.peel.1 t.peel.2).eval g ν = t.eval g ν := by
  induction t with
  | kite a b t e _ _ iht _ =>
    show (wrapP (if e.isErr then (.kite a b :: t.peel.1, t.peel.2) else ([], .kite a b t e)).1
      (if e.isErr then (.kite a b :: t.peel.1, t.peel.2) else ([], .kite a b t e)).2).eval g ν = _
    cases he : e.isErr
    · rfl
    · simp only [if_true]
      show (LTm.kite a b (wrapP t.peel.1 t.peel.2) .err).eval g ν = _
      rw [LTm.eval_kite, LTm.eval_kite, iht, LTm.eval_of_isErr (g := g) ν he]
      rfl
  | seq d a _ iha =>
    show (LTm.seq d (wrapP a.peel.1 a.peel.2)).eval g ν = _
    rw [LTm.eval_seq, LTm.eval_seq, iha]
  | _ => rfl

/-- A guard a term has at its top fails only where the term halts. -/
theorem LTm.eval_none_of_peel {s : Srt} {t : LTm C s} {f : GFrame C} (hf : f ∈ t.peel.1)
    (h : ¬ f.Holds g ν) : t.eval g ν = none := by
  classical
  rw [← LTm.peel_eval, wrapP_eval, if_neg (fun hall => h (hall f hf))]

/-- **The guards `fs` around `t`**, a guard `t` already has at its top left
out (`GFrame.beq`): `if (c) then (if (c) then t else err) else err` is the
inner one. -/
def wrapG {s : Srt} (fs : List (GFrame C)) (t : LTm C s) : LTm C s :=
  fs.foldr (fun f a => if a.peel.1.any f.beq then a else f.wrap a) t

open Classical in
theorem wrapG_eval {s : Srt} (fs : List (GFrame C)) (t : LTm C s) :
    (wrapG fs t).eval g ν = if ∀ f ∈ fs, f.Holds g ν then t.eval g ν else none := by
  induction fs with
  | nil => simp only [wrapG, List.foldr_nil, List.not_mem_nil, false_implies, implies_true,
      if_true]
  | cons f fs ih =>
    show (if (wrapG fs t).peel.1.any f.beq then wrapG fs t else f.wrap (wrapG fs t)).eval g ν = _
    simp only [List.mem_cons, forall_eq_or_imp]
    split
    · rename_i hany
      obtain ⟨f', hf', hb⟩ := List.any_eq_true.1 hany
      cases GFrame.eq_of_beq hb
      by_cases hf : f.Holds g ν
      · rw [ih]; simp only [hf, true_and]
      · rw [LTm.eval_none_of_peel hf' hf]; simp only [hf, false_and, if_false]
    · rw [GFrame.wrap_eval, ih]
      by_cases hf : f.Holds g ν
      · simp only [hf, true_and, if_true]
      · simp only [hf, false_and, if_false]

/-- A term is its guards around what they guard, each guard once. -/
theorem LTm.peel_evalG {s : Srt} (t : LTm C s) :
    (wrapG t.peel.1 t.peel.2).eval g ν = t.eval g ν := by
  classical
  rw [wrapG_eval]
  exact (wrapP_eval _ _).symm.trans (LTm.peel_eval t)

/-- **A guard goes out through a context that halts where its argument
does** (`F`): `F(if (c) then t else err)` is `if (c) then F(t) else err`. -/
theorem wrapG_out {s s' : Srt} (F : LTm C s → LTm C s')
    (hF : ∀ t₁ t₂ : LTm C s, t₁.eval g ν = t₂.eval g ν → (F t₁).eval g ν = (F t₂).eval g ν)
    (hF0 : (F .err).eval g ν = none) (fs : List (GFrame C)) (t : LTm C s) :
    (F (wrapG fs t)).eval g ν = (wrapG fs (F t)).eval g ν := by
  classical
  rw [wrapG_eval]
  split
  · rename_i h
    exact hF _ _ (by rw [wrapG_eval, if_pos h])
  · rename_i h
    rw [← hF0]
    exact hF _ _ (by rw [wrapG_eval, if_neg h]; rfl)

theorem wrapG_congr {s : Srt} (fs : List (GFrame C)) {t₁ t₂ : LTm C s}
    (h : t₁.eval g ν = t₂.eval g ν) : (wrapG fs t₁).eval g ν = (wrapG fs t₂).eval g ν := by
  classical
  rw [wrapG_eval, wrapG_eval, h]

theorem wrapG_some {s : Srt} {fs : List (GFrame C)} {t : LTm C s} {x : s.Den C g.H}
    (h : (wrapG fs t).eval g ν = some x) : t.eval g ν = some x := by
  classical
  rw [wrapG_eval] at h
  split at h
  · exact h
  · cases h

/-- At a unary symbol: a member's object, its guards out. -/
def _root_.Solidity.Op1.hoistA {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    List (GFrame C) × LTm C s :=
  match o, x with
  | .mfield h, x => (x.peel.1, .app1 (.mfield h) x.peel.2)
  | o, x => ([], .app1 o x)

/-- At a binary symbol: an element's array, its guards out. -/
def _root_.Solidity.Op2.hoistA {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    List (GFrame C) × LTm C s :=
  match o, x, y with
  | .mat ak, x, y => (x.peel.1, .app2 (.mat ak) x.peel.2 y)
  | o, x, y => ([], .app2 o x y)

/-- **An address with its object's guards out**: `(if (c) then o else err).f`
is `if (c) then o.f else err`. -/
def LTm.hoistA {s : Srt} (b : LTm C s) : List (GFrame C) × LTm C s :=
  match b with
  | .app1 o x => o.hoistA x
  | .app2 o x y => o.hoistA x y
  | b => ([], b)

theorem LTm.hoistA_eval {s : Srt} (b : LTm C s) :
    (wrapG b.hoistA.1 b.hoistA.2).eval g ν = b.eval g ν := by
  cases b with
  | app1 o x =>
    cases o
    case mfield h =>
      show (wrapG x.peel.1 (.app1 (.mfield h) x.peel.2)).eval g ν = _
      rw [← wrapG_out (fun t => LTm.app1 (.mfield h) t)
        (fun t₁ t₂ e => by simp only [LTm.eval_app1, e]) rfl]
      simp only [LTm.eval_app1, LTm.peel_evalG]
    all_goals rfl
  | app2 o x y =>
    cases o
    case mat ak =>
      show (wrapG x.peel.1 (.app2 (.mat ak) x.peel.2 y)).eval g ν = _
      rw [← wrapG_out (fun t => LTm.app2 (.mat ak) t y)
        (fun t₁ t₂ e => by simp only [LTm.eval_app2, e]) rfl]
      simp only [LTm.eval_app2, LTm.peel_evalG]
    all_goals rfl
  | _ => rfl

theorem LTm.hoistA_some {s : Srt} {b : LTm C s} {x : s.Den C g.H} (h : b.eval g ν = some x) :
    b.hoistA.2.eval g ν = some x :=
  wrapG_some (by rw [LTm.hoistA_eval]; exact h)

/-- **A symbol that reads its right argument, the argument's guards out**
(a read of memory at an address, a length at an array). -/
theorem LTm.app2_wrapG {a b s : Srt} (o : Op2 C a b s) (ho : o.strictR = true) (x : LTm C a)
    (fs : List (GFrame C)) (y : LTm C b) :
    (LTm.app2 o x (wrapG fs y)).eval g ν = (wrapG fs (.app2 o x y)).eval g ν :=
  wrapG_out (fun t => LTm.app2 o x t) (fun t₁ t₂ e => by simp only [LTm.eval_app2, e])
    (by rw [LTm.eval_app2]; exact Op2.eval_none_right g o ho _) fs y

theorem LTm.app2_hoistA {a b s : Srt} (o : Op2 C a b s) (ho : o.strictR = true) (x : LTm C a)
    (y : LTm C b) :
    (LTm.app2 o x y).eval g ν = (wrapG y.hoistA.1 (.app2 o x y.hoistA.2)).eval g ν := by
  rw [← LTm.app2_wrapG o ho, LTm.eval_app2, LTm.eval_app2, LTm.hoistA_eval]

theorem LTm.app2_peel {a b s : Srt} (o : Op2 C a b s) (ho : o.strictR = true) (x : LTm C a)
    (y : LTm C b) :
    (LTm.app2 o x y).eval g ν = (wrapG y.peel.1 (.app2 o x y.peel.2)).eval g ν := by
  rw [← LTm.app2_wrapG o ho, LTm.eval_app2, LTm.eval_app2, LTm.peel_evalG]

end Guards

end Decide

end Solidity
