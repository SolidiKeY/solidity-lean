import Solidity.Calculus.Closer
import Solidity.Calculus.ElimFacts
import Solidity.Calculus.DecideEval
import Solidity.Calculus.TermLaws
import Solidity.Theory.Typed.MemMirror

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
  **readOnWriteFrame**: an address apart from it reads below
  (`LTm.apart?`: two members, a member and an element, two literal
  indices of one identity).
* **readOnAddMFrame**: an address whose object is older than an
  allocation (`LTm.boundedIn`: allocated on the spine below it, or read out
  of a memory there) reads below it; **readOnAddM** with **initMember**
  and **defaultValueInt**/**defaultValueBool**: an address at a member path
  of the fresh root reads its default.
* **readFromCopyToStorage**: a member of a copy of storage reads the
  storage there, its read eliminated as the storage reads are
  (`LTm.elim`).
* **readFromCopyToStorageIdentity**, and **readFromCopyToStorage** below
  the root (KeY's `idC(idp, fxs)`): an identity member of a copy's object,
  read at the copy, stays that read and holds the storage member
  (`copyObjN`); a word of such an object, or an element of a copied
  storage array (Lean only), reads the storage copied (`copyPathRd?`), and
  the object is fresh over the memory the copy grows (`LTm.copyFresh?`).
  Sound by `Theory/Typed/MemMirror.lean`.

A read whose address's object is guarded (`if (c) then o else err`, `d;
o`: a read walked before it) is read with the guards out (`LTm.hoistA`,
`wrapG`), each guard once; the addresses a write compares are read so too.

Each rewrite is an equation of reads (`LTm.memRes_eval`): it keeps what
the term reads in every state, a halting term halting.
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

section CopyObj

variable {g : State C []} {ν : AEnv}

/-- How deep a read walks down a memory, and a returning check down a term. -/
def memFuel : Nat := 256

/-- At a binary symbol: `sfind(st, q)` taken to `sfind(st, q.f)`. -/
def _root_.Solidity.Op2.sfindFieldStep {s f : Name} {T : Ty} (hf : C.fieldType s f = some T)
    {a b : Srt} (o : Op2 C a b (.sv (.ref (.struct s)))) (x : LTm C a) (y : LTm C b) :
    Option (LTm C (.sv T)) :=
  match o, x, y with
  | .sfind, st, q => some (.app2 .sfind st (.app1 (.field hf) q))
  | _, _, _ => none

/-- `sfind(st, q)` taken to `sfind(st, q.f)`. -/
def LTm.sfindField {s f : Name} {T : Ty} (S : LTm C (.sv (.ref (.struct s))))
    (hf : C.fieldType s f = some T) : Option (LTm C (.sv T)) :=
  match S with
  | .app2 o x y => o.sfindFieldStep hf x y
  | _ => none

theorem LTm.sfindField_eval {s f : Name} {T : Ty} {S : LTm C (.sv (.ref (.struct s)))}
    {hf : C.fieldType s f = some T} {S' : LTm C (.sv T)} (h : S.sfindField hf = some S')
    {v : SVal (.ref (.struct s))} (hv : (S.eval g ν : Option (SVal _)) = some v) :
    (S'.eval g ν : Option (SVal T)) = some ((SVal.view v : SFields _).get hf) := by
  cases S with
  | app2 o x y =>
    cases o <;> simp only [LTm.sfindField, Op2.sfindFieldStep, reduceCtorEq, Option.some.injEq] at h
    subst h
    rw [LTm.eval_app2] at hv ⊢
    rw [LTm.eval_app1]
    cases hx : (x.eval g ν : Option (Storage C)) with
    | none => rw [hx, Op2.eval_none_left] at hv; cases hv
    | some st =>
      cases hy : (y.eval g ν : Option (SRef C _)) with
      | none => rw [hx, hy, Op2.eval_none_right g _ rfl] at hv; cases hv
      | some r =>
        rw [hx, hy] at hv
        change st.find r = some v at hv
        change st.find (r.field hf) = _
        rw [SRef.field, Storage.find_append, hv]
        cases v with
        | struct fs => rfl
  | _ => simp only [LTm.sfindField, reduceCtorEq] at h

/-- At a binary symbol: `sfind(st, q)` taken to the word `find(st, q.f)`. -/
def _root_.Solidity.Op2.findFieldStep {s f : Name} {P : PrimTy} (hf : C.fieldType s f = some (.prim P))
    {a b : Srt} (o : Op2 C a b (.sv (.ref (.struct s)))) (x : LTm C a) (y : LTm C b) :
    Option (LTm C (.val P)) :=
  match o, x, y with
  | .sfind, st, q => some (.app2 .find st (.app1 (.field hf) q))
  | _, _, _ => none

/-- `sfind(st, q)` taken to the word `find(st, q.f)`. -/
def LTm.findField {s f : Name} {P : PrimTy} (S : LTm C (.sv (.ref (.struct s))))
    (hf : C.fieldType s f = some (.prim P)) : Option (LTm C (.val P)) :=
  match S with
  | .app2 o x y => o.findFieldStep hf x y
  | _ => none

theorem LTm.findField_eval {s f : Name} {P : PrimTy} {S : LTm C (.sv (.ref (.struct s)))}
    {hf : C.fieldType s f = some (.prim P)} {y : LTm C (.val P)} (h : S.findField hf = some y)
    {v : SVal (.ref (.struct s))} (hv : (S.eval g ν : Option (SVal _)) = some v) :
    (y.eval g ν : Option P.Denote) = some ((SVal.view v : SFields _).get hf).view := by
  cases S with
  | app2 o x z =>
    cases o <;> simp only [LTm.findField, Op2.findFieldStep, reduceCtorEq, Option.some.injEq] at h
    subst h
    rw [LTm.eval_app2] at hv ⊢
    rw [LTm.eval_app1]
    cases hx : (x.eval g ν : Option (Storage C)) with
    | none => rw [hx, Op2.eval_none_left] at hv; cases hv
    | some st =>
      cases hz : (z.eval g ν : Option (SRef C _)) with
      | none => rw [hx, hz, Op2.eval_none_right g _ rfl] at hv; cases hv
      | some r =>
        rw [hx, hz] at hv
        change st.find r = some v at hv
        change (st.find (r.field hf)).bind (fun w => some w.view) = _
        rw [SRef.field, Storage.find_append, hv]
        cases v with
        | struct fs => rfl
  | _ => simp only [LTm.findField, reduceCtorEq] at h

/-- At a binary symbol: `sfind(st, q)` of an array taken to the word at
`i`, within the stored length. -/
def _root_.Solidity.Op2.findIndexStep {P : PrimTy} (i : LTm C (.val .uint))
    {a b : Srt} (o : Op2 C a b (.sv (.ref (.array (.prim P))))) (x : LTm C a) (y : LTm C b) :
    Option (LTm C (.val P)) :=
  match o, x, y with
  | .sfind, st, q =>
    some (.app3 .ite (.app2 (.binop .lt rfl) i (.app2 .len st q))
      (.app2 .find st (.index (.arr .dyn) q i)) .err)
  | _, _, _ => none

/-- `sfind(st, q)` of an array taken to `if (i < len(st, q)) then
find(st, q[i]) else err`. -/
def LTm.findIndex {P : PrimTy} (S : LTm C (.sv (.ref (.array (.prim P)))))
    (i : LTm C (.val .uint)) : Option (LTm C (.val P)) :=
  match S with
  | .app2 o x y => o.findIndexStep i x y
  | _ => none

theorem LTm.findIndex_eval {P : PrimTy} {S : LTm C (.sv (.ref (.array (.prim P))))}
    {i : LTm C (.val .uint)} {y : LTm C (.val P)} (h : S.findIndex i = some y)
    {n : Nat} {e : SVec (.prim P) n} {sh : SList (.prim P)} {hn : n < 2 ^ 256}
    (hv : (S.eval g ν : Option (SVal _)) = some (.array e sh hn)) :
    (y.eval g ν : Option P.Denote) =
      (i.eval g ν : Option PrimTy.uint.Denote).bind fun k =>
        (e.toList[k.1.toNat]?).map fun x => x.view := by
  cases S with
  | app2 o x z =>
    cases o <;> simp only [LTm.findIndex, Op2.findIndexStep, reduceCtorEq, Option.some.injEq] at h
    subst h
    rw [LTm.eval_app2] at hv
    cases hx : (x.eval g ν : Option (Storage C)) with
    | none => rw [hx, Op2.eval_none_left] at hv; cases hv
    | some st =>
      cases hz : (z.eval g ν : Option (SRef C _)) with
      | none => rw [hx, hz, Op2.eval_none_right g _ rfl] at hv; cases hv
      | some r =>
        rw [hx, hz] at hv
        change st.find r = some (.array e sh hn) at hv
        cases hi : (i.eval g ν : Option PrimTy.uint.Denote) with
        | none =>
          simp only [LTm.eval_app3, LTm.eval_app2, hi]
          rw [Op2.eval_none_left]
          rfl
        | some k =>
          simp only [LTm.eval_app3, LTm.eval_app2, LTm.eval_index, hi, hx, hz]
          have hlen : Op2.eval g Op2.len (some st) (some r) = some (lenU n hn) := by
            show (st.len r) = _
            unfold Storage.len; rw [hv]; rfl
          have hf : Op2.eval g Op2.find (some st) (some (SRef.index r (IndexTy.arr ArrTy.dyn) k)) =
              ((e.toList ++ sh.toList)[k.1.toNat]?).map fun x => x.view := by
            rw [show SRef.index r (IndexTy.arr ArrTy.dyn) k = r.append (.at k .nil) by rw [SRef.index, Path.index_dyn]]
            change (st.find (r.append (.at k .nil))).bind (fun w => some w.view) = _
            rw [Storage.find_append, hv, Option.bind_some]
            try rw [SVal.find_eq_findM]
            simp only [SVal.findM]
            cases (e.toList ++ sh.toList)[k.1.toNat]? <;> rfl
          simp only [Option.bind_some]
          rw [hlen, hf]
          change (bif decide (k.1 < (n : Int)) then _ else none) = _
          have hk := k.2
          simp only [PrimTy.inRange, decide_eq_true_eq] at hk
          by_cases hkn : k.1.toNat < n
          · have hlt : k.1 < (n : Int) := by omega
            have hl : k.1.toNat < e.toList.length := by rw [SVec.length_toList]; exact hkn
            simp only [hlt, decide_true, cond_true, List.getElem?_append_left hl]
          · have hlt : ¬ k.1 < (n : Int) := by omega
            have hl : e.toList.length ≤ k.1.toNat := by rw [SVec.length_toList]; omega
            simp only [hlt, decide_false, cond_false, List.getElem?_eq_none hl, Option.map_none]
  | _ => simp only [LTm.findIndex, reduceCtorEq] at h

/-- `copyObjN`'s step at an identity member: `o.f`, `o` holding
`sfind(st, q)`, holds `sfind(st, q.f)`. -/
def _root_.Solidity.Op1.objField
    (ih : {R : RefTy} → LTm C (.ident R) → Option (LTm C (.sv (.ref R))))
    {a : Srt} {R : RefTy} (o : Op1 C a (.addr (.ref R))) (x : LTm C a) :
    Option (LTm C (.sv (.ref R))) :=
  match o, x with
  | .mfield hf, x => (ih x).bind fun S₁ => S₁.sfindField hf

/-- `copyObjN`'s step at a binary symbol: the copy's root, or an identity
member read at the copy. -/
def _root_.Solidity.Op2.objStep (X m : LTm C .mem) {U : Ty} (S : LTm C (.sv U))
    (ih : {R : RefTy} → LTm C (.ident R) → Option (LTm C (.sv (.ref R))))
    {a b : Srt} {R : RefTy} (o : Op2 C a b (.ident R)) (x : LTm C a) (y : LTm C b) :
    Option (LTm C (.sv (.ref R))) :=
  match o, x, y with
  | .copy _, m', S' => if (m'.beqR m || m'.beqR m.stripW) && S'.beqR S then some S' else none
  | .iread, X', b =>
    if X'.beqR X then
      match b with
      | .app1 o' x' => o'.objField ih x'
      | _ => none
    else none

/-- **What an object of a copy of storage holds, read at the copy**
`X = copySt(m, S)` (`readFromCopyToStorageIdentity`, KeY's
`idC(idp, fxs)`): the root holds `S`; an identity member read at `X` of an
object holding `sfind(st, q)` holds `sfind(st, q.f)`.  By the recursor on
the depth. -/
def copyObjN (X m : LTm C .mem) {U : Ty} (S : LTm C (.sv U)) (n : Nat) :
    {R : RefTy} → LTm C (.ident R) → Option (LTm C (.sv (.ref R))) :=
  Nat.rec (motive := fun _ => {R : RefTy} → LTm C (.ident R) → Option (LTm C (.sv (.ref R))))
    (fun _ => none)
    (fun _ ih {_} o =>
      match o with
      | .app2 op x y => op.objStep X m S ih x y
      | _ => none) n

/-- The copy `copySt(m, S)` read: `m` grown by the copy of `S`. -/
theorem LTm.copySt_eval {m : LTm C .mem} {U : Ty} {hU : U.mapFree = true} {S : LTm C (.sv U)}
    {μ : Grown g.H (fun _ => Unit)} (hm : m.eval g ν = some μ) {v : SVal U}
    (hS : (S.eval g ν : Option (SVal U)) = some v) :
    (LTm.app2 (.copySt hU) m S).eval g ν = some (μ.then (v.copyStToM μ.heap hU)) := by
  rw [LTm.eval_app2, hm, hS]; rfl

theorem copyObjN_eval {m : LTm C .mem} {U : Ty} {hU : U.mapFree = true} {S : LTm C (.sv U)}
    {μ : Grown g.H (fun _ => Unit)} (hm : m.eval g ν = some μ) {v : SVal U}
    (hS : (S.eval g ν : Option (SVal U)) = some v) (n : Nat) :
    ∀ {R : RefTy} (o : LTm C (.ident R)) (S' : LTm C (.sv (.ref R))),
      copyObjN (.app2 (.copySt hU) m S) m S n o = some S' →
      ∃ (r : HRef (v.copyStToM μ.heap hU).H' R) (v' : SVal (.ref R)),
        (o.eval g ν : Option Nat) = some r.id ∧ (S'.eval g ν : Option (SVal (.ref R))) = some v' ∧
        v'.Mirrors (v.copyStToM μ.heap hU).heap μ.H'.length r := by
  induction n with
  | zero => intro R o S' h; cases h
  | succ n ih =>
    intro R o S' h
    cases o with
    | app2 op x y =>
      cases op
      case copy hR =>
        change (if (x.beqR m || x.beqR m.stripW) && y.beqR S then some y else none) = some S' at h
        split at h
        case isFalse => cases h
        case isTrue hc =>
          cases h
          simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
          obtain ⟨hx, hy⟩ := hc
          obtain ⟨hUU, hyS⟩ := Sigma.mk.inj (LTm.sigma_eq_of_beqR hy)
          cases hUU
          cases eq_of_heq hyS
          have hxm : (LTm.app2 (.copy hR) x S').eval g ν = (LTm.app2 (.copy hR) m S').eval g ν := by
            rcases hx with hx | hx
            · rw [LTm.eq_of_beqR hx]
            · rw [LTm.eq_of_beqR hx]; exact LTm.copy_stripW_eval hm hR S'
          refine ⟨(v.copyStToM μ.heap hU).val, v, ?_, hS, SVal.mirrors_copyStToM μ.heap v hU⟩
          rw [hxm, LTm.eval_app2, hm, hS]; rfl
      case iread =>
        change (if x.beqR (LTm.app2 (.copySt hU) m S) then
          (match y with
            | .app1 o' x' => o'.objField (copyObjN (.app2 (.copySt hU) m S) m S n) x'
            | _ => none) else none) = some S' at h
        split at h
        case isFalse => cases h
        case isTrue hx =>
          cases LTm.eq_of_beqR hx
          cases y with
          | app1 o' x' =>
            cases o'
            case mfield s f hf =>
              change ((copyObjN (.app2 (.copySt hU) m S) m S n x').bind
                fun S₁ => S₁.sfindField hf) = some S' at h
              obtain ⟨S₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
              obtain ⟨r₁, v₁, hx', hS₁, hM⟩ := ih x' S₁ h₁
              cases v₁ with
              | struct fs =>
                simp only [SVal.Mirrors] at hM
                refine ⟨(v.copyStToM μ.heap hU).heap.field r₁ hf, fs.get hf, ?_,
                  LTm.sfindField_eval h₂ hS₁, SFields.Mirrors.get fs _ hM.2 hf⟩
                simp only [LTm.iread_evalT, LTm.copySt_eval hm hS, Option.bind_some, LTm.eval_app1,
                  hx', Op1.eval_eq_evalM, Op1.evalM, Option.map_some, MAddrT.resolve_eq_resolveM,
                  MAddrT.resolveM]
                change ((((HRef.ofId? (SVal.copyStToM μ.heap v hU).H' (.struct s) r₁.id).map
                  (fun x => MAddr.field x hf)).bind
                    fun rb => (SVal.copyStToM μ.heap v hU).heap.readAddr rb).bind
                      fun r => some (r : HRef _ R).id) = _
                rw [HRef.ofId?_self (r := r₁)]
                rfl
          | _ => cases h
    | _ => cases h

/-- `copyPathRd?` at a member: the word the member of the object holds. -/
def _root_.Solidity.Op1.copyFieldRd
    (obj : {R : RefTy} → LTm C (.ident R) → Option (LTm C (.sv (.ref R))))
    {a : Srt} {P : PrimTy} (o : Op1 C a (.addr (.prim P))) (x : LTm C a) :
    Option (LTm C (.val P)) :=
  match o, x with
  | .mfield (f := f) hf, x => if f != "length" then (obj x).bind fun S₁ => S₁.findField hf else none

/-- `copyPathRd?` at an element: the word the array holds there, within its
length. -/
def _root_.Solidity.Op2.copyElemRd
    (obj : {R : RefTy} → LTm C (.ident R) → Option (LTm C (.sv (.ref R))))
    {a b : Srt} {P : PrimTy} (o : Op2 C a b (.addr (.prim P))) (x : LTm C a) (y : LTm C b) :
    Option (LTm C (.val P)) :=
  match o, x, y with
  | .mat .dyn, x, i => (obj x).bind fun S₁ => S₁.findIndex i
  | _, _, _ => none

/-- **A word of an object of a copy of storage, read at the copy**
(`readFromCopyToStorage` at `idC(idp, fxs)`, any `fxs`; an element Lean
only): what the storage it copied holds there (`copyObjN`). -/
def copyPathRd? (X m : LTm C .mem) {U : Ty} (S : LTm C (.sv U)) {P : PrimTy}
    (b : LTm C (.addr (.prim P))) : Option (LTm C (.val P)) :=
  match b with
  | .app1 o x => o.copyFieldRd (copyObjN X m S memFuel) x
  | .app2 o x y => o.copyElemRd (copyObjN X m S memFuel) x y
  | _ => none

theorem copyPathRd?_eval {m : LTm C .mem} {U : Ty} {hU : U.mapFree = true} {S : LTm C (.sv U)}
    {P : PrimTy} {b : LTm C (.addr (.prim P))} {y : LTm C (.val P)}
    (h : copyPathRd? (.app2 (.copySt hU) m S) m S b = some y) :
    ((LTm.app2 .read (.app2 (.copySt hU) m S) b).eval g ν : Option P.Denote) =
      (LTm.seq (.app2 (.copySt hU) m S) y).eval g ν := by
  cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none =>
    rw [LTm.eval_app2_none _ _ _ (LTm.eval_app2_none _ _ _ hm), LTm.eval_seq,
      LTm.eval_app2_none _ _ _ hm]; rfl
  | some μ =>
  cases hS : (S.eval g ν : Option (SVal U)) with
  | none =>
    have hX : (LTm.app2 (.copySt hU) m S).eval g ν = none := by
      rw [LTm.eval_app2, hm, hS, Op2.eval_none_right g _ rfl]
    rw [LTm.eval_app2_none _ _ _ hX, LTm.eval_seq, hX]; rfl
  | some v =>
  rw [LTm.eval_seq, LTm.copySt_eval hm hS, Option.bind_some, LTm.read_evalT,
    LTm.copySt_eval hm hS, Option.bind_some]
  cases b with
  | app1 o x =>
    cases o
    case mfield s f hf =>
      change (if f != "length" then (copyObjN _ m S memFuel x).bind fun S₁ => S₁.findField hf
        else none) = some y at h
      split at h
      case isFalse => cases h
      case isTrue =>
        obtain ⟨S₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨r, v₁, hx, hS₁, hM⟩ := copyObjN_eval hm hS memFuel x S₁ h₁
        cases v₁ with
        | struct fs =>
          simp only [SVal.Mirrors] at hM
          rw [LTm.findField_eval h₂ hS₁, LTm.eval_app1, hx]
          change ((((HRef.ofId? (SVal.copyStToM μ.heap v hU).H' (.struct s) r.id).map
            (fun x => MAddr.field x hf)).bind
              fun rb => (SVal.copyStToM μ.heap v hU).heap.readAddr rb)) = _
          rw [HRef.ofId?_self (r := r)]
          change some (MFields.get _ ((v.copyStToM μ.heap hU).heap.get r) hf) = _
          rw [SVal.Mirrors.prim _ _ (SFields.Mirrors.get fs _ hM.2 hf)]
          rfl
  | app2 o x i =>
    cases o
    case mat ak =>
      cases ak
      case dyn =>
        change ((copyObjN _ m S memFuel x).bind fun S₁ => S₁.findIndex i) = some y at h
        obtain ⟨S₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨r, v₁, hx, hS₁, hM⟩ := copyObjN_eval hm hS memFuel x S₁ h₁
        cases v₁ with
        | array e sh hn =>
          simp only [SVal.Mirrors] at hM
          rw [LTm.findIndex_eval h₂ hS₁, LTm.eval_app2, hx]
          cases hi : (i.eval g ν : Option PrimTy.uint.Denote) with
          | none => rfl
          | some k =>
            change ((((HRef.ofId? (SVal.copyStToM μ.heap v hU).H' (.array (.prim P)) r.id).map
              (fun x => MAddr.index x .dyn k)).bind
                fun rb => (SVal.copyStToM μ.heap v hU).heap.readAddr rb)) = _
            rw [HRef.ofId?_self (r := r)]
            change (MObj.elems .dyn ((v.copyStToM μ.heap hU).heap.get r))[k.1.toNat]? = _
            rcases SVec.Mirrors.getElem e _ hM.2 k.1.toNat with ⟨h1, h2⟩ | ⟨x₀, w, h1, h2, h3⟩
            · rw [h2, Option.bind_some, h1]; rfl
            · rw [h2, Option.bind_some, h1, SVal.Mirrors.prim _ _ h3]; rfl
      all_goals cases h
    all_goals cases h
  | _ => cases h

/-- `LTm.copyFresh?` at a binary symbol. -/
def _root_.Solidity.Op2.copyFreshStep {a b : Srt} {R : RefTy} (o : Op2 C a b (.ident R))
    (x : LTm C a) (y : LTm C b) (t : LTm C (.ident R)) : Option (LTm C .mem) :=
  match o, x, y with
  | .iread, X, _ =>
    match X.memView with
    | .copySt m _ S => if (copyObjN X m S memFuel t).isSome then some m else none
    | _ => none
  | _, _, _ => none

/-- **An object a copy made, read at the copy**, is fresh over the memory
the copy grows (`Grown.alloc_fresh`, as the copy's root). -/
def LTm.copyFresh? {R : RefTy} (t : LTm C (.ident R)) : Option (LTm C .mem) :=
  match t with
  | .app2 o x y => o.copyFreshStep x y t
  | _ => none

theorem LTm.copyFresh?_eval {R : RefTy} {t : LTm C (.ident R)} {m : LTm C .mem}
    (h : t.copyFresh? = some m) {id : Nat} (ht : (t.eval g ν : Option Nat) = some id) :
    ∃ μ : Grown g.H (fun _ => Unit), m.eval g ν = some μ ∧ μ.H'.length ≤ id := by
  cases t with
  | app2 o X b =>
    cases o
    case iread =>
      change (match X.memView with
        | .copySt m _ S => if (copyObjN X m S memFuel (.app2 .iread X b)).isSome then some m
          else none
        | _ => none) = some _ at h
      split at h
      case h_1 m' U hU S hX =>
        obtain rfl := LTm.memView_copySt hX
        split at h
        case isFalse => cases h
        case isTrue hc =>
          cases h
          obtain ⟨S', hS'⟩ := Option.isSome_iff_exists.1 hc
          cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
          | none =>
            rw [LTm.eval_app2_none _ _ _ (LTm.eval_app2_none _ _ _ hm)] at ht; cases ht
          | some μ =>
            cases hS : (S.eval g ν : Option (SVal U)) with
            | none =>
              have hX : (LTm.app2 (.copySt hU) m S).eval g ν = none := by
                rw [LTm.eval_app2, hm, hS, Op2.eval_none_right g _ rfl]
              rw [LTm.eval_app2_none _ _ _ hX] at ht; cases ht
            | some v =>
              obtain ⟨r, v', hr, -, hM⟩ := copyObjN_eval hm hS memFuel _ S' hS'
              rw [hr] at ht
              cases ht
              exact ⟨μ, rfl, SVal.Mirrors.id_ge v' r hM⟩
      all_goals cases h
    all_goals cases h
  | _ => cases h

/-- **The memory an identity is fresh over**: an allocation's, a copy's,
an object's of a copy (`LTm.copyFresh?`). -/
def LTm.freshOverC? {R : RefTy} (t : LTm C (.ident R)) : Option (LTm C .mem) :=
  match t.freshOver? with
  | some m => some m
  | none => t.copyFresh?

theorem LTm.freshOverC?_eval {R : RefTy} {t : LTm C (.ident R)} {m : LTm C .mem}
    (h : t.freshOverC? = some m) {id : Nat} (ht : (t.eval g ν : Option Nat) = some id) :
    ∃ μ : Grown g.H (fun _ => Unit), m.eval g ν = some μ ∧ μ.H'.length ≤ id := by
  unfold LTm.freshOverC? at h
  split at h
  · rename_i m' hm
    cases h
    exact LTm.freshOver?_eval hm ht
  · exact LTm.copyFresh?_eval h ht

end CopyObj

section Views

variable {g : State C []} {ν : AEnv}

/-- **Two identities that differ** (`Grown.alloc_fresh`, the freshness behind `newFromAdd`): one fresh over a
memory the other is older than (`LTm.freshOverC?`). -/
def LTm.identApart? {R R' : RefTy} (t : LTm C (.ident R)) (t' : LTm C (.ident R')) : Bool :=
  (match t'.freshOverC? with
    | some m => t.boundedIn m
    | none => false) ||
  (match t.freshOverC? with
    | some m => t'.boundedIn m
    | none => false)

theorem LTm.identApart?_ne {R R' : RefTy} {t : LTm C (.ident R)} {t' : LTm C (.ident R')}
    (h : t.identApart? t' = true) {id id' : Nat} (ht : (t.eval g ν : Option Nat) = some id)
    (ht' : (t'.eval g ν : Option Nat) = some id') : id ≠ id' := by
  unfold LTm.identApart? at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · split at h
    · rename_i m hm
      obtain ⟨μ, hμ, hle⟩ := LTm.freshOverC?_eval hm ht'
      have : id < μ.H'.length := LTm.boundedIn_eval hμ t h id ht
      omega
    · cases h
  · split at h
    · rename_i m hm
      obtain ⟨μ, hμ, hle⟩ := LTm.freshOverC?_eval hm ht
      have : id' < μ.H'.length := LTm.boundedIn_eval hμ t' h id' ht'
      omega
    · cases h

/-- An address term's shape. -/
inductive AddrShapeL (C : Contract) where
  | field (f : Name) (o : (R : RefTy) × LTm C (.ident R))
  | index (i : (R : RefTy) × LTm C (.ident R)) (k : Option PrimTy.uint.Denote)

/-- At a unary symbol. -/
def _root_.Solidity.Op1.addrStepL {a u : Srt} : Op1 C a u → LTm C a → Option (AddrShapeL C)
  | .mfield (f := f) _, x => some (.field f ⟨_, x⟩)
  | _, _ => none

/-- At a binary symbol. -/
def _root_.Solidity.Op2.addrStepL {a b u : Srt} : Op2 C a b u → LTm C a → LTm C b →
    Option (AddrShapeL C)
  | .mat _, x, y => some (.index ⟨_, x⟩ y.uintLit?)
  | _, _, _ => none

/-- An address term's shape.  Generic in the sort. -/
def LTm.addrShape? {u : Srt} : LTm C u → Option (AddrShapeL C)
  | .app1 o x => o.addrStepL x
  | .app2 o x y => o.addrStepL x y
  | _ => none

/-- **Two address terms that never meet** (`readOnWriteFrame`'s side
condition, decided on the terms): two members, a member and an element, or
two elements of one identity at two literal indices; each address with its
object's guards out (`LTm.hoistA`). -/
def LTm.apart? {T U : Ty} (a : LTm C (.addr T)) (b : LTm C (.addr U)) : Bool :=
  match a.hoistA.2.addrShape?, b.hoistA.2.addrShape? with
  | some (.field f o), some (.field g o') => f != g || LTm.identApart? o.2 o'.2
  | some (.field _ _), some (.index _ _) => true
  | some (.index _ _), some (.field _ _) => true
  | some (.index i k), some (.index j k') =>
    (i.2.beqR j.2 && match k, k' with
      | some k, some k' => k != k'
      | _, _ => false) || LTm.identApart? i.2 j.2
  | _, _ => false

/-- What an address term's shape says of the address it reads. -/
def AddrShapeL.Reads (g : State C []) (ν : AEnv) {T : Ty} : AddrShapeL C → MAddrT T → Prop
  | .field f o, ad => ∃ (s : Name) (id : Nat) (h : lookupBy f (structDef s) = some T),
      ad = MAddrT.field id h ∧ (o.2.eval g ν : Option Nat) = some id
  | .index ⟨R, i⟩ k, ad => ∃ (id : Nat) (a : ArrTy R T) (j : PrimTy.uint.Denote),
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
    obtain ⟨id, hid, rfl⟩ := Option.map_eq_some_iff.1 ha
    exact ⟨s, id, hf, rfl, hid⟩
  | app2 o x y =>
    cases o <;> simp only [LTm.addrShape?, Op2.addrStepL, reduceCtorEq, Option.some.injEq] at h
    subst h
    rename_i R arr
    have ha : (((x.eval g ν : Option Nat)).bind fun id =>
        (y.eval g ν : Option PrimTy.uint.Denote).bind fun k => some (MAddrT.index id arr k)) =
      some ad := ha
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at ha
    obtain ⟨id, hi, w, hw, rfl⟩ := ha
    refine ⟨id, arr, w, hi, rfl, fun k' hk => ?_⟩
    have hw' := LTm.uintLit?_eval (g := g) (ν := ν) hk
    rw [hw] at hw'
    exact Option.some.inj hw'
  | _ => simp only [LTm.addrShape?, reduceCtorEq] at h

/-- Two apart address terms resolve, in one heap typing, to apart
addresses. -/
theorem LTm.apart?_resolve {T U : Ty} {a : LTm C (.addr T)} {b : LTm C (.addr U)}
    (h : a.apart? b = true) {ad : MAddrT T} {bd : MAddrT U}
    (ha : (a.eval g ν : Option (MAddrT T)) = some ad)
    (hb : (b.eval g ν : Option (MAddrT U)) = some bd) : ad.Apart bd := by
  have ha := LTm.hoistA_some ha
  have hb := LTm.hoistA_some hb
  unfold LTm.apart? at h
  split at h
  · rename_i f o f' o' hfa hfb
    obtain ⟨s, id, hf, rfl, hid⟩ := LTm.addrShape?_eval hfa ha
    obtain ⟨s', id', hg, rfl, hid'⟩ := LTm.addrShape?_eval hfb hb
    rcases Bool.or_eq_true_iff.1 h with h | h
    · exact .inr (by simpa only [bne_iff_ne, ne_eq] using h)
    · exact .inl (LTm.identApart?_ne h hid hid')
  · rename_i f o i k hfa hfb
    obtain ⟨s, id, hf, rfl, -⟩ := LTm.addrShape?_eval hfa ha
    obtain ⟨id', arr, j, -, rfl, -⟩ := LTm.addrShape?_eval hfb hb
    trivial
  · rename_i i k f o hfa hfb
    obtain ⟨id', arr, j, -, rfl, -⟩ := LTm.addrShape?_eval hfa ha
    obtain ⟨s, id, hf, rfl, -⟩ := LTm.addrShape?_eval hfb hb
    trivial
  · rename_i i k j k' hfa hfb
    obtain ⟨R, i⟩ := i
    obtain ⟨R', j⟩ := j
    obtain ⟨id, arr, n, hi, rfl, hn⟩ := LTm.addrShape?_eval hfa ha
    obtain ⟨id', arr', n', hi', rfl, hn'⟩ := LTm.addrShape?_eval hfb hb
    rcases Bool.or_eq_true_iff.1 h with h | h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨hij, hk⟩ := h
      cases LTm.sigma_eq_of_beqR hij
      rw [hi] at hi'
      cases hi'
      refine .inr ?_
      split at hk
      · rename_i k₁ k₂
        have hk' : k₁ ≠ k₂ := by simpa only [bne_iff_ne, ne_eq] using hk
        exact fun e => hk' ((hn k₁ rfl).symm.trans (e.trans (hn' k₂ rfl)))
      · cases hk
    · exact .inl (LTm.identApart?_ne h hi hi')
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

/-- **readOnWrite** at the address written, its object's guards out
(`LTm.hoistA`): where the write returns, the guards hold. -/
theorem LTm.read_write_hoist {P : PrimTy} (m : LTm C .mem) (a : LTm C (.addr (.prim P)))
    (x : LTm C (.val P)) :
    ((LTm.app2 .read (.app3 .write m a (.app1 .mval x)) a.hoistA.2).eval g ν : Option P.Denote) =
      (LTm.seq (.app3 .write m a (.app1 .mval x)) x).eval g ν := by
  rw [LTm.read_eval_readId, LTm.eval_seq]
  cases hW : ((LTm.app3 .write m a (.app1 .mval x)).eval g ν :
      Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ' =>
    obtain ⟨μ, ad, w, hm, ha, hv, hw⟩ := LTm.write_some hW
    rw [Option.bind_some, LTm.hoistA_some ha, Option.bind_some, (Grown.writeT_facts hw).1]
    have hx : (x.eval g ν : Option P.Denote) = some w := hv
    rw [Option.bind_some, hx]

/-- **readOnWrite** of an identity, its object's guards out. -/
theorem LTm.iread_write_hoist {R : RefTy} (m : LTm C .mem) (a : LTm C (.addr (.ref R)))
    (t : LTm C (.ident R)) :
    ((LTm.app2 .iread (.app3 .write m a (.app1 .ref t)) a.hoistA.2).eval g ν : Option Nat) =
      (LTm.seq (.app3 .write m a (.app1 .ref t)) t).eval g ν := by
  rw [LTm.iread_eval_readId, LTm.eval_seq]
  cases hW : ((LTm.app3 .write m a (.app1 .ref t)).eval g ν :
      Option (Grown g.H (fun _ => Unit))) with
  | none => rfl
  | some μ' =>
    obtain ⟨μ, ad, w, hm, ha, hv, hw⟩ := LTm.write_some hW
    rw [Option.bind_some, LTm.hoistA_some ha, Option.bind_some, (Grown.writeT_facts hw).1]
    have hx : (t.eval g ν : Option Nat) = some w := hv
    rw [Option.bind_some, hx]

/-- **readOnWriteFrame**: an address apart from the one written reads
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

/-- **readOnAddMFrame**: below an allocation, an address whose object is
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
      rw [Grown.read_then_old μ₀ (μ₀.heap.allocDefault R hR) (SVal.keeps_copyStToM _ hR μ₀.heap) bd
        (LTm.boundedIn_eval hm b h bd hb)]
      exact MVal.map_wk_prim _ _

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
      rw [Grown.read_then_old μ₀ (μ₀.heap.allocDefault R hR) (SVal.keeps_copyStToM _ hR μ₀.heap) bd
        (LTm.boundedIn_eval hm b h bd hb)]
      exact MVal.bind_id_map_wk _ _

/-- **readOnAddMFrame** below a copy into memory. -/
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
        rw [Grown.read_then_old μ₀ _ (SVal.keeps_copyStToM v hU μ₀.heap) bd
          (LTm.boundedIn_eval hm b h bd hb)]
        exact MVal.map_wk_prim _ _

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
        rw [Grown.read_then_old μ₀ _ (SVal.keeps_copyStToM v hU μ₀.heap) bd
          (LTm.boundedIn_eval hm b h bd hb)]
        exact MVal.bind_id_map_wk _ _

/-- **readOnAddM**, **initMember**, **defaultValueInt**: below an
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
    have hX : ((LTm.app1 (.addM R hR) m).eval g ν : Option (Grown g.H (fun _ => Unit))) =
        some (μ₀.then (μ₀.heap.allocDefault R hR)) := by
      rw [LTm.eval_app1, Op1.eval_eq_evalM]
      simp only [Op1.evalM, hm, Option.map_some]
    rw [LTm.read_evalT, hX, Option.bind_some]
    exact Srt.FreshRead.read_prim (LTm.freshPath_eval (hR := hR) hm b hp) hT

/-- A member address term, viewed: its object and member. -/
structure FieldV (C : Contract) where
  {s f : Name}
  {T : Ty}
  hf : C.fieldType s f = some T
  t : LTm C (.ident (.struct s))

def _root_.Solidity.Op1.fieldV {a u : Srt} (o : Op1 C a u) (x : LTm C a) : Option (FieldV C) :=
  match o, x with
  | .mfield hf, x => some ⟨hf, x⟩
  | _, _ => none

/-- A member address term's object and member. -/
def LTm.fieldV? {u : Srt} (b : LTm C u) : Option (FieldV C) :=
  match b with
  | .app1 o x => o.fieldV x
  | _ => none

/-- A storage value term read out of storage, viewed: `sfind(st, q)`. -/
structure SFindV (C : Contract) where
  {T : Ty}
  st : LTm C .st
  q : LTm C (.path T)

def _root_.Solidity.Op2.sfindV {a b u : Srt} (o : Op2 C a b u) (x : LTm C a) (y : LTm C b) :
    Option (SFindV C) :=
  match o, x, y with
  | .sfind, x, y => some ⟨x, y⟩
  | _, _, _ => none

/-- A storage value term's storage and path, where it is read out of one. -/
def LTm.sfindV? {u : Srt} (S : LTm C u) : Option (SFindV C) :=
  match S with
  | .app2 o x y => o.sfindV x y
  | _ => none

/-- An identity minted over `m` without its writes, minted over `m` itself
(`LTm.stripW`): how a copy's root reads at the node that copies it. -/
def _root_.Solidity.Op2.unstripId (m : LTm C .mem) {a b s : Srt} (o : Op2 C a b s) (x : LTm C a)
    (y : LTm C b) : LTm C s :=
  match o, x with
  | .copy h, x => if x.beqR m.stripW then .app2 (.copy h) m y else .app2 (.copy h) x y
  | o, x => .app2 o x y

/-- `Op2.unstripId` on a term. -/
def LTm.unstripId {s : Srt} (t : LTm C s) (m : LTm C .mem) : LTm C s :=
  match t with
  | .app2 o x y => o.unstripId m x y
  | t => t

/-- An address with its object's identity read at `m` (`LTm.unstripId`). -/
def _root_.Solidity.Op1.unstripA (m : LTm C .mem) {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    LTm C s :=
  match o with
  | .mfield h => .app1 (.mfield h) (x.unstripId m)
  | o => .app1 o x

/-- At a binary symbol. -/
def _root_.Solidity.Op2.unstripA (m : LTm C .mem) {a b s : Srt} (o : Op2 C a b s) (x : LTm C a)
    (y : LTm C b) : LTm C s :=
  match o with
  | .mat ak => .app2 (.mat ak) (x.unstripId m) y
  | o => .app2 o x y

/-- **An address read at the copy that minted its object**: its identity
over `m` in place of `m` without its writes, so that the copy's laws
(`copyFieldRd?`, `copyNewArrayRd?`) see the root they copy. -/
def LTm.unstripAddr {s : Srt} (b : LTm C s) (m : LTm C .mem) : LTm C s :=
  match b with
  | .app1 o x => o.unstripA m x
  | .app2 o x y => o.unstripA m x y
  | b => b

theorem LTm.unstripId_eval {m : LTm C .mem} {μ : Grown g.H (fun _ => Unit)}
    (hm : m.eval g ν = some μ) {s : Srt} (t : LTm C s) :
    (t.unstripId m).eval g ν = t.eval g ν := by
  cases t with
  | app2 o x y =>
    cases o
    case copy =>
      show (if x.beqR m.stripW then _ else _ : LTm C _).eval g ν = _
      split
      · rename_i hx
        obtain rfl := LTm.eq_of_beqR hx
        exact (LTm.copy_stripW_eval hm _ y).symm
      · rfl
    all_goals rfl
  | _ => rfl

theorem LTm.unstripAddr_eval {m : LTm C .mem} {μ : Grown g.H (fun _ => Unit)}
    (hm : m.eval g ν = some μ) {s : Srt} (b : LTm C s) :
    (b.unstripAddr m).eval g ν = b.eval g ν := by
  cases b with
  | app1 o x =>
    cases o
    case mfield =>
      show (LTm.app1 _ (x.unstripId m)).eval g ν = _
      rw [LTm.eval_app1, LTm.eval_app1, LTm.unstripId_eval hm]
    all_goals rfl
  | app2 o x y =>
    cases o
    case mat =>
      show (LTm.app2 _ (x.unstripId m) y).eval g ν = _
      rw [LTm.eval_app2, LTm.eval_app2, LTm.unstripId_eval hm]
    all_goals rfl
  | _ => rfl

/-- A read at the node `copySt(m, S)`, its address read there
(`LTm.unstripAddr`). -/
theorem LTm.read_unstrip {P : PrimTy} {U : Ty} (m : LTm C .mem) (hU : U.mapFree = true)
    (S : LTm C (.sv U)) (b : LTm C (.addr (.prim P))) :
    (LTm.app2 .read (.app2 (.copySt hU) m S) (b.unstripAddr m)).eval g ν =
      (LTm.app2 .read (.app2 (.copySt hU) m S) b).eval g ν := by
  cases hm : (m.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none =>
    rw [LTm.eval_app2_none _ _ _ (LTm.eval_app2_none _ _ _ hm),
      LTm.eval_app2_none _ _ _ (LTm.eval_app2_none _ _ _ hm)]
  | some μ => simp only [LTm.eval_app2, LTm.unstripAddr_eval hm]

/-- **A member of a copy of storage, read** (`readFromCopyToStorage`): the
word at the member of the copy's root, as the storage it copied holds it
there. -/
def copyFieldRd? (m : LTm C .mem) {U : Ty} (S : LTm C (.sv U)) {P : PrimTy}
    (b : LTm C (.addr (.prim P))) : Option (LTm C (.val P)) :=
  match b.fieldV? with
  | some fv =>
    match fv.t.identView with
    | .copy m' _ S' =>
      if m'.beqR m && S'.beqR S && fv.f != "length" then
        match S.sfindV? with
        | some ⟨st, q⟩ =>
          (q.castTo? (s' := .path (.ref (.struct fv.s)))).bind fun q' =>
            ((LTm.app1 (.field fv.hf) q').castTo? (s' := .path (.prim P))).map fun q'' =>
              .app2 .find st q''
        | none => none
      else none
    | _ => none
  | none => none

theorem copyFieldRd?_eval {m : LTm C .mem} {U : Ty} {hU : U.mapFree = true} {S : LTm C (.sv U)}
    {P : PrimTy} {b : LTm C (.addr (.prim P))} {y : LTm C (.val P)} (h : copyFieldRd? m S b = some y) :
    ((LTm.app2 .read (.app2 (.copySt hU) m S) b).eval g ν : Option P.Denote) =
      (LTm.seq (.app2 (.copySt hU) m S) y).eval g ν := by
  unfold copyFieldRd? at h
  split at h
  · rename_i fv hfv
    split at h
    · rename_i m' U' hU' S' ht
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
        obtain ⟨⟨hm, hS⟩, hl⟩ := hc
        split at h
        · rename_i T' st q hsf
          obtain ⟨q', hq', h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨q'', hq'', rfl⟩ := Option.map_eq_some_iff.1 h
          cases b with
          | app1 o x =>
            cases o <;> simp only [LTm.fieldV?, Op1.fieldV, reduceCtorEq, Option.some.injEq] at hfv
            subst hfv
            rename_i s f hf
            obtain ⟨-, hq2⟩ := Sigma.mk.inj (LTm.castTo?_eq hq'')
            cases eq_of_heq hq2
            obtain ⟨hT, hq1⟩ := Sigma.mk.inj (LTm.castTo?_eq hq')
            cases hT
            cases eq_of_heq hq1
            cases LTm.sigma_eq_of_beqR hm
            obtain ⟨hUU, hSS⟩ := Sigma.mk.inj (LTm.sigma_eq_of_beqR hS)
            cases hUU
            cases eq_of_heq hSS
            cases x with
            | app2 o xm xS =>
              cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq, IdentV.copy.injEq] at ht
              obtain ⟨rfl, hR, hxS⟩ := ht
              cases hR
              cases eq_of_heq hxS
              cases xS with
              | app2 o st' q0 =>
                cases o <;> simp only [LTm.sfindV?, Op2.sfindV, reduceCtorEq, Option.some.injEq,
                  SFindV.mk.injEq] at hsf
                obtain ⟨-, hst', hq0⟩ := hsf
                subst st
                cases eq_of_heq hq0
                have ev : ((LTm.app2 .sfind st' q0).eval g ν : Option (SVal _)) =
                    (st'.eval g ν : Option (Storage C)).bind fun st₀ =>
                      (q0.eval g ν : Option (SRef C _)).bind fun r₀ => st₀.find r₀ := by
                  rw [LTm.eval_app2]
                  cases (st'.eval g ν : Option (Storage C)) <;>
                    cases (q0.eval g ν : Option (SRef C _)) <;> rfl
                rw [LTm.read_evalT, LTm.eval_seq, LTm.eval_app2 g ν (Op2.copySt hU), Op2.eval_eq_evalM]
                cases hxm : (xm.eval g ν : Option (Grown g.H (fun _ => Unit))) with
                | none => rfl
                | some μ₀ =>
                  cases hv : ((LTm.app2 .sfind st' q0).eval g ν : Option (SVal _)) with
                  | none => rfl
                  | some v =>
                    rw [ev] at hv
                    simp only [Option.bind_eq_some_iff] at hv
                    obtain ⟨st₀, hst, r₀, hr₀, hfv⟩ := hv
                    rename_i hcp
                    have hv2 : ((LTm.app2 .sfind st' q0).eval g ν : Option (SVal _)) = some v := by
                      rw [ev, hst, Option.bind_some, hr₀, Option.bind_some, hfv]
                    have hb : ((LTm.app1 (Op1.mfield f) (LTm.app2 (Op2.copy hcp) xm
                        (LTm.app2 Op2.sfind st' q0))).eval g ν : Option (MAddrT _)) =
                        some (MAddrT.field (v.copyStToM μ₀.heap hcp).val.id f) := by
                      rw [LTm.eval_app1, LTm.eval_app2, hxm, hv2]; rfl
                    rw [show Op2.evalM g (Op2.copySt hU) (some μ₀) (some v) =
                      some (μ₀.then (v.copyStToM μ₀.heap hU)) from rfl, Option.bind_some,
                      Option.bind_some, hb, Option.bind_some]
                    show ((MAddrT.field (SVal.copyStToM μ₀.heap v hU).val.id f).resolve
                      (SVal.copyStToM μ₀.heap v hU).H').bind
                      (fun rb => (SVal.copyStToM μ₀.heap v hU).heap.readAddr rb) = _
                    rw [MAddrT.resolve_eq_resolveM]
                    simp only [MAddrT.resolveM]
                    rw [HRef.ofId?_self (r := ((SVal.copyStToM μ₀.heap v hU).val : HRef _ _))]
                    simp only [Option.map_some, Option.bind_some]
                    show some ((SVal.copyStToM μ₀.heap v hU).heap.field
                      (SVal.copyStToM μ₀.heap v hU).val f) = _
                    rw [SVal.copyStToM_field μ₀.heap v hU f, LTm.eval_app2, hst, LTm.eval_app1, hr₀]
                    show _ = (st₀.find (r₀.field f)).bind fun w => some w.view
                    rw [SRef.field, Storage.find_append, hfv]
                    cases v with
                    | struct fs => rfl
              | _ => simp only [LTm.sfindV?, reduceCtorEq] at hsf
            | app1 o xm => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht
            | _ => simp only [LTm.identView, reduceCtorEq] at ht
          | _ => simp only [LTm.fieldV?, reduceCtorEq] at hfv
        · cases h
      · cases h
    · cases h
  · cases h

end Laws

/-! ## The length of an array, walked down its memory -/

section Len

variable {g : State C []} {ν : AEnv}

/-- `new T[](n)`'s `n`, where a storage value term is one. -/
def _root_.Solidity.Op1.newArrArg {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    Option (LTm C (.val .uint)) :=
  match o, x with
  | .newArr _, x => some x
  | _, _ => none

def LTm.newArrLen? {U : Ty} (S : LTm C (.sv U)) : Option (LTm C (.val .uint)) :=
  match S with
  | .app1 o x => o.newArrArg x
  | _ => none

/-- `len(s, p)` of `sfind(s, p)` at an array path (Lean only): the length a
copy of the stored array keeps. -/
def _root_.Solidity.Op2.sfindLen {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    Option (LTm C (.val .uint)) :=
  match o, x, y with
  | @Op2.sfind _ (.ref (.array _)), x, y => some (.app2 .len x y)
  | _, _, _ => none

def LTm.sfindLen? {U : Ty} (S : LTm C (.sv U)) : Option (LTm C (.val .uint)) :=
  match S with
  | .app2 o x y => o.sfindLen x y
  | _ => none

/-- **An array's length, walked down a memory that returns**: a write keeps every length, an allocation and a copy
every older array's; a fresh dynamic array's is `0`, a copy of
`new T[](n)`'s is `n`, a copy of a stored array's its stored length
(`len(s, p)`, Lean only: solkey copies no storage array to memory).  By the recursor on the depth. -/
def lenAtN (n : Nat) : {E : Ty} → LTm C .mem → LTm C (.ident (.array E)) → LTm C (.val .uint) :=
  Nat.rec (motive := fun _ => {E : Ty} → LTm C .mem → LTm C (.ident (.array E)) →
      LTm C (.val .uint))
    (fun X t => .app2 .mlen X t)
    (fun _ ih {_} X t =>
      match X.memView with
      | .write m _ _ => ih m t
      | .addM m R _ =>
        if t.boundedIn m then ih m t
        else
          match t.identView with
          | .alloc m' R' _ => if m'.beqR m && R' == R then .nat 0 else .app2 .mlen X t
          | _ => .app2 .mlen X t
      | .copySt m _ S =>
        if t.boundedIn m then ih m t
        else
          match t.identView with
          | .copy m' _ S' =>
            if (m'.beqR m || m'.beqR m.stripW) && S'.beqR S then
              match S'.newArrLen? with
              | some x => x
              | none =>
                match S'.sfindLen? with
                | some x => x
                | none => .app2 .mlen X t
            else .app2 .mlen X t
          | _ => .app2 .mlen X t
      | .other => .app2 .mlen X t) n

theorem lenAtN_eval (n : Nat) : ∀ {E : Ty} (X : LTm C .mem) (t : LTm C (.ident (.array E)))
    (μ : Grown g.H (fun _ => Unit)), X.eval g ν = some μ →
    ((lenAtN n X t).eval g ν : Option PrimTy.uint.Denote) = (LTm.app2 .mlen X t).eval g ν := by
  induction n with
  | zero => intro E X t μ _; rfl
  | succ n ih =>
    intro E X t μ hX
    show (match X.memView with
      | .write m _ _ => lenAtN n m t
      | .addM m R _ =>
        if t.boundedIn m then lenAtN n m t
        else
          match t.identView with
          | .alloc m' R' _ => if m'.beqR m && R' == R then .nat 0 else .app2 .mlen X t
          | _ => .app2 .mlen X t
      | .copySt m _ S =>
        if t.boundedIn m then lenAtN n m t
        else
          match t.identView with
          | .copy m' _ S' =>
            if (m'.beqR m || m'.beqR m.stripW) && S'.beqR S then
              match S'.newArrLen? with
              | some x => x
              | none =>
                match S'.sfindLen? with
                | some x => x
                | none => .app2 .mlen X t
            else .app2 .mlen X t
          | _ => .app2 .mlen X t
      | .other => .app2 .mlen X t : LTm C (.val .uint)).eval g ν = _
    split
    · rename_i m T a v hM
      obtain rfl := LTm.memView_write hM
      obtain ⟨μ₀, ad, w, hm, -, -, hw⟩ := LTm.write_some hX
      rw [ih m t μ₀ hm, LTm.mlen_evalT, LTm.mlen_evalT, hm, hX, Option.bind_some, Option.bind_some]
      cases (t.eval g ν : Option Nat) with
      | none => rfl
      | some id => exact (Grown.writeT_lenU hw id).symm
    · rename_i m R hR hM
      obtain rfl := LTm.memView_addM hM
      have hX' := hX
      rw [LTm.eval_app1, Op1.eval_eq_evalM] at hX'
      simp only [Op1.evalM, Option.map_eq_some_iff] at hX'
      obtain ⟨μ₀, hm, rfl⟩ := hX'
      split
      · rename_i hb
        rw [ih m t μ₀ hm, LTm.mlen_evalT, LTm.mlen_evalT, hm, hX, Option.bind_some, Option.bind_some]
        cases ht : (t.eval g ν : Option Nat) with
        | none => rfl
        | some id =>
          exact (Grown.lenU_addM_old μ₀ R hR id (LTm.boundedIn_eval hm t hb id ht)).symm
      · split
        · rename_i m' R' hR' ht
          split
          · rename_i hc
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            obtain ⟨hmm, rfl⟩ := hc
            cases LTm.sigma_eq_of_beqR hmm
            cases t with
            | app1 o x =>
              cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq, IdentV.alloc.injEq] at ht
              obtain ⟨rfl, -, -⟩ := ht
              rw [LTm.mlen_evalT, hX, Option.bind_some, LTm.eval_app1, hm, Op1.eval_eq_evalM]
              simp only [Op1.evalM, Option.map_some, Option.bind_some]
              show some (uintOfNat 0) = Option.map (fun r => (μ₀.heap.allocDefault _ hR).heap.lenU r)
                (HRef.ofId? (μ₀.heap.allocDefault _ hR).H' _ (μ₀.heap.allocDefault _ hR).val.id)
              rw [HRef.ofId?_self (r := ((μ₀.heap.allocDefault _ hR).val : HRef _ _)), Option.map_some]
              refine congrArg some (Subtype.ext ?_)
              rw [uintOfNat_val (by decide)]
              show (0 : Int) = ((μ₀.heap.allocDefault _ hR).heap.len (μ₀.heap.allocDefault _ hR).val .dyn : Int)
              rw [Heap.allocDefault_array_len]; rfl
            | app2 o x y => cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq] at ht
            | _ => simp only [LTm.identView, reduceCtorEq] at ht
          · rfl
        · rfl
    · rename_i m U hU S hM
      obtain rfl := LTm.memView_copySt hM
      have hX' := hX
      rw [LTm.eval_app2, Op2.eval_eq_evalM] at hX'
      simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hX'
      obtain ⟨μ₀, hm, v, hv, rfl⟩ := hX'
      split
      · rename_i hb
        rw [ih m t μ₀ hm, LTm.mlen_evalT, LTm.mlen_evalT, hm, hX, Option.bind_some, Option.bind_some]
        cases ht : (t.eval g ν : Option Nat) with
        | none => rfl
        | some id =>
          exact (Grown.lenU_copySt_old μ₀ v hU id (LTm.boundedIn_eval hm t hb id ht)).symm
      · split
        · rename_i m' U' hU' S' ht
          split
          · rename_i hc
            split
            · rename_i x hx
              simp only [Bool.and_eq_true] at hc
              obtain ⟨hmm, hSS⟩ := hc
              obtain ⟨μ₁, h₁, e₁⟩ := LTm.base_eval hmm hm
              obtain ⟨hUU, hS⟩ := Sigma.mk.inj (LTm.sigma_eq_of_beqR hSS)
              cases hUU
              cases eq_of_heq hS
              cases t with
              | app2 o x' y' =>
                cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq, IdentV.copy.injEq] at ht
                obtain ⟨rfl, rfl, hy⟩ := ht
                cases eq_of_heq hy
                cases y' with
                | app1 o z =>
                  cases o <;> simp only [LTm.newArrLen?, Op1.newArrArg, reduceCtorEq,
                    Option.some.injEq] at hx
                  subst hx
                  have hv' := hv
                  rw [LTm.eval_app1, Op1.eval_eq_evalM] at hv'
                  simp only [Op1.evalM, Option.map_eq_some_iff] at hv'
                  obtain ⟨k, hk, rfl⟩ := hv'
                  rw [hk, LTm.mlen_evalT, hX, Option.bind_some, LTm.eval_app2, h₁, hv,
                    Op2.eval_eq_evalM]
                  show some k = Option.map
                    (fun r => (SVal.copyStToM μ₀.heap (newArrT (RefTy.array E) k _) hU).heap.lenU r)
                    (HRef.ofId? (SVal.copyStToM μ₀.heap (newArrT (RefTy.array E) k _) hU).H' _
                      (SVal.copyStToM μ₁.heap (newArrT (RefTy.array E) k _) hU).val.id)
                  rw [SVal.copyStToM_id_eq _ hU μ₁.heap μ₀.heap e₁]
                  rw [HRef.ofId?_self (r := ((SVal.copyStToM μ₀.heap (newArrT (RefTy.array E) k _)
                    hU).val : HRef _ _)), Option.map_some]
                  refine congrArg some (Subtype.ext ?_)
                  show k.1 = ((SVal.copyStToM μ₀.heap (newArrT (RefTy.array E) k _) hU).heap.len
                    (SVal.copyStToM μ₀.heap (newArrT (RefTy.array E) k _) hU).val .dyn : Int)
                  rw [newArrT_copy_len]
                  have := k.2
                  simp only [PrimTy.inRange, decide_eq_true_eq] at this
                  omega
                | _ => simp only [LTm.newArrLen?, reduceCtorEq] at hx
              | app1 o x' => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht
              | _ => simp only [LTm.identView, reduceCtorEq] at ht
            · split
              · rename_i x _ hx
                simp only [Bool.and_eq_true] at hc
                obtain ⟨hmm, hSS⟩ := hc
                obtain ⟨μ₁, h₁, e₁⟩ := LTm.base_eval hmm hm
                obtain ⟨hUU, hS⟩ := Sigma.mk.inj (LTm.sigma_eq_of_beqR hSS)
                cases hUU
                cases eq_of_heq hS
                cases t with
                | app2 o x' y' =>
                  cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq,
                    IdentV.copy.injEq] at ht
                  obtain ⟨rfl, rfl, hy⟩ := ht
                  cases eq_of_heq hy
                  cases y' with
                  | app2 o st q =>
                    cases o <;> simp only [LTm.sfindLen?, Op2.sfindLen, reduceCtorEq,
                      Option.some.injEq] at hx
                    subst hx
                    have hv' := hv
                    rw [LTm.eval_app2, Op2.eval_eq_evalM] at hv'
                    simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv'
                    obtain ⟨s₀, hs₀, r₀, hr₀, hf⟩ := hv'
                    have hlen : ((LTm.app2 Op2.len st q).eval g ν : Option PrimTy.uint.Denote) =
                        Storage.len s₀ r₀ := by
                      rw [LTm.eval_app2, Op2.eval_eq_evalM, hs₀, hr₀]; rfl
                    rw [hlen, LTm.mlen_evalT, hX, Option.bind_some, LTm.eval_app2, h₁, hv,
                      Op2.eval_eq_evalM]
                    show (Storage.len s₀ r₀ : Option PrimTy.uint.Denote) = Option.map
                      (fun r => (SVal.copyStToM μ₀.heap v hU).heap.lenU r)
                      (HRef.ofId? (SVal.copyStToM μ₀.heap v hU).H' _
                        (SVal.copyStToM μ₁.heap v hU).val.id)
                    rw [SVal.copyStToM_id_eq v hU μ₁.heap μ₀.heap e₁]
                    rw [HRef.ofId?_self (r := ((SVal.copyStToM μ₀.heap v hU).val : HRef _ _)),
                      Option.map_some]
                    unfold Storage.len
                    rw [hf]
                    show some (Solidity.lenU (SVal.view v : ArrView _).n (SVal.view v : ArrView _).hn) = _
                    refine congrArg some (Subtype.ext ?_)
                    show ((SVal.view v : ArrView _).n : Int) =
                      ((SVal.copyStToM μ₀.heap v hU).heap.len (SVal.copyStToM μ₀.heap v hU).val
                        .dyn : Int)
                    rw [SVal.copyStToM_array_len]
                  | _ => simp only [LTm.sfindLen?, reduceCtorEq] at hx
                | app1 o x' => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht
                | _ => simp only [LTm.identView, reduceCtorEq] at ht
              · rfl
          · rfl
        · rfl
    · rfl

end Len

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


/-- `LTm.onSpine_eval` up to writes. -/
theorem LTm.onSpineS_eval {M W : LTm C .mem} (h : M.onSpineS W = true)
    {μ : Grown g.H (fun _ => Unit)} (hM : M.eval g ν = some μ) :
    ∃ ω, W.eval g ν = some ω ∧ ω.H' <+: μ.H' := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact LTm.onSpine_eval h hM
  · obtain ⟨μ₁, h₁, e₁⟩ := LTm.stripW_eval hM
    obtain ⟨ω, hω, hext⟩ := LTm.onSpine_eval (Bool.and_eq_true_iff.1 h).2 h₁
    exact ⟨ω, hω, e₁ ▸ hext⟩
/-- A question of returning, about a memory: whether it returns; whether an
identity is an object of its type in it; whether an address resolves and
reads there. -/
inductive MemQ (C : Contract) where
  | mem (M : LTm C .mem)
  | ident {R : RefTy} (t : LTm C (.ident R)) (M : LTm C .mem)
  | addr {T : Ty} (a : LTm C (.addr T)) (M : LTm C .mem)

/-- Every word of `cs` is `true`. -/
def AllT (g : State C []) (ν : AEnv) (cs : List (LTm C (.val .bool))) : Prop :=
  ∀ c ∈ cs, (c.eval g ν : Option Bool) = some true

theorem AllT.append {cs ds : List (LTm C (.val .bool))} :
    AllT g ν (cs ++ ds) ↔ AllT g ν cs ∧ AllT g ν ds :=
  ⟨fun h => ⟨fun c hc => h c (List.mem_append_left _ hc),
      fun c hc => h c (List.mem_append_right _ hc)⟩,
    fun ⟨h₁, h₂⟩ c hc => (List.mem_append.1 hc).elim (h₁ c) (h₂ c)⟩

theorem AllT.nil : AllT g ν ([] : List (LTm C (.val .bool))) := fun _ h => nomatch h

theorem AllT.single {c : LTm C (.val .bool)} :
    AllT g ν [c] ↔ (c.eval g ν : Option Bool) = some true := by
  constructor
  · intro h; exact h c (List.mem_singleton_self c)
  · intro h c' hc; rw [List.mem_singleton.1 hc]; exact h

/-- `(t; true)`: `true` where `t` returns. -/
def LTm.retsC {s : Srt} (t : LTm C s) : LTm C (.val .bool) := .seq t .tt

theorem LTm.retsC_true {s : Srt} (t : LTm C s) :
    AllT g ν [t.retsC] ↔ (t.eval g ν).isSome = true := by
  rw [AllT.single, LTm.retsC, LTm.eval_seq]
  cases t.eval g ν with
  | none => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | some _ => exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- The word a guard comes to: `c` of `if (c) then · else err`, `d`
returning of `d; ·`. -/
def GFrame.cond? : GFrame C → Option (LTm C (.val .bool))
  | .kite (p := .bool) c b => if b.isTT then some c else none
  | .kite _ _ => none
  | .seq d => some d.retsC

theorem GFrame.cond?_iff {f : GFrame C} {c : LTm C (.val .bool)} (h : f.cond? = some c) :
    f.Holds g ν ↔ (c.eval g ν : Option Bool) = some true := by
  cases f with
  | kite a b =>
    rename_i p
    cases p with
    | bool =>
      simp only [GFrame.cond?] at h
      split at h
      · rename_i hb
        cases h
        have hb' := LTm.isTT_eval (g := g) (ν := ν) hb
        constructor
        · rintro ⟨x, hx, hy⟩
          rw [hb'] at hy
          cases hy
          exact hx
        · intro hc
          exact ⟨true, hc, hb'⟩
      · cases h
    | uint | int => simp only [GFrame.cond?, reduceCtorEq] at h
  | seq d =>
    simp only [GFrame.cond?, Option.some.injEq] at h
    subst h
    rw [← AllT.single, LTm.retsC_true]
    rfl

/-- The words the guards `fs` come to. -/
def framesCond? (fs : List (GFrame C)) : Option (List (LTm C (.val .bool))) :=
  fs.mapM GFrame.cond?

theorem framesCond?_iff : (fs : List (GFrame C)) → {cs : List (LTm C (.val .bool))} →
    framesCond? fs = some cs → ((∀ f ∈ fs, f.Holds g ν) ↔ AllT g ν cs)
  | [], cs, h => by
    simp only [framesCond?, List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨fun _ => AllT.nil, fun _ f hf => nomatch hf⟩
  | f :: fs, cs, h => by
    simp only [framesCond?, List.mapM_cons, bind, pure, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨c, hc, cs', hcs', rfl⟩ := h
    have H := framesCond?_iff fs hcs'
    rw [show c :: cs' = [c] ++ cs' from rfl, AllT.append, AllT.single, ← GFrame.cond?_iff hc, ← H]
    simp only [List.mem_cons, forall_eq_or_imp]

open Classical in
/-- A guarded term returns where its guards hold and what they guard returns. -/
theorem LTm.eval_peel {s : Srt} (t : LTm C s) :
    t.eval g ν = if ∀ f ∈ t.peel.1, f.Holds g ν then t.peel.2.eval g ν else none := by
  classical
  rw [← LTm.peel_eval, wrapP_eval]

/-- **What a question's words say**: a memory returns exactly where they
are `true`; where the memory returns, an identity is an object of its type
there, and an address resolves and reads, where they are, and they are
where the identity or the address returns so. -/
def MemQ.HoldsC (g : State C []) (ν : AEnv) : MemQ C → List (LTm C (.val .bool)) → Prop
  | .mem M, cs => (M.eval g ν : Option (Grown g.H (fun _ => Unit))).isSome = true ↔ AllT g ν cs
  | @MemQ.ident _ R t M, cs => ∀ μ, (M.eval g ν : Option (Grown g.H (fun _ => Unit))) = some μ →
      (AllT g ν cs → ∃ id, (t.eval g ν : Option Nat) = some id ∧ μ.H'[id]? = some R) ∧
      ((t.eval g ν : Option Nat).isSome = true → AllT g ν cs)
  | @MemQ.addr _ T a M, cs => ∀ μ, (M.eval g ν : Option (Grown g.H (fun _ => Unit))) = some μ →
      (AllT g ν cs → ∃ ad ra, (a.eval g ν : Option (MAddrT T)) = some ad ∧
        ad.resolve μ.H' = some ra ∧ (μ.heap.readAddr ra).isSome = true) ∧
      (∀ ad ra, (a.eval g ν : Option (MAddrT T)) = some ad → ad.resolve μ.H' = some ra →
        (μ.heap.readAddr ra).isSome = true → AllT g ν cs)

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

/-- An address term's array, its kind and the index, where it is an
element. -/
def _root_.Solidity.Op2.matObj {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    Option ((R : RefTy) × (E : Ty) × ArrTy R E × LTm C (.ident R) × LTm C (.val .uint)) :=
  match o, x, y with
  | .mat arr, x, y => some ⟨_, _, arr, x, y⟩
  | _, _, _ => none

/-- An element address's array and index. -/
def LTm.matObj? {s : Srt} (a : LTm C s) :
    Option ((R : RefTy) × (E : Ty) × ArrTy R E × LTm C (.ident R) × LTm C (.val .uint)) :=
  match a with
  | .app2 o x y => o.matObj x y
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

theorem retsS_isSome {s : Srt} {t : LTm C s} (h : t.retsS = true) :
    (t.eval g ν).isSome = true := by
  obtain ⟨v, hv⟩ := LTm.retsS_eval (g := g) (ν := ν) h
  rw [hv]; rfl

/-- The words a copy's source returns at: none for a fresh array of a
length that returns. -/
def svConds {U : Ty} (S : LTm C (.sv U)) : List (LTm C (.val .bool)) :=
  match S with
  | .app1 o x => if o.svOk x then [] else [S.retsC]
  | _ => [S.retsC]

theorem svConds_iff {U : Ty} (S : LTm C (.sv U)) :
    (S.eval g ν : Option (SVal U)).isSome = true ↔ AllT g ν (svConds S) := by
  cases S with
  | app1 o x =>
    show _ ↔ AllT g ν (if o.svOk x then [] else [(LTm.app1 o x).retsC])
    split
    · rename_i hok
      refine ⟨fun _ => AllT.nil, fun _ => ?_⟩
      cases o <;> simp only [Op1.svOk, Bool.false_eq_true] at hok
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (retsS_isSome (g := g) (ν := ν) hok)
      rw [LTm.eval_app1, hw]; rfl
    · exact (LTm.retsC_true _).symm
  | _ => exact (LTm.retsC_true _).symm

/-- **An index within an array's bounds** (`memoryIndexInBounds`), in a
memory that returns: below its length walked down the memory (`lenAtN`),
or below a fixed array's. -/
def lenCond {R : RefTy} {E : Ty} (arr : ArrTy R E) (M : LTm C .mem) (t : LTm C (.ident R))
    (i : LTm C (.val .uint)) : LTm C (.val .bool) :=
  match R, arr, t with
  | _, .dyn, t => .lt i (lenAtN memFuel M t)
  | _, @ArrTy.fixed _ n, _ => if n < 2 ^ 256 then .lt i (.nat n) else i.retsC

theorem lenCond_iff {R : RefTy} {E : Ty} (arr : ArrTy R E) (M : LTm C .mem)
    (t : LTm C (.ident R)) (i : LTm C (.val .uint)) {μ : Grown g.H (fun _ => Unit)}
    (hM : M.eval g ν = some μ) {id : Nat} (ht : (t.eval g ν : Option Nat) = some id)
    {r : HRef μ.H' R} (hr : HRef.ofId? μ.H' R id = some r) :
    ((lenCond arr M t i).eval g ν : Option Bool) = some true ↔
      ∃ k : PrimTy.uint.Denote, (i.eval g ν : Option _) = some k ∧ k.1.toNat < μ.heap.len r arr := by
  have k0 : ∀ k : PrimTy.uint.Denote, 0 ≤ k.1 := fun k => by
    have := k.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at this
    omega
  have klt : ∀ k : PrimTy.uint.Denote, k.1 < 2 ^ 256 := fun k => by
    have := k.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at this
    omega
  cases arr with
  | dyn =>
    show ((LTm.lt i (lenAtN memFuel M t)).eval g ν : Option Bool) = some true ↔ _
    rw [LTm.eval_lt, lenAtN_eval memFuel M t μ hM, LTm.mlen_evalT, hM, Option.bind_some, ht,
      Option.bind_some, hr, Option.map_some]
    cases (i.eval g ν : Option PrimTy.uint.Denote) with
    | none => exact ⟨fun h => (nomatch h), fun ⟨_, hk, _⟩ => (nomatch hk)⟩
    | some k =>
      simp only [Option.bind_some, Option.map_some, Option.some.injEq, decide_eq_true_eq]
      have e : (μ.heap.lenU r).1 = (μ.heap.len r .dyn : Int) := rfl
      have := k0 k
      constructor
      · intro hlt; exact ⟨k, rfl, by omega⟩
      · rintro ⟨k', hk', hlt⟩; cases hk'; omega
  | @fixed E n =>
    have hlen : μ.heap.len r .fixed = n := by
      unfold Heap.len; rw [MObj.elems_fixed]
      exact (μ.heap.get r : {l : List (MVal μ.H' E) // l.length = n}).2
    rw [hlen]
    show ((if n < 2 ^ 256 then LTm.lt i (.nat n) else i.retsC).eval g ν : Option Bool) = some true ↔ _
    split
    · rename_i hn
      rw [LTm.eval_lt, LTm.eval_nat]
      cases (i.eval g ν : Option PrimTy.uint.Denote) with
      | none => exact ⟨fun h => (nomatch h), fun ⟨_, hk, _⟩ => (nomatch hk)⟩
      | some k =>
        simp only [Option.bind_some, Option.map_some, Option.some.injEq, decide_eq_true_eq,
          uintOfNat_val hn]
        have := k0 k
        constructor
        · intro hlt; exact ⟨k, rfl, by omega⟩
        · rintro ⟨k', hk', hlt⟩; cases hk'; omega
    · rename_i hn
      rw [← AllT.single, LTm.retsC_true]
      cases (i.eval g ν : Option PrimTy.uint.Denote) with
      | none => exact ⟨fun h => (nomatch h), fun ⟨_, hk, _⟩ => (nomatch hk)⟩
      | some k =>
        have := klt k
        have := k0 k
        exact ⟨fun _ => ⟨k, rfl, by omega⟩, fun _ => rfl⟩

/-- One step of the returning check: the words each question comes to. -/
def memCondStep (ih : MemQ C → Option (List (LTm C (.val .bool)))) :
    MemQ C → Option (List (LTm C (.val .bool)))
  | .mem M =>
    match M.memView with
    | .write m a v =>
      (ih (.mem m)).bind fun c₁ => (ih (.addr a m)).bind fun c₂ =>
        (match v with
          | .app1 o x =>
            match o.refArg x with
            | some ⟨_, t⟩ => ih (.ident t m)
            | none =>
              some (if ({} : Facts C).returns (({} : Facts C).nf x) then [] else [x.retsC])
          | _ => none).map fun c₃ => c₁ ++ c₂ ++ c₃
    | .addM m _ _ => ih (.mem m)
    | .copySt m _ S =>
      (ih (.mem m)).map fun c => c ++ svConds S
    | .other => if M.retsS then some [] else none
  | .ident t M =>
    if t.peel.1.isEmpty then
      match t.identView with
      | .alloc m R h => if M.onSpine (.app1 (.addM R h) m) then some [] else none
      | .copy m h S => if M.onSpineS (.app2 (.copySt h) m S) then some [] else none
      | .iread X b => if M.onSpine X then ih (.addr b X) else none
      | .other => none
    else (framesCond? t.peel.1).bind fun c₀ => (ih (.ident t.peel.2 M)).map fun c => c₀ ++ c
  | .addr a M =>
    match a.fieldObj? with
    | some ⟨_, t⟩ => ih (.ident t M)
    | none =>
      match a.matObj? with
      | some ⟨_, _, arr, t, i⟩ => (ih (.ident t M)).map fun c => c ++ [lenCond arr M t i]
      | none => none

/-- **When a memory term returns, read on the terms** `n` deep: the words
it comes to — each write lands (a member of an object of the memory, or an
element within its array's bounds; its value a word or an identity there),
each copy copies a source that returns.  By the recursor on the depth. -/
def memCondN (n : Nat) : MemQ C → Option (List (LTm C (.val .bool))) :=
  Nat.rec (motive := fun _ => MemQ C → Option (List (LTm C (.val .bool)))) (fun _ => none)
    (fun _ ih => memCondStep ih) n


/-- **What the check says holds.** -/
theorem memCondN_sound (n : Nat) :
    ∀ (q : MemQ C) (cs : List (LTm C (.val .bool))), memCondN n q = some cs → q.HoldsC g ν cs := by
  induction n with
  | zero => intro q cs h; cases h
  | succ n ih =>
    intro q cs h
    cases q with
    | mem M =>
      show (M.eval g ν : Option (Grown g.H (fun _ => Unit))).isSome = true ↔ AllT g ν cs
      simp only [memCondN, memCondStep] at h
      split at h
      · rename_i m T a v hX
        obtain rfl := LTm.memView_write hX
        obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨c₂, h₂, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨c₃, h₃, rfl⟩ := Option.map_eq_some_iff.1 h
        have H₁ := ih _ _ h₁
        have H₂ := ih _ _ h₂
        have H₃ : ∀ μ, (m.eval g ν : Option (Grown g.H (fun _ => Unit))) = some μ →
            (AllT g ν c₃ → ∃ w mv, (v.eval g ν : Option (MvT T)) = some w ∧
              MvT.toMVal μ.H' T w = some mv) ∧
            ((v.eval g ν : Option (MvT T)).isSome = true → AllT g ν c₃) := by
          intro μ hμ
          cases v with
          | app1 o x =>
            simp only at h₃
            split at h₃
            · rename_i R' t hr
              cases o <;> simp only [Op1.refArg, reduceCtorEq, Option.some.injEq] at hr
              obtain ⟨rfl, hh⟩ := Sigma.mk.inj hr
              cases hh
              have HI := ih _ _ h₃ μ hμ
              refine ⟨fun hc => ?_, fun hv => HI.2 ?_⟩
              · obtain ⟨id, hid, hty⟩ := HI.1 hc
                refine ⟨id, ⟨id, hty⟩, ?_, ?_⟩
                · rw [LTm.eval_app1, hid]; rfl
                · simp only [MvT.toMVal, HRef.ofId?, hty, dite_true]
              · cases ht : (x.eval g ν : Option Nat) with
                | none => rw [LTm.eval_app1_none _ _ ht] at hv; cases hv
                | some _ => rfl
            · rename_i hr
              cases o <;> simp only [Op1.refArg, reduceCtorEq] at hr
              simp only [Option.some.injEq] at h₃
              subst h₃
              split
              · rename_i hv
                refine ⟨fun _ => ?_, fun _ => AllT.nil⟩
                have hv' := Facts.returns_sound (g := g) (ν := ν) (Facts.ok_empty ν) _ hv
                rw [Facts.nf_eval (Facts.ok_empty ν)] at hv'
                obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hv'
                exact ⟨w, w, by rw [LTm.eval_app1, hw]; rfl, rfl⟩
              · refine ⟨fun hc => ?_, fun hv => (LTm.retsC_true x).2 ?_⟩
                · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((LTm.retsC_true x).1 hc)
                  exact ⟨w, w, by rw [LTm.eval_app1, hw]; rfl, rfl⟩
                · cases hx : x.eval g ν with
                  | none => rw [LTm.eval_app1_none _ _ hx] at hv; cases hv
                  | some _ => rfl
          | _ => simp only [reduceCtorEq] at h₃
        rw [AllT.append, AllT.append]
        constructor
        · intro hW
          obtain ⟨μ', hμ'⟩ := Option.isSome_iff_exists.1 hW
          obtain ⟨μ, ad, w, hm, ha, hv, hw⟩ := LTm.write_some hμ'
          unfold Grown.writeT at hw
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hw
          obtain ⟨ra, hra, mv, hmv, hp, hhp, -⟩ := hw
          refine ⟨⟨H₁.1 (by rw [hm]; rfl), (H₂ μ hm).2 ad ra ha hra ?_⟩,
            (H₃ μ hm).2 (by rw [hv]; rfl)⟩
          rw [← Heap.writeAddr_isSome _ _ mv, hhp]; rfl
        · rintro ⟨⟨a₁, a₂⟩, a₃⟩
          obtain ⟨μ, hμ⟩ := Option.isSome_iff_exists.1 (H₁.2 a₁)
          obtain ⟨ad, ra, had, hra, hrd⟩ := (H₂ μ hμ).1 a₂
          obtain ⟨w, mv, hvw, hmv⟩ := (H₃ μ hμ).1 a₃
          obtain ⟨hp, hhp⟩ := Option.isSome_iff_exists.1
            ((Heap.writeAddr_isSome μ.heap ra mv).trans hrd)
          rw [LTm.eval_app3, hμ, had, hvw, Op3.eval_eq_evalM]
          simp only [Op3.evalM, Grown.writeT, Option.bind_eq_bind, Option.bind_some, hra, hmv, hhp]
          rfl
      · rename_i m R hR hX
        obtain rfl := LTm.memView_addM hX
        have H : (m.eval g ν : Option (Grown g.H (fun _ => Unit))).isSome = true ↔ AllT g ν cs :=
          ih _ _ h
        rw [← H, LTm.eval_app1, Op1.eval_eq_evalM]
        simp only [Op1.evalM, Option.isSome_map]
      · rename_i m U hU S hX
        obtain rfl := LTm.memView_copySt hX
        obtain ⟨c, h₁, rfl⟩ := Option.map_eq_some_iff.1 h
        have hS := svConds_iff (g := g) (ν := ν) S
        have H : (m.eval g ν : Option (Grown g.H (fun _ => Unit))).isSome = true ↔ AllT g ν c :=
          ih _ _ h₁
        rw [AllT.append, ← H, ← hS, LTm.eval_app2, Op2.eval_eq_evalM]
        cases (m.eval g ν : Option (Grown g.H (fun _ => Unit))) <;>
          cases (S.eval g ν : Option (SVal U)) <;>
          simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_none, Option.bind_some,
            Option.isSome_none, Option.isSome_some, Bool.false_eq_true, and_false, false_and,
            and_self, iff_self]
      · split at h
        · rename_i hr
          cases h
          exact ⟨fun _ => AllT.nil, fun _ => retsS_isSome hr⟩
        · cases h
    | ident t M =>
      intro μ hμ
      simp only [memCondN, memCondStep] at h
      by_cases hpe : t.peel.1.isEmpty = true
      case neg =>
        rw [if_neg hpe] at h
        obtain ⟨c₀, h₀, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨c₁, h₁, rfl⟩ := Option.map_eq_some_iff.1 h
        have HF := framesCond?_iff (g := g) (ν := ν) _ h₀
        have HI := ih _ _ h₁ μ hμ
        classical
        rw [AllT.append, LTm.eval_peel t]
        refine ⟨fun ⟨a₀, a₁⟩ => ?_, fun ht => ?_⟩
        · rw [if_pos (HF.2 a₀)]; exact HI.1 a₁
        · split at ht
          · rename_i hf
            exact ⟨HF.1 hf, HI.2 ht⟩
          · cases ht
      rw [if_pos hpe] at h
      split at h
      · rename_i m R' hR ht
        split at h
        · rename_i hsp
          cases h
          refine ⟨fun _ => ?_, fun _ => AllT.nil⟩
          cases t with
          | app1 o x =>
            cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht
            simp only [IdentV.alloc.injEq] at ht
            obtain ⟨rfl, rfl⟩ := ht
            obtain ⟨ω, hω, hext⟩ := LTm.onSpine_eval hsp hμ
            rw [LTm.eval_app1, Op1.eval_eq_evalM] at hω
            simp only [Op1.evalM, Option.map_eq_some_iff] at hω
            obtain ⟨μ₀, hμ₀, rfl⟩ := hω
            refine ⟨(μ₀.heap.allocDefault _ hR).val.id, ?_, ?_⟩
            · rw [LTm.eval_app1, hμ₀, Op1.eval_eq_evalM]; rfl
            · exact HTy.getElem?_of_prefix hext (μ₀.heap.allocDefault _ hR).val.get?
          | app2 o x y => cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq] at ht
          | _ => simp only [LTm.identView, reduceCtorEq] at ht
        · cases h
      · rename_i m U hU S ht
        split at h
        · rename_i hsp
          cases h
          refine ⟨fun _ => ?_, fun _ => AllT.nil⟩
          cases t with
          | app1 o x => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht
          | app2 o x y =>
            cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq] at ht
            simp only [IdentV.copy.injEq] at ht
            obtain ⟨rfl, hU', hS⟩ := ht
            subst hU'
            cases hS
            obtain ⟨ω, hω, hext⟩ := LTm.onSpineS_eval hsp hμ
            rw [LTm.eval_app2, Op2.eval_eq_evalM] at hω
            simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.some.injEq] at hω
            obtain ⟨μ₀, hμ₀, v, hv, rfl⟩ := hω
            refine ⟨(v.copyStToM μ₀.heap hU).val.id, ?_, ?_⟩
            · rw [LTm.eval_app2, hμ₀, hv, Op2.eval_eq_evalM]; rfl
            · exact HTy.getElem?_of_prefix hext (v.copyStToM μ₀.heap hU).val.get?
          | _ => simp only [LTm.identView, reduceCtorEq] at ht
        · cases h
      · rename_i X T b ht
        split at h
        · rename_i hX
          cases t with
          | app1 o x => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht
          | app2 o x y =>
            cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq] at ht
            simp only [IdentV.iread.injEq] at ht
            obtain ⟨rfl, hT, hb'⟩ := ht
            subst hT
            cases hb'
            obtain ⟨ξ, hξ, hext⟩ := LTm.onSpine_eval hX hμ
            have HA := ih _ _ h ξ hξ
            refine ⟨fun hc => ?_, fun hi => ?_⟩
            · obtain ⟨ad, ra, had, hra, hrd⟩ := HA.1 hc
              obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hrd
              refine ⟨r.id, ?_, HTy.getElem?_of_prefix hext r.get?⟩
              rw [LTm.iread_evalT, hξ, had, Option.bind_some, Option.bind_some, hra,
                Option.bind_some, hr]
              rfl
            · rw [LTm.iread_evalT, hξ, Option.bind_some] at hi
              cases hb : (y.eval g ν : Option (MAddrT _)) with
              | none => rw [hb] at hi; cases hi
              | some ad =>
                rw [hb, Option.bind_some] at hi
                cases hra : ad.resolve ξ.H' with
                | none => rw [hra] at hi; cases hi
                | some ra =>
                  rw [hra, Option.bind_some] at hi
                  refine HA.2 ad ra hb hra ?_
                  cases hrd : ξ.heap.readAddr ra with
                  | none => rw [hrd] at hi; cases hi
                  | some _ => rfl
          | _ => simp only [LTm.identView, reduceCtorEq] at ht
        · cases h
      · cases h
    | addr a M =>
      intro μ hμ
      simp only [memCondN, memCondStep] at h
      split at h
      · rename_i R t ht
        cases a with
        | app1 o x =>
          cases o <;> simp only [LTm.fieldObj?, Op1.fieldObj, reduceCtorEq, Option.some.injEq] at ht
          obtain ⟨rfl, ht⟩ := Sigma.mk.inj ht
          cases ht
          rename_i s f T hf
          have HI := ih _ _ h μ hμ
          refine ⟨fun hc => ?_, fun ad ra had _ _ => HI.2 ?_⟩
          · obtain ⟨id, hid, hty⟩ := HI.1 hc
            refine ⟨.field id hf, .field ⟨id, hty⟩ hf, ?_, ?_, rfl⟩
            · rw [LTm.eval_app1, hid]; rfl
            · simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?, hty, dite_true,
                Option.map_some]
          · cases hx : (x.eval g ν : Option Nat) with
            | none => rw [LTm.eval_app1_none _ _ hx] at had; cases had
            | some _ => rfl
        | _ => simp only [LTm.fieldObj?, reduceCtorEq] at ht
      · split at h
        · rename_i R E arr t i _ hm
          obtain ⟨c, h₁, rfl⟩ := Option.map_eq_some_iff.1 h
          have HI := ih _ _ h₁ μ hμ
          cases a with
          | app2 o x y =>
            cases o <;> simp only [LTm.matObj?, Op2.matObj, reduceCtorEq, Option.some.injEq] at hm
            cases hm
            rename_i k arr _
            have hev : ∀ id (kv : PrimTy.uint.Denote), (i.eval g ν : Option Nat) = some id →
                (k.eval g ν : Option PrimTy.uint.Denote) = some kv →
                ((LTm.app2 (.mat arr) i k).eval g ν : Option (MAddrT _)) =
                  some (.index id arr kv) := by
              intro id kv h1 h2; rw [LTm.eval_app2, h1, h2, Op2.eval_eq_evalM]; rfl
            rw [AllT.append]
            refine ⟨fun ⟨a₁, a₂⟩ => ?_, fun ad ra had hra hrd => ⟨?_, ?_⟩⟩
            · obtain ⟨id, hid, hty⟩ := HI.1 a₁
              have hr : HRef.ofId? μ.H' E id = some ⟨id, hty⟩ := by
                simp only [HRef.ofId?, hty, dite_true]
              obtain ⟨kv, hk, hlt⟩ := (lenCond_iff arr M i k hμ hid hr).1 (AllT.single.1 a₂)
              refine ⟨.index id arr kv, .index ⟨id, hty⟩ arr kv, hev id kv hid hk, ?_, ?_⟩
              · simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, hr, Option.map_some]
              · rw [Heap.readAddr_index_isSome]
                simp only [decide_eq_true_eq]
                exact hlt
            · apply HI.2
              cases hx : (i.eval g ν : Option Nat) with
              | none => rw [LTm.eval_app2_none _ _ _ hx] at had; cases had
              | some _ => rfl
            · cases hx : (i.eval g ν : Option Nat) with
              | none => rw [LTm.eval_app2_none _ _ _ hx] at had; cases had
              | some id =>
                cases hk : (k.eval g ν : Option PrimTy.uint.Denote) with
                | none => rw [LTm.eval_app2, hx, hk, Op2.eval_eq_evalM] at had; cases had
                | some kv =>
                  rw [hev id kv hx hk] at had
                  cases had
                  simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM,
                    Option.map_eq_some_iff] at hra
                  obtain ⟨r, hr, rfl⟩ := hra
                  rw [Heap.readAddr_index_isSome] at hrd
                  simp only [decide_eq_true_eq] at hrd
                  exact AllT.single.2 ((lenCond_iff arr M i k hμ hx hr).2 ⟨kv, hk, hrd⟩)
          | _ => simp only [LTm.matObj?, reduceCtorEq] at hm
        · cases h

/-- The memory an identity term's returning is read in. -/
def LTm.identMem? {s : Srt} (t : LTm C s) : Option (LTm C .mem) :=
  match t.identView with
  | .alloc m R h => some (.app1 (.addM R h) m)
  | .copy m h S => some (.app2 (.copySt h) m S)
  | .iread X _ => some X
  | .other => none

theorem LTm.identMem?_rets {R : RefTy} {t : LTm C (.ident R)} {M : LTm C .mem}
    (h : t.identMem? = some M) (ht : (t.eval g ν : Option Nat).isSome = true) :
    (M.eval g ν : Option (Grown g.H (fun _ => Unit))).isSome = true := by
  unfold LTm.identMem? at h
  split at h
  · rename_i m R' hR ht'
    cases h
    cases t with
    | app1 o x =>
      cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq, IdentV.alloc.injEq] at ht'
      obtain ⟨rfl, -⟩ := ht'
      cases hx : (x.eval g ν : Option (Grown g.H (fun _ => Unit))) with
      | none => rw [LTm.eval_app1_none _ _ hx] at ht; cases ht
      | some μ => rw [LTm.eval_app1, hx, Op1.eval_eq_evalM]; rfl
    | app2 o x y => cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq] at ht'
    | _ => simp only [LTm.identView, reduceCtorEq] at ht'
  · rename_i m U hU S ht'
    cases h
    cases t with
    | app1 o x => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht'
    | app2 o x y =>
      cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq, IdentV.copy.injEq] at ht'
      obtain ⟨rfl, rfl, hy⟩ := ht'
      cases eq_of_heq hy
      cases hx : (x.eval g ν : Option (Grown g.H (fun _ => Unit))) with
      | none => rw [LTm.eval_app2_none _ _ _ hx] at ht; cases ht
      | some μ =>
        cases hy' : (y.eval g ν : Option (SVal _)) with
        | none =>
          rw [LTm.eval_app2, hx, hy', Op2.eval_eq_evalM] at ht; cases ht
        | some v => rw [LTm.eval_app2, hx, hy', Op2.eval_eq_evalM]; rfl
    | _ => simp only [LTm.identView, reduceCtorEq] at ht'
  · rename_i X T b ht'
    cases h
    cases t with
    | app1 o x => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht'
    | app2 o x y =>
      cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq, IdentV.iread.injEq] at ht'
      obtain ⟨rfl, -⟩ := ht'
      cases hx : (x.eval g ν : Option (Grown g.H (fun _ => Unit))) with
      | none => rw [LTm.eval_app2_none _ _ _ hx] at ht; cases ht
      | some μ => rfl
    | _ => simp only [LTm.identView, reduceCtorEq] at ht'
  · cases h

/-- A copy into storage, viewed: its memory and object. -/
def _root_.Solidity.Op2.copyMemV {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    Option ((R : RefTy) × LTm C .mem × LTm C (.ident R)) :=
  match o, x, y with
  | .copyMem, x, y => some ⟨_, x, y⟩
  | _, _, _ => none

/-- A copy into storage's memory and object. -/
def LTm.copyMemV? {s : Srt} (t : LTm C s) : Option ((R : RefTy) × LTm C .mem × LTm C (.ident R)) :=
  match t with
  | .app2 o x y => o.copyMemV x y
  | _ => none

theorem LTm.copyMem_isSome {R : RefTy} (M : LTm C .mem) (t : LTm C (.ident R)) :
    ((LTm.app2 .copyMem M t).eval g ν : Option (SVal (.ref R))).isSome = true ↔
      ∃ μ : Grown g.H (fun _ => Unit), M.eval g ν = some μ ∧
        ∃ id, (t.eval g ν : Option Nat) = some id ∧ μ.H'[id]? = some R := by
  rw [LTm.eval_app2, Op2.eval_eq_evalM]
  cases hm : (M.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩
  | some μ =>
    cases ht : (t.eval g ν : Option Nat) with
    | none => exact ⟨fun h => (nomatch h), fun ⟨_, _, _, h, _⟩ => (nomatch h)⟩
    | some id =>
      show ((HRef.ofId? μ.H' R id).bind fun r =>
        some (MVal.copyMToSt μ.heap (T := .ref R) r)).isSome = true ↔ _
      unfold HRef.ofId?
      by_cases hid : μ.H'[id]? = some R
      · simp only [hid, dite_true, Option.bind_some, Option.isSome_some, true_iff]
        exact ⟨μ, rfl, id, rfl, hid⟩
      · simp only [hid, dite_false, Option.bind_none, Option.isSome_none, Bool.false_eq_true,
          false_iff, not_exists, not_and]
        intro μ' hμ' id' hid' hR
        cases hμ'
        cases hid'
        exact hid hR

/-- The words a guard's returning comes to: a memory's, an identity's in
its memory. -/
def guardQ {s : Srt} (d : LTm C s) : Option (List (LTm C (.val .bool))) :=
  match (d.castTo? : Option (LTm C .mem)) with
  | some M => memCondN memFuel (.mem M)
  | none =>
    match s, d with
    | .ident _, d =>
      if d.peel.1.isEmpty then
        d.identMem?.bind fun M => (memCondN memFuel (.mem M)).bind fun c₁ =>
          (memCondN memFuel (.ident d M)).map fun c₂ => c₁ ++ c₂
      else
        (framesCond? d.peel.1).bind fun c₀ =>
          (d.peel.2.identMem?.bind fun M => (memCondN memFuel (.mem M)).bind fun c₁ =>
            (memCondN memFuel (.ident d.peel.2 M)).map fun c₂ => c₁ ++ c₂).map fun c => c₀ ++ c
    | .sv _, d =>
      match d.copyMemV? with
      | some ⟨_, M, t⟩ => (memCondN memFuel (.mem M)).bind fun c₁ =>
          (memCondN memFuel (.ident t M)).map fun c₂ => c₁ ++ c₂
      | none => some (svConds d)
    | _, _ => none

/-- `guardQ` at an identity with no guard of its own. -/
theorem guardQ_ident {R : RefTy} (d' : LTm C (.ident R)) {cs : List (LTm C (.val .bool))}
    (h : (d'.identMem?.bind fun M => (memCondN memFuel (.mem M)).bind fun c₁ =>
        (memCondN memFuel (.ident d' M)).map fun c₂ => c₁ ++ c₂) = some cs) :
    (d'.eval g ν : Option Nat).isSome = true ↔ AllT g ν cs := by
  obtain ⟨M, hM, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨c₂, h₂, rfl⟩ := Option.map_eq_some_iff.1 h
  have HM := memCondN_sound (g := g) (ν := ν) memFuel (.mem M) c₁ h₁
  have HI := memCondN_sound (g := g) (ν := ν) memFuel (.ident d' M) c₂ h₂
  rw [AllT.append]
  constructor
  · intro hd
    have hMs := LTm.identMem?_rets hM hd
    obtain ⟨μ, hμ⟩ := Option.isSome_iff_exists.1 hMs
    exact ⟨HM.1 hMs, (HI μ hμ).2 hd⟩
  · rintro ⟨a₁, a₂⟩
    obtain ⟨μ, hμ⟩ := Option.isSome_iff_exists.1 (HM.2 a₁)
    obtain ⟨id, hid, -⟩ := (HI μ hμ).1 a₂
    show (d'.eval g ν : Option Nat).isSome = true
    rw [hid]; rfl

theorem guardQ_sound {s : Srt} {d : LTm C s} {cs : List (LTm C (.val .bool))}
    (h : guardQ d = some cs) : (d.eval g ν).isSome = true ↔ AllT g ν cs := by
  unfold guardQ at h
  split at h
  · rename_i M hM
    cases LTm.castTo?_eq hM
    exact memCondN_sound memFuel (.mem M) cs h
  · split at h
    · rename_i R d' _
      split at h
      · exact guardQ_ident d' h
      · obtain ⟨c₀, h₀, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
        have HF := framesCond?_iff (g := g) (ν := ν) _ h₀
        have HI := guardQ_ident (g := g) (ν := ν) d'.peel.2 hc
        classical
        rw [AllT.append, ← HI, LTm.eval_peel d']
        constructor
        · intro hd
          split at hd
          · rename_i hf; exact ⟨HF.1 hf, hd⟩
          · cases hd
        · rintro ⟨a₀, a₁⟩
          rw [if_pos (HF.2 a₀)]; exact a₁
    · rename_i U d' _
      split at h
      · rename_i R M t hcm
        obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨c₂, h₂, rfl⟩ := Option.map_eq_some_iff.1 h
        have HM := memCondN_sound (g := g) (ν := ν) memFuel (.mem M) c₁ h₁
        have HI := memCondN_sound (g := g) (ν := ν) memFuel (.ident t M) c₂ h₂
        cases d' with
        | app2 o x y =>
          cases o <;> simp only [LTm.copyMemV?, Op2.copyMemV, reduceCtorEq, Option.some.injEq] at hcm
          obtain ⟨rfl, hcm⟩ := Sigma.mk.inj hcm
          simp only [heq_eq_eq, Prod.mk.injEq] at hcm
          obtain ⟨rfl, rfl⟩ := hcm
          rw [LTm.copyMem_isSome, AllT.append]
          constructor
          · rintro ⟨μ, hμ, id, hid, hR⟩
            exact ⟨HM.1 (by rw [hμ]; rfl), (HI μ hμ).2 (by rw [hid]; rfl)⟩
          · rintro ⟨a₁, a₂⟩
            obtain ⟨μ, hμ⟩ := Option.isSome_iff_exists.1 (HM.2 a₁)
            exact ⟨μ, hμ, (HI μ hμ).1 a₂⟩
        | _ => simp only [LTm.copyMemV?, reduceCtorEq] at hcm
      · cases h
        exact svConds_iff d'
    · cases h

/-- A word the closer folds to `true` (`Facts.nf` with no facts). -/
def LTm.isTrueC (c : LTm C (.val .bool)) : Bool :=
  match (({} : Facts C).nf c).litV? with
  | some v => v
  | none => false

theorem LTm.isTrueC_eval {c : LTm C (.val .bool)} (h : c.isTrueC = true) :
    (c.eval g ν : Option Bool) = some true := by
  unfold LTm.isTrueC at h
  split at h
  · rename_i v hv
    rw [← Facts.nf_eval (Facts.ok_empty ν), LTm.eval_litV? g ν hv, h]
  · cases h

/-- `a`, guarded by the words `cs`: `if (c) then … else err`, a word the
closer folds to `true` dropped, and a guard `a` already has at its top
(`LTm.peel`). -/
def guardL (cs : List (LTm C (.val .bool))) {s : Srt} (a : LTm C s) : LTm C s :=
  cs.foldr (fun c a => if c.isTrueC then a
    else if a.peel.1.any (GFrame.kite c .tt).beq then a else .kite c .tt a .err) a

open Classical in
theorem guardL_eval (cs : List (LTm C (.val .bool))) {s : Srt} (a : LTm C s) :
    (guardL cs a).eval g ν = if AllT g ν cs then a.eval g ν else none := by
  induction cs with
  | nil => rw [if_pos AllT.nil]; rfl
  | cons c cs ih =>
    have hc : AllT g ν (c :: cs) ↔ (c.eval g ν : Option Bool) = some true ∧ AllT g ν cs := by
      rw [show c :: cs = [c] ++ cs from rfl, AllT.append, AllT.single]
    show (if c.isTrueC then guardL cs a
      else if (guardL cs a).peel.1.any (GFrame.kite c .tt).beq then guardL cs a
      else .kite c .tt (guardL cs a) .err).eval g ν = _
    split
    · rename_i htc
      have h1 := LTm.isTrueC_eval (g := g) (ν := ν) htc
      rw [ih]
      by_cases h2 : AllT g ν cs
      · rw [if_pos h2, if_pos (hc.2 ⟨h1, h2⟩)]
      · rw [if_neg h2, if_neg (fun h => h2 (hc.1 h).2)]
    split
    · rename_i hany
      obtain ⟨f', hf', hb⟩ := List.any_eq_true.1 hany
      cases GFrame.eq_of_beq hb
      by_cases h1 : (c.eval g ν : Option Bool) = some true
      · rw [ih]
        by_cases h2 : AllT g ν cs
        · rw [if_pos h2, if_pos (hc.2 ⟨h1, h2⟩)]
        · rw [if_neg h2, if_neg (fun h => h2 (hc.1 h).2)]
      · have hn : ¬ (GFrame.kite c .tt).Holds g ν := by
          rintro ⟨x, hx, hy⟩
          have ht : ((LTm.tt : LTm C (.val .bool)).eval g ν : Option Bool) = some true := rfl
          rw [ht] at hy
          cases hy
          exact h1 hx
        rw [LTm.eval_none_of_peel hf' hn, if_neg (fun h => h1 (hc.1 h).1)]
    rw [LTm.eval_kite, ih]
    by_cases h1 : (c.eval g ν : Option Bool) = some true
    · rw [h1]
      by_cases h2 : AllT g ν cs
      · rw [if_pos (hc.2 ⟨h1, h2⟩), if_pos h2]; rfl
      · rw [if_neg (fun h => h2 (hc.1 h).2), if_neg h2]; rfl
    · rw [if_neg (fun h => h1 (hc.1 h).1)]
      cases hce : (c.eval g ν : Option Bool) with
      | none => rfl
      | some x =>
        cases x
        · rfl
        · exact absurd hce h1

/-- `d; a`, the guard read as the words it comes to (`guardQ`). -/
def seqMemL1 {s' s : Srt} (d : LTm C s') (a : LTm C s) : LTm C s :=
  match guardQ d with
  | some cs => guardL cs a
  | none => .seq d a

theorem seqMemL1_eval {s' s : Srt} (d : LTm C s') (a : LTm C s) :
    (seqMemL1 d a).eval g ν = (LTm.seq d a).eval g ν := by
  unfold seqMemL1
  split
  · rename_i cs h
    rw [guardL_eval, LTm.eval_seq]
    by_cases hc : AllT g ν cs
    · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((guardQ_sound h).2 hc)
      rw [if_pos hc, hw]; rfl
    · have hd : d.eval g ν = none := by
        cases hd : d.eval g ν with
        | none => rfl
        | some _ => exact absurd ((guardQ_sound h).1 (by rw [hd]; rfl)) hc
      rw [if_neg hc, hd]; rfl
  · rfl

/-- `d; a`, a guard `d₁; d₂` taken as two (`(d₁; d₂); a` is `d₁; (d₂; a)`),
each read as the words it comes to. -/
def seqMemL {s' s : Srt} (d : LTm C s') (a : LTm C s) : LTm C s :=
  match d with
  | .seq d₁ d₂ => seqMemL1 d₁ (seqMemL1 d₂ a)
  | d => seqMemL1 d a

theorem seqMemL_eval {s' s : Srt} (d : LTm C s') (a : LTm C s) :
    (seqMemL d a).eval g ν = (LTm.seq d a).eval g ν := by
  cases d with
  | seq d₁ d₂ =>
    show (seqMemL1 d₁ (seqMemL1 d₂ a)).eval g ν = _
    rw [seqMemL1_eval, LTm.eval_seq, LTm.eval_seq, LTm.eval_seq]
    cases d₁.eval g ν with
    | none => rfl
    | some _ => simp only [Option.bind_some, seqMemL1_eval, LTm.eval_seq]
  | _ => simp only [seqMemL]; exact seqMemL1_eval _ a

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

/-- An array-element address, retaining the array's element type. -/
structure ArrayV (C : Contract) where
  {R : RefTy}
  {E : Ty}
  ak : ArrTy R E
  t : LTm C (.ident R)
  i : LTm C (.val .uint)

def arrayArg {a b s : Srt} (o : Op2 C a b s)
    (x : LTm C a) (y : LTm C b) : Option (ArrayV C) :=
  match o, x, y with
  | .mat ak, x, y => some ⟨ak, x, y⟩
  | _, _, _ => none

def arrayV? {s : Srt} (b : LTm C s) : Option (ArrayV C) :=
  match b with
  | .app2 o x y => arrayArg o x y
  | _ => none

/-- `selectOnCopyMemPrim` followed by `initElement`: a primitive read of
the same fresh-array copy, guarded by its size. -/
def copyNewArrayRd? {U : Ty} {P : PrimTy}
    (m : LTm C .mem) (S : LTm C (.sv U)) (b : LTm C (.addr (.prim P))) :
    Option (LTm C (.val P)) := do
  let a ← arrayV? b
  let t ← a.t.castTo? (s' := .ident (.array (.prim P)))
  match t.identView with
  | .copy m' _ S' =>
    if m'.beqR m && S'.beqR S then
      let n ← S'.newArrLen?
      some (.app3 .ite (.app2 (.binop .lt rfl) a.i n) (.lit (PrimTy.dflt P)) .err)
    else none
  | _ => none

theorem copyNewArrayRd?_eval (g : State C []) (ν : AEnv)
    {U : Ty} {hU : U.mapFree = true} {m : LTm C .mem} {S : LTm C (.sv U)}
    {P : PrimTy} {b : LTm C (.addr (.prim P))} {y : LTm C (.val P)}
    (h : copyNewArrayRd? m S b = some y) :
    ((LTm.app2 .read (.app2 (.copySt hU) m S) b).eval g ν : Option P.Denote) =
      (LTm.seq (.app2 (.copySt hU) m S) y).eval g ν := by
  unfold copyNewArrayRd? at h
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · rename_i m' R' hR S' hview
    split at h
    · rename_i hc
      obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hm, hS⟩ := hc
      cases LTm.sigma_eq_of_beqR hm
      obtain ⟨hUU, hSS⟩ := Sigma.mk.inj (LTm.sigma_eq_of_beqR hS)
      cases hUU
      cases eq_of_heq hSS
      cases b with
      | app2 o xb ib =>
        cases o <;> simp only [arrayV?, arrayArg, Option.some.injEq] at ha
        rename_i ak
        cases ha
        obtain ⟨hType, het⟩ := Sigma.mk.inj (LTm.castTo?_eq ht)
        cases hType
        cases eq_of_heq het
        have hak : ak = .dyn := match ak with | .dyn => rfl
        rw [hak]
        dsimp only at hview ⊢
        cases xb with
        | app2 o xm xS =>
          cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq,
            IdentV.copy.injEq] at hview
          obtain ⟨rfl, hType, heq⟩ := hview
          cases hType
          cases eq_of_heq heq
          cases xS with
          | app1 o z =>
            cases o <;> simp only [LTm.newArrLen?, Op1.newArrArg,
              Option.some.injEq, reduceCtorEq] at hn
            subst n
            simp only [LTm.eval_app1, LTm.eval_app2, LTm.eval_app3, LTm.eval_seq,
              Op1.eval_eq_evalM, Op2.eval_eq_evalM, Op3.eval_eq_evalM,
              Op1.evalM, Op2.evalM, Op3.evalM, Option.bind_eq_bind]
            cases hx : (xm.eval g ν : Option (Grown g.H (fun _ => Unit))) <;>
              (try simp only [Option.bind_none, Option.bind_some])
            rename_i μ
            cases hz : (z.eval g ν : Option PrimTy.uint.Denote) <;>
              (try simp only [Option.map_none, Option.map_some, Option.bind_none, Option.bind_some])
            rename_i v
            cases hi : (ib.eval g ν : Option PrimTy.uint.Denote) <;>
              (try simp only [Option.bind_none, Option.bind_some])
            rename_i k
            simp only [Grown.readT, Grown.then, MAddrT.resolve_eq_resolveM, MAddrT.resolveM,
              HRef.ofId?_self, Option.map_some]
            simp only [Option.bind_eq_bind, Option.bind_some]
            rw [newArrT_copy_prim_index]
            change (if k.1.toNat < v.1.toNat then some (PrimTy.dflt P) else none) =
              (bif decide (k.1 < v.1) then some (PrimTy.dflt P) else none)
            have hv := v.2
            have hk := k.2
            simp only [PrimTy.inRange, decide_eq_true_eq] at hv hk
            have he : (k.1.toNat < v.1.toNat) = (k.1 < v.1) := propext (by omega)
            simp only [he]
            by_cases hc : k.1 < v.1 <;>
              simp only [hc, decide_true, decide_false, if_true, if_false] <;> rfl
          | _ => simp only [LTm.newArrLen?, reduceCtorEq] at hn
        | app1 o x => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at hview
        | _ => simp only [LTm.identView, reduceCtorEq] at hview
      | _ => simp only [arrayV?, reduceCtorEq] at ha
    · cases h
  · cases h

/-- **A read of a word, walked down its memory** `n` writes and
allocations deep: `readOnWrite`, `readOnWriteFrame`, `readOnAddMFrame`,
`readOnAddM`.  By the recursor on the depth. -/
def memReadN (n : Nat) : {P : PrimTy} → LTm C .mem → LTm C (.addr (.prim P)) → LTm C (.val P) :=
  Nat.rec (motive := fun _ => {P : PrimTy} → LTm C .mem → LTm C (.addr (.prim P)) → LTm C (.val P))
    (fun X b => .app2 .read X b)
    (fun _ ih {P} X b =>
      match X.memView with
      | .write m a v =>
        if a.hoistA.2.beqR b then
          match v.mvArg? with
          | some ⟨_, x⟩ =>
            match x.castTo? with
            | some x' => seqMemL X x'
            | none => .app2 .read X b
          | none => .app2 .read X b
        else if a.apart? b then seqMemL X (ih m b)
        else .app2 .read X b
      | .addM m R _ =>
        if b.boundedIn m then ih m b
        else if (LTm.freshPath? m R b).bind (Ty.ref R).memberTy == some (.prim P) then
          seqMemL m (.lit (PrimTy.dflt P))
        else .app2 .read X b
      | .copySt m _ S =>
        if b.boundedIn m then seqMemL S (ih m b)
        else
          match copyFieldRd? m S (b.unstripAddr m) with
          | some y => seqMemL X y
          | none =>
            match copyNewArrayRd? m S (b.unstripAddr m) with
            | some y => seqMemL X y
            | none =>
              match copyPathRd? X m S b with
              | some y => seqMemL X y
              | none => .app2 .read X b
      | .other => .app2 .read X b) n

/-- **A read of an identity, walked down its memory.** -/
def memIReadN (n : Nat) : {R : RefTy} → LTm C .mem → LTm C (.addr (.ref R)) → LTm C (.ident R) :=
  Nat.rec (motive := fun _ => {R : RefTy} → LTm C .mem → LTm C (.addr (.ref R)) → LTm C (.ident R))
    (fun X b => .app2 .iread X b)
    (fun _ ih {R} X b =>
      match X.memView with
      | .write m a v =>
        if a.hoistA.2.beqR b then
          match v.mvArg? with
          | some ⟨_, x⟩ =>
            match x.castTo? with
            | some x' => seqMemL X x'
            | none => .app2 .iread X b
          | none => .app2 .iread X b
        else if a.apart? b then seqMemL X (ih m b)
        else .app2 .iread X b
      | .addM m _ _ =>
        if b.boundedIn m then ih m b else .app2 .iread X b
      | .copySt m _ S =>
        if b.boundedIn m then seqMemL S (ih m b) else .app2 .iread X b
      | .other => .app2 .iread X b) n

theorem memReadN_eval (n : Nat) : ∀ {P : PrimTy} (X : LTm C .mem) (b : LTm C (.addr (.prim P))),
    ((memReadN n X b).eval g ν : Option P.Denote) = (LTm.app2 .read X b).eval g ν := by
  induction n with
  | zero => intro P X b; rfl
  | succ n ih =>
    intro P X b
    show (match X.memView with
      | .write m a v =>
        if a.hoistA.2.beqR b then
          match v.mvArg? with
          | some ⟨_, x⟩ =>
            match x.castTo? with
            | some x' => seqMemL X x'
            | none => .app2 .read X b
          | none => .app2 .read X b
        else if a.apart? b then seqMemL X (memReadN n m b)
        else .app2 .read X b
      | .addM m R _ =>
        if b.boundedIn m then memReadN n m b
        else if (LTm.freshPath? m R b).bind (Ty.ref R).memberTy == some (.prim P) then
          seqMemL m (.lit (PrimTy.dflt P))
        else .app2 .read X b
      | .copySt m _ S =>
        if b.boundedIn m then seqMemL S (memReadN n m b)
        else
          match copyFieldRd? m S (b.unstripAddr m) with
          | some y => seqMemL X y
          | none =>
            match copyNewArrayRd? m S (b.unstripAddr m) with
            | some y => seqMemL X y
            | none =>
              match copyPathRd? X m S b with
              | some y => seqMemL X y
              | none => .app2 .read X b
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
              rw [seqMemL_eval]; exact (LTm.read_write_hoist m _ x').symm
            | _ => simp only [LTm.mvArg?, reduceCtorEq] at hv
          · rfl
        · rfl
      · split
        · rename_i hap
          rw [seqMemL_eval, LTm.read_write_apart' m a v b hap, LTm.eval_seq, LTm.eval_seq, ih]
        · rfl
    · rename_i m R hR hX
      obtain rfl := LTm.memView_addM hX
      split
      · rename_i hb
        rw [ih, LTm.read_addM_old m R hR b hb]
      · split
        · rename_i hf
          rw [seqMemL_eval]; exact (LTm.read_addM_fresh m R hR b (beq_iff_eq.1 hf)).symm
        · rfl
    · rename_i m U hU S hX
      obtain rfl := LTm.memView_copySt hX
      split
      · rename_i hb
        rw [seqMemL_eval, LTm.read_copySt_old m hU S b hb, LTm.eval_seq, LTm.eval_seq, ih]
      · split
        · rename_i y hy
          rw [seqMemL_eval, ← LTm.read_unstrip]
          exact (copyFieldRd?_eval hy).symm
        · split
          · rename_i y hy
            rw [seqMemL_eval, ← LTm.read_unstrip]
            exact (copyNewArrayRd?_eval g ν hy).symm
          · split
            · rename_i y hy
              rw [seqMemL_eval]
              exact (copyPathRd?_eval hy).symm
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
        if a.hoistA.2.beqR b then
          match v.mvArg? with
          | some ⟨_, x⟩ =>
            match x.castTo? with
            | some x' => seqMemL X x'
            | none => .app2 .iread X b
          | none => .app2 .iread X b
        else if a.apart? b then seqMemL X (memIReadN n m b)
        else .app2 .iread X b
      | .addM m _ _ =>
        if b.boundedIn m then memIReadN n m b else .app2 .iread X b
      | .copySt m _ S =>
        if b.boundedIn m then seqMemL S (memIReadN n m b) else .app2 .iread X b
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
              rw [seqMemL_eval]; exact (LTm.iread_write_hoist m _ x').symm
            | _ => simp only [LTm.mvArg?, reduceCtorEq] at hv
          · rfl
        · rfl
      · split
        · rename_i hap
          rw [seqMemL_eval, LTm.iread_write_apart' m a v b hap, LTm.eval_seq, LTm.eval_seq, ih]
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
        rw [seqMemL_eval, LTm.iread_copySt_old m hU S b hb, LTm.eval_seq, LTm.eval_seq, ih]
      · rfl
    · rfl

end Walk

/-! ## The hash of a byte string read off the memory (Lean only)

Where a byte string's length and every byte read down the memory to
literals (`lenAtN`, `memReadN`), a hash of it (`keccak256`, `sha256`,
`ripemd160`: `HashKind.apply`) is that function of
those bytes, which the kernel evaluates; no solkey taclet reads a hash
(solkey's `keccak256` is uninterpreted). -/

section Keccak

variable {g : State C []} {ν : AEnv}

/-- The literal a term comes to where it returns: a literal, under at most
`n` sequences or guards (`guardL`'s `kite c true a err`).  By recursion on
`n`, so that the kernel evaluates it. -/
def LTm.litInN {p : PrimTy} : Nat → LTm C (.val p) → Option p.Denote
  | 0, _ => none
  | n + 1, t =>
    match t with
    | .app0 (.lit v) => some v
    | .seq _ a => LTm.litInN n a
    | .kite _ _ t e => if e.isErr then LTm.litInN n t else none
    | _ => none

/-- `litInN` within the memory's fuel. -/
def LTm.litIn? {p : PrimTy} (t : LTm C (.val p)) : Option p.Denote := LTm.litInN memFuel t

theorem LTm.litInN_eval {p : PrimTy} (n : Nat) : ∀ (t : LTm C (.val p)) {v : p.Denote},
    LTm.litInN n t = some v → ∀ {x : p.Denote}, (t.eval g ν : Option p.Denote) = some x → x = v := by
  induction n with
  | zero => intro t v h; cases h
  | succ n ih =>
    intro t v h x hx
    unfold LTm.litInN at h
    split at h
    · cases h
      exact (Option.some.inj hx).symm
    · rename_i d a
      rw [LTm.eval_seq] at hx
      cases hd : d.eval g ν with
      | none => rw [hd] at hx; cases hx
      | some _ =>
        rw [hd, Option.bind_some] at hx
        exact ih a h hx
    · rename_i q a b t e
      split at h
      · rename_i he
        rw [LTm.eval_kite] at hx
        cases ha : (a.eval g ν : Option q.Denote) with
        | none => rw [ha] at hx; cases hx
        | some u =>
          rw [ha, Option.bind_some] at hx
          cases hb : (b.eval g ν : Option q.Denote) with
          | none => rw [hb] at hx; cases hx
          | some w =>
            rw [hb, Option.bind_some] at hx
            split at hx
            · exact ih t h hx
            · rw [LTm.eval_of_isErr g ν he] at hx; cases hx
      · cases h
    · cases h

theorem LTm.litIn?_eval {p : PrimTy} (t : LTm C (.val p)) {v : p.Denote} (h : t.litIn? = some v)
    {x : p.Denote} (hx : (t.eval g ν : Option p.Denote) = some x) : x = v :=
  LTm.litInN_eval memFuel t h hx

/-- The bytes `i, i+1, …, i+k-1` of the byte string `t` in `X`, each read
down the memory (`memReadN`) to a literal. -/
def keccakWords (rd : PrimTy.uint.Denote → Option PrimTy.uint.Denote) :
    Nat → Nat → Option (List PrimTy.uint.Denote)
  | 0, _ => some []
  | k + 1, i =>
    match rd (uintOfNat i) with
    | some v =>
      match keccakWords rd k (i + 1) with
      | some vs => some (v :: vs)
      | none => none
    | none => none

/-- The most bytes a hash is read for. -/
def keccakMaxBytes : Nat := 64

/-- **The hash of a byte string read off the memory** (Lean only): where
its length and every byte read down the memory to literals, the hash `k` is
evaluated on them (`HashKind.apply`); where the memory does not return, the
symbol as it was. -/
def keccakAt (k : HashKind) (X : LTm C .mem) (t : LTm C (.ident (.array (.prim .uint)))) : LTm C (.val .uint) :=
  match (lenAtN memFuel X t).litIn? with
  | some n =>
    if n.1.toNat ≤ keccakMaxBytes then
      match keccakWords (fun iv => (memReadN memFuel X (.app2 (.mat .dyn) t (.lit iv))).litIn?)
          n.1.toNat 0 with
      | some vs => .orElse (.seq (seqMemL X (lenAtN memFuel X t))
          (.lit (k.apply (vs.map (·.1))))) (.app2 (.hash k) X t)
      | none => .app2 (.hash k) X t
    else .app2 (.hash k) X t
  | none => .app2 (.hash k) X t

/-- `keccakAt` at a byte string, the symbol elsewhere; any hashing builtin `k` (`HashKind.apply`). -/
def keccakRes (k : HashKind) {R : RefTy} (X : LTm C .mem) (t : LTm C (.ident R)) : LTm C (.val .uint) :=
  match R, t with
  | .array (.prim .uint), t => keccakAt k X t
  | _, t => .app2 (.hash k) X t

theorem eval_read_mat (X : LTm C .mem) (t : LTm C (.ident (.array (.prim .uint))))
    (iv : PrimTy.uint.Denote) (μ : Grown g.H (fun _ => Unit)) (id : Nat)
    (hX : X.eval g ν = some μ) (ht : t.eval g ν = some id) :
    ((LTm.app2 .read X (.app2 (.mat .dyn) t (.lit iv))).eval g ν : Option PrimTy.uint.Denote) =
      (HRef.ofId? μ.H' (.array (.prim .uint)) id).bind fun r => μ.heap.index r .dyn iv := by
  rw [LTm.eval_app2, LTm.eval_app2, hX, ht]
  show (μ.readT (MAddrT.index id .dyn iv)) = _
  unfold Grown.readT
  rw [MAddrT.resolve_eq_resolveM]
  simp only [MAddrT.resolveM]
  cases HRef.ofId? μ.H' (.array (.prim .uint)) id <;> rfl

theorem eval_mlen_some (X : LTm C .mem) (t : LTm C (.ident (.array (.prim .uint))))
    {ℓ : PrimTy.uint.Denote} (h : ((LTm.app2 .mlen X t).eval g ν : Option PrimTy.uint.Denote) = some ℓ) :
    ∃ μ id r, X.eval g ν = some μ ∧ t.eval g ν = some id ∧
      HRef.ofId? μ.H' (.array (.prim .uint)) id = some r ∧ μ.heap.lenU r = ℓ := by
  rw [LTm.eval_app2, Op2.eval_eq_evalM] at h
  cases hX : X.eval g ν with
  | none => rw [hX] at h; cases h
  | some μ =>
    cases ht : t.eval g ν with
    | none => rw [hX, ht] at h; cases h
    | some id =>
      rw [hX, ht] at h
      change (HRef.ofId? μ.H' (.array (.prim .uint)) id).bind (fun r => some (μ.heap.lenU r)) =
        some ℓ at h
      cases hr : HRef.ofId? μ.H' (.array (.prim .uint)) id with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        exact ⟨μ, id, r, rfl, rfl, hr, Option.some.inj h⟩

theorem keccakWords_spec (rd : PrimTy.uint.Denote → Option PrimTy.uint.Denote) (k : Nat) :
    ∀ (i : Nat) (vs : List PrimTy.uint.Denote), keccakWords rd k i = some vs →
      vs.length = k ∧ ∀ (j : Nat) (hj : j < vs.length), rd (uintOfNat (i + j)) = some vs[j] := by
  induction k with
  | zero =>
    intro i vs h
    cases h
    exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro i vs h
    unfold keccakWords at h
    cases hv : rd (uintOfNat i) with
    | none => rw [hv] at h; cases h
    | some v =>
      rw [hv] at h
      cases hws : keccakWords rd k (i + 1) with
      | none => rw [hws] at h; cases h
      | some ws =>
        rw [hws] at h
        cases h
        obtain ⟨hlen, hall⟩ := ih (i + 1) ws hws
        refine ⟨by simp only [List.length_cons, hlen], ?_⟩
        intro j hj
        cases j with
        | zero => exact hv
        | succ j =>
          have := hall j (by simp only [List.length_cons] at hj; omega)
          rw [show i + (j + 1) = i + 1 + j by omega]
          exact this

theorem keccakAt_eval (k : HashKind) (X : LTm C .mem) (t : LTm C (.ident (.array (.prim .uint)))) :
    (keccakAt k X t).eval g ν = (LTm.app2 (.hash k) X t).eval g ν := by
  unfold keccakAt
  split
  · rename_i n hn
    split
    · split
      · rename_i vs hvs
        rw [LTm.eval_orElse]
        cases hL : ((LTm.seq (seqMemL X (lenAtN memFuel X t))
            (.lit (k.apply (vs.map (·.1))))).eval g ν : Option PrimTy.uint.Denote) with
        | none => rfl
        | some x =>
          show some x = _
          rw [LTm.eval_seq, seqMemL_eval, LTm.eval_seq] at hL
          cases hX : X.eval g ν with
          | none => rw [hX] at hL; cases hL
          | some μ =>
            rw [hX, Option.bind_some] at hL
            cases hℓ : ((lenAtN memFuel X t).eval g ν : Option PrimTy.uint.Denote) with
            | none => rw [hℓ] at hL; cases hL
            | some ℓ =>
              rw [hℓ] at hL
              simp only [Option.bind_some] at hL
              have hx : x = k.apply (vs.map (·.1)) := (Option.some.inj hL).symm
              have hℓn := LTm.litIn?_eval _ hn hℓ
              rw [lenAtN_eval memFuel X t μ hX] at hℓ
              obtain ⟨μ', id, r, hX', ht, hr, hlen⟩ := eval_mlen_some X t hℓ
              rw [hX] at hX'
              cases hX'
              obtain ⟨hvl, hall⟩ := keccakWords_spec _ _ 0 vs hvs
              -- the object's bytes are `vs`
              have hE : MObj.elems .dyn (μ.heap.get r) = vs := by
                have hl : (MObj.elems .dyn (μ.heap.get r)).length = n.1.toNat := by
                  have h1 : (μ.heap.lenU r).1 = ((μ.heap.len r .dyn : Nat) : Int) := rfl
                  rw [hlen, hℓn] at h1
                  unfold Heap.len at h1
                  omega
                apply List.ext_getElem (by rw [hl, hvl])
                intro j h1 h2
                have hrd := hall j h2
                rw [Nat.zero_add] at hrd
                have e := eval_read_mat (g := g) (ν := ν) X t (uintOfNat j) μ id hX ht
                rw [← memReadN_eval memFuel] at e
                rw [hr, Option.bind_some] at e
                unfold Heap.index at e
                have hj : (uintOfNat j).1.toNat = j := by
                  have hn256 := uint_lt n
                  have hjn : j < n.1.toNat := hl ▸ h1
                  rw [uintOfNat_val (by omega)]; rfl
                rw [hj, List.getElem?_eq_getElem h1] at e
                exact LTm.litIn?_eval _ hrd e
              rw [LTm.eval_app2, hX, ht, hx]
              show some (k.apply (vs.map (·.1))) = some (μ.hashId k _ id)
              unfold Grown.hashId
              rw [hr]
              show _ = some (k.apply (MObj.words _ (μ.heap.get r)))
              rw [← hE, MObj.elems_dyn]
              rfl
      · rfl
    · rfl
  · rfl

theorem keccakRes_eval (k : HashKind) {R : RefTy} (X : LTm C .mem) (t : LTm C (.ident R)) :
    (keccakRes k X t).eval g ν = (LTm.app2 (.hash k) X t).eval g ν := by
  unfold keccakRes
  split
  · exact keccakAt_eval k X _
  · rfl

end Keccak

/-! ## The pass -/

section Pass

variable {g : State C []} {ν : AEnv}

/-- **An identity minted over a memory, minted over its allocations**
(`LTm.stripW`, Lean only: solkey names it by a Skolem `freshIdp`): where
every word the memory's writes land on folds to `true` (`guardQ`,
`LTm.isTrueC`), the root of a copy over the memory is the root over it
without its writes, which no longer carries the writes before it; else the
identity is kept as it is, so that the copy's laws still see it. -/
def copyRes {R : RefTy} (h : (Ty.ref R).mapFree = true) (X : LTm C .mem)
    (S : LTm C (.sv (.ref R))) : LTm C (.ident R) :=
  let X' := X.stripW
  if X'.beqR X then .app2 (.copy h) X S
  else match guardQ X with
    | some cs => if cs.all LTm.isTrueC then .app2 (.copy h) X' S else .app2 (.copy h) X S
    | none => .app2 (.copy h) X S

theorem copyRes_eval {R : RefTy} (h : (Ty.ref R).mapFree = true) (X : LTm C .mem)
    (S : LTm C (.sv (.ref R))) :
    (copyRes h X S).eval g ν = (LTm.app2 (.copy h) X S).eval g ν := by
  unfold copyRes
  dsimp only
  split
  · rfl
  split
  · rename_i cs hq
    split
    · rename_i hall
      have hc : AllT g ν cs := fun c hc =>
        LTm.isTrueC_eval (List.all_eq_true.1 hall c hc)
      obtain ⟨μ, hX⟩ := Option.isSome_iff_exists.1 ((guardQ_sound hq).2 hc)
      exact LTm.copy_stripW_eval hX h S
    · rfl
  · rfl

theorem seqMemL_tt_eval {s : Srt} (d : LTm C s) :
    ((seqMemL d .tt).eval g ν : Option Bool) = (seqL d .tt).eval g ν := by
  rw [seqMemL_eval, LTm.eval_seq, seqL_eval]

/-- A binary symbol, its reads of memory walked. -/
def _root_.Solidity.Op2.memRes {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    LTm C s :=
  match o, x, y with
  | .read, X, b => wrapG b.hoistA.1 (memReadN memFuel X b.hoistA.2)
  | .iread, X, b => wrapG b.hoistA.1 (memIReadN memFuel X b.hoistA.2)
  | .mlen, X, t => wrapG t.peel.1 (seqMemL X (lenAtN memFuel X t.peel.2))
  | .hash k, X, t => keccakRes k X t
  | .copy h, X, S => copyRes h X S
  | o, x, y => .app2 o x y

theorem Op2.memRes_eval {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    (o.memRes x y).eval g ν = (LTm.app2 o x y).eval g ν := by
  cases o
  case read =>
    simp only [Op2.memRes]
    rw [LTm.app2_hoistA .read rfl x y]
    exact wrapG_congr _ (memReadN_eval _ x _)
  case iread =>
    simp only [Op2.memRes]
    rw [LTm.app2_hoistA .iread rfl x y]
    exact wrapG_congr _ (memIReadN_eval _ x _)
  case mlen =>
    simp only [Op2.memRes]
    rw [LTm.app2_peel .mlen rfl x y]
    refine wrapG_congr _ ?_
    rw [seqMemL_eval, LTm.eval_seq]
    cases hx : (x.eval g ν : Option (Grown g.H (fun _ => Unit))) with
    | none => rw [LTm.eval_app2_none _ _ _ hx]; rfl
    | some μ => exact lenAtN_eval memFuel x _ μ hx
  case hash k => simp only [Op2.memRes]; exact keccakRes_eval k x y
  case copy h => simp only [Op2.memRes]; exact copyRes_eval h x y
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

theorem LTm.seqMem_eq_seqMemM {s : Srt} (t : LTm C s) : t.seqMem = t.seqMemM := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih | obsW x ih | obsL x ih | obsH x ih => simp only [LTm.seqMemM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.seqMemM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [LTm.seqMemM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [LTm.seqMemM, ← ihq, ← ihi]; rfl
  | seq d a ihd iha => simp only [LTm.seqMemM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [LTm.seqMemM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [LTm.seqMemM, ← iha, ← ihb, ← iht, ← ihe]; rfl

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
  | .eq a b => .eq (({} : Facts C).nf a).memRes.seqMem (({} : Facts C).nf b).memRes.seqMem
  | .not φ => .not φ.memResM
  | .and φ ψ => .and φ.memResM ψ.memResM
  | .imp φ ψ => .imp φ.memResM ψ.memResM
  | .all k p φ => .all k p φ.memResM

/-- **Every read of memory in a formula walked.**  By the recursor. -/
@[implemented_by LFml.memResM]
def LFml.memRes (φ : LFml C) : LFml C :=
  @LFml.rec C (fun _ => LFml C) .tt
    (@fun _ a b => .eq (({} : Facts C).nf a).memRes.seqMem (({} : Facts C).nf b).memRes.seqMem)
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
    show (LFml.eq (({} : Facts C).nf a).memRes.seqMem
      (({} : Facts C).nf b).memRes.seqMem).holds g ν ↔ _
    rw [LFml.holds_eq_iff, LFml.holds_eq_iff, LTm.seqMem_eval, LTm.seqMem_eval, LTm.memRes_eval,
      LTm.memRes_eval, Facts.nf_eval (Facts.ok_empty ν), Facts.nf_eval (Facts.ok_empty ν)]
  | not φ ih => intro ν; exact not_congr (ih ν)
  | and φ ψ ihφ ihψ => intro ν; exact and_congr (ihφ ν) (ihψ ν)
  | imp φ ψ ihφ ihψ => intro ν; exact imp_congr (ihφ ν) (ihψ ν)
  | all k p φ ih => intro ν; exact forall_congr' fun v => ih _

theorem LFml.memRes_valid {φ : LFml C} (h : φ.memRes.Valid) : φ.Valid :=
  fun g ν => (LFml.memRes_holds φ ν).1 (h g ν)

end Pass

/-- A read of a storage term the elimination did not take: `find`, `len`,
`sfind`. -/
def _root_.Solidity.Op2.isStRd {a b s : Srt} : Op2 C a b s → Bool
  | .find | .len | .sfind => true
  | _ => false

/-- `LTm.hasStRd`'s compiled twin. -/
def LTm.hasStRdM : {s : Srt} → LTm C s → Bool
  | _, .app1 _ x => x.hasStRdM
  | _, .app2 o x y => o.isStRd || x.hasStRdM || y.hasStRdM
  | _, .app3 _ x y z => x.hasStRdM || y.hasStRdM || z.hasStRdM
  | _, .index _ q i => q.hasStRdM || i.hasStRdM
  | _, .seq d a => d.hasStRdM || a.hasStRdM
  | _, .orElse a b => a.hasStRdM || b.hasStRdM
  | _, .kite a b t e => a.hasStRdM || b.hasStRdM || t.hasStRdM || e.hasStRdM
  | _, _ => false

/-- **A term with a storage read left**: one the walk of memory exposed
(a member of a copy of storage) for the elimination to take.  By the
recursor. -/
@[implemented_by LTm.hasStRdM]
def LTm.hasStRd {s : Srt} (t : LTm C s) : Bool :=
  @LTm.rec C (fun _ _ => Bool)
    (@fun _ _ => false) (@fun _ _ => false)
    (@fun _ _ _ _ ihx => ihx)
    (@fun _ _ _ o _ _ ihx ihy => o.isStRd || ihx || ihy)
    (@fun _ _ _ _ _ _ _ _ ihx ihy ihz => ihx || ihy || ihz)
    (@fun _ _ _ _ _ _ ihq ihi => ihq || ihi)
    (@fun _ _ _ => false) (@fun _ _ _ => false) (@fun _ _ _ => false)
    (@fun _ _ _ _ ihd iha => ihd || iha)
    (@fun _ _ _ iha ihb => iha || ihb)
    (@fun _ _ _ _ _ _ iha ihb iht ihe => iha || ihb || iht || ihe)
    (@fun _ => false) s t

theorem LTm.hasStRd_eq_hasStRdM {s : Srt} (t : LTm C s) : t.hasStRd = t.hasStRdM := by
  induction t with
  | var | app0 | obsW | obsL | obsH | err => rfl
  | app1 o x ih => simp only [LTm.hasStRdM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.hasStRdM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [LTm.hasStRdM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [LTm.hasStRdM, ← ihq, ← ihi]; rfl
  | seq d a ihd iha => simp only [LTm.hasStRdM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [LTm.hasStRdM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [LTm.hasStRdM, ← iha, ← ihb, ← iht, ← ihe]; rfl

/-- `LFml.hasStRd`'s compiled twin. -/
def LFml.hasStRdM : LFml C → Bool
  | .eq a b => a.hasStRd || b.hasStRd
  | .not φ => φ.hasStRdM
  | .and φ ψ | .imp φ ψ => φ.hasStRdM || ψ.hasStRdM
  | .all _ _ φ => φ.hasStRdM
  | .tt => false

/-- A formula with a storage read left.  By the recursor. -/
@[implemented_by LFml.hasStRdM]
def LFml.hasStRd (φ : LFml C) : Bool :=
  @LFml.rec C (fun _ => Bool) false (@fun _ a b => a.hasStRd || b.hasStRd)
    (fun _ ih => ih) (fun _ _ ihφ ihψ => ihφ || ihψ) (fun _ _ ihφ ihψ => ihφ || ihψ)
    (fun _ _ _ ih => ih) φ

theorem LFml.hasStRd_eq_hasStRdM (φ : LFml C) : φ.hasStRd = φ.hasStRdM := by
  induction φ with
  | tt | eq => rfl
  | not φ ih | all k p φ ih => simp only [LFml.hasStRdM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [LFml.hasStRdM, ← ihφ, ← ihψ]; rfl

/-- The storage reads a walk of memory exposed (a member of a copy of
storage, a guard of a copy's source) eliminated once more (`LFml.elim`),
and memory walked again. -/
def LFml.memElim (φ : LFml C) : LFml C :=
  if φ.hasStRd then φ.elim.memRes else φ

theorem LFml.memElim_valid {φ : LFml C} (h : φ.memElim.Valid) : φ.Valid := by
  unfold LFml.memElim at h
  split at h
  · exact fun g ν => (LFml.elim_holds g φ ν).1 (LFml.memRes_valid h g ν)
  · exact h

/-- **The closer with memory read**: every read of memory walked
(`LFml.memRes`), the storage reads that walk exposed eliminated and the
memory walked again (`LFml.memElim`), then `LFml.close`; where that does
not close, once more, for the reads the second walk exposed (the guards
of a copy's source on a word read below the copy's root). -/
def LFml.closeMem (φ : LFml C) : Bool := closeTwice φ.memRes.memElim
where
  /-- `ψ` closed, or closed after one more elimination. -/
  closeTwice (ψ : LFml C) : Bool := ψ.close || (ψ.hasStRd && ψ.memElim.close)

theorem LFml.closeMem_valid {φ : LFml C} (h : φ.closeMem = true) : φ.Valid := by
  unfold LFml.closeMem LFml.closeMem.closeTwice at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact LFml.memRes_valid (LFml.memElim_valid (LFml.close_valid h))
  · exact LFml.memRes_valid (LFml.memElim_valid (LFml.memElim_valid
      (LFml.close_valid (Bool.and_eq_true_iff.1 h).2)))

/-! ## Before the elimination -/

section Fold

variable {g : State C []}

/-- `LFml.nfE`'s compiled twin. -/
def LFml.nfEM : LFml C → LFml C
  | .tt => .tt
  | .eq a b => .eq (({} : Facts C).nf a) (({} : Facts C).nf b)
  | .not φ => .not φ.nfEM
  | .and φ ψ => .and φ.nfEM ψ.nfEM
  | .imp φ ψ => .imp φ.nfEM ψ.nfEM
  | .all k p φ => .all k p φ.nfEM

/-- **Every term in its normal form with no premise**: literals folded, so
that the elimination compares keys it can (`keyCmp`).  By the recursor. -/
@[implemented_by LFml.nfEM]
def LFml.nfE (φ : LFml C) : LFml C :=
  @LFml.rec C (fun _ => LFml C) .tt
    (@fun _ a b => .eq (({} : Facts C).nf a) (({} : Facts C).nf b))
    (fun _ ih => .not ih) (fun _ _ ihφ ihψ => .and ihφ ihψ) (fun _ _ ihφ ihψ => .imp ihφ ihψ)
    (fun k p _ ih => .all k p ih) φ

theorem LFml.nfE_eq_nfEM (φ : LFml C) : φ.nfE = φ.nfEM := by
  induction φ with
  | tt | eq => rfl
  | not φ ih | all k p φ ih => simp only [LFml.nfEM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [LFml.nfEM, ← ihφ, ← ihψ]; rfl

theorem LFml.nfE_holds (φ : LFml C) : ∀ (ν : AEnv), φ.nfE.holds g ν ↔ φ.holds g ν := by
  induction φ with
  | tt => intro ν; exact Iff.rfl
  | eq a b =>
    intro ν
    show (LFml.eq (({} : Facts C).nf a) (({} : Facts C).nf b)).holds g ν ↔ _
    rw [LFml.holds_eq_iff, LFml.holds_eq_iff, Facts.nf_eval (Facts.ok_empty ν),
      Facts.nf_eval (Facts.ok_empty ν)]
  | not φ ih => intro ν; exact not_congr (ih ν)
  | and φ ψ ihφ ihψ => intro ν; exact and_congr (ihφ ν) (ihψ ν)
  | imp φ ψ ihφ ihψ => intro ν; exact imp_congr (ihφ ν) (ihψ ν)
  | all k p φ ih => intro ν; exact forall_congr' fun v => ih _

/-- **`sol_decide` on a reduction**: its terms folded (`LFml.nfE`), the
reads of writes eliminated under its premises (`LFml.elimF`), memory read and closed
(`LFml.closeMem`). -/
def LFml.decideMem (φ : LFml C) : Bool := (φ.nfE.elimF {}).closeMem

theorem LFml.decideMem_valid {φ : LFml C} (h : φ.decideMem = true) : φ.Valid := fun g ν =>
  (LFml.nfE_holds φ ν).1 ((LFml.elimF_holds g φ.nfE {} ν (Facts.ok_empty ν)).1
    (LFml.closeMem_valid h g ν))

end Fold

end Decide

end Solidity
