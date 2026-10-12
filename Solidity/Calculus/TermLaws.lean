import Solidity.Calculus.TermLib
import Solidity.Calculus.SeqRewrite
import Solidity.Calculus.StateFacts

/-!
# The term laws at an update's right-hand sides, scoped

solkey's term laws, read on the scoped terms `Tm C Γ s` (`Calculus/Fml.lean`)
and the scoped updates `Upd C Γ Δ`, over `State C Γ`: what makes each exact
inside an update's right-hand sides, under either modality.  A law `t ⇝ t'`
rewrites there when the right side returns what the left side does
(`Tm.EvalRefinesAt`), and, wherever the update returns, the left side
returns what the right side does: the update holds the write the law reads
back.  `LawCov` bundles the two with the syntactic check that gives the
second, decided by `rfl`.

* **The literal laws** (`LitLaw`): KeY's `*_literals` taclets, exact
  everywhere (`LitLaw.exact`), at their typed literals: each side condition
  is the operator's typed evaluation (`BinOp.evalT`), its range check
  included.
* **A storage law onto a literal** (`LawCov.findOnSave`):
  `find(save(s, p, sval(w)), p)` over `storage := save(s, p, sval(w))`.
* **Two member-wise forms of one read** (`LawCov.findMemberCons`):
  `find(s, r.p)` and `find(select(s, r), p)` return alike in every state
  (`Storage.find_selectT`).

**Typed sorts** (W9.8.3c).  A term reads the typed state directly
(`Tm.eval`), so the laws are proved on the typed storage
(`Storage.findOnSave`, `Storage.find_selectT`), with no erased state.  Not
ported yet (`docs/intrinsic.md`, W9.8.3c laws record): the frame and
delete-value laws past an update (`TermTaclet.RefLaw`, `Upd.coversRef`),
which need the typed frame laws of a delete, a push and a pop and a shape's
divergence read as `Path.Diverges`; the memory laws (`EvalLaw`,
`Upd.coversEval`) on the `Grown` heap; and the member-wise reads of a write
under a `select` (`Tm.baseAny`).
-/

namespace Solidity

open Theory Theory.StValue
open Solidity (Srt Op0 Op1 Op2 Op3)

variable {C : Contract} {Γ : Ctx}

/-! ## Refinement of evaluation -/

/-- Where `t` returns, `t'` returns the same, in every state (at any sort). -/
def Tm.EvalRefinesAt {u : Srt} (t t' : Tm C Γ u) : Prop :=
  ∀ σ : State C Γ, OLe (t.eval σ) (t'.eval σ)

/-- **A Theory equation onto a literal refines evaluation**, at any scope
(`Tm.EvalRefines.of_theq`): where `t` returns `x` it denotes `x`
(`Tm.denote_eval`), and the literal returns what it denotes. -/
theorem Tm.evalRefinesAt_of_theq {P : PrimTy} {t t' : Tm C Γ (.val P)} (h : Tm.Theq t t')
    (ht : t'.isLit = true) : Tm.EvalRefinesAt t t' := fun σ x hx => by
  have e := h σ
  rw [Tm.denote_eval σ t x hx] at e
  cases hl : t'.litVal? with
  | none => simp only [Tm.isLit, hl, Option.isSome_none, Bool.false_eq_true] at ht
  | some v =>
    obtain rfl := Tm.eq_of_litVal? hl
    have e : StValue.prim (PrimTy.erase v) = .prim (PrimTy.erase x) :=
      (Theory.StValue.Equiv.prim_iff.1 e.symm)
    rw [PrimTy.erase_injective (StValue.prim.inj e)]
    rfl

/-! ## The literal laws -/

/-- KeY's `*_literals` taclets, as the typed evaluator computes them: the
side condition is the operator's typed evaluation of the two literals,
which decides the range check.  Hover a constructor for the taclet. -/
inductive LitLaw : {P : PrimTy} → Tm C Γ (.val P) → Tm C Γ (.val P) → Prop
  /-- **`add_literals`**: `a + b ⇝ a + b` folded, in `uint` range. -/
  | add_literals {a b c : PrimTy.uint.Denote} (h : BinOp.add.evalT a b = some c := by decide) :
      LitLaw (Tms.Term.binop .add .uint (Tms.Term.lit a) (Tms.Term.lit b)) (Tms.Term.lit c)
  /-- **`sub_literals`**: `a - b ⇝ a - b` folded, in `uint` range. -/
  | sub_literals {a b c : PrimTy.uint.Denote} (h : BinOp.sub.evalT a b = some c := by decide) :
      LitLaw (Tms.Term.binop .sub .uint (Tms.Term.lit a) (Tms.Term.lit b)) (Tms.Term.lit c)
  /-- **`leq_literals`**: `a <= b ⇝ true` or `false`. -/
  | leq_literals {a b : PrimTy.uint.Denote} {c : Bool} (h : BinOp.le.evalT a b = some c := by decide) :
      LitLaw (Tms.Term.binop .le .uint (Tms.Term.lit a) (Tms.Term.lit b)) (Tms.Term.litB c)
  /-- **`less_literals`**: `a < b ⇝ true` or `false`. -/
  | less_literals {a b : PrimTy.uint.Denote} {c : Bool} (h : BinOp.lt.evalT a b = some c := by decide) :
      LitLaw (Tms.Term.binop .lt .uint (Tms.Term.lit a) (Tms.Term.lit b)) (Tms.Term.litB c)
  /-- **`greater_literals`**: `a > b ⇝ true` or `false`. -/
  | greater_literals {a b : PrimTy.uint.Denote} {c : Bool}
      (h : BinOp.gt.evalT a b = some c := by decide) :
      LitLaw (Tms.Term.binop .gt .uint (Tms.Term.lit a) (Tms.Term.lit b)) (Tms.Term.litB c)
  /-- **`geq_literals`**: `a >= b ⇝ true` or `false`. -/
  | geq_literals {a b : PrimTy.uint.Denote} {c : Bool} (h : BinOp.ge.evalT a b = some c := by decide) :
      LitLaw (Tms.Term.binop .ge .uint (Tms.Term.lit a) (Tms.Term.lit b)) (Tms.Term.litB c)
  /-- **`div_literals`**: `a / b ⇝ a / b` folded (truncated, as Solidity divides), the divisor not
  zero. -/
  | div_literals {a b c : PrimTy.uint.Denote} (h : BinOp.div.evalT a b = some c := by decide) :
      LitLaw (Tms.Term.binop .div .uint (Tms.Term.lit a) (Tms.Term.lit b)) (Tms.Term.lit c)

/-- **A literal law is exact**: its right side is a literal, which its left
side returns in every state. -/
theorem LitLaw.exact {P : PrimTy} {t t' : Tm C Γ (.val P)} :
    LitLaw t t' → ∃ v, t' = Tms.Term.lit v ∧ ∀ σ : State C Γ, t.eval σ = some v
  | @LitLaw.add_literals _ _ a b c h => ⟨c, rfl, fun _ => (binopT_some .add a b).trans h⟩
  | @LitLaw.sub_literals _ _ a b c h => ⟨c, rfl, fun _ => (binopT_some .sub a b).trans h⟩
  | @LitLaw.leq_literals _ _ a b c h => ⟨c, rfl, fun _ => (binopT_some .le a b).trans h⟩
  | @LitLaw.less_literals _ _ a b c h => ⟨c, rfl, fun _ => (binopT_some .lt a b).trans h⟩
  | @LitLaw.greater_literals _ _ a b c h => ⟨c, rfl, fun _ => (binopT_some .gt a b).trans h⟩
  | @LitLaw.geq_literals _ _ a b c h => ⟨c, rfl, fun _ => (binopT_some .ge a b).trans h⟩
  | @LitLaw.div_literals _ _ a b c h => ⟨c, rfl, fun _ => (binopT_some .div a b).trans h⟩

/-- The two sides of a literal law evaluate alike in every state. -/
theorem LitLaw.evalEq {P : PrimTy} {t t' : Tm C Γ (.val P)} (r : LitLaw t t') (σ : State C Γ) :
    t.eval σ = t'.eval σ := by
  obtain ⟨v, rfl, hv⟩ := r.exact
  rw [hv σ]
  rfl

/-- The two sides of a literal law denote alike in the Theory. -/
theorem LitLaw.theq {P : PrimTy} {t t' : Tm C Γ (.val P)} (r : LitLaw t t') : Tm.Theq t t' := by
  obtain ⟨v, rfl, hv⟩ := r.exact
  intro σ
  rw [Tm.denote_eval σ t v (hv σ)]
  exact Theory.StValue.Equiv.refl _

/-! ## What an update's elements write -/

/-- The storage terms an element writes the storage with. -/
def UpdElem.storTerms {Δ : Ctx} : UpdElem C Γ Δ → List (Tm C Γ .st)
  | .storage s => [s]
  | _ => []

/-- The right-hand sides of an update's `storage :=` elements. -/
def Upd.storTerms : {Δ : Ctx} → Upd C Γ Δ → List (Tm C Γ .st)
  | _, .nil => []
  | _, .snoc U e => U.storTerms ++ e.storTerms
  | _, .decl U _ _ => U.storTerms
  | _, .pop U _ => U.storTerms
  | _, .drop U _ => U.storTerms

/-- **A storage write that is an element of an update that returns,
returns.** -/
theorem Upd.storage_eval_of_globT {σ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    {g : GlobT C σ.H} → U.globT σ = some g → ∀ s ∈ U.storTerms, ∃ st, s.eval σ = some st
  | _, .nil, _, _ => fun _ h => nomatch h
  | _, .snoc U e, g, h => by
    change (U.globT σ).bind (e.globT σ) = some g at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨g₀, hU, hw⟩ := h
    intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · exact Upd.storage_eval_of_globT U hU s hs
    · cases e with
      | storage s' =>
        simp only [UpdElem.storTerms, List.mem_singleton] at hs
        subst hs
        rw [UpdElem.globT_eq_globTM] at hw
        simp only [UpdElem.globTM, Option.bind_eq_some_iff] at hw
        obtain ⟨st, hst, -⟩ := hw
        exact ⟨st, hst⟩
      | _ => nomatch hs
  | _, .decl U _ r, g, h => by
    change (U.globT σ).bind (fun g => (r.eval σ).bind fun _ => some g) = some g at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨g₀, hU, -⟩ := h
    exact Upd.storage_eval_of_globT U hU
  | _, .pop U _, _, h | _, .drop U _, _, h => Upd.storage_eval_of_globT U h

/-! ## A storage law onto a literal

`{ storage := save(storage, p, 10) ‖ x := find(save(storage, p, 10), p) }`
halts exactly where `save(storage, p, 10)` does, and so does
`{ storage := save(storage, p, 10) ‖ x := 10 }`: the read returns wherever the
write it reads back does (`Storage.findOnSave`), and the write is an
element of the update. -/

section FindOnSave

variable {P : PrimTy} (s : Tm C Γ .st) (p : Tm C Γ (.path (.prim P))) (w : P.Denote)

/-- `save(s, p, sval(w))`. -/
abbrev Tm.saveLit : Tm C Γ .st := Tms.STerm.save s p (Tms.SValT.val (Tms.Term.lit w))

/-- `find(save(s, p, sval(w)), p)`. -/
abbrev Tm.findSaveLit : Tm C Γ (.val P) := Tms.Term.find (Tm.saveLit s p w) p

/-- A word written, read back where the write lands: what the read returns
is the word (`Storage.findOnSave`). -/
theorem Tm.findSaveLit_eval_of_save {σ : State C Γ} {st' : Storage C}
    (h : (Tm.saveLit s p w).eval σ = some st') : (Tm.findSaveLit s p w).eval σ = some w := by
  have h' : ((s.eval σ).bind fun st => (p.eval σ).bind fun r => st.write r (.prim w)) = some st' := by
    have h₀ : (Tm.saveLit s p w).eval σ =
        ((s.eval σ).bind fun st => (p.eval σ).bind fun r => (some (SVal.prim w)).bind fun v =>
          st.write r v) := rfl
    rw [h₀] at h
    exact h
  obtain ⟨st, hs, h'⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨r, hr, h'⟩ := Option.bind_eq_some_iff.1 h'
  have hf := Storage.findOnSave st r w h'
  show ((Tm.saveLit s p w).eval σ).bind (fun st => (p.eval σ).bind fun r =>
    (st.find r).bind fun v => some v.view) = _
  rw [h, Option.bind_some, hr, Option.bind_some, hf, Option.bind_some]
  rfl

/-- The read of a word written returns the word, where it returns. -/
theorem Tm.findSaveLit_fwd : Tm.EvalRefinesAt (Tm.findSaveLit s p w) (Tms.Term.lit w) := by
  intro σ x hx
  have h : ((Tm.saveLit s p w).eval σ).bind (fun st => (p.eval σ).bind fun r =>
      (st.find r).bind fun v => some v.view) = some x := hx
  obtain ⟨st', hst', -⟩ := Option.bind_eq_some_iff.1 h
  rw [Tm.findSaveLit_eval_of_save s p w hst'] at hx
  exact hx

end FindOnSave

/-! ## Two member-wise forms of one read

solkey reads a path from its head (`findMemberCons`): `find(s, alice.age)` is
`find(select(s, alice), age)`.  On the typed storage `select(s, r)` is the
struct at `r` read as a storage of its members (`Storage.selectT`), so the
two reads return alike in every state (`Storage.find_selectT`). -/

/-- `r.f` is `f` under `select(s, r)`. -/
theorem SRef.ofRoot_field_under {r f sn : Name} {T : Ty}
    (hr : C.rootType r = some (.ref (.struct sn))) (hf : C.fieldType sn f = some T) :
    (SRef.ofRoot r hr).field hf = SRef.under (SRef.ofRoot (C := Contract.ofStruct sn) f hf) hr := by
  simp only [SRef.field, SRef.append, SRef.ofRoot, SRef.under, Path.append_nil]

/-- A member after a path under `select(s, r)` is that member under it. -/
theorem SRef.under_field {r s sn f : Name} {T : Ty} (hf : C.fieldType sn f = some T)
    (q : SRef (Contract.ofStruct s) (.ref (.struct sn)))
    (hr : C.rootType r = some (.ref (.struct s))) :
    (q.under hr).field hf = (q.field (C := Contract.ofStruct s) hf).under hr := by
  simp only [SRef.field, SRef.append, SRef.under, Path.append_field]

/-- What `shift?` gives reads, from the root, the path it shifted. -/
def Srt.ShiftEval' (σ : State C Γ) : (u : Srt) → u.ShiftD C Γ → Option (u.Den C σ.H) → Prop
  | .path _, sh, x => x = (sh.p.eval σ).map fun q => q.under sh.h
  | _, _, _ => True

/-- What `shift?` gives, if anything, reads the path it shifted. -/
def Srt.ShiftEval (σ : State C Γ) (u : Srt) (o : Option (u.ShiftD C Γ))
    (x : Option (u.Den C σ.H)) : Prop :=
  ∀ sh, o = some sh → Srt.ShiftEval' σ u sh x

theorem Tm.shift?_eval (σ : State C Γ) {u : Srt} (p : Tm C Γ u) :
    Srt.ShiftEval σ u p.shift? (p.eval σ) := by
  induction p with
  | app1 o x ih =>
    cases o with
    | field hf =>
      rename_i sn f T
      intro sh h
      have h : (match x.rootOf? with
        | some ⟨r, hr⟩ => some ⟨r, sn, hr, .app0 (.member sn f hf)⟩
        | none => x.shift?.map fun sh => ⟨sh.r, sh.sn, sh.h, .app1 (.fieldIn hf) sh.p⟩) =
          some sh := h
      cases hx : x.rootOf? with
      | some rr =>
        rw [hx] at h
        obtain ⟨r, hr⟩ := rr
        cases h
        have he : x.eval σ = some (SRef.ofRoot r hr) := by
          cases x with
          | app0 o =>
            cases o with
            | root r' hr' => cases hx; rfl
            | _ => cases hx
          | _ => cases hx
        show (x.eval σ).map (·.field hf) = some ((SRef.ofRoot (C := Contract.ofStruct sn) f hf).under hr)
        rw [he, Option.map_some, SRef.ofRoot_field_under]
      | none =>
        rw [hx] at h
        obtain ⟨sh', hs, rfl⟩ := Option.map_eq_some_iff.1 h
        have ih : x.eval σ = (sh'.p.eval σ).map fun q => q.under sh'.h := ih sh' hs
        show (x.eval σ).map (·.field hf) = ((sh'.p.eval σ).map (·.field hf)).map _
        rw [ih]
        cases sh'.p.eval σ with
        | none => rfl
        | some q =>
          simp only [Option.map_some]
          exact congrArg some (SRef.under_field hf q sh'.h)
    | _ => intro sh h; cases h
  | _ => intro sh h; cases h

/-- **`findMemberCons`, in a run**: `find(s, r.p)` and `find(select(s, r), p)`
return alike in every state. -/
theorem Tm.findMemberCons_eval {s : Tm C Γ .st} {P : PrimTy} {p : Tm C Γ (.path (.prim P))}
    {r sn : Name} {hr : C.rootType r = some (.ref (.struct sn))}
    {p' : Tm C Γ (.spath sn (.prim P))} (h : p.shift? = some ⟨r, sn, hr, p'⟩) (σ : State C Γ) :
    (Tms.Term.find s p).eval σ = (Tm.app2 .findIn (Tms.STerm.select s r hr) p').eval σ := by
  have hp : p.eval σ = (p'.eval σ).map fun q => q.under hr := Tm.shift?_eval σ p _ h
  show ((s.eval σ).bind fun st => (p.eval σ).bind fun q => (st.find q).bind fun v => some v.view) =
    (((s.eval σ).map fun st => st.selectT hr).bind fun st => (p'.eval σ).bind fun q =>
      (st.find q).bind fun v => some v.view)
  rw [hp]
  cases s.eval σ with
  | none => rfl
  | some st =>
    cases p'.eval σ with
    | none => rfl
    | some q =>
      simp only [Option.bind_some, Option.map_some, Storage.find_selectT]

/-! ## The storage's frame, typed

solkey's frame laws (`findOnSaveFrame`, `findOnDelAtFrame`, `lenOn*Frame`)
read on the typed storage: a write, a delete, a push and a pop are each a
`Storage.save` at their reference (`Storage.write_some`, `delete_save`,
`push_save`, `pop_save`), and a save leaves what a reference that parts from
it reads (`Storage.find_save_frame`; the Theory's `diverges` read as
`Path.Diverges`, `Path.diverges_of_erase`), and an array's length where it
writes below one of its elements (`Storage.len_save_frame`). -/

section Frame

/-- **Two typed paths whose segments part, part** (`Path.Diverges`): the
Theory's `diverges` on the erased segments.  At one source type the two
paths take the same constructor at each step. -/
theorem Path.diverges_of_erase {T U W : Ty} (p : Path T U) (q : Path T W)
    (h : Theory.StValue.diverges p.erase q.erase = true) : Path.Diverges p q := by
  induction p generalizing W with
  | nil => simp only [Path.erase, Theory.StValue.diverges, Bool.false_eq_true] at h
  | @field s f T₁ U₁ hf p ih =>
    cases q with
    | nil => simp only [Path.erase, Theory.StValue.diverges, Bool.false_eq_true] at h
    | @field _ f' T₂ _ hf' q =>
      by_cases e : f = f'
      · subst e
        obtain rfl : T₁ = T₂ := Option.some.inj (hf.symm.trans hf')
        simp only [Path.erase, Theory.StValue.diverges, if_pos rfl] at h
        exact .fieldIn hf (ih q h)
      · exact .field hf hf' p q e
  | @«at» E U₁ i p ih =>
    cases q with
    | nil => simp only [Path.erase, Theory.StValue.diverges, Bool.false_eq_true] at h
    | «at» j q =>
      by_cases e : i = j
      · subst e
        simp only [Path.erase, Theory.StValue.diverges, if_pos rfl] at h
        exact .atIn i (ih q h)
      · exact .at p q e
  | @atF E U₁ n i p ih =>
    cases q with
    | nil => simp only [Path.erase, Theory.StValue.diverges, Bool.false_eq_true] at h
    | atF j q =>
      by_cases e : i = j
      · subst e
        simp only [Path.erase, Theory.StValue.diverges, if_pos rfl] at h
        exact .atFIn i (ih q h)
      · exact .atF p q e
  | @key K V U₁ k p ih =>
    cases q with
    | nil => simp only [Path.erase, Theory.StValue.diverges, Bool.false_eq_true] at h
    | key k' q =>
      by_cases e : k = k'
      · subst e
        simp only [Path.erase, Theory.StValue.diverges, if_pos rfl] at h
        exact .keyIn k (ih q h)
      · exact .key p q e

/-- Two typed paths from one type with one erasure are one path. -/
theorem Path.heq_of_erase {T U W : Ty} (p : Path T U) (q : Path T W) (h : p.erase = q.erase) :
    U = W ∧ HEq p q := by
  induction p generalizing W with
  | nil =>
    cases q with
    | nil => exact ⟨rfl, HEq.rfl⟩
    | _ => simp only [Path.erase, reduceCtorEq] at h
  | @field s f T₁ U₁ hf p ih =>
    cases q with
    | nil => simp only [Path.erase, reduceCtorEq] at h
    | @field _ f' T₂ _ hf' q =>
      simp only [Path.erase, List.cons.injEq, Semantics.Seg.field.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain rfl : T₁ = T₂ := Option.some.inj (hf.symm.trans hf')
      obtain ⟨rfl, e⟩ := ih q h
      cases e
      exact ⟨rfl, HEq.rfl⟩
  | @«at» E U₁ i p ih =>
    cases q with
    | nil => simp only [Path.erase, reduceCtorEq] at h
    | «at» j q =>
      simp only [Path.erase, List.cons.injEq, Semantics.Seg.at.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, e⟩ := ih q h
      cases e
      exact ⟨rfl, HEq.rfl⟩
  | @atF E U₁ n i p ih =>
    cases q with
    | nil => simp only [Path.erase, reduceCtorEq] at h
    | atF j q =>
      simp only [Path.erase, List.cons.injEq, Semantics.Seg.at.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, e⟩ := ih q h
      cases e
      exact ⟨rfl, HEq.rfl⟩
  | @key K V U₁ k p ih =>
    cases q with
    | nil => simp only [Path.erase, reduceCtorEq] at h
    | key k' q =>
      simp only [Path.erase, List.cons.injEq, Semantics.Seg.at.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, e⟩ := ih q h
      cases e
      exact ⟨rfl, HEq.rfl⟩

/-- A typed path whose erasure extends another's, from one type, is the
other followed by a path. -/
theorem Path.split_of_erase {T U W : Ty} (p : Path T U) (q : Path T W) {s : List Semantics.Seg}
    (h : q.erase = p.erase ++ s) : ∃ r : Path U W, q = p.append r ∧ r.erase = s := by
  induction p generalizing W with
  | nil => exact ⟨q, (Path.append_nil q).symm, h⟩
  | @field s₀ f T₁ U₁ hf p ih =>
    cases q with
    | nil => simp only [Path.erase, List.cons_append, reduceCtorEq] at h
    | @field _ f' T₂ _ hf' q =>
      simp only [Path.erase, List.cons_append, List.cons.injEq, Semantics.Seg.field.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain rfl : T₁ = T₂ := Option.some.inj (hf.symm.trans hf')
      obtain ⟨r, rfl, hr⟩ := ih q h
      exact ⟨r, (Path.append_field hf p r).symm, hr⟩
  | @«at» E U₁ i p ih =>
    cases q with
    | nil => simp only [Path.erase, List.cons_append, reduceCtorEq] at h
    | «at» j q =>
      simp only [Path.erase, List.cons_append, List.cons.injEq, Semantics.Seg.at.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨r, rfl, hr⟩ := ih q h
      exact ⟨r, (Path.append_at _ p r).symm, hr⟩
  | @atF E U₁ n i p ih =>
    cases q with
    | nil => simp only [Path.erase, List.cons_append, reduceCtorEq] at h
    | atF j q =>
      simp only [Path.erase, List.cons_append, List.cons.injEq, Semantics.Seg.at.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨r, rfl, hr⟩ := ih q h
      exact ⟨r, (Path.append_atF _ p r).symm, hr⟩
  | @key K V U₁ k p ih =>
    cases q with
    | nil => simp only [Path.erase, List.cons_append, reduceCtorEq] at h
    | key k' q =>
      simp only [Path.erase, List.cons_append, List.cons.injEq, Semantics.Seg.at.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨r, rfl, hr⟩ := ih q h
      exact ⟨r, (Path.append_key _ p r).symm, hr⟩

/-- A save below a path is a save at the path of the value found there,
saved below. -/
theorem SVal.saveM_append {T U W : Ty} (x : SVal T) (p : Path T U) (r : Path U W) (v : SVal W)
    {x' : SVal T} (h : x.saveM (p.append r) v = some x') :
    ∃ y y', x.findM p = some y ∧ y.saveM r v = some y' ∧ x.saveM p y' = some x' := by
  induction p with
  | nil => exact ⟨x, x', by cases x <;> rfl, by rw [Path.append_nil] at h; exact h, by cases x <;> rfl⟩
  | @field s f T₁ U₁ hf p ih =>
    cases x with
    | struct fs =>
      simp only [Path.append_field, SVal.saveM, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      obtain ⟨y, y', hy, hy', hz'⟩ := ih (fs.get hf) r hz
      refine ⟨y, y', ?_, hy', ?_⟩
      · simp only [SVal.findM]; exact hy
      · simp only [SVal.saveM, hz', Option.bind_eq_bind, Option.bind_some]
  | @«at» E U₁ i p ih =>
    cases x with
    | array e sh hn =>
      simp only [Path.append_at, SVal.saveM] at h
      split at h
      · rename_i hi
        split at h
        · rename_i x0 hx
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨z, hz, rfl⟩ := h
          obtain ⟨y, y', hy, hy', hz'⟩ := ih x0 r hz
          refine ⟨y, y', ?_, hy', ?_⟩
          · simp only [SVal.findM, hi, if_true, hx]; exact hy
          · simp only [SVal.saveM, hi, if_true, hx, hz', Option.bind_eq_bind, Option.bind_some]
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
  | @atF E U₁ n i p ih =>
    cases x with
    | fixed e =>
      simp only [Path.append_atF, SVal.saveM] at h
      split at h
      · rename_i hi
        split at h
        · rename_i x0 hx
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨z, hz, rfl⟩ := h
          obtain ⟨y, y', hy, hy', hz'⟩ := ih x0 r hz
          refine ⟨y, y', ?_, hy', ?_⟩
          · simp only [SVal.findM, hi, if_true, hx]; exact hy
          · simp only [SVal.saveM, hi, if_true, hx, hz', Option.bind_eq_bind, Option.bind_some]
        · simp only [reduceCtorEq] at h
      · simp only [reduceCtorEq] at h
  | @key K V U₁ k p ih =>
    cases x with
    | map m d =>
      simp only [Path.append_key, SVal.saveM] at h
      split at h
      · rename_i x0 hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨z, hz, rfl⟩ := h
        obtain ⟨y, y', hy, hy', hz'⟩ := ih x0 r hz
        refine ⟨y, y', ?_, hy', ?_⟩
        · simp only [SVal.findM, hx]; exact hy
        · simp only [SVal.saveM, hx, hz', Option.bind_eq_bind, Option.bind_some]
      · rename_i hx
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨z, hz, rfl⟩ := h
        obtain ⟨y, y', hy, hy', hz'⟩ := ih d r hz
        refine ⟨y, y', ?_, hy', ?_⟩
        · simp only [SVal.findM, hx]; exact hy
        · simp only [SVal.saveM, hx, hz', Option.bind_eq_bind, Option.bind_some]

/-- A save at an element below an array keeps the array's live length. -/
theorem SVal.saveM_at_n {E W : Ty} {y y' : SVal (.ref (.array E))} {i : Int} {r : Path E W}
    {v : SVal W} (h : y.saveM (.at i r) v = some y') :
    (SVal.view y' : ArrView E).n = (SVal.view y : ArrView E).n := by
  cases y with
  | array e sh hn =>
    rename_i n
    simp only [SVal.saveM] at h
    split at h
    · split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨z, -, rfl⟩ := h
        show (List.take n _).length = n
        rw [List.length_take, List.length_set, List.length_append, SVec.length_toList]
        omega
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h

/-- The Theory's `diverges a (b ++ [x])`: `a` parts from `b`, or goes on
below it. -/
theorem diverges_append_single {a b : List Semantics.Seg} {x : Semantics.Seg}
    (h : Theory.StValue.diverges a (b ++ [x]) = true) :
    Theory.StValue.diverges a b = true ∨ ∃ rest, rest ≠ [] ∧ a = b ++ rest := by
  induction b generalizing a with
  | nil =>
    cases a with
    | nil => simp only [Theory.StValue.diverges, Bool.false_eq_true] at h
    | cons y a' => exact .inr ⟨y :: a', List.cons_ne_nil _ _, rfl⟩
  | cons c b' ih =>
    cases a with
    | nil => simp only [Theory.StValue.diverges, Bool.false_eq_true] at h
    | cons d a' =>
      simp only [List.cons_append, Theory.StValue.diverges] at h ⊢
      by_cases e : d = c
      · subst e
        simp only [if_pos rfl] at h ⊢
        rcases ih h with h' | ⟨rest, hne, rfl⟩
        · exact .inl h'
        · exact .inr ⟨rest, hne, rfl⟩
      · simp only [e, if_false]
        exact .inl trivial

namespace Storage

/-- A delete is a save at its reference. -/
theorem delete_save {T : Ty} {st st' : Storage C} {r : SRef C T} (h : st.delete r = some st') :
    ∃ x, st.find r = some x ∧ st.save r x.defaultOf = some st' := by
  simp only [Storage.delete, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  exact h

/-- A push is a save at the array's reference. -/
theorem push_save {E : Ty} {st st' : Storage C} {r : SRef C (.ref (.array E))}
    {val : SVal E → Option (SVal E)} (h : st.push r val = some st') : ∃ w, st.save r w = some st' := by
  simp only [Storage.push, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, -, h⟩ := h
  obtain ⟨x, -, h⟩ := h
  split at h
  · exact ⟨_, h⟩
  · simp only [reduceCtorEq] at h

/-- A pop is a save at the array's reference. -/
theorem pop_save {E : Ty} {st st' : Storage C} {keep : Bool} {r : SRef C (.ref (.array E))}
    (h : st.pop keep r = some st') : ∃ w, st.save r w = some st' := by
  simp only [Storage.pop, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, -, h⟩ := h
  split at h
  · simp only [reduceCtorEq] at h
  · exact ⟨_, h⟩

/-- A save that lands reads back at its reference. -/
theorem find_save_same {U : Ty} {st st' : Storage C} {r : SRef C U} {v : SVal U}
    (h : st.save r v = some st') : st'.find r = some v := by
  obtain ⟨x', hs, rfl⟩ := save_some h
  simp only [Storage.find, SFields.get_set_same]
  exact SVal.find_save_same _ _ _ hs

/-- **A save leaves a reference that parts from it** (solkey's
`findOnSaveFrame`): across roots, or below one root by `Path.Diverges`. -/
theorem find_save_frame {U W : Ty} {st st' : Storage C} {r : SRef C U} {v : SVal U}
    {q : SRef C W} (hd : Theory.StValue.diverges r.absT q.absT = true)
    (h : st.save r v = some st') : st'.find q = st.find q := by
  obtain ⟨x', hs, rfl⟩ := save_some h
  rcases r with ⟨n, hr, p⟩
  rcases q with ⟨n', hq, p'⟩
  by_cases e : n = n'
  · subst e
    rename_i T₁ T₂
    obtain rfl : T₁ = T₂ := Option.some.inj (hr.symm.trans hq)
    simp only [SRef.absT, rootPath, Theory.StValue.diverges, if_pos rfl] at hd
    show ((SFields.set st hr x').get hr).find p' = (st.get hr).find p'
    rw [SFields.get_set_same]
    rw [SVal.save_eq_saveM] at hs
    rw [SVal.find_eq_findM, SVal.find_eq_findM]
    exact SVal.findM_saveM_diverges (Path.diverges_of_erase p p' hd) _ v hs
  · show ((SFields.set st hr x').get hq).find p' = (st.get hq).find p'
    rw [SFields.get_set_ne _ hr hq e]

/-- `lenU` of one count, whatever its bound's proof. -/
theorem lenU_congr {n m : Nat} (e : n = m) (h : n < 2 ^ 256) (h' : m < 2 ^ 256) :
    lenU n h = lenU m h' := by
  subst e; rfl

/-- **A save leaves an array's length** where it parts from the length's
path (solkey's `lenOnSaveFrame`): elsewhere, or below one of the array's
elements. -/
theorem len_save_frame {U E : Ty} {st st' : Storage C} {r : SRef C U} {v : SVal U}
    {q : SRef C (.ref (.array E))}
    (hd : Theory.StValue.diverges r.absT (q.absT ++ [Theory.StValue.lengthSeg]) = true)
    (h : st.save r v = some st') : st'.len q = st.len q := by
  rcases diverges_append_single hd with hd | ⟨rest, hne, he⟩
  · simp only [Storage.len, find_save_frame hd h]
  · obtain ⟨x', hs, rfl⟩ := save_some h
    rcases r with ⟨n, hr, p⟩
    rcases q with ⟨n', hq, p'⟩
    simp only [SRef.absT, rootPath, List.cons_append, List.cons.injEq,
      Semantics.Seg.field.injEq] at he
    obtain ⟨rfl, he⟩ := he
    rename_i T₁ T₂
    obtain rfl : T₁ = T₂ := Option.some.inj (hr.symm.trans hq)
    obtain ⟨rr, rfl, hrr⟩ := Path.split_of_erase p' p he
    cases rr with
    | nil => exact absurd hrr.symm hne
    | «at» i rr' =>
      rw [SVal.save_eq_saveM] at hs
      obtain ⟨y, y', hy, hy', hx'⟩ := SVal.saveM_append _ p' (.at i rr') v hs
      have hfy' : x'.findM p' = some y' := SVal.findM_saveM _ p' y' hx'
      show (((SFields.set st hr x').get hr).find p').bind _ = ((st.get hr).find p').bind _
      rw [SFields.get_set_same, SVal.find_eq_findM, SVal.find_eq_findM, hfy', hy]
      simp only [Option.bind_some]
      exact congrArg some (lenU_congr (SVal.saveM_at_n hy') _ _)

end Storage

end Frame

/-! ## The frame and delete-value laws, in a run

A frame or delete-value law may leave a storage read on its right that is
not total, but once the storage operation it reads past returns, the two
sides return alike (`TermTaclet.RefLaw.exact`): `t ⇝ t'` refines, and
refines back wherever an update holds the operation (`Upd.coversRef`). -/

section RefEval

variable {σ : State C Γ}

theorem Tm.eval_find {P : PrimTy} (s : Tm C Γ .st) (q : Tm C Γ (.path (.prim P))) :
    (Tms.Term.find s q).eval σ =
      (s.eval σ).bind fun st => (q.eval σ).bind fun r => (st.find r).bind fun v => some v.view :=
  rfl
theorem Tm.eval_len {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tms.Term.len s q).eval σ = (s.eval σ).bind fun st => (q.eval σ).bind fun r => st.len r :=
  rfl
theorem Tm.eval_delValue {P : PrimTy} (t : Tm C Γ (.val P)) :
    (Tms.Term.delValue t).eval σ = (t.eval σ).map fun _ => PrimTy.dflt P := rfl

/-- Two paths whose shapes part reach references that part. -/
theorem Tm.diverges_eval {T U : Ty} {p : Tm C Γ (.path T)} {q : Tm C Γ (.path U)}
    (h : p.diverges q = true) {r : SRef C T} {r' : SRef C U} (hp : p.eval σ = some r)
    (hq : q.eval σ = some r') : Theory.StValue.diverges r.absT r'.absT = true := by
  have e := Tm.diverges_denote σ h
  rwa [show p.denote σ = r.absT from Tm.denote_eval σ p r hp,
    show q.denote σ = r'.absT from Tm.denote_eval σ q r' hq] at e

/-- A path that leaves another's length reaches a reference that does. -/
theorem Tm.divergesLen_eval {T U : Ty} {q : Tm C Γ (.path T)} {p : Tm C Γ (.path U)}
    (h : q.divergesLen p = true) {r : SRef C T} {r' : SRef C U} (hq : q.eval σ = some r)
    (hp : p.eval σ = some r') :
    Theory.StValue.diverges r.absT (r'.absT ++ [Theory.StValue.lengthSeg]) = true := by
  have e := Tm.divergesLen_denote σ h
  rwa [show q.denote σ = r.absT from Tm.denote_eval σ q r hq,
    show p.denote σ = r'.absT from Tm.denote_eval σ p r' hp] at e

/-- Two typed references with one Theory path are one reference. -/
theorem SRef.heq_of_absT {U W : Ty} (r : SRef C U) (q : SRef C W) (h : r.absT = q.absT) :
    U = W ∧ HEq r q := by
  rcases r with ⟨n, hr, p⟩
  rcases q with ⟨n', hq, p'⟩
  simp only [SRef.absT, rootPath, List.cons.injEq, Semantics.Seg.field.injEq] at h
  obtain ⟨rfl, h⟩ := h
  rename_i T₁ T₂
  obtain rfl : T₁ = T₂ := Option.some.inj (hr.symm.trans hq)
  obtain ⟨rfl, e⟩ := Path.heq_of_erase p p' h
  cases e
  exact ⟨rfl, HEq.rfl⟩

/-- Two paths of the same segments reach one reference. -/
theorem Tm.sameSegs_eval {T U : Ty} {p : Tm C Γ (.path T)} {q : Tm C Γ (.path U)}
    (h : p.sameSegs q = true) {r : SRef C T} {r' : SRef C U} (hp : p.eval σ = some r)
    (hq : q.eval σ = some r') : T = U ∧ HEq r r' := by
  have e := Tm.sameSegs_denote σ h
  rw [show p.denote σ = r.absT from Tm.denote_eval σ p r hp,
    show q.denote σ = r'.absT from Tm.denote_eval σ q r' hq] at e
  exact SRef.heq_of_absT r r' e

/-- `s'` is a save at `p` over `s`, wherever it returns. -/
def Tm.SavesAt (σ : State C Γ) (s' : Tm C Γ .st) {T : Ty} (p : Tm C Γ (.path T))
    (s : Tm C Γ .st) : Prop :=
  ∀ st', s'.eval σ = some st' →
    ∃ st r w, s.eval σ = some st ∧ p.eval σ = some r ∧ st.save r w = some st'

theorem Tm.savesAt_save {T : Ty} (s : Tm C Γ .st) (p : Tm C Γ (.path T)) (v : Tm C Γ (.sv T)) :
    Tm.SavesAt σ (Tms.STerm.save s p v) p s := fun st' h => by
  have h : ((s.eval σ).bind fun st => (p.eval σ).bind fun r => (v.eval σ).bind fun w =>
      st.write r w) = some st' := h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨st, hs, r, hp, w, -, hw⟩ := h
  obtain ⟨w', hw'⟩ := Storage.write_some hw
  exact ⟨st, r, w', hs, hp, hw'⟩

theorem Tm.savesAt_delAt {T : Ty} (s : Tm C Γ .st) (p : Tm C Γ (.path T)) :
    Tm.SavesAt σ (Tms.STerm.delAt s p) p s := fun st' h => by
  have h : ((s.eval σ).bind fun st => (p.eval σ).bind fun r => st.delete r) = some st' := h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨st, hs, r, hp, hd⟩ := h
  obtain ⟨x, -, hx⟩ := Storage.delete_save hd
  exact ⟨st, r, _, hs, hp, hx⟩

theorem Tm.savesAt_push {E : Ty} (s : Tm C Γ .st) (p : Tm C Γ (.path (.ref (.array E))))
    (v : Tm C Γ (.sv E)) : Tm.SavesAt σ (Tms.STerm.push s p v) p s := fun st' h => by
  have h : ((s.eval σ).bind fun st => (p.eval σ).bind fun r =>
      st.push r fun _ => (v.eval σ).map SVal.strip) = some st' := h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨st, hs, r, hp, hd⟩ := h
  obtain ⟨w, hw⟩ := Storage.push_save hd
  exact ⟨st, r, w, hs, hp, hw⟩

theorem Tm.savesAt_pop {E : Ty} (s : Tm C Γ .st) (p : Tm C Γ (.path (.ref (.array E)))) :
    Tm.SavesAt σ (Tms.STerm.pop s p) p s := fun st' h => by
  have h : ((s.eval σ).bind fun st => (p.eval σ).bind fun r => st.pop false r) = some st' := h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨st, hs, r, hp, hd⟩ := h
  obtain ⟨w, hw⟩ := Storage.pop_save hd
  exact ⟨st, r, w, hs, hp, hw⟩

/-- **A read off a save, where the save returns, reads under it.** -/
theorem Tm.find_frame_eval {s s' : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)}
    {P : PrimTy} {q : Tm C Γ (.path (.prim P))} (hS : Tm.SavesAt σ s' p s)
    (hd : p.diverges q = true) {st' : Storage C} (he : s'.eval σ = some st') :
    (Tms.Term.find s' q).eval σ = (Tms.Term.find s q).eval σ := by
  obtain ⟨st, r, w, hs, hp, hw⟩ := hS st' he
  rw [Tm.eval_find, Tm.eval_find, he, hs, Option.bind_some, Option.bind_some]
  cases hq : q.eval σ with
  | none => rfl
  | some rq => simp only [Option.bind_some, Storage.find_save_frame (Tm.diverges_eval hd hp hq) hw]

/-- **A length read off a save, where the save returns, reads under it.** -/
theorem Tm.len_frame_eval {s s' : Tm C Γ .st} {T : Ty} {q : Tm C Γ (.path T)} {E : Ty}
    {p : Tm C Γ (.path (.ref (.array E)))} (hS : Tm.SavesAt σ s' q s)
    (hd : q.divergesLen p = true) {st' : Storage C} (he : s'.eval σ = some st') :
    (Tms.Term.len s' p).eval σ = (Tms.Term.len s p).eval σ := by
  obtain ⟨st, r, w, hs, hq, hw⟩ := hS st' he
  rw [Tm.eval_len, Tm.eval_len, he, hs, Option.bind_some, Option.bind_some]
  cases hp : p.eval σ with
  | none => rfl
  | some rp => simp only [Option.bind_some, Storage.len_save_frame (Tm.divergesLen_eval hd hq hp) hw]

/-- **A read at a delete, where the delete returns, is the default of the
read under it** (`find_delAt_same`). -/
theorem Tm.find_delAt_value_eval {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)} {P : PrimTy}
    {q : Tm C Γ (.path (.prim P))} (hq : p.sameSegs q = true) {st' : Storage C}
    (he : (Tms.STerm.delAt s p).eval σ = some st') :
    (Tms.Term.find (Tms.STerm.delAt s p) q).eval σ =
      (Tms.Term.delValue (Tms.Term.find s q)).eval σ := by
  have he' : ((s.eval σ).bind fun st => (p.eval σ).bind fun r => st.delete r) = some st' := he
  simp only [Option.bind_eq_some_iff] at he'
  obtain ⟨st, hs, r, hp, hd⟩ := he'
  obtain ⟨x, hx, hsave⟩ := Storage.delete_save hd
  rw [Tm.eval_find, Tm.eval_delValue, Tm.eval_find, he, hs, Option.bind_some, Option.bind_some]
  cases hqe : q.eval σ with
  | none => rfl
  | some rq =>
    obtain ⟨rfl, e⟩ := Tm.sameSegs_eval hq hp hqe
    cases e
    rw [Option.bind_some, Option.bind_some, Storage.find_save_same hsave, hx]
    cases x
    rw [SVal.defaultOf_prim]
    rfl

end RefEval

/-- The storage laws whose two sides return alike once the storage operation
they read past returns (`RefLaw.exact`): the laws that may rewrite a
covered update under either modality though their right side is not total.
Each constructor takes its term taclet's arguments. -/
inductive TermTaclet.RefLaw : {P : PrimTy} → {t t' : Tm C Γ (.val P)} → TermTaclet t t' → Prop
  | findOnSaveFrame {s : Tm C Γ .st} {T : Ty} {P : PrimTy} {p : Tm C Γ (.path T)}
      {q : Tm C Γ (.path (.prim P))} {v : Tm C Γ (.sv T)} (h : p.diverges q = true := by rfl) :
      RefLaw (TermTaclet.findOnSaveFrame (s := s) (p := p) (q := q) (v := v) h)
  | findOnDelAtValue {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)} {P : PrimTy}
      {q : Tm C Γ (.path (.prim P))} (hp : p.hasSeg = true := by rfl)
      (hq : p.sameSegs q = true := by first | rfl | exact Tm.sameSegs_refl _) :
      RefLaw (TermTaclet.findOnDelAtValue (s := s) (p := p) (q := q) hp hq)
  | findOnDelAtFrame {s : Tm C Γ .st} {T : Ty} {p : Tm C Γ (.path T)} {P : PrimTy}
      {q : Tm C Γ (.path (.prim P))} (h : p.diverges q = true := by rfl) :
      RefLaw (TermTaclet.findOnDelAtFrame (s := s) (p := p) (q := q) h)
  | findOnPushFrame {s : Tm C Γ .st} {E : Ty} {p : Tm C Γ (.path (.ref (.array E)))}
      {v : Tm C Γ (.sv E)} {P : PrimTy} {q : Tm C Γ (.path (.prim P))}
      (h : p.diverges q = true := by rfl) :
      RefLaw (TermTaclet.findOnPushFrame (s := s) (p := p) (v := v) (q := q) h)
  | findOnPopFrame {s : Tm C Γ .st} {E : Ty} {p : Tm C Γ (.path (.ref (.array E)))}
      {P : PrimTy} {q : Tm C Γ (.path (.prim P))} (h : p.diverges q = true := by rfl) :
      RefLaw (TermTaclet.findOnPopFrame (s := s) (p := p) (q := q) h)
  | lenOnSaveFrame {s : Tm C Γ .st} {T : Ty} {q : Tm C Γ (.path T)} {v : Tm C Γ (.sv T)}
      {E : Ty} {p : Tm C Γ (.path (.ref (.array E)))} (h : q.divergesLen p = true := by rfl) :
      RefLaw (TermTaclet.lenOnSaveFrame (s := s) (q := q) (v := v) (p := p) h)
  | lenOnDelAtFrame {s : Tm C Γ .st} {T : Ty} {q : Tm C Γ (.path T)}
      {E : Ty} {p : Tm C Γ (.path (.ref (.array E)))} (h : q.divergesLen p = true := by rfl) :
      RefLaw (TermTaclet.lenOnDelAtFrame (s := s) (q := q) (p := p) h)

/-! ### The storage a read reads, and the writes an update holds -/

/-- The storage a read reads. -/
def Op2.storeArg {a b s : Srt} : Op2 C a b s → Tm C Γ a → Option (Tm C Γ .st)
  | .find, x => some x
  | .len, x => some x
  | _, _ => none

/-- The storage a read reads (`find(s, p)`, `len(s, p)`).  Generic in the
sort. -/
def Tm.readStore? {u : Srt} : Tm C Γ u → Option (Tm C Γ .st)
  | .app2 o x _ => o.storeArg x
  | _ => none

theorem Tm.readStore?_eval {σ : State C Γ} {u : Srt} {t : Tm C Γ u} {X : Tm C Γ .st}
    (h : t.readStore? = some X) (ht : t.eval σ ≠ none) : X.eval σ ≠ none := by
  cases t with
  | app2 o x y =>
    cases o <;> simp only [Tm.readStore?, Op2.storeArg, Option.some.injEq, reduceCtorEq] at h
    all_goals
      subst h
      intro hx
      rw [Tm.eval_app2, hx, Op2.eval_eq_evalM] at ht
      exact ht rfl
  | _ => simp only [Tm.readStore?, reduceCtorEq] at h

/-- A symbol's value is strict in its first argument: where it halts, so
does the term. -/
theorem Tm.eval_app1_none {σ : State C Γ} {a u : Srt} (o : Op1 C a u) (x : Tm C Γ a)
    (hx : x.eval σ = none) : (Tm.app1 o x).eval σ = none := by
  rw [Tm.eval_app1, hx, Op1.eval_eq_evalM]
  cases o <;> rfl

theorem Tm.eval_app2_none {σ : State C Γ} {a b u : Srt} (o : Op2 C a b u) (x : Tm C Γ a)
    (y : Tm C Γ b) (hx : x.eval σ = none) : (Tm.app2 o x y).eval σ = none := by
  rw [Tm.eval_app2, hx, Op2.eval_eq_evalM]
  cases o <;> rfl

theorem Tm.eval_app3_none {σ : State C Γ} {a b c u : Srt} (o : Op3 C a b c u) (x : Tm C Γ a)
    (y : Tm C Γ b) (z : Tm C Γ c) (hx : x.eval σ = none) : (Tm.app3 o x y z).eval σ = none := by
  rw [Tm.eval_app3, hx, Op3.eval_eq_evalM]
  cases o <;> rfl

/-- `w` is on the spine below `t`: a symbol's first argument, or one below
it.  Generic in both sorts. -/
def Tm.onSpineAny {k : Srt} (w : Tm C Γ k) : {u : Srt} → Tm C Γ u → Bool
  | _, .app1 _ x => x.beqR w || Tm.onSpineAny w x
  | _, .app2 _ x _ => x.beqR w || Tm.onSpineAny w x
  | _, .app3 _ x _ _ => x.beqR w || Tm.onSpineAny w x
  | _, _ => false

/-- `w` is `t` or on its spine: where `t` returns, `w` does. -/
def Tm.onSpine {k : Srt} (t w : Tm C Γ k) : Bool := t.beqR w || Tm.onSpineAny w t

theorem Tm.onSpineAny_eval {σ : State C Γ} {k : Srt} {w : Tm C Γ k} {u : Srt} (t : Tm C Γ u)
    (h : Tm.onSpineAny w t = true) (ht : t.eval σ ≠ none) : w.eval σ ≠ none := by
  induction t with
  | app1 o x ihx =>
    have hx : x.eval σ ≠ none := fun hx => ht (Tm.eval_app1_none o x hx)
    simp only [Tm.onSpineAny, Bool.or_eq_true] at h
    rcases h with h | h
    · cases Tm.sigma_eq_of_beqR h; exact hx
    · exact ihx h hx
  | app2 o x y ihx _ =>
    have hx : x.eval σ ≠ none := fun hx => ht (Tm.eval_app2_none o x y hx)
    simp only [Tm.onSpineAny, Bool.or_eq_true] at h
    rcases h with h | h
    · cases Tm.sigma_eq_of_beqR h; exact hx
    · exact ihx h hx
  | app3 o x y z ihx _ _ =>
    have hx : x.eval σ ≠ none := fun hx => ht (Tm.eval_app3_none o x y z hx)
    simp only [Tm.onSpineAny, Bool.or_eq_true] at h
    rcases h with h | h
    · cases Tm.sigma_eq_of_beqR h; exact hx
    · exact ihx h hx
  | _ => simp only [Tm.onSpineAny, Bool.false_eq_true] at h

theorem Tm.onSpine_eval {σ : State C Γ} {k : Srt} {t w : Tm C Γ k} (h : t.onSpine w = true)
    (ht : t.eval σ ≠ none) : w.eval σ ≠ none := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain rfl := Tm.eq_of_beqR h; exact ht
  · exact Tm.onSpineAny_eval (w := w) t h ht

/-- `U` writes the storage with a term on whose spine the write `w` lies:
`w` returns wherever `U` does. -/
def Upd.holdsWrite {Δ : Ctx} (U : Upd C Γ Δ) (w : Tm C Γ .st) : Bool :=
  U.storTerms.any (·.onSpine w)

theorem Upd.holdsWrite_eval {Δ : Ctx} {U : Upd C Γ Δ} {w : Tm C Γ .st}
    (h : U.holdsWrite w = true) {σ : State C Γ} {g : GlobT C σ.H} (hU : U.globT σ = some g) :
    w.eval σ ≠ none := by
  obtain ⟨S, hS, hs⟩ := List.any_eq_true.1 h
  obtain ⟨st, hst⟩ := Upd.storage_eval_of_globT U hU S hS
  exact Tm.onSpine_eval hs (by rw [hst]; exact Option.some_ne_none _)

/-- **A reference law is exact past its storage operation**: the read's
storage returns wherever the read does, and where it returns the two sides
return alike. -/
theorem TermTaclet.RefLaw.exact {P : PrimTy} {t t' : Tm C Γ (.val P)} {r : TermTaclet t t'} :
    RefLaw r → ∃ X, t.readStore? = some X ∧
      ∀ σ : State C Γ, X.eval σ ≠ none → t.eval σ = t'.eval σ
  | .findOnSaveFrame h => ⟨_, rfl, fun _ hX => by
      obtain ⟨st', he⟩ := Option.ne_none_iff_exists'.1 hX
      exact Tm.find_frame_eval (Tm.savesAt_save _ _ _) h he⟩
  | .findOnDelAtValue _ hq => ⟨_, rfl, fun _ hX => by
      obtain ⟨st', he⟩ := Option.ne_none_iff_exists'.1 hX
      exact Tm.find_delAt_value_eval hq he⟩
  | .findOnDelAtFrame h => ⟨_, rfl, fun _ hX => by
      obtain ⟨st', he⟩ := Option.ne_none_iff_exists'.1 hX
      exact Tm.find_frame_eval (Tm.savesAt_delAt _ _) h he⟩
  | .findOnPushFrame h => ⟨_, rfl, fun _ hX => by
      obtain ⟨st', he⟩ := Option.ne_none_iff_exists'.1 hX
      exact Tm.find_frame_eval (Tm.savesAt_push _ _ _) h he⟩
  | .findOnPopFrame h => ⟨_, rfl, fun _ hX => by
      obtain ⟨st', he⟩ := Option.ne_none_iff_exists'.1 hX
      exact Tm.find_frame_eval (Tm.savesAt_pop _ _) h he⟩
  | .lenOnSaveFrame h => ⟨_, rfl, fun _ hX => by
      obtain ⟨st', he⟩ := Option.ne_none_iff_exists'.1 hX
      exact Tm.len_frame_eval (Tm.savesAt_save _ _ _) h he⟩
  | .lenOnDelAtFrame h => ⟨_, rfl, fun _ hX => by
      obtain ⟨st', he⟩ := Option.ne_none_iff_exists'.1 hX
      exact Tm.len_frame_eval (Tm.savesAt_delAt _ _) h he⟩

/-- **A reference law keeps every value its left side returns.** -/
theorem TermTaclet.RefLaw.evalRefines {P : PrimTy} {t t' : Tm C Γ (.val P)} {r : TermTaclet t t'}
    (hr : RefLaw r) : Tm.EvalRefinesAt t t' := fun σ x hx => by
  obtain ⟨X, hX, he⟩ := hr.exact
  rw [← he σ (Tm.readStore?_eval hX (by rw [hx]; exact Option.some_ne_none _))]
  exact hx

/-- A covered reference law's storage operation is held by the update. -/
def Upd.coversRef {Δ : Ctx} {u : Srt} (U : Upd C Γ Δ) (q : Tm C Γ u × Tm C Γ u) : Bool :=
  match q.1.readStore? with
  | some X => U.holdsWrite X
  | none => false

/-- **Wherever a covered update returns, a reference law refines back.** -/
theorem TermTaclet.RefLaw.back {P : PrimTy} {t t' : Tm C Γ (.val P)} {r : TermTaclet t t'}
    (hr : RefLaw r) {Δ : Ctx} {U : Upd C Γ Δ} (hc : U.coversRef (t, t') = true) {σ : State C Γ}
    {g : GlobT C σ.H} (hU : U.globT σ = some g) : OLe (t'.eval σ) (t.eval σ) := by
  obtain ⟨X, hX, he⟩ := hr.exact
  simp only [Upd.coversRef, hX] at hc
  rw [he σ (Upd.holdsWrite_eval hc hU)]
  exact OLe.refl _

/-! ## Reading member-wise

solkey reads a path from its head (`findMemberCons`, `selectOnSaveMember`,
`selectOnDelAtMember`): `find(save(storage, alice.age, 42), alice.age)`
becomes `findIn(select(save(storage, alice.age, 42), alice), age)`, then
`findIn(saveIn(select(storage, alice), age, 42), age)`.  On the typed
storage `select(s, r)` is the struct at `r` as a storage of its members
(`Storage.selectT`), and a save or a delete of a member path in it is the
save or delete of the path from `r`, seen from `r` (`Storage.save_under`,
`Storage.delete_under`).  So a storage of members built by `saveIn` and
`delAtIn` over one `select` is the storage term it reads seen from its root
(`Tm.base`), and a read of it returns exactly what the read it is returns
(`Tm.base?_eval`): two member-wise forms of one read have one base
(`Tm.sameBase`), and a law between them is exact under any update
(`LawCov.eqv`).  A `select` under a `select` (`selectIn`) has no base. -/

section MemberWise

/-- A save of a member path seen from the root `r` is the save of the path
from `r`. -/
theorem Storage.save_under {s r : Name} {U : Ty} (st : Storage C)
    (h : C.rootType r = some (.ref (.struct s))) (q : SRef (Contract.ofStruct s) U) (w : SVal U) :
    (st.save (q.under h) w).map (·.selectT h) = (st.selectT h).save q w := by
  unfold Storage.save Storage.selectT SRef.under
  generalize hx : st.get h = x
  cases x with
  | struct fs =>
    simp only [SVal.view_struct, SVal.save_eq_saveM, SVal.saveM, Option.bind_eq_bind]
    cases hy : (fs.get q.hroot).saveM q.path w with
    | none => rfl
    | some y =>
      simp only [Option.bind_some, Option.map_some, SFields.get_set_same, SVal.view_struct]

/-- A read of a member path seen from the root `r` is the read of the path
from `r` (`Storage.find_selectT`). -/
theorem Storage.write_under {s r : Name} {U : Ty} (st : Storage C)
    (h : C.rootType r = some (.ref (.struct s))) (q : SRef (Contract.ofStruct s) U) (w : SVal U) :
    (st.write (q.under h) w).map (·.selectT h) = (st.selectT h).write q w := by
  unfold Storage.write
  split
  · exact Storage.save_under st h q w
  · rw [← Storage.find_selectT st h q]
    cases (st.selectT h).find q with
    | none => rfl
    | some x =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      exact Storage.save_under st h q _

theorem Storage.delete_under {s r : Name} {U : Ty} (st : Storage C)
    (h : C.rootType r = some (.ref (.struct s))) (q : SRef (Contract.ofStruct s) U) :
    (st.delete (q.under h)).map (·.selectT h) = (st.selectT h).delete q := by
  unfold Storage.delete
  rw [← Storage.find_selectT st h q]
  cases (st.selectT h).find q with
  | none => rfl
  | some x =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    exact Storage.save_under st h q _

variable {Γ : Ctx}

/-- What `Tm.unshift` gives at a sort: a member path as a path from a
root. -/
@[reducible] def Srt.Unsh (C : Contract) (Γ : Ctx) : Srt → Type
  | .spath _ T => Tm C Γ (.path T)
  | _ => PUnit

/-- A member under the root `r`. -/
def Op0.unshStep (r : Name) {sn : Name} (hr : C.rootType r = some (.ref (.struct sn))) {u : Srt} :
    Op0 C u → Option (Srt.Unsh C Γ u)
  | .member s f hf => if h : s = sn then some (.app1 (.field hf) (.app0 (.root r (h ▸ hr))))
    else none
  | _ => none

/-- A member after a member path, under its root. -/
def Op1.unshStep {a u : Srt} : Op1 C a u → Option (Srt.Unsh C Γ a) → Option (Srt.Unsh C Γ u)
  | .fieldIn hf, ih => ih.map fun p => .app1 (.field hf) p
  | _, _ => none

/-- A member path read from the root `r` of the struct `sn` it is in: `age`
under `alice` is `alice.age`.  Generic in the sort; `none` on anything but
members. -/
def Tm.unshift (r : Name) {sn : Name} (hr : C.rootType r = some (.ref (.struct sn))) :
    {u : Srt} → Tm C Γ u → Option (Srt.Unsh C Γ u)
  | _, .app0 o => o.unshStep r hr
  | _, .app1 o x => o.unshStep (Tm.unshift r hr x)
  | _, _ => none

/-- What `unshift` gives reads, from the root, the member path it read. -/
def Srt.UnshOK (σ : State C Γ) (r : Name) : (u : Srt) → Option (u.Den C σ.H) →
    Option (Srt.Unsh C Γ u) → Prop
  | .spath s _, x, some p' => ∀ hr : C.rootType r = some (.ref (.struct s)),
      p'.eval σ = x.map fun q => q.under hr
  | _, _, _ => True

theorem Srt.UnshOK.none (σ : State C Γ) (r : Name) {u : Srt} (x : Option (u.Den C σ.H)) :
    Srt.UnshOK σ r u x none := by
  cases u <;> trivial

theorem Tm.unshift_eval (σ : State C Γ) (r : Name) {sn : Name}
    (hr : C.rootType r = some (.ref (.struct sn))) {u : Srt} (p : Tm C Γ u) :
    Srt.UnshOK σ r u (p.eval σ) (Tm.unshift r hr p) := by
  induction p with
  | app0 o =>
    cases o with
    | member s f hf =>
      show Srt.UnshOK σ r _ _ (if h : s = sn then _ else none)
      split
      · rename_i h
        subst h
        intro hr'
        show some ((SRef.ofRoot r _).field hf) = some ((SRef.ofRoot (C := Contract.ofStruct s) f hf).under hr')
        rw [SRef.ofRoot_field_under]
      · exact Srt.UnshOK.none σ r _
    | _ => exact Srt.UnshOK.none σ r _
  | app1 o x ih =>
    cases o with
    | fieldIn hf =>
      show Srt.UnshOK σ r _ _ ((Tm.unshift r hr x).map _)
      revert ih
      cases Tm.unshift r hr x with
      | none => intro _; exact Srt.UnshOK.none σ r _
      | some p' =>
        intro ih hr'
        have ih : p'.eval σ = (x.eval σ).map fun q => q.under hr' := ih hr'
        show (Tm.app1 (.field hf) p').eval σ = ((Tm.app1 (.fieldIn hf) x).eval σ).map _
        rw [Tm.eval_app1, Tm.eval_app1, Op1.eval_eq_evalM, Op1.eval_eq_evalM]
        simp only [Op1.evalM]
        rw [ih]
        cases x.eval σ with
        | none => rfl
        | some q => exact congrArg some (SRef.under_field hf q hr')
    | _ => exact Srt.UnshOK.none σ r _
  | _ => exact Srt.UnshOK.none σ r _

/-- A storage of members' base: the root it is seen from and the storage
term it reads there. -/
structure Based (C : Contract) (Γ : Ctx) (s : Name) where
  r : Name
  h : C.rootType r = some (.ref (.struct s))
  b : Tm C Γ .st

/-- What `Tm.base` gives at a sort. -/
@[reducible] def Srt.BaseD (C : Contract) (Γ : Ctx) : Srt → Type
  | .sts s => Based C Γ s
  | _ => PUnit

def Op1.baseStep {a u : Srt} : Op1 C a u → Tm C Γ a → Option (Srt.BaseD C Γ u)
  | .select r h, x => some ⟨r, h, x⟩
  | _, _ => none

def Op2.baseStep {a b u : Srt} : Op2 C a b u → Tm C Γ b → Option (Srt.BaseD C Γ a) →
    Option (Srt.BaseD C Γ u)
  | .delAtIn, y, ih => ih.bind fun bd =>
    (Tm.unshift bd.r bd.h y).map fun p' => ⟨bd.r, bd.h, .app2 .delAt bd.b p'⟩
  | _, _, _ => none

def Op3.baseStep {a b c u : Srt} : Op3 C a b c u → Tm C Γ b → Tm C Γ c →
    Option (Srt.BaseD C Γ a) → Option (Srt.BaseD C Γ u)
  | .saveIn, y, z, ih => ih.bind fun bd =>
    (Tm.unshift bd.r bd.h y).map fun p' => ⟨bd.r, bd.h, .app3 .save bd.b p' z⟩
  | _, _, _, _ => none

/-- A storage of members as the storage term it reads seen from its root:
`saveIn(select(s, r), p, v)` is `save(s, r.p, v)` seen from `r`.  Generic in
the sort. -/
def Tm.base : {u : Srt} → Tm C Γ u → Option (Srt.BaseD C Γ u)
  | _, .app1 o x => o.baseStep x
  | _, .app2 o x y => o.baseStep y (Tm.base x)
  | _, .app3 o x y z => o.baseStep y z (Tm.base x)
  | _, _ => none

/-- What `base` gives evaluates, seen from its root, as the storage of
members. -/
def Srt.BaseOK (σ : State C Γ) : (u : Srt) → Option (u.Den C σ.H) → Option (Srt.BaseD C Γ u) → Prop
  | .sts _, x, some bd => x = (bd.b.eval σ).map fun st => st.selectT bd.h
  | _, _, _ => True

theorem Srt.BaseOK.none (σ : State C Γ) {u : Srt} (x : Option (u.Den C σ.H)) :
    Srt.BaseOK σ u x none := by
  cases u <;> trivial

theorem Tm.base_eval (σ : State C Γ) {u : Srt} (t : Tm C Γ u) :
    Srt.BaseOK σ u (t.eval σ) (Tm.base t) := by
  induction t with
  | app1 o x _ =>
    cases o with
    | select r h => rfl
    | _ => exact Srt.BaseOK.none σ _
  | app2 o x y ihx _ =>
    cases o with
    | delAtIn =>
      show Srt.BaseOK σ _ _ ((Tm.base x).bind _)
      revert ihx
      cases Tm.base x with
      | none => intro _; exact Srt.BaseOK.none σ _
      | some bd =>
        intro ihx
        have ihx : x.eval σ = (bd.b.eval σ).map fun st => st.selectT bd.h := ihx
        have hy := Tm.unshift_eval σ bd.r bd.h y
        revert hy
        show _ → Srt.BaseOK σ _ _ ((Tm.unshift bd.r bd.h y).map _)
        cases Tm.unshift bd.r bd.h y with
        | none => intro _; exact Srt.BaseOK.none σ _
        | some p' =>
          intro hy
          have hy : p'.eval σ = (y.eval σ).map fun q => q.under bd.h := hy bd.h
          show ((x.eval σ).bind fun st => (y.eval σ).bind fun q => st.delete q) =
            (((bd.b.eval σ).bind fun st => (p'.eval σ).bind fun q => st.delete q)).map _
          rw [ihx, hy]
          cases bd.b.eval σ with
          | none => rfl
          | some st =>
            cases y.eval σ with
            | none => rfl
            | some q =>
              simp only [Option.map_some, Option.bind_some]
              exact (Storage.delete_under st bd.h q).symm
    | _ => trivial
  | app3 o x y z ihx _ _ =>
    cases o with
    | saveIn =>
      show Srt.BaseOK σ _ _ ((Tm.base x).bind _)
      revert ihx
      cases Tm.base x with
      | none => intro _; exact Srt.BaseOK.none σ _
      | some bd =>
        intro ihx
        have ihx : x.eval σ = (bd.b.eval σ).map fun st => st.selectT bd.h := ihx
        have hy := Tm.unshift_eval σ bd.r bd.h y
        revert hy
        show _ → Srt.BaseOK σ _ _ ((Tm.unshift bd.r bd.h y).map _)
        cases Tm.unshift bd.r bd.h y with
        | none => intro _; exact Srt.BaseOK.none σ _
        | some p' =>
          intro hy
          have hy : p'.eval σ = (y.eval σ).map fun q => q.under bd.h := hy bd.h
          show ((x.eval σ).bind fun st => (y.eval σ).bind fun q => (z.eval σ).bind fun w =>
              st.write q w) =
            (((bd.b.eval σ).bind fun st => (p'.eval σ).bind fun q => (z.eval σ).bind fun w =>
              st.write q w)).map _
          rw [ihx, hy]
          cases bd.b.eval σ with
          | none => rfl
          | some st =>
            cases y.eval σ with
            | none => rfl
            | some q =>
              cases z.eval σ with
              | none => rfl
              | some w =>
                simp only [Option.map_some, Option.bind_some]
                exact (Storage.write_under st bd.h q w).symm
    | _ => exact Srt.BaseOK.none σ _
  | _ => exact Srt.BaseOK.none σ _

/-- A read, member-wise, as the read it is: `findIn(select(s, r), p)` is
`find(s, r.p)`. -/
def Op2.readBase {a b u : Srt} : Op2 C a b u → Tm C Γ a → Tm C Γ b → Option (Srt.BaseD C Γ a) →
    Option (Tm C Γ u)
  | .find, x, y, _ => some (.app2 .find x y)
  | .findIn, _, y, ih => ih.bind fun bd =>
    (Tm.unshift bd.r bd.h y).map fun q' => .app2 .find bd.b q'
  | _, _, _, _ => none

/-- A read as the read of the storage term it reads, from the root.
Generic in the sort. -/
def Tm.base? {u : Srt} : Tm C Γ u → Option (Tm C Γ u)
  | .app2 o x y => o.readBase x y (Tm.base x)
  | _ => none

/-- **A read, member-wise, returns what the read it is returns.** -/
theorem Tm.base?_eval (σ : State C Γ) {u : Srt} {t t' : Tm C Γ u} (h : t.base? = some t') :
    t.eval σ = t'.eval σ := by
  cases t with
  | app2 o x y =>
    cases o with
    | find =>
      change Op2.readBase .find x y (Tm.base x) = some t' at h
      simp only [Op2.readBase, Option.some.injEq] at h
      subst h; rfl
    | findIn =>
      have hb := Tm.base_eval σ x
      change Op2.readBase .findIn x y (Tm.base x) = some t' at h
      simp only [Op2.readBase] at h
      revert hb
      cases hbx : Tm.base x with
      | none => rw [hbx] at h; simp only [Option.bind_none, reduceCtorEq] at h
      | some bd =>
        intro hb
        have hb : x.eval σ = (bd.b.eval σ).map fun st => st.selectT bd.h := hb
        rw [hbx] at h
        simp only [Option.bind_some] at h
        have hy := Tm.unshift_eval σ bd.r bd.h y
        revert hy
        cases hu : Tm.unshift bd.r bd.h y with
        | none => rw [hu] at h; simp only [Option.map_none, reduceCtorEq] at h
        | some q' =>
          rw [hu] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          intro hy
          have hy : q'.eval σ = (y.eval σ).map fun q => q.under bd.h := hy bd.h
          show ((x.eval σ).bind fun st => (y.eval σ).bind fun q => (st.find q).bind fun v =>
              some v.view) =
            ((bd.b.eval σ).bind fun st => (q'.eval σ).bind fun q => (st.find q).bind fun v =>
              some v.view)
          rw [hb, hy]
          cases bd.b.eval σ with
          | none => rfl
          | some st =>
            cases y.eval σ with
            | none => rfl
            | some q => simp only [Option.map_some, Option.bind_some, Storage.find_selectT]
    | _ => simp only [Tm.base?, Op2.readBase, reduceCtorEq] at h
  | _ => simp only [Tm.base?, reduceCtorEq] at h

/-- The two terms are one read member-wise: they have one base
(`Tm.base?`), compared by `Tm.beqR`. -/
def Tm.sameBase {u : Srt} (t t' : Tm C Γ u) : Bool :=
  match t.base?, t'.base? with
  | some b, some b' => b.beqR b'
  | _, _ => false

/-- **Two member-wise forms of one read return alike**, in every state. -/
theorem Tm.sameBase_eval {u : Srt} {t t' : Tm C Γ u} (h : Tm.sameBase t t' = true)
    (σ : State C Γ) : t.eval σ = t'.eval σ := by
  unfold Tm.sameBase at h
  split at h
  · rename_i b b' hb hb'
    obtain rfl := Tm.eq_of_beqR h
    rw [Tm.base?_eval σ hb, Tm.base?_eval σ hb']
  · nomatch h

/-- A write read member-wise returns where the write it reads returns:
the update holding `save(s, r.p, v)` holds `saveIn(select(s, r), p, v)`. -/
theorem Tm.base_returns {s : Name} {S : Tm C Γ (.sts s)} {bd : Based C Γ s}
    (h : Tm.base S = some bd) {σ : State C Γ} (hb : bd.b.eval σ ≠ none) : S.eval σ ≠ none := by
  have e : S.eval σ = (bd.b.eval σ).map fun st => st.selectT bd.h := by
    have := Tm.base_eval σ S
    rw [h] at this
    exact this
  rw [e]
  intro h'
  exact hb (Option.map_eq_none_iff.1 h')

end MemberWise

/-! ## A read of a word written, covered -/

/-- A save's path, where it writes a literal word. -/
def Op3.saveLitPath {a b c u : Srt} : Op3 C a b c u → Tm C Γ b → Tm C Γ c →
    Option ((T : Ty) × Tm C Γ (.path T))
  | .save, y, z => if z.svLit?.isSome then some ⟨_, y⟩ else none
  | _, _, _ => none

/-- A storage term's path, where it saves a literal word. -/
def Tm.saveLitPath {u : Srt} : Tm C Γ u → Option ((T : Ty) × Tm C Γ (.path T))
  | .app3 o _ y z => o.saveLitPath y z
  | _ => none

/-- A read of a save of a literal word, at its path, the save held by `U`. -/
def Op2.findSaveLitStep {Δ : Ctx} (U : Upd C Γ Δ) {a b u : Srt} :
    Op2 C a b u → Tm C Γ a → Tm C Γ b → Bool
  | .find, x, y => (x.saveLitPath.any fun p => p.2.beqR y) && U.holdsWrite x
  | _, _, _ => false

/-- `find(save(s, p, sval(w)), p)`, the save held by `U`. -/
def Tm.findSaveLitAt {Δ : Ctx} (U : Upd C Γ Δ) {u : Srt} : Tm C Γ u → Bool
  | .app2 o x y => o.findSaveLitStep U x y
  | _ => false

/-- `t` reads, member-wise or not, the word a save writes at the path it
reads, and `U` holds the save: `find(save(s, p, sval(w)), p)` over
`storage := save(s, p, sval(w))`.  Syntactic, so that `rfl` decides it. -/
def Upd.coversLit {Δ : Ctx} {u : Srt} (U : Upd C Γ Δ) (t : Tm C Γ u) : Bool :=
  match t.base? with
  | some b => Tm.findSaveLitAt U b
  | none => false

theorem Tm.findSaveLitAt_eval {Δ : Ctx} {U : Upd C Γ Δ} {σ : State C Γ} {g : GlobT C σ.H}
    (hU : U.globT σ = some g) {u : Srt} (b : Tm C Γ u) (h : Tm.findSaveLitAt U b = true) :
    b.eval σ ≠ none := by
  cases b with
  | app2 o x y =>
    cases o <;> simp only [Tm.findSaveLitAt, Op2.findSaveLitStep, Bool.false_eq_true,
      Bool.and_eq_true, Option.any_eq_true] at h
    obtain ⟨⟨⟨T, p⟩, hp, hpy⟩, hw⟩ := h
    have hx := Upd.holdsWrite_eval hw hU
    obtain ⟨st', hst'⟩ := Option.ne_none_iff_exists'.1 hx
    cases x with
    | app3 o' s p₀ z =>
      cases o' <;> simp only [Tm.saveLitPath, Op3.saveLitPath, reduceCtorEq] at hp
      split at hp
      · rename_i hz
        simp only [Option.some.injEq, Sigma.mk.injEq] at hp
        obtain ⟨rfl, hp⟩ := hp
        cases hp
        cases Tm.sigma_eq_of_beqR hpy
        obtain ⟨w, hw'⟩ := Option.isSome_iff_exists.1 hz
        cases z with
        | app1 o'' a =>
          cases o'' <;> simp only [Tm.svLit?, Op1.svStep, reduceCtorEq] at hw'
          cases a with
          | app0 o3 =>
            cases o3 <;> simp only [Tm.litW?, Op0.litW?, reduceCtorEq] at hw'
            rename_i v
            rw [Tm.findSaveLit_eval_of_save s _ v hst']
            exact Option.some_ne_none _
          | _ => simp only [Tm.litW?, reduceCtorEq] at hw'
        | _ => simp only [Tm.svLit?, reduceCtorEq] at hw'
      · cases hp
    | _ => simp only [Tm.saveLitPath, reduceCtorEq] at hp
  | _ => simp only [Tm.findSaveLitAt, Bool.false_eq_true] at h

/-- Where a covering update returns, the read it covers returns. -/
theorem Upd.coversLit_eval {Δ : Ctx} {U : Upd C Γ Δ} {u : Srt} {t : Tm C Γ u}
    (hc : U.coversLit t = true) {σ : State C Γ} {g : GlobT C σ.H} (hU : U.globT σ = some g) :
    t.eval σ ≠ none := by
  unfold Upd.coversLit at hc
  split at hc
  · rename_i b hb
    rw [Tm.base?_eval σ hb]
    exact Tm.findSaveLitAt_eval hU b hc
  · nomatch hc


/-! ## The laws of memory reads

A memory read is no Theory equation (its Theory denotation is opaque), so a
law of one is a refinement of the run: where the read returns, its
replacement returns the same (`EvalLaw.exact`), on the typed heap
(`Heap.readAddr_writeAddr_same`, `Heap.readAddr_writeAddr_apart`).  Inside
an update over either modality the update must hold the write the law reads
past (`Upd.coversEval`), as `Upd.coversRef` for the storage. -/

section Heap

theorem Objs.get_set_same {H : HTy} {R : RefTy} : (Rs : List RefTy) → (os : Objs H Rs) →
    (i : Nat) → (h : Rs[i]? = some R) → (o : MObj H R) → Objs.get Rs (Objs.set Rs os i h o) i h = o
  | [], _, _, h, _ => absurd h (by simp only [List.getElem?_nil, reduceCtorEq, not_false_eq_true])
  | R' :: _, _, 0, h, _ => by
    obtain rfl : R' = R := Option.some.inj (by simpa only [List.getElem?_cons_zero] using h)
    rfl
  | _ :: Rs, os, i + 1, h, o => Objs.get_set_same Rs os.2 i _ o

theorem Objs.get_set_ne {H : HTy} {R R₂ : RefTy} : (Rs : List RefTy) → (os : Objs H Rs) →
    (i j : Nat) → i ≠ j → (h : Rs[i]? = some R) → (h₂ : Rs[j]? = some R₂) → (o : MObj H R) →
    Objs.get Rs (Objs.set Rs os i h o) j h₂ = Objs.get Rs os j h₂
  | [], _, _, _, _, h, _, _ => absurd h (by simp only [List.getElem?_nil, reduceCtorEq, not_false_eq_true])
  | _ :: _, _, 0, 0, hij, _, _, _ => absurd rfl hij
  | _ :: _, _, 0, _ + 1, _, _, _, _ => rfl
  | _ :: _, _, _ + 1, 0, _, _, _, _ => rfl
  | _ :: Rs, os, i + 1, j + 1, hij, h, h₂, o =>
    Objs.get_set_ne Rs os.2 i j (fun e => hij (congrArg (· + 1) e)) _ _ o

theorem Heap.get_set_same {H : HTy} {R : RefTy} (hp : Heap H) (r : HRef H R) (o : MObj H R) :
    (hp.set r o).get r = o :=
  Objs.get_set_same H hp r.id r.get? o

theorem Heap.get_set_ne {H : HTy} {R R₂ : RefTy} (hp : Heap H) (r : HRef H R) (r₂ : HRef H R₂)
    (hne : r.id ≠ r₂.id) (o : MObj H R) : (hp.set r o).get r₂ = hp.get r₂ :=
  Objs.get_set_ne H hp r.id r₂.id hne r.get? r₂.get? o

/-- Two references of one identity are one reference. -/
theorem HRef.heq_of_id {H : HTy} {R R₂ : RefTy} (r : HRef H R) (r₂ : HRef H R₂) (e : r.id = r₂.id) :
    R = R₂ ∧ HEq r r₂ := by
  rcases r with ⟨i, h⟩
  rcases r₂ with ⟨j, h₂⟩
  simp only at e
  subst e
  obtain rfl : R = R₂ := Option.some.inj (h.symm.trans h₂)
  exact ⟨rfl, HEq.rfl⟩

theorem MFields.get_set_same {H : HTy} {f : Name} : (fs : List (Name × Ty)) → {T : Ty} →
    (x : MFields H fs) → (h : Semantics.lookupBy f fs = some T) → (v : MVal H T) →
    MFields.get fs (MFields.set fs x h v) h = v
  | [], _, _, h, _ => absurd h (by simp only [Semantics.lookupBy, reduceCtorEq, not_false_eq_true])
  | (f', T') :: fs, T, x, h, v => by
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [MFields.get, MFields.set, e, dite_true]
    · simp only [MFields.get, MFields.set, e, dite_false]
      exact MFields.get_set_same fs x.2 _ v

theorem MFields.get_set_ne {H : HTy} {f g : Name} : (fs : List (Name × Ty)) → {T U : Ty} →
    (x : MFields H fs) → (h : Semantics.lookupBy f fs = some T) →
    (hg : Semantics.lookupBy g fs = some U) → f ≠ g →
    (v : MVal H T) → MFields.get fs (MFields.set fs x h v) hg = MFields.get fs x hg
  | [], _, _, _, h, _, _, _ => absurd h (by simp only [Semantics.lookupBy, reduceCtorEq, not_false_eq_true])
  | (f', T') :: fs, T, U, x, h, hg, hfg, v => by
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      have eg : ¬ g = f' := fun h' => hfg (e.trans h'.symm)
      simp only [MFields.get, MFields.set, e, dite_true, eg, dite_false]
    · by_cases eg : g = f'
      · simp only [MFields.get, MFields.set, e, dite_false, eg, dite_true]
      · simp only [MFields.get, MFields.set, e, dite_false, eg]
        exact MFields.get_set_ne fs x.2 _ _ hfg v

theorem MObj.elems_setElem {H : HTy} {R : RefTy} {E : Ty} (a : ArrTy R E) (o : MObj H R) (i : Nat)
    (v : MVal H E) : MObj.elems a (MObj.setElem a o i v) = (MObj.elems a o).set i v := by
  cases a <;> simp only [MObj.setElem_dyn, MObj.elems_dyn, MObj.setElem_fixed, MObj.elems_fixed]

/-- An array object is not a struct. -/
theorem ArrTy.ne_struct {R : RefTy} {E : Ty} (a : ArrTy R E) (s : Name) : R ≠ .struct s := by
  cases a <;> exact fun h => RefTy.noConfusion h

/-- Two addresses that never meet: two members, or a member and an element
(two kinds of object), or two elements of one array at two indices. -/
def MAddr.Apart {H : HTy} {T U : Ty} : MAddr H T → MAddr H U → Prop
  | @MAddr.field _ _ f _ _ _, @MAddr.field _ _ g _ _ _ => f ≠ g
  | .field .., .index .. => True
  | .index .., .field .. => True
  | .index r _ i, .index r' _ j => r.id = r'.id → i ≠ j

/-- **A write reads back where it lands** (`readOnWrite`). -/
theorem Heap.readAddr_writeAddr_same {H : HTy} {T : Ty} {hp hp' : Heap H} {ad : MAddr H T}
    {v : MVal H T} (h : hp.writeAddr ad v = some hp') : hp'.readAddr ad = some v := by
  cases ad with
  | field r hf =>
    simp only [Heap.writeAddr, Option.some.injEq] at h
    subst h
    simp only [Heap.readAddr, Heap.field, Heap.setField, Heap.get_set_same, MFields.get_set_same]
  | index r a i =>
    simp only [Heap.writeAddr, Heap.setIndex] at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq] at h
      subst h
      simp only [Heap.readAddr, Heap.index, hb.1, if_true, Heap.get_set_same, MObj.elems_setElem,
        List.getElem?_set_self hb.2]
    · simp only [reduceCtorEq] at h

/-- **A write leaves an address apart from it** (`readWriteDifferent`). -/
theorem Heap.readAddr_writeAddr_apart {H : HTy} {T U : Ty} {hp hp' : Heap H} {ad : MAddr H T}
    {bd : MAddr H U} {v : MVal H T} (h : hp.writeAddr ad v = some hp') (hab : ad.Apart bd) :
    hp'.readAddr bd = hp.readAddr bd := by
  cases ad with
  | field r hf =>
    simp only [Heap.writeAddr, Option.some.injEq] at h
    subst h
    cases bd with
    | field r' hg =>
      simp only [Heap.readAddr, Heap.field, Heap.setField, Option.some.injEq]
      by_cases e : r.id = r'.id
      · obtain ⟨hR, hr⟩ := HRef.heq_of_id r r' e
        cases hR
        cases hr
        rw [Heap.get_set_same, MFields.get_set_ne _ _ _ _ hab]
      · rw [Heap.get_set_ne _ r r' e]
    | index r' a j =>
      have e : r.id ≠ r'.id := fun e => ArrTy.ne_struct a _ (HRef.heq_of_id r r' e).1.symm
      simp only [Heap.readAddr, Heap.index, Heap.setField, Heap.get_set_ne _ r r' e]
  | index r a i =>
    simp only [Heap.writeAddr, Heap.setIndex] at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq] at h
      subst h
      cases bd with
      | field r' hg =>
        have e : r.id ≠ r'.id := fun e => ArrTy.ne_struct a _ (HRef.heq_of_id r r' e).1
        simp only [Heap.readAddr, Heap.field, Heap.get_set_ne _ r r' e]
      | index r' a' j =>
        by_cases e : r.id = r'.id
        · obtain ⟨hR, hr⟩ := HRef.heq_of_id r r' e
          cases hR
          cases hr
          have hij : i ≠ j := hab e
          cases a <;> cases a' <;>
          · simp only [Heap.readAddr, Heap.index, Heap.get_set_same, MObj.elems_setElem]
            by_cases hj : 0 ≤ j
            · have hn : i.toNat ≠ j.toNat := by omega
              simp only [hj, if_true, List.getElem?_set_ne hn]
            · simp only [hj, if_false]
        · simp only [Heap.readAddr, Heap.index, Heap.get_set_ne _ r r' e]
    · simp only [reduceCtorEq] at h

end Heap

section MemEval

variable {Γ : Ctx}

/-- An address term's shape: a member, or an element of an identity at an
index, literal or not. -/
inductive AddrShape (C : Contract) (Γ : Ctx) where
  | field (f : Name)
  | index (i : (R : RefTy) × Tm C Γ (.ident R)) (k : Option Int)

def Op1.addrStep {a u : Srt} : Op1 C a u → Option (AddrShape C Γ)
  | .mfield (f := f) _ => some (.field f)
  | _ => none

def Op2.addrStep {a b u : Srt} : Op2 C a b u → Tm C Γ a → Tm C Γ b → Option (AddrShape C Γ)
  | .mat _, x, y => some (.index ⟨_, x⟩ y.litInt?)
  | _, _, _ => none

/-- An address term's shape.  Generic in the sort. -/
def Tm.addrShape? {u : Srt} : Tm C Γ u → Option (AddrShape C Γ)
  | .app1 o _ => o.addrStep
  | .app2 o x y => o.addrStep x y
  | _ => none

/-- Two address terms that never meet: two members, a member and an element,
or two elements of one identity at two literal indices.  Syntactic, so that
`rfl` decides it. -/
def Tm.apart? {T U : Ty} (a : Tm C Γ (.addr T)) (b : Tm C Γ (.addr U)) : Bool :=
  match a.addrShape?, b.addrShape? with
  | some (.field f), some (.field g) => f != g
  | some (.field _), some (.index _ _) => true
  | some (.index _ _), some (.field _) => true
  | some (.index i (some k)), some (.index j (some k')) => i.2.beqR j.2 && k != k'
  | _, _ => false

/-- What an address term's shape says of the address it reads. -/
def AddrShape.Reads (σ : State C Γ) {T : Ty} : AddrShape C Γ → MAddrT T → Prop
  | .field f, ad => ∃ (s : Name) (id : Nat) (h : Semantics.lookupBy f (Semantics.structDef s) = some T),
      ad = MAddrT.field id h
  | .index ⟨R, i⟩ k, ad => ∃ (id : Nat) (E : Ty) (a : ArrTy R T) (j : Int), i.eval σ = some id ∧
      ad = MAddrT.index id a j ∧ ∀ k', k = some k' → j = k'

theorem Tm.litInt?_uint {σ : State C Γ} {y : Tm C Γ (.val .uint)} {k : Int} (h : y.litInt? = some k)
    {w : PrimTy.uint.Denote} (hw : y.eval σ = some w) : w.1 = k := by
  obtain ⟨⟨P, v⟩, hv, rfl⟩ := Option.map_eq_some_iff.1 h
  cases y with
  | app0 o =>
    cases o with
    | lit v' =>
      simp only [Tm.litW?, Op0.litW?, Option.some.injEq, Sigma.mk.injEq] at hv
      obtain ⟨rfl, hv⟩ := hv
      cases hv
      have : (Tm.app0 (Γ := Γ) (Op0.lit v')).eval σ = some v' := rfl
      rw [this] at hw
      cases hw
      rfl
    | _ => simp only [Tm.litW?, Op0.litW?, reduceCtorEq] at hv
  | _ => simp only [Tm.litW?, reduceCtorEq] at hv

theorem Tm.addrShape?_eval (σ : State C Γ) {T : Ty} {a : Tm C Γ (.addr T)} {sh : AddrShape C Γ}
    (h : a.addrShape? = some sh) {ad : MAddrT T} (ha : a.eval σ = some ad) : sh.Reads σ ad := by
  cases a with
  | app1 o x =>
    cases o <;> simp only [Tm.addrShape?, Op1.addrStep, reduceCtorEq, Option.some.injEq] at h
    subst h
    rename_i s f hf
    have ha : (x.eval σ).map (fun id => MAddrT.field id hf) = some ad := ha
    obtain ⟨id, -, rfl⟩ := Option.map_eq_some_iff.1 ha
    exact ⟨s, id, hf, rfl⟩
  | app2 o x y =>
    cases o <;> simp only [Tm.addrShape?, Op2.addrStep, reduceCtorEq, Option.some.injEq] at h
    subst h
    rename_i R arr
    have ha : ((x.eval σ).bind fun id => (y.eval σ).bind fun k => some (MAddrT.index id arr k.1)) =
      some ad := ha
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at ha
    obtain ⟨id, hi, w, hw, rfl⟩ := ha
    exact ⟨id, T, arr, w.1, hi, rfl, fun k' hk => Tm.litInt?_uint hk hw⟩
  | _ => simp only [Tm.addrShape?, reduceCtorEq] at h

/-- Two apart address terms resolve, in one heap typing, to apart
addresses. -/
theorem Tm.apart?_resolve (σ : State C Γ) {T U : Ty} {a : Tm C Γ (.addr T)} {b : Tm C Γ (.addr U)}
    (h : a.apart? b = true) {ad : MAddrT T} {bd : MAddrT U} (ha : a.eval σ = some ad)
    (hb : b.eval σ = some bd) {H : HTy} {ra : MAddr H T} {rb : MAddr H U}
    (hra : ad.resolve H = some ra) (hrb : bd.resolve H = some rb) : ra.Apart rb := by
  unfold Tm.apart? at h
  split at h
  · rename_i f g hfa hfb
    obtain ⟨s, id, hf, rfl⟩ := Tm.addrShape?_eval σ hfa ha
    obtain ⟨s', id', hg, rfl⟩ := Tm.addrShape?_eval σ hfb hb
    simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, Option.map_eq_some_iff] at hra hrb
    obtain ⟨r, -, rfl⟩ := hra
    obtain ⟨r', -, rfl⟩ := hrb
    simpa only [bne_iff_ne, ne_eq] using h
  · rename_i f i k hfa hfb
    obtain ⟨s, id, hf, rfl⟩ := Tm.addrShape?_eval σ hfa ha
    obtain ⟨id', E, arr, j, -, rfl, -⟩ := Tm.addrShape?_eval σ hfb hb
    simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, Option.map_eq_some_iff] at hra hrb
    obtain ⟨r, -, rfl⟩ := hra
    obtain ⟨r', -, rfl⟩ := hrb
    trivial
  · rename_i i k f hfa hfb
    obtain ⟨id', E, arr, j, -, rfl, -⟩ := Tm.addrShape?_eval σ hfa ha
    obtain ⟨s, id, hf, rfl⟩ := Tm.addrShape?_eval σ hfb hb
    simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, Option.map_eq_some_iff] at hra hrb
    obtain ⟨r, -, rfl⟩ := hra
    obtain ⟨r', -, rfl⟩ := hrb
    trivial
  · rename_i i k j k' hfa hfb
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hij, hk⟩ := h
    obtain ⟨R, i⟩ := i
    obtain ⟨R', j⟩ := j
    cases Tm.sigma_eq_of_beqR hij
    obtain ⟨id, E, arr, n, hi, rfl, hn⟩ := Tm.addrShape?_eval σ hfa ha
    obtain ⟨id', E', arr', n', hi', rfl, hn'⟩ := Tm.addrShape?_eval σ hfb hb
    rw [hi] at hi'
    cases hi'
    simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, Option.map_eq_some_iff] at hra hrb
    obtain ⟨r, -, rfl⟩ := hra
    obtain ⟨r', -, rfl⟩ := hrb
    intro _
    rw [hn k rfl, hn' k' rfl]
    exact hk
  · nomatch h

end MemEval

/-- A law of a memory read, at the value or the identity sort: where the
read returns, the replacement returns the same (`EvalLaw.exact`). -/
inductive EvalLaw {Γ : Ctx} : {u : Srt} → Tm C Γ u → Tm C Γ u → Prop
  /-- **`readOnWrite`**: `read(write(m, a, v), a) ⇝ v` (`Heap.readAddr_writeAddr_same`). -/
  | readOnWrite {m : Tm C Γ .mem} {P : PrimTy} {a : Tm C Γ (.addr (.prim P))} {v : P.Denote} :
      EvalLaw (Tms.Term.read (Tms.MTerm.write m a (Tms.MValT.val (Tms.Term.lit v))) a)
        (Tms.Term.lit v)
  /-- **`readWriteDifferent`**: a write leaves every other address,
  `read(write(m, a, v), b) ⇝ read(m, b)` where `a` and `b` never meet
  (`Tm.apart?`, `Heap.readAddr_writeAddr_apart`). -/
  | readWriteDifferent {m : Tm C Γ .mem} {T : Ty} {a : Tm C Γ (.addr T)} {v : Tm C Γ (.mv T)}
      {P : PrimTy} {b : Tm C Γ (.addr (.prim P))} (h : a.apart? b = true := by rfl) :
      EvalLaw (Tms.Term.read (Tms.MTerm.write m a v) b) (Tms.Term.read m b)
  /-- **`readWriteDifferentIdentity`**: `readWriteDifferent` at the identity sort. -/
  | readWriteDifferentIdentity {m : Tm C Γ .mem} {T : Ty} {a : Tm C Γ (.addr T)}
      {v : Tm C Γ (.mv T)} {R : RefTy} {b : Tm C Γ (.addr (.ref R))}
      (h : a.apart? b = true := by rfl) :
      EvalLaw (Tms.ITerm.read (Tms.MTerm.write m a v) b) (Tms.ITerm.read m b)
  /-- **`readOnWriteIdentity`**: `readOnWrite` at the identity sort,
  `read(write(m, a, ref(i)), a) ⇝ i` (`Heap.readAddr_writeAddr_same`). -/
  | readOnWriteIdentity {m : Tm C Γ .mem} {R : RefTy} {a : Tm C Γ (.addr (.ref R))}
      {i : Tm C Γ (.ident R)} :
      EvalLaw (Tms.ITerm.read (Tms.MTerm.write m a (Tms.MValT.ref i)) a) i

section EvalLawSound

variable {Γ : Ctx} {σ : State C Γ}

/-- The memory a read reads. -/
def Op2.memArg {a b s : Srt} : Op2 C a b s → Tm C Γ a → Option (Tm C Γ .mem)
  | .read, x => some x
  | .iread, x => some x
  | _, _ => none

/-- The memory a read reads (`read(m, a)`, at either sort).  Generic in the
sort. -/
def Tm.readMem? {u : Srt} : Tm C Γ u → Option (Tm C Γ .mem)
  | .app2 o x _ => o.memArg x
  | _ => none

theorem Tm.readMem?_eval {u : Srt} {t : Tm C Γ u} {X : Tm C Γ .mem} (h : t.readMem? = some X)
    (ht : t.eval σ ≠ none) : X.eval σ ≠ none := by
  cases t with
  | app2 o x y =>
    cases o <;> simp only [Tm.readMem?, Op2.memArg, Option.some.injEq, reduceCtorEq] at h
    all_goals
      subst h
      exact fun hx => ht (Tm.eval_app2_none _ x y hx)
  | _ => simp only [Tm.readMem?, reduceCtorEq] at h

/-- A memory write that returns: its parts, and the heap it leaves. -/
theorem Tm.write_some {T : Ty} {m : Tm C Γ .mem} {a : Tm C Γ (.addr T)} {v : Tm C Γ (.mv T)}
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

theorem Tm.eval_read {P : PrimTy} (X : Tm C Γ .mem) (b : Tm C Γ (.addr (.prim P))) :
    (Tms.Term.read X b).eval σ = (X.eval σ).bind fun μ => (b.eval σ).bind fun bd =>
      (bd.resolve μ.H').bind fun rb => μ.heap.readAddr rb := rfl

theorem Tm.eval_iread {R : RefTy} (X : Tm C Γ .mem) (b : Tm C Γ (.addr (.ref R))) :
    (Tms.ITerm.read X b).eval σ = (X.eval σ).bind fun μ => (b.eval σ).bind fun bd =>
      ((bd.resolve μ.H').bind fun rb => μ.heap.readAddr rb).bind fun r => some r.id := rfl

/-- **A memory law is exact past its write**: the read's memory returns
wherever the read does, and where it returns the two sides return alike. -/
theorem EvalLaw.exact {u : Srt} {t t' : Tm C Γ u} : EvalLaw t t' → ∃ X, t.readMem? = some X ∧
    ∀ σ : State C Γ, X.eval σ ≠ none → t.eval σ = t'.eval σ
  | .readOnWrite => ⟨_, rfl, fun σ hX => by
      obtain ⟨μ', hX⟩ := Option.ne_none_iff_exists'.1 hX
      obtain ⟨μ, ad, w, ra, mv, hp, -, ha, hv, hra, hmv, hw, rfl⟩ := Tm.write_some hX
      cases hv
      cases hmv
      rw [Tm.eval_read, hX, Option.bind_some, ha, Option.bind_some]
      show (ad.resolve μ.H').bind (fun rb => hp.readAddr rb) = _
      rw [hra, Option.bind_some, Heap.readAddr_writeAddr_same hw]
      rfl⟩
  | @EvalLaw.readWriteDifferent _ _ m T a v P b h => ⟨_, rfl, fun σ hX => by
      obtain ⟨μ', hX⟩ := Option.ne_none_iff_exists'.1 hX
      obtain ⟨μ, ad, w, ra, mv, hp, hm, ha, -, hra, -, hw, rfl⟩ := Tm.write_some hX
      rw [Tm.eval_read, Tm.eval_read, hX, hm, Option.bind_some, Option.bind_some]
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
  | @EvalLaw.readWriteDifferentIdentity _ _ m T a v R b h => ⟨_, rfl, fun σ hX => by
      obtain ⟨μ', hX⟩ := Option.ne_none_iff_exists'.1 hX
      obtain ⟨μ, ad, w, ra, mv, hp, hm, ha, -, hra, -, hw, rfl⟩ := Tm.write_some hX
      rw [Tm.eval_iread, Tm.eval_iread, hX, hm, Option.bind_some, Option.bind_some]
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
      rw [Tm.eval_iread, hX, Option.bind_some, ha, Option.bind_some]
      show ((ad.resolve μ.H').bind fun rb => hp.readAddr rb).bind _ = _
      rw [hra, Option.bind_some, Heap.readAddr_writeAddr_same hw, Option.bind_some]
      have hv : i.eval σ = some w := hv
      rw [hv]
      simp only [MvT.toMVal, HRef.ofId?] at hmv
      split at hmv
      · cases hmv; rfl
      · cases hmv⟩

/-- **A memory law keeps every value its left side returns.** -/
theorem EvalLaw.evalRefines {u : Srt} {t t' : Tm C Γ u} (r : EvalLaw t t') :
    Tm.EvalRefinesAt t t' := fun σ x hx => by
  obtain ⟨X, hX, he⟩ := r.exact
  rw [← he σ (Tm.readMem?_eval hX (by rw [hx]; exact Option.some_ne_none _))]
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

/-- **A memory write that is an element of an update that returns,
returns.** -/
theorem Upd.memory_eval_of_globT {σ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    {g : GlobT C σ.H} → U.globT σ = some g → ∀ s ∈ U.memTerms, s.eval σ ≠ none
  | _, .nil, _, _ => fun _ h => nomatch h
  | _, .snoc U e, g, h => by
    change (U.globT σ).bind (e.globT σ) = some g at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨g₀, hU, hw⟩ := h
    intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · exact Upd.memory_eval_of_globT U hU s hs
    · cases e with
      | memory s' =>
        simp only [UpdElem.memTerms, List.mem_singleton] at hs
        subst hs
        rw [UpdElem.globT_eq_globTM] at hw
        simp only [UpdElem.globTM, Option.bind_eq_some_iff] at hw
        obtain ⟨μ, hμ, -⟩ := hw
        rw [hμ]
        exact Option.some_ne_none _
      | _ => nomatch hs
  | _, .decl U _ r, g, h => by
    change (U.globT σ).bind (fun g => (r.eval σ).bind fun _ => some g) = some g at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨g₀, hU, -⟩ := h
    exact Upd.memory_eval_of_globT U hU
  | _, .pop U _, _, h | _, .drop U _, _, h => Upd.memory_eval_of_globT U h

/-- `U` writes the memory with a term on whose spine the memory `w` lies. -/
def Upd.holdsMem {Δ : Ctx} (U : Upd C Γ Δ) (w : Tm C Γ .mem) : Bool :=
  U.memTerms.any (·.onSpine w)

theorem Upd.holdsMem_eval {Δ : Ctx} {U : Upd C Γ Δ} {w : Tm C Γ .mem} (h : U.holdsMem w = true)
    {g : GlobT C σ.H} (hU : U.globT σ = some g) : w.eval σ ≠ none := by
  obtain ⟨S, hS, hs⟩ := List.any_eq_true.1 h
  exact Tm.onSpine_eval hs (Upd.memory_eval_of_globT U hU S hS)

/-- A covered memory law's write is held by the update. -/
def Upd.coversEval {Δ : Ctx} {u : Srt} (U : Upd C Γ Δ) (q : Tm C Γ u × Tm C Γ u) : Bool :=
  match q.1.readMem? with
  | some X => U.holdsMem X
  | none => false

/-- **Wherever a covered update returns, a memory law refines back.** -/
theorem EvalLaw.back {u : Srt} {t t' : Tm C Γ u} (r : EvalLaw t t') {Δ : Ctx} {U : Upd C Γ Δ}
    (hc : U.coversEval (t, t') = true) {g : GlobT C σ.H} (hU : U.globT σ = some g) :
    OLe (t'.eval σ) (t.eval σ) := by
  obtain ⟨X, hX, he⟩ := r.exact
  simp only [Upd.coversEval, hX] at hc
  rw [he σ (Upd.holdsMem_eval hc hU)]
  exact OLe.refl _

end EvalLawSound

/-! ## The laws, bundled -/

/-- A law at an update's right-hand sides, scoped: the right side returns what the
left side does (`fwd`), and wherever an update the check `chk` accepts returns, the
left side returns what the right side does (`back`). -/
structure LawCov (C : Contract) (Γ : Ctx) (u : Srt) (t t' : Tm C Γ u) where
  chk : {Δ : Ctx} → Upd C Γ Δ → Bool
  fwd : Tm.EvalRefinesAt t t'
  back : ∀ {Δ : Ctx} (U : Upd C Γ Δ) (σ : State C Γ) (g : GlobT C σ.H), chk U = true →
    U.globT σ = some g → OLe (t'.eval σ) (t.eval σ)

/-- A literal law, under any update. -/
def LawCov.lit {P : PrimTy} {t t' : Tm C Γ (.val P)} (r : LitLaw t t') : LawCov C Γ (.val P) t t' where
  chk _ := true
  fwd σ := (r.evalEq σ ▸ OLe.refl _)
  back _ σ _ _ _ := (r.evalEq σ ▸ OLe.refl _)

/-- **`findOnSave` at an update**: the read of a word written, where the
update holds the write. -/
def LawCov.findOnSave {P : PrimTy} (s : Tm C Γ .st) (p : Tm C Γ (.path (.prim P)))
    (w : P.Denote) : LawCov C Γ (.val P) (Tm.findSaveLit s p w) (Tms.Term.lit w) where
  chk U := U.holdsWrite (Tm.saveLit s p w)
  fwd := Tm.findSaveLit_fwd s p w
  back U σ g hc hU := by
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
  back _ σ _ _ _ := Tm.findMemberCons_eval h σ ▸ OLe.refl _

/-- **A term taclet onto a literal, where the update holds the write it
reads back** (`Upd.coversLit`): the read returns wherever the update does,
and the literal is what it returns (`TermTaclet.sound`). -/
def LawCov.covered {P : PrimTy} {t t' : Tm C Γ (.val P)} (r : TermTaclet t t')
    (ht : t'.isLit = true) : LawCov C Γ (.val P) t t' where
  chk U := U.coversLit t
  fwd := Tm.evalRefinesAt_of_theq r.sound ht
  back U σ g hc hU := fun x hx => by
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
  back _ _ _ hc hU := hr.back hc hU

/-- **Two member-wise forms of one read, under any update** (`Tm.sameBase`). -/
def LawCov.eqv {u : Srt} {t t' : Tm C Γ u} (h : Tm.sameBase t t' = true) : LawCov C Γ u t t' where
  chk _ := true
  fwd σ := Tm.sameBase_eval h σ ▸ OLe.refl _
  back _ σ _ _ _ := Tm.sameBase_eval h σ ▸ OLe.refl _

/-- **A memory law, where the update holds the write it reads past**
(`Upd.coversEval`). -/
def LawCov.eval {u : Srt} {t t' : Tm C Γ u} (r : EvalLaw t t') : LawCov C Γ u t t' where
  chk U := U.coversEval (t, t')
  fwd := r.evalRefines
  back _ _ _ hc hU := r.back hc hU

/-! ## A premise about closed terms, at any scope -/

/-- `KindFreeAt` of closed terms holds at any scope they are read in: a
chain's hypothesis about terms at the empty scope (`st!{ … }`, `pt!{ … }`)
gives a law's premise at an update's scope. -/
theorem Tm.KindFreeAt.ofNil {T : Ty} {s : Tm C Γ .st} {p : Tm C Γ (.path T)} {s₀ : Tm C [] .st}
    {p₀ : Tm C [] (.path T)} (h : Tm.KindFreeAt s₀ p₀) (hs : s.toNil? = some s₀)
    (hp : p.toNil? = some p₀) : Tm.KindFreeAt s p := fun σ => by
  rw [Tm.denote_toNilS σ s hs, Tm.denote_toNilS σ p hp]
  exact h σ.toNil

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
