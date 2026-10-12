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
  chk U := U.storTerms.any (·.beqR (Tm.saveLit s p w))
  fwd := Tm.findSaveLit_fwd s p w
  back U σ g hc hU := by
    obtain ⟨t, ht, hb⟩ := List.any_eq_true.1 hc
    obtain rfl := Tm.eq_of_beqR hb
    obtain ⟨st', hst'⟩ := Upd.storage_eval_of_globT U hU _ ht
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
