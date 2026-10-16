import Solidity.Calculus.TermLib
import Solidity.Calculus.SeqRewrite
import Solidity.Calculus.StateFacts
import Solidity.Theory.Typed.Mem

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
(`Storage.findOnSave`, `Storage.find_selectT`), with no erased state.  The frame and
delete-value laws past an update are `TermTaclet.RefLaw` (`Upd.coversRef`);
the memory laws are `EvalLaw` (`Upd.coversEval`).
-/

namespace Solidity

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
    have e : some v = some x := e.symm
    rw [Option.some.inj e]
    rfl

/-! ## The literal laws -/

/-- KeY's `*_literals` taclets, as the typed evaluator computes them: the
side condition is the operator's typed evaluation of the two literals,
which decides the range check.  Hover a constructor for the taclet. -/
inductive LitLaw : {P : PrimTy} → Tm C Γ (.val P) → Tm C Γ (.val P) → Prop
  /-- **`add_literals`**: `a + b ⇝ a + b` folded, in `uint` range. -/
  | add_literals {a b c : PrimTy.uint.Denote} (h : BinOp.add.evalT (p := .uint) rfl a b = some c := by decide) :
      LitLaw (Tms.Term.binop .add .uint (Tms.Term.lit a) (Tms.Term.lit b)) (Tms.Term.lit c)
  /-- **`sub_literals`**: `a - b ⇝ a - b` folded, in `uint` range. -/
  | sub_literals {a b c : PrimTy.uint.Denote} (h : BinOp.sub.evalT (p := .uint) rfl a b = some c := by decide) :
      LitLaw (Tms.Term.binop .sub .uint (Tms.Term.lit a) (Tms.Term.lit b)) (Tms.Term.lit c)
  /-- **`leq_literals`**: `a <= b ⇝ true` or `false`. -/
  | leq_literals {a b : PrimTy.uint.Denote} {c : Bool} (h : BinOp.le.evalT (p := .uint) rfl a b = some c := by decide) :
      LitLaw (Tms.Term.binop .le .uint (Tms.Term.lit a) (Tms.Term.lit b)) (Tms.Term.litB c)
  /-- **`less_literals`**: `a < b ⇝ true` or `false`. -/
  | less_literals {a b : PrimTy.uint.Denote} {c : Bool} (h : BinOp.lt.evalT (p := .uint) rfl a b = some c := by decide) :
      LitLaw (Tms.Term.binop .lt .uint (Tms.Term.lit a) (Tms.Term.lit b)) (Tms.Term.litB c)
  /-- **`greater_literals`**: `a > b ⇝ true` or `false`. -/
  | greater_literals {a b : PrimTy.uint.Denote} {c : Bool}
      (h : BinOp.gt.evalT (p := .uint) rfl a b = some c := by decide) :
      LitLaw (Tms.Term.binop .gt .uint (Tms.Term.lit a) (Tms.Term.lit b)) (Tms.Term.litB c)
  /-- **`geq_literals`**: `a >= b ⇝ true` or `false`. -/
  | geq_literals {a b : PrimTy.uint.Denote} {c : Bool} (h : BinOp.ge.evalT (p := .uint) rfl a b = some c := by decide) :
      LitLaw (Tms.Term.binop .ge .uint (Tms.Term.lit a) (Tms.Term.lit b)) (Tms.Term.litB c)
  /-- **`div_literals`**: `a / b ⇝ a / b` folded (truncated, as Solidity divides), the divisor not
  zero. -/
  | div_literals {a b c : PrimTy.uint.Denote} (h : BinOp.div.evalT (p := .uint) rfl a b = some c := by decide) :
      LitLaw (Tms.Term.binop .div .uint (Tms.Term.lit a) (Tms.Term.lit b)) (Tms.Term.lit c)

/-- **A literal law is exact**: its right side is a literal, which its left
side returns in every state. -/
theorem LitLaw.exact {P : PrimTy} {t t' : Tm C Γ (.val P)} :
    LitLaw t t' → ∃ v, t' = Tms.Term.lit v ∧ ∀ σ : State C Γ, t.eval σ = some v
  | @LitLaw.add_literals _ _ a b c h => ⟨c, rfl, fun _ => (binopT_some .add rfl a b).trans h⟩
  | @LitLaw.sub_literals _ _ a b c h => ⟨c, rfl, fun _ => (binopT_some .sub rfl a b).trans h⟩
  | @LitLaw.leq_literals _ _ a b c h => ⟨c, rfl, fun _ => (binopT_some .le rfl a b).trans h⟩
  | @LitLaw.less_literals _ _ a b c h => ⟨c, rfl, fun _ => (binopT_some .lt rfl a b).trans h⟩
  | @LitLaw.greater_literals _ _ a b c h => ⟨c, rfl, fun _ => (binopT_some .gt rfl a b).trans h⟩
  | @LitLaw.geq_literals _ _ a b c h => ⟨c, rfl, fun _ => (binopT_some .ge rfl a b).trans h⟩
  | @LitLaw.div_literals _ _ a b c h => ⟨c, rfl, fun _ => (binopT_some .div rfl a b).trans h⟩

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
  rfl

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

/-- **A storage write that is an element of an update that reverts nowhere
returns or is out of gas.** -/
theorem Upd.storage_okx {σ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) → U.exhOk σ = true →
    ∀ s ∈ U.storTerms, (s.eval σ).isSome = true ∨ s.exhB σ = true
  | _, .nil, _ => fun _ h => nomatch h
  | _, .snoc U e, h => by
    simp only [Upd.exhOk, Bool.and_eq_true, Bool.or_eq_true] at h
    intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · exact Upd.storage_okx U h.1 s hs
    · cases e with
      | storage s' =>
        simp only [UpdElem.storTerms, List.mem_singleton] at hs
        subst hs
        exact h.2
      | _ => nomatch hs
  | _, .decl U _ _, h => by
    simp only [Upd.exhOk, Bool.and_eq_true] at h
    exact Upd.storage_okx U h.1
  | _, .pop U _, h | _, .drop U _, h => Upd.storage_okx U h

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
`Path.Diverges`, `Path.diverges_of_labels`), and an array's length where it
writes below one of its elements (`Storage.len_save_frame`). -/

section Frame

/-- **Two typed paths whose segments part, part** (`Path.Diverges`): the
Theory's `diverges` on the erased segments.  At one source type the two
paths take the same constructor at each step. -/
theorem Path.diverges_of_labels {T U W : Ty} (p : Path T U) (q : Path T W)
    (h : Theory.diverges p.labels q.labels = true) : Path.Diverges p q := by
  induction p generalizing W with
  | nil => simp only [Path.labels, Theory.diverges, Bool.false_eq_true] at h
  | @field s f T₁ U₁ hf p ih =>
    cases q with
    | nil => simp only [Path.labels, Theory.diverges, Bool.false_eq_true] at h
    | @field _ f' T₂ _ hf' q =>
      by_cases e : f = f'
      · subst e
        obtain rfl : T₁ = T₂ := Option.some.inj (hf.symm.trans hf')
        simp only [Path.labels, Theory.diverges, if_pos rfl] at h
        exact .fieldIn hf (ih q h)
      · exact .field hf hf' p q e
  | @«at» E U₁ i p ih =>
    cases q with
    | nil => simp only [Path.labels, Theory.diverges, Bool.false_eq_true] at h
    | «at» j q =>
      by_cases e : i = j
      · subst e
        simp only [Path.labels, Theory.diverges, if_pos rfl] at h
        exact .atIn i (ih q h)
      · exact .at p q e
  | @atF E U₁ n i p ih =>
    cases q with
    | nil => simp only [Path.labels, Theory.diverges, Bool.false_eq_true] at h
    | atF j q =>
      by_cases e : i = j
      · subst e
        simp only [Path.labels, Theory.diverges, if_pos rfl] at h
        exact .atFIn i (ih q h)
      · exact .atF p q e
  | @key K V U₁ k p ih =>
    cases q with
    | nil => simp only [Path.labels, Theory.diverges, Bool.false_eq_true] at h
    | key k' q =>
      by_cases e : k = k'
      · subst e
        simp only [Path.labels, Theory.diverges, if_pos rfl] at h
        exact .keyIn k (ih q h)
      · exact .key p q e

/-- The Theory's `diverges a (b ++ [x])`: `a` parts from `b`, or goes on
below it. -/
theorem diverges_append_single {a b : List Semantics.Selector} {x : Semantics.Selector}
    (h : Theory.diverges a (b ++ [x]) = true) :
    Theory.diverges a b = true ∨ ∃ rest, rest ≠ [] ∧ a = b ++ rest := by
  induction b generalizing a with
  | nil =>
    cases a with
    | nil => simp only [Theory.diverges, Bool.false_eq_true] at h
    | cons y a' => exact .inr ⟨y :: a', List.cons_ne_nil _ _, rfl⟩
  | cons c b' ih =>
    cases a with
    | nil => simp only [Theory.diverges, Bool.false_eq_true] at h
    | cons d a' =>
      simp only [List.cons_append, Theory.diverges] at h ⊢
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

/-- **A save leaves a reference that parts from it** (`findOnSaveFrame`,
solkey's `selectOnSaveCons` `\else`): across roots, or below one root,
by `Theory.diverges`. -/
theorem find_save_frame {U W : Ty} {st st' : Storage C} {r : SRef C U} {v : SVal U}
    {q : SRef C W} (hd : Theory.diverges r.labels q.labels = true)
    (h : st.save r v = some st') : st'.find q = st.find q := by
  obtain ⟨x', hs, rfl⟩ := save_some h
  rcases r with ⟨n, hr, p⟩
  rcases q with ⟨n', hq, p'⟩
  by_cases e : n = n'
  · subst e
    rename_i T₁ T₂
    obtain rfl : T₁ = T₂ := Option.some.inj (hr.symm.trans hq)
    simp only [SRef.labels, Theory.diverges, if_pos rfl] at hd
    show ((SFields.set st hr x').get hr).find p' = (st.get hr).find p'
    rw [SFields.get_set_same]
    rw [SVal.save_eq_saveM] at hs
    rw [SVal.find_eq_findM, SVal.find_eq_findM]
    exact SVal.findM_saveM_diverges (Path.diverges_of_labels p p' hd) _ v hs
  · show ((SFields.set st hr x').get hq).find p' = (st.get hq).find p'
    rw [SFields.get_set_ne _ hr hq e]

/-- `lenU` of one count, whatever its bound's proof. -/
theorem lenU_congr {n m : Nat} (e : n = m) (h : n < 2 ^ 256) (h' : m < 2 ^ 256) :
    lenU n h = lenU m h' := by
  subst e; rfl

/-- **A save leaves an array's length** where it parts from the length's
path (`lenOnSaveFrame`): elsewhere, or below one of the array's
elements. -/
theorem len_save_frame {U E : Ty} {st st' : Storage C} {r : SRef C U} {v : SVal U}
    {q : SRef C (.ref (.array E))}
    (hd : Theory.diverges r.labels (q.labels ++ [Theory.lengthSeg]) = true)
    (h : st.save r v = some st') : st'.len q = st.len q := by
  rcases diverges_append_single hd with hd | ⟨rest, hne, he⟩
  · simp only [Storage.len, find_save_frame hd h]
  · obtain ⟨x', hs, rfl⟩ := save_some h
    rcases r with ⟨n, hr, p⟩
    rcases q with ⟨n', hq, p'⟩
    simp only [SRef.labels, List.cons_append, List.cons.injEq,
      Semantics.Selector.root.injEq] at he
    obtain ⟨rfl, he⟩ := he
    rename_i T₁ T₂
    obtain rfl : T₁ = T₂ := Option.some.inj (hr.symm.trans hq)
    obtain ⟨rr, rfl, hrr⟩ := Path.split_of_labels p' p he
    cases rr with
    | nil =>
      rw [Path.labels_nil] at hrr
      exact absurd hrr.symm hne
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

theorem Tm.find_evalT {P : PrimTy} (s : Tm C Γ .st) (q : Tm C Γ (.path (.prim P))) :
    (Tms.Term.find s q).eval σ =
      (s.eval σ).bind fun st => (q.eval σ).bind fun r => (st.find r).bind fun v => some v.view :=
  rfl
theorem Tm.len_evalT {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tms.Term.len s q).eval σ = (s.eval σ).bind fun st => (q.eval σ).bind fun r => st.len r :=
  rfl
theorem Tm.delValue_evalT {P : PrimTy} (t : Tm C Γ (.val P)) :
    (Tms.Term.delValue t).eval σ = (t.eval σ).map fun _ => PrimTy.dflt P := rfl

/-- Two paths whose shapes part reach references that part. -/
theorem Tm.diverges_eval {T U : Ty} {p : Tm C Γ (.path T)} {q : Tm C Γ (.path U)}
    (h : p.diverges q = true) {r : SRef C T} {r' : SRef C U} (hp : p.eval σ = some r)
    (hq : q.eval σ = some r') : Theory.diverges r.labels r'.labels = true := by
  have e := Tm.diverges_segs σ h
  rwa [show p.denote σ = .ref r from Tm.denote_eval σ p r hp,
    show q.denote σ = .ref r' from Tm.denote_eval σ q r' hq] at e

/-- A path that leaves another's length reaches a reference that does. -/
theorem Tm.divergesLen_eval {T U : Ty} {q : Tm C Γ (.path T)} {p : Tm C Γ (.path U)}
    (h : q.divergesLen p = true) {r : SRef C T} {r' : SRef C U} (hq : q.eval σ = some r)
    (hp : p.eval σ = some r') :
    Theory.diverges r.labels (r'.labels ++ [Theory.lengthSeg]) = true := by
  have e := Tm.divergesLen_segs σ h
  rwa [show q.denote σ = .ref r from Tm.denote_eval σ q r hq,
    show p.denote σ = .ref r' from Tm.denote_eval σ p r' hp] at e

/-- Two paths of the same segments reach one reference. -/
theorem Tm.sameSegs_eval {T U : Ty} {p : Tm C Γ (.path T)} {q : Tm C Γ (.path U)}
    (h : p.sameSegs q = true) {r : SRef C T} {r' : SRef C U} (hp : p.eval σ = some r)
    (hq : q.eval σ = some r') : T = U ∧ HEq r r' := by
  obtain ⟨rfl, e⟩ := Tm.sameSegs_heq σ h
  have e := eq_of_heq e
  rw [show p.denote σ = .ref r from Tm.denote_eval σ p r hp,
    show q.denote σ = .ref r' from Tm.denote_eval σ q r' hq] at e
  cases e
  exact ⟨rfl, HEq.rfl⟩

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
  rw [Tm.find_evalT, Tm.find_evalT, he, hs, Option.bind_some, Option.bind_some]
  cases hq : q.eval σ with
  | none => rfl
  | some rq => simp only [Option.bind_some, Storage.find_save_frame (Tm.diverges_eval hd hp hq) hw]

/-- **A length read off a save, where the save returns, reads under it.** -/
theorem Tm.len_frame_eval {s s' : Tm C Γ .st} {T : Ty} {q : Tm C Γ (.path T)} {E : Ty}
    {p : Tm C Γ (.path (.ref (.array E)))} (hS : Tm.SavesAt σ s' q s)
    (hd : q.divergesLen p = true) {st' : Storage C} (he : s'.eval σ = some st') :
    (Tms.Term.len s' p).eval σ = (Tms.Term.len s p).eval σ := by
  obtain ⟨st, r, w, hs, hq, hw⟩ := hS st' he
  rw [Tm.len_evalT, Tm.len_evalT, he, hs, Option.bind_some, Option.bind_some]
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
  rw [Tm.find_evalT, Tm.delValue_evalT, Tm.find_evalT, he, hs, Option.bind_some, Option.bind_some]
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

theorem Op2.exhB_none_fst {H : HTy} {a b k : Srt} (o : Op2 C a b k) (y : Option (b.Den C H)) :
    o.exhB none y = false := by
  cases o <;> rfl

theorem Op3.exhB_none_fst {H : HTy} {a b c k : Srt} (o : Op3 C a b c k) (y : Option (b.Den C H))
    (z : Option (c.Den C H)) : o.exhB none y z = false := by
  cases o <;> rfl

/-- What a term out of gas reads first returns or is out of gas. -/
theorem Tm.onSpineAny_okx {σ : State C Γ} {k : Srt} {w : Tm C Γ k} {u : Srt} (t : Tm C Γ u)
    (h : Tm.onSpineAny w t = true) (ht : t.exhB σ = true) :
    (w.eval σ).isSome = true ∨ w.exhB σ = true := by
  cases hw : w.eval σ with
  | some _ => exact .inl rfl
  | none =>
    refine .inr ?_
    induction t with
    | app1 o x ihx =>
      simp only [Tm.onSpineAny, Bool.or_eq_true] at h
      simp only [Tm.exhB, Bool.and_eq_true] at ht
      rcases h with h | h
      · cases Tm.sigma_eq_of_beqR h; exact ht.2
      · exact ihx h ht.2
    | app2 o x y ihx _ =>
      simp only [Tm.onSpineAny, Bool.or_eq_true] at h
      have hx : x.eval σ = none := by
        rcases h with h | h
        · cases Tm.sigma_eq_of_beqR h; exact hw
        · exact Classical.byContradiction fun hx => Tm.onSpineAny_eval x h hx hw
      simp only [Tm.exhB, hx, Op2.exhB_none_fst, Option.isSome_none, Bool.and_false,
        Bool.false_and, Bool.or_false, Bool.false_or, Bool.and_eq_true] at ht
      rcases h with h | h
      · cases Tm.sigma_eq_of_beqR h; exact ht.2.1
      · exact ihx h ht.2.1
    | app3 o x y z ihx _ _ =>
      simp only [Tm.onSpineAny, Bool.or_eq_true] at h
      have hx : x.eval σ = none := by
        rcases h with h | h
        · cases Tm.sigma_eq_of_beqR h; exact hw
        · exact Classical.byContradiction fun hx => Tm.onSpineAny_eval x h hx hw
      simp only [Tm.exhB, hx, Op3.exhB_none_fst, Option.isSome_none, Bool.and_false,
        Bool.false_and, Bool.or_false, Bool.false_or, Bool.and_eq_true] at ht
      rcases h with h | h
      · cases Tm.sigma_eq_of_beqR h; exact ht.2.1.1
      · exact ihx h ht.2.1.1
    | _ => simp only [Tm.onSpineAny, Bool.false_eq_true] at h

/-- What a term that returns or is out of gas has on its spine returns or
is out of gas. -/
theorem Tm.onSpine_okx {σ : State C Γ} {k : Srt} {t w : Tm C Γ k} (h : t.onSpine w = true)
    (ht : (t.eval σ).isSome = true ∨ t.exhB σ = true) :
    (w.eval σ).isSome = true ∨ w.exhB σ = true := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain rfl := Tm.eq_of_beqR h; exact ht
  · rcases ht with ht | ht
    · left
      have := Tm.onSpineAny_eval (σ := σ) (w := w) t h (by
        intro hn; rw [hn] at ht; cases ht)
      cases hw : w.eval σ with
      | none => exact absurd hw this
      | some _ => rfl
    · exact Tm.onSpineAny_okx t h ht

/-- `U` writes the storage with a term on whose spine the write `w` lies, a
term with no push (`Tm.pushFree`): `w` returns wherever `U` reverts nowhere
(it is never out of gas). -/
def Upd.holdsWrite {Δ : Ctx} (U : Upd C Γ Δ) (w : Tm C Γ .st) : Bool :=
  w.pushFree && U.storTerms.any (·.onSpine w)

theorem Upd.holdsWrite_eval {Δ : Ctx} {U : Upd C Γ Δ} {w : Tm C Γ .st}
    (h : U.holdsWrite w = true) {σ : State C Γ} (hU : U.exhOk σ = true) :
    w.eval σ ≠ none := by
  obtain ⟨hp, h⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨S, hS, hs⟩ := List.any_eq_true.1 h
  have hw := Tm.onSpine_okx hs (Upd.storage_okx U hU S hS)
  rw [Tm.exhB_of_pushFree σ w hp] at hw
  intro hn
  rw [hn] at hw
  simp only [Option.isSome_none, Bool.false_eq_true, or_self] at hw

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
    (hU : U.exhOk σ = true) : OLe (t'.eval σ) (t.eval σ) := by
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
save or delete of the path from `r`, seen from `r` (`Storage.save_underAt`,
`Storage.delete_underAt`); under a `selectIn(…, f)`, from `r.f`.  So a
storage of members built by `saveIn`, `delAtIn` and `selectIn` over one
`select` is the storage term it reads seen from a struct's path (`Tm.base`),
and a read of it returns exactly what the read it is returns
(`Tm.base?_eval`): two member-wise forms of one read have one base
(`Tm.sameBase`), and a law between them is exact under any update
(`LawCov.eqv`). -/

section MemberWise

/-! ### Paths and references below a prefix -/

/-- A member path under the struct at `ref`, as a path from the root. -/
def SRef.underAt {C : Contract} {s : Name} {U : Ty} (q : SRef (Contract.ofStruct s) U)
    (ref : SRef C (.ref (.struct s))) : SRef C U :=
  ref.append (.field q.hroot q.path)

/-- A member after a member path, under `ref`. -/
theorem SRef.underAt_field {C : Contract} {s s' f : Name} {T : Ty}
    (q : SRef (Contract.ofStruct s) (.ref (.struct s'))) (hg : C.fieldType s' f = some T)
    (ref : SRef C (.ref (.struct s))) :
    (q.field (C := Contract.ofStruct s) hg).underAt ref = (q.underAt ref).field hg := by
  simp only [SRef.underAt, SRef.field, SRef.append, Path.append_assoc, Path.append_field]

namespace Storage

variable {C : Contract}

/-- The value of a struct at a reference, as a storage of its members. -/
abbrev viewAt {s : Name} (v : SVal (.ref (.struct s))) : Storage (Contract.ofStruct s) :=
  (SVal.view v : SFields (Semantics.structDef s))

theorem find_append {U W : Ty} (st : Storage C) (r : SRef C U) (q : Path U W) :
    st.find (r.append q) = (st.find r).bind (·.find q) := by
  simp only [Storage.find, SRef.append, SVal.find_eq_findM, SVal.findM_append]

/-- A read of a member path under `ref`: the read of the member path in the
struct found at `ref`. -/
theorem find_underAt {s : Name} {U : Ty} (st : Storage C) (ref : SRef C (.ref (.struct s)))
    (q : SRef (Contract.ofStruct s) U) :
    st.find (q.underAt ref) = (st.find ref).bind fun v => (viewAt v).find q := by
  rw [SRef.underAt, find_append]
  cases st.find ref with
  | none => rfl
  | some v =>
    cases v with
    | struct fs =>
      simp only [Option.bind_some, SVal.find_eq_findM, SVal.findM, Storage.find]
      rfl

/-- A member of the struct found at `ref`, as a storage. -/
theorem find_field_viewAt {s s' f : Name} (st : Storage C) (ref : SRef C (.ref (.struct s)))
    (hf : C.fieldType s f = some (.ref (.struct s'))) :
    ((st.find ref).map viewAt).map (fun fs => fs.selectT (C := Contract.ofStruct s) hf) =
      (st.find (ref.field hf)).map viewAt := by
  rw [SRef.field, find_append]
  cases st.find ref with
  | none => rfl
  | some v =>
    cases v with
    | struct fs =>
      simp only [Option.map_some, Option.bind_some, SVal.find_eq_findM, SVal.findM]
      rfl

/-- A save of a member path under `ref`, seen from `ref`, is the save in the
struct found there. -/
theorem save_underAt {s : Name} {U : Ty} (st : Storage C) (ref : SRef C (.ref (.struct s)))
    (q : SRef (Contract.ofStruct s) U) (w : SVal U) :
    (st.save (q.underAt ref) w).bind (fun st' => (st'.find ref).map viewAt) =
      (st.find ref).bind fun v => (viewAt v).save q w := by
  rcases ref with ⟨n, hr, p⟩
  simp only [SRef.underAt, SRef.append, Storage.save, Storage.find, SVal.save_eq_saveM,
    SVal.find_eq_findM, Option.bind_eq_bind]
  rw [SVal.saveM_append_eq]
  cases hy : (st.get hr).findM p with
  | none => rfl
  | some y =>
    cases y with
    | struct fs =>
      simp only [Option.bind_some, SVal.saveM, Option.bind_eq_bind, Storage.viewAt, SVal.view_struct]
      cases hz : (fs.get q.hroot).saveM q.path w with
      | none => simp only [Option.bind_none]
      | some z =>
        simp only [Option.bind_some]
        obtain ⟨x', hx'⟩ := SVal.saveM_of_findM _ p hy (.struct (fs.set q.hroot z))
        rw [hx']
        simp only [Option.bind_some, SFields.get_set_same, SVal.findM_saveM _ p _ hx',
          Option.map_some, SVal.view_struct]

theorem write_underAt {s : Name} {U : Ty} (st : Storage C) (ref : SRef C (.ref (.struct s)))
    (q : SRef (Contract.ofStruct s) U) (w : SVal U) :
    (st.write (q.underAt ref) w).bind (fun st' => (st'.find ref).map viewAt) =
      (st.find ref).bind fun v => (viewAt v).write q w := by
  unfold Storage.write
  split
  · exact save_underAt st ref q w
  · rw [find_underAt]
    cases hf : st.find ref with
    | none => rfl
    | some v =>
      simp only [Option.bind_some, Option.bind_eq_bind]
      cases (viewAt v).find q with
      | none => rfl
      | some x =>
        simp only [Option.bind_some]
        rw [save_underAt, hf, Option.bind_some]

theorem delete_underAt {s : Name} {U : Ty} (st : Storage C) (ref : SRef C (.ref (.struct s)))
    (q : SRef (Contract.ofStruct s) U) :
    (st.delete (q.underAt ref)).bind (fun st' => (st'.find ref).map viewAt) =
      (st.find ref).bind fun v => (viewAt v).delete q := by
  unfold Storage.delete
  rw [find_underAt]
  cases hf : st.find ref with
  | none => rfl
  | some v =>
    simp only [Option.bind_some, Option.bind_eq_bind]
    cases (viewAt v).find q with
    | none => rfl
    | some x =>
      simp only [Option.bind_some]
      rw [save_underAt, hf, Option.bind_some]

end Storage

variable {Γ : Ctx}

/-- What `Tm.unshift` gives at a sort: a member path as a path from the
root. -/
@[reducible] def Srt.Unsh (C : Contract) (Γ : Ctx) : Srt → Type
  | .spath _ T => Tm C Γ (.path T)
  | _ => PUnit

/-- A member under the struct at `pre`. -/
def Op0.unshStep {sn : Name} (pre : Tm C Γ (.path (.ref (.struct sn)))) {u : Srt} :
    Op0 C u → Option (Srt.Unsh C Γ u)
  | .member s _ hf => if h : s = sn then some (.app1 (.field (h ▸ hf)) pre) else none
  | _ => none

/-- A member after a member path, under its prefix. -/
def Op1.unshStep {a u : Srt} : Op1 C a u → Option (Srt.Unsh C Γ a) → Option (Srt.Unsh C Γ u)
  | .fieldIn hf, ih => ih.map fun p => .app1 (.field hf) p
  | _, _ => none

/-- A member path read from the path `pre` of the struct `sn` it is in: `age`
under `alice` is `alice.age`.  Generic in the sort; `none` on anything but
members. -/
def Tm.unshift {sn : Name} (pre : Tm C Γ (.path (.ref (.struct sn)))) :
    {u : Srt} → Tm C Γ u → Option (Srt.Unsh C Γ u)
  | _, .app0 o => o.unshStep pre
  | _, .app1 o x => o.unshStep (Tm.unshift pre x)
  | _, _ => none

/-- What `unshift` gives reads, from the root, the member path it read. -/
def Srt.UnshOK (σ : State C Γ) {sn : Name} (pre : Tm C Γ (.path (.ref (.struct sn)))) :
    (u : Srt) → Option (u.Den C σ.H) → Option (Srt.Unsh C Γ u) → Prop
  | .spath s _, x, some p' => ∀ (h : s = sn) (ref : SRef C (.ref (.struct sn))),
      pre.eval σ = some ref → p'.eval σ = x.map fun q => (h ▸ q).underAt ref
  | _, _, _ => True

theorem Srt.UnshOK.none (σ : State C Γ) {sn : Name} (pre : Tm C Γ (.path (.ref (.struct sn))))
    {u : Srt} (x : Option (u.Den C σ.H)) : Srt.UnshOK σ pre u x none := by
  cases u <;> trivial

theorem Tm.unshift_eval (σ : State C Γ) {sn : Name} (pre : Tm C Γ (.path (.ref (.struct sn))))
    {u : Srt} (p : Tm C Γ u) : Srt.UnshOK σ pre u (p.eval σ) (Tm.unshift pre p) := by
  induction p with
  | app0 o =>
    cases o with
    | member s f hf =>
      show Srt.UnshOK σ pre _ _ (if h : s = sn then _ else none)
      split
      · rename_i h
        subst h
        intro _ ref hpre
        show (pre.eval σ).map (·.field hf) = some ((SRef.ofRoot (C := Contract.ofStruct s) f hf).underAt ref)
        rw [hpre]
        rfl
      · exact Srt.UnshOK.none σ pre _
    | _ => exact Srt.UnshOK.none σ pre _
  | app1 o x ih =>
    cases o with
    | fieldIn hf =>
      show Srt.UnshOK σ pre _ _ ((Tm.unshift pre x).map _)
      revert ih
      cases Tm.unshift pre x with
      | none => intro _; exact Srt.UnshOK.none σ pre _
      | some p' =>
        intro ih h ref hpre
        subst h
        have ih : p'.eval σ = (x.eval σ).map fun q => q.underAt ref := ih rfl ref hpre
        show (Tm.app1 (.field hf) p').eval σ = ((Tm.app1 (.fieldIn hf) x).eval σ).map _
        rw [Tm.eval_app1, Tm.eval_app1, Op1.eval_eq_evalM, Op1.eval_eq_evalM]
        simp only [Op1.evalM]
        rw [ih]
        cases x.eval σ with
        | none => rfl
        | some q => exact congrArg some (SRef.underAt_field q hf ref).symm
    | _ => exact Srt.UnshOK.none σ pre _
  | _ => exact Srt.UnshOK.none σ pre _

/-- A storage of members' base: the storage term it reads, and the path of
the struct it is seen from. -/
structure Based (C : Contract) (Γ : Ctx) (s : Name) where
  b : Tm C Γ .st
  pre : Tm C Γ (.path (.ref (.struct s)))

/-- What `Tm.base` gives at a sort. -/
@[reducible] def Srt.BaseD (C : Contract) (Γ : Ctx) : Srt → Type
  | .sts s => Based C Γ s
  | _ => PUnit

def Op1.baseStep {a u : Srt} : Op1 C a u → Tm C Γ a → Option (Srt.BaseD C Γ a) →
    Option (Srt.BaseD C Γ u)
  | .select r h, x, _ => some ⟨x, .app0 (.root r h)⟩
  | .selectIn hf, _, ih => ih.map fun bd => ⟨bd.b, .app1 (.field hf) bd.pre⟩
  | _, _, _ => none

def Op2.baseStep {a b u : Srt} : Op2 C a b u → Tm C Γ b → Option (Srt.BaseD C Γ a) →
    Option (Srt.BaseD C Γ u)
  | .delAtIn, y, ih => ih.bind fun bd =>
    (Tm.unshift bd.pre y).map fun p' => ⟨.app2 .delAt bd.b p', bd.pre⟩
  | _, _, _ => none

def Op3.baseStep {a b c u : Srt} : Op3 C a b c u → Tm C Γ b → Tm C Γ c →
    Option (Srt.BaseD C Γ a) → Option (Srt.BaseD C Γ u)
  | .saveIn, y, z, ih => ih.bind fun bd =>
    (Tm.unshift bd.pre y).map fun p' => ⟨.app3 .save bd.b p' z, bd.pre⟩
  | _, _, _, _ => none

/-- A storage of members as the storage term it reads seen from a struct's
path: `saveIn(select(s, r), p, v)` is `save(s, r.p, v)` seen from `r`, and
`selectIn(…, f)` the same seen from `r.f`.  Generic in the sort. -/
def Tm.base : {u : Srt} → Tm C Γ u → Option (Srt.BaseD C Γ u)
  | _, .app1 o x => o.baseStep x (Tm.base x)
  | _, .app2 o x y => o.baseStep y (Tm.base x)
  | _, .app3 o x y z => o.baseStep y z (Tm.base x)
  | _, _ => none

/-- What `base` gives evaluates, seen from its prefix, as the storage of
members. -/
def Srt.BaseOK (σ : State C Γ) : (u : Srt) → Option (u.Den C σ.H) → Option (Srt.BaseD C Γ u) → Prop
  | .sts _, x, some bd => (∃ ref, bd.pre.eval σ = some ref) ∧
      x = (bd.b.eval σ).bind fun st => (bd.pre.eval σ).bind fun ref =>
        (st.find ref).map Storage.viewAt
  | _, _, _ => True

theorem Srt.BaseOK.none (σ : State C Γ) {u : Srt} (x : Option (u.Den C σ.H)) :
    Srt.BaseOK σ u x none := by
  cases u <;> trivial

theorem Tm.base_eval (σ : State C Γ) {u : Srt} (t : Tm C Γ u) :
    Srt.BaseOK σ u (t.eval σ) (Tm.base t) := by
  induction t with
  | app1 o x ihx =>
    cases o with
    | select r h =>
      refine ⟨⟨_, rfl⟩, ?_⟩
      show (x.eval σ).map (fun st => st.selectT h) = _
      cases x.eval σ with
      | none => rfl
      | some st =>
        show some _ = (st.find (SRef.ofRoot r h)).map Storage.viewAt
        simp only [Storage.find, SRef.ofRoot, SVal.find_eq_findM, SVal.findM, Option.map_some]
        rfl
    | selectIn hf =>
      show Srt.BaseOK σ _ _ ((Tm.base x).map _)
      revert ihx
      cases Tm.base x with
      | none => intro _; exact Srt.BaseOK.none σ _
      | some bd =>
        intro ⟨⟨ref, hpre⟩, ihx⟩
        refine ⟨⟨ref.field hf, ?_⟩, ?_⟩
        · show (bd.pre.eval σ).map (·.field hf) = _
          rw [hpre]; rfl
        · show (x.eval σ).map (fun fs => Storage.selectT (C := Contract.ofStruct _) fs hf) = _
          rw [ihx]
          show _ = (bd.b.eval σ).bind fun st => ((bd.pre.eval σ).map (·.field hf)).bind fun ref =>
            (st.find ref).map Storage.viewAt
          rw [hpre]
          cases bd.b.eval σ with
          | none => rfl
          | some st =>
            simp only [Option.bind_some, Option.map_some]
            rw [← Storage.find_field_viewAt st ref hf]
    | _ => exact Srt.BaseOK.none σ _
  | app2 o x y ihx _ =>
    cases o with
    | delAtIn =>
      show Srt.BaseOK σ _ _ ((Tm.base x).bind _)
      revert ihx
      cases Tm.base x with
      | none => intro _; exact Srt.BaseOK.none σ _
      | some bd =>
        intro ⟨⟨ref, hpre⟩, ihx⟩
        have hy := Tm.unshift_eval σ bd.pre y
        revert hy
        show _ → Srt.BaseOK σ _ _ ((Tm.unshift bd.pre y).map _)
        cases Tm.unshift bd.pre y with
        | none => intro _; exact Srt.BaseOK.none σ _
        | some p' =>
          intro hy
          have hy : p'.eval σ = (y.eval σ).map fun q => q.underAt ref := hy rfl ref hpre
          refine ⟨⟨ref, hpre⟩, ?_⟩
          show ((x.eval σ).bind fun st => (y.eval σ).bind fun q => st.delete q) =
            ((bd.b.eval σ).bind fun st => (p'.eval σ).bind fun q => st.delete q).bind _
          rw [ihx, hy, hpre]
          cases bd.b.eval σ with
          | none => rfl
          | some st =>
            simp only [Option.bind_some]
            cases y.eval σ with
            | none => cases st.find ref <;> rfl
            | some q =>
              simp only [Option.map_some, Option.bind_some]
              rw [Storage.delete_underAt st ref q]
              cases st.find ref <;> rfl
    | _ => exact Srt.BaseOK.none σ _
  | app3 o x y z ihx _ _ =>
    cases o with
    | saveIn =>
      show Srt.BaseOK σ _ _ ((Tm.base x).bind _)
      revert ihx
      cases Tm.base x with
      | none => intro _; exact Srt.BaseOK.none σ _
      | some bd =>
        intro ⟨⟨ref, hpre⟩, ihx⟩
        have hy := Tm.unshift_eval σ bd.pre y
        revert hy
        show _ → Srt.BaseOK σ _ _ ((Tm.unshift bd.pre y).map _)
        cases Tm.unshift bd.pre y with
        | none => intro _; exact Srt.BaseOK.none σ _
        | some p' =>
          intro hy
          have hy : p'.eval σ = (y.eval σ).map fun q => q.underAt ref := hy rfl ref hpre
          refine ⟨⟨ref, hpre⟩, ?_⟩
          show ((x.eval σ).bind fun st => (y.eval σ).bind fun q => (z.eval σ).bind fun w =>
              st.write q w) =
            ((bd.b.eval σ).bind fun st => (p'.eval σ).bind fun q => (z.eval σ).bind fun w =>
              st.write q w).bind _
          rw [ihx, hy, hpre]
          cases bd.b.eval σ with
          | none => rfl
          | some st =>
            simp only [Option.bind_some]
            cases y.eval σ with
            | none => cases st.find ref <;> rfl
            | some q =>
              cases z.eval σ with
              | none => simp only [Option.map_some, Option.bind_some, Option.bind_none]; cases st.find ref <;> rfl
              | some w =>
                simp only [Option.map_some, Option.bind_some]
                rw [Storage.write_underAt st ref q w]
                cases st.find ref <;> rfl
    | _ => exact Srt.BaseOK.none σ _
  | _ => exact Srt.BaseOK.none σ _

/-- A read, member-wise, as the read it is: `findIn(select(s, r), p)` is
`find(s, r.p)`. -/
def Op2.readBase {a b u : Srt} : Op2 C a b u → Tm C Γ a → Tm C Γ b → Option (Srt.BaseD C Γ a) →
    Option (Tm C Γ u)
  | .find, x, y, _ => some (.app2 .find x y)
  | .findIn, _, y, ih => ih.bind fun bd =>
    (Tm.unshift bd.pre y).map fun q' => .app2 .find bd.b q'
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
        intro ⟨⟨ref, hpre⟩, hb⟩
        rw [hbx] at h
        simp only [Option.bind_some] at h
        have hy := Tm.unshift_eval σ bd.pre y
        revert hy
        cases hu : Tm.unshift bd.pre y with
        | none => rw [hu] at h; simp only [Option.map_none, reduceCtorEq] at h
        | some q' =>
          rw [hu] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          intro hy
          have hy : q'.eval σ = (y.eval σ).map fun q => q.underAt ref := hy rfl ref hpre
          show ((x.eval σ).bind fun st => (y.eval σ).bind fun q => (st.find q).bind fun v =>
              some v.view) =
            ((bd.b.eval σ).bind fun st => (q'.eval σ).bind fun q => (st.find q).bind fun v =>
              some v.view)
          rw [hb, hy, hpre]
          cases bd.b.eval σ with
          | none => rfl
          | some st =>
            simp only [Option.bind_some]
            cases y.eval σ with
            | none => cases st.find ref <;> rfl
            | some q =>
              simp only [Option.map_some, Option.bind_some, Storage.find_underAt]
              cases st.find ref <;> rfl
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

end MemberWise

/-! ## A read below a delete, covered -/

/-- `f` of the path a member is of, or on the way down from it, by members
only. -/
def Op1.fieldsStep (f : {T : Ty} → Tm C Γ (.path T) → Bool) {a s : Srt} :
    Op1 C a s → Tm C Γ a → Bool → Bool
  | .field _, x, ih => f x || ih
  | _, _, _ => false

/-- `f` of some path the term goes on below by members only.  Generic in
the sort. -/
def Tm.fieldsBelowAny (f : {T : Ty} → Tm C Γ (.path T) → Bool) : {u : Srt} → Tm C Γ u → Bool
  | _, .app1 o x => o.fieldsStep f x (x.fieldsBelowAny f)
  | _, _ => false

/-- A path read where the storage `st` has a value: generic in the sort,
nothing asked of the others. -/
def Srt.FoundIn (st : Storage C) {H : HTy} : (u : Srt) → Option (u.Den C H) → Prop
  | .path _, x => ∃ r, x = some r ∧ st.find r ≠ none
  | _, _ => True

/-- **Members below a path found are found**: a struct has every member. -/
theorem Tm.fieldsBelow_found {σ : State C Γ} {U : Ty} {p : Tm C Γ (.path U)} {st : Storage C}
    {r : SRef C U} (hp : p.eval σ = some r) (hr : st.find r ≠ none) {u : Srt} (q : Tm C Γ u) :
    q.fieldsBelowAny (·.beqR p) = true → Srt.FoundIn st u (q.eval σ) := by
  induction q with
  | app1 o x ih =>
    intro h
    cases o with
    | field hf =>
      have hx : Srt.FoundIn st _ (x.eval σ) := by
        rcases Bool.or_eq_true_iff.mp h with h | h
        · cases Tm.sigma_eq_of_beqR h
          exact ⟨r, hp, hr⟩
        · exact ih h
      obtain ⟨rx, hrx, hfx⟩ := hx
      refine ⟨rx.field hf, ?_, ?_⟩
      · rw [Tm.eval_app1, hrx, Op1.eval_eq_evalM]
        rfl
      · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hfx
        rw [SRef.field, Storage.find_append, hv]
        cases v with
        | struct fs =>
          simp only [Option.bind_some, SVal.find_eq_findM, SVal.findM]
          exact Option.some_ne_none _
    | _ => simp only [Tm.fieldsBelowAny, Op1.fieldsStep, Bool.false_eq_true] at h
  | _ => intro h; simp only [Tm.fieldsBelowAny, Bool.false_eq_true] at h

/-- A delete's path. -/
def Op2.delAtPath? {a b u : Srt} : Op2 C a b u → Tm C Γ b → Option ((T : Ty) × Tm C Γ (.path T))
  | .delAt, y => some ⟨_, y⟩
  | _, _ => none

/-- A storage term's path, where it deletes. -/
def Tm.delAtPath? {u : Srt} : Tm C Γ u → Option ((T : Ty) × Tm C Γ (.path T))
  | .app2 o _ y => o.delAtPath? y
  | _ => none

/-- A read of a delete, by members below its path, the delete held by `U`. -/
def Op2.findDelBelowStep {Δ : Ctx} (U : Upd C Γ Δ) {a b u : Srt} :
    Op2 C a b u → Tm C Γ a → Tm C Γ b → Bool
  | .find, x, y =>
    (x.delAtPath?.any fun p => y.beqR p.2 || y.fieldsBelowAny (·.beqR p.2)) && U.holdsWrite x
  | _, _, _ => false

/-- `find(delAt(s, p), p)` or `find(delAt(s, p), p.f₁…fₖ)`, the delete held by
`U` (`findOnDelAt`'s and `findOnDelAtBelow`'s reads). -/
def Tm.findDelBelowAt {Δ : Ctx} (U : Upd C Γ Δ) {u : Srt} : Tm C Γ u → Bool
  | .app2 o x y => o.findDelBelowStep U x y
  | _ => false

/-- **A read by members below a delete the update holds returns**: the
delete leaves its path found (`Storage.delete_save`), and a struct has every
member. -/
theorem Tm.findDelBelowAt_eval {Δ : Ctx} {U : Upd C Γ Δ} {σ : State C Γ}
    (hU : U.exhOk σ = true) {u : Srt} (b : Tm C Γ u) (h : Tm.findDelBelowAt U b = true) :
    b.eval σ ≠ none := by
  cases b with
  | app2 o x y =>
    cases o <;> simp only [Tm.findDelBelowAt, Op2.findDelBelowStep, Bool.false_eq_true,
      Bool.and_eq_true, Option.any_eq_true] at h
    obtain ⟨⟨⟨T, p⟩, hp, hpy⟩, hw⟩ := h
    obtain ⟨st', hst'⟩ := Option.ne_none_iff_exists'.1 (Upd.holdsWrite_eval hw hU)
    cases x with
    | app2 o' S p₀ =>
      cases o' <;> simp only [Tm.delAtPath?, Op2.delAtPath?, reduceCtorEq] at hp
      simp only [Option.some.injEq, Sigma.mk.injEq] at hp
      obtain ⟨rfl, hp⟩ := hp
      cases hp
      have he : ((S.eval σ).bind fun st => (p₀.eval σ).bind fun r => st.delete r) = some st' :=
        hst'
      simp only [Option.bind_eq_some_iff] at he
      obtain ⟨st, -, r, hr, hd⟩ := he
      obtain ⟨v₀, -, hsave⟩ := Storage.delete_save hd
      have hf : st'.find r ≠ none := by
        rw [Storage.find_save_same hsave]
        exact Option.some_ne_none _
      have hfound : Srt.FoundIn st' _ (y.eval σ) := by
        rcases Bool.or_eq_true_iff.mp hpy with hpy | hpy
        · cases Tm.sigma_eq_of_beqR hpy
          exact ⟨r, hr, hf⟩
        · exact Tm.fieldsBelow_found hr hf y hpy
      obtain ⟨rq, hrq, hfq⟩ := hfound
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hfq
      show ((Tm.app2 .delAt S p₀).eval σ).bind (fun st => (y.eval σ).bind fun r =>
        (st.find r).bind fun v => some v.view) ≠ none
      rw [hst', Option.bind_some, hrq, Option.bind_some, hv]
      exact Option.some_ne_none _
    | _ => simp only [Tm.delAtPath?, reduceCtorEq] at hp
  | _ => simp only [Tm.findDelBelowAt, Bool.false_eq_true] at h

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
`storage := save(s, p, sval(w))`; or a word by members below a delete `U`
holds (`Tm.findDelBelowAt`, `findOnDelAtBelow`'s reads).  Syntactic, so
that `rfl` decides it. -/
def Upd.coversLit {Δ : Ctx} {u : Srt} (U : Upd C Γ Δ) (t : Tm C Γ u) : Bool :=
  match t.base? with
  | some b => Tm.findSaveLitAt U b || Tm.findDelBelowAt U b
  | none => false

theorem Tm.findSaveLitAt_eval {Δ : Ctx} {U : Upd C Γ Δ} {σ : State C Γ}
    (hU : U.exhOk σ = true) {u : Srt} (b : Tm C Γ u) (h : Tm.findSaveLitAt U b = true) :
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
    (hc : U.coversLit t = true) {σ : State C Γ} (hU : U.exhOk σ = true) :
    t.eval σ ≠ none := by
  unfold Upd.coversLit at hc
  split at hc
  · rename_i b hb
    rw [Tm.base?_eval σ hb]
    rcases Bool.or_eq_true_iff.mp hc with hc | hc
    · exact Tm.findSaveLitAt_eval hU b hc
    · exact Tm.findDelBelowAt_eval hU b hc
  · nomatch hc


/-! ## The laws of memory reads

A memory read is no Theory equation (its Theory denotation is opaque), so a
law of one is a refinement of the run: where the read returns, its
replacement returns the same (`EvalLaw.exact`), on the typed heap
(`Heap.readAddr_writeAddr_same`, `Heap.readAddr_writeAddr_apart`).  Inside
an update over either modality the update must hold the write the law reads
past (`Upd.coversEval`), as `Upd.coversRef` for the storage. -/


section MemEval

variable {Γ : Ctx}

/-- An address term's shape: a member, or an element of an identity at an
index, literal or not. -/
inductive AddrShape (C : Contract) (Γ : Ctx) where
  | field (f : Name)
  | index (i : (R : RefTy) × Tm C Γ (.ident R)) (k : Option PrimTy.uint.Denote)

def Op1.addrStep {a u : Srt} : Op1 C a u → Option (AddrShape C Γ)
  | .mfield (f := f) _ => some (.field f)
  | _ => none

/-- A `uint` literal term, its value. -/
def Tm.uintLit? (y : Tm C Γ (.val .uint)) : Option PrimTy.uint.Denote :=
  match y.litW? with
  | some ⟨.uint, v⟩ => some v
  | _ => none

theorem Tm.uintLit?_eval {σ : State C Γ} {y : Tm C Γ (.val .uint)} {w : PrimTy.uint.Denote}
    (h : y.uintLit? = some w) : y.eval σ = some w := by
  cases y with
  | app0 o =>
    cases o with
    | lit v' =>
      simp only [Tm.uintLit?, Tm.litW?, Op0.litW?, Option.some.injEq] at h
      subst h
      rfl
    | _ => simp only [Tm.uintLit?, Tm.litW?, Op0.litW?, reduceCtorEq] at h
  | _ => simp only [Tm.uintLit?, Tm.litW?, reduceCtorEq] at h

def Op2.addrStep {a b u : Srt} : Op2 C a b u → Tm C Γ a → Tm C Γ b → Option (AddrShape C Γ)
  | .mat _, x, y => some (.index ⟨_, x⟩ y.uintLit?)
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
  | .index ⟨R, i⟩ k, ad => ∃ (id : Nat) (E : Ty) (a : ArrTy R T) (j : PrimTy.uint.Denote),
      i.eval σ = some id ∧ ad = MAddrT.index id a j ∧ ∀ k', k = some k' → j = k'

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
    have ha : ((x.eval σ).bind fun id => (y.eval σ).bind fun k => some (MAddrT.index id arr k)) =
      some ad := ha
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at ha
    obtain ⟨id, hi, w, hw, rfl⟩ := ha
    exact ⟨id, T, arr, w, hi, rfl, fun k' hk => Option.some.inj (hw.symm.trans (Tm.uintLit?_eval hk))⟩
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
    intro _ e
    exact hk ((hn k rfl).symm.trans (e.trans (hn' k' rfl)))
  · nomatch h

end MemEval

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
