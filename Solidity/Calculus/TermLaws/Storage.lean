import Solidity.Calculus.TermLib
import Solidity.Calculus.SeqRewrite
import Solidity.Calculus.StateFacts
import Solidity.Theory.Typed.Mem

/-!
# Term laws: literals and the storage's frame

Refinement of evaluation, the literal laws, what an update's elements
write, a storage law onto a literal, member-wise forms of a read, the
storage's frame and the delete-value laws in a run.

A piece of `Calculus/TermLaws.lean`, whose docstring describes the whole.
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
  /-- **`equal_literals`**: `a == b ⇝ true` or `false`. -/
  | equal_literals {a b : PrimTy.uint.Denote} {c : Bool}
      (h : BinOp.eqB.evalT (p := .uint) rfl a b = some c := by decide) :
      LitLaw (Tms.Term.binop .eqB .uint (Tms.Term.lit a) (Tms.Term.lit b)) (Tms.Term.litB c)
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
  | @LitLaw.equal_literals _ _ a b c h => ⟨c, rfl, fun _ => (binopT_some .eqB rfl a b).trans h⟩
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

end Solidity
