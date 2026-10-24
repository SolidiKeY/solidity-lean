import Solidity.Calculus.TermLaws.Storage

/-!
# Term laws: reads member-wise and of memory

Reading member-wise, a read below a delete and of a word written covered,
and the laws of memory reads.

A piece of `Calculus/TermLaws.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3)

variable {C : Contract} {Γ : Ctx}

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

def Op3.savePath {a b c u : Srt} : Op3 C a b c u → Tm C Γ b → Tm C Γ c →
    Option ((T : Ty) × Tm C Γ (.path T))
  | .save, y, _ => some ⟨_, y⟩
  | _, _, _ => none

/-- A storage term's path, where it saves. -/
def Tm.savePath {u : Srt} : Tm C Γ u → Option ((T : Ty) × Tm C Γ (.path T))
  | .app3 o _ y z => o.savePath y z
  | _ => none

/-- A read of a save of a literal word, at its path, or a length read at the
path of any save (`lenOnSaveFixedCopy`'s), the save held by `U`. -/
def Op2.findSaveLitStep {Δ : Ctx} (U : Upd C Γ Δ) {a b u : Srt} :
    Op2 C a b u → Tm C Γ a → Tm C Γ b → Bool
  | .find, x, y => (x.saveLitPath.any fun p => p.2.beqR y) && U.holdsWrite x
  | .len, x, y => (x.savePath.any fun p => p.2.beqR y) && U.holdsWrite x
  | _, _, _ => false

/-- `find(save(s, p, sval(w)), p)` or `len(save(s, p, v), p)`, the save held by `U`. -/
def Tm.findSaveLitAt {Δ : Ctx} (U : Upd C Γ Δ) {u : Srt} : Tm C Γ u → Bool
  | .app2 o x y => o.findSaveLitStep U x y
  | _ => false

/-- `t` reads, member-wise or not, the word a save writes at the path it
reads, and `U` holds the save: `find(save(s, p, sval(w)), p)` over
`storage := save(s, p, sval(w))`; or a word by members below a delete `U`
holds (`Tm.findDelBelowAt`, `findOnDelAtBelow`'s reads); or a length read
at the path of a save `U` holds (`Tm.findSaveLitAt` of `t` itself, which has
no `base?`).  Syntactic, so that `rfl` decides it. -/
def Upd.coversLit {Δ : Ctx} {u : Srt} (U : Upd C Γ Δ) (t : Tm C Γ u) : Bool :=
  (match t.base? with
    | some b => Tm.findSaveLitAt U b || Tm.findDelBelowAt U b
    | none => false) || Tm.findSaveLitAt U t

theorem Tm.findSaveLitAt_eval {Δ : Ctx} {U : Upd C Γ Δ} {σ : State C Γ}
    (hU : U.exhOk σ = true) {u : Srt} (b : Tm C Γ u) (h : Tm.findSaveLitAt U b = true) :
    b.eval σ ≠ none := by
  cases b with
  | app2 o x y =>
    cases o with
    | len =>
      simp only [Tm.findSaveLitAt, Op2.findSaveLitStep, Bool.and_eq_true,
        Option.any_eq_true] at h
      obtain ⟨⟨⟨T, p⟩, hp, hpy⟩, hw⟩ := h
      obtain ⟨st', hst'⟩ := Option.ne_none_iff_exists'.1 (Upd.holdsWrite_eval hw hU)
      cases x with
      | app3 o' s p₀ z =>
        cases o' <;> simp only [Tm.savePath, Op3.savePath, reduceCtorEq, Option.some.injEq,
          Sigma.mk.injEq] at hp
        obtain ⟨rfl, hp⟩ := hp
        cases hp
        cases Tm.sigma_eq_of_beqR hpy
        obtain ⟨st, r, w, -, hr, hsave⟩ := Tm.savesAt_save (σ := σ) s p₀ z st' hst'
        rw [Tm.len_evalT, hst', Option.bind_some, hr, Option.bind_some]
        simp only [Storage.len, Storage.find_save_same hsave, Option.bind_some]
        exact Option.some_ne_none _
      | _ => simp only [Tm.savePath, reduceCtorEq] at hp
    | find => ?_
    | _ => simp only [Tm.findSaveLitAt, Op2.findSaveLitStep, Bool.false_eq_true] at h
    simp only [Tm.findSaveLitAt, Op2.findSaveLitStep, Bool.and_eq_true, Option.any_eq_true] at h
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
  rcases Bool.or_eq_true_iff.mp hc with hc | hc
  · split at hc
    · rename_i b hb
      rw [Tm.base?_eval σ hb]
      rcases Bool.or_eq_true_iff.mp hc with hc | hc
      · exact Tm.findSaveLitAt_eval hU b hc
      · exact Tm.findDelBelowAt_eval hU b hc
    · nomatch hc
  · exact Tm.findSaveLitAt_eval hU t hc


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

end Solidity
