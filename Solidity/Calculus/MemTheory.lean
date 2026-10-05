import Solidity.Calculus.MemRead
import Solidity.Theory.CrossDomain
import Solidity.Theory.Bridge.Find

/-!
# The memory clauses agree with `memoryRules.key` and `structMemoryRules.key`

The closer's memory readers (`LMem.readT`, `LMem.readI`, `Calculus/MemRead.lean`)
are sound by the interpreter, and `docs/lean-key-rule-map.md` cites beside
each one the Theory lemma of the taclet it transcribes.  This module makes
those citations checked: a memory of the closer is read as a term of
`Theory/Terms.lean` (`LMem.toTheory`), and wherever a reader answers, its answer
is `Theory.Memory.readIn`'s on that term.  Each arm of the two theorems
closes by rewriting with the taclet's own lemma (`readOnWrite`,
`readAddEqual`, `readAddDifferent`, `initMember`, `initElement`, `initSize`,
`initIdentity`, `readCopySt`, `readCopyStOther`), and the copy arm reads the
copied storage through `SVal.abs_find`.  The shape steps and the defaults'
values hold by unfolding (`shapeStep`, `MemValue.asIntAt`), not by naming
`shapeAtMember` or `defaultDefInt`.

* **Roots.**  The `k`-th allocation is the root `shaped(ofNat(k), sh)`: an
  ordinal, not an object number, since the closer names an object by its
  birth (`MemNames.Births`).  The bottom of the term is `pre(heap)`, which no
  answered read reaches: a reader answers only below a root the memory
  allocated.  The shape is the allocated type's, which is what `initSize`
  reads a fixed array's length from.
* **The cast is the sort of the value read.**  KeY resolves `init<[α]>` by
  the sort the read is taken at; a `Value` carries its sort, so the read is
  cast as the closer's value is (`castLike`), an `int` by
  `MemValue.asIntAt` and a `bool` by `MemValue.asBool`.
* **Members are global in the Theory.**  `fieldShape` reads one member table,
  which the structs' declarations are not (`Basket.items` is `uint[]`,
  `FixedTriple.items` is `uint[3]`).  So a read's default agrees under
  `DeclAlong`, a hypothesis on that read alone: the table is the
  declarations of the members along its path below the allocated type, none
  named `length`.  The instance at the end discharges it.
* **A copy has no `addM`.**  KeY's `memoryStorageCopy` writes
  `copySt(addM(memory, root), root, find(storage, p))`; the image here is
  `copySt` alone, its root unshaped (`LMem.allocTy?` is `none`), since no read
  below a copy reaches the `addM` (`readCopySt` shadows the root) and a
  copy's lengths are read from storage.  `Theory.Memory.new` of the image
  therefore still counts the copy's root as fresh.
* **What the Theory term refuses.**  A write of a length, a member named
  `length`, and a value or an index that does not evaluate have no Theory
  term (`LSel.wseg`, `LSel.toSeg`): the closer never writes a length
  (`LMem.writeG`), and the Theory's `size` is the member `length`.
-/

namespace Solidity
namespace Decide
open Semantics SemanticsProperties

/-! ## A memory as a Theory term -/

/-- The root of the `k`-th allocation, tagged with its shape. -/
def rootT (sh : Nat → Theory.Shape) (k : Nat) : Theory.IdentityPrim :=
  .shaped (.ofNat k) (sh k)

theorem rootT_inj {sh : Nat → Theory.Shape} {k k' : Nat} (h : rootT sh k = rootT sh k') :
    k = k' := by
  simp only [rootT, Theory.IdentityPrim.shaped.injEq, Theory.IdentityPrim.ofNat.injEq] at h
  exact h.1

/-- A name as KeY's path identity `idC(root, path)`. -/
def LId.toTheory (sh : Nat → Theory.Shape) (i : LId) : Theory.Identity :=
  .idC (rootT sh i.root) i.path

theorem LId.toTheory_inj {sh : Nat → Theory.Shape} {i j : LId}
    (h : i.toTheory sh = j.toTheory sh) : i = j := by
  simp only [LId.toTheory, Theory.Identity.idC.injEq] at h
  obtain ⟨hr, hp⟩ := h
  cases i
  cases j
  simp only [LId.mk.injEq]
  exact ⟨rootT_inj hr, hp⟩

/-- The segment a selector reads: the length is the member `length`. -/
def LSel.toSeg (σ : State) : LSel → Option Seg
  | .fld f => if f = "length" then none else some (.field f)
  | .idx t => match t.eval σ >>= Value.asInt with
    | .ok c => some (.at c)
    | .error _ => none
  | .size => some (.field "length")

/-- The segment a selector writes: no length. -/
def LSel.wseg (σ : State) : LSel → Option Seg
  | .fld f => LSel.toSeg σ (.fld f)
  | .idx t => LSel.toSeg σ (.idx t)
  | .size => none

/-- A memory value: a word evaluated, a reference by its identity. -/
def LMV.toTheory (σ : State) (sh : Nat → Theory.Shape) : LMV → Option Theory.MemValue
  | .word t => match t.eval σ with
    | .ok p => some (.prim p)
    | .error _ => none
  | .ref j => some (.ident (j.toTheory sh))

/-- `new R(c)` (`memoryArrayFreshAlloc`): an array is `addM` with its length
written; anything else is `addM`. -/
def newT (M : Theory.Memory) (r : Theory.IdentityPrim) (R : RefTy) (c : Int) : Theory.Memory :=
  match R with
  | .array _ => .write (.addM M r R) (.idCC r) (.field "length") (.prim (.int c.toNat))
  | _ => .addM M r R

/-- **The memory as a Theory term**, its operands evaluated in `σ`: `init` is
`pre(σ.heap)`, a copy from storage is `copySt` of the subtree's `abs`. -/
def LMem.toTheory (σ : State) (sh : Nat → Theory.Shape) : LMem → Option Theory.Memory
  | .init => some (.pre σ.heap)
  | .addM m k R => (m.toTheory σ sh).map fun M => .addM M (rootT sh k) R
  | .newArr m k R n => (m.toTheory σ sh).bind fun M =>
      (n.eval σ >>= Value.asInt).toOption.map fun c => newT M (rootT sh k) R c
  | .copySt m k s q => (m.toTheory σ sh).bind fun M =>
      (s.eval σ >>= fun v => q.eval σ >>= v.findLive).toOption.map fun sv =>
        .copySt M (rootT sh k) sv.abs.asStruct
  | .write m j b v => (m.toTheory σ sh).bind fun M => (b.wseg σ).bind fun sg =>
      (v.toTheory σ sh).map fun w => .write M (j.toTheory sh) sg w

/-- The type the newest allocation of the root `k` allocated (`none` for a
copy, whose lengths are read from storage). -/
def LMem.allocTy? : LMem → Nat → Option RefTy
  | .init, _ => none
  | .addM m k R, k' | .newArr m k R _, k' => if k' = k then some R else m.allocTy? k'
  | .copySt m k _ _, k' => if k' = k then none else m.allocTy? k'
  | .write m _ _ _, k' => m.allocTy? k'

/-- Each root's shape, read off its allocation. -/
def LMem.shapes (m : LMem) (k : Nat) : Theory.Shape :=
  ((m.allocTy? k).map Theory.Shape.ofRefTy).getD .leaf

/-- The member table `decl` agrees with the structs' declarations along the
path `p` below `T`: each member the path names is declared at `decl`'s type,
and none is named `length`. -/
def DeclAlong (decl : Name → Ty) : Ty → List Seg → Prop
  | _, [] => True
  | T, s :: rest => match T, s with
    | .ref (.struct sn), .field f => ∀ U, lookupBy f (structDef sn) = some U →
        f ≠ "length" ∧ decl f = U ∧ DeclAlong decl U rest
    | .ref (.fixed E _), .at _ => DeclAlong decl E rest
    | .ref (.array E), .at _ => DeclAlong decl E rest
    | _, _ => True

/-- A slot cast at the sort of `v`. -/
def castLike (decl : Name → Ty) (loc : Theory.Identity) (a : Seg) (mv : Theory.MemValue) :
    Value → Value
  | .int _ => .int (Theory.MemValue.asIntAt decl mv loc a)
  | .bool _ => .bool mv.asBool

/-! ## Inversions -/

theorem toTheory_addM {σ : State} {sh : Nat → Theory.Shape} {m : LMem} {k : Nat} {R : RefTy}
    {M : Theory.Memory} (h : (LMem.addM m k R).toTheory σ sh = some M) :
    ∃ M', m.toTheory σ sh = some M' ∧ M = .addM M' (rootT sh k) R := by
  cases hm : m.toTheory σ sh with
  | none => simp only [LMem.toTheory, hm, Option.map_none, reduceCtorEq] at h
  | some M' =>
    simp only [LMem.toTheory, hm, Option.map_some, Option.some.injEq] at h
    exact ⟨M', rfl, h.symm⟩

theorem toTheory_newArr {σ : State} {sh : Nat → Theory.Shape} {m : LMem} {k : Nat} {R : RefTy}
    {n : LTerm} {M : Theory.Memory} (h : (LMem.newArr m k R n).toTheory σ sh = some M) :
    ∃ M' c, m.toTheory σ sh = some M' ∧ (n.eval σ >>= Value.asInt) = .ok c ∧
      M = newT M' (rootT sh k) R c := by
  cases hm : m.toTheory σ sh with
  | none => simp only [LMem.toTheory, hm, Option.bind_none, reduceCtorEq] at h
  | some M' =>
    cases hc : (n.eval σ >>= Value.asInt) with
    | error e => simp only [LMem.toTheory, hm, Except.toOption, hc, Option.map_none,
        Option.bind_fun_none, reduceCtorEq] at h
    | ok c =>
      simp only [LMem.toTheory, hm, Except.toOption, hc, Option.map_some, Option.bind_some,
          Option.some.injEq] at h
      exact ⟨M', c, rfl, rfl, h.symm⟩

theorem toTheory_copySt {σ : State} {sh : Nat → Theory.Shape} {m : LMem} {k : Nat} {s : LStor}
    {q : LPath} {M : Theory.Memory} (h : (LMem.copySt m k s q).toTheory σ sh = some M) :
    ∃ M' sv, m.toTheory σ sh = some M' ∧
      (s.eval σ >>= fun v => q.eval σ >>= v.findLive) = .ok sv ∧
      M = .copySt M' (rootT sh k) sv.abs.asStruct := by
  cases hm : m.toTheory σ sh with
  | none => simp only [LMem.toTheory, hm, Option.bind_none, reduceCtorEq] at h
  | some M' =>
    cases hc : (s.eval σ >>= fun v => q.eval σ >>= v.findLive) with
    | error e => simp only [LMem.toTheory, hm, Except.toOption, hc, Option.map_none,
        Option.bind_fun_none, reduceCtorEq] at h
    | ok sv =>
      simp only [LMem.toTheory, hm, Except.toOption, hc, Option.map_some, Option.bind_some,
          Option.some.injEq] at h
      exact ⟨M', sv, rfl, rfl, h.symm⟩

theorem toTheory_write {σ : State} {sh : Nat → Theory.Shape} {m : LMem} {j : LId} {b : LSel}
    {v : LMV} {M : Theory.Memory} (h : (LMem.write m j b v).toTheory σ sh = some M) :
    ∃ M' sb w, m.toTheory σ sh = some M' ∧ b.wseg σ = some sb ∧ v.toTheory σ sh = some w ∧
      M = .write M' (j.toTheory sh) sb w := by
  cases hm : m.toTheory σ sh with
  | none => simp only [LMem.toTheory, hm, Option.bind_none, reduceCtorEq] at h
  | some M' =>
    cases hb : b.wseg σ with
    | none => simp only [LMem.toTheory, hm, hb, Option.bind_none, Option.bind_fun_none,
        reduceCtorEq] at h
    | some sb =>
      cases hw : v.toTheory σ sh with
      | none => simp only [LMem.toTheory, hm, hb, hw, Option.map_none, Option.bind_fun_none,
          reduceCtorEq] at h
      | some w =>
        simp only [LMem.toTheory, hm, hb, hw, Option.map_some, Option.bind_some,
            Option.some.injEq] at h
        exact ⟨M', sb, w, rfl, rfl, rfl, h.symm⟩

theorem toSeg_fld {σ : State} {f : Name} {sg : Seg} (h : (LSel.fld f).toSeg σ = some sg) :
    f ≠ "length" ∧ sg = .field f := by
  simp only [LSel.toSeg] at h
  split at h
  · cases h
  · rename_i hf
    cases h
    exact ⟨hf, rfl⟩

theorem toSeg_idx {σ : State} {t : LTerm} {sg : Seg} (h : (LSel.idx t).toSeg σ = some sg) :
    ∃ c, (t.eval σ >>= Value.asInt) = .ok c ∧ sg = .at c := by
  simp only [LSel.toSeg] at h
  split at h
  · rename_i c hc
    cases h
    exact ⟨c, hc, rfl⟩
  · cases h

theorem eval_asInt {σ : State} {t : LTerm} {c : Int} (h : (t.eval σ >>= Value.asInt) = .ok c) :
    t.eval σ = .ok (.int c) := by
  cases ht : t.eval σ with
  | error e => simp only [bind, Except.bind, ht, reduceCtorEq] at h
  | ok v =>
    cases v with
    | int d => simp only [bind, Except.bind, ht, Value.asInt, Except.ok.injEq] at h; rw [h]
    | bool _ => simp only [bind, Except.bind, ht, Value.asInt, reduceCtorEq] at h

/-! ## Selectors -/

theorem selRel_same_seg {σ : State} {b a : LSel} {sb sg : Seg} (h : selRel b a = .same)
    (hb : b.wseg σ = some sb) (ha : a.toSeg σ = some sg) : sb = sg := by
  cases b with
  | size => simp only [LSel.wseg, reduceCtorEq] at hb
  | fld f =>
    obtain ⟨-, rfl⟩ := toSeg_fld (σ := σ) hb
    cases a with
    | fld g =>
      obtain ⟨-, rfl⟩ := toSeg_fld ha
      simp only [selRel] at h
      split at h
      · rename_i hfg
        rw [hfg]
      · cases h
    | idx t => simp only [selRel, reduceCtorEq] at h
    | size => simp only [selRel, reduceCtorEq] at h
  | idx w =>
    obtain ⟨cw, hcw, rfl⟩ := toSeg_idx (σ := σ) hb
    cases a with
    | idx r =>
      obtain ⟨cr, hcr, rfl⟩ := toSeg_idx ha
      simp only [selRel] at h
      split at h
      · split at h
        · rename_i hcd
          simp only [LTerm.eval, Res.ok_bind, Value.asInt, Except.ok.injEq] at hcr hcw
          rw [← hcr, ← hcw, hcd]
        · cases h
      · cases h
    | fld g => simp only [selRel, reduceCtorEq] at h
    | size => simp only [selRel, reduceCtorEq] at h

theorem selRel_apart_seg {σ : State} {b a : LSel} {sb sg : Seg} (h : selRel b a = .apart)
    (hb : b.wseg σ = some sb) (ha : a.toSeg σ = some sg) : sb ≠ sg := by
  cases b with
  | size => simp only [LSel.wseg, reduceCtorEq] at hb
  | fld f =>
    obtain ⟨hf, rfl⟩ := toSeg_fld (σ := σ) hb
    cases a with
    | fld g =>
      obtain ⟨-, rfl⟩ := toSeg_fld ha
      simp only [selRel] at h
      split at h
      · cases h
      · rename_i hfg
        simpa only [ne_eq, Seg.field.injEq] using hfg
    | idx t =>
      obtain ⟨c, -, rfl⟩ := toSeg_idx ha
      simp only [ne_eq, reduceCtorEq, not_false_eq_true]
    | size =>
      simp only [LSel.toSeg, Option.some.injEq] at ha
      subst ha
      simpa only [ne_eq, Seg.field.injEq] using hf
  | idx w =>
    obtain ⟨cw, hcw, rfl⟩ := toSeg_idx (σ := σ) hb
    cases a with
    | idx r =>
      obtain ⟨cr, hcr, rfl⟩ := toSeg_idx ha
      simp only [selRel] at h
      split at h
      · split at h
        · cases h
        · rename_i hcd
          simp only [LTerm.eval, Res.ok_bind, Value.asInt, Except.ok.injEq] at hcr hcw
          subst hcr hcw
          intro h
          cases h
          exact hcd rfl
      · cases h
    | fld g =>
      obtain ⟨-, rfl⟩ := toSeg_fld ha
      simp only [ne_eq, reduceCtorEq, not_false_eq_true]
    | size =>
      simp only [LSel.toSeg, Option.some.injEq] at ha
      subst ha
      simp only [ne_eq, reduceCtorEq, not_false_eq_true]

theorem selRel_key_seg {σ : State} {b a : LSel} {r w : LTerm} {sb sg : Seg}
    (h : selRel b a = .key r w) (hb : b.wseg σ = some sb) (ha : a.toSeg σ = some sg) :
    ∃ cr cw, (r.eval σ >>= Value.asInt) = .ok cr ∧ (w.eval σ >>= Value.asInt) = .ok cw ∧
      sg = .at cr ∧ sb = .at cw := by
  obtain ⟨rfl, rfl⟩ := selRel_key h
  obtain ⟨cw, hcw, rfl⟩ := toSeg_idx (σ := σ) hb
  obtain ⟨cr, hcr, rfl⟩ := toSeg_idx ha
  exact ⟨cr, cw, hcr, hcw, rfl, rfl⟩

/-! ## Defaults and shapes -/

theorem castLike_prim (decl : Name → Ty) (loc : Theory.Identity) (a : Seg) (p : Value) :
    castLike decl loc a (.prim p) p = p := by
  cases p <;> rfl

theorem seqL_ok {σ : State} {g a : LTerm} {v : Value} (h : (seqL g a).eval σ = .ok v) :
    a.eval σ = .ok v := by
  rw [seqL_eval] at h
  cases hg : g.eval σ with
  | error e => simp only [bind, Except.bind, hg, reduceCtorEq] at h
  | ok _ => simpa only [bind, Except.bind, hg] using h

/-- A primitive default read where `init<[int]>` is `0` (`initMember`,
`initElement`) is the cast of `dflt`. -/
theorem dfltWord_cast {σ : State} {decl : Name → Ty} {loc : Theory.Identity} {a : Seg}
    (h0 : Theory.MemValue.asIntAt decl .dflt loc a = 0) {T : Option Ty} {v : Value}
    (hv : (dfltWord T).eval σ = .ok v) : v = castLike decl loc a .dflt v := by
  match T, hv with
  | some (.prim q), hv =>
    simp only [dfltWord, LTerm.eval, Except.ok.injEq] at hv
    subst hv
    cases q <;> simp only [PrimTy.default, castLike, h0, Theory.MemValue.asBool]
  | some (.ref _), hv => simp only [dfltWord, LTerm.eval, reduceCtorEq] at hv
  | none, hv => simp only [dfltWord, LTerm.eval, reduceCtorEq] at hv

/-- One step of `shapeAt` is `Ty.at`'s. -/
theorem shapeStep_at {decl : Name → Ty} {T U : Ty} {s : Seg} {p : List Seg}
    (hd : DeclAlong decl T (s :: p)) (h : T.at s = some U) :
    Theory.shapeStep decl (Theory.Shape.ofTy T) s = Theory.Shape.ofTy U ∧ DeclAlong decl U p := by
  cases T with
  | prim q => cases s <;> simp only [Ty.at, reduceCtorEq] at h
  | ref R =>
    cases R with
    | struct sn =>
      cases s with
      | field f =>
        have h' : lookupBy f (structDef sn) = some U := h
        have hd' : ∀ V, lookupBy f (structDef sn) = some V →
            f ≠ "length" ∧ decl f = V ∧ DeclAlong decl V p := hd
        obtain ⟨hf, hdf, hp⟩ := hd' U h'
        refine ⟨?_, hp⟩
        simp only [Theory.shapeStep, Theory.Shape.ofTy, Theory.Shape.ofRefTy, hf, ↓reduceIte,
          Theory.fieldShape, hdf]
      | «at» k => simp only [Ty.at, reduceCtorEq] at h
    | array E => cases s <;> simp only [Ty.at, reduceCtorEq] at h
    | fixed E n =>
      cases s with
      | field f => simp only [Ty.at, reduceCtorEq] at h
      | «at» k =>
        simp only [Ty.at] at h
        split at h
        · cases h
          exact ⟨rfl, hd⟩
        · cases h
    | mapping K V => cases s <;> simp only [Ty.at, reduceCtorEq] at h

/-- `shapeAt` follows `Ty.memberTy` where `decl` is the declarations along
the path. -/
theorem shapeAt_memberTy {decl : Name → Ty} : ∀ (p : List Seg) (T U : Ty),
    DeclAlong decl T p → T.memberTy p = some U →
    Theory.shapeAt decl (Theory.Shape.ofTy T) p = Theory.Shape.ofTy U
  | [], T, U, _, h => by
    simp only [Ty.memberTy, Option.some.injEq] at h
    subst h
    rfl
  | s :: p, T, U, hd, h => by
    simp only [Ty.memberTy] at h
    cases hs : T.at s with
    | none => simp only [hs, Option.bind_none, reduceCtorEq] at h
    | some V =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨hstep, hp⟩ := shapeStep_at hd hs
      show Theory.shapeAt decl (Theory.shapeStep decl (Theory.Shape.ofTy T) s) p = _
      rw [hstep]
      exact shapeAt_memberTy p V U hp h

/-- **The default of a fresh object** (`readAddEqual`'s `dflt`, then
`initMember`, `initElement`, `initSize`): `dfltSel` is the cast of `dflt`. -/
theorem dfltSel_agree (σ : State) {decl : Name → Ty} {T : Option Ty} {r : Theory.IdentityPrim}
    {sh : Theory.Shape} {p : List Seg} {a : LSel} {sg : Seg} {v : Value}
    (hT : ∀ U, T = some U → Theory.shapeAt decl sh p = Theory.Shape.ofTy U)
    (hs : a.toSeg σ = some sg) (hv : (dfltSel T a).eval σ = .ok v) :
    v = castLike decl (.idC (.shaped r sh) p) sg .dflt v := by
  unfold dfltSel at hv
  split at hv
  · obtain ⟨hf, rfl⟩ := toSeg_fld hs
    exact dfltWord_cast (Theory.Memory.initMember decl _ p _ hf) hv
  · obtain ⟨c, -, rfl⟩ := toSeg_idx hs
    exact dfltWord_cast (Theory.Memory.initElement decl _ p c) (seqL_ok hv)
  · rename_i E n
    simp only [LSel.toSeg, Option.some.injEq] at hs
    subst hs
    simp only [LTerm.eval, Except.ok.injEq] at hv
    subst hv
    simp only [castLike, Theory.Memory.initSize, hT _ rfl, Theory.Shape.ofTy,
      Theory.Shape.ofRefTy, Theory.sizeOfFixed]
  · simp only [LSel.toSeg, Option.some.injEq] at hs
    subst hs
    simp only [LTerm.eval, Except.ok.injEq] at hv
    subst hv
    simp only [castLike, Theory.Memory.initSize, hT _ rfl, Theory.Shape.ofTy,
      Theory.Shape.ofRefTy, Theory.sizeOfDyn]
  · simp only [LTerm.eval, reduceCtorEq] at hv

/-- A read of `new R(n)` (`memoryArrayFreshAlloc`: `readOnWrite` at the length
written, `readAddEqual` below it). -/
theorem newSel_agree (σ : State) {decl : Name → Ty} {M : Theory.Memory}
    {r : Theory.IdentityPrim} {R : RefTy} {n : LTerm} {c : Int}
    (hn : (n.eval σ >>= Value.asInt) = .ok c) {p : List Seg} (hd : DeclAlong decl (.ref R) p)
    {a : LSel} {sg : Seg} {v : Value}
    (hs : a.toSeg σ = some sg) (hv : (newSel R n p a).eval σ = .ok v) :
    let rt : Theory.IdentityPrim := .shaped r (Theory.Shape.ofRefTy R)
    v = castLike decl (.idC rt p) sg (Theory.Memory.readIn (newT M rt R c) (.idC rt p) sg) v := by
  intro rt
  cases R with
  | array E =>
    simp only [newT]
    rw [Theory.Memory.readOnWrite]
    cases p with
    | nil =>
      cases a with
      | fld f => simp only [newSel, LTerm.eval, reduceCtorEq] at hv
      | idx t =>
        obtain ⟨c', -, rfl⟩ := toSeg_idx hs
        simp only [reduceCtorEq, and_false, if_false, Theory.Memory.readAddEqual]
        exact dfltWord_cast (Theory.Memory.initElement decl _ [] c') (seqL_ok hv)
      | size =>
        simp only [LSel.toSeg, Option.some.injEq] at hs
        subst hs
        simp only [newSel] at hv
        rw [natL_eval σ n (eval_asInt hn)] at hv
        cases hv
        simp only [and_self, if_true, castLike]
        rfl
    | cons s rest =>
      have hne : ¬ (Theory.Identity.idCC rt = .idC rt (s :: rest) ∧ Seg.field "length" = sg) := by
        simp only [Theory.Memory.idCCDef, Theory.Identity.idC.injEq, List.nil_eq, reduceCtorEq,
            and_false, false_and, not_false_eq_true]
      rw [if_neg hne, Theory.Memory.readAddEqual]
      cases s with
      | field f => simp only [newSel, LTerm.eval, reduceCtorEq] at hv
      | «at» j =>
        simp only [newSel] at hv
        refine dfltSel_agree σ (fun U hU => ?_) hs (seqL_ok hv)
        show Theory.shapeAt decl (Theory.Shape.ofTy E) rest = _
        exact shapeAt_memberTy rest E U hd hU
  | struct sn =>
    simp only [newT, newSel, Theory.Memory.readAddEqual] at hv ⊢
    exact dfltSel_agree σ (fun U hU => shapeAt_memberTy p (.ref (.struct sn)) U hd hU) hs hv
  | fixed E k =>
    simp only [newT, newSel, Theory.Memory.readAddEqual] at hv ⊢
    exact dfltSel_agree σ (fun U hU => shapeAt_memberTy p (.ref (.fixed E k)) U hd hU) hs hv
  | mapping K V =>
    simp only [newT, newSel, Theory.Memory.readAddEqual] at hv ⊢
    exact dfltSel_agree σ (fun U hU => shapeAt_memberTy p (.ref (.mapping K V)) U hd hU) hs hv

/-- A read below another root passes `new R(n)` (`readOnWrite`,
`readAddDifferent`). -/
theorem newT_other {M : Theory.Memory} {r r' : Theory.IdentityPrim} {R : RefTy} {c : Int}
    (hne : r ≠ r') (p : List Seg) (sg : Seg) :
    Theory.Memory.readIn (newT M r R c) (.idC r' p) sg = Theory.Memory.readIn M (.idC r' p) sg := by
  cases R with
  | array E =>
    simp only [newT]
    rw [Theory.Memory.readOnWrite, if_neg (by simp only [Theory.Memory.idCCDef,
        Theory.Identity.idC.injEq, hne, List.nil_eq, false_and, not_false_eq_true]),
      Theory.Memory.readAddDifferent _ _ _ _ _ _ hne]
  | struct _ | fixed _ _ | mapping _ _ =>
    exact Theory.Memory.readAddDifferent _ _ _ _ _ _ hne

/-! ## Copies from storage -/

theorem findSt_readAt : ∀ (P : List Seg) (w : Theory.StValue), P ≠ [] →
    Theory.StValue.findSt w.asStruct P = w.readAt P
  | [], _, h => absurd rfl h
  | [_], _, _ => rfl
  | a :: b :: rest, w, _ => by
    show Theory.StValue.findSt (Theory.StValue.selectSt w.asStruct a).asStruct (b :: rest) = _
    rw [findSt_readAt (b :: rest) _ (List.cons_ne_nil _ _)]
    rfl

theorem readAt_append : ∀ (P Q : List Seg) (w : Theory.StValue),
    w.readAt (P ++ Q) = (w.readAt P).readAt Q
  | [], _, _ => rfl
  | _ :: P, Q, _ => readAt_append P Q _

/-- A word the interpreter finds below a copy is `findSt` of its `abs`
(`SVal.abs_find`). -/
theorem copy_word {sv : SVal} {P : List Seg} {v : Value}
    (h : (sv.findLive P >>= SVal.asValue) = .ok v) (hP : P ≠ []) :
    Theory.StValue.findSt sv.abs.asStruct P = .prim v := by
  cases hw : sv.findLive P with
  | error e => simp only [bind, Except.bind, hw, reduceCtorEq] at h
  | ok w =>
    simp only [hw, bind, Except.bind] at h
    have hwv : w = .prim v := by
      cases w with
      | prim p => cases p <;> (simp only [SVal.asValue, Except.ok.injEq] at h; subst h; rfl)
      | struct _ | array _ _ _ | map _ _ => simp only [SVal.asValue, reduceCtorEq] at h
    subst hwv
    rw [findSt_readAt P _ hP, SVal.abs_find (SVal.find_of_findLive hw)]
    rfl

/-- A length the interpreter reads below a copy is the `length` member of its
`abs`. -/
theorem copy_len {sv : SVal} {P : List Seg} {v : Value}
    (h : (sv.findLive P >>= Close.arrLen) = .ok v) :
    Theory.StValue.findSt sv.abs.asStruct (P ++ [.field "length"]) = .prim v := by
  cases hw : sv.findLive P with
  | error e => simp only [bind, Except.bind, hw, reduceCtorEq] at h
  | ok w =>
    simp only [hw, bind, Except.bind] at h
    cases w with
    | array es shd fx =>
      simp only [Close.arrLen, Except.ok.injEq] at h
      subst h
      rw [findSt_readAt _ _ (by simp only [ne_eq, List.append_eq_nil_iff, List.cons_ne_self,
          and_false, not_false_eq_true]), readAt_append, SVal.abs_find (SVal.find_of_findLive hw)]
      simp only [Theory.StValue.readAt, SVal.select_abs_array]
      rfl
    | prim _ | struct _ | map _ _ => simp only [Close.arrLen, reduceCtorEq] at h

theorem LPath.ext_field_eval {σ : State} {q : LPath} {qs p : List Seg} (hq : q.eval σ = .ok qs)
    (f : Name) : ((q.ext p).field f).eval σ = .ok (qs ++ (p ++ [.field f])) := by
  simp only [LPath.eval, LPath.ext_eval, hq, Res.ok_bind, List.append_assoc]

theorem LPath.ext_at_eval {σ : State} {q : LPath} {qs p : List Seg} (hq : q.eval σ = .ok qs)
    {t : LTerm} {c : Int} (ht : (t.eval σ >>= Value.asInt) = .ok c) :
    ((q.ext p).at t).eval σ = .ok (qs ++ (p ++ [.at c])) := by
  simp only [LPath.eval, LPath.ext_eval, hq, Res.ok_bind, ht, List.append_assoc]

/-- **A read of a copy from storage** (`readCopySt`, and `readFromCopyToStorage`
with `findDefinitionSize` at the length). -/
theorem copySel_agree (σ : State) (decl : Name → Ty) (loc : Theory.Identity) {s : LStor}
    {q : LPath} {sv : SVal} (hsv : (s.eval σ >>= fun v => q.eval σ >>= v.findLive) = .ok sv)
    {p : List Seg} {a : LSel} {t : LTerm} {sg : Seg} {v : Value}
    (hc : copySel s q p a = some t) (hs : a.toSeg σ = some sg) (hv : t.eval σ = .ok v) :
    v = castLike decl loc sg
      (Theory.StValue.toMemValue (Theory.StValue.findSt sv.abs.asStruct (p ++ [sg]))) v := by
  cases hse : s.eval σ with
  | error e => simp only [bind, Except.bind, hse, reduceCtorEq] at hsv
  | ok vs =>
  cases hq : q.eval σ with
  | error e => simp only [bind, Except.bind, hse, hq, reduceCtorEq] at hsv
  | ok qs =>
  simp only [hse, hq, Res.ok_bind] at hsv
  cases a with
  | fld f =>
    obtain ⟨-, rfl⟩ := toSeg_fld hs
    simp only [copySel] at hc
    split at hc
    · cases hc
      simp only [LTerm.eval, hse, LPath.ext_field_eval hq, Res.ok_bind] at hv
      rw [SVal.findLive_append, hsv, Res.ok_bind] at hv
      rw [copy_word hv (by simp only [ne_eq, List.append_eq_nil_iff, List.cons_ne_self,
          and_false, not_false_eq_true])]
      exact (castLike_prim decl loc _ v).symm
    · cases hc
  | idx t' =>
    obtain ⟨c, hcv, rfl⟩ := toSeg_idx hs
    simp only [copySel] at hc
    split at hc
    · cases hc
      simp only [LTerm.eval, hse, LPath.ext_at_eval hq hcv, Res.ok_bind] at hv
      rw [SVal.findLive_append, hsv, Res.ok_bind] at hv
      rw [copy_word hv (by simp only [ne_eq, List.append_eq_nil_iff, List.cons_ne_self,
          and_false, not_false_eq_true])]
      exact (castLike_prim decl loc _ v).symm
    · cases hc
  | size =>
    simp only [LSel.toSeg, Option.some.injEq] at hs
    subst hs
    simp only [copySel] at hc
    split at hc
    · cases hc
      simp only [LTerm.eval, hse, LPath.ext_eval, hq, Res.ok_bind] at hv
      rw [SVal.findLive_append, hsv, Res.ok_bind] at hv
      rw [copy_len hv]
      exact (castLike_prim decl loc _ v).symm
    · cases hc

/-! ## The agreement theorems -/

/-- **`readT` is `readIn`.**  Wherever the closer's word reader answers and its
answer evaluates, the answer is the Theory's read of the memory's term, cast
at its sort.  `hsh` asks that the read root carry its allocated shape, which
`LMem.shapes` does (`LMem.readT_agree_shapes`), and that `decl` be the
declarations along the read's path below the allocated type. -/
theorem LMem.readT_agree (σ : State) {decl : Name → Ty} (sh : Nat → Theory.Shape) :
    (m : LMem) → ∀ (i : LId) (a : LSel) {t : LTerm} {M : Theory.Memory} {sg : Seg} {v : Value},
    (∀ R, m.allocTy? i.root = some R →
      sh i.root = Theory.Shape.ofRefTy R ∧ DeclAlong decl (.ref R) i.path) →
    m.toTheory σ sh = some M → a.toSeg σ = some sg → m.readT i a = some t → t.eval σ = .ok v →
    v = castLike decl (i.toTheory sh) sg (Theory.Memory.readIn M (i.toTheory sh) sg) v
  | .init, _, _, _, _, _, _, _, _, _, ht, _ => by simp only [LMem.readT, reduceCtorEq] at ht
  | .addM m k R, i, a, t, M, sg, v, hsh, hM, hs, ht, hv => by
    obtain ⟨M', hM', rfl⟩ := toTheory_addM hM
    by_cases hk : i.root = k
    · subst hk
      simp only [LMem.readT, if_true, Option.some.injEq] at ht
      subst ht
      obtain ⟨hR, hd⟩ := hsh R (by simp only [LMem.allocTy?, ↓reduceIte])
      simp only [LId.toTheory, rootT, hR, Theory.Memory.readAddEqual]
      exact dfltSel_agree σ (fun U hU => shapeAt_memberTy i.path (.ref R) U hd hU) hs hv
    · simp only [LMem.readT, hk, if_false] at ht
      simp only [LId.toTheory]
      rw [Theory.Memory.readAddDifferent _ _ _ _ _ _ (fun h => hk (rootT_inj h).symm)]
      exact LMem.readT_agree σ sh m i a
        (fun R' h => hsh R' (by simp only [LMem.allocTy?, hk, ↓reduceIte, h])) hM' hs ht hv
  | .newArr m k R n, i, a, t, M, sg, v, hsh, hM, hs, ht, hv => by
    obtain ⟨M', c, hM', hc, rfl⟩ := toTheory_newArr hM
    by_cases hk : i.root = k
    · subst hk
      simp only [LMem.readT, if_true, Option.some.injEq] at ht
      subst ht
      obtain ⟨hR, hd⟩ := hsh R (by simp only [LMem.allocTy?, ↓reduceIte])
      simp only [LId.toTheory, rootT, hR]
      exact newSel_agree σ hc hd hs hv
    · simp only [LMem.readT, hk, if_false] at ht
      simp only [LId.toTheory]
      rw [newT_other (fun h => hk (rootT_inj h).symm)]
      exact LMem.readT_agree σ sh m i a
        (fun R' h => hsh R' (by simp only [LMem.allocTy?, hk, ↓reduceIte, h])) hM' hs ht hv
  | .copySt m k s q, i, a, t, M, sg, v, hsh, hM, hs, ht, hv => by
    obtain ⟨M', sv, hM', hsv, rfl⟩ := toTheory_copySt hM
    by_cases hk : i.root = k
    · subst hk
      simp only [LMem.readT, if_true] at ht
      simp only [LId.toTheory, Theory.Memory.readCopySt]
      exact copySel_agree σ decl _ hsv ht hs hv
    · simp only [LMem.readT, hk, if_false] at ht
      simp only [LId.toTheory]
      rw [Theory.Memory.readCopyStOther _ _ _ _ _ _ (fun h => hk (rootT_inj h).symm)]
      exact LMem.readT_agree σ sh m i a
        (fun R' h => hsh R' (by simp only [LMem.allocTy?, hk, ↓reduceIte, h])) hM' hs ht hv
  | .write m j b w, i, a, t, M, sg, v, hsh, hM, hs, ht, hv => by
    obtain ⟨M', sb, mw, hM', hb, hw, rfl⟩ := toTheory_write hM
    rw [Theory.Memory.readOnWrite]
    have hsh' : ∀ R, m.allocTy? i.root = some R →
        sh i.root = Theory.Shape.ofRefTy R ∧ DeclAlong decl (.ref R) i.path := hsh
    by_cases hij : i = j
    · subst hij
      simp only [LMem.readT, if_true] at ht
      cases hr : selRel b a with
      | same =>
        simp only [hr, Option.some.injEq] at ht
        subst ht
        rw [if_pos ⟨rfl, selRel_same_seg hr hb hs⟩]
        cases w with
        | ref _ => simp only [LMV.wordT, LTerm.eval, reduceCtorEq] at hv
        | word t' =>
          simp only [LMV.wordT] at hv
          simp only [LMV.toTheory, hv, Option.some.injEq] at hw
          subst hw
          exact (castLike_prim decl _ _ v).symm
      | apart =>
        simp only [hr] at ht
        rw [if_neg (fun h => selRel_apart_seg hr hb hs h.2)]
        exact LMem.readT_agree σ sh m i a hsh' hM' hs ht hv
      | key r w' =>
        simp only [hr] at ht
        obtain ⟨t0, ht0, rfl⟩ := Option.map_eq_some_iff.mp ht
        obtain ⟨cr, cw, hcr, hcw, rfl, rfl⟩ := selRel_key_seg hr hb hs
        simp only [LTerm.eval, hcr, hcw, Res.ok_bind] at hv
        by_cases hcc : cr = cw
        · subst hcc
          rw [if_pos ⟨rfl, rfl⟩]
          simp only [if_true] at hv
          cases w with
          | ref _ => simp only [LMV.wordT, LTerm.eval, reduceCtorEq] at hv
          | word t' =>
            simp only [LMV.wordT] at hv
            simp only [LMV.toTheory, hv, Option.some.injEq] at hw
            subst hw
            exact (castLike_prim decl _ _ v).symm
        · rw [if_neg (fun h => hcc (by simpa only [Seg.at.injEq] using h.2.symm))]
          simp only [hcc, if_false] at hv
          exact LMem.readT_agree σ sh m i a hsh' hM' hs ht0 hv
    · simp only [LMem.readT, hij, if_false] at ht
      rw [if_neg (fun h => hij (LId.toTheory_inj h.1).symm)]
      exact LMem.readT_agree σ sh m i a hsh' hM' hs ht hv

/-- `readT_agree` with each root shaped by its allocation. -/
theorem LMem.readT_agree_shapes (σ : State) {decl : Name → Ty} {m : LMem} {i : LId}
    (hd : ∀ R, m.allocTy? i.root = some R → DeclAlong decl (.ref R) i.path)
    {a : LSel} {t : LTerm} {M : Theory.Memory} {sg : Seg} {v : Value}
    (hM : m.toTheory σ m.shapes = some M) (hs : a.toSeg σ = some sg) (ht : m.readT i a = some t)
    (hv : t.eval σ = .ok v) :
    v = castLike decl (i.toTheory m.shapes) sg
      (Theory.Memory.readIn M (i.toTheory m.shapes) sg) v :=
  LMem.readT_agree σ m.shapes m i a (fun R h => ⟨by simp only [LMem.shapes, h, Option.map_some,
      Option.getD_some], hd R h⟩) hM hs ht hv

/-- **The interpreter's read is the Theory's.**  `readT_sim` and `readT_agree`
together: what the interpreter reads at a name the closer answers for is
`readIn` of the memory's term. -/
theorem LMem.read_agree (σ : State) {decl : Name → Ty} {m : LMem}
    {μ : State} {B : MemNames.Births} {i : LId}
    (hd : ∀ R, m.allocTy? i.root = some R → DeclAlong decl (.ref R) i.path)
    {a : LSel} {t : LTerm} {M : Theory.Memory} {sg : Seg} {n : Nat} {v : Value} (hrun : m.run σ = .ok (μ, B))
    (hM : m.toTheory σ m.shapes = some M) (hs : a.toSeg σ = some sg) (ht : m.readT i a = some t)
    (hn : LId.evalR B i = .ok n) (hr : a.read σ μ n = .ok v) :
    v = castLike decl (i.toTheory m.shapes) sg
      (Theory.Memory.readIn M (i.toTheory m.shapes) sg) v := by
  have hv : t.eval σ = .ok v :=
    (LMem.readT_sim σ m i a hrun ht v).mpr (by simp only [hn, Res.ok_bind, hr])
  exact LMem.readT_agree_shapes σ hd hM hs ht hv

/-- A read that holds no identity resolves as `initIdentity` says. -/
theorem readId_fresh {M : Theory.Memory} {loc : Theory.Identity} {sg : Seg}
    (h : ∀ x, Theory.Memory.readIn M loc sg ≠ .ident x) :
    Theory.Memory.readId M loc sg = loc.extend sg := by
  unfold Theory.Memory.readId
  cases hr : Theory.Memory.readIn M loc sg with
  | ident x => exact absurd hr (h x)
  | prim _ => rfl
  | dflt => rfl

theorem seg_toSeg {σ : State} {a : LSel} {g sg : Seg} (hg : a.seg? = some g)
    (hs : a.toSeg σ = some sg) : g = sg := by
  cases a with
  | fld f =>
    obtain ⟨-, rfl⟩ := toSeg_fld hs
    simp only [LSel.seg?, Option.some.injEq] at hg
    exact hg.symm
  | idx t =>
    obtain ⟨c, hc, rfl⟩ := toSeg_idx hs
    simp only [LSel.seg?] at hg
    split at hg
    · rename_i heq
      cases heq
    · rename_i j heq
      injection heq with ht
      subst ht
      cases hg
      simp only [LTerm.eval, Res.ok_bind, Value.asInt, Except.ok.injEq] at hc
      rw [hc]
    · cases hg
  | size => simp only [LSel.seg?, reduceCtorEq] at hg

theorem extend_toTheory (sh : Nat → Theory.Shape) (i : LId) (sg : Seg) :
    (i.extend sg).toTheory sh = (i.toTheory sh).extend sg := rfl

/-- **`readI` is `readId`.**  Wherever the closer's name reader answers, its
name is the identity the Theory reads: `initIdentity` one segment below an
allocation or a copy (`readFromCopyToStorageIdentity`), the identity written
otherwise (`readOnWrite`). -/
theorem LMem.readI_agree (σ : State) (sh : Nat → Theory.Shape) :
    (m : LMem) → ∀ (i : LId) (a : LSel) {j : LId} {M : Theory.Memory} {sg : Seg},
    m.toTheory σ sh = some M → a.toSeg σ = some sg → m.readI i a = some j →
    Theory.Memory.readId M (i.toTheory sh) sg = j.toTheory sh
  | .init, _, _, _, _, _, _, _, hj => by simp only [LMem.readI, reduceCtorEq] at hj
  | .addM m k R, i, a, j, M, sg, hM, hs, hj => by
    obtain ⟨M', hM', rfl⟩ := toTheory_addM hM
    by_cases hk : i.root = k
    · subst hk
      simp only [LMem.readI, if_true] at hj
      obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hj
      rw [seg_toSeg hg hs, extend_toTheory]
      simp only [LId.toTheory, Theory.Memory.readId, Theory.Memory.readAddEqual,
        Theory.Memory.initIdentity, Theory.Identity.extend_idC]
    · simp only [LMem.readI, hk, if_false] at hj
      simp only [LId.toTheory, Theory.Memory.readId]
      rw [Theory.Memory.readAddDifferent _ _ _ _ _ _ (fun h => hk (rootT_inj h).symm)]
      exact LMem.readI_agree σ sh m i a hM' hs hj
  | .newArr m k R n, i, a, j, M, sg, hM, hs, hj => by
    obtain ⟨M', c, hM', -, rfl⟩ := toTheory_newArr hM
    by_cases hk : i.root = k
    · subst hk
      simp only [LMem.readI, if_true] at hj
      obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hj
      rw [seg_toSeg hg hs, extend_toTheory]
      apply readId_fresh
      intro x
      cases R with
      | array E =>
        simp only [LId.toTheory, newT]
        rw [Theory.Memory.readOnWrite]
        split
        · exact fun h => nomatch h
        · rw [Theory.Memory.readAddEqual]
          exact fun h => nomatch h
      | struct _ | fixed _ _ | mapping _ _ =>
        simp only [LId.toTheory, newT]
        rw [Theory.Memory.readAddEqual]
        exact fun h => nomatch h
    · simp only [LMem.readI, hk, if_false] at hj
      simp only [LId.toTheory, Theory.Memory.readId]
      rw [newT_other (fun h => hk (rootT_inj h).symm)]
      exact LMem.readI_agree σ sh m i a hM' hs hj
  | .copySt m k s q, i, a, j, M, sg, hM, hs, hj => by
    obtain ⟨M', sv, hM', -, rfl⟩ := toTheory_copySt hM
    by_cases hk : i.root = k
    · subst hk
      simp only [LMem.readI, if_true] at hj
      obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hj
      rw [seg_toSeg hg hs, extend_toTheory]
      apply readId_fresh
      intro x
      simp only [LId.toTheory, Theory.Memory.readCopySt]
      cases Theory.StValue.findSt _ _ <;> simp only [Theory.StValue.toMemValue, ne_eq,
          reduceCtorEq, not_false_eq_true]
    · simp only [LMem.readI, hk, if_false] at hj
      simp only [LId.toTheory, Theory.Memory.readId]
      rw [Theory.Memory.readCopyStOther _ _ _ _ _ _ (fun h => hk (rootT_inj h).symm)]
      exact LMem.readI_agree σ sh m i a hM' hs hj
  | .write m j0 b w, i, a, j, M, sg, hM, hs, hj => by
    obtain ⟨M', sb, mw, hM', hb, hw, rfl⟩ := toTheory_write hM
    simp only [Theory.Memory.readId]
    rw [Theory.Memory.readOnWrite]
    by_cases hij : i = j0
    · subst hij
      simp only [LMem.readI, if_true] at hj
      cases hr : selRel b a with
      | same =>
        cases w with
        | word _ => simp only [hr, reduceCtorEq] at hj
        | ref j' =>
          simp only [hr, Option.some.injEq] at hj
          subst hj
          rw [if_pos ⟨rfl, selRel_same_seg hr hb hs⟩]
          simp only [LMV.toTheory, Option.some.injEq] at hw
          subst hw
          rfl
      | apart =>
        simp only [hr] at hj
        rw [if_neg (fun h => selRel_apart_seg hr hb hs h.2)]
        exact LMem.readI_agree σ sh m i a hM' hs hj
      | key r w' => simp only [hr, reduceCtorEq] at hj
    · simp only [LMem.readI, hij, if_false] at hj
      rw [if_neg (fun h => hij (LId.toTheory_inj h.1).symm)]
      exact LMem.readI_agree σ sh m i a hM' hs hj

/-! ## An instance

`DeclAlong` asks only for the members a read passes, so it holds where the
global struct table could not be one member table: below a `Basket`, `items`
is `uint[]`, although `FixedTriple.items` is `uint[3]`. -/

/-- The length of a fresh `Basket`'s `items` is `initSize`'s. -/
example (σ : State) :
    let m : LMem := .addM .init 0 (.struct "Basket")
    let i : LId := ⟨0, [.field "items"]⟩
    Value.int 0 = castLike (fun _ => .ref (.array Ty.uint)) (i.toTheory m.shapes)
      (.field "length")
      (Theory.Memory.readIn (.addM (.pre σ.heap) (rootT m.shapes 0) (.struct "Basket"))
        (i.toTheory m.shapes) (.field "length")) (.int 0) :=
  LMem.readT_agree_shapes σ (a := .size) (t := .lit (.int 0)) (fun R h => by
      simp only [LMem.allocTy?, ↓reduceIte, Option.some.injEq] at h
      subst h
      intro U hU
      have hU' : some (Ty.ref (.array Ty.uint)) = some U := hU
      cases hU'
      exact ⟨by decide, rfl, trivial⟩) rfl rfl rfl rfl

end Decide
end Solidity
