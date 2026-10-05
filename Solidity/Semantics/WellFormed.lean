import Solidity.Semantics

/-!
# Well-formed storage, as a test

Every obligation of solkey's `TestSuite` ranges over a storage the contract
can be in, KeY's `wellFormed(heap)`: the term `wt(storage)` (`Op1.wt`,
`Update.lean`).  The term is read by the interpreter, so what it tests has
to be a function, and it sits below `Update.lean`, before any typing module.
`storageWtB` asks two things of every root:

* its shape: `SVal.canonB` and `SVal.tightB`, which decide `SVal.canon`
  (`Typing/Reachability.lean`) and `SVal.tight`
  (`Typing/Constructibility.lean`) clause for clause, by the same
  recursion, so that the proof of agreement is one case per clause;
* its words: `SVal.wordsB`, every word in its type's range and every
  mapping key in its key type's, as solc stores them (`PrimVal.fits`).

`Calculus/Problem.lean` proves that a storage passes the shape test exactly
when it is reachable.  The words are a test of their own because the AST
reaches more than solc does: a literal `.lit (i : Int)` is not range-checked
below the front end (`fitCheck`), so a program the AST admits can store a
`uint` of `-1`.  A well-formed storage is a reachable one whose words fit.
-/

namespace Solidity

namespace Semantics

/-- `v` is `defaultForTy T`, by recursion on `v`: `defaultForTy` is
well-founded, and the kernel does not reduce it. -/
def SVal.isDfltB : SVal → Ty → Bool
  | SVal.bool b, Ty.bool => !b
  | SVal.int n, Ty.uint => decide (n = 0)
  | SVal.int n, Ty.int => decide (n = 0)
  | SVal.struct fields, Ty.ref (RefTy.struct s) => isDfltFieldsB fields (structDef s)
  | SVal.array elems shadow fx, Ty.ref (RefTy.array _) => elems.isEmpty && shadow.isEmpty && !fx
  | SVal.array elems shadow fx, Ty.ref (RefTy.fixed E n) =>
      fx && shadow.isEmpty && decide (elems.length = n) && isDfltElemsB E elems
  | SVal.map entries d, Ty.ref (RefTy.mapping _ V) => entries.isEmpty && d.isDfltB V
  | _, _ => false
where
  isDfltFieldsB : List (Name × SVal) → List (Name × Ty) → Bool
    | [], [] => true
    | (n, v) :: rest, (n', T) :: rest' => decide (n = n') && v.isDfltB T && isDfltFieldsB rest rest'
    | _, _ => false
  isDfltElemsB (E : Ty) : List SVal → Bool
    | [] => true
    | v :: rest => v.isDfltB E && isDfltElemsB E rest

open SVal.isDfltB (isDfltFieldsB isDfltElemsB) in
mutual

theorem SVal.isDfltB_sound : ∀ {v : SVal} {T : Ty}, v.isDfltB T = true → v = defaultForTy T
  | SVal.prim (.bool b), Ty.bool, h => by
    cases b
    · simp only [defaultForTy]
    · simp only [SVal.isDfltB, Bool.not_true, Bool.false_eq_true] at h
  | SVal.prim (.int n), Ty.uint, h => by
    simp only [SVal.isDfltB, decide_eq_true_eq] at h
    simp only [defaultForTy, h]
  | SVal.prim (.int n), Ty.int, h => by
    simp only [SVal.isDfltB, decide_eq_true_eq] at h
    simp only [defaultForTy, h]
  | SVal.struct fields, Ty.ref (RefTy.struct s), h => by
    rw [defaultForTy, SVal.isDfltFields_sound h]
  | SVal.array elems shadow fx, Ty.ref (RefTy.array _), h => by
    simp only [SVal.isDfltB, Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true'] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rw [defaultForTy]
  | SVal.array elems shadow fx, Ty.ref (RefTy.fixed E n), h => by
    simp only [SVal.isDfltB, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, he⟩ := h
    rw [defaultForTy]
    exact congrArg (SVal.array · [] true) (SVal.isDfltElems_sound he)
  | SVal.map entries d, Ty.ref (RefTy.mapping _ V), h => by
    simp only [SVal.isDfltB, Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨rfl, hd⟩ := h
    rw [defaultForTy, SVal.isDfltB_sound hd]
  | SVal.prim (.bool _), Ty.uint, h | SVal.prim (.bool _), Ty.int, h
  | SVal.prim (.int _), Ty.bool, h | SVal.prim _, Ty.ref _, h
  | SVal.struct _, Ty.prim _, h | SVal.struct _, Ty.ref (.array _), h
  | SVal.struct _, Ty.ref (.fixed _ _), h | SVal.struct _, Ty.ref (.mapping _ _), h
  | SVal.array .., Ty.prim _, h | SVal.array .., Ty.ref (.struct _), h
  | SVal.array .., Ty.ref (.mapping _ _), h
  | SVal.map .., Ty.prim _, h | SVal.map .., Ty.ref (.struct _), h
  | SVal.map .., Ty.ref (.array _), h | SVal.map .., Ty.ref (.fixed _ _), h => by
    simp only [SVal.isDfltB, Bool.false_eq_true] at h

theorem SVal.isDfltFields_sound :
    ∀ {fs : List (Name × SVal)} {l : List (Name × Ty)}, isDfltFieldsB fs l = true →
      fs = defaultForFields l
  | [], [], _ => by rw [defaultForFields]
  | (n, v) :: rest, (n', T) :: rest', h => by
    simp only [isDfltFieldsB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hv⟩, hr⟩ := h
    rw [defaultForFields, SVal.isDfltB_sound hv, SVal.isDfltFields_sound hr]
  | [], _ :: _, h | _ :: _, [], h => by simp only [isDfltFieldsB, Bool.false_eq_true] at h

theorem SVal.isDfltElems_sound {E : Ty} :
    ∀ {es : List SVal}, isDfltElemsB E es = true → es = List.replicate es.length (defaultForTy E)
  | [], _ => rfl
  | v :: rest, h => by
    simp only [isDfltElemsB, Bool.and_eq_true] at h
    have h1 : v = defaultForTy E := SVal.isDfltB_sound h.1
    subst h1
    rw [List.length_cons, List.replicate_succ]
    exact congrArg (defaultForTy E :: ·) (SVal.isDfltElems_sound h.2)

end

open SVal.isDfltB (isDfltFieldsB isDfltElemsB) in
/-- A default is one. -/
theorem SVal.isDfltB_default (T : Ty) : (defaultForTy T).isDfltB T = true := by
  induction T using defaultForTy.induct
    (motive2 := fun l => isDfltFieldsB (defaultForFields l) l = true) with
  | case1 => simp only [defaultForTy, SVal.isDfltB, Bool.not_false]
  | case2 => simp only [defaultForTy, SVal.isDfltB, decide_true]
  | case3 => simp only [defaultForTy, SVal.isDfltB, decide_true]
  | case4 name ih => rw [defaultForTy]; exact ih
  | case5 elem => simp only [defaultForTy, SVal.isDfltB, List.isEmpty_nil, Bool.not_false,
      Bool.and_self]
  | case6 elem n ih =>
    rw [defaultForTy]
    simp only [SVal.isDfltB, List.isEmpty_nil, List.length_replicate, decide_true, Bool.and_true,
      Bool.true_and]
    induction n with
    | zero => rfl
    | succ k ihk => simp only [List.replicate_succ, isDfltElemsB, ih, ihk, Bool.and_self]
  | case7 key value ih => rw [defaultForTy]; simp only [SVal.isDfltB, List.isEmpty_nil, ih,
      Bool.and_self]
  | case8 => simp only [defaultForFields, isDfltFieldsB]
  | case9 n t rest iht ihrest =>
    simp only [defaultForFields, isDfltFieldsB, decide_true, iht, ihrest, Bool.and_self]

theorem SVal.isDfltB_iff {v : SVal} {T : Ty} : v.isDfltB T = true ↔ v = defaultForTy T :=
  ⟨SVal.isDfltB_sound, fun h => h ▸ SVal.isDfltB_default T⟩

/-- `SVal.canon` as a test. -/
def SVal.canonB : SVal → Ty → Bool
  | SVal.int _, Ty.int => true
  | SVal.int _, Ty.uint => true
  | SVal.bool _, Ty.bool => true
  | SVal.struct fields, Ty.ref (RefTy.struct s) =>
      decide (fields.map (·.1) = (structDef s).map (·.1)) && canonFieldsB s fields
  | SVal.array elems shadow fx, Ty.ref (RefTy.array E) =>
      !fx && canonElemsB E elems && canonElemsB E shadow
  | SVal.array elems shadow fx, Ty.ref (RefTy.fixed E n) =>
      fx && decide (elems.length = n) && canonElemsB E elems && canonElemsB E shadow
  | SVal.map entries dflt, Ty.ref (RefTy.mapping _ V) =>
      nodupKeysB entries && canonEntriesB V entries && dflt.isDfltB V &&
        dflt.canonB V
  | _, _ => false
where
  canonFieldsB (s : Name) : List (Name × SVal) → Bool
    | [] => true
    | (n, v) :: rest =>
        (match lookupBy n (structDef s) with
         | some T => v.canonB T
         | none => false) && canonFieldsB s rest
  canonElemsB (E : Ty) : List SVal → Bool
    | [] => true
    | v :: rest => v.canonB E && canonElemsB E rest
  canonEntriesB (V : Ty) : List (Int × SVal) → Bool
    | [] => true
    | (_, v) :: rest => v.canonB V && canonEntriesB V rest

/-- `SVal.tight` as a test. -/
def SVal.tightB : SVal → Ty → Bool
  | SVal.struct fields, Ty.ref (RefTy.struct s) => tightFieldsB s fields
  | SVal.array elems shadow _, Ty.ref (RefTy.array E) =>
      (E.defaultOkS || elems.isEmpty && shadow.isEmpty) &&
      (!E.isPrimitive || shadow.all fun w => w.isDfltB E) &&
      tightElemsB E elems && tightElemsB E shadow
  | SVal.array elems shadow _, Ty.ref (RefTy.fixed E _) => shadow.isEmpty && tightElemsB E elems
  | SVal.map entries _, Ty.ref (RefTy.mapping K V) =>
      (K.numericKey || entries.isEmpty) && tightEntriesB V entries
  | _, _ => true
where
  tightFieldsB (s : Name) : List (Name × SVal) → Bool
    | [] => true
    | (n, v) :: rest =>
        (match lookupBy n (structDef s) with
         | some T => v.tightB T
         | none => true) && tightFieldsB s rest
  tightElemsB (E : Ty) : List SVal → Bool
    | [] => true
    | v :: rest => v.tightB E && tightElemsB E rest
  tightEntriesB (V : Ty) : List (Int × SVal) → Bool
    | [] => true
    | (_, v) :: rest => v.tightB V && tightEntriesB V rest

/-- A mapping key fits its key type: a `uint` or `int` key in its range,
any `Int` at a type no program indexes with (`Ty.numericKey`). -/
def Ty.keyFitsB : Ty → Int → Bool
  | .prim p, k => !p.isNumeric || PrimVal.fits (.int k) p
  | .ref _, _ => true

/-- Every word of `v` in its type's range (`PrimVal.fits`), every key of a
mapping in its key type's (`Ty.keyFitsB`). -/
def SVal.wordsB : SVal → Ty → Bool
  | SVal.prim v, Ty.prim p => PrimVal.fits v p
  | SVal.struct fields, Ty.ref (RefTy.struct s) => wordsFieldsB fields (structDef s)
  | SVal.array elems shadow _, Ty.ref (RefTy.array E) =>
      wordsElemsB E elems && wordsElemsB E shadow
  | SVal.array elems shadow _, Ty.ref (RefTy.fixed E _) =>
      wordsElemsB E elems && wordsElemsB E shadow
  | SVal.map entries dflt, Ty.ref (RefTy.mapping K V) =>
      wordsEntriesB K V entries && dflt.wordsB V
  | _, _ => true
where
  wordsFieldsB : List (Name × SVal) → List (Name × Ty) → Bool
    | (_, v) :: rest, (_, T) :: rest' => v.wordsB T && wordsFieldsB rest rest'
    | _, _ => true
  wordsElemsB (E : Ty) : List SVal → Bool
    | [] => true
    | v :: rest => v.wordsB E && wordsElemsB E rest
  wordsEntriesB (K V : Ty) : List (Int × SVal) → Bool
    | [] => true
    | (k, v) :: rest => Ty.keyFitsB K k && v.wordsB V && wordsEntriesB K V rest

open SVal.wordsB (wordsFieldsB wordsElemsB wordsEntriesB) in
/-- A default's words fit. -/
theorem SVal.wordsB_default (T : Ty) : (defaultForTy T).wordsB T = true := by
  induction T using defaultForTy.induct
    (motive2 := fun l => wordsFieldsB (defaultForFields l) l = true) with
  | case1 => simp only [defaultForTy, SVal.wordsB]; decide
  | case2 => simp only [defaultForTy, SVal.wordsB]; decide
  | case3 => simp only [defaultForTy, SVal.wordsB]; decide
  | case4 name ih => rw [defaultForTy]; exact ih
  | case5 elem => simp only [defaultForTy, SVal.wordsB, wordsElemsB, Bool.and_self]
  | case6 elem n ih =>
    rw [defaultForTy]
    simp only [SVal.wordsB, wordsElemsB, Bool.and_true]
    induction n with
    | zero => rfl
    | succ k ihk => simp only [List.replicate_succ, wordsElemsB, ih, ihk, Bool.and_self]
  | case7 key value ih => rw [defaultForTy]; simp only [SVal.wordsB, wordsEntriesB, ih,
      Bool.and_self]
  | case8 => simp only [defaultForFields, wordsFieldsB]
  | case9 n t rest iht ihrest => simp only [defaultForFields, wordsFieldsB, iht, ihrest,
      Bool.and_self]

/-- The storage `st` holds the roots `vs`, in order, each canonical and
tight at its type: the shape `wt(storage)` tests. -/
def storageShapeB (vs : List (Name × Ty)) (st : List (Name × SVal)) : Bool :=
  decide (st.map (·.1) = vs.map (·.1)) &&
    vs.all fun rT =>
      match lookupBy rT.1 st with
      | some v => v.canonB rT.2 && v.tightB rT.2
      | none => false

/-- Every root of `st` holds words in range at its type in `vs`. -/
def storageWordsB (vs : List (Name × Ty)) (st : List (Name × SVal)) : Bool :=
  vs.all fun rT =>
    match lookupBy rT.1 st with
    | some v => v.wordsB rT.2
    | none => true

/-- What `wt(storage)` tests: the shape and the words. -/
def storageWtB (vs : List (Name × Ty)) (st : List (Name × SVal)) : Bool :=
  storageShapeB vs st && storageWordsB vs st

end Semantics

end Solidity
