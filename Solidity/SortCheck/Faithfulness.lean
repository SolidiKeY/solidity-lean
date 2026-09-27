import Solidity.Typing.Soundness
import Solidity.Calculus.RuleShapes
import Solidity.SortCheck.Annotations

/-!
# Sort-faithfulness of the taclet annotations

The table ↔ semantics edge of the conformance loop: every read-sort
annotation in `TacletAnnotations.tacletReadAnns` is *faithful* — the sort a
taclet's value read declares agrees with the value `Stmt.run` actually finds
there, in every state the invariant `RunWT` (`Typing/Soundness.lean`) holds
of.  `solkeycheck` keeps the table equal to the `.key` text; this module
keeps it true of the interpreter, so a table updated to match a buggy
taclet stops building here (`Counterexamples/PreFixSortAnnotations.lean`
is the bug `12e72a1b4b` fixed, refuted).

What a declared sort claims about the value found (`SortOkS`, `SortOkM`):

- `generic vc` — the value inhabits the read place's static type: the
  varcond resolves the schema sort to exactly that type;
- `fixed s` — the value's runtime sort lies below `s`: `StValue` and
  `MemValue` claim nothing, `int` a number, `Struct` a storage tree node,
  `Identity` a memory reference.

**Which read.**  Every read-bearing taclet is a Step-3 rule, whose statement
is all simple and reads storage or memory in exactly one place: the source
of a copy, the local a read binds, the target of `⊕=` and `++`
(`Stmt.read?`).  That is the read the row annotates (a row's other reads are
`size` cells, the `net` ledger and `delete` defaults, which the Lean model
has no cell for: `solkeycheck` checks their tokens).  The typed syntax makes
the fixed claims *static*: an `⊕=` target is at a numeric type by its
constructor, a copy source at a reference type.  So each row is faithful
once its constructors read at a type of the right class (`ReadClass`), and
`Read.sortOk` does the rest from the typing of the evaluators.

**Which statements.**  A row names a KeY taclet; `RuleShapes.tacletOrigins`
names the `Taclet` constructors that transcribe it (`ctorsOf`).  For each of
the 34 read-bearing constructors, `faithful_<ctor>` quantifies over the
constructor's schema variables and takes the statement from the
constructor's own type (`stmtOf`), so the statement is the rule's `\find`,
not a restatement of it.  `rows_covered` checks that every row with a value
read is claimed by constructors in `faithfulCtors`, each of which carries its
theorem.
-/

namespace Solidity
namespace SortFaithfulness

open Semantics
open TacletAnnotations

variable {C : Contract}

/-! ## The value read of a statement -/

/-- A read of a storage path or a memory path, at its static type. -/
inductive Read (C : Contract) where
  | storage (T : Ty) (p : SPath C T)
  | memory (T : Ty) (p : MPath C T)

/-- `alice.age` is read from storage, `m.age` from memory. -/
def Read.domain : Read C → ReadDomain
  | .storage .. => .storage
  | .memory .. => .memory

/-- `alice.age` is read at `uint`. -/
def Read.ty : Read C → Ty
  | .storage T _ | .memory T _ => T

/-- The read's locals are used as declared. -/
def Read.wt (Γ : Ctx) : Read C → Bool
  | .storage _ p => p.wt Γ
  | .memory _ p => p.wt Γ

/-- The place `x ⊕= e` and `x++` read: `alice.age` in storage, `m.age` in
memory; a stack local is not read from a state component. -/
def OpLoc.read? : {p : PrimTy} → OpLoc C p → Option (Read C)
  | _, .local _ => none
  | p, .root r h => some (.storage (.prim p) (.loc (.root r h)))
  | p, .field b f h => some (.storage (.prim p) (.loc (.field b f h)))
  | p, .index it b i => some (.storage (.prim p) (.loc (.index it b (.simple i))))
  | p, .mfield b f h => some (.memory (.prim p) (.loc (.field b f h)))
  | p, .mindex b i => some (.memory (.prim p) (.loc (.index b (.simple i))))

/-- The value read a statement performs: `x = alice.age;` reads `alice.age`,
`alice = bob;` reads `bob`, `m = alice;` reads `alice`, `alice.age += 1;`
reads `alice.age`. -/
def Stmt.read? : Stmt C → Option (Read C)
  | @Stmt.assignLocal _ p _ (.read l) => some (.storage (.prim p) (.loc l))
  | @Stmt.assignLocal _ p _ (.readMem l) => some (.memory (.prim p) (.loc l))
  | @Stmt.assign _ _ _ (@Src.copy _ R sp _) => some (.storage (.ref R) sp)
  | @Stmt.push _ _ _ (some (@Src.copy _ R sp _)) _ => some (.storage (.ref R) sp)
  | @Stmt.rebindMem _ R _ (.copy sp _) => some (.storage (.ref R) sp)
  | @Stmt.rebindMem _ R _ (.alias mp) => some (.memory (.ref R) mp)
  | @Stmt.assignFromMem _ R _ mp => some (.memory (.ref R) mp)
  | .opAssign _ _ _ l _ => OpLoc.read? l
  | .incDec _ _ l => OpLoc.read? l
  | .assignIncDec _ _ _ l _ => OpLoc.read? l
  | _ => none

/-- The place `alice.age += 1;` reads is checked when the target is. -/
theorem OpLoc.read?_wt {Γ : Ctx} : ∀ {p : PrimTy} {l : OpLoc C p} {R : Read C},
    l.wt Γ = true → OpLoc.read? l = some R → R.wt Γ = true
  | _, .local _, _, _, h => nomatch h
  | _, .root .., _, _, h => by cases h; rfl
  | _, .field .., _, hw, h => by cases h; exact hw
  | _, .index .., _, hw, h => by cases h; exact hw
  | _, .mfield .., _, hw, h => by cases h; exact hw
  | _, .mindex .., _, hw, h => by cases h; exact hw

/-- A checked statement's read is checked: in `x = p.age;` the alias `p` is
a `Person storage` in `Γ`. -/
theorem Stmt.read?_wt {Γ Γ' : Ctx} {s : Stmt C} {R : Read C} (hs : s.wt Γ = some Γ')
    (h : Stmt.read? s = some R) : R.wt Γ = true := by
  cases s with
  | assignLocal x r =>
    obtain ⟨hc, -⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    cases r <;> simp only [Stmt.read?, reduceCtorEq] at h <;> cases h <;> exact hc.2
  | assign l r =>
    obtain ⟨hc, -⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    cases r <;> simp only [Stmt.read?, reduceCtorEq] at h
    cases h; exact hc.2
  | push b v _ =>
    obtain ⟨hc, -⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    rcases v with _ | ⟨_ | _⟩ <;> simp only [Stmt.read?, reduceCtorEq] at h
    cases h; simpa [Src.wt] using hc.2
  | rebindMem x r =>
    obtain ⟨hc, -⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    cases r <;> simp only [Stmt.read?] at h <;> cases h <;> exact hc.2
  | assignFromMem l p =>
    obtain ⟨hc, -⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    cases h; exact hc.2
  | opAssign op _ _ l r =>
    obtain ⟨hc, -⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    exact OpLoc.read?_wt hc.1 h
  | incDec _ _ l =>
    obtain ⟨hc, -⟩ := wt_if hs
    exact OpLoc.read?_wt hc h
  | assignIncDec x _ _ l _ =>
    obtain ⟨hc, -⟩ := wt_if hs
    simp only [Bool.and_eq_true] at hc
    exact OpLoc.read?_wt hc.2 h
  | _ => simp [Stmt.read?] at h

/-! ## What a declared sort claims -/

/-- What `find<[s]>`/`select<[s]>` claims of the storage value found, the
read place being of type `T`. -/
def SortOkS : ReadSort → Ty → SVal → Bool
  | .generic _, T, v => v.hasTy T
  | .fixed s, _, v => v.keySort.le s

/-- What `read<[s]>` claims of the memory slot found. -/
def SortOkM (H : HeapTy) : ReadSort → Ty → MVal → Bool
  | .generic _, T, mv => MVal.hasTyH H mv T
  | .fixed s, _, mv => mv.keySort.le s

/-- The declared sort `rs` holds of whatever the read finds in `σ`:
resolving the storage path and finding the value, or reading the memory
slot. -/
def Read.SortOk (σ : State) (H : HeapTy) (rs : ReadSort) : Read C → Prop
  | .storage T p => ∀ r segs v, p.resolve σ = .ok (r, segs) →
      σ.findStorage r segs = .ok v → SortOkS rs T v = true
  | .memory T p => ∀ mv, p.mval σ = .ok mv → SortOkM H rs T mv = true

/-- What a constructor's schema fixes about its read's static type. -/
inductive ReadClass where
  /-- Nothing: `v = sp.fld` reads a member of whatever type it has. -/
  | any
  /-- A number: the target of `⊕=` and `++`. -/
  | numeric
  /-- A reference: a copy source, a memory object. -/
  | reference
  deriving DecidableEq, Repr

/-- `uint` is numeric, `Person` a reference. -/
def ReadClass.fits : ReadClass → Ty → Bool
  | .any, _ => true
  | .numeric, T => isNumericTy T
  | .reference, T => T.isReference

/-- Which declared sorts a read of class `cls` in `dom` supports: a
varcond-generic sort always (it resolves to the static type), `StValue` and
`MemValue` always (they claim nothing), `int` on a number, `Struct` on a
storage reference, `Identity` on a memory one. -/
def ReadClass.supports (cls : ReadClass) : ReadDomain → ReadSort → Bool
  | _, .generic _ => true
  | .storage, .fixed .stValue => true
  | .memory, .fixed .memValue => true
  | _, .fixed .int => cls == .numeric
  | .storage, .fixed .struct => cls == .reference
  | .memory, .fixed .identity => cls == .reference
  | _, _ => false

/-- A memory slot typed `uint` holds a number: `m.age` in `m.age += 1;`. -/
theorem MVal.int_of_hasTyH_numeric {H : HeapTy} {mv : MVal} {T : Ty}
    (hT : isNumericTy T = true) (h : MVal.hasTyH H mv T = true) : ∃ n, mv = .int n := by
  cases T with
  | prim p =>
    cases mv with
    | prim pv => cases p <;> cases pv <;> simp_all [MVal.hasTyH, isNumericTy, PrimTy.isNumeric]
    | ref _ => cases p <;> simp [MVal.hasTyH] at h
  | ref _ => simp [isNumericTy] at hT

/-- A memory slot typed at a reference holds an identity: `m.account`. -/
theorem MVal.ref_of_hasTyH_ref {H : HeapTy} {mv : MVal} {T : Ty}
    (hT : T.isReference = true) (h : MVal.hasTyH H mv T = true) : ∃ id, mv = .ref id := by
  cases T with
  | prim p => simp [Ty.isReference, Ty.isPrimitive] at hT
  | ref _ =>
    cases mv with
    | prim pv => cases pv <;> simp [MVal.hasTyH] at h
    | ref id => exact ⟨id, rfl⟩

/-- **The semantic core.**  A read whose locals are used as declared, of a
class the declared sort is supported by, finds a value the sort claims, in
every `RunWT` state: `x = total;` finds a number where `total : uint`,
`alice.age += 1` finds an `int`, `m = alice;` finds a `Struct` node. -/
theorem Read.sortOk {Γ : Ctx} {H : HeapTy} {σ : State} (hwt : RunWT C Γ H σ) {R : Read C}
    (hw : R.wt Γ = true) {cls : ReadClass} (hfit : cls.fits R.ty = true) {rs : ReadSort}
    (hsup : cls.supports R.domain rs = true) : R.SortOk σ H rs := by
  cases R with
  | storage T p =>
    intro r segs v hr hv
    have hty := findStorage_hasTy hwt.storage (SPath.resolve_wt hwt p hw hr) hv
    cases rs with
    | generic _ => exact hty
    | fixed s =>
      show v.keySort.le s = true
      cases s <;> simp only [ReadClass.supports, Read.domain, beq_iff_eq] at hsup <;>
        (try exact Bool.noConfusion hsup) <;> subst_vars
      · exact SVal.keySort_le_stValue v
      · obtain ⟨n, rfl⟩ := hasTy_numeric hfit hty
        rfl
      · rw [(SVal.isRefVal_iff_keySort_struct v).mp (hasTy_isRefVal hfit hty)]
        exact KeySort.le_refl _
  | memory T p =>
    intro mv hmv
    have hty := MPath.mval_wt hwt p hw hmv
    cases rs with
    | generic _ => exact hty
    | fixed s =>
      show mv.keySort.le s = true
      cases s <;> simp only [ReadClass.supports, Read.domain, beq_iff_eq] at hsup <;>
        (try exact Bool.noConfusion hsup) <;> subst_vars
      · exact MVal.keySort_le_memValue mv
      · obtain ⟨n, rfl⟩ := MVal.int_of_hasTyH_numeric hfit hty
        rfl
      · obtain ⟨id, rfl⟩ := MVal.ref_of_hasTyH_ref hfit hty
        rfl

/-- The claims hold after any checked run: from a well-typed state, run a
block whose locals check, and the next statement's read finds what its
sort declares.  `Person storage p = alice; p.age = 10;` then
`x = alice.age;` still reads a number. -/
theorem Read.sortOk_after_run {Γ Γ₁ Γ₂ : Ctx} {H : HeapTy} {σ σ₁ : State} {P : Prog C}
    {s : Stmt C} {R : Read C} {cls : ReadClass} {rs : ReadSort} (hwt : RunWT C Γ H σ)
    (hP : Prog.wt Γ P = some Γ₁) (hrun : Prog.run σ P = .ok σ₁) (hs : s.wt Γ₁ = some Γ₂)
    (hR : Stmt.read? s = some R) (hfit : cls.fits R.ty = true)
    (hsup : cls.supports R.domain rs = true) : ∃ H', R.SortOk σ₁ H' rs :=
  let ⟨H', _, hwt'⟩ := Prog.run_wt P hwt hP hrun
  ⟨H', Read.sortOk hwt' (Stmt.read?_wt hs hR) hfit hsup⟩

/-! ## Rows, constructors, statements -/

/-- A constructor's type, `Taclet C k m s p` under its side conditions
(`Rules.lean`): the statement `s` it is about. -/
class TacletAbout (α : Prop) (C : outParam Contract) (s : outParam (Stmt C)) : Prop where

instance {k : Nat} {m : Modality} {s : Stmt C} {p : Premise C} :
    TacletAbout (Taclet C k m s p) C s := ⟨⟩

instance {P α : Prop} {s : Stmt C} [TacletAbout α C s] : TacletAbout (P → α) C s := ⟨⟩

/-- The statement a taclet constructor is about: the rule's `\find`, read off
its type (past its side conditions, which a faithfulness statement does not
need: it holds of the statement whichever rule fires). -/
def stmtOf {α : Prop} {s : Stmt C} [TacletAbout α C s] (_ : α) : Stmt C := s

/-- The KeY taclets constructor `n` transcribes (`RuleShapes.tacletOrigins`),
by name. -/
def keyNamesOf (n : Lean.Name) : List String :=
  match RuleShapes.tacletOrigins.lookup n with
  | some o => o.taclets.map KeyTaclet.name
  | none => []

/-- The constructors that transcribe the KeY taclet named `key`. -/
def ctorsOf (key : String) : List Lean.Name :=
  (RuleShapes.tacletOrigins.filter fun (_, o) => o.taclets.any (·.name == key)).map (·.1)

/-- The rows of the taclets constructor `n` transcribes. -/
def rowsOf (n : Lean.Name) : List TacletReadAnn :=
  let names := keyNamesOf n
  tacletReadAnns.filter fun row => names.contains row.keyName

/-- A row's value reads: the ones a Lean statement has a place for. -/
def valueReads (row : TacletReadAnn) : List TacletRead :=
  row.reads.filter (·.site == .value)

/-- Every value read of every row constructor `n` transcribes is in `dom`
and supported by a read of class `cls`. -/
def rowsSupported (n : Lean.Name) (dom : ReadDomain) (cls : ReadClass) : Bool :=
  (rowsOf n).all fun row => (valueReads row).all fun r => r.domain == dom && cls.supports dom r.sort

/-- A row is faithful at a statement: each value read it declares is the
statement's read, and in every `RunWT` state where the statement's locals
check, the declared sort holds of what the read finds. -/
def RowFaithful (row : TacletReadAnn) (s : Stmt C) : Prop :=
  ∀ r ∈ valueReads row, ∃ R, Stmt.read? s = some R ∧ R.domain = r.domain ∧
    ∀ (Γ Γ' : Ctx) (H : HeapTy) (σ : State), RunWT C Γ H σ → s.wt Γ = some Γ' →
      R.SortOk σ H r.sort

/-- Every row constructor `n` transcribes is faithful at `s`. -/
def CtorFaithful (n : Lean.Name) (s : Stmt C) : Prop :=
  ∀ row ∈ rowsOf n, RowFaithful row s

/-- A row is faithful at a statement whose read is of a class the row's
declared sorts are all supported by: `find<[int]>` at `total += 1;`. -/
theorem rowFaithful_of {row : TacletReadAnn} {s : Stmt C} {R : Read C} {dom : ReadDomain}
    {cls : ReadClass} (hR : Stmt.read? s = some R) (hdom : R.domain = dom)
    (hfit : cls.fits R.ty = true)
    (hrow : (valueReads row).all (fun r => r.domain == dom && cls.supports dom r.sort) = true) :
    RowFaithful row s := by
  intro r hr
  have h := List.all_eq_true.mp hrow r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨R, hR, hdom.trans h.1.symm, fun Γ Γ' H σ hwt hs => ?_⟩
  exact Read.sortOk hwt (Stmt.read?_wt hs hR) hfit (hdom ▸ h.2)

/-- A constructor is faithful at a statement whose read is of a class every
row's declared sorts are supported by. -/
theorem ctorFaithful_of {n : Lean.Name} {s : Stmt C} {R : Read C} {dom : ReadDomain}
    {cls : ReadClass} (hR : Stmt.read? s = some R) (hdom : R.domain = dom)
    (hfit : cls.fits R.ty = true) (hrows : rowsSupported n dom cls = true) :
    CtorFaithful n s := fun row hrow =>
  rowFaithful_of hR hdom hfit (List.all_eq_true.mp hrows row hrow)

/-! ## The read-bearing constructors

One theorem per constructor with a value read, in `Rules.lean`'s order of
the rows: the statement is the constructor's own, its schema variables
universally quantified, so each theorem covers every statement the rule
fires on.  The class is what the constructor's schema fixes: an `⊕=` target
is `numeric` by `hp`, a copy source a `reference` by its index. -/

/-- `alice = bob;` reads `bob`, a `Person`: the copy source is a reference, and
the row's `find<[StValue]>` claims no more than a storage value. -/
theorem faithful_storageRootWriteCopySource {C : Contract} {k : Nat} {m : Modality} {gsp : Name}
    {x : RefTy} {hgsp : Eq (Contract.rootType C gsp) (some (Ty.ref x))} {sp : SPath C (Ty.ref x)}
    {hm : Eq (Ty.mapFree (Ty.ref x)) true} :
    CtorFaithful ``Taclet.storageRootWriteCopySource
      (stmtOf (@Taclet.storageRootWriteCopySource C k m gsp x hgsp sp hm)) :=
  ctorFaithful_of (dom := .storage) (cls := .reference) rfl rfl rfl (by decide +kernel)

/-- `x = total;` reads a number, `total`'s declared `uint`:
`select<[alphaPrim]>` with `\hasSort` resolves to it. -/
theorem faithful_storageRootReadSelect {C : Contract} {k : Nat} {m : Modality} {v : Var}
    {gsp : Name} {x : PrimTy} {hgsp : Eq (Contract.rootType C gsp) (some (Ty.prim x))} :
    CtorFaithful ``Taclet.storageRootReadSelect
      (stmtOf (@Taclet.storageRootReadSelect C k m v gsp x hgsp)) :=
  ctorFaithful_of (dom := .storage) (cls := .any) rfl rfl rfl (by decide +kernel)

/-- `alice.account = a;` (`a : Account storage`) reads `a`'s `Account` node
under `find<[StValue]>`. -/
theorem faithful_storageFieldWriteCopySource {C : Contract} {k : Nat} {m : Modality} {x : Name}
    {sp : SPath C (Ty.struct x)} {fld : Name} {x_1 : RefTy}
    {hfld : Eq (Contract.fieldType C x fld) (some (Ty.ref x_1))} {sp2 : SPath C (Ty.ref x_1)}
    {hm : Eq (Ty.mapFree (Ty.ref x_1)) true} :
    CtorFaithful ``Taclet.storageFieldWriteCopySource
      (stmtOf (@Taclet.storageFieldWriteCopySource C k m x sp fld x_1 hfld sp2 hm)) :=
  ctorFaithful_of (dom := .storage) (cls := .reference) rfl rfl rfl (by decide +kernel)

/-- `x = alice.age;` reads a number, `age`'s declared `uint` (`\hasFieldSort`). -/
theorem faithful_storageFieldReadFind {C : Contract} {k : Nat} {m : Modality} {v : Var} {x : Name}
    {sp : SPath C (Ty.struct x)} {fld : Name} {x_1 : PrimTy}
    {hfld : Eq (Contract.fieldType C x fld) (some (Ty.prim x_1))} :
    CtorFaithful ``Taclet.storageFieldReadFind
      (stmtOf (@Taclet.storageFieldReadFind C k m v x sp fld x_1 hfld)) :=
  ctorFaithful_of (dom := .storage) (cls := .any) rfl rfl rfl (by decide +kernel)

/-- `tok = a.token;` reads the `Token` member under `find<[StValue]>`. -/
theorem faithful_storageFieldReadStoreRoot {C : Contract} {k : Nat} {m : Modality} {gsp : Name}
    {x : RefTy} {hgsp : Eq (Contract.rootType C gsp) (some (Ty.ref x))} {x_1 : Name}
    {sp : SPath C (Ty.struct x_1)} {fr : Name}
    {hfr : Eq (Contract.fieldType C x_1 fr) (some (Ty.ref x))}
    {hm : Eq (Ty.mapFree (Ty.ref x)) true} :
    CtorFaithful ``Taclet.storageFieldReadStoreRoot
      (stmtOf (@Taclet.storageFieldReadStoreRoot C k m gsp x hgsp x_1 sp fr hfr hm)) :=
  ctorFaithful_of (dom := .storage) (cls := .reference) rfl rfl rfl (by decide +kernel)

/-- `x = balances[i];` reads a number, the mapping's value type (`\hasElementSort`). -/
theorem faithful_storageIndexReadMappingFind {C : Contract} {k : Nat} {m : Modality} {v : Var}
    {x x_1 : PrimTy} {map : SPath C (Ty.ref (RefTy.mapping (Ty.prim x) (Ty.prim x_1)))}
    {ie : Simple C x} :
    CtorFaithful ``Taclet.storageIndexReadMappingFind
      (stmtOf (@Taclet.storageIndexReadMappingFind C k m v x x_1 map ie)) :=
  ctorFaithful_of (dom := .storage) (cls := .any) rfl rfl rfl (by decide +kernel)

/-- `alice = folks[i];` reads the `Person` entry under `find<[StValue]>`. -/
theorem faithful_storageIndexReadMappingStoreRoot {C : Contract} {k : Nat} {m : Modality}
    {gsp : Name} {x : RefTy} {hgsp : Eq (Contract.rootType C gsp) (some (Ty.ref x))}
    {x_1 : PrimTy} {map : SPath C (Ty.ref (RefTy.mapping (Ty.prim x_1) (Ty.ref x)))}
    {ie : Simple C x_1} {hm : Eq (Ty.mapFree (Ty.ref x)) true} :
    CtorFaithful ``Taclet.storageIndexReadMappingStoreRoot
      (stmtOf (@Taclet.storageIndexReadMappingStoreRoot C k m gsp x hgsp x_1 map ie hm)) :=
  ctorFaithful_of (dom := .storage) (cls := .reference) rfl rfl rfl (by decide +kernel)

/-- `folks[i] = p;` reads `p`'s `Person` node under `find<[StValue]>`. -/
theorem faithful_storageIndexWriteMappingCopySource {C : Contract} {k : Nat} {m : Modality}
    {x : PrimTy} {x_1 : RefTy} {map : SPath C (Ty.ref (RefTy.mapping (Ty.prim x) (Ty.ref x_1)))}
    {ie : Simple C x} {sp2 : SPath C (Ty.ref x_1)} {hm : Eq (Ty.mapFree (Ty.ref x_1)) true} :
    CtorFaithful ``Taclet.storageIndexWriteMappingCopySource
      (stmtOf (@Taclet.storageIndexWriteMappingCopySource C k m x x_1 map ie sp2 hm)) :=
  ctorFaithful_of (dom := .storage) (cls := .reference) rfl rfl rfl (by decide +kernel)

/-- `x = values[i];` reads a number, the array's element type (`\hasElementSort`). -/
theorem faithful_storageIndexReadArrayFind {C : Contract} {k : Nat} {m : Modality} {v : Var}
    {x : PrimTy} {arr : SPath C (Ty.ref (RefTy.array (Ty.prim x)))} {ie : Simple C PrimTy.uint} :
    CtorFaithful ``Taclet.storageIndexReadArrayFind
      (stmtOf (@Taclet.storageIndexReadArrayFind C k m v x arr ie)) :=
  ctorFaithful_of (dom := .storage) (cls := .any) rfl rfl rfl (by decide +kernel)

/-- `alice = persons[i];` reads the `Person` element under `find<[StValue]>`. -/
theorem faithful_storageIndexReadArrayStoreRoot {C : Contract} {k : Nat} {m : Modality}
    {gsp : Name} {x : RefTy} {hgsp : Eq (Contract.rootType C gsp) (some (Ty.ref x))}
    {arr : SPath C (Ty.ref (RefTy.array (Ty.ref x)))} {ie : Simple C PrimTy.uint}
    {hm : Eq (Ty.mapFree (Ty.ref x)) true} :
    CtorFaithful ``Taclet.storageIndexReadArrayStoreRoot
      (stmtOf (@Taclet.storageIndexReadArrayStoreRoot C k m gsp x hgsp arr ie hm)) :=
  ctorFaithful_of (dom := .storage) (cls := .reference) rfl rfl rfl (by decide +kernel)

/-- `persons[i] = p;` reads `p`'s `Person` node under `find<[StValue]>`. -/
theorem faithful_storageIndexWriteArrayCopySource {C : Contract} {k : Nat} {m : Modality}
    {x : RefTy} {arr : SPath C (Ty.ref (RefTy.array (Ty.ref x)))} {ie : Simple C PrimTy.uint}
    {sp2 : SPath C (Ty.ref x)} {hm : Eq (Ty.mapFree (Ty.ref x)) true} :
    CtorFaithful ``Taclet.storageIndexWriteArrayCopySource
      (stmtOf (@Taclet.storageIndexWriteArrayCopySource C k m x arr ie sp2 hm)) :=
  ctorFaithful_of (dom := .storage) (cls := .reference) rfl rfl rfl (by decide +kernel)

/-- `persons.push(p);` reads `p`'s `Person` node under `find<[StValue]>`. -/
theorem faithful_storagePushValueCopySource {C : Contract} {k : Nat} {m : Modality} {x : RefTy}
    {sp : SPath C (Ty.array (Ty.ref x))} {sp2 : SPath C (Ty.ref x)}
    {hm : Eq (Ty.mapFree (Ty.ref x)) true} :
    CtorFaithful ``Taclet.storagePushValueCopySource
      (stmtOf (@Taclet.storagePushValueCopySource C k m x sp sp2 hm)) :=
  ctorFaithful_of (dom := .storage) (cls := .reference) rfl rfl rfl (by decide +kernel)

/-- `m = alice;` reads `alice` under `find<[Struct]>`: a copy source is a
reference, so what it finds is a tree node. -/
theorem faithful_memoryStorageCopy {C : Contract} {k : Nat} {m : Modality} {mv : Var} {x : RefTy}
    {sp : SPath C (Ty.ref x)} {hm : Eq (Ty.mapFree (Ty.ref x)) true} :
    CtorFaithful ``Taclet.memoryStorageCopy (stmtOf (@Taclet.memoryStorageCopy C k m mv x sp hm)) :=
  ctorFaithful_of (dom := .storage) (cls := .reference) rfl rfl rfl (by decide +kernel)

/-- `total += x;` reads `total` under `find<[int]>`: the target of `⊕=` is
numeric, so what it finds is an `int`. -/
theorem faithful_storageRootOpAssign {C : Contract} {k : Nat} {m : Modality} {p : PrimTy}
    {op : BinOp} {hop : Eq (BinOp.hasCompoundAssign op) true} {hp : Eq (PrimTy.isNumeric p) true}
    {gsp : Name} {hgsp : Eq (Contract.rootType C gsp) (some (Ty.prim p))} {se : Simple C p} :
    CtorFaithful ``Taclet.storageRootOpAssign
      (stmtOf (@Taclet.storageRootOpAssign C k m p op hop hp gsp hgsp se)) :=
  ctorFaithful_of (dom := .storage) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- `alice.age += x;` reads `alice.age` under `find<[int]>`. -/
theorem faithful_storageFieldOpAssign {C : Contract} {k : Nat} {m : Modality} {p : PrimTy}
    {op : BinOp} {hop : Eq (BinOp.hasCompoundAssign op) true} {hp : Eq (PrimTy.isNumeric p) true}
    {x : Name} {sp : SPath C (Ty.struct x)} {fld : Name}
    {hfld : Eq (Contract.fieldType C x fld) (some (Ty.prim p))} {se : Simple C p} :
    CtorFaithful ``Taclet.storageFieldOpAssign
      (stmtOf (@Taclet.storageFieldOpAssign C k m p op hop hp x sp fld hfld se)) :=
  ctorFaithful_of (dom := .storage) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- `balances[i] += x;` reads the entry under `find<[int]>`. -/
theorem faithful_storageIndexMappingOpAssign {C : Contract} {k : Nat} {m : Modality} {p : PrimTy}
    {op : BinOp} {hop : Eq (BinOp.hasCompoundAssign op) true} {hp : Eq (PrimTy.isNumeric p) true}
    {x : PrimTy} {map : SPath C (Ty.ref (RefTy.mapping (Ty.prim x) (Ty.prim p)))}
    {ie : Simple C x} {se : Simple C p} :
    CtorFaithful ``Taclet.storageIndexMappingOpAssign
      (stmtOf (@Taclet.storageIndexMappingOpAssign C k m p op hop hp x map ie se)) :=
  ctorFaithful_of (dom := .storage) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- `values[i] += x;` reads the element under `find<[int]>`. -/
theorem faithful_storageIndexArrayOpAssign {C : Contract} {k : Nat} {m : Modality} {p : PrimTy}
    {op : BinOp} {hop : Eq (BinOp.hasCompoundAssign op) true} {hp : Eq (PrimTy.isNumeric p) true}
    {arr : SPath C (Ty.ref (RefTy.array (Ty.prim p)))} {ie : Simple C PrimTy.uint}
    {se : Simple C p} :
    CtorFaithful ``Taclet.storageIndexArrayOpAssign
      (stmtOf (@Taclet.storageIndexArrayOpAssign C k m p op hop hp arr ie se)) :=
  ctorFaithful_of (dom := .storage) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- `total++;` reads `total` under `find<[int]>`. -/
theorem faithful_storageRootIncrement {C : Contract} {k : Nat} {m : Modality} {p : PrimTy}
    {op : IncDec} {hp : Eq (PrimTy.isNumeric p) true} {gsp : Name}
    {hgsp : Eq (Contract.rootType C gsp) (some (Ty.prim p))} :
    CtorFaithful ``Taclet.storageRootIncrement
      (stmtOf (@Taclet.storageRootIncrement C k m p op hp gsp hgsp)) :=
  ctorFaithful_of (dom := .storage) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- `alice.age++;` reads `alice.age` under `find<[int]>`. -/
theorem faithful_storageFieldIncrement {C : Contract} {k : Nat} {m : Modality} {p : PrimTy}
    {op : IncDec} {hp : Eq (PrimTy.isNumeric p) true} {x : Name} {sp : SPath C (Ty.struct x)}
    {fld : Name} {hfld : Eq (Contract.fieldType C x fld) (some (Ty.prim p))} :
    CtorFaithful ``Taclet.storageFieldIncrement
      (stmtOf (@Taclet.storageFieldIncrement C k m p op hp x sp fld hfld)) :=
  ctorFaithful_of (dom := .storage) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- `balances[i]++;` and `values[i]--;` read the entry under `find<[int]>`. -/
theorem faithful_storageIndexIncrement {C : Contract} {k : Nat} {m : Modality} {p : PrimTy}
    {op : IncDec} {hp : Eq (PrimTy.isNumeric p) true} {x : RefTy} {x_1 : PrimTy}
    {it : IndexTy x x_1 (Ty.prim p)} {sp : SPath C (Ty.ref x)} {ie : Simple C x_1} :
    CtorFaithful ``Taclet.storageIndexIncrement
      (stmtOf (@Taclet.storageIndexIncrement C k m p op hp x x_1 it sp ie)) :=
  ctorFaithful_of (dom := .storage) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- `x = total++;` reads `total` under `find<[int]>`, twice. -/
theorem faithful_storageRootIncrementAssignment {C : Contract} {k : Nat} {m : Modality}
    {p : PrimTy} {v : Var} {op : IncDec} {hp : Eq (PrimTy.isNumeric p) true} {gsp : Name}
    {hgsp : Eq (Contract.rootType C gsp) (some (Ty.prim p))}
    {hs : Eq (OpLoc.recvSimple (OpLoc.root gsp hgsp)) true} :
    CtorFaithful ``Taclet.storageRootIncrementAssignment
      (stmtOf (@Taclet.storageRootIncrementAssignment C k m p v op hp gsp hgsp hs)) :=
  ctorFaithful_of (dom := .storage) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- `x = alice.age++;` reads `alice.age` under `find<[int]>`. -/
theorem faithful_storageFieldIncrementAssignment {C : Contract} {k : Nat} {m : Modality}
    {p : PrimTy} {v : Var} {op : IncDec} {hp : Eq (PrimTy.isNumeric p) true} {x : Name}
    {sp : SPath C (Ty.struct x)} {fld : Name}
    {hfld : Eq (Contract.fieldType C x fld) (some (Ty.prim p))}
    {hs : Eq (OpLoc.recvSimple (OpLoc.field sp fld hfld)) true} :
    CtorFaithful ``Taclet.storageFieldIncrementAssignment
      (stmtOf (@Taclet.storageFieldIncrementAssignment C k m p v op hp x sp fld hfld hs)) :=
  ctorFaithful_of (dom := .storage) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- `x = values[i]++;` reads the element under `find<[int]>`. -/
theorem faithful_storageIndexIncrementAssignment {C : Contract} {k : Nat} {m : Modality}
    {p : PrimTy} {v : Var} {op : IncDec} {hp : Eq (PrimTy.isNumeric p) true} {x : RefTy}
    {x_1 : PrimTy} {it : IndexTy x x_1 (Ty.prim p)} {sp : SPath C (Ty.ref x)} {ie : Simple C x_1}
    {hs : Eq (OpLoc.recvSimple (OpLoc.index it sp ie)) true} :
    CtorFaithful ``Taclet.storageIndexIncrementAssignment
      (stmtOf (@Taclet.storageIndexIncrementAssignment C k m p v op hp x x_1 it sp ie hs)) :=
  ctorFaithful_of (dom := .storage) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- `alice.account = m;` (`m : Account memory`) reads `m` under
`read<[Identity]>`: a memory reference. -/
theorem faithful_memoryToStorageFieldCopyRoot {C : Contract} {k : Nat} {m : Modality} {x : Name}
    {sp : SPath C (Ty.struct x)} {fld : Name} {x_1 : RefTy}
    {hfld : Eq (Contract.fieldType C x fld) (some (Ty.ref x_1))} {mpath : MPath C (Ty.ref x_1)} :
    CtorFaithful ``Taclet.memoryToStorageFieldCopyRoot
      (stmtOf (@Taclet.memoryToStorageFieldCopyRoot C k m x sp fld x_1 hfld mpath)) :=
  ctorFaithful_of (dom := .memory) (cls := .reference) rfl rfl rfl (by decide +kernel)

/-- `x = m.age;` reads a number, `age`'s declared `uint` (`\hasMemoryFieldSort`). -/
theorem faithful_memoryFieldReadHeap {C : Contract} {k : Nat} {m : Modality} {v mv : Var}
    {fld x : Name} {x_1 : PrimTy} {hfld : Eq (Contract.fieldType C x fld) (some (Ty.prim x_1))} :
    CtorFaithful ``Taclet.memoryFieldReadHeap
      (stmtOf (@Taclet.memoryFieldReadHeap C k m v mv fld x x_1 hfld)) :=
  ctorFaithful_of (dom := .memory) (cls := .any) rfl rfl rfl (by decide +kernel)

/-- `n = m.account;` reads a reference the store typing claims at `Account`
(`\hasMemoryFieldSort`). -/
theorem faithful_memoryFieldReadAliasRoot {C : Contract} {k : Nat} {m : Modality} {mv₁ mv₂ : Var}
    {fr x : Name} {x_1 : RefTy} {hfr : Eq (Contract.fieldType C x fr) (some (Ty.ref x_1))} :
    CtorFaithful ``Taclet.memoryFieldReadAliasRoot
      (stmtOf (@Taclet.memoryFieldReadAliasRoot C k m mv₁ mv₂ fr x x_1 hfr)) :=
  ctorFaithful_of (dom := .memory) (cls := .any) rfl rfl rfl (by decide +kernel)

/-- `x = ns[i];` (`ns : uint[] memory`) reads a number (`\hasMemoryElementSort`). -/
theorem faithful_memoryIndexReadHeap {C : Contract} {k : Nat} {x : PrimTy} {m : Modality}
    {v mv : Var} {ie : Simple C PrimTy.uint} :
    CtorFaithful ``Taclet.memoryIndexReadHeap
      (stmtOf (@Taclet.memoryIndexReadHeap C k x m v mv ie)) :=
  ctorFaithful_of (dom := .memory) (cls := .any) rfl rfl rfl (by decide +kernel)

/-- `p = ps[i];` (`ps : Person[] memory`) reads an `Identity`. -/
theorem faithful_memoryIndexReadAliasRoot {C : Contract} {k : Nat} {x : RefTy} {m : Modality}
    {mv₁ mv₂ : Var} {ie : Simple C PrimTy.uint} :
    CtorFaithful ``Taclet.memoryIndexReadAliasRoot
      (stmtOf (@Taclet.memoryIndexReadAliasRoot C k x m mv₁ mv₂ ie)) :=
  ctorFaithful_of (dom := .memory) (cls := .reference) rfl rfl rfl (by decide +kernel)

/-- `m.age += x;` reads `m.age` under `read<[int]>`. -/
theorem faithful_memoryFieldOpAssign {C : Contract} {k : Nat} {m : Modality} {p : PrimTy}
    {op : BinOp} {hop : Eq (BinOp.hasCompoundAssign op) true} {hp : Eq (PrimTy.isNumeric p) true}
    {mv : Var} {fld x : Name} {hfld : Eq (Contract.fieldType C x fld) (some (Ty.prim p))}
    {se : Simple C p} :
    CtorFaithful ``Taclet.memoryFieldOpAssign
      (stmtOf (@Taclet.memoryFieldOpAssign C k m p op hop hp mv fld x hfld se)) :=
  ctorFaithful_of (dom := .memory) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- `ns[i] += x;` reads the element under `read<[int]>`. -/
theorem faithful_memoryIndexArrayOpAssign {C : Contract} {k : Nat} {m : Modality} {p : PrimTy}
    {op : BinOp} {hop : Eq (BinOp.hasCompoundAssign op) true} {hp : Eq (PrimTy.isNumeric p) true}
    {mv : Var} {ie : Simple C PrimTy.uint} {se : Simple C p} :
    CtorFaithful ``Taclet.memoryIndexArrayOpAssign
      (stmtOf (@Taclet.memoryIndexArrayOpAssign C k m p op hop hp mv ie se)) :=
  ctorFaithful_of (dom := .memory) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- `m.age++;` reads `m.age` under `read<[int]>`. -/
theorem faithful_memoryFieldIncrement {C : Contract} {k : Nat} {m : Modality} {p : PrimTy}
    {op : IncDec} {hp : Eq (PrimTy.isNumeric p) true} {mv : Var} {fld x : Name}
    {hfld : Eq (Contract.fieldType C x fld) (some (Ty.prim p))} :
    CtorFaithful ``Taclet.memoryFieldIncrement
      (stmtOf (@Taclet.memoryFieldIncrement C k m p op hp mv fld x hfld)) :=
  ctorFaithful_of (dom := .memory) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- `ns[i]++;` reads the element under `read<[int]>`. -/
theorem faithful_memoryIndexArrayIncrement {C : Contract} {k : Nat} {m : Modality} {p : PrimTy}
    {op : IncDec} {hp : Eq (PrimTy.isNumeric p) true} {mv : Var} {ie : Simple C PrimTy.uint} :
    CtorFaithful ``Taclet.memoryIndexArrayIncrement
      (stmtOf (@Taclet.memoryIndexArrayIncrement C k m p op hp mv ie)) :=
  ctorFaithful_of (dom := .memory) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- `x = m.age++;` reads `m.age` under `read<[int]>`, twice. -/
theorem faithful_memoryFieldIncrementAssignment {C : Contract} {k : Nat} {m : Modality}
    {p : PrimTy} {v : Var} {op : IncDec} {hp : Eq (PrimTy.isNumeric p) true} {mv : Var}
    {fld x : Name} {hfld : Eq (Contract.fieldType C x fld) (some (Ty.prim p))}
    {hs : Eq (OpLoc.recvSimple (OpLoc.mfield (MPath.var mv) fld hfld)) true} :
    CtorFaithful ``Taclet.memoryFieldIncrementAssignment
      (stmtOf (@Taclet.memoryFieldIncrementAssignment C k m p v op hp mv fld x hfld hs)) :=
  ctorFaithful_of (dom := .memory) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- `x = ns[i]++;` reads the element under `read<[int]>`, twice. -/
theorem faithful_memoryIndexArrayIncrementAssignment {C : Contract} {k : Nat} {m : Modality}
    {p : PrimTy} {v : Var} {op : IncDec} {hp : Eq (PrimTy.isNumeric p) true} {mv : Var}
    {ie : Simple C PrimTy.uint} {hs : Eq (OpLoc.recvSimple (OpLoc.mindex (MPath.var mv) ie)) true} :
    CtorFaithful ``Taclet.memoryIndexArrayIncrementAssignment
      (stmtOf (@Taclet.memoryIndexArrayIncrementAssignment C k m p v op hp mv ie hs)) :=
  ctorFaithful_of (dom := .memory) (cls := .numeric)
    rfl rfl (by simpa [ReadClass.fits, Read.ty, isNumericTy] using hp) (by decide +kernel)

/-- A constructor with the theorem that it is faithful. -/
structure Proved where
  ctor : Lean.Name
  claim : Prop
  proof : claim

/-- The read-bearing constructors, each with its faithfulness theorem. -/
def faithfulCtors : List Proved := [
  ⟨``Taclet.storageRootWriteCopySource, _, @faithful_storageRootWriteCopySource⟩,
  ⟨``Taclet.storageRootReadSelect, _, @faithful_storageRootReadSelect⟩,
  ⟨``Taclet.storageFieldWriteCopySource, _, @faithful_storageFieldWriteCopySource⟩,
  ⟨``Taclet.storageFieldReadFind, _, @faithful_storageFieldReadFind⟩,
  ⟨``Taclet.storageFieldReadStoreRoot, _, @faithful_storageFieldReadStoreRoot⟩,
  ⟨``Taclet.storageIndexReadMappingFind, _, @faithful_storageIndexReadMappingFind⟩,
  ⟨``Taclet.storageIndexReadMappingStoreRoot, _, @faithful_storageIndexReadMappingStoreRoot⟩,
  ⟨``Taclet.storageIndexWriteMappingCopySource, _, @faithful_storageIndexWriteMappingCopySource⟩,
  ⟨``Taclet.storageIndexReadArrayFind, _, @faithful_storageIndexReadArrayFind⟩,
  ⟨``Taclet.storageIndexReadArrayStoreRoot, _, @faithful_storageIndexReadArrayStoreRoot⟩,
  ⟨``Taclet.storageIndexWriteArrayCopySource, _, @faithful_storageIndexWriteArrayCopySource⟩,
  ⟨``Taclet.storagePushValueCopySource, _, @faithful_storagePushValueCopySource⟩,
  ⟨``Taclet.memoryStorageCopy, _, @faithful_memoryStorageCopy⟩,
  ⟨``Taclet.storageRootOpAssign, _, @faithful_storageRootOpAssign⟩,
  ⟨``Taclet.storageFieldOpAssign, _, @faithful_storageFieldOpAssign⟩,
  ⟨``Taclet.storageIndexMappingOpAssign, _, @faithful_storageIndexMappingOpAssign⟩,
  ⟨``Taclet.storageIndexArrayOpAssign, _, @faithful_storageIndexArrayOpAssign⟩,
  ⟨``Taclet.storageRootIncrement, _, @faithful_storageRootIncrement⟩,
  ⟨``Taclet.storageFieldIncrement, _, @faithful_storageFieldIncrement⟩,
  ⟨``Taclet.storageIndexIncrement, _, @faithful_storageIndexIncrement⟩,
  ⟨``Taclet.storageRootIncrementAssignment, _, @faithful_storageRootIncrementAssignment⟩,
  ⟨``Taclet.storageFieldIncrementAssignment, _, @faithful_storageFieldIncrementAssignment⟩,
  ⟨``Taclet.storageIndexIncrementAssignment, _, @faithful_storageIndexIncrementAssignment⟩,
  ⟨``Taclet.memoryToStorageFieldCopyRoot, _, @faithful_memoryToStorageFieldCopyRoot⟩,
  ⟨``Taclet.memoryFieldReadHeap, _, @faithful_memoryFieldReadHeap⟩,
  ⟨``Taclet.memoryFieldReadAliasRoot, _, @faithful_memoryFieldReadAliasRoot⟩,
  ⟨``Taclet.memoryIndexReadHeap, _, @faithful_memoryIndexReadHeap⟩,
  ⟨``Taclet.memoryIndexReadAliasRoot, _, @faithful_memoryIndexReadAliasRoot⟩,
  ⟨``Taclet.memoryFieldOpAssign, _, @faithful_memoryFieldOpAssign⟩,
  ⟨``Taclet.memoryIndexArrayOpAssign, _, @faithful_memoryIndexArrayOpAssign⟩,
  ⟨``Taclet.memoryFieldIncrement, _, @faithful_memoryFieldIncrement⟩,
  ⟨``Taclet.memoryIndexArrayIncrement, _, @faithful_memoryIndexArrayIncrement⟩,
  ⟨``Taclet.memoryFieldIncrementAssignment, _, @faithful_memoryFieldIncrementAssignment⟩,
  ⟨``Taclet.memoryIndexArrayIncrementAssignment, _, @faithful_memoryIndexArrayIncrementAssignment⟩ ]

/-- **Every row is covered.**  Each annotation row with a value read names a
KeY taclet some `Taclet` constructor transcribes, and every constructor
transcribing it is in `faithfulCtors`: with the theorems above, every
row's value-read sort is faithful wherever its rule fires.  A new
read-bearing taclet, or a row moved to a constructor without a theorem,
fails here. -/
theorem rows_covered :
    tacletReadAnns.all (fun row => (valueReads row).isEmpty ||
      (!(ctorsOf row.keyName).isEmpty &&
        (ctorsOf row.keyName).all ((faithfulCtors.map (·.ctor)).contains ·))) = true := by
  decide +kernel

/-- What the theorems speak about: of the 110 rows, 95 carry a value read
(65 in storage, 30 in memory), 87 of them with a sort that says something
and 8 with only the claim-free `StValue`; the other 15 read only `size`
cells, the `net` ledger or `delete` defaults, which `solkeycheck` checks
token by token. -/
theorem rows_accounting :
    tacletReadAnns.length = 110 ∧
    (tacletReadAnns.filter fun row => !(valueReads row).isEmpty).length = 95 ∧
    (tacletReadAnns.filter fun row => (valueReads row).any (·.domain == .storage)).length = 65 ∧
    (tacletReadAnns.filter fun row => (valueReads row).any (·.domain == .memory)).length = 30 ∧
    (tacletReadAnns.filter fun row => (valueReads row).any (·.sort != .fixed .stValue)).length
      = 87 := by
  decide +kernel

end SortFaithfulness
end Solidity
