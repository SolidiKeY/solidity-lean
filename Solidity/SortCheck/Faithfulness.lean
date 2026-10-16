import Solidity.Typing.Sorts
import Solidity.Semantics.Run
import Solidity.Calculus.RuleShapes
import Solidity.SortCheck.Annotations

/-!
# Sort-faithfulness of the taclet annotations

The table ↔ semantics edge of the conformance loop: every read-sort
annotation in `TacletAnnotations.tacletReadAnns` is *faithful* — the sort a
taclet's value read declares agrees with the value the typed run's
evaluators (`Semantics/Run.lean`: `SPath.resolveT`, `MPath.mvalT`,
`Val.evalT`) find there, in every typed state: the value is of its type by
construction, and its runtime sort is its type's (`SVal.keySort`,
`Typing/Sorts.lean`).
`solkeycheck` keeps the table equal to the `.key` text; this module keeps it
true of the interpreter, so a table updated to match a buggy
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
(`Stmt.read?`, a `Read` of the scoped statement's own paths).  That is
the read the row annotates (a row's other reads are `size` cells, the `net`
ledger and `delete` defaults, which the Lean model has no cell for:
`solkeycheck` checks their tokens).  The typed syntax makes
the fixed claims *static*: an `⊕=` target is at a numeric type by its
constructor, a copy source at a reference type.  So each row is faithful
once its constructors read at a type of the right class (`ReadClass`), and
`Read.sortOk` does the rest from the typing of the typed values.

**Which statements.**  A row names a KeY taclet; `RuleShapes.tacletOrigins`
names the scoped `Taclet` constructors that transcribe it (`ctorsOf`).
For each of the 36 read-bearing constructors, `faithful_<ctor>` quantifies
over the constructor's schema variables and takes the statement from the
constructor's own type (`stmtOf`), so the statement is the rule's `\find`,
not a restatement of it; `faithful_theorem` states it from the type, the
binders being the ones the rule's schema variables bind (`Calculus/Rules.lean`).  `rows_covered` checks that every row with a value
read is claimed by constructors in `faithfulCtors`, each of which carries its
theorem.
-/

namespace Solidity
namespace SortFaithfulness

open TacletAnnotations

variable {C : Contract}

/-! ## The value read of a statement -/

/-- A read of the scoped syntax over `Γ`: a storage path or a memory path,
at its static type, or a length. -/
inductive Read (C : Contract) (Γ : Ctx) where
  | storage (T : Ty) (p : SPath C Γ T)
  | memory (T : Ty) (p : MPath C Γ T)
  /-- `values.length`: KeY reads it as the member `length` of the array, a
  `uint` cell (`size`). -/
  | slen {E : Ty} (p : SPath C Γ (.array E))
  /-- `xs.length` of a memory array. -/
  | mlen {E : Ty} (p : MPath C Γ (.array E))
  /-- `y = values.push()`: the slot appended (`pushSlot`), read at the
  element type. -/
  | sslot {E : Ty} (p : SPath C Γ (.array E))

/-- `alice.age` is read from storage, `m.age` from memory. -/
def Read.domain {Γ : Ctx} : Read C Γ → ReadDomain
  | .storage .. | .slen _ | .sslot _ => .storage
  | .memory .. | .mlen _ => .memory

/-- `alice.age` is read at `uint`, and so is a length. -/
def Read.ty {Γ : Ctx} : Read C Γ → Ty
  | .storage T _ | .memory T _ => T
  | .slen _ | .mlen _ => .uint
  | .sslot (E := E) _ => E

/-- The place `x ⊕= e` and `x++` read: `alice.age` in storage, `m.age` in
memory; a stack local is not read from a state component. -/
def OpLoc.read? {Γ : Ctx} : {p : PrimTy} → OpLoc C Γ p → Option (Read C Γ)
  | _, .local _ => none
  | p, .root r h => some (.storage (.prim p) (.loc (.root r h)))
  | p, .field b f h => some (.storage (.prim p) (.loc (.field b f h)))
  | p, .index it b i => some (.storage (.prim p) (.loc (.index it b (.simple i))))
  | p, .mfield b f h => some (.memory (.prim p) (.loc (.field b f h)))
  | p, .mindex a b i => some (.memory (.prim p) (.loc (.index a b (.simple i))))

/-- The value read a statement performs: `x = alice.age;` reads `alice.age`,
`alice = bob;` reads `bob`, `m = alice;` reads `alice`, `alice.age += 1;`
reads `alice.age`. -/
def Stmt.read? {Γ Γ' : Ctx} : Stmt C Γ Γ' → Option (Read C Γ)
  | @Stmt.assignLocal _ _ p _ (.read l) => some (.storage (.prim p) (.loc l))
  | @Stmt.assignLocal _ _ p _ (.readMem l) => some (.memory (.prim p) (.loc l))
  | @Stmt.assignLocal _ _ _ _ (.len b _) => some (.slen b)
  | @Stmt.assignLocal _ _ _ _ (.mlen b _) => some (.mlen b)
  | @Stmt.assign _ _ _ _ (@Src.copy _ _ R sp _) => some (.storage (.ref R) sp)
  | @Stmt.push _ _ _ _ (some (@Src.copy _ _ R sp _)) _ => some (.storage (.ref R) sp)
  | @Stmt.rebindMem _ _ R _ (.copy sp _) => some (.storage (.ref R) sp)
  | @Stmt.rebindMem _ _ R _ (.alias mp) => some (.memory (.ref R) mp)
  | @Stmt.assignFromMem _ _ R _ mp => some (.memory (.ref R) mp)
  | .opAssign _ _ _ l _ => OpLoc.read? l
  | .incDec _ _ l => OpLoc.read? l
  | .assignIncDec _ _ _ l _ => OpLoc.read? l
  | .assignLocalPush _ b => some (.sslot b)
  | .pushOpAssign _ _ _ b _ | .pushIncDec _ _ b => some (.sslot b)
  | _ => none

/-! ## What a declared sort claims -/

/-- What `find<[s]>`/`select<[s]>` claims of the storage value found: a
varcond-generic sort, that it inhabits the read place's type, which a typed
value does; a fixed sort, that its runtime sort lies below. -/
def SortOkS : ReadSort → {T : Ty} → SVal T → Bool
  | .generic _, _, _ => true
  | .fixed s, _, v => v.keySort.le s

/-- What `read<[s]>` claims of the memory slot found. -/
def SortOkM {H : HTy} : ReadSort → (T : Ty) → MVal H T → Bool
  | .generic _, _, _ => true
  | .fixed s, T, mv => (MVal.keySort T mv).le s

/-- The declared sort `rs` holds of whatever the read finds in the typed
state `σ`: resolving the storage path and finding the value, or reading the
memory slot. -/
def Read.SortOk {Γ : Ctx} (σ : State C Γ) (rs : ReadSort) : Read C Γ → Prop
  | .storage T p => ∀ r (v : SVal T), p.resolveT σ = .ok r → σ.storage.find r = some v →
      SortOkS rs v = true
  | .memory T p => ∀ mv, p.mvalT σ = .ok mv → SortOkM rs T mv = true
  | .slen p => ∀ v, (Val.len (p := .uint) p rfl).evalT σ = .ok v →
      SortOkS rs (SVal.prim v) = true
  | .mlen p => ∀ v, (Val.mlen (p := .uint) p rfl).evalT σ = .ok v →
      SortOkM (H := σ.H) rs (.prim .uint) v = true
  | .sslot (E := E) p => ∀ r (v : SVal (.ref (.array E))), p.resolveT σ = .ok r →
      σ.storage.find r = some v →
      SortOkS rs (pushSlot E (SVal.view v : ArrView E).shadow.toList).1 = true

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

/-- **The semantic core.**  A read of a class the declared sort is supported
by finds a value the sort claims, in every typed state: `x = total;` finds a
number where `total : uint`, `alice.age += 1` finds an `int`, `m = alice;`
finds a `Struct` node.  `Person storage p = alice; p.age = 10;` then
`x = alice.age;` still reads a number. -/
theorem Read.sortOk {Γ : Ctx} (σ : State C Γ)
    {R : Read C Γ} {cls : ReadClass} (hfit : cls.fits R.ty = true) {rs : ReadSort}
    (hsup : cls.supports R.domain rs = true) : R.SortOk σ rs := by
  cases R with
  | storage T p =>
    unfold Read.SortOk
    intro r v _ _
    cases rs with
    | generic _ => rfl
    | fixed s =>
      show v.keySort.le s = true
      cases s <;> simp only [ReadClass.supports, Read.domain, beq_iff_eq] at hsup <;>
        (try exact Bool.noConfusion hsup) <;> subst_vars
      · exact SVal.keySort_le_stValue v
      · rw [SVal.keySort_numeric (T := T) hfit v]; rfl
      · rw [SVal.keySort_ref (T := T) hfit v]; exact KeySort.le_refl _
  | memory T p =>
    unfold Read.SortOk
    intro mv _
    cases rs with
    | generic _ => rfl
    | fixed s =>
      show (MVal.keySort T mv).le s = true
      cases s <;> simp only [ReadClass.supports, Read.domain, beq_iff_eq] at hsup <;>
        (try exact Bool.noConfusion hsup) <;> subst_vars
      · exact MVal.keySort_le_memValue T mv
      · rw [MVal.keySort_numeric (T := T) hfit mv]; rfl
      · rw [MVal.keySort_ref (T := T) hfit mv]; rfl
  | slen p =>
    unfold Read.SortOk
    intro v _
    cases rs with
    | generic _ => rfl
    | fixed s =>
      show (SVal.prim v).keySort.le s = true
      cases s <;> simp only [ReadClass.supports, Read.domain, beq_iff_eq] at hsup <;>
        (try exact Bool.noConfusion hsup) <;> subst_vars
      · exact SVal.keySort_le_stValue _
      · rfl
      · simp [ReadClass.fits, Read.ty, Ty.isReference, Ty.isPrimitive] at hfit
  | mlen p =>
    unfold Read.SortOk
    intro v _
    cases rs with
    | generic _ => rfl
    | fixed s =>
      show (MVal.keySort (H := σ.H) (.prim .uint) v).le s = true
      cases s <;> simp only [ReadClass.supports, Read.domain, beq_iff_eq] at hsup <;>
        (try exact Bool.noConfusion hsup) <;> subst_vars
      · exact MVal.keySort_le_memValue (H := σ.H) (.prim .uint) v
      · rfl
      · simp [ReadClass.fits, Read.ty, Ty.isReference, Ty.isPrimitive] at hfit
  | @sslot E p =>
    unfold Read.SortOk
    intro r v _ _
    generalize (pushSlot E (SVal.view v : ArrView E).shadow.toList).1 = x
    cases rs with
    | generic _ => rfl
    | fixed s =>
      show x.keySort.le s = true
      cases s <;> simp only [ReadClass.supports, Read.domain, beq_iff_eq] at hsup <;>
        (try exact Bool.noConfusion hsup) <;> subst_vars
      · exact SVal.keySort_le_stValue x
      · rw [SVal.keySort_numeric (T := E) hfit x]; rfl
      · rw [SVal.keySort_ref (T := E) hfit x]; exact KeySort.le_refl _

/-! ## Rows, constructors, statements -/

/-- A constructor's type, `Taclet C k m s p` under its side conditions
(`Calculus/Rules.lean`): the statement `s` it is about. -/
class TacletAbout (α : Prop) (C : outParam Contract) (Γ Γ' : outParam Ctx)
    (s : outParam (Stmt C Γ Γ')) : Prop where

instance {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} : TacletAbout (Taclet C k m s p) C Γ Γ' s := ⟨⟩

instance {P α : Prop} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} [TacletAbout α C Γ Γ' s] :
    TacletAbout (P → α) C Γ Γ' s := ⟨⟩

/-- The statement a taclet constructor is about: the rule's `\find`, read off
its type (past its side conditions, which a faithfulness statement does not
need: it holds of the statement whichever rule fires). -/
def stmtOf {α : Prop} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} [TacletAbout α C Γ Γ' s] (_ : α) :
    Stmt C Γ Γ' := s

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

/-- A row is faithful at a statement over `Γ`: each value read it declares
is the statement's read, and in every typed state over `Γ` the declared
sort holds of what the read finds. -/
def RowFaithful (row : TacletReadAnn) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Prop :=
  ∀ r ∈ valueReads row, ∃ R, Stmt.read? s = some R ∧ R.domain = r.domain ∧
    ∀ σ : State C Γ, R.SortOk σ r.sort

/-- Every row constructor `n` transcribes is faithful at `s`. -/
def CtorFaithful (n : Lean.Name) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Prop :=
  ∀ row ∈ rowsOf n, RowFaithful row s

/-- A row is faithful at a statement whose read is of a class the row's
declared sorts are all supported by: `find<[int]>` at `total += 1;`. -/
theorem rowFaithful_of {row : TacletReadAnn} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {R : Read C Γ} {dom : ReadDomain} {cls : ReadClass} (hR : Stmt.read? s = some R)
    (hdom : R.domain = dom) (hfit : cls.fits R.ty = true)
    (hrow : (valueReads row).all (fun r => r.domain == dom && cls.supports dom r.sort) = true) :
    RowFaithful row s := by
  intro r hr
  have h := List.all_eq_true.mp hrow r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨R, hR, hdom.trans h.1.symm, fun σ => Read.sortOk σ hfit (hdom ▸ h.2)⟩

/-- A constructor is faithful at a statement whose read is of a class every
row's declared sorts are supported by. -/
theorem ctorFaithful_of {n : Lean.Name} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {R : Read C Γ}
    {dom : ReadDomain} {cls : ReadClass} (hR : Stmt.read? s = some R) (hdom : R.domain = dom)
    (hfit : cls.fits R.ty = true) (hrows : rowsSupported n dom cls = true) :
    CtorFaithful n s := fun row hrow =>
  rowFaithful_of hR hdom hfit (List.all_eq_true.mp hrows row hrow)

/-! ## The read-bearing constructors

One theorem per constructor with a value read, `faithful_<ctor>`, stated by
`faithful_theorem r dom cls` in `Calculus/Rules.lean`'s order of the
rows: it quantifies over the constructor's schema variables (its binders,
read off its type) and states `CtorFaithful ``Taclet.r (stmtOf
(@Taclet.r …))`, so the statement is the rule's `\find`, not a
restatement of it, and each theorem covers every statement the rule fires
on; the proof is `ctorFaithful_of` at the domain `dom` and the class `cls`,
what the constructor's schema fixes (an `⊕=` target is `numeric` by `hp`, a
copy source a `reference` by its index).  `#check @faithful_<ctor>` prints
the statement. -/

section Gen
open Lean Elab Command Term Meta

/-- `faithful_theorem r dom cls`: the theorem `faithful_r`, that the scoped
taclet `Taclet.r` is faithful (`CtorFaithful`) at its own statement,
for all its schema variables, by `ctorFaithful_of` at `dom` and `cls`. -/
elab "faithful_theorem " r:ident dom:term:max cls:term:max : command => do
  let ctor := `Solidity.Taclet ++ r.getId
  let thm := (← getCurrNamespace) ++ (`faithful).appendAfter ("_" ++ r.getId.toString)
  let (ty, pf) ← liftTermElabM do
    let info ← getConstInfo ctor
    forallTelescope info.type fun xs _ => do
      let d ← exprToSyntax (mkAppN (mkConst ctor (info.levelParams.map mkLevelParam)) xs)
      let stmt ← elabType (← `(CtorFaithful $(quote ctor) (stmtOf $d)))
      let pf ← elabTermEnsuringType
        (← `(ctorFaithful_of (dom := $dom) (cls := $cls) rfl rfl (by first | rfl | assumption)
          (by decide +kernel))) stmt
      synthesizeSyntheticMVarsNoPostponing
      let stmt ← instantiateMVars stmt
      let pf ← instantiateMVars pf
      if pf.hasExprMVar then throwError "faithful_theorem: the proof of {ctor} is not closed"
      return (← mkForallFVars xs stmt, ← mkLambdaFVars xs pf)
  liftCoreM <| addDecl (.thmDecl { name := thm, levelParams := [], type := ty, value := pf })

end Gen

-- `alice = bob;` reads `bob`, a `Person`: the copy source is a reference, and
-- the row's `find<[StValue]>` claims no more than a storage value.
faithful_theorem storageRootWriteCopySource .storage .reference
-- `x = total;` reads a number, `total`'s declared `uint`.
faithful_theorem storageRootReadSelect .storage .any
faithful_theorem storageFieldWriteCopySource .storage .reference
faithful_theorem storageFieldReadFind .storage .any
faithful_theorem storageLengthRead .storage .any
faithful_theorem memoryLengthRead .memory .any
faithful_theorem storageFieldReadStoreRoot .storage .reference
faithful_theorem storageIndexReadMappingFind .storage .any
faithful_theorem storageIndexReadMappingStoreRoot .storage .reference
faithful_theorem storageIndexWriteMappingCopySource .storage .reference
faithful_theorem storageIndexReadArrayFind .storage .any
faithful_theorem storageIndexReadArrayStoreRoot .storage .reference
faithful_theorem storageIndexWriteArrayCopySource .storage .reference
faithful_theorem storagePushValueCopySource .storage .reference
-- `y = values.push();` reads the slot appended, at the element type.
faithful_theorem storageLocalPrimitivePushBind .storage .any
faithful_theorem storagePushAddAssign .storage .numeric
faithful_theorem storagePushSubAssign .storage .numeric
faithful_theorem storagePushMulAssign .storage .numeric
faithful_theorem storagePushDivAssign .storage .numeric
faithful_theorem storagePushModAssign .storage .numeric
faithful_theorem storagePushPreincrement .storage .numeric
faithful_theorem storagePushPostincrement .storage .numeric
faithful_theorem storagePushPredecrement .storage .numeric
faithful_theorem storagePushPostdecrement .storage .numeric
faithful_theorem memoryStorageCopy .storage .reference
faithful_theorem storageRootOpAssign .storage .numeric
faithful_theorem storageFieldOpAssign .storage .numeric
faithful_theorem storageIndexMappingOpAssign .storage .numeric
faithful_theorem storageIndexArrayOpAssign .storage .numeric
faithful_theorem storageRootIncrement .storage .numeric
faithful_theorem storageFieldIncrement .storage .numeric
faithful_theorem storageIndexIncrement .storage .numeric
faithful_theorem storageRootIncrementAssignment .storage .numeric
faithful_theorem storageFieldIncrementAssignment .storage .numeric
faithful_theorem storageIndexIncrementAssignment .storage .numeric
faithful_theorem memoryToStorageFieldCopyRoot .memory .reference
faithful_theorem memoryFieldRead .memory .any
faithful_theorem memoryFieldReadAliasRoot .memory .any
faithful_theorem memoryIndexReadArrayValue .memory .any
faithful_theorem memoryIndexReadArrayMemory .memory .reference
faithful_theorem memoryFieldOpAssign .memory .numeric
faithful_theorem memoryIndexArrayOpAssign .memory .numeric
faithful_theorem memoryFieldIncrement .memory .numeric
faithful_theorem memoryIndexArrayIncrement .memory .numeric
faithful_theorem memoryFieldIncrementAssignment .memory .numeric
faithful_theorem memoryIndexArrayIncrementAssignment .memory .numeric


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
  ⟨``Taclet.storageLengthRead, _, @faithful_storageLengthRead⟩,
  ⟨``Taclet.memoryLengthRead, _, @faithful_memoryLengthRead⟩,
  ⟨``Taclet.storageFieldReadStoreRoot, _, @faithful_storageFieldReadStoreRoot⟩,
  ⟨``Taclet.storageIndexReadMappingFind, _, @faithful_storageIndexReadMappingFind⟩,
  ⟨``Taclet.storageIndexReadMappingStoreRoot, _, @faithful_storageIndexReadMappingStoreRoot⟩,
  ⟨``Taclet.storageIndexWriteMappingCopySource, _, @faithful_storageIndexWriteMappingCopySource⟩,
  ⟨``Taclet.storageIndexReadArrayFind, _, @faithful_storageIndexReadArrayFind⟩,
  ⟨``Taclet.storageIndexReadArrayStoreRoot, _, @faithful_storageIndexReadArrayStoreRoot⟩,
  ⟨``Taclet.storageIndexWriteArrayCopySource, _, @faithful_storageIndexWriteArrayCopySource⟩,
  ⟨``Taclet.storagePushValueCopySource, _, @faithful_storagePushValueCopySource⟩,
  ⟨``Taclet.storageLocalPrimitivePushBind, _, @faithful_storageLocalPrimitivePushBind⟩,
  ⟨``Taclet.storagePushAddAssign, _, @faithful_storagePushAddAssign⟩,
  ⟨``Taclet.storagePushSubAssign, _, @faithful_storagePushSubAssign⟩,
  ⟨``Taclet.storagePushMulAssign, _, @faithful_storagePushMulAssign⟩,
  ⟨``Taclet.storagePushDivAssign, _, @faithful_storagePushDivAssign⟩,
  ⟨``Taclet.storagePushModAssign, _, @faithful_storagePushModAssign⟩,
  ⟨``Taclet.storagePushPreincrement, _, @faithful_storagePushPreincrement⟩,
  ⟨``Taclet.storagePushPostincrement, _, @faithful_storagePushPostincrement⟩,
  ⟨``Taclet.storagePushPredecrement, _, @faithful_storagePushPredecrement⟩,
  ⟨``Taclet.storagePushPostdecrement, _, @faithful_storagePushPostdecrement⟩,
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
  ⟨``Taclet.memoryFieldRead, _, @faithful_memoryFieldRead⟩,
  ⟨``Taclet.memoryFieldReadAliasRoot, _, @faithful_memoryFieldReadAliasRoot⟩,
  ⟨``Taclet.memoryIndexReadArrayValue, _, @faithful_memoryIndexReadArrayValue⟩,
  ⟨``Taclet.memoryIndexReadArrayMemory, _, @faithful_memoryIndexReadArrayMemory⟩,
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

/-- What the theorems speak about: of the 131 rows, 105 carry a value read
(75 in storage, 30 in memory), 97 of them with a sort that says something
and 8 with only the claim-free `StValue`; the other 26 read only `size`
cells, the `net` ledger or `delete` defaults, which `solkeycheck` checks
token by token. -/
theorem rows_accounting :
    tacletReadAnns.length = 131 ∧
    (tacletReadAnns.filter fun row => !(valueReads row).isEmpty).length = 105 ∧
    (tacletReadAnns.filter fun row => (valueReads row).any (·.domain == .storage)).length = 75 ∧
    (tacletReadAnns.filter fun row => (valueReads row).any (·.domain == .memory)).length = 30 ∧
    (tacletReadAnns.filter fun row => (valueReads row).any (·.sort != .fixed .stValue)).length
      = 97 := by
  decide +kernel

end SortFaithfulness
end Solidity
