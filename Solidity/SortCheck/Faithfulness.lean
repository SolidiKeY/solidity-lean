import Solidity.Typing.TypedWT
import Solidity.Semantics.Core.StateErase
import Solidity.Calculus.RuleShapes
import Solidity.SortCheck.Annotations

/-!
# Sort-faithfulness of the taclet annotations

The table ↔ semantics edge of the conformance loop: every read-sort
annotation in `TacletAnnotations.tacletReadAnns` is *faithful* — the sort a
taclet's value read declares agrees with the value the interpreter finds
there, in every state that agrees (`Agree`, `Semantics/Core/StateErase.lean`) with a
scoped state the invariant `RunWT` (`Typing/Soundness.lean`) holds of.
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
(`Stmt.read?`, on the scoped statement, a `CRead` that erases to a `Read`
under any names of its locals).  That is the read the row annotates (a row's other reads are
`size` cells, the `net` ledger and `delete` defaults, which the Lean model
has no cell for: `solkeycheck` checks their tokens).  The typed syntax makes
the fixed claims *static*: an `⊕=` target is at a numeric type by its
constructor, a copy source at a reference type.  So each row is faithful
once its constructors read at a type of the right class (`ReadClass`), and
`Read.sortOk` does the rest from the typing of the evaluators.

**Which statements.**  A row names a KeY taclet; `RuleShapes.tacletOrigins`
names the scoped `Core.Taclet` constructors that transcribe it (`ctorsOf`).
For each of the 36 read-bearing constructors, `faithful_<ctor>` quantifies
over the constructor's schema variables and takes the statement from the
constructor's own type (`stmtOf`), so the statement is the rule's `\find`,
not a restatement of it; `faithful_theorem` states it from the type, the
binders being the ones the rule's schema variables bind (`Calculus/Core/Rules.lean`).  `rows_covered` checks that every row with a value
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
  /-- `values.length`: KeY reads it as the member `length` of the array, a
  `uint` cell (`size`). -/
  | slen {E : Ty} (p : SPath C (.array E))
  /-- `xs.length` of a memory array. -/
  | mlen {E : Ty} (p : MPath C (.array E))

/-- `alice.age` is read from storage, `m.age` from memory. -/
def Read.domain : Read C → ReadDomain
  | .storage .. | .slen _ => .storage
  | .memory .. | .mlen _ => .memory

/-- `alice.age` is read at `uint`, and so is a length. -/
def Read.ty : Read C → Ty
  | .storage T _ | .memory T _ => T
  | .slen _ | .mlen _ => .uint

/-- The read's locals are used as declared: it is the erasure, under the
names `ns`, of a read in the scoped syntax over `Γ` (`resolve` finds one when
it accepts the statement). -/
def Read.Typed (ns : List Var) (Γ : Core.Ctx) : Read C → Prop
  | .storage T p => ∃ p' : Core.SPath C Γ T, p'.erase ns = p
  | .memory T p => ∃ p' : Core.MPath C Γ T, p'.erase ns = p
  | @Read.slen _ E p => ∃ p' : Core.SPath C Γ (.array E), p'.erase ns = p
  | @Read.mlen _ E p => ∃ p' : Core.MPath C Γ (.array E), p'.erase ns = p

/-- A read of the scoped syntax over `Γ`: a storage or memory path at its
type, or a length.  It erases, under the names `ns`, to a `Read` its locals
are used as declared in (`CRead.erase_typed`). -/
inductive CRead (C : Contract) (Γ : Core.Ctx) where
  | storage (T : Ty) (p : Core.SPath C Γ T)
  | memory (T : Ty) (p : Core.MPath C Γ T)
  | slen {E : Ty} (p : Core.SPath C Γ (.array E))
  | mlen {E : Ty} (p : Core.MPath C Γ (.array E))

/-- The read under the names `ns`. -/
def CRead.erase {Γ : Core.Ctx} (ns : List Var) : CRead C Γ → Read C
  | .storage T p => .storage T (p.erase ns)
  | .memory T p => .memory T (p.erase ns)
  | .slen p => .slen (p.erase ns)
  | .mlen p => .mlen (p.erase ns)

/-- `alice.age` is read from storage, `m.age` from memory. -/
def CRead.domain {Γ : Core.Ctx} : CRead C Γ → ReadDomain
  | .storage .. | .slen _ => .storage
  | .memory .. | .mlen _ => .memory

/-- `alice.age` is read at `uint`, and so is a length. -/
def CRead.ty {Γ : Core.Ctx} : CRead C Γ → Ty
  | .storage T _ | .memory T _ => T
  | .slen _ | .mlen _ => .uint

theorem CRead.erase_typed {Γ : Core.Ctx} (ns : List Var) :
    (R : CRead C Γ) → (R.erase ns).Typed ns Γ
  | .storage _ p | .memory _ p | .slen p | .mlen p => ⟨p, rfl⟩

theorem CRead.erase_domain {Γ : Core.Ctx} (ns : List Var) :
    (R : CRead C Γ) → (R.erase ns).domain = R.domain
  | .storage .. | .memory .. | .slen _ | .mlen _ => rfl

theorem CRead.erase_ty {Γ : Core.Ctx} (ns : List Var) : (R : CRead C Γ) → (R.erase ns).ty = R.ty
  | .storage .. | .memory .. | .slen _ | .mlen _ => rfl

/-- The place `x ⊕= e` and `x++` read: `alice.age` in storage, `m.age` in
memory; a stack local is not read from a state component. -/
def OpLoc.read? {Γ : Core.Ctx} : {p : PrimTy} → Core.OpLoc C Γ p → Option (CRead C Γ)
  | _, .local _ => none
  | p, .root r h => some (.storage (.prim p) (.loc (.root r h)))
  | p, .field b f h => some (.storage (.prim p) (.loc (.field b f h)))
  | p, .index it b i => some (.storage (.prim p) (.loc (.index it b (.simple i))))
  | p, .mfield b f h => some (.memory (.prim p) (.loc (.field b f h)))
  | p, .mindex a b i => some (.memory (.prim p) (.loc (.index a b (.simple i))))

/-- The value read a statement performs: `x = alice.age;` reads `alice.age`,
`alice = bob;` reads `bob`, `m = alice;` reads `alice`, `alice.age += 1;`
reads `alice.age`. -/
def Stmt.read? {Γ Γ' : Core.Ctx} : Core.Stmt C Γ Γ' → Option (CRead C Γ)
  | @Core.Stmt.assignLocal _ _ p _ (.read l) => some (.storage (.prim p) (.loc l))
  | @Core.Stmt.assignLocal _ _ p _ (.readMem l) => some (.memory (.prim p) (.loc l))
  | @Core.Stmt.assignLocal _ _ _ _ (.len b _) => some (.slen b)
  | @Core.Stmt.assignLocal _ _ _ _ (.mlen b _) => some (.mlen b)
  | @Core.Stmt.assign _ _ _ _ (@Core.Src.copy _ _ R sp _) => some (.storage (.ref R) sp)
  | @Core.Stmt.push _ _ _ _ (some (@Core.Src.copy _ _ R sp _)) _ => some (.storage (.ref R) sp)
  | @Core.Stmt.rebindMem _ _ R _ (.copy sp _) => some (.storage (.ref R) sp)
  | @Core.Stmt.rebindMem _ _ R _ (.alias mp) => some (.memory (.ref R) mp)
  | @Core.Stmt.assignFromMem _ _ R _ mp => some (.memory (.ref R) mp)
  | .opAssign _ _ _ l _ => OpLoc.read? l
  | .incDec _ _ l => OpLoc.read? l
  | .assignIncDec _ _ _ l _ => OpLoc.read? l
  | _ => none

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
  | .slen p => ∀ v, (Val.len (p := .uint) p rfl).eval σ = .ok v → SortOkS rs .uint v.toSVal = true
  | .mlen p => ∀ v, (Val.mlen (p := .uint) p rfl).eval σ = .ok v →
      SortOkM H rs .uint v.toMVal = true

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
every state that agrees with a `RunWT` state: `x = total;` finds a number
where `total : uint`, `alice.age += 1` finds an `int`, `m = alice;` finds a
`Struct` node. -/
theorem Read.sortOk {Γ : Core.Ctx} {ns : List Var} {H : HeapTy} {σ : Core.State C Γ}
    {τ : State} (hwt : Core.RunWT C H σ) (hag : Core.Agree ns σ τ) {R : Read C}
    (hw : R.Typed ns Γ) {cls : ReadClass} (hfit : cls.fits R.ty = true) {rs : ReadSort}
    (hsup : cls.supports R.domain rs = true) : R.SortOk τ H rs := by
  cases R with
  | storage T p =>
    intro r segs v hr hv
    obtain ⟨p', rfl⟩ := hw
    rw [Core.SPath.resolve_erase hag] at hr
    rw [hag.findStorage] at hv
    have hty := findStorage_hasTy hwt.glob.storage (Core.SPath.resolve_wt hwt p' hr) hv
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
    obtain ⟨p', rfl⟩ := hw
    rw [Core.MPath.mval_erase hag] at hmv
    have hty := Core.MPath.mval_wt hwt p' hmv
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
  | slen p =>
    intro v hv
    obtain ⟨p', rfl⟩ := hw
    have hty := Core.Val.eval_wt hwt (Core.Val.len (p := .uint) p' rfl)
      (by rw [← Core.Val.eval_erase hag]; exact hv)
    cases rs with
    | generic _ => exact hty
    | fixed s =>
      show v.toSVal.keySort.le s = true
      cases s <;> simp only [ReadClass.supports, Read.domain, beq_iff_eq] at hsup <;>
        (try exact Bool.noConfusion hsup) <;> subst_vars
      · exact SVal.keySort_le_stValue _
      · obtain ⟨n, hn⟩ := hasTy_numeric (ty := .uint) rfl hty
        rw [hn]; rfl
      · simp [ReadClass.fits, Read.ty, Ty.isReference, Ty.isPrimitive] at hfit
  | mlen p =>
    intro v hv
    obtain ⟨p', rfl⟩ := hw
    have hty := Value.toMVal_hasTyH (H := H)
      (Core.Val.eval_wt hwt (Core.Val.mlen (p := .uint) p' rfl)
        (by rw [← Core.Val.eval_erase hag]; exact hv))
    cases rs with
    | generic _ => exact hty
    | fixed s =>
      show v.toMVal.keySort.le s = true
      cases s <;> simp only [ReadClass.supports, Read.domain, beq_iff_eq] at hsup <;>
        (try exact Bool.noConfusion hsup) <;> subst_vars
      · exact MVal.keySort_le_memValue _
      · obtain ⟨n, hn⟩ := MVal.int_of_hasTyH_numeric (T := .uint) rfl hty
        rw [hn]; rfl
      · simp [ReadClass.fits, Read.ty, Ty.isReference, Ty.isPrimitive] at hfit

/-- The claims hold in every typed state, so after any run: a typed state's
erasure is well-typed by construction (`TState.erase_wt`), and the next
statement's read finds what its sort declares.
`Person storage p = alice; p.age = 10;` then `x = alice.age;` still reads a
number. -/
theorem Read.sortOk_typed {Γ : Core.Ctx} {ns : List Var} (hnd : nodupKeysB C.vars = true)
    (σ : Core.TState C Γ) {τ : State} {R : Read C} {cls : ReadClass} {rs : ReadSort}
    (hag : Core.Agree ns σ.erase τ) (hR : R.Typed ns Γ) (hfit : cls.fits R.ty = true)
    (hsup : cls.supports R.domain rs = true) : ∃ H', R.SortOk τ H' rs :=
  ⟨_, Read.sortOk (Core.TState.erase_wt hnd σ) hag hR hfit hsup⟩

/-! ## Rows, constructors, statements -/

/-- A constructor's type, `Core.Taclet C k m s p` under its side conditions
(`Calculus/Core/Rules.lean`): the statement `s` it is about. -/
class TacletAbout (α : Prop) (C : outParam Contract) (Γ Γ' : outParam Core.Ctx)
    (s : outParam (Core.Stmt C Γ Γ')) : Prop where

instance {k : Nat} {m : Modality} {Γ Γ' : Core.Ctx} {s : Core.Stmt C Γ Γ'}
    {p : Core.Premise C Γ Γ'} : TacletAbout (Core.Taclet C k m s p) C Γ Γ' s := ⟨⟩

instance {P α : Prop} {Γ Γ' : Core.Ctx} {s : Core.Stmt C Γ Γ'} [TacletAbout α C Γ Γ' s] :
    TacletAbout (P → α) C Γ Γ' s := ⟨⟩

/-- The statement a taclet constructor is about: the rule's `\find`, read off
its type (past its side conditions, which a faithfulness statement does not
need: it holds of the statement whichever rule fires). -/
def stmtOf {α : Prop} {Γ Γ' : Core.Ctx} {s : Core.Stmt C Γ Γ'} [TacletAbout α C Γ Γ' s] (_ : α) :
    Core.Stmt C Γ Γ' := s

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
is the statement's read, and under any names of `Γ`'s locals, in every
state that agrees with a `RunWT` state over `Γ`, the declared sort holds of
what the read finds. -/
def RowFaithful (row : TacletReadAnn) {Γ Γ' : Core.Ctx} (s : Core.Stmt C Γ Γ') : Prop :=
  ∀ r ∈ valueReads row, ∃ R, Stmt.read? s = some R ∧ R.domain = r.domain ∧
    ∀ (ns : List Var) (H : HeapTy) (σ : Core.State C Γ) (τ : State),
      Core.RunWT C H σ → Core.Agree ns σ τ → (R.erase ns).SortOk τ H r.sort

/-- Every row constructor `n` transcribes is faithful at `s`. -/
def CtorFaithful (n : Lean.Name) {Γ Γ' : Core.Ctx} (s : Core.Stmt C Γ Γ') : Prop :=
  ∀ row ∈ rowsOf n, RowFaithful row s

/-- A row is faithful at a statement whose read is of a class the row's
declared sorts are all supported by: `find<[int]>` at `total += 1;`. -/
theorem rowFaithful_of {row : TacletReadAnn} {Γ Γ' : Core.Ctx} {s : Core.Stmt C Γ Γ'}
    {R : CRead C Γ} {dom : ReadDomain} {cls : ReadClass} (hR : Stmt.read? s = some R)
    (hdom : R.domain = dom) (hfit : cls.fits R.ty = true)
    (hrow : (valueReads row).all (fun r => r.domain == dom && cls.supports dom r.sort) = true) :
    RowFaithful row s := by
  intro r hr
  have h := List.all_eq_true.mp hrow r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨R, hR, hdom.trans h.1.symm, fun ns H σ τ hwt hag => ?_⟩
  exact Read.sortOk hwt hag (R.erase_typed ns) (R.erase_ty ns ▸ hfit)
    (R.erase_domain ns ▸ hdom ▸ h.2)

/-- A constructor is faithful at a statement whose read is of a class every
row's declared sorts are supported by. -/
theorem ctorFaithful_of {n : Lean.Name} {Γ Γ' : Core.Ctx} {s : Core.Stmt C Γ Γ'} {R : CRead C Γ}
    {dom : ReadDomain} {cls : ReadClass} (hR : Stmt.read? s = some R) (hdom : R.domain = dom)
    (hfit : cls.fits R.ty = true) (hrows : rowsSupported n dom cls = true) :
    CtorFaithful n s := fun row hrow =>
  rowFaithful_of hR hdom hfit (List.all_eq_true.mp hrows row hrow)

/-! ## The read-bearing constructors

One theorem per constructor with a value read, `faithful_<ctor>`, stated by
`faithful_theorem r dom cls` in `Calculus/Core/Rules.lean`'s order of the
rows: it quantifies over the constructor's schema variables (its binders,
read off its type) and states `CtorFaithful ``Core.Taclet.r (stmtOf
(@Core.Taclet.r …))`, so the statement is the rule's `\find`, not a
restatement of it, and each theorem covers every statement the rule fires
on; the proof is `ctorFaithful_of` at the domain `dom` and the class `cls`,
what the constructor's schema fixes (an `⊕=` target is `numeric` by `hp`, a
copy source a `reference` by its index).  `#check @faithful_<ctor>` prints
the statement. -/

section Gen
open Lean Elab Command Term Meta

/-- `faithful_theorem r dom cls`: the theorem `faithful_r`, that the scoped
taclet `Core.Taclet.r` is faithful (`CtorFaithful`) at its own statement,
for all its schema variables, by `ctorFaithful_of` at `dom` and `cls`. -/
elab "faithful_theorem " r:ident dom:term:max cls:term:max : command => do
  let ctor := `Solidity.Core.Taclet ++ r.getId
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
  ⟨``Core.Taclet.storageRootWriteCopySource, _, @faithful_storageRootWriteCopySource⟩,
  ⟨``Core.Taclet.storageRootReadSelect, _, @faithful_storageRootReadSelect⟩,
  ⟨``Core.Taclet.storageFieldWriteCopySource, _, @faithful_storageFieldWriteCopySource⟩,
  ⟨``Core.Taclet.storageFieldReadFind, _, @faithful_storageFieldReadFind⟩,
  ⟨``Core.Taclet.storageLengthRead, _, @faithful_storageLengthRead⟩,
  ⟨``Core.Taclet.memoryLengthRead, _, @faithful_memoryLengthRead⟩,
  ⟨``Core.Taclet.storageFieldReadStoreRoot, _, @faithful_storageFieldReadStoreRoot⟩,
  ⟨``Core.Taclet.storageIndexReadMappingFind, _, @faithful_storageIndexReadMappingFind⟩,
  ⟨``Core.Taclet.storageIndexReadMappingStoreRoot, _, @faithful_storageIndexReadMappingStoreRoot⟩,
  ⟨``Core.Taclet.storageIndexWriteMappingCopySource, _, @faithful_storageIndexWriteMappingCopySource⟩,
  ⟨``Core.Taclet.storageIndexReadArrayFind, _, @faithful_storageIndexReadArrayFind⟩,
  ⟨``Core.Taclet.storageIndexReadArrayStoreRoot, _, @faithful_storageIndexReadArrayStoreRoot⟩,
  ⟨``Core.Taclet.storageIndexWriteArrayCopySource, _, @faithful_storageIndexWriteArrayCopySource⟩,
  ⟨``Core.Taclet.storagePushValueCopySource, _, @faithful_storagePushValueCopySource⟩,
  ⟨``Core.Taclet.memoryStorageCopy, _, @faithful_memoryStorageCopy⟩,
  ⟨``Core.Taclet.storageRootOpAssign, _, @faithful_storageRootOpAssign⟩,
  ⟨``Core.Taclet.storageFieldOpAssign, _, @faithful_storageFieldOpAssign⟩,
  ⟨``Core.Taclet.storageIndexMappingOpAssign, _, @faithful_storageIndexMappingOpAssign⟩,
  ⟨``Core.Taclet.storageIndexArrayOpAssign, _, @faithful_storageIndexArrayOpAssign⟩,
  ⟨``Core.Taclet.storageRootIncrement, _, @faithful_storageRootIncrement⟩,
  ⟨``Core.Taclet.storageFieldIncrement, _, @faithful_storageFieldIncrement⟩,
  ⟨``Core.Taclet.storageIndexIncrement, _, @faithful_storageIndexIncrement⟩,
  ⟨``Core.Taclet.storageRootIncrementAssignment, _, @faithful_storageRootIncrementAssignment⟩,
  ⟨``Core.Taclet.storageFieldIncrementAssignment, _, @faithful_storageFieldIncrementAssignment⟩,
  ⟨``Core.Taclet.storageIndexIncrementAssignment, _, @faithful_storageIndexIncrementAssignment⟩,
  ⟨``Core.Taclet.memoryToStorageFieldCopyRoot, _, @faithful_memoryToStorageFieldCopyRoot⟩,
  ⟨``Core.Taclet.memoryFieldRead, _, @faithful_memoryFieldRead⟩,
  ⟨``Core.Taclet.memoryFieldReadAliasRoot, _, @faithful_memoryFieldReadAliasRoot⟩,
  ⟨``Core.Taclet.memoryIndexReadArrayValue, _, @faithful_memoryIndexReadArrayValue⟩,
  ⟨``Core.Taclet.memoryIndexReadArrayMemory, _, @faithful_memoryIndexReadArrayMemory⟩,
  ⟨``Core.Taclet.memoryFieldOpAssign, _, @faithful_memoryFieldOpAssign⟩,
  ⟨``Core.Taclet.memoryIndexArrayOpAssign, _, @faithful_memoryIndexArrayOpAssign⟩,
  ⟨``Core.Taclet.memoryFieldIncrement, _, @faithful_memoryFieldIncrement⟩,
  ⟨``Core.Taclet.memoryIndexArrayIncrement, _, @faithful_memoryIndexArrayIncrement⟩,
  ⟨``Core.Taclet.memoryFieldIncrementAssignment, _, @faithful_memoryFieldIncrementAssignment⟩,
  ⟨``Core.Taclet.memoryIndexArrayIncrementAssignment, _, @faithful_memoryIndexArrayIncrementAssignment⟩ ]

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

/-- What the theorems speak about: of the 119 rows, 95 carry a value read
(65 in storage, 30 in memory), 87 of them with a sort that says something
and 8 with only the claim-free `StValue`; the other 24 read only `size`
cells, the `net` ledger or `delete` defaults, which `solkeycheck` checks
token by token. -/
theorem rows_accounting :
    tacletReadAnns.length = 119 ∧
    (tacletReadAnns.filter fun row => !(valueReads row).isEmpty).length = 95 ∧
    (tacletReadAnns.filter fun row => (valueReads row).any (·.domain == .storage)).length = 65 ∧
    (tacletReadAnns.filter fun row => (valueReads row).any (·.domain == .memory)).length = 30 ∧
    (tacletReadAnns.filter fun row => (valueReads row).any (·.sort != .fixed .stValue)).length
      = 87 := by
  decide +kernel

end SortFaithfulness
end Solidity
