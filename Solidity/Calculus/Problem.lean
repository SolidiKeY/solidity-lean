import Solidity.Typing.Constructibility
import Solidity.Calculus.Derive

/-!
# Obligations, as solkey states them

solkey's `SolidityProblemSynthesizer` makes one obligation per function of a
contract with no specification: `\<{ f(x̄)@C; }\>(true)`, or
`\[{ f(x̄)@C; }\](true)` for a function tagged `@custom:key box`, the
parameters `x̄` program variables of sort `int` or `bool`, so free: the
obligation is proved for every value of them.  Here the parameters are
`∀` binders over their type's range (`Fml.all`): a `uint` ranges over
`[0, 2²⁵⁶)` and an `int` over the signed 256-bit range, where KeY's `int` is
unbounded, and an `int8` parameter ranges over the signed 256-bit range, as
its KeY sort does.

* **Box**: `∀x̄. [ f(x̄); ] true`.  A failed `assert` panics, and no
  modality holds of a panic (`Modality.afterRun`), so this is KeY's
  `assertSimple` "Violated" obligation, with no cut: a failed `require`
  reverts, which the box accepts, as in KeY.
* **Diamond**: `∀x̄. wt(storage) → ⟨ f(x̄); ⟩ true`.  The diamond does not
  hold of every storage: a write into a root that is not there is stuck.
  solkey's storage is the contract's by construction; here `wt(storage)`
  (`Fml.wt`) says it is one the contract can be in: every root there, in
  order, canonical and tight (`storageWtB`), which is exactly reachable
  (`wt_iff_reachable`), KeY's `wellFormed(heap)`.

**Why one atomic term.**  `wt` is a symbol of the term language, `Op1.wt`,
read by the interpreter as a test of the storage it is given, and stated
as `defined(wt(storage))`: it returns exactly on a well-formed storage.  An
expanded layout (`∀` over every root and member) would make every leaf a
quantified formula the closer has to instantiate; one atom costs one
constructor of `Op1` and nothing in `Fml`.  The closer sets it aside
(`Derive.dropWt`), which only weakens a leaf; a fact derived from it is the
closer's to add.

The argument `vs` of `wt` is the contract's roots, carried by the symbol
since a symbol does not know its contract (`Fml.wt` fills it in).
-/

namespace Solidity

open Semantics
open Semantics.SVal.canon (canonFields canonElems canonEntries)
open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB)
open Semantics.SVal.tight (tightFields tightElems tightEntries)
open Semantics.SVal.tightB (tightFieldsB tightElemsB tightEntriesB)
open SemanticsProperties (lookupBy_eq_some_mem)

variable {C : Contract}

/-! ## The test decides `canon ∧ tight` -/

theorem keysNodupB_eq {κ α : Type} [DecidableEq κ] :
    ∀ (l : List (κ × α)), keysNodupB l = nodupKeysB l
  | [] => rfl
  | (k, _) :: rest => by simp only [keysNodupB, nodupKeysB, keysNodupB_eq rest]

theorem Ty.numKeyB_eq (T : Ty) : Ty.numKeyB T = T.numericKey := by
  cases T <;> rfl

mutual

theorem SVal.canonB_iff : ∀ {v : SVal} {T : Ty}, v.canonB T = true ↔ v.canon T
  | SVal.prim (.int _), Ty.int | SVal.prim (.int _), Ty.uint | SVal.prim (.bool _), Ty.bool =>
    ⟨fun _ => trivial, fun _ => rfl⟩
  | SVal.struct fields, Ty.ref (RefTy.struct s) => by
    simp only [SVal.canonB, SVal.canon, Bool.and_eq_true, decide_eq_true_eq,
      SVal.canonFieldsB_iff]
  | SVal.array elems shadow fx, Ty.ref (RefTy.array E) => by
    simp only [SVal.canonB, SVal.canon, Bool.and_eq_true, Bool.not_eq_true',
      SVal.canonElemsB_iff, and_assoc]
  | SVal.array elems shadow fx, Ty.ref (RefTy.fixed E n) => by
    simp only [SVal.canonB, SVal.canon, Bool.and_eq_true, decide_eq_true_eq,
      SVal.canonElemsB_iff, and_assoc]
  | SVal.map entries dflt, Ty.ref (RefTy.mapping _ V) => by
    simp only [SVal.canonB, SVal.canon, Bool.and_eq_true, keysNodupB_eq,
      SVal.canonEntriesB_iff, SVal.isDfltB_iff, SVal.canonB_iff (v := dflt), and_assoc]
  | SVal.prim (.int _), Ty.bool | SVal.prim (.bool _), Ty.uint | SVal.prim (.bool _), Ty.int
  | SVal.prim _, Ty.ref _
  | SVal.struct _, Ty.prim _ | SVal.struct _, Ty.ref (.array _)
  | SVal.struct _, Ty.ref (.fixed _ _) | SVal.struct _, Ty.ref (.mapping _ _)
  | SVal.array .., Ty.prim _ | SVal.array .., Ty.ref (.struct _)
  | SVal.array .., Ty.ref (.mapping _ _)
  | SVal.map .., Ty.prim _ | SVal.map .., Ty.ref (.struct _)
  | SVal.map .., Ty.ref (.array _) | SVal.map .., Ty.ref (.fixed _ _) =>
    ⟨fun h => by simp only [SVal.canonB, Bool.false_eq_true] at h,
      fun h => by simp only [SVal.canon] at h⟩

theorem SVal.canonFieldsB_iff {s : Name} :
    ∀ {fs : List (Name × SVal)}, canonFieldsB s fs = true ↔ canonFields s fs
  | [] => ⟨fun _ => trivial, fun _ => rfl⟩
  | (n, v) :: rest => by
    simp only [canonFieldsB, canonFields, Bool.and_eq_true, SVal.canonFieldsB_iff (fs := rest)]
    cases lookupBy n (structDef s) with
    | none => simp only [Bool.false_eq_true, false_and]
    | some T => simp only [SVal.canonB_iff (v := v) (T := T)]

theorem SVal.canonElemsB_iff {E : Ty} :
    ∀ {es : List SVal}, canonElemsB E es = true ↔ canonElems E es
  | [] => ⟨fun _ => trivial, fun _ => rfl⟩
  | v :: rest => by
    simp only [canonElemsB, canonElems, Bool.and_eq_true, SVal.canonB_iff (v := v),
      SVal.canonElemsB_iff (es := rest)]

theorem SVal.canonEntriesB_iff {V : Ty} :
    ∀ {es : List (Int × SVal)}, canonEntriesB V es = true ↔ canonEntries V es
  | [] => ⟨fun _ => trivial, fun _ => rfl⟩
  | (_, v) :: rest => by
    simp only [canonEntriesB, canonEntries, Bool.and_eq_true, SVal.canonB_iff (v := v),
      SVal.canonEntriesB_iff (es := rest)]

end

mutual

theorem SVal.tightB_iff : ∀ {v : SVal} {T : Ty}, v.tightB T = true ↔ v.tight T
  | SVal.struct fields, Ty.ref (RefTy.struct s) => by
    simp only [SVal.tightB, SVal.tight, SVal.tightFieldsB_iff]
  | SVal.array elems shadow _, Ty.ref (RefTy.array E) => by
    simp only [SVal.tightB, SVal.tight, Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff,
      Bool.not_eq_true', List.all_eq_true, SVal.isDfltB_iff, SVal.tightElemsB_iff, and_assoc]
    cases E.defaultOkS <;> cases E.isPrimitive <;>
      simp only [true_or, false_or, Bool.false_eq_true, Bool.true_eq_false, true_and,
        forall_const, false_implies]
  | SVal.array elems shadow _, Ty.ref (RefTy.fixed E _) => by
    simp only [SVal.tightB, SVal.tight, Bool.and_eq_true, List.isEmpty_iff,
      SVal.tightElemsB_iff]
  | SVal.map entries _, Ty.ref (RefTy.mapping K V) => by
    simp only [SVal.tightB, SVal.tight, Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff,
      Ty.numKeyB_eq, SVal.tightEntriesB_iff]
    cases K.numericKey <;>
      simp only [true_or, false_or, Bool.false_eq_true, true_and, forall_const, reduceCtorEq,
        false_implies]
  | SVal.prim _, _
  | SVal.struct _, Ty.prim _ | SVal.struct _, Ty.ref (.array _)
  | SVal.struct _, Ty.ref (.fixed _ _) | SVal.struct _, Ty.ref (.mapping _ _)
  | SVal.array .., Ty.prim _ | SVal.array .., Ty.ref (.struct _)
  | SVal.array .., Ty.ref (.mapping _ _)
  | SVal.map .., Ty.prim _ | SVal.map .., Ty.ref (.struct _)
  | SVal.map .., Ty.ref (.array _) | SVal.map .., Ty.ref (.fixed _ _) =>
    ⟨fun _ => trivial, fun _ => rfl⟩

theorem SVal.tightFieldsB_iff {s : Name} :
    ∀ {fs : List (Name × SVal)}, tightFieldsB s fs = true ↔ tightFields s fs
  | [] => ⟨fun _ => trivial, fun _ => rfl⟩
  | (n, v) :: rest => by
    simp only [tightFieldsB, tightFields, Bool.and_eq_true, SVal.tightFieldsB_iff (fs := rest)]
    cases lookupBy n (structDef s) with
    | none => simp only [true_and]
    | some T => simp only [SVal.tightB_iff (v := v) (T := T)]

theorem SVal.tightElemsB_iff {E : Ty} :
    ∀ {es : List SVal}, tightElemsB E es = true ↔ tightElems E es
  | [] => ⟨fun _ => trivial, fun _ => rfl⟩
  | v :: rest => by
    simp only [tightElemsB, tightElems, Bool.and_eq_true, SVal.tightB_iff (v := v),
      SVal.tightElemsB_iff (es := rest)]

theorem SVal.tightEntriesB_iff {V : Ty} :
    ∀ {es : List (Int × SVal)}, tightEntriesB V es = true ↔ tightEntries V es
  | [] => ⟨fun _ => trivial, fun _ => rfl⟩
  | (_, v) :: rest => by
    simp only [tightEntriesB, tightEntries, Bool.and_eq_true, SVal.tightB_iff (v := v),
      SVal.tightEntriesB_iff (es := rest)]

end

/-- A storage the test accepts holds the roots, canonical and tight. -/
theorem storageWtB_sound {st : List (Name × SVal)} (h : storageWtB C.vars st = true) :
    CanonStorage C st ∧ TightStorage C st := by
  simp only [storageWtB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hn, hall⟩ := h
  have hroot : ∀ r T, lookupBy r C.vars = some T →
      ∃ v, lookupBy r st = some v ∧ v.canonB T = true ∧ v.tightB T = true := by
    intro r T hT
    have := hall (r, T) (lookupBy_eq_some_mem hT)
    revert this
    cases lookupBy r st with
    | none => intro h; exact absurd h (by simp only [Bool.false_eq_true, not_false_eq_true])
    | some v =>
      intro h
      simp only [Bool.and_eq_true] at h
      exact ⟨v, rfl, h⟩
  refine ⟨⟨hn, fun r T hT => ?_⟩, fun r T v hT hv => ?_⟩
  · obtain ⟨v, hv, hc, -⟩ := hroot r T hT
    exact ⟨v, hv, SVal.canonB_iff.1 hc⟩
  · obtain ⟨w, hw, -, ht⟩ := hroot r T hT
    rw [hv] at hw
    cases hw
    exact SVal.tightB_iff.1 ht

/-- A storage that holds the roots, canonical and tight, passes the test,
when no root is declared twice. -/
theorem storageWtB_complete (hnd : nodupKeysB C.vars = true) {st : List (Name × SVal)}
    (hc : CanonStorage C st) (ht : TightStorage C st) : storageWtB C.vars st = true := by
  simp only [storageWtB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨hc.1, fun rT hm => ?_⟩
  have hl : lookupBy rT.1 C.vars = some rT.2 := lookupBy_eq_of_nodup hnd hm
  obtain ⟨v, hv, hcv⟩ := hc.2 _ _ hl
  rw [hv]
  simp only [Bool.and_eq_true]
  exact ⟨SVal.canonB_iff.2 hcv, SVal.tightB_iff.2 (ht _ _ _ hl hv)⟩

/-! ## The premise -/

/-- `wt(storage)`: the storage is one `C` can be in. -/
def Fml.wt (C : Contract) : Fml C := .defined (.wt C.vars .storage)

theorem holds_wt {σ : State} : holds σ (Fml.wt C) ↔ storageWtB C.vars σ.storage = true := by
  simp only [Fml.wt, holds, Tm.eval, Op1.eval, Op0.eval, pure, Except.pure, bind, Except.bind]
  cases storageWtB C.vars σ.storage with
  | true => exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩
  | false => exact ⟨fun ⟨_, h⟩ => (nomatch h), fun h => (nomatch h)⟩

/-- **`wt` is reachability**: for a contract whose types have well-formed
defaults all the way down, a storage passes `wt` exactly when a checked
program reaches it from the contract's initial state. -/
theorem wt_iff_reachable (hnd : nodupKeysB C.vars = true)
    (hdeep : C.vars.all (·.2.okDeep) = true) {st : List (Name × SVal)} :
    storageWtB C.vars st = true ↔ Reachable C st :=
  ⟨fun h => (reachable_iff hnd hdeep).2 (storageWtB_sound h),
    fun h => let ⟨hc, ht⟩ := (reachable_iff hnd hdeep).1 h; storageWtB_complete hnd hc ht⟩

/-- Every reachable storage is well-formed: the premise excludes no state
the contract can be in. -/
theorem wt_of_reachable (hnd : nodupKeysB C.vars = true)
    (hdeep : C.vars.all (·.2.okDeep) = true) {st : List (Name × SVal)} (h : Reachable C st) :
    storageWtB C.vars st = true :=
  (wt_iff_reachable hnd hdeep).2 h

/-- The contract's initial storage is well-formed (the empty program reaches
it), so the premise is satisfiable. -/
theorem initStorage_wt (hnd : nodupKeysB C.vars = true)
    (hdeep : C.vars.all (·.2.okDeep) = true) : holds C.initState (Fml.wt C) :=
  holds_wt.2 (wt_of_reachable hnd hdeep ⟨[], [], C.initState, rfl, rfl, rfl⟩)

/-! ## The obligations -/

/-- solkey's obligation for a function of body `P` and parameters `xs`
under the modality `m`: `∀xs. [ P ] true`, or
`∀xs. wt(storage) → ⟨ P ⟩ true`. -/
def Problem.fml (m : Modality) (xs : List (PrimTy × Var)) (P : Prog C) : Fml C :=
  match m with
  | .box => Fml.alls xs (.modal .box P .tt)
  | .diamond => Fml.alls xs (.imp (Fml.wt C) (.modal .diamond P .tt))

/-- The parameters an obligation binds, its modality and its program, read
back off the formula: what `Problem.text` prints. -/
def Problem.parts : Fml C → Option (List (PrimTy × Var) × Modality × Prog C)
  | .all x p φ => (Problem.parts φ).map fun (xs, r) => ((p, x) :: xs, r)
  | .modal .box P .tt => some ([], .box, P)
  | .imp (.defined (.app1 (.wt _) (.app0 .storage))) (.modal .diamond P .tt) =>
    some ([], .diamond, P)
  | _ => none

/-- How many storage writes the context's updates hold. -/
def Derive.storageWrites (Γ : List (Hyp C)) : Nat :=
  Γ.foldl (fun n h => match h with
    | .upd _ U => n + (U.filter fun | .storage _ => true | _ => false).length
    | _ => n) 0

/-- `#solkey_scan`'s view of `⊢ φ`: how many leaves `sol_prove`'s walk
leaves, closed by `synClose` or (`walk`) not, and the most storage writes
in one leaf's context; `none` past `Derive.budget`. -/
def Derive.scanLeaves (walk : Bool) (φ : Fml C) : Option (Nat × Nat) :=
  (Derive.residue Derive.budget (if walk then fun _ _ => false else Derive.synClose)
    Derive.budget [] φ).map fun (ls, _) =>
      (ls.length, ls.foldl (fun m l => max m (Derive.storageWrites l.1)) 0)

/-- KeY's sort of a parameter, as solkey declares it: `int` for every
integer type. -/
def PrimTy.keySort : PrimTy → String
  | .bool => "bool"
  | .uint | .int => "int"

/-- The obligation in solkey's problem syntax (`--print-problem`): the
parameters as program variables, the call under the modality, and the
premise `wt(storage)` where solkey has none (its storage is well-formed by
construction). -/
def Problem.text (contract fn : String) (φ : Fml C) : String :=
  match Problem.parts φ with
  | none => "(not an obligation)"
  | some (xs, m, _) =>
    let vars := if xs.isEmpty then "" else
      "\\programVariables {\n" ++
        String.join (xs.map fun (p, x) => s!"    {p.keySort} {x};\n") ++ "}\n\n"
    let call := s!"{fn}({", ".intercalate (xs.map fun (_, x) => toString x)})@{contract};"
    let body := match m with
      | .box => s!"\\[\{ {call} }\\](true)"
      | .diamond => s!"wt(storage) -> \\<\{ {call} }\\>(true)"
    vars ++ "\\problem {\n    " ++ body ++ "\n}"

end Solidity
