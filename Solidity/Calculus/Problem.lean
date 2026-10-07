import Solidity.Typing.CanonTest
import Solidity.Calculus.Derive

/-!
# Obligations, as solkey states them

solkey's `SolidityProblemSynthesizer` makes one obligation per function of a
contract with no specification: `\<{ f(x̄)@C; }\>(true)`, or
`\[{ f(x̄)@C; }\](true)` for a function tagged `@custom:key box`, with no
premise, the parameters `x̄` program variables of sort `int` or `bool`, so
free: the obligation is proved for every value of them.  Here the
parameters are `∀` binders over their type's 256-bit range (`Fml.all`): a
`uint` ranges over `[0, 2²⁵⁶)` and an `int` over `[-2²⁵⁵, 2²⁵⁵)`, where
KeY's `int` is unbounded.  The width is not bound: an `int8` parameter
ranges over `[-2²⁵⁵, 2²⁵⁵)` too, which is neither solc's `[-128, 128)` nor
KeY's every integer, because `solc_problems` keeps only the parameter's
`PrimTy`; the obligation is then stronger than Solidity's, over more
inputs.

**The premise is the model's own.**  solkey's `storage` is a free `Struct`
term whose integer fields are unbounded, and no solidity taclet mentions a
well-formed heap; here the storage is a state of the interpreter, any
list of roots.  `wt(storage)` (`Fml.wt`) assumes most of what Solidity
guarantees of a deployed contract's storage: every root there, in order,
canonical and tight, which is exactly reachable (`shape_iff_reachable`),
and every word in its type's range (`storageWtB`, `wt_iff_reachable`).
It does not bound a dynamic array's length, which solc keeps at most
`2^64` (`push` panics, 0x41, on an array already that long), and the
model's `push` (`pushOn`) never panics.  The delta cuts both ways.  A
diamond that reads a length through checked arithmetic can fail from a
storage solc cannot reach, so it is stronger than Solidity's and may not be
derivable (`storagePushReadBack`).  And a diamond over a `push` with no
bound on the length before it asserts normal termination where solc
panics, from a storage of length `2^64` that `wt` accepts: three derived
ones hold only up to this delta (`storagePushLengthPositive`,
`storagePopUnknownLength`, `arrayOfMappingsIndex`; `docs/solc-alignment.md`,
"Remaining deltas").  They are solkey's, whose `int` is unbounded.
Otherwise a derived obligation is Solidity's, not solkey's: where solkey's
free storage can break an `assert` (a `uint` field below zero), the premise
excludes it, so the Lean theorem need not imply solkey's obligation.

* **Box**: `∀x̄. wt(storage) → [ f(x̄); ] true`.  A failed `assert` panics,
  and no modality holds of a panic (`Modality.afterRun`), so this is KeY's
  `assertSimple` "Violated" obligation, with no cut: a failed `require`
  reverts, which the box accepts, as in KeY.  Without the premise the box
  would be false of functions Solidity runs safely: a `uint[3]` root
  stored as a mapping keeps a write through `delete`, so an `assert` that
  the element is reset fails.
* **Diamond**: `∀x̄. wt(storage) → ⟨ f(x̄); ⟩ true`.  The diamond does not
  hold of every storage: a write into a root that is not there is stuck, and
  `total + 0` reverts on a `uint` root holding `-1`.

**Why one atomic term.**  `wt` is a symbol of the term language, `Op1.wt`,
read by the interpreter as a test of the storage it is given, and stated
as `defined(wt(storage))`: it returns exactly on a well-formed storage.  An
expanded layout (`∀` over every root and member) would make every leaf a
quantified formula the closer has to instantiate; one atom costs one
constructor of `Op1` and nothing in `Fml`.  The closer sets it aside as a
formula (`Derive.dropWt`, only a weakening) and reads it as the layout the
storage holds (`Derive.topWt`, `Decide.LayoutOk`): a read at a path the
layout types returns.

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

/-! ## The shape test -/

/-- A storage the shape test accepts holds the roots, canonical and tight. -/
theorem storageShapeB_sound {st : List (Name × SVal)} (h : storageShapeB C.vars st = true) :
    CanonStorage C st ∧ TightStorage C st := by
  simp only [storageShapeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
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

/-- A storage that holds the roots, canonical and tight, passes the shape
test, when no root is declared twice. -/
theorem storageShapeB_complete (hnd : nodupKeysB C.vars = true) {st : List (Name × SVal)}
    (hc : CanonStorage C st) (ht : TightStorage C st) : storageShapeB C.vars st = true := by
  simp only [storageShapeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
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

/-- **The shape is reachability**: for a contract whose types have
well-formed defaults all the way down, a storage passes the shape test
exactly when a checked program reaches it from the contract's initial
state. -/
theorem shape_iff_reachable (hnd : nodupKeysB C.vars = true)
    (hdeep : C.vars.all (·.2.okDeep) = true) {st : List (Name × SVal)} :
    storageShapeB C.vars st = true ↔ Reachable C st :=
  ⟨fun h => (reachable_iff hnd hdeep).2 (storageShapeB_sound h),
    fun h => let ⟨hc, ht⟩ := (reachable_iff hnd hdeep).1 h; storageShapeB_complete hnd hc ht⟩

/-- **`wt` is reachability with words in range**: a storage is well-formed
exactly when a program reaches it and its words fit their types, which a
program solc compiles keeps (`Semantics/WellFormed.lean`). -/
theorem wt_iff_reachable (hnd : nodupKeysB C.vars = true)
    (hdeep : C.vars.all (·.2.okDeep) = true) {st : List (Name × SVal)} :
    storageWtB C.vars st = true ↔ Reachable C st ∧ storageWordsB C.vars st = true := by
  rw [storageWtB, Bool.and_eq_true, shape_iff_reachable hnd hdeep]

/-- A fresh contract's root holds its type's default. -/
theorem lookupBy_initStorage_vars (r : Name) :
    lookupBy r C.initStorage = (lookupBy r C.vars).map defaultForTy := by
  simp only [Contract.initStorage]
  induction C.vars with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨g, T⟩ := x
    simp only [List.map, lookupBy]
    split
    · rfl
    · exact ih

/-- The words of a fresh contract fit: every root holds its default. -/
theorem storageWordsB_init (hnd : nodupKeysB C.vars = true) :
    storageWordsB C.vars C.initStorage = true := by
  simp only [storageWordsB, List.all_eq_true]
  intro rT hm
  have hl : lookupBy rT.1 C.vars = some rT.2 := lookupBy_eq_of_nodup hnd hm
  rw [lookupBy_initStorage_vars, hl]
  exact SVal.wordsB_default rT.2

/-- The contract's initial storage is well-formed (the empty program reaches
it, and its words are defaults), so the premise is satisfiable. -/
theorem initStorage_wt (hnd : nodupKeysB C.vars = true)
    (hdeep : C.vars.all (·.2.okDeep) = true) : holds C.initState (Fml.wt C) :=
  holds_wt.2 ((wt_iff_reachable hnd hdeep).2
    ⟨⟨[], [], C.initState, rfl, rfl, rfl⟩, storageWordsB_init hnd⟩)

/-! ## The obligations -/

/-- solkey's obligation for a function of body `P` and parameters `xs`
under the modality `m`: `∀xs. wt(storage) → [ P ] true`, or the same with
`⟨ P ⟩`. -/
def Problem.fml (m : Modality) (xs : List (PrimTy × Var)) (P : Prog C) : Fml C :=
  Fml.alls xs (.imp (Fml.wt C) (.modal m P .tt))

/-- solkey's deployment update,
`{storage := mtSt ‖ net := storeSt(mtSt, at(msgSender), msgValue) ‖ selfBalance := msgValue}`:
the empty storage, a ledger holding the deployer's payment, and the value
sent as the contract's funds (`Contract.deployState`). -/
def Problem.deployUpd (C : Contract) : Upd C :=
  [.storage (.mtSt C.vars), .netMt (.env .msgSender) (.env .msgValue), .setBalance (.env .msgValue)]

/-- solkey's obligation for a constructor, of parameters `xs`, deployed by
`P` (`constructor(x̄);`): `∀xs. {deployUpd} ⟨ P ⟩ true`, or the box.  No
`wt(storage)` premise: the update discards the storage, and the empty one
is well formed (`initStorage_wt`). -/
def Problem.ctorFml (m : Modality) (xs : List (PrimTy × Var)) (P : Prog C) : Fml C :=
  Fml.alls xs (.upd m (Problem.deployUpd C) (.modal m P .tt))

/-- A constructor's obligation with no specification, `Problem.ctorFml` of
the contract's constructor: its parameters bound, the program
`constructor(x̄);` elaborated with them in scope.  solkey states this form
only where neither the contract nor the constructor is specified, and with
`{storage := mtSt || net := mtSt}`; Lean with `Problem.deployUpd`, its
specified problem's update (`docs/solkey-feedback.md`).  A constructor
marked `skip`, or specified, is refused. -/
def Problem.ctor [FreshNames] (C : Contract) (m : Modality) : Except String (Fml C) := do
  let some d := C.ctor | throw "the contract declares no constructor: an implicit one has no obligation"
  if d.spec.skip then throw "constructor is marked `skip`: it has no obligation"
  -- solkey states the unspecified form only where neither the contract
  -- nor the constructor is specified
  unless C.inv.isEmpty && d.spec.requires.isEmpty && d.spec.ensures.isEmpty &&
      d.spec.assignable.isNone do
    throw "constructor: the contract or its constructor is specified: its obligation is `spec!{constructor}`"
  let ps ← d.params.mapM fun (n, T) => match T with
    | .prim p => pure (n, p)
    | _ => throw s!"constructor: the parameter {n} has a reference type"
  let call : List RawStmt := [.call (.name "constructor") (ps.map fun (n, _) => RawExpr.name n)]
  let P ← ((elabStmts C call).run { funs := C.funs }).run' (ps.map fun (n, p) => (n, LocalTy.val p), 1)
  pure (Problem.ctorFml m (ps.map fun (n, p) => (p, Var.ofName n)) P)

/-- `problem[C]{constructor}`: `Problem.ctor C .diamond`, the unspecified
constructor obligation, elaborated (`constructor` is a keyword,
not an `ident`). -/
syntax (name := problemCtor) "problem[" term "]{ " &"constructor" " }" : term

/-- `problem!{constructor}`: `problem[C]{constructor}` for the file's
`InContract` contract. -/
syntax (name := problemCtorBang) "problem!{ " &"constructor" " }" : term

open Lean Elab Term Meta in
elab_rules (kind := problemCtor) : term
  | `(problem[ $c ]{ constructor }) =>
    elabAgainst c fun q => `((Problem.ctor ($c) Modality.diamond).map (Fml.quote $q))

macro_rules (kind := problemCtorBang)
  | `(problem!{ constructor }) => `(problem[InContract.contract]{ constructor })

/-- What a binding of a constructor's parameters keeps of a deployment's
start: the empty storage, the payment booked, the value as the funds. -/
private def DeployStart (C : Contract) (σ : State) : Prop :=
  σ.storage = C.initStorage ∧ σ.net = [(σ.tx.msgSender, σ.tx.msgValue)] ∧
    σ.selfBalance = σ.tx.msgValue

/-- The deployment update leaves a deployment's start as it is. -/
private theorem deployUpd_apply {σ : State} (h : DeployStart C σ) :
    (Problem.deployUpd C).apply σ = .ok σ := by
  obtain ⟨hs, hn, hb⟩ := h
  cases σ
  simp only at hs hn hb
  subst hs hn hb
  rfl

/-- **A derived constructor obligation holds of the deployment**: from
`deployState tx`, the parameters bound to any values of their types
(`Binds`), the program runs under `m`, and does not panic. -/
theorem Problem.deploy_of_valid {m : Modality} {xs : List (PrimTy × Var)} {P : Prog C}
    (h : Valid (Problem.ctorFml m xs P)) (tx : TxEnv) {σ : State}
    (hb : Binds xs (C.deployState tx) σ) : m.afterRun (fun _ => True) (Prog.run σ P) := by
  have hσ : holds σ (.upd m (Problem.deployUpd C) (.modal m P .tt)) := holds_alls.1 (h _) σ hb
  obtain ⟨_, hvs⟩ := hb
  have hd : DeployStart C σ :=
    bindData_induct (P := DeployStart C) (fun _ _ _ hp => hp) ⟨rfl, rfl, rfl⟩ hvs
  simp only [holds, deployUpd_apply hd, Modality.after] at hσ
  exact hσ

/-- With no parameters, `Contract.deploy` itself: a constructor that is not
`payable` is sent no value. -/
theorem Problem.deploy_of_valid_nil {m : Modality} {P : Prog C}
    (h : Valid (Problem.ctorFml m [] P)) (tx : TxEnv)
    (hpay : (C.ctor.map (·.payable)).getD false = true ∨ tx.msgValue = 0) :
    m.afterRun (fun _ => True) (C.deploy P tx) := by
  have hrun : C.deploy P tx = Prog.run (C.deployState tx) P := by
    rcases hpay with hp | hv
    · simp only [Contract.deploy, hp, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
    · simp only [Contract.deploy, hv, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, if_false]
  rw [hrun]
  exact Problem.deploy_of_valid h tx ⟨[], rfl⟩

/-- The parameters an obligation binds, whether it is a deployment, its
modality and its program, read back off the formula: what `Problem.text`
prints. -/
def Problem.parts : Fml C → Option (List (PrimTy × Var) × Bool × Modality × Prog C)
  | .all x p φ => (Problem.parts φ).map fun (xs, r) => ((p, x) :: xs, r)
  | .imp (.defined (.app1 (.wt _) (.app0 .storage))) (.modal m P .tt) => some ([], false, m, P)
  | .upd m [.storage (.app0 (.mtSt _)), .netMt (.env .msgSender) (.env .msgValue),
      .setBalance (.env .msgValue)] (.modal m' P .tt) =>
    if m = m' then some ([], true, m, P) else none
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
premise `wt(storage)`, which solkey's has not.  A deployment is printed
with its update, solkey's specified one: solkey's unspecified constructor
problem writes `{storage := mtSt || net := mtSt}`, an empty ledger and free
funds, where the interpreter's deployment books the payment
(`Contract.deployState`). -/
def Problem.text (contract fn : String) (φ : Fml C) : String :=
  match Problem.parts φ with
  | none => "(not an obligation)"
  | some (xs, deploy, m, _) =>
    let vars := if xs.isEmpty then "" else
      "\\programVariables {\n" ++
        String.join (xs.map fun (p, x) => s!"    {p.keySort} {x};\n") ++ "}\n\n"
    let call := s!"{fn}({", ".intercalate (xs.map fun (_, x) => toString x)})@{contract};"
    let pre := if deploy then
      "{storage := mtSt || net := storeSt(mtSt, at(msgSender), msgValue) || selfBalance := msgValue} "
      else "wt(storage) -> "
    let body := match m with
      | .box => s!"{pre}\\[\{ {call} }\\](true)"
      | .diamond => s!"{pre}\\<\{ {call} }\\>(true)"
    vars ++ "\\problem {\n    " ++ body ++ "\n}"

end Solidity
