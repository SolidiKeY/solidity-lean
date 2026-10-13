import Solidity.Typing.CanonTest
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.NotationResolve
import Solidity.Calculus.Quote
import Solidity.Calculus.Logic

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
KeY's every integer, because `solc_scoped_problems` keeps only the
parameter's `PrimTy`; the obligation is then stronger than Solidity's, over
more inputs.

**The premise is the model's own.**  solkey's `storage` is a free `Struct`
term whose integer fields are unbounded, and no solidity taclet mentions a
well-formed heap; here the storage is a typed storage of the interpreter,
its roots at their types, its words in range.  `wt(storage)` (`Fml.wt`)
assumes most of what Solidity guarantees of a deployed contract's storage:
every root canonical and tight, which is exactly reachable
(`shape_iff_reachable`, for every key and slot in range), and every mapping
key in its key type's range (`Storage.wtB`, `wt_iff_reachable`; the term
runs that test, `Semantics/StorageWt.lean`).  Reachable is by
the typed interpreter (`Reachable`).
It does not bound a dynamic array's length, which solc keeps at most
`2^64` (`push` panics, 0x41, on an array already that long), and the
model's `push` (`Storage.push`) never panics (at `2^256 - 1` elements it is out
of gas, which both modalities accept).  A diamond that reads a length back
after a push (`storagePushReadBack`) is valid all the same, the length then
at least `1`, though not derived.  And a diamond over a `push` with no
bound on the length before it asserts normal termination where solc
panics, from a storage of length `2^64` that `wt` accepts: three derived
ones hold only up to this delta (`storagePushLengthPositive`,
`storagePopUnknownLength`, `arrayOfMappingsIndex`; `docs/solc-alignment.md`,
"Remaining deltas").  They are solkey's, whose `int` is unbounded.
Otherwise a derived obligation is Solidity's, not solkey's: where solkey's
free storage can break an `assert` (a `uint` field below zero), the premise
excludes it, so the Lean theorem need not imply solkey's obligation.

* **Box**: `∀x̄. wt(storage) → [ f(x̄); ] true`.  A failed `assert` panics,
  and no modality holds of a panic (`Modality.afterRunTR`), so this is KeY's
  `assertSimple` "Violated" obligation, with no cut: a failed `require`
  reverts, which the box accepts, as in KeY.  Without the premise the box
  would be false of functions Solidity runs safely: a `uint[3]` root
  stored as a mapping keeps a write through `delete`, so an `assert` that
  the element is reset fails.
* **Diamond**: `∀x̄. wt(storage) → ⟨ f(x̄); ⟩ true`.  The diamond does not
  hold of every storage: `total + 0` reverts on a `uint` root holding `-1`.

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

open Semantics (structDef lookupBy setBy nodupKeysB)

variable {C : Contract}

/-! ## The premise -/

/-- `wt(storage)`: the storage is one `C` can be in. -/
def Fml.wt (C : Contract) {Γ : Ctx} : Fml C Γ :=
  .defined (.app1 .wt (.app0 .storage))

/-- `wt(storage)` holds in a typed state exactly when its storage passes the
test (`Storage.wtB`). -/
theorem holds_wt {Γ : Ctx} {σ : State C Γ} :
    holds σ (Fml.wt C) ↔ σ.storage.wtB = true := by
  rw [Fml.wt, holds_defined]
  show (Storage.wtT σ.storage) ≠ none ↔ _
  unfold Storage.wtT
  cases σ.storage.wtB with
  | true => exact ⟨fun _ => rfl, fun _ h => nomatch h⟩
  | false => exact ⟨fun h => absurd rfl h, fun h => nomatch h⟩

/-- A reachable storage passes the shape test. -/
theorem shape_of_reachable (hdeep : C.vars.all (·.2.okDeep) = true) {st : Storage C}
    (h : Reachable C st) : st.shapeB = true :=
  (Storage.shapeB_iff st).2 (reachable_shape hdeep h)

/-- **The shape is reachability**: for a contract whose types have
well-formed defaults all the way down, a storage whose keys and slots are in
range (`SVal.Fits`) passes the shape test exactly when a program reaches it
from the contract's initial state. -/
theorem shape_iff_reachable (hnd : nodupKeysB C.vars = true)
    (hdeep : C.vars.all (·.2.okDeep) = true) {st : Storage C} (hf : st.Fits) :
    st.shapeB = true ↔ Reachable C st := by
  rw [Storage.shapeB_iff, reachable_iff hnd hdeep hf]

/-- **`wt` is reachability**: a storage whose keys and slots are in range is
well-formed exactly when a program reaches it.  Its words are in range by
their types; its keys, by `Fits`. -/
theorem wt_iff_reachable (hnd : nodupKeysB C.vars = true)
    (hdeep : C.vars.all (·.2.okDeep) = true) {st : Storage C} (hf : st.Fits) :
    st.wtB = true ↔ Reachable C st := by
  rw [Storage.wtB, Storage.keysB_of_fits hf, Bool.and_true, shape_iff_reachable hnd hdeep hf]

/-- A reachable storage is well-formed: its keys are in range
(`reachable_bnd`). -/
theorem wt_of_reachable (hdeep : C.vars.all (·.2.okDeep) = true) {st : Storage C}
    (h : Reachable C st) : st.wtB = true := by
  rw [Storage.wtB, shape_of_reachable hdeep h, Storage.keysB_of_bnd (reachable_bnd h)]
  rfl

/-- The contract's initial storage is well-formed (the empty program reaches
it), so the premise is satisfiable. -/
theorem initStorage_wt (hdeep : C.vars.all (·.2.okDeep) = true) :
    holds (State.init C) (Fml.wt C) :=
  holds_wt.2 (wt_of_reachable hdeep
    ⟨[], .nil, ⟨State.init C, List.prefix_refl _⟩, Prog.run_nil _, rfl⟩)

/-! ## The obligations

Scoped (`docs/intrinsic.md`, M6b, W8): the program is read in the context
of the parameters, `paramsN xs` (the first parameter outermost, so its
position the deepest), which `∀` binds over each type's range
(`Fml.closeN`). -/

/-- The parameters `xs` as a named context, the first parameter the
outermost (deepest) local. -/
def paramsN (xs : List (PrimTy × Var)) : NCtx := xs.reverse.map fun (p, x) => (x, .val p)

/-- solkey's obligation for a function of body `P` and parameters `xs`
under the modality `m`, `P` read in their context: `∀xs. wt(storage) → [ P ]
true`, or the same with `⟨ P ⟩`. -/
def Problem.fml (m : Modality) (xs : List (PrimTy × Var)) {Γ' : Ctx}
    (P : Prog C (paramsN xs).ctx Γ') : Fml C [] :=
  Fml.closeN true (paramsN xs) (.imp (Fml.wt C) (.modal m P .nil .tt))

/-- solkey's deployment update,
`{storage := mtSt ‖ net := storeSt(mtSt, at(msgSender), msgValue) ‖ selfBalance := msgValue}`:
the empty storage, a ledger holding the deployer's payment, and the value
sent as the contract's funds (`State.deploy`). -/
def Problem.deployUpd (C : Contract) {Γ : Ctx} : Upd C Γ Γ :=
  ((Upd.nil.snoc (.storage (.app0 .mtSt))).snoc
    (.netMt (.app0 (.env .msgSender)) (.app0 (.env .msgValue)))).snoc
    (.setBalance (.app0 (.env .msgValue)))

/-- solkey's obligation for a constructor, of parameters `xs`, deployed by
`P` (`constructor(x̄);`): `∀xs. {deployUpd} ⟨ P ⟩ true`, or the box.  No
`wt(storage)` premise: the update discards the storage, and the empty one
is well formed (`initStorage_wt`). -/
def Problem.ctorFml (m : Modality) (xs : List (PrimTy × Var)) {Γ' : Ctx}
    (P : Prog C (paramsN xs).ctx Γ') : Fml C [] :=
  Fml.closeN true (paramsN xs) (.upd m (Problem.deployUpd C) (.modal m P .nil .tt))

/-- A constructor's obligation with no specification, `Problem.ctorFml` of
the contract's constructor: its parameters bound, the program
`constructor(x̄);` elaborated with them in scope.  solkey states this form
only where neither the contract nor the constructor is specified, and with
`{storage := mtSt || net := mtSt}`; Lean with `Problem.deployUpd`, its
specified problem's update (`docs/solkey-feedback.md`).  A constructor
marked `skip`, or specified, is refused. -/
def Problem.ctor [FreshNames] (C : Contract) (m : Modality) : Except String (Fml C []) := do
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
  let xs := ps.map fun (n, p) => (p, Var.ofName n)
  let call : List RawStmt := [.call (.name "constructor") (ps.map fun (n, _) => RawExpr.name n)]
  let Γ : ECtx := ps.reverse.map fun (n, p) => (n, LocalTy.val p)
  let P ← ((elabStmtsP C call).run { funs := C.funs }).run' (Γ, 1)
  let ⟨_, P⟩ ← SProg.chain (paramsN xs).names (paramsN xs).ctx P
  pure (Problem.ctorFml m xs P)

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

/-- Whether a term is `wt(storage)`. -/
def Problem.isWt {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .app1 .wt (.app0 .storage) => true
  | _, _ => false

/-- Whether an update is the deployment's, `Problem.deployUpd`'s shape. -/
def Problem.isDeploy {Γ Δ : Ctx} : Upd C Γ Δ → Bool
  | .snoc (.snoc (.snoc .nil (.storage (.app0 .mtSt)))
      (.netMt (.app0 (.env .msgSender)) (.app0 (.env .msgValue))))
      (.setBalance (.app0 (.env .msgValue))) => true
  | _ => false

/-- The parameters an obligation binds, whether it is a deployment, and its
modality, read back off the formula: what `Problem.text` prints. -/
def Problem.parts : {Γ : Ctx} → Fml C Γ → Option (List (PrimTy × Var) × Bool × Modality)
  | _, .all x p φ => (Problem.parts φ).map fun (xs, r) => ((p, x) :: xs, r)
  | _, .imp (.defined t) (.modal m _ _ .tt) => if Problem.isWt t then some ([], false, m) else none
  | _, .upd m U (.modal m' _ _ .tt) =>
    if Problem.isDeploy U && m = m' then some ([], true, m) else none
  | _, _ => none

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
(`State.deploy`). -/
def Problem.text (contract fn : String) (φ : Fml C []) : String :=
  match Problem.parts φ with
  | none => "(not an obligation)"
  | some (xs, deploy, m) =>
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
