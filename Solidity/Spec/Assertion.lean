import Solidity.Semantics

/-!
# SolSpec: the assertion layer

The Lean backend of the NatSpec specification language (see
`docs/spec-language.md`). Three things live here:

1. **Assertion vocabulary** — total readers that turn a
   `Semantics.State` into the `Int`/`Bool`/`Prop` values a specification
   talks about (`intAt`, `boolAt`, `lenAt`, `localInt`, …). They are
   *total*: a read that the interpreter would reject (absent root, index
   out of bounds, shape mismatch) yields the type's zero value. That
   keeps assertions plain propositions rather than partial computations;
   the front-end compensates by emitting a **well-formedness** conjunct
   (`0 ≤ i < a.length`) for every index in a *proved* clause, which is
   the Dafny discipline.

2. **Verification conditions** — `vc` walks an *annotated block*
   (`Ann`: a Solidity statement, a ghost `assert`, or a ghost `assume`)
   through the executable semantics of `Semantics.execStmt`, threading
   the state. Which halts are acceptable is a parameter: `totalVC`
   accepts none (the `⟨body⟩ post` reading — the function must not
   revert), `partialVC` accepts `revert` (the `[body] post` reading).
   `revertsVC` is the dual used by `@custom:reverts_when`.

3. **Range predicates** — `inRange lo hi v`, how the front-end states
   what a `uintN`/`intN` declaration means. The official interpreter
   (`Semantics.lean`) computes over `Int` with solc's checked arithmetic
   at 256 bits (`Semantics.checkArith`: an out-of-range result
   *reverts*), so a 256-bit overflow is a `revert` to every obligation
   here — `partialVC` accepts it, `totalVC` fails on it. Narrower widths
   are not modelled by the interpreter; for them a specification gets
   bounded arithmetic by *assuming* the bounds of every input and
   *proving* the bounds of every result, and an overflow shows up as a
   failed range obligation. See `docs/spec-language.md` § "Arithmetic".

Nothing here is axiomatic: every definition is executable and every
obligation is discharged against `Semantics.execStmt`, the same
interpreter `sol_wp` and the EVM correctness proof use.
-/

namespace Solidity
namespace Spec

open Semantics

/-! ## Reading a state from an assertion

Specifications are written over storage *paths* — a root name plus a
list of `Seg`ments (a struct field, or an array index / mapping key).
That is exactly the address `Semantics.State.findStorage` takes, so an
assertion reader is a thin total wrapper around it. -/

/-- The storage value at a path, or `none` where the interpreter would
halt (unknown root, index out of bounds, shape mismatch). -/
def svalAt (s : State) (root : Name) (segs : List Seg) : Option SVal :=
  match s.findStorage root segs with
  | .ok v => some v
  | .error _ => none

/-- Integer read of a storage path; `0` when the path does not name an
integer. -/
def intAt (s : State) (root : Name) (segs : List Seg) : Int :=
  match svalAt s root segs with
  | some (SVal.int v) => v
  | _ => 0

/-- Boolean read of a storage path; `false` when the path does not name
a boolean. -/
def boolAt (s : State) (root : Name) (segs : List Seg) : Bool :=
  match svalAt s root segs with
  | some (SVal.bool b) => b
  | _ => false

/-- `a.length` of the array at a storage path; `0` when the path does
not name an array. Mirrors the `Seg.field "length"` arm of
`SVal.find`, but as an `Int` an assertion can do arithmetic with. -/
def lenAt (s : State) (root : Name) (segs : List Seg) : Int :=
  match svalAt s root segs with
  | some (SVal.array elems) => (elems.length : Int)
  | _ => 0

/-- Does a storage path hold an integer? The front-end conjoins this
into the well-formedness of a clause that reads through a mapping or an
array whose shape the specification depends on. -/
def isIntAt (s : State) (root : Name) (segs : List Seg) : Bool :=
  match svalAt s root segs with
  | some (SVal.int _) => true
  | _ => false

/-- Integer read of a stack local (a parameter, a `uint x = …`
declaration, or the synthesized `return` variable); `0` when the name is
unbound or does not hold an integer. -/
def localInt (s : State) (name : Name) : Int :=
  match s.getEnv name with
  | .ok (Binding.val (Value.int v)) => v
  | _ => 0

/-- Boolean read of a stack local; `false` when unbound or non-boolean. -/
def localBool (s : State) (name : Name) : Bool :=
  match s.getEnv name with
  | .ok (Binding.val (Value.bool b)) => b
  | _ => false

/-- The `net` payment ledger at an address (`a.transfer(v)` books
`net(a) := net(a) - v`). -/
def netAt (s : State) (addr : Int) : Int := s.getNet addr

/-! ## Reading through the interpreter

The readers above address storage by *path*, which is what the
TypeScript front-end emits: it knows every declaration's type and
deliberately avoids the fixed name tables of `SoliditySyntax`. The
in-Lean surface syntax (`Spec/Syntax.lean`) cannot do that — a
`solspec!{…}` specification is written in the same vocabulary as the
program — so it reads through the interpreter instead: a specification
atom is a `WrappedExpr`, evaluated by `Semantics.evalValue` in the state
being talked about.

The two agree wherever both apply; `valInt`/`valBool` are the more
general pair (any expression the program language can write), `intAt`
and friends the more direct one (a path, with no evaluation to unfold).

Evaluation is total here in the same sense as above: a read the
interpreter rejects — an index out of bounds, a shape mismatch, a name
the state does not bind — yields the type's zero. Note the one wrinkle
this inherits: `evalValue` can *mutate* (`i++` is an expression), so a
specification that increments reads the pre-increment value and drops
the effect. Do not write one. -/

/-- Integer value of a program expression in a state; `0` when
evaluation does not produce an integer. -/
def valInt (s : State) (e : WrappedExpr) : Int :=
  match Semantics.evalValue s e with
  | .ok (_, Value.int v) => v
  | _ => 0

/-- Boolean value of a program expression in a state; `false` when
evaluation does not produce a boolean. -/
def valBool (s : State) (e : WrappedExpr) : Bool :=
  match Semantics.evalValue s e with
  | .ok (_, Value.bool b) => b
  | _ => false

/-! ## Frames

`@custom:modifies a, b` says every *other* storage root keeps its entry
value. The front-end knows the contract's declarations and can emit the
complement directly; the in-Lean syntax cannot, so it states the same
thing relative to the entry state's own storage list — which is a
literal, so it reduces. -/

/-- Every entry of `entries` is either a permitted root or unchanged in
`s`. Written by recursion rather than with `∀ x ∈ …` so that a literal
storage list unfolds into a plain conjunction. -/
def frameEntries (roots : List Name) (s : State) :
    List (Name × SVal) -> Prop
  | [] => True
  | (r, v) :: rest =>
      (r ∈ roots ∨ Semantics.lookupBy r s.storage = some v) ∧
        frameEntries roots s rest

/-- The frame condition: going from `s0` to `s`, only the named storage
roots changed. -/
def modifiesOnly (roots : List Name) (s0 s : State) : Prop :=
  frameEntries roots s s0.storage

/-! ## Range predicates

`uintN`/`intN` bounds. The front-end emits the two endpoints as decimal
numerals rather than `2 ^ n` terms, so `omega` sees plain linear
arithmetic over `Int`. -/

/-- `lo ≤ v ∧ v ≤ hi`: the meaning of a bounded Solidity integer type.
Assumed of every input, proved of every result. -/
def inRange (lo hi v : Int) : Prop := lo ≤ v ∧ v ≤ hi

theorem inRange_def {lo hi v : Int} : inRange lo hi v ↔ (lo ≤ v ∧ v ≤ hi) :=
  Iff.rfl

/-- Bounded quantification, the shape `forall`/`exists` over an index
range compile to. Kept as a definition so the tactic can recognize it. -/
def forallIn (lo hi : Int) (P : Int -> Prop) : Prop :=
  ∀ i : Int, lo ≤ i -> i < hi -> P i

/-- Existential over an index range (`exists` in a specification). -/
def existsIn (lo hi : Int) (P : Int -> Prop) : Prop :=
  ∃ i : Int, lo ≤ i ∧ i < hi ∧ P i

/-! ## Annotated blocks and their verification conditions -/

/-- A step of an annotated program: an ordinary Solidity statement, a
ghost assertion to *prove* at this point, or a ghost assumption to
*carry* from this point on. Ghost steps have no run-time effect — they
are the specification-language analogues of Dafny's `assert` and
`assume`. -/
inductive Ann where
  | stmt (st : Stmt)
  | assert (φ : State -> Prop)
  | assume (φ : State -> Prop)

/-- Verification condition of an annotated block.

`haltOk` decides which halts the specification tolerates:

* `fun _ => False` — total correctness. Neither `revert` nor `stuck` is
  acceptable: the function must run to completion and establish `Q`.
  This is the diamond reading, and the default for a specified function.
* `fun h => h = Halt.revert` — partial correctness (`@custom:partial`).
  A revert discharges the obligation vacuously, exactly as a box
  judgment does; `stuck` (a program outside the modelled fragment) never
  discharges anything.

The `stmt` arm is *the* place the executable semantics enters: `vc` is
weakest-precondition-shaped but computed forward, because
`Semantics.execStmt` is a function. -/
def vc (haltOk : Halt -> Prop) : State -> List Ann -> (State -> Prop) -> Prop
  | s, [], Q => Q s
  | s, Ann.assert φ :: rest, Q => φ s ∧ vc haltOk s rest Q
  | s, Ann.assume φ :: rest, Q => φ s -> vc haltOk s rest Q
  | s, Ann.stmt st :: rest, Q =>
      match Semantics.execStmt s st with
      | .ok s' => vc haltOk s' rest Q
      | .error h => haltOk h

/-- The continuation of `vc` after one statement, as a function of the
interpreter's verdict. Factoring it out is what lets the tactic peel a
step with a *total* rewrite (`vc_stmt_eval`), the way
`Wp.Box.wpNext` does for `sol_wp`: the verdict need not be predicted
before it is computed. -/
def vcNext (haltOk : Halt -> Prop) (rest : List Ann) (Q : State -> Prop) :
    Res State -> Prop
  | .ok s' => vc haltOk s' rest Q
  | .error h => haltOk h

@[simp] theorem vc_nil (haltOk : Halt -> Prop) (s : State) (Q : State -> Prop) :
    vc haltOk s [] Q = Q s := rfl

@[simp] theorem vc_assert (haltOk : Halt -> Prop) (s : State)
    (φ : State -> Prop) (rest : List Ann) (Q : State -> Prop) :
    vc haltOk s (Ann.assert φ :: rest) Q = (φ s ∧ vc haltOk s rest Q) := rfl

@[simp] theorem vc_assume (haltOk : Halt -> Prop) (s : State)
    (φ : State -> Prop) (rest : List Ann) (Q : State -> Prop) :
    vc haltOk s (Ann.assume φ :: rest) Q = (φ s -> vc haltOk s rest Q) := rfl

/-- Peel one statement given the interpreter's verdict, whatever it is.
Total by construction: the hypothesis is established for the `r` the
interpreter actually computes, and `vcNext` dispatches on it afterwards
by iota reduction. -/
theorem vc_stmt_eval {haltOk : Halt -> Prop} {st : Stmt} {rest : List Ann}
    {s : State} {Q : State -> Prop} {r : Res State}
    (hexec : Semantics.execStmt s st = r) :
    vc haltOk s (Ann.stmt st :: rest) Q = vcNext haltOk rest Q r := by
  subst hexec; rfl

/-- Total correctness: the body runs to completion (no `revert`, no
`stuck`) and `Q` holds of the final state. The default reading of a
specified function — `@custom:ensures` promises something happened. -/
abbrev totalVC (s : State) (body : List Ann) (Q : State -> Prop) : Prop :=
  vc (fun _ => False) s body Q

/-- Partial correctness (`@custom:partial`): a `revert` discharges the
obligation, so `Q` constrains only the terminating-normally runs. Note
this is genuinely weaker — a function whose first statement is
`require(false)` satisfies every partial specification. -/
abbrev partialVC (s : State) (body : List Ann) (Q : State -> Prop) : Prop :=
  vc (fun h => h = Halt.revert) s body Q

/-- The `@custom:reverts_when` obligation: from this state the body must
halt with `revert`. Ghost `assert`s are transparent to it (they have no
run-time effect); a ghost `assume` guards it, as everywhere else. -/
def revertsVC : State -> List Ann -> Prop
  | _, [] => False
  | s, Ann.assert _ :: rest => revertsVC s rest
  | s, Ann.assume φ :: rest => φ s -> revertsVC s rest
  | s, Ann.stmt st :: rest =>
      match Semantics.execStmt s st with
      | .ok s' => revertsVC s' rest
      | .error h => h = Halt.revert

/-- `revertsVC`'s continuation after one statement (see `vcNext`). -/
def revertsNext (rest : List Ann) : Res State -> Prop
  | .ok s' => revertsVC s' rest
  | .error h => h = Halt.revert

@[simp] theorem revertsVC_nil (s : State) : revertsVC s [] = False := rfl

@[simp] theorem revertsVC_assert (s : State) (φ : State -> Prop)
    (rest : List Ann) :
    revertsVC s (Ann.assert φ :: rest) = revertsVC s rest := rfl

@[simp] theorem revertsVC_assume (s : State) (φ : State -> Prop)
    (rest : List Ann) :
    revertsVC s (Ann.assume φ :: rest) = (φ s -> revertsVC s rest) := rfl

theorem revertsVC_stmt_eval {st : Stmt} {rest : List Ann} {s : State}
    {r : Res State} (hexec : Semantics.execStmt s st = r) :
    revertsVC s (Ann.stmt st :: rest) = revertsNext rest r := by
  subst hexec; rfl

/-- A whole specification as a predicate on the entry state: assume the
precondition there, then run the annotated body under `haltOk` and check
the postcondition. `post` takes *both* states because `old(e)` reads the
entry one, and `body` takes the entry state because a ghost
`assert`/`assume` may mention `old(e)` too.

This is what `solspec!{ requires … ensures … < … > }` elaborates to.
The
front-end does not use it — it emits one theorem per clause, so that a
failure lands on the line that caused it, and hoists the precondition
into the theorem's hypotheses where `omega` can see it without an
`intro`. -/
def Obligation (haltOk : Halt -> Prop) (pre : State -> Prop)
    (body : State -> List Ann) (post : State -> State -> Prop)
    (s0 : State) : Prop :=
  pre s0 -> vc haltOk s0 (body s0) (post s0)

/-- `Obligation` for a `reverts_when` clause: under the precondition and
the trigger, the body must halt with `revert`. -/
def RevertObligation (pre trigger : State -> Prop)
    (body : State -> List Ann) (s0 : State) : Prop :=
  pre s0 -> trigger s0 -> revertsVC s0 (body s0)

end Spec
end Solidity
