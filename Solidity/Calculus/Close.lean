import Solidity.Calculus.SurfaceNotation
import Solidity.Calculus.TacticSyntax
import Solidity.Calculus.CloseLemmas

/-!
# Closing the first-order goal: `sol_close`

`sol_symex` leaves `{U₁} … {Uₙ} φ` with no modality in it.  Its updates are
not rewritten away, as mini-solkey's `Ch14_Updates` does: a term here *is* a
call of the interpreter (`Tm.eval`), so applying an update
in an arbitrary state `σ` is running it, and what remains is a statement
about what `saveStorage`, `findStorage`, `readAddr` and `getEnv` return on a
`σ` nobody knows.  `sol_close` proves that statement with one contextual
`simp` over the `close_rw` set, then `omega` or `grind` for the arithmetic.

**Weakest preconditions.**  `Modality.wp m x P` is `P` of what `x` returns,
or `m.onHalt` when it halts; `Modality.after` is its instance at `State`.
Pushed through the binds of the evaluators (`Modality.wp_bind`, and one
equation per constructor below), it turns the goal into a nest of `∀ τ,
x = .ok τ → …` (the box) or `∃ τ, x = .ok τ ∧ …` (the diamond).  A
`split` on the unfolded `match`es does not get there: it splits the
outermost one only, and leaves the evaluator's inner matches in
hypotheses.

**Read after write.**  Under the box, a write is named on the spot, together
with what `ReadWrite.lean` knows of the state it returns: a storage write
(`Modality.wp_box_saveStorage`) reads back at and below the path written
and as before apart from it, a memory write (`wp_box_writeAddr`) likewise
at an address, a copy (`wp_box_copyStToM`, `wp_box_copyMem`) member by
member, and each leaves the other components alone.  A read of a subtree
(`wp_box_findStorage`) is named with the reads below it, which is what
settles a read above a write.  The `simp` is contextual, so every such
fact rewrites what follows it; the apartness of concrete paths is decided
by computation, that of symbolic keys (`balances[k]`, `balances[j]`) by a
hypothesis `k != j` of the formula or a branch.  Every step is a lemma or a
hypothesis: nothing evaluated is trusted, the kernel checks the proof.

**A scoped leaf** (`open scoped Solidity.Scoped`) is read by
`Calculus/CloseScoped.lean`'s steps, which each step below steps aside for
(`Close.scopedGoal`): the scoped formula with `close_rw_s`, its parameters
at their types.  This module's set `close_rw` holds what the interpreter's
states and values are made of, which `sol_decide`'s unfolding
(`Calculus/Decide.lean`) reads too.  What either set knows of the
interpreter is `Calculus/CloseLemmas.lean`'s.

What does not close, and why (on either side):

* a write under the diamond: the closer reads the write's update on the
  erasure's untyped term model, where `find`/`save` at `alice` is not known
  to be defined, so `⟨ alice.age = 1; ⟩ true` stays open at
  `{ storage := save(storage, alice.age, 1) } true`.  Write the box, or put
  the well-formedness of the storage in the premise;
* two symbolic keys the formula does not tell apart: there is no case
  split on `k = j`, so `[ balances[k] = 5; balances[j] = 6; ] balances[k] == 5`
  stays open (it is false at `k = j`);
* two memory objects: nothing says that two allocations are different
  objects, since `⊨` includes states whose heap already holds an object at
  `nextId`;
* a read of an array a push wrote, the array known only by its shape:
  `[ uint n = values.length; values.push(42); ] values.length == n + 1`
  stays open, since the push's write is left as `saveStorage … = .ok τ`
  with none of the facts `wp_box_saveStorage` names
  (`Examples/Tactics/CallOperands.lean` pins it open, and writes its push rows as
  chains for this);
* a default read out of a fresh memory object (`Person memory m;
  uint x = m.age;`): the default of a struct type is a well-founded
  definition (`defaultForTy`) that `simp` does not unfold.
-/

namespace Solidity

open Semantics SemanticsProperties

namespace Close

/-! ## Evaluation, one constructor at a time

The evaluators' own equations end in `match`es on a binding or a pair,
which `simp` cannot see through while the scrutinee is unknown.  These
restate them as binds of named functions, so that `Modality.wp_bind`
applies and the scrutinee is named first.  A read of memory stays whole
(`readVal`), since what is known of it is known of the value. -/

/-- `oldNet` bound to a ledger reads it. -/
@[simp] theorem bindingLedger_ledger (l : List (Int × Int)) :
    bindingLedger (.ledger l) = .ok l := rfl

/-- `old` bound to a storage reads it. -/
@[simp] theorem bindingStore_store (st : List (Name × SVal)) :
    bindingStore (.store st) = .ok st := rfl

/-- `x` bound to `10` reads `10`. -/
@[simp] theorem bindingVal_val (v : Value) : bindingVal (.val v) = .ok v := rfl
/-- `p` bound to `alice.account` reads that path. -/
@[simp] theorem bindingPath_spath (r : Name) (segs : List Seg) :
    bindingPath (.spath r segs) = .ok (r, segs) := rfl
/-- `m` bound to the object `3` reads `3`. -/
theorem bindingRef_mref (id : Nat) : bindingRef (.mref id) = .ok id := rfl
/-- A local read as a value was bound to one: `a == 1` says `a` holds `1`. -/
@[simp] theorem bindingVal_eq_ok {b : Binding} {v : Value} :
    bindingVal b = .ok v ↔ b = .val v := by
  cases b <;> simp [bindingVal]
/-- A local read as an object was bound to one. -/
theorem bindingRef_eq_ok {b : Binding} {id : Nat} :
    bindingRef b = .ok id ↔ b = .mref id := by
  cases b <;> simp [bindingRef]

section Eval

/-- Binding a local leaves the ledger. -/
theorem net_setEnv (σ : State) (x : Var) (b : Binding) : (σ.setEnv x b).net = σ.net := rfl
/-- Binding a local leaves the storage. -/
theorem storage_setEnv (σ : State) (x : Var) (b : Binding) : (σ.setEnv x b).storage = σ.storage :=
  rfl

end Eval

end Close

/-! ## The tactic -/

attribute [close_rw]
  Theory.StValue.Equiv.prim_iff Theory.StValue.prim.injEq
  Close.forall_unit Close.exists_unit
  Close.find_overlay_fields Close.layAt_prim Close.fieldPath_nil Close.fieldPath_field
  Close.fieldPath_at
  -- values and the state's parts
  Close.equiv_prim_left_iff IntOp.apply State.envVal State.getNet
  Close.idxOk_array Close.idxOk_map Close.pastEnd_array
  Close.lookupBy_setBy_int State.pay State.setNet
  -- operators
  Close.evalBinop_strict Close.evalBinop_and Close.evalBinop_or applyBinOp applyUnOp unopCheck
  Close.pickBranch_eq BinOp.retTy BinOp.isArith checkArith uintBound intBound
  Close.uintBitwise_ofNat Close.uintBitwise_ofNat_cast Close.uintBitwise_cast_ofNat
  uintBitwise_natCast Nat.reduceAnd Nat.reduceOr Nat.reduceXor
  -- runs
  Modality.wp_ok Modality.wp_pure Modality.wp_error Modality.wp_bind Modality.wp_ite
  Modality.wp_diamond Modality.onHalt_box Modality.onHalt_diamond
  Close.pure_eq_ok Res.ok_bind Res.error_bind Close.bind_ok_right bind_assoc
  Close.saveStorage_bind_restore Close.writeAddr_bind_restore
  -- values
  Close.bindingVal_val Close.bindingPath_spath Close.bindingRef_mref Close.bindingStore_store
  Close.bindingLedger_ledger
  Close.bindingVal_eq_ok
  Close.bindingRef_eq_ok Close.asInt_eq_ok Close.asBool_eq_ok Close.asRef_eq_ok Close.toMVal_eq
  Close.toSVal_int Close.toSVal_bool Close.asValue_toSVal Close.asValue_toMVal Close.asValue_int
  Close.asValue_bool Close.mval_asValue_prim Close.mval_asValue_ref Close.mval_asRef_ref
  Close.defaultOf_int Close.defaultOf_bool Close.asInt_int Close.asBool_bool
  -- states
  State.findStorage_setEnv State.checkIndex_setEnv Close.checkIndex_mk
  State.getEnv_setEnv_self State.getEnv_setEnv_ne Close.findStorage_mk
  Close.getEnv_mk Close.readAddr_mk Close.readVal_mk Close.readAddr_setEnv Close.readVal_setEnv
  Close.tx_setEnv Close.selfBalance_setEnv Close.net_setEnv Close.lookupBy_ite
  -- paths, arrays, copies
  Close.diverge_cons' Close.not_diverge_nil_left Close.not_diverge_nil_right Close.prefix_nil
  Close.prefix_cons Close.prefix_cons_nil Close.after_nil Close.after_cons SVal.find_nil
  List.nil_append List.cons_append List.append_nil
  Close.arrLen_array Close.arrLen_eq_ok Close.pushOn_array Close.popOn_push Close.popOn_push_keep Close.find_push_last
  Close.copyLeaf_prim Close.apart_field Close.apart_index Close.apart_field_index
  Close.apart_index_field
  -- logic
  Except.ok.injEq Binding.val.injEq Binding.mref.injEq Binding.store.injEq Binding.ledger.injEq
  PrimVal.int.injEq
  PrimVal.bool.injEq
  MVal.prim.injEq MVal.ref.injEq SVal.prim.injEq Prod.mk.injEq Seg.field.injEq Seg.at.injEq
  Var.user.injEq Var.fresh.injEq Int.ofNat.injEq
  forall_eq' forall_eq exists_eq_left' exists_eq_left exists_eq' exists_eq forall_exists_index
  and_imp
  true_and and_true and_self implies_true forall_const ne_eq not_false_eq_true not_true_eq_false
  true_or or_true or_false false_or not_and not_exists Classical.not_not true_implies
  false_implies decide_eq_true_eq decide_eq_false_iff_not
  Bool.and_true Bool.and_false Bool.true_and Bool.false_and Bool.or_true Bool.or_false
  Bool.true_or Bool.false_or Bool.not_true Bool.not_false Bool.not_not
  Bool.not_eq_true' Bool.not_eq_false' Bool.and_eq_true Bool.or_eq_true Bool.and_eq_false_iff
  Bool.or_eq_false_iff
  -- computation
  reduceCtorEq reduceIte reduceDIte String.reduceEq Nat.reduceEqDiff Nat.reducePow Int.reduceEq
  Int.reduceAdd Int.reduceSub Int.reduceMul Int.reduceNeg Int.reduceLT Int.reduceLE

-- A write, a subtree read, a copy is named together with what is known of it.
attribute [close_rw] Modality.wp_box_saveStorage Modality.wp_box_findStorage
  Modality.wp_box_writeAddr Modality.wp_box_copyStToM Modality.wp_box_allocDefault
  Modality.wp_box_copyMem Modality.wp_box_transferAt

-- The bare box names a result with nothing, so it waits in a set of its own
-- (`close_rw_last`, consulted after `close_rw`) until every fact is in scope:
-- a push is not named before the array it pushes onto is known.  The diamond
-- is named at once, since what a premise says is what the rest needs.
attribute [close_rw_last] Modality.wp_box

namespace Close

open Lean Elab Tactic Meta in
/-- Whether the main goal is a scoped leaf's: it or its context reads a
typed state (`Solidity.State`, `EState`, `Valid`, `CloseS.holdsE`).  The
steps below then step aside for `Calculus/CloseScoped.lean`'s, which read
it with `close_rw_s`. -/
def scopedGoal : TacticM Bool := withMainContext do
  let names : List Lean.Name :=
    [`Solidity.State, `Solidity.EState, `Solidity.Valid, `Solidity.CloseS.holdsE]
  let hit (e : Expr) : Bool := (e.find? fun x => x.isConst && names.contains x.constName!).isSome
  if hit (← instantiateMVars (← getMainTarget)) then return true
  for d in ← getLCtx do
    if !d.isImplementationDetail && hit (← instantiateMVars d.type) then return true
  return false

end Close

open Lean Elab Tactic in
/-- The first pass of `sol_close`: evaluate, and name every write with what
is known of it. -/
elab "sol_close_eval" : tactic => do
  if ← Close.scopedGoal then throwUnsupportedSyntax
  evalTactic (← `(tactic| simp only [close_rw]))

open Lean Elab Tactic in
/-- The second: each premise in scope for what follows it, so that the facts
about a write rewrite the reads after it.  Nothing is named bare yet: a
result a later fact decides (the array a push lands on) is decided first. -/
elab "sol_close_facts" : tactic => do
  if ← Close.scopedGoal then throwUnsupportedSyntax
  evalTactic (← `(tactic|
    simp (config := { contextual := true, maxSteps := 400000 }) only [close_rw]))

open Lean Elab Tactic in
/-- The third: what is left is named bare, under the box. -/
elab "sol_close_reads" : tactic => do
  if ← Close.scopedGoal then throwUnsupportedSyntax
  evalTactic (← `(tactic|
    simp (config := { contextual := true, maxSteps := 400000 }) only [close_rw, close_rw_last]))

open Lean Elab Tactic in
/-- `sol_close_reads` on the goal and every hypothesis. -/
elab "sol_close_reads_all" : tactic => do
  if ← Close.scopedGoal then throwUnsupportedSyntax
  evalTactic (← `(tactic|
    simp_all (config := { maxSteps := 400000 }) only [close_rw, close_rw_last]))

/-- `sol_close`'s first step: a scoped leaf (`Valid ψ`) read as
`CloseS.holdsE` reads it (`Calculus/CloseScoped.lean`); any other goal is
left as it is. -/
syntax "sol_close_unwrap" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| sol_close_unwrap) => pure ()

/-- `sol_close`: prove a formula with no modality left in an arbitrary state
(`Calculus/Close.lean`; a scoped leaf by `Calculus/CloseScoped.lean`'s
steps of the same names).  Run `sol_symex` first; with no goal left it does
nothing. -/
macro "sol_close" : tactic => `(tactic|
  all_goals
   (sol_close_unwrap
    intro σ
    sol_close_eval
    all_goals try sol_close_facts
    all_goals try sol_close_reads
    all_goals try (intros; sol_close_reads_all)
    all_goals try (subst_vars; sol_close_reads_all)
    all_goals (try intros)
    -- a bounds check returns `()`: nothing is left to choose
    all_goals (try simp only [Close.exists_unit, Close.forall_unit, exists_const, forall_const] at *)
    all_goals first | omega | grind))

open Lean Elab Tactic in
/-- `sol_close_mt`'s first pass: `sol_close_eval` with the storage
evaluators unfolded over a deployment's storage. -/
elab "sol_close_mt_eval" : tactic => do
  if ← Close.scopedGoal then throwUnsupportedSyntax
  evalTactic (← `(tactic|
    simp (config := { decide := true }) only [close_rw, List.map_cons, List.map_nil,
      defaultForTy, State.saveStorage, State.findStorage, lookupBy, setBy, SVal.save, SVal.find,
      Close.storage_setEnv, Except.ok.injEq, exists_eq_left']))

/-- `sol_close` from a deployment's storage, `{storage := mtSt ‖ …}` in
front (`STerm.eval_mtSt`): the storage is then a list of the roots at their
defaults, and the storage evaluators are unfolded over it — solkey's
`selectOnEmptyStorage` and `saveOnEmptyStorage` (`structRules.key`), read off
that list, which is what lets a write under the diamond return.  Not in
`close_rw`: an arbitrary storage is left to the read-after-write facts.
Known limits (pinned open in `Examples/Tactics/Constructors.lean`): a read
at a free key of a mapping the deployment does not write (the default
map's `checkIndex`), and a member of a struct root (`defaultForTy` of a
struct, `defaultForFields` of the struct table, is not unfolded). -/
macro "sol_close_mt" : tactic => `(tactic|
  all_goals
   (sol_close_unwrap
    intro σ
    sol_close_mt_eval
    all_goals try sol_close_facts
    all_goals try sol_close_reads
    all_goals try (intros; sol_close_reads_all)
    all_goals (try intros)
    all_goals first | omega | grind))

end Solidity
