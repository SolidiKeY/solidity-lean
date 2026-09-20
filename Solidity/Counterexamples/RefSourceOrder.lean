import Solidity.Calculus.RuleSoundness
import Solidity.Semantics.DecEq

/-!
# What `hprim` carves out: the interpreter, not the rule

`memoryToStorageUnfoldLeftSndTargetIndex_sound` and its siblings assume
`hprim : rhs.ty.isPrimitive = true`.  That is *not* implied by the rule's own
condition, which is only

    isSimple path ∧ isComplex index ∧ isMemory rhs ∧ isSimple rhs

so the rule fires on a **reference**-typed memory source too, and on that
instance there is no soundness theorem.  This file exhibits the instance: rule
and interpreter genuinely disagree on it.

**Which of the two is wrong is settled, and it is the interpreter.**  The same
program runs on a real EVM as solkey's
`TestSuite.storageIndexWriteRefSourceImpureIndex`, checked by
`SolidityRuntimeExecutionTest`, and the chain stores `1` — the residual's
answer, not the interpreter's.  solc is right-hand-side-first for a *primitive*
source, but for a struct source it resolves the target slot first and then
copies member by member, reading the source at copy time; the index has already
run by then.  KeY closes `assert(persons[0].age == 1)` and is right to.

So `hprim` is not hiding an unsound rule.  It is marking the shapes on which
`Semantics.execAssignNested` — uniformly value-first, see `docs/solc-alignment.md` —
is unfaithful to solc.  Until the interpreter is made target-first for reference
sources, the reference case cannot be *stated* correctly, let alone proved, and
`hprim` is the honest way to say so.

`Rules.freezeRhs` declines to freeze a reference for an unrelated and still-valid
reason: a snapshot would have to be a declaration, and `Stmt.memoryDecl` from a
memory source binds `Binding.mref` — an alias, not a copy
(`Semantics.execStmt`, memoryDecl arm).  Solidity has no memory-to-memory deep
copy to emit.  With a target-first interpreter no snapshot is wanted anyway.

## The Solidity

```solidity
struct Account { uint balance; }
struct Person  { Account account; uint age; }

Person[] people;                    // storage

function f() public {
    people.push();                  // people[0] exists, age == 0
    Person memory carol;            // carol.age == 0

    people[carol.age++] = carol;

    assert(people[0].age == 1);     // holds on chain
}
```

The rule rewrites the assignment to

```solidity
Person[] storage sp = people;       // path capture
uint idx = carol.age++;             // index capture: idx == 0, carol.age := 1
sp[idx] = carol;                    // copies carol *now* -- age == 1
```

which stores `1` (`prog_residual`) and agrees with the chain.  This Lean
interpreter copies `carol` before running the index and stores `0`
(`prog_original`).  `refSource_disagrees` is therefore a statement about the
interpreter's evaluation order; read as a claim about the calculus it would be
backwards.
-/
namespace Solidity
namespace Counterexamples
namespace RefSourceOrder

open Rules RuleSoundness Semantics

/-- Agreement forces equal storages (or the same abort). -/
theorem ResultsAgree.map_storage {ns : List Name} {a b : Res State}
    (h : ResultsAgree ns a b) :
    a.map State.storage = b.map State.storage := by
  match a, b, h with
  | .error e₁, .error e₂, h =>
      have h' : e₁ = e₂ := h
      subst h'
      rfl
  | .ok s₁, .ok s₂, h =>
      have h' : EnvAgreeExcept ns s₁ s₂ := h
      simp only [Except.map, h'.storage]
  | .error _, .ok _, h => exact (h : False).elim
  | .ok _, .error _, h => exact (h : False).elim

/-- `people = [default Person]`, and `carol` a memory `Person` with `age = 0`. -/
def store : State :=
  let s : State :=
    { State.exampleStore with
        storage :=
          setBy "people" (SVal.array [defaultForRef (RefTy.struct "Person")] [])
            State.exampleStore.storage,
        env := [] }
  match execStmt s sstmt!{ Person memory carol } with
  | .ok s' => s'
  | .error _ => s

def prog : Stmt := sstmt!{ people[carol.age++] = carol }

/-- The rule applies: simple path, complex index, memory simple source. -/
theorem prog_cond :
    (ruleEffect .memoryToStorageUnfoldLeftSndTargetIndex).cond prog := by
  change _ = true ∧ _ = true ∧ _ = true ∧ _ = true
  decide

/-- And the source is a **reference**, so `hprim` does not hold. -/
theorem prog_not_prim :
    (sexpr!{ carol }).ty.isPrimitive = false := by decide

def residual : Block :=
  (ruleEffect .memoryToStorageUnfoldLeftSndTargetIndex).block prog prog_cond

/-- Value first: this interpreter copies `carol` while `age = 0`, then the index
increments it, so `people[0].age` is `0`.  A real EVM stores `1`. -/
theorem prog_original :
    (execStmt store prog).map
        (fun s => s.findStorage "people" [Seg.at 0, Seg.field "age"]) =
      .ok (.ok (SVal.int 0)) := by
  native_decide

/-- Index first: the residual increments `carol.age` and *then* copies, so it
stores `1` — which is what the chain stores. -/
theorem prog_residual :
    (execBlock store residual).map
        (fun s => s.findStorage "people" [Seg.at 0, Seg.field "age"]) =
      .ok (.ok (SVal.int 1)) := by
  native_decide

theorem prog_storage_ne :
    (execStmt store prog).map State.storage ≠
      (execBlock store residual).map State.storage := by
  native_decide

/-- **Rule and interpreter disagree on a reference-typed memory source**, so
`hprim` is not bookkeeping: drop it and `..._sound` is false *as stated against
this interpreter*.  The disagreement indicts `execAssignNested`, which is
value-first for every source type: the real EVM agrees with `residual`
(solkey `TestSuite.storageIndexWriteRefSourceImpureIndex`).  The repair is to
make the interpreter target-first for reference sources; until then `hprim`
stays. -/
theorem refSource_disagrees :
    ¬ ResultsAgree aliasNames (execStmt store prog) (execBlock store residual) :=
  fun h => prog_storage_ne (ResultsAgree.map_storage h)

end RefSourceOrder
end Counterexamples
end Solidity
