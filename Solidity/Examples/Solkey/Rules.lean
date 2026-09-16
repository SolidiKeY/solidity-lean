import Solidity.Wp.Verifier
import Solidity.Theory.Memory
import Solidity.Theory.Denote

/-!
# solkey `keyext.solidity.core/src/test/resources/.../examples/*.key`, ported

The 41 rule-level problems `RulesTest` enumerates, hand-written: they are
`.key` files, so there is nothing for `scripts/solkey-port.mjs` to read.

Only seven of them state a *program* judgment. `u` and `v` are the two
`int` program variables of `commonFields.key`; KeY leaves them
unconstrained and a premise such as `u = 42 ->` supplies their value,
which ports to a declaration.

Twenty-seven more are **term-level**: they assert heap-algebra identities
such as `selectSt(storeSt(mtSt, balance, 10), balance) = 10`
(`simpleExample1.key`), or they run a program's *updates* — the sequential
`{st := save(…)}{v := find(…)}(v = 20)` of `storageExample1.key` — with no
modality to execute at all.  `sol_wp` proves dynamic logic judgments and a
bare equation between store terms is not one, so those are proved directly
over the theories: `Theory/Storage.lean` for `selectSt`/`storeSt`/`save`/`find`
and `Theory/Memory.lean` for `write`/`addM`/`read`/`new`/`idC`.  Each one is
the taclets applied in the order KeY applies them, which is why the proofs
name `selectOnStore`, `find_save_frame`, `readOnWrite`, `readOnAddM` and
`defaultDefIdentity` rather than computing.

The `.key` files' own Solidity comments are reproduced in the docstrings:
these are the worked memory and storage examples of the paper's first draft.

One more problem lives here from a different upstream directory:
`keyext.solidity.examples/storage/copyKeepsMapping.key`, added by solkey
`c80a54494c`. It is term-level for the same reason, so it belongs with these
rather than in a module of its own — `scripts/solkey-port.mjs` gives it its own
`storage` suite over the same contract.

The remaining seven exercise the KeY loader and taclet machinery
(`hasSortVarcondTest`, `listTests`, `storageFieldRead`/`storageFieldWrite`
and `memberAccessExample`'s ad-hoc taclets over `\problem { true }`,
`functionBodyExpandTest`, the empty `problem`).  They are recorded
`unsupported` in `tests/solkey/expected.tsv`.
-/

namespace Solidity
namespace Solkey
namespace Rules

open Semantics Wp Theory

set_option maxHeartbeats 8000000

/-- solkey `assignRuleExample.key`: `u = 42 -> \<{ v = u; }\>(v = 42)`;
the premise on the unconstrained `u` becomes its declaration. -/
theorem solkey_Rules_assignRuleExample :
    (sol!{ < uint u = 42; v = u > (v == 42) }).Holds := by
  sol_wp

/-- solkey `contextAssignTest.key`: two sequential assignments through
context blocks. -/
theorem solkey_Rules_contextAssignTest :
    (sol!{ < v = 42; u = v > (u == 42) }).Holds := by
  sol_wp

/-- solkey `fieldAccessTest.key`: `\<{ value = 42; }\>(true)` — `value`
is the `Token` member of `commonFields.key`, reached here through the
`alice` path the Lean schema gives it. -/
theorem solkey_Rules_fieldAccessTest :
    (sol!{ < alice.account.token.value = 42 > (true) }).Holds := by
  sol_wp

/-- solkey `revert.key`: a plain assignment terminates normally. -/
theorem solkey_Rules_revert :
    (sol!{ < v = 42 > (true) }).Holds := by
  sol_wp

/-- solkey `simpleExpressionTest.key` -/
theorem solkey_Rules_simpleExpressionTest :
    (sol!{ < v = 100 > (v == 100) }).Holds := by
  sol_wp

/-- solkey `schemaVarExample.key`: `\<{ u; }\>(true)` — a bare expression
statement. `u` is declared first because the port starts from a concrete
store, where reading an unbound stack variable is stuck rather than
unconstrained. -/
theorem solkey_Rules_schemaVarExample :
    (sol!{ < uint u = 0; u > (true) }).Holds := by
  sol_wp

/-- solkey `programRulesTest.key`: one `\problem` conjoining four
judgments — the assign rule under a premise, a bare expression statement
under both modalities, and an assignment observed in the postcondition. -/
theorem solkey_Rules_programRulesTest :
    (sol!{ < uint u = 42; v = u > (v == 42) }).Holds
      ∧ (sol!{ < uint u = 0; u > (true) }).Holds
      ∧ (sol!{ [ uint u = 0; u ] (true) }).Holds
      ∧ (sol!{ < v = 42 > (v == 42) }).Holds :=
  ⟨by sol_wp, by sol_wp, by sol_wp, by sol_wp⟩


/-! ## The term-level problems

`commonFields.key`'s vocabulary, once.  Its `\unique Field`s are `Seg.field`s
and its `\unique IdentityPrim ca, cb` are two `Nat`s a hypothesis keeps
apart — `\unique` is exactly that hypothesis, and `idC`'s own uniqueness is
`Identity`'s `DecidableEq`. -/

private abbrev age : Seg := .field "age"
private abbrev owner : Seg := .field "owner"
private abbrev balance : Seg := .field "balance"
private abbrev account : Seg := .field "account"
private abbrev carol : Seg := .field "carol"
private abbrev carolAcc : Seg := .field "carolAcc"
private abbrev eve : Seg := .field "eve"
private abbrev f1 : Seg := .field "f1"
private abbrev f2 : Seg := .field "f2"

/-- A primitive read crossing from memory into storage.  KeY's `Prim` is a
sub-sort of both `StValue` and `MemValue`, which is what `simpleExample10`
turns on; this is that sub-sorting, written down. -/
private def stOf : MVal -> StValue
  | .prim p => .prim p
  | .ref _ => .dflt

/-! ### `structRules.key` identities -/

/-- solkey `simpleExample1.key`:
`selectSt<[int]>(storeSt(mtSt, balance, 10), balance) = 10`. -/
theorem solkey_Rules_simpleExample1 :
    (StValue.selectSt (StValue.storeSt .mtSt balance (.prim (.int 10)))
      balance).asInt = 10 := by
  decide

/-- solkey `simpleExample2.key`: the later store wins. -/
theorem solkey_Rules_simpleExample2 :
    (StValue.selectSt
      (StValue.storeSt (StValue.storeSt .mtSt balance (.prim (.int 10)))
        balance (.prim (.int 11))) balance).asInt = 11 := by
  decide

/-- solkey `simpleExample3.key`: a store at another field is invisible. -/
theorem solkey_Rules_simpleExample3 :
    (StValue.selectSt
      (StValue.storeSt (StValue.storeSt .mtSt balance (.prim (.int 10)))
        age (.prim (.int 30))) balance).asInt = 10 := by
  decide

/-- solkey `simpleExample7.key`:
`find<[int]>(save(mtSt, cons1(age), 20), cons1(age)) = 20`. -/
theorem solkey_Rules_simpleExample7 :
    (StValue.find (StValue.save .mtSt [age] (.prim (.int 20))) [age]).asInt
      = 20 := by
  rw [StValue.find_save_same_asInt]; rfl

/-- solkey `simpleExample8.key`: the same, two selectors deep. -/
theorem solkey_Rules_simpleExample8 :
    (StValue.find (StValue.save .mtSt [account, age] (.prim (.int 20)))
      [account, age]).asInt = 20 := by
  rw [StValue.find_save_same_asInt]; rfl

/-- solkey `simpleExample9.key`: a sibling write does not disturb the read —
`find_save_frame` over `diverges [account, balance] [account, age]`. -/
theorem solkey_Rules_simpleExample9 :
    (StValue.find
      (StValue.save (StValue.save .mtSt [account, age] (.prim (.int 20)))
        [account, balance] (.prim (.int 30))) [account, age]).asInt = 20 := by
  rw [StValue.find_save_frame _ _ _ _ (by decide),
    StValue.find_save_same_asInt]
  rfl

/-! ### `memoryRules.key` identities -/

/-- solkey `simpleExample4.key`:
`read<[int]>(write(mem, bob, age, 20), bob, age) = 20`. -/
theorem solkey_Rules_simpleExample4 :
    ∀ (h : List (Nat × MObj)) (mem : Memory) (bob : Identity),
      (Memory.readIn h (.write mem bob age (.prim (.int 20))) bob
        age).asPrim = MVal.int 20 := by
  intro h mem bob
  simp [MemValue.asPrim]

/-- solkey `simpleExample5.key`: the later write wins, in memory. -/
theorem solkey_Rules_simpleExample5 :
    ∀ (h : List (Nat × MObj)) (mem : Memory) (bob : Identity),
      (Memory.readIn h
        (.write (.write mem bob age (.prim (.int 19))) bob age
          (.prim (.int 20))) bob age).asPrim = MVal.int 20 := by
  intro h mem bob
  simp [MemValue.asPrim]

/-- solkey `simpleExample6.key`: a reference read names the identity a later
write then reaches — `read<[Identity]>` feeding `read<[int]>`. -/
theorem solkey_Rules_simpleExample6 :
    ∀ (h : List (Nat × MObj)) (mem : Memory) (bob bobAcc : Identity),
      (Memory.readIn h
        (.write (.write mem bobAcc owner (.ident bob)) bob age
          (.prim (.int 20)))
        (Memory.readId h (.write mem bobAcc owner (.ident bob)) bobAcc owner)
        age).asPrim = MVal.int 20 := by
  intro h mem bob bobAcc
  simp [Memory.readId, MemValue.asIdentity, MemValue.asPrim]

/-- solkey `simpleExample10.key`: a memory read feeding a storage save —
the two theories meet at `Prim`. -/
theorem solkey_Rules_simpleExample10 :
    ∀ (h : List (Nat × MObj)) (mem : Memory) (bob : Identity),
      (StValue.find
        (StValue.save .mtSt [balance]
          (stOf (Memory.readIn h (.write mem bob age (.prim (.int 20))) bob
            age).asPrim)) [balance]).asInt = 20 := by
  intro h mem bob
  rw [StValue.find_save_same_asInt]
  simp [MemValue.asPrim, stOf, StValue.asInt]

/-! ### `storageExample*.key` — the update sequences of the draft's storage
examples.  Each is the `\problem`'s nested `{st := …}` updates with the final
`find` read where the `.key` file puts it.

The copies read a value member through the leaf of a `save`.  KeY resolves
that by the read's sort (`find<[int]>` takes the written value's member);
the shape dispatch of `Theory/Storage.lean` looks at what the location held
instead, so over an arbitrary `st` the `.key` claim needs its well-sortedness
spelled out: the member the copy lands on holds neither a mapping nor a
struct (`Theory.StValue.find_save_extends_field`).  Rooted at `mtSt` (the
`-2` files) it holds outright. -/

/-- solkey `storageExample1.key`: a deep copy taken between two writes to the
source sees the *first* — `find_save_frame` off the second, then
`find_save_prefix`/`find_save_same` through the copy. -/
theorem solkey_Rules_storageExample1 :
    ∀ st : StValue,
      StValue.isMapping (StValue.selectSt (StValue.find st [carolAcc, owner]) age) = false ->
      StValue.isNode (StValue.selectSt (StValue.find st [carolAcc, owner]) age) = false ->
      (StValue.find
        (StValue.save
          (StValue.save (StValue.save st [carol, age] (.prim (.int 20)))
            [carolAcc, owner]
            (StValue.asStruct
              (StValue.find (StValue.save st [carol, age] (.prim (.int 20)))
                [carol])))
          [carol, age] (.prim (.int 21)))
        [carolAcc, owner, age]).asInt = 20 := by
  intro st hm hn
  rw [StValue.find_save_frame _ _ _ _ (by decide)]
  rw [show [carolAcc, owner, age] = [carolAcc, owner] ++ [age] from rfl,
    StValue.find_save_extends_field _ _ _ _
      (by rwa [StValue.find_save_frame _ _ _ _ (by decide)])
      (by rwa [StValue.find_save_frame _ _ _ _ (by decide)]),
    StValue.selectSt_asStruct]
  change (StValue.find _ [carol, age]).asInt = 20
  rw [StValue.find_save_same_asInt]
  rfl

/-- solkey `storageExample2.key`:
```
carol.age = 20;
eve = carol;
return eve.age;
```
A whole-root copy is a deep copy: the value follows. -/
theorem solkey_Rules_storageExample2 :
    ∀ st : StValue,
      StValue.isMapping (StValue.selectSt (StValue.find st [eve]) age) = false ->
      StValue.isNode (StValue.selectSt (StValue.find st [eve]) age) = false ->
      (StValue.find
        (StValue.save (StValue.save st [carol, age] (.prim (.int 20)))
          [eve]
          (StValue.asStruct
            (StValue.find (StValue.save st [carol, age] (.prim (.int 20)))
              [carol])))
        [eve, age]).asInt = 20 := by
  intro st hm hn
  rw [show [eve, age] = [eve] ++ [age] from rfl,
    StValue.find_save_extends_field _ _ _ _
      (by rwa [StValue.find_save_frame _ _ _ _ (by decide)])
      (by rwa [StValue.find_save_frame _ _ _ _ (by decide)]),
    StValue.selectSt_asStruct]
  change (StValue.find _ [carol, age]).asInt = 20
  rw [StValue.find_save_same_asInt]
  rfl

/-- solkey `storageExample3.key`:
```
carol.age = 20;
return eve.age;
```
A read off the written path gets the default from the empty storage. -/
theorem solkey_Rules_storageExample3 :
    (StValue.find (StValue.save .mtSt [carol, age] (.prim (.int 20)))
      [eve, age]).asInt = 0 := by
  simp [StValue.find, StValue.asInt, StValue.selectSt]

/-- solkey `storageExample4.key`:
```
carol.age = 20;
eve = carol;
carol.age = 30;
return eve.age;
```
There is no sharing in a deep copy: writing the source afterwards leaves the
copy alone. -/
theorem solkey_Rules_storageExample4 :
    ∀ st : StValue,
      StValue.isMapping (StValue.selectSt (StValue.find st [eve]) age) = false ->
      StValue.isNode (StValue.selectSt (StValue.find st [eve]) age) = false ->
      (StValue.find
        (StValue.save
          (StValue.save (StValue.save st [carol, age] (.prim (.int 20)))
            [eve]
            (StValue.asStruct
              (StValue.find (StValue.save st [carol, age] (.prim (.int 20)))
                [carol])))
          [carol, age] (.prim (.int 30)))
        [eve, age]).asInt = 20 := by
  intro st hm hn
  rw [StValue.find_save_frame _ _ _ _ (by decide)]
  rw [show [eve, age] = [eve] ++ [age] from rfl,
    StValue.find_save_extends_field _ _ _ _
      (by rwa [StValue.find_save_frame _ _ _ _ (by decide)])
      (by rwa [StValue.find_save_frame _ _ _ _ (by decide)]),
    StValue.selectSt_asStruct]
  change (StValue.find _ [carol, age]).asInt = 20
  rw [StValue.find_save_same_asInt]
  rfl

/-- solkey `storageExample1-2.key`: `storageExample1` rooted at `mtSt`. -/
theorem solkey_Rules_storageExample1_2 :
    (StValue.find
      (StValue.save
        (StValue.save (StValue.save .mtSt [carol, age] (.prim (.int 20)))
          [carolAcc, owner]
          (StValue.asStruct
            (StValue.find (StValue.save .mtSt [carol, age] (.prim (.int 20)))
              [carol])))
        [carol, age] (.prim (.int 21)))
      [carolAcc, owner, age]).asInt = 20 := by
  rw [StValue.find_save_frame _ _ _ _ (by decide)]
  rw [show [carolAcc, owner, age] = [carolAcc, owner] ++ [age] from rfl,
    StValue.find_save_extends_field _ _ _ _
      (by rw [StValue.find_save_frame _ _ _ _ (by decide)]; decide)
      (by rw [StValue.find_save_frame _ _ _ _ (by decide)]; decide),
    StValue.selectSt_asStruct]
  change (StValue.find _ [carol, age]).asInt = 20
  rw [StValue.find_save_same_asInt]
  rfl

/-- solkey `storageExample2-2.key`: `storageExample2` rooted at `mtSt`. -/
theorem solkey_Rules_storageExample2_2 :
    (StValue.find
      (StValue.save (StValue.save .mtSt [carol, age] (.prim (.int 20)))
        [eve]
        (StValue.asStruct
          (StValue.find (StValue.save .mtSt [carol, age] (.prim (.int 20)))
            [carol])))
      [eve, age]).asInt = 20 := by
  rw [show [eve, age] = [eve] ++ [age] from rfl,
    StValue.find_save_extends_field _ _ _ _
      (by rw [StValue.find_save_frame _ _ _ _ (by decide)]; decide)
      (by rw [StValue.find_save_frame _ _ _ _ (by decide)]; decide),
    StValue.selectSt_asStruct]
  change (StValue.find _ [carol, age]).asInt = 20
  rw [StValue.find_save_same_asInt]
  rfl

/-- solkey `storageExample4-2.key`: `storageExample4` rooted at `mtSt`. -/
theorem solkey_Rules_storageExample4_2 :
    (StValue.find
      (StValue.save
        (StValue.save (StValue.save .mtSt [carol, age] (.prim (.int 20)))
          [eve]
          (StValue.asStruct
            (StValue.find (StValue.save .mtSt [carol, age] (.prim (.int 20)))
              [carol])))
        [carol, age] (.prim (.int 30)))
      [eve, age]).asInt = 20 := by
  rw [StValue.find_save_frame _ _ _ _ (by decide)]
  rw [show [eve, age] = [eve] ++ [age] from rfl,
    StValue.find_save_extends_field _ _ _ _
      (by rw [StValue.find_save_frame _ _ _ _ (by decide)]; decide)
      (by rw [StValue.find_save_frame _ _ _ _ (by decide)]; decide),
    StValue.selectSt_asStruct]
  change (StValue.find _ [carol, age]).asInt = 20
  rw [StValue.find_save_same_asInt]
  rfl

/-- solkey `storageExample5.key`:
```
carol.f1.f2.f3.f4.f5 = 1;
carol.f1.f2.f3.f4.f6 = 2;   (four times)
return carol.f1.f2.f3.f4.f5;
```
A five-deep path written beside a sibling, then a shallow write at `f7` read
back: `find_save_frame` five segments down, four times over. -/
theorem solkey_Rules_storageExample5 :
    (StValue.find
      (StValue.save
        (StValue.save
          (StValue.save
            (StValue.save
              (StValue.save
                (StValue.save .mtSt
                  [.field "f1", .field "f2", .field "f3", .field "f4",
                    .field "f5"] (.prim (.int 1)))
                [.field "f1", .field "f2", .field "f3", .field "f4",
                  .field "f6"] (.prim (.int 2)))
              [.field "f1", .field "f2", .field "f3", .field "f4",
                .field "f6"] (.prim (.int 2)))
            [.field "f1", .field "f2", .field "f3", .field "f4",
              .field "f6"] (.prim (.int 2)))
          [.field "f1", .field "f2", .field "f3", .field "f4",
            .field "f6"] (.prim (.int 2)))
        [.field "f7"] (.prim (.int 3)))
      [.field "f7"]).asInt = 3 := by
  rw [StValue.find_save_same]
  rfl

/-! ### `memoryExample*.key` — the draft's memory examples

These are what the path identities buy.  `addM(mem, ca)` allocates a root and
nothing else; every member of it, primitive or reference, is manufactured by
`readOnAddM` into `default<[α]>` and then by `defaultDef`/`defaultDefIdentity`
into `0` or into `idC(ca, flds · a)`.  Aliasing is decided by `idC`'s
injectivity, which is where the `.key` proofs spend their steps. -/

/-- solkey `memoryExample1.key`: a reference member read out and written
through — the memory twin of `storageExample1`, and an *alias* rather than a
copy, so the later write is the one observed. -/
theorem solkey_Rules_memoryExample1 :
    ∀ (h : List (Nat × MObj)) (mem : Memory) (bob bobAcc : Identity),
      bob ≠ bobAcc →
      (Memory.readIn h
        (.write (.write (.write mem bob age (.prim (.int 19)))
          bobAcc owner (.ident bob)) bob age (.prim (.int 20)))
        (Memory.readId h
          (.write (.write (.write mem bob age (.prim (.int 19)))
            bobAcc owner (.ident bob)) bob age (.prim (.int 20)))
          bobAcc owner)
        age).asPrim = MVal.int 20 := by
  intro h mem bob bobAcc hne
  simp [Memory.readId, MemValue.asIdentity, MemValue.asPrim, hne,
    Ne.symm hne]

/-- solkey `memoryExample4.key`:
```
alice = new Person();
return alice.age;
```
The shortest thing the `new` family says: a primitive member of a root that
was only *added* reads as `0`, with nothing written for it.  `readOnAddM`
then `defaultDef`. -/
theorem solkey_Rules_memoryExample4 :
    ∀ (h : List (Nat × MObj)) (mem : Memory) (ca : Nat) (ty : RefTy),
      (Memory.readIn h (.addM mem ca ty) (.idCC ca) age).asPrim
        = MVal.int 0 := by
  intro h mem ca ty
  simp [MemValue.asPrim]

/-- …and the freshness premise that licenses it: `new(addM(mem, ca), ca)` is
`false`, and `new` at any other root is untouched (`newFromAdd`). -/
theorem solkey_Rules_memoryExample4_new :
    ∀ (h : List (Nat × MObj)) (mem : Memory) (ca cb : Nat) (ty : RefTy),
      ca ≠ cb →
      Memory.new h (.addM mem ca ty) ca = false ∧
        Memory.new h (.addM mem ca ty) cb = Memory.new h mem cb := by
  intro h mem ca cb ty hne
  exact ⟨by simp, by simp [hne]⟩

/-- solkey `memoryExample2.key`:
```
alice = new Person();
alice.balance = 20;
alice.account.balance = 10;
return alice.balance;
```
`alice.account` is not allocated and not written: `readOnAddM` and
`defaultDefIdentity` manufacture `idC(ca, [account])` for it, and the write
through that identity is *elsewhere* than `alice` — which is `idC`'s
injectivity, the step the `.key` proof spends itself on. -/
theorem solkey_Rules_memoryExample2 :
    ∀ (h : List (Nat × MObj)) (mem : Memory) (ca : Nat) (ty : RefTy),
      (Memory.readIn h
        (.write
          (.write (.addM mem ca ty) (.idCC ca) balance (.prim (.int 20)))
          (Memory.readId h
            (.write (.addM mem ca ty) (.idCC ca) balance (.prim (.int 20)))
            (.idCC ca) account)
          balance (.prim (.int 10)))
        (.idCC ca) balance).asPrim = MVal.int 20 := by
  intro h mem ca ty
  simp [Memory.readId, MemValue.asIdentity, MemValue.asPrim]

/-- solkey `memoryExample2-2.key`: the same program with `alice` bound to the
*member* identity `idC(ca, [account])` instead of the root. -/
theorem solkey_Rules_memoryExample2_2 :
    ∀ (h : List (Nat × MObj)) (mem : Memory) (ca : Nat) (ty : RefTy),
      (Memory.readIn h
        (.write
          (.write (.addM mem ca ty) (.idC ca [account]) balance
            (.prim (.int 20)))
          (Memory.readId h
            (.write (.addM mem ca ty) (.idC ca [account]) balance
              (.prim (.int 20)))
            (.idC ca [account]) account)
          balance (.prim (.int 10)))
        (.idC ca [account]) balance).asPrim = MVal.int 20 := by
  intro h mem ca ty
  simp [Memory.readId, MemValue.asIdentity, MemValue.asPrim]

/-- solkey `memoryExample3.key`:
```
alice = new Person();
bob = new Person();
alice.age = 20;
bob.age = 30;
return (alice.age, bob.age);
```
Two roots do not interfere.  The `.key` proof reaches
`idC(cb, nil) = idC(ca, nil)` and discharges it from `\unique`; here that is
`idC`'s injectivity applied to `ca ≠ cb`. -/
theorem solkey_Rules_memoryExample3 :
    ∀ (h : List (Nat × MObj)) (mem : Memory) (ca cb : Nat) (ty : RefTy),
      ca ≠ cb →
      (Memory.readIn h
          (.write (.write (.addM (.addM mem ca ty) cb ty)
            (.idCC ca) age (.prim (.int 20))) (.idCC cb) age
            (.prim (.int 30))) (.idCC ca) age).asPrim = MVal.int 20 ∧
        (Memory.readIn h
          (.write (.write (.addM (.addM mem ca ty) cb ty)
            (.idCC ca) age (.prim (.int 20))) (.idCC cb) age
            (.prim (.int 30))) (.idCC cb) age).asPrim = MVal.int 30 := by
  intro h mem ca cb ty hne
  exact ⟨by simp [MemValue.asPrim, hne, Ne.symm hne],
    by simp [MemValue.asPrim]⟩

/-- solkey `memoryExample5.key`:
```
aliceAcc = new Account();
bobAcc = new Account();
aliceAcc.owner = bobAcc.owner;
aliceAcc.owner.age = 20;
return bobAcc.owner.age;
```
The shallow embedding: assigning a reference member *aliases*, so writing
through Alice's owner is writing through Bob's.  Both sides name the same
manufactured identity `idC(cb, [owner])`. -/
theorem solkey_Rules_memoryExample5 :
    ∀ (h : List (Nat × MObj)) (mem : Memory) (ca cb : Nat) (ty : RefTy),
      ca ≠ cb →
      (Memory.readIn h
        (.write
          (.write (.addM (.addM mem ca ty) cb ty) (.idCC ca) owner
            (.ident (.idC cb [owner])))
          (.idC cb [owner]) age (.prim (.int 20)))
        (.idC cb [owner]) age).asPrim = MVal.int 20 := by
  intro h mem ca cb ty hne
  simp [MemValue.asPrim]

/-- …and the read that produces that identity on both sides:
`read<[Identity]>(addM(addM(mem, ca), cb), idC(cb, nil), owner)` is
`idC(cb, [owner])` by `readOnAddM` and `defaultDefIdentity`. -/
theorem solkey_Rules_memoryExample5_owner :
    ∀ (h : List (Nat × MObj)) (mem : Memory) (ca cb : Nat) (ty : RefTy),
      Memory.readId h (.addM (.addM mem ca ty) cb ty) (.idCC cb) owner
        = .idC cb [owner] := by
  intro h mem ca cb ty
  simp [Memory.readId, MemValue.asIdentity]

/-! ### `problem*.key` and `mainExamples.key` -/

/-- solkey `problem1.key`: `selectSt<[int]>(storeSt(s, balance, 10), balance)`
over an arbitrary `s`. -/
theorem solkey_Rules_problem1 :
    ∀ s : StValue,
      (StValue.selectSt (StValue.storeSt s balance (.prim (.int 10)))
        balance).asInt = 10 := by
  intro s
  simp [StValue.asInt]

/-- solkey `problem2.key`: the same problem, declared twice upstream. -/
theorem solkey_Rules_problem2 :
    ∀ s : StValue,
      (StValue.selectSt (StValue.storeSt s balance (.prim (.int 10)))
        balance).asInt = 10 := by
  intro s
  simp [StValue.asInt]

/-- solkey `mainExamples.key`: the one line of that `\problem` that is not
commented out — `idC(idp1, [f1, f2]) != idC(idp1, [f2, f1])`, the injectivity
of `idC` on which every aliasing step above rests. -/
theorem solkey_Rules_mainExamples :
    ∀ idp1 : Nat, Identity.idC idp1 [f1, f2] ≠ Identity.idC idp1 [f2, f1] := by
  intro idp1
  simp

/-- The commented lines of `mainExamples.key`, as far as the theories reach.
`copySt`/`copyMem` are not modelled (`docs/lean-key-rule-map.md`), so the
three lines over them have no counterpart; every other one is here. -/
example : ∀ (h : List (Nat × MObj)) (mem : Memory) (id1 : Identity)
    (idp1 idp2 : Nat) (ty : RefTy) (flds : List Seg),
    -- `read<[int]>(write(mem, id1, f1, 0), id1, f1) = 0`
    (Memory.readIn h (.write mem id1 f1 (.prim (.int 0))) id1 f1).asPrim
        = MVal.int 0 ∧
      -- `read<[int]>(mtMem, id1, f1) = default(id1, f1)`
      Memory.readIn h .mtMem id1 f1 = .dflt ∧
      -- `! new(addM(mem, idp1), idp1)`
      Memory.new h (.addM mem idp1 ty) idp1 = false ∧
      -- `new(mem, idp2) -> new(write(mem, id1, f1, 0), idp2)`
      (Memory.new h mem idp2 = true →
        Memory.new h (.write mem id1 f1 (.prim (.int 0))) idp2 = true) ∧
      -- `new(mtMem, idp1)`
      Memory.new h .mtMem idp1 = true ∧
      -- `readR<[int]>(write(mem, id1, f1, 0), id1, cons(f1, nil)) = 0`
      (Memory.readR h (.write mem id1 f1 (.prim (.int 0))) id1 [f1]).asPrim
        = MVal.int 0 ∧
      -- `selectSt<[int]>(storeSt(mtSt, f1, 0), f1) = 0`
      (StValue.selectSt (StValue.storeSt .mtSt f1 (.prim (.int 0)))
        f1).asInt = 0 ∧
      -- `selectSt<[int]>(storeSt(mtSt, f1, 0), f2) = selectSt<[int]>(mtSt, f2)`
      StValue.selectSt (StValue.storeSt .mtSt f1 (.prim (.int 0))) f2
        = StValue.selectSt .mtSt f2 ∧
      -- `find<[int]>(save(st, flds12, 0), flds12) = 0`
      (StValue.find (StValue.save .mtSt [f1, f2] (.prim (.int 0)))
        [f1, f2]).asInt = 0 := by
  intro h mem id1 idp1 idp2 ty flds
  refine ⟨by simp [MemValue.asPrim], rfl, by simp, fun hn => by simpa using hn,
    rfl, by simp [MemValue.asPrim], by decide, by decide, ?_⟩
  rw [StValue.find_save_same]; rfl

/-- `read<[int]>(addM(mem, idp1), idC(idp2, flds), f1)` skips the add when the
roots differ — `readAddDifferent`, the `\else` branch of `readOnAddM`. -/
example : ∀ (h : List (Nat × MObj)) (mem : Memory) (idp1 idp2 : Nat)
    (ty : RefTy) (flds : List Seg), idp1 ≠ idp2 →
    Memory.readIn h (.addM mem idp1 ty) (.idC idp2 flds) f1
      = Memory.readIn h mem (.idC idp2 flds) f1 := by
  intro h mem idp1 idp2 ty flds hne
  exact Memory.readAddDifferent h mem idp1 idp2 ty flds f1 hne

/-- `readR` over a two-field path: `readRCons`, then `readREmpty`. -/
example : ∀ (h : List (Nat × MObj)) (mem : Memory) (id1 id2 : Identity),
    Memory.readR h (.write (.write mem id2 f2 (.prim (.int 0))) id1 f1
      (.ident id2)) id1 [f1, f2] = .prim (.int 0) := by
  intro h mem id1 id2
  by_cases hid : id1 = id2
  · subst hid; simp [Memory.readId, MemValue.asIdentity]
  · simp [Memory.readId, MemValue.asIdentity, hid, Ne.symm hid]

/-! ### `keyext.solidity.examples/storage/copyKeepsMapping.key`

The one obligation of the mapping-preserving copy that no `.sol` example can
state: both front ends reject a copy whose type carries a mapping, so the
mapping-preserving half of `save`'s leaf is pinned by a `.key` problem
instead.

The `\unique MapField balances` / `\unique RefField inner` of the `.key`
file are *sorts*, which `Semantics.Seg` does not carry (`Theory/Storage.lean`
dispatches on the value's shape instead), so the shape is fixed here and every
payload is left universally quantified. -/

private abbrev nonce : Seg := .field "nonce"
private abbrev balances : Seg := .field "balances"
private abbrev inner : Seg := .field "inner"
private abbrev ledger : Seg := .field "ledger"
private abbrev ledger2 : Seg := .field "ledger2"

/-- A `ledger`: a `Field nonce`, a `MapField balances`, and a `RefField inner`
holding the same two. -/
private def ledgerVal (n : Int) (bal : List (Int × SVal)) (d : SVal)
    (inN : Int) (inBal : List (Int × SVal)) (inD : SVal) : SVal :=
  SVal.struct
    [("nonce", SVal.int n), ("balances", SVal.map bal d),
     ("inner", SVal.struct
        [("nonce", SVal.int inN), ("balances", SVal.map inBal inD)])]

/-- solkey `copyKeepsMapping.key`:
```
{storage := save(storage, cons(ledger2, nil), find<[StValue]>(storage, cons(ledger, nil)))}
```
`ledger2 = ledger`, read back four ways.  The first two conjuncts are the
value members — `nonce` at the top and through the `RefField` — which the copy
takes from the source.  The last two compare the post-state read, under the
update, with the pre-state read outside it: the target keeps **its own**
mapping entries, at the top and one level down through the `RefField` —
`selectOnSaveEmptyMap` firing at depth 1 and, after `selectOnSaveEmptyRef`,
at depth 2.  (Until the fold of `copyAt` into `save` the file compared the
two post-state reads with themselves; `docs/solkey-feedback.md` records it.) -/
theorem solkey_Rules_copyKeepsMapping :
    ∀ (n1 n2 : Int) (b1 b2 : List (Int × SVal)) (d1 d2 : SVal)
      (i1 i2 : Int) (ib1 ib2 : List (Int × SVal)) (id1 id2 : SVal),
      let st : StValue := .sval (SVal.struct
        [("ledger", ledgerVal n1 b1 d1 i1 ib1 id1),
         ("ledger2", ledgerVal n2 b2 d2 i2 ib2 id2)])
      let upd : StValue := StValue.save st [ledger2] (StValue.find st [ledger])
      (StValue.find upd [ledger2, nonce]).asInt
          = (StValue.find upd [ledger, nonce]).asInt
        ∧ (StValue.find upd [ledger2, inner, nonce]).asInt
          = (StValue.find upd [ledger, inner, nonce]).asInt
        ∧ StValue.find upd [ledger2, balances, .at 1]
          = StValue.find st [ledger2, balances, .at 1]
        ∧ StValue.find upd [ledger2, inner, balances, .at 1]
          = StValue.find st [ledger2, inner, balances, .at 1] := by
  intro n1 n2 b1 b2 d1 d2 i1 i2 ib1 ib2 id1 id2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show ([ledger2, nonce] : List Seg) = [ledger2] ++ [nonce] from rfl,
      StValue.find_save_extends, StValue.find_save_frame _ _ _ _ (by decide)]
    simp [ledgerVal, StValue.find, StValue.selectSt, StValue.svalSelect, lookupBy,
      StValue.asStruct, StValue.isMapping, StValue.isNode, StValue.base]
  · rw [show ([ledger2, inner, nonce] : List Seg) = [ledger2] ++ [inner, nonce] from rfl,
      StValue.find_save_extends, StValue.find_save_frame _ _ _ _ (by decide)]
    simp [ledgerVal, StValue.find, StValue.selectSt, StValue.svalSelect, lookupBy,
      StValue.asStruct, StValue.isMapping, StValue.isNode, StValue.base]
  · rw [show ([ledger2, balances, .at 1] : List Seg) = [ledger2] ++ [balances, .at 1] from rfl,
      StValue.find_save_extends]
    simp [ledgerVal, StValue.find, StValue.selectSt, StValue.svalSelect, lookupBy,
      StValue.asStruct, StValue.isMapping, StValue.base]
  · rw [show ([ledger2, inner, balances, .at 1] : List Seg)
        = [ledger2] ++ [inner, balances, .at 1] from rfl,
      StValue.find_save_extends]
    simp [ledgerVal, StValue.find, StValue.selectSt, StValue.svalSelect, lookupBy,
      StValue.asStruct, StValue.isMapping, StValue.isNode, StValue.base]

/-- The same, as the four members of one `.key` problem read: written value
members from the source, the target's own mappings kept. -/
example :
    ∀ (n1 n2 : Int) (b1 b2 : List (Int × SVal)) (d1 d2 : SVal)
      (i1 i2 : Int) (ib1 ib2 : List (Int × SVal)) (id1 id2 : SVal),
      let st : StValue := .sval (SVal.struct
        [("ledger", ledgerVal n1 b1 d1 i1 ib1 id1),
         ("ledger2", ledgerVal n2 b2 d2 i2 ib2 id2)])
      let upd : StValue := StValue.save st [ledger2] (StValue.find st [ledger])
      StValue.find upd [ledger2, balances, .at 1]
          = StValue.find st [ledger2, balances, .at 1]
        ∧ StValue.find upd [ledger2, inner, balances, .at 1]
          = StValue.find st [ledger2, inner, balances, .at 1] := by
  intro n1 n2 b1 b2 d1 d2 i1 i2 ib1 ib2 id1 id2
  refine ⟨?_, ?_⟩
  · rw [show ([ledger2, balances, .at 1] : List Seg) = [ledger2] ++ [balances, .at 1] from rfl,
      StValue.find_save_extends]
    simp [ledgerVal, StValue.find, StValue.selectSt, StValue.svalSelect, lookupBy,
      StValue.isMapping, StValue.base]
  · rw [show ([ledger2, inner, balances, .at 1] : List Seg)
        = [ledger2] ++ [inner, balances, .at 1] from rfl,
      StValue.find_save_extends]
    simp [ledgerVal, StValue.find, StValue.selectSt, StValue.svalSelect, lookupBy,
      StValue.asStruct, StValue.isMapping, StValue.isNode, StValue.base]

/-- …and it is *not* the source's: the refutation an inverted `isMapping`
branch would fail. -/
example :
    let st : StValue := .sval (SVal.struct
      [("ledger", ledgerVal 1 [(1, SVal.int 11)] (SVal.int 0) 3 [(1, SVal.int 33)] (SVal.int 0)),
       ("ledger2", ledgerVal 2 [(1, SVal.int 22)] (SVal.int 0) 4 [(1, SVal.int 44)] (SVal.int 0))])
    let upd : StValue := StValue.save st [ledger2] (StValue.find st [ledger])
    (StValue.find upd [ledger2, balances, .at 1]).asInt = 22
      ∧ (StValue.find upd [ledger2, inner, balances, .at 1]).asInt = 44 := by
  native_decide

end Rules
end Solkey
end Solidity
