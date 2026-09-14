import Solidity.Evm.Correctness

/-!
# Differential tests and worked instantiations

Executable validation of the compiler on concrete programs, complementing
the preservation theorems of `Evm/Correctness.lean`:

- `diffTest` compiles a block, runs the *official* interpreter
  (`Semantics.execBlock`) and the EVM machine's fuel runner (`Evm.run`)
  side by side, and compares outcome, final storage on every layout
  root, the net ledger and the contract balance. Each
  `example : diffTest … = true := by native_decide` is an end-to-end
  check of parser conventions, compiler, machine, and the storage
  layout at once — including the reverts the compiled guards must
  reproduce (zero divisor, out-of-bounds, `uint` overflow, unfunded
  `transfer`).
- `reprState_exampleEvm` instantiates the `ReprState` invariant for a
  concrete initial state, and the theorems at the bottom apply
  `compile_preserves_ok` / `compile_preserves_revert` to concrete
  programs — demonstrating the preservation theorems are usable, not
  just provable.
-/

namespace Solidity
namespace Evm
namespace Examples

open Semantics

/-- Storage layout used by the examples: the primitive uint globals of
`StandardExample.sol` (`storageOriginFor` marks them `global`), plus its two
mapping roots (`balances : uint => uint`, `flags : uint => bool`). -/
def exampleLayout : List Name :=
  ["total", "age", "owner", "balance", "balances", "flags", "values",
   "alice", "wallet"]

/-- Matching initial interpreter state: all primitive roots zero, the
mappings empty with zero/false defaults. -/
def exampleEvmStore : State :=
  { storage :=
      [ ("total", SVal.int 0),
        ("age", SVal.int 0),
        ("owner", SVal.int 0),
        ("balance", SVal.int 0),
        ("balances", SVal.map [] (SVal.int 0)),
        ("flags", SVal.map [] (SVal.bool false)),
        ("values", SVal.array []),
        ("alice", SVal.struct
          [ ("account", SVal.struct
              [ ("balance", SVal.int 0),
                ("token", SVal.struct [("value", SVal.int 0)]) ]),
            ("age", SVal.int 0) ]),
        ("wallet", SVal.struct
          [ ("owner", SVal.int 0),
            ("stash", SVal.map [] (SVal.int 0)) ]) ] }

/-- The machine's all-zero storage represents `exampleEvmStore`. -/
def emptyStore : Store := []

/-! ## The differential checker -/

def svalMatches (sv : SVal) (w : Word) : Bool :=
  match sv with
  | SVal.int v => v == (w.toNat : Int)
  | SVal.bool b => w == wBool b
  | _ => false

/-- A mapping root agrees when every listed (in-range) entry and the
first few default keys read back the same word from the derived slot. -/
def mapAgrees (i : Nat) (entries : List (Int × SVal)) (dflt : SVal)
    (st : Store) : Bool :=
  (entries.all fun (k, _) =>
    if 0 ≤ k ∧ k < keyBoundI then
      svalMatches ((lookupBy k entries).getD dflt)
        (st.read (mapSlotW (slotWord i) (BitVec.ofNat 256 k.toNat)))
    else true) &&
  ((List.range 5).all fun kn =>
    svalMatches ((lookupBy (kn : Int) entries).getD dflt)
      (st.read (mapSlotW (slotWord i) (BitVec.ofNat 256 kn))))

/-- An array root agrees when the length word sits at the direct slot
and every element reads back from its derived slot. -/
def arrayAgrees (i : Nat) (elems : List SVal) (st : Store) : Bool :=
  (st.read (slotWord i) == BitVec.ofNat 256 elems.length) &&
  ((List.range elems.length).all fun j =>
    svalMatches (elems.getD j (SVal.int 0))
      (st.read (mapSlotW (slotWord i) (BitVec.ofNat 256 j))))

/-- A struct field agrees when primitive; non-primitive fields carry
no machine claim. -/
def fieldAgrees (sv : SVal) (w : Word) : Bool :=
  match sv with
  | SVal.int v => v == (w.toNat : Int)
  | SVal.bool b => w == wBool b
  | _ => true

/-- A struct root agrees field-wise at the derived slots. -/
def structAgrees (i : Nat) (sfields : List (Name × SVal))
    (st : Store) : Bool :=
  (List.range sfields.length).all fun j =>
    fieldAgrees (sfields.getD j ("", SVal.int 0)).2
      (st.read (mapSlotW (slotWord i) (BitVec.ofNat 256 j)))

def storageAgrees (L : List Name) (s : State) (st : Store) : Bool :=
  (List.range L.length).all fun i =>
    match L[i]? with
    | some name =>
        match lookupBy name s.storage with
        | some (SVal.map entries dflt) => mapAgrees i entries dflt st
        | some (SVal.array elems) => arrayAgrees i elems st
        | some (SVal.struct sfields) => structAgrees i sfields st
        | some sv => svalMatches sv (st.read (slotWord i))
        | none => false
    | none => false

/-- The net ledger agrees when every (in-range) entry's balance reads
back from its net-ledger slot. -/
def netAgrees (s : State) (st : Store) : Bool :=
  s.net.all fun (a, _) =>
    if 0 ≤ a ∧ a < keyBoundI then
      (0 ≤ s.getNet a) &&
      (s.getNet a ==
        ((st.read (netSlotW (BitVec.ofNat 256 a.toNat))).toNat : Int))
    else true

/-- The contract balance agrees when it reads back from `balanceSlotW`. -/
def balanceAgrees (s : State) (st : Store) : Bool :=
  (0 ≤ s.selfBalance) &&
    (s.selfBalance == ((st.read balanceSlotW).toNat : Int))

/-- Compile `b`, run interpreter and machine, compare: a normal stop
must reproduce every storage root, every net-ledger entry and the
contract balance; a source revert must become a machine `REVERT`. -/
def diffTest (L : List Name) (b : Block) (s0 : State) (st0 : Store)
    (fuel : Nat := 100000) : Bool :=
  match compileProgram L b with
  | none => false
  | some c =>
      match execBlock s0 b, run c fuel ⟨0, [], st0⟩ with
      | .ok s', .ok _ st' =>
          storageAgrees L s' st' && netAgrees s' st' && balanceAgrees s' st'
      | .error .revert, .reverted => true
      | _, _ => false

def diff (b : Block) : Bool :=
  diffTest exampleLayout b exampleEvmStore emptyStore

/-! ## Differential test suite -/

-- Straight-line arithmetic into storage.
example : diff (solbox!{ total = 1 + 2 }).stmts = true := by native_decide

example : diff (solbox!{ total = 7 - 3; age = 6 * 7 }).stmts = true := by
  native_decide

-- Stack locals: declaration, reads under temporaries, overwriting.
example : diff (solbox!{
    uint x = 10;
    uint y = 4;
    total = x * y - 2;
    x = x + 1;
    age = x }).stmts = true := by native_decide

-- Division and modulus (with in-range operands).
example : diff (solbox!{ total = 17 / 5; age = 17 % 5 }).stmts = true := by
  native_decide

-- Division by zero must revert on both sides.
example : diff (solbox!{ uint x = 0; total = 10 / x }).stmts = true := by
  native_decide

-- Exponentiation.
example : diff (solbox!{ total = 2 ** 10 }).stmts = true := by
  native_decide

-- Branching on comparisons.
example : diff (solbox!{
    uint x = 5;
    if ((x < 10)) { total = 1 } else { total = 2 } }).stmts = true := by
  native_decide

example : diff (solbox!{
    uint x = 50;
    if ((x < 10)) { total = 1 } else { total = 2 } }).stmts = true := by
  native_decide

-- Nested control flow writing several roots.
example : diff (solbox!{
    uint x = 3;
    if ((x == 3)) {
      total = 1;
      if ((x <= 2)) { age = 10 } else { age = 20 }
    } else {
      total = 0
    };
    owner = x }).stmts = true := by native_decide

-- Short-circuit `||` guards the division (no revert).
example : diff (solbox!{
    uint x = 0;
    if (((x == 0) || ((10 / x) > 1))) { total = 5 } else { total = 6 }
    }).stmts = true := by native_decide

-- Short-circuit `&&`.
example : diff (solbox!{
    uint x = 1;
    if (((x == 0) && ((10 / x) > 1))) { total = 5 } else { total = 6 }
    }).stmts = true := by native_decide

-- `require`: passing and reverting runs.
example : diff (solbox!{ require((1 < 2)); total = 7 }).stmts = true := by
  native_decide

example : diff (solbox!{ require((2 < 1)); total = 7 }).stmts = true := by
  native_decide

-- `assert` and explicit `revert`.
example : diff (solbox!{ assert((3 <= 3)); balance = 9 }).stmts = true := by
  native_decide

example : diff (solbox!{ total = 1; revert() }).stmts = true := by
  native_decide

-- Compound assignment on storage roots.
example : diff (solbox!{
    total = 5; total += 37; total -= 2; total *= 2; total /= 4
    }).stmts = true := by native_decide

-- Equality / inequality.
example : diff (solbox!{
    uint x = 4;
    if (((3 <= 3) && (x != 5))) { total = 1 } else { total = 2 }
    }).stmts = true := by native_decide

-- Reads of storage roots inside expressions.
example : diff (solbox!{
    total = 6; age = total * total; balance = age + total
    }).stmts = true := by native_decide

-- Mapping writes and reads (uint => uint).
example : diff (solbox!{
    balances[1] = 42; total = balances[1] + balances[0]
    }).stmts = true := by native_decide

-- Mapping keys and values computed from locals and other entries.
example : diff (solbox!{
    uint k = 3;
    balances[k] = k + 1;
    balances[2] = balances[k] * 2;
    total = balances[2] + balances[3]
    }).stmts = true := by native_decide

-- Overwriting an entry; entry read under temporaries.
example : diff (solbox!{
    balances[7] = 10;
    balances[7] = balances[7] + 5;
    total = 100 - balances[7]
    }).stmts = true := by native_decide

-- Compound assignment on a mapping entry.
example : diff (solbox!{
    balances[5] = 10; balances[5] += 32; total = balances[5]
    }).stmts = true := by native_decide

-- Boolean mapping (uint => bool), branching on an entry.
example : diff (solbox!{
    flags[7] = (1 < 2);
    if ((flags[7])) { total = 1 } else { total = 2 };
    if ((flags[8])) { age = 1 } else { age = 2 }
    }).stmts = true := by native_decide

-- A reverting run leaves the machine reverting too, mapping writes
-- included.
example : diff (solbox!{
    balances[1] = 5; require((balances[1] == 6)); total = 9
    }).stmts = true := by native_decide

-- Arrays: push, indexed reads, length.
example : diff (solbox!{
    values.push(5);
    values.push(7);
    total = values[0] + values[1];
    age = values.length
    }).stmts = true := by native_decide

-- Indexed writes and compound assignment on elements.
example : diff (solbox!{
    values.push(1);
    values.push(2);
    values[0] = values[1] * 10;
    values[1] += 5;
    total = values[0] + values[1]
    }).stmts = true := by native_decide

-- A valueless push appends the default; pop shortens.
example : diff (solbox!{
    values.push();
    values.push(9);
    values.pop();
    total = values.length + values[0]
    }).stmts = true := by native_decide

-- Out-of-bounds read reverts on both sides.
example : diff (solbox!{
    values.push(1); total = values[3]
    }).stmts = true := by native_decide

-- Out-of-bounds write reverts on both sides (after the right-hand
-- side evaluated).
example : diff (solbox!{ values[0] = 4 }).stmts = true := by
  native_decide

-- Pop of an empty array reverts on both sides.
example : diff (solbox!{
    values.push(1); values.pop(); values.pop()
    }).stmts = true := by native_decide

-- Push after pop overwrites the stale slot.
example : diff (solbox!{
    values.push(3);
    values.pop();
    values.push(8);
    total = values[0];
    age = values.length
    }).stmts = true := by native_decide

-- Struct roots: primitive field writes, reads, compound assignment.
example : diff (solbox!{
    alice.age = 4;
    wallet.owner = alice.age + 1;
    alice.age += 2;
    total = alice.age * wallet.owner
    }).stmts = true := by native_decide

-- Struct fields interacting with locals, mappings, and control flow.
example : diff (solbox!{
    uint x = 10;
    alice.age = x + 4;
    balances[2] = alice.age;
    if ((alice.age > 10)) { wallet.owner = 1 } else { wallet.owner = 2 };
    total = balances[2] + wallet.owner
    }).stmts = true := by native_decide

-- A revert after a struct-field write leaves both sides reverting.
example : diff (solbox!{
    alice.age = 7; require((alice.age == 8)); total = 1
    }).stmts = true := by native_decide

/-! ## Transfers

The interpreter's `net` ledger lives in the machine's storage at
`netSlotW`. Debits only, so transfer tests start from a state with
positive balances (and a machine store carrying the matching words). -/

def transferState : State :=
  -- Funded: the interpreter checks and debits the contract balance,
  -- and so does the compiled code (`transferTail` reads and writes the
  -- balance word at `balanceSlotW`).
  { exampleEvmStore with
      net := [((3 : Int), (100 : Int)), (7, 50)],
      selfBalance := 1000000000 }

def transferStore0 : Store :=
  [ (netSlotW (BitVec.ofNat 256 3), BitVec.ofNat 256 100),
    (netSlotW (BitVec.ofNat 256 7), BitVec.ofNat 256 50),
    (balanceSlotW, BitVec.ofNat 256 1000000000) ]

def diffT (b : Block) : Bool :=
  diffTest exampleLayout b transferState transferStore0

-- A plain transfer debits the recipient's ledger entry.
example : diffT (solbox!{
    uint to = 3;
    to.transfer(30)
    }).stmts = true := by native_decide

-- Transfers interleaved with storage writes; amount from storage.
example : diffT (solbox!{
    uint to = 7;
    total = 20;
    to.transfer(total);
    to.transfer(5);
    balance = total + 1
    }).stmts = true := by native_decide

-- A transfer before a revert still reverts on both sides.
example : diffT (solbox!{
    uint to = 3;
    to.transfer(10);
    require((1 == 2))
    }).stmts = true := by native_decide

-- Insufficient balance: the interpreter reverts (the EVM's value-transfer
-- check), and so does the compiled guard on the balance word.
def poorState : State :=
  { exampleEvmStore with net := [((3 : Int), (100 : Int))], selfBalance := 5 }

def poorStore0 : Store :=
  [ (netSlotW (BitVec.ofNat 256 3), BitVec.ofNat 256 100),
    (balanceSlotW, BitVec.ofNat 256 5) ]

def diffP (b : Block) : Bool :=
  diffTest exampleLayout b poorState poorStore0

example : diffP (solbox!{
    uint to = 3;
    to.transfer(6)
    }).stmts = true := by native_decide

-- Exactly the balance still goes through; one more unit after it reverts.
example : diffP (solbox!{
    uint to = 3;
    to.transfer(5);
    total = 1
    }).stmts = true := by native_decide

example : diffP (solbox!{
    uint to = 3;
    to.transfer(5);
    to.transfer(1)
    }).stmts = true := by native_decide

/-! ## Checked `uint` arithmetic

`+`, `-`, `*` at `uint` revert on overflow in the source semantics
(`checkArith`); the compiled code guards them (`checkedOpCode`) and
reverts at the same programs. Boundary values go through on both
sides. -/

-- Addition wrapping past `2^256 - 1`.
example : diff (solbox!{ uint x = 2 ** 255; total = x + x }).stmts = true := by
  native_decide

-- Subtraction below zero.
example : diff (solbox!{ uint x = 0; total = x - 1 }).stmts = true := by
  native_decide

-- Multiplication wrapping.
example : diff (solbox!{ uint x = 2 ** 255; total = x * 2 }).stmts = true := by
  native_decide

-- Compound forms on a stack local and on a storage root.
example : diff (solbox!{ uint x = 2 ** 255; x += x; total = x }).stmts = true := by
  native_decide

example : diff (solbox!{ total = 2 ** 255; total *= 2 }).stmts = true := by
  native_decide

-- Boundary successes: `2^256 - 1` is representable, `x - x` is `0`, a
-- zero factor never overflows.
example : diff (solbox!{
    uint x = 2 ** 255; total = x - 1 + x; age = x - x; balance = 5 * age
    }).stmts = true := by native_decide

/-! ## Function calls, inlined then compiled

Calls mean their inlining (`SolidityJudgment.checkInlined`), so the
differential test for a call-bearing block runs both sides on
`inlineBlock depth b` — exactly what `compileProgramInlined`
compiles. -/

def diffInlined (depth : Nat) (b : Block) : Bool :=
  diff (SoliditySyntax.inlineBlock depth b)

-- `total = addOne(4)` — one expansion.
example : diffInlined 8
    [Stmt.callStmt (some (SoliditySyntax.rootPlace "total")) "addOne"
      [SoliditySyntax.intLitExpr 4]] = true := by native_decide

-- One call's result (via a storage root) feeds the next call.
example : diffInlined 8
    [ Stmt.callStmt (some (SoliditySyntax.rootPlace "age")) "addOne"
        [SoliditySyntax.intLitExpr 4],
      Stmt.callStmt (some (SoliditySyntax.rootPlace "total")) "double"
        [SoliditySyntax.rootExpr "age"] ] = true := by native_decide

-- `inc2` itself calls `addOne` twice — nested expansion.
example : diffInlined 8
    [Stmt.callStmt (some (SoliditySyntax.rootPlace "total")) "inc2"
      [SoliditySyntax.intLitExpr 4]] = true := by native_decide

-- Call result into a mapping entry, argument reading another entry.
example : diffInlined 8
    ((solbox!{ balances[1] = 10 }).stmts ++
      [Stmt.callStmt
        (some (SoliditySyntax.indexPlace
          (SoliditySyntax.rootExpr "balances")
          (SoliditySyntax.intLitExpr 2))) "double"
        [SoliditySyntax.indexExpr (SoliditySyntax.rootExpr "balances")
          (SoliditySyntax.intLitExpr 1)]]) = true := by native_decide

-- Out of fuel: the residual `callStmt` is outside the fragment, so
-- compilation refuses (no claim is made) — the diff test fails closed.
example : diffInlined 0
    [Stmt.callStmt (some (SoliditySyntax.rootPlace "total")) "addOne"
      [SoliditySyntax.intLitExpr 4]] = false := by native_decide

/-! ## Instantiating the preservation theorems -/

/-- The concrete initial state is represented by the all-zero machine
storage — so the preservation theorems apply to it. -/
theorem reprState_exampleEvm :
    ReprState exampleLayout [] exampleEvmStore [] emptyStore where
  len := rfl
  nodup := List.nodup_nil
  disj := by intro n hn; cases hn
  locals := by intro i n h; simp at h
  rootsEnv := by intro n _; rfl
  roots := by
    intro i n h
    match i with
    | 0 =>
        refine ⟨SVal.int 0, ?_, ?_⟩
        · have hn : n = "total" := by
            simpa [exampleLayout] using h.symm
          subst hn; rfl
        · simp [ReprRoot, ReprSVal, Store.read, lookupBy, emptyStore]
    | 1 =>
        refine ⟨SVal.int 0, ?_, ?_⟩
        · have hn : n = "age" := by
            simpa [exampleLayout] using h.symm
          subst hn; rfl
        · simp [ReprRoot, ReprSVal, Store.read, lookupBy, emptyStore]
    | 2 =>
        refine ⟨SVal.int 0, ?_, ?_⟩
        · have hn : n = "owner" := by
            simpa [exampleLayout] using h.symm
          subst hn; rfl
        · simp [ReprRoot, ReprSVal, Store.read, lookupBy, emptyStore]
    | 3 =>
        refine ⟨SVal.int 0, ?_, ?_⟩
        · have hn : n = "balance" := by
            simpa [exampleLayout] using h.symm
          subst hn; rfl
        · simp [ReprRoot, ReprSVal, Store.read, lookupBy, emptyStore]
    | 4 =>
        refine ⟨SVal.map [] (SVal.int 0), ?_, ?_⟩
        · have hn : n = "balances" := by
            simpa [exampleLayout] using h.symm
          subst hn; rfl
        · intro k _ _
          simp [ReprSVal, Store.read, lookupBy, emptyStore]
    | 5 =>
        refine ⟨SVal.map [] (SVal.bool false), ?_, ?_⟩
        · have hn : n = "flags" := by
            simpa [exampleLayout] using h.symm
          subst hn; rfl
        · intro k _ _
          simp [ReprSVal, Store.read, lookupBy, emptyStore, wBool]
    | 6 =>
        refine ⟨SVal.array [], ?_, ?_⟩
        · have hn : n = "values" := by
            simpa [exampleLayout] using h.symm
          subst hn; rfl
        · refine ⟨Nat.zero_le _, rfl, ?_⟩
          intro j hj
          exact absurd hj (by simp)
    | 7 =>
        refine ⟨SVal.struct
          [ ("account", SVal.struct
              [ ("balance", SVal.int 0),
                ("token", SVal.struct [("value", SVal.int 0)]) ]),
            ("age", SVal.int 0) ], ?_, ?_⟩
        · have hn : n = "alice" := by
            simpa [exampleLayout] using h.symm
          subst hn; rfl
        · refine ⟨by decide, ?_⟩
          intro j hj
          match j with
          | 0 => exact trivial
          | 1 => simp [ReprField, Store.read, lookupBy, emptyStore]
          | j + 2 =>
              simp only [List.length_cons, List.length_nil] at hj
              omega
    | 8 =>
        refine ⟨SVal.struct
          [ ("owner", SVal.int 0),
            ("stash", SVal.map [] (SVal.int 0)) ], ?_, ?_⟩
        · have hn : n = "wallet" := by
            simpa [exampleLayout] using h.symm
          subst hn; rfl
        · refine ⟨by decide, ?_⟩
          intro j hj
          match j with
          | 0 => simp [ReprField, Store.read, lookupBy, emptyStore]
          | 1 => exact trivial
          | j + 2 =>
              simp only [List.length_cons, List.length_nil] at hj
              omega
    | i + 9 => simp [exampleLayout] at h
  net := by
    intro a _ _
    exact ⟨Int.le_refl 0, (by decide : (0 : Int) < wordSizeI), rfl⟩
  balance := ⟨Int.le_refl 0, (by decide : (0 : Int) < wordSizeI), rfl⟩
  layoutNodup := by decide
  layoutSmall := by
    simp only [exampleLayout, List.length_cons, List.length_nil, layoutBound]
    omega

/-- Boolean projections of `Res` outcomes (`Res State` carries no
`DecidableEq`, so the theorem hypotheses are established through these
and `native_decide`). -/
def isOkR {α : Type} : Res α → Bool
  | .ok _ => true
  | _ => false

def isRevertR {α : Type} : Res α → Bool
  | .error .revert => true
  | _ => false

theorem eq_revert_of_isRevertR {α : Type} {x : Res α}
    (h : isRevertR x = true) : x = .error .revert := by
  cases x with
  | ok a => simp [isRevertR] at h
  | error e =>
      cases e
      · rfl
      · simp [isRevertR] at h

/-- A program the bounded semantics completes on. -/
def okProg : Block :=
  (solbox!{ uint x = 6; total = x * 7; require((total == 42)) }).stmts

/-- A program that reverts (`require` of a false condition). -/
def revertProg : Block :=
  (solbox!{ uint x = 1; require((x == 2)); total = 9 }).stmts

/-- `compile_preserves_ok`, instantiated: for any successful
compilation of `okProg`, the official interpreter's result is mirrored
by the machine run of the compiled code. -/
theorem okProg_preserved :
    ∀ code, compileProgram exampleLayout okProg = some code →
      ∃ s', execBlock exampleEvmStore okProg = .ok s' ∧
        ∃ Γ' σ' st',
          Steps code ⟨0, [], emptyStore⟩ ⟨code.length, σ', st'⟩ ∧
            ReprState exampleLayout Γ' s' σ' st' := by
  intro code hc
  cases hexec : execWBlock exampleEvmStore okProg with
  | error e =>
      exfalso
      have hok : isOkR (execWBlock exampleEvmStore okProg) = true := by
        native_decide
      rw [hexec] at hok
      simp [isOkR] at hok
  | ok s' =>
      obtain ⟨hofficial, hmachine⟩ :=
        compile_preserves_ok hc hexec reprState_exampleEvm
      exact ⟨s', hofficial, hmachine⟩

/-- `compile_preserves_revert`, instantiated: the compiled `revertProg`
reaches a `REVERT` instruction on the machine, mirroring the
interpreter's revert. -/
theorem revertProg_preserved :
    ∀ code, compileProgram exampleLayout revertProg = some code →
      execBlock exampleEvmStore revertProg = .error .revert ∧
        Reverting code ⟨0, [], emptyStore⟩ := by
  intro code hc
  exact compile_preserves_revert hc
    (eq_revert_of_isRevertR (by native_decide)) reprState_exampleEvm

/-- An overflowing program: `x + x` at `x = 2^255`. -/
def overflowProg : Block :=
  (solbox!{ uint x = 2 ** 255; total = x + x }).stmts

/-- `compile_preserves_revert` on an arithmetic overflow: the source
semantics reverts (`checkArith`), and the compiled overflow guard
reaches `REVERT`. -/
theorem overflowProg_preserved :
    ∀ code, compileProgram exampleLayout overflowProg = some code →
      execBlock exampleEvmStore overflowProg = .error .revert ∧
        Reverting code ⟨0, [], emptyStore⟩ := by
  intro code hc
  exact compile_preserves_revert hc
    (eq_revert_of_isRevertR (by native_decide)) reprState_exampleEvm

/-- A transfer the contract cannot fund: `exampleEvmStore` has balance `0`. -/
def transferRevertProg : Block :=
  (solbox!{ uint to = 3; to.transfer(1) }).stmts

/-- `compile_preserves_revert` on an insufficient balance: the source
semantics reverts, and the compiled balance guard reaches `REVERT`. -/
theorem transferRevertProg_preserved :
    ∀ code, compileProgram exampleLayout transferRevertProg = some code →
      execBlock exampleEvmStore transferRevertProg = .error .revert ∧
        Reverting code ⟨0, [], emptyStore⟩ := by
  intro code hc
  exact compile_preserves_revert hc
    (eq_revert_of_isRevertR (by native_decide)) reprState_exampleEvm

/-- A call-bearing program: `total = inc2(40)` (which itself calls
`addOne` twice). Its meaning is its inlining. -/
def callProg : Block :=
  [Stmt.callStmt (some (SoliditySyntax.rootPlace "total")) "inc2"
    [SoliditySyntax.intLitExpr 40]]

/-- `compileInlined_preserves_ok`, instantiated on `callProg`: the
official interpreter's run of the inlined program is mirrored by the
machine run of the code `compileProgramInlined` produces. -/
theorem callProg_preserved :
    ∀ code, compileProgramInlined exampleLayout 8 callProg = some code →
      ∃ s', execBlock exampleEvmStore
          (SoliditySyntax.inlineBlock 8 callProg) = .ok s' ∧
        ∃ Γ' σ' st',
          Steps code ⟨0, [], emptyStore⟩ ⟨code.length, σ', st'⟩ ∧
            ReprState exampleLayout Γ' s' σ' st' := by
  intro code hc
  cases hexec : execWBlock exampleEvmStore
      (SoliditySyntax.inlineBlock 8 callProg) with
  | error e =>
      exfalso
      have hok : isOkR (execWBlock exampleEvmStore
          (SoliditySyntax.inlineBlock 8 callProg)) = true := by
        native_decide
      rw [hexec] at hok
      simp [isOkR] at hok
  | ok s' =>
      obtain ⟨hofficial, hmachine⟩ :=
        compileInlined_preserves_ok hc hexec reprState_exampleEvm
      exact ⟨s', hofficial, hmachine⟩

/-! ## Judgment transfer, instantiated

The bounded checkers `judgeW`/`revertW` are decided by `native_decide`;
`judgment_transfer` then hands over both the official
`SolidityJudgment.Holds` verdict and the machine-level reading in one
step — the "sol! judgments hold on the machine" workflow. -/

/-- `⟨total = 21; total += 21⟩ (total == 42)`. -/
def judgProg : Block := (solbox!{ total = 21; total += 21 }).stmts
def judgPost : WrappedExpr := sexpr!{ (total == 42) }

theorem judg_transferred :
    ∀ code, compileJudgment exampleLayout judgProg judgPost = some code →
      (SolidityJudgment.mk ⟨.diamond, judgProg⟩ judgPost).Holds
          exampleEvmStore ∧
        ∃ σ' st', Steps code ⟨0, [], emptyStore⟩
          ⟨code.length, 1 :: σ', st'⟩ :=
  fun _ hc =>
    judgment_transfer hc (by native_decide) reprState_exampleEvm .diamond

/-- A judgment over a mapping: `⟨balances[3] = 40; balances[3] += 2⟩
(balances[3] == 42)`. -/
def judgMapProg : Block :=
  (solbox!{ balances[3] = 40; balances[3] += 2 }).stmts
def judgMapPost : WrappedExpr := sexpr!{ (balances[3] == 42) }

theorem judgMap_transferred :
    ∀ code,
      compileJudgment exampleLayout judgMapProg judgMapPost = some code →
      (SolidityJudgment.mk ⟨.diamond, judgMapProg⟩ judgMapPost).Holds
          exampleEvmStore ∧
        ∃ σ' st', Steps code ⟨0, [], emptyStore⟩
          ⟨code.length, 1 :: σ', st'⟩ :=
  fun _ hc =>
    judgment_transfer hc (by native_decide) reprState_exampleEvm .diamond

/-- A judgment over an array: `⟨values.push(40); values[0] += 2⟩
(values[0] == 42)`. -/
def judgArrProg : Block :=
  (solbox!{ values.push(40); values[0] += 2 }).stmts
def judgArrPost : WrappedExpr := sexpr!{ (values[0] == 42) }

theorem judgArr_transferred :
    ∀ code,
      compileJudgment exampleLayout judgArrProg judgArrPost = some code →
      (SolidityJudgment.mk ⟨.diamond, judgArrProg⟩ judgArrPost).Holds
          exampleEvmStore ∧
        ∃ σ' st', Steps code ⟨0, [], emptyStore⟩
          ⟨code.length, 1 :: σ', st'⟩ :=
  fun _ hc =>
    judgment_transfer hc (by native_decide) reprState_exampleEvm .diamond

/-- A judgment over a struct root: `⟨alice.age = 40; alice.age += 2⟩
(alice.age == 42)`. -/
def judgStructProg : Block :=
  (solbox!{ alice.age = 40; alice.age += 2 }).stmts
def judgStructPost : WrappedExpr := sexpr!{ (alice.age == 42) }

theorem judgStruct_transferred :
    ∀ code,
      compileJudgment exampleLayout judgStructProg judgStructPost
        = some code →
      (SolidityJudgment.mk ⟨.diamond, judgStructProg⟩
          judgStructPost).Holds exampleEvmStore ∧
        ∃ σ' st', Steps code ⟨0, [], emptyStore⟩
          ⟨code.length, 1 :: σ', st'⟩ :=
  fun _ hc =>
    judgment_transfer hc (by native_decide) reprState_exampleEvm .diamond

/-- A box judgment validated by a revert:
`[require((1 == 2)); total = 5] (total == 5)` holds vacuously, and the
machine reaches `REVERT`. -/
def judgRevProg : Block := (solbox!{ require((1 == 2)); total = 5 }).stmts
def judgRevPost : WrappedExpr := sexpr!{ (total == 5) }

theorem judgRev_transferred :
    ∀ code,
      compileJudgment exampleLayout judgRevProg judgRevPost = some code →
      (SolidityJudgment.mk ⟨.box, judgRevProg⟩ judgRevPost).Holds
          exampleEvmStore ∧
        Reverting code ⟨0, [], emptyStore⟩ :=
  fun _ hc =>
    judgment_transfer_revert hc (by native_decide) reprState_exampleEvm

/-- A call-bearing judgment, inlined then transferred:
`⟨total = inc2(40)⟩ (total == 42)` — the judgment's meaning is its
inlining (`checkInlined`), and that is exactly what is compiled. -/
theorem judgCall_transferred :
    ∀ code,
      compileJudgment exampleLayout
        (SoliditySyntax.inlineBlock 8 callProg) judgPost = some code →
      (SolidityJudgment.mk
          ⟨.diamond, SoliditySyntax.inlineBlock 8 callProg⟩
          judgPost).Holds exampleEvmStore ∧
        ∃ σ' st', Steps code ⟨0, [], emptyStore⟩
          ⟨code.length, 1 :: σ', st'⟩ :=
  fun _ hc =>
    judgment_transfer hc (by native_decide) reprState_exampleEvm .diamond

end Examples
end Evm
end Solidity
