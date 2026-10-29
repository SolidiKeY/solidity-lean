import Solidity.Syntax.Scoped
import Solidity.Roadmap.Evm

/-!
# The stipend cost rule (decision G06 Q3)

A `transfer` or `send` to an instance of the compiled system forwards
exactly the 2300-gas stipend, so whether it succeeds depends on the gas of
the recipient's `receive`/fallback body.  The second-round decision fixes a
**compiler-independent source rule**: the source semantics fails every such
payment whose body the rule does not admit; the compiler must make every
admitted body complete within the stipend (G06's `StipendRule.Fitted`), and
make every other body fail when entered with at most the stipend
(`Enforced`).  The rule assumes cold (EIP-2929) access costs.

The rule reads the scoped source AST (`Solidity/Syntax/Scoped.lean`) and
changes nothing in it.  A body is admitted when it is **storage-free,
call-free and straight-line**, and **small**:

- **Rejected outright** (`cost = none`): any storage access, read or write;
  under cold costs one `SLOAD` is 2100 of the 2300, and EIP-2200 makes
  every `SSTORE` fail at 2300 gas or less remaining, so no body that writes
  storage can ever succeed.  Also any memory object or memory read
  (allocation and expansion grow with sizes the rule cannot bound), hashing,
  payments and external calls (`transfer`, `send`, `try`), loops,
  recursion, storage aliases and array operations.
- **Admitted with a cost**: local declarations and assignments, `require`,
  `assert`, `revert` (with literal data), `if`/`else` (the costlier branch
  counted), blocks, and internal calls of non-recursive functions with no
  or one value return (their body counted at the call); expressions over literals, locals and the
  environment values (`msg.sender`, `msg.value`, `block.timestamp`,
  `address(this)`, `address(this).balance`, all warm opcodes) with
  arithmetic other than `**`, comparisons, `?:` and `addmod`/`mulmod`.
  Compound assignments and increments (`x += 1`, `i++`) are rejected even
  on locals: conservative, since their target may be storage or memory.
- **Also rejected**: `**` (`EXP` costs 50 gas per exponent byte, and the
  checked operator loops over the exponent's bits), and internal calls
  whose return is a memory object, a storage alias or a tuple.
- **Cost**: one unit per evaluated node and statement, the costlier branch
  of each conditional; admitted when `unit · cost + reserve ≤ 2300`, with
  `unit = 50` and `reserve = 300` (`osakaCold`): at most 40 units.  The
  constants are generous per node (a checked addition with its overflow
  test is about 40 gas in solc's legacy output) and reserve the entry,
  dispatch and return.  They are part of the rule's definition: changing
  them changes the source semantics, so G43 must prove the compiler fits
  them, not retune them.
-/

namespace Solidity.Stipend

open Solidity.Roadmap.Evm (StipendRule Pin pinned)

variable {C : Contract}

/-- The constants of the rule. -/
structure CostModel where
  /-- Gas charged per evaluated node or statement. -/
  unit : Nat
  /-- Gas kept for the entry, dispatch and return. -/
  reserve : Nat

/-- The model of the decision: Osaka with cold access costs. -/
def osakaCold : CostModel := ⟨50, 300⟩

/-! ## Cost of expressions and statements -/

/-- Optional costs add; a rejected part rejects the whole. -/
def addC (a b : Option Nat) : Option Nat := do let x ← a; let y ← b; some (x + y)

def maxC (a b : Option Nat) : Option Nat := do let x ← a; let y ← b; some (max x y)

/-- The cost of a value: its nodes, or `none` when it reads storage or
memory or hashes. -/
def valCost {Γ : Ctx} : {p : PrimTy} → Val C Γ p → Option Nat
  | _, .simple _ => some 1
  | _, .binop op _ _ a b =>
    -- `EXP` costs `10 + 50` per exponent byte, and checked `**` loops over
    -- the exponent's bits: no node bound covers it.
    if op = .pow ∨ op = .powW then none else addC (some 1) (addC (valCost a) (valCost b))
  | _, .unop _ _ _ a => addC (some 1) (valCost a)
  | _, .ternary c a b => addC (some 1) (addC (valCost c) (maxC (valCost a) (valCost b)))
  | _, .modular _ a b k => addC (some 1) (addC (valCost a) (addC (valCost b) (valCost k)))
  | _, .read _ | _, .readMem _ | _, .len _ _ | _, .mlen _ _ | _, .hash _ _ _ => none

def argsCost {Γ : Ctx} : {ps : Ctx} → Args C Γ ps → Option Nat
  | _, .nil => some 0
  | _, .snoc as _ _ e => addC (argsCost as) (valCost e)
  | _, .snocStorage .. | _, .snocMemory .. => none

/-- A revert-data part: literal bytes by their words, a selector, a word;
not memory. -/
def revPartCost {Γ : Ctx} : RevPart C Γ → Option Nat
  | .bytes bs => some (bs.length / 32 + 1)
  | .sel _ => some 1
  | .word v => (valCost v)
  | .mem _ _ => none

def revListCost {Γ : Ctx} : List (RevPart C Γ) → Option Nat
  | [] => some 0
  | d :: ds => addC (revPartCost d) (revListCost ds)

/-- A call's return the rule admits: none, or one value.  A memory return
allocates a default object of unbounded size; a storage return is an alias;
a tuple's binders may be either. -/
def retOk {Γ rs Γ' : Ctx} : CallRet Γ rs Γ' → Bool
  | .none | .val .. => true
  | .rets _ | .mem .. | .storage .. => false

mutual

/-- **The cost of a statement**, or `none` when the rule rejects it. -/
def stmtCost : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Option Nat
  | _, _, .assignLocal _ r => addC (some 1) (valCost r)
  | _, _, .declLocal _ _ none => some 1
  | _, _, .declLocal _ _ (some v) => addC (some 1) (valCost v)
  | _, _, .require c => addC (some 1) (valCost c)
  | _, _, .assert c => addC (some 1) (valCost c)
  | _, _, .revert => some 1
  | _, _, .assumeFalse => some 1
  | _, _, .revertData d => addC (some 1) (revListCost d)
  | _, _, .ite c t e => addC (some 1) (addC (valCost c) (maxC (progCost t) (progCost e)))
  | _, _, .block b => progCost b
  | _, _, .call _ args ret body =>
    if retOk ret then addC (some 1) (addC (argsCost args) (progCost body)) else none
  | _, _, .assign .. | _, _, .rebind .. | _, _, .declStorage .. | _, _, .opAssign .. => none
  | _, _, .incDec .. | _, _, .assignIncDec .. | _, _, .assignLocalPush .. | _, _, .push .. => none
  | _, _, .pop .. | _, _, .transfer .. | _, _, .send .. | _, _, .declMem .. => none
  | _, _, .rebindMem .. | _, _, .assignFromMem .. | _, _, .assignMem .. | _, _, .delete .. => none
  | _, _, .deleteMem .. | _, _, .assignNew .. | _, _, .tryCall .. | _, _, .loop .. => none
  | _, _, .pushOpAssign .. | _, _, .pushIncDec .. | _, _, .callReceiver .. => none
  | _, _, .callReceiverPush .. | _, _, .callRec .. | _, _, .catchData .. => none

/-- The cost of a sequence: the sum of its statements'. -/
def progCost : {Γ Γ' : Ctx} → Prog C Γ Γ' → Option Nat
  | _, _, .nil => some 0
  | _, _, .cons s P => addC (stmtCost s) (progCost P)

end

/-! ## The rule -/

/-- A `receive`/fallback body: a program from the empty frame. -/
structure Body (C : Contract) where
  {out : Ctx}
  prog : Prog C [] out

/-- A body fits the stipend `s` under model `M`: it has a cost, and
`unit · cost + reserve ≤ s`. -/
def fitsWith (M : CostModel) (s : Nat) (b : Body C) : Bool :=
  match progCost b.prog with
  | some c => M.unit * c + M.reserve ≤ s
  | none => false

/-- **The stipend rule** of the pinned Osaka EVM: `osakaCold` at the pin's
2300-gas stipend. -/
def rule (C : Contract) : StipendRule (Body C) where
  fits b := fitsWith osakaCold pinned.stipend b = true

instance (b : Body C) : Decidable ((rule C).fits b) := by unfold rule; infer_instance

/-! ## What the compiler owes (G43) -/

/-- The second half of the compiler's obligation: every body the rule
rejects fails when entered with at most the stipend (`failsUnderStipend`
is the compiled body's run, from G43's code), so source and EVM agree on
every stipend payment to an instance of the system. -/
def Enforced {Body : Type} (R : StipendRule Body) (failsUnderStipend : Body → Prop) : Prop :=
  ∀ b, ¬R.fits b → failsUnderStipend b

/-- **The obligation G43 discharges**: admitted bodies complete within the
stipend (`StipendRule.Fitted`, `gasUsed` the compiled body's worst-case gas
with cold access costs and EIP-2200's sentry), and rejected ones fail. -/
def Obligation (C : Contract) (gasUsed : Body C → Nat) (failsUnderStipend : Body C → Prop) :
    Prop :=
  (rule C).Fitted pinned gasUsed ∧ Enforced (rule C) failsUnderStipend

/-- The admitted bodies cost at most 40 units. -/
theorem fits_iff (b : Body C) : (rule C).fits b ↔ ∃ c, progCost b.prog = some c ∧ c ≤ 40 := by
  show fitsWith osakaCold pinned.stipend b = true ↔ _
  unfold fitsWith
  cases h : progCost b.prog with
  | none => simp only [Bool.false_eq_true, reduceCtorEq, false_and, exists_false]
  | some c =>
    simp only [Option.some.injEq, exists_eq_left', decide_eq_true_eq]
    show 50 * c + 300 ≤ 2300 ↔ c ≤ 40
    omega

/-- A body with a rejected statement first is rejected. -/
theorem not_fits_cons {Γ₁ : Ctx} {out : Ctx} (s : Stmt C [] Γ₁) (P : Prog C Γ₁ out)
    (h : stmtCost s = none) : ¬(rule C).fits ⟨.cons s P⟩ := by
  rw [fits_iff]
  rintro ⟨c, hc, -⟩
  simp only [progCost, h, addC, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hc

/-! ## Examples and non-examples -/

/-- `receive() external payable {}` fits. -/
theorem empty_fits : (rule C).fits ⟨(.nil : Prog C [] [])⟩ :=
  (fits_iff _).2 ⟨0, rfl, by decide⟩

/-- `require(msg.value != 0);` fits. -/
def requireValue : Prog C [] [] :=
  .cons (.require (.binop .neB rfl rfl (.simple (.env .msgValue rfl)) (.simple (.lit 0 rfl)))) .nil

theorem requireValue_fits : (rule C).fits ⟨(requireValue : Prog C [] [])⟩ :=
  (fits_iff _).2 ⟨4, rfl, by decide⟩

/-- A payment from the body (`payable(msg.sender).transfer(1);`) does not. -/
theorem transfer_not_fits :
    ¬(rule C).fits ⟨(.cons (.transfer (.simple (.env .msgSender rfl)) (.simple (.lit 1 rfl))) .nil :
      Prog C [] [])⟩ :=
  not_fits_cons _ _ rfl

/-- A loop does not, however small. -/
theorem loop_not_fits (a : LoopAnn C []) :
    ¬(rule C).fits ⟨(.cons (.loop a (.simple (.bool false)) .nil) .nil : Prog C [] [])⟩ :=
  not_fits_cons _ _ rfl

/-- A body that stores does not: under EIP-2200 no `SSTORE` succeeds with
2300 gas or less left. -/
theorem assign_not_fits {T : Ty} (l : Loc C [] T) (r : Src C [] T) :
    ¬(rule C).fits ⟨(.cons (.assign l r) .nil : Prog C [] [])⟩ :=
  not_fits_cons _ _ rfl

/-- A body that reads storage does not: one cold `SLOAD` is 2100 gas. -/
theorem read_not_fits {p : PrimTy} (l : Loc C [] (.prim p)) :
    ¬(rule C).fits ⟨(.cons (.require (.binop .eqB rfl rfl (.read l) (.read l))) .nil :
      Prog C [] [])⟩ := by
  rw [fits_iff]
  rintro ⟨c, hc, -⟩
  cases hc

/-- `n` copies of `require(msg.value != 0);`, 4 units each. -/
def requires : Nat → Prog C [] []
  | 0 => .nil
  | n + 1 => .cons (.require (.binop .neB rfl rfl (.simple (.env .msgValue rfl))
      (.simple (.lit 0 rfl)))) (requires n)

theorem requires_cost (n : Nat) : progCost (requires n : Prog C [] []) = some (4 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show addC (some 4) (progCost (requires n : Prog C [] [])) = some (4 * (n + 1))
    rw [ih]
    show some (4 + 4 * n) = some (4 * (n + 1))
    rw [Nat.mul_succ, Nat.add_comm]

/-- Ten `require(msg.value != 0);` fit (40 units), eleven do not. -/
theorem requires_ten_fits : (rule C).fits ⟨(requires 10 : Prog C [] [])⟩ :=
  (fits_iff _).2 ⟨40, requires_cost 10, by decide⟩

theorem requires_eleven_not_fits : ¬(rule C).fits ⟨(requires 11 : Prog C [] [])⟩ := by
  rw [fits_iff, requires_cost]
  rintro ⟨c, hc, hle⟩
  cases hc
  omega

/-- `uint y = a ** b;` is rejected, whatever its operands. -/
theorem pow_not_fits {p : PrimTy} (x : Var) (a b : Val C [] p) (h : BinOp.pow.accepts p = true)
    (hq : BinOp.pow.ret p = .uint) :
    ¬(rule C).fits ⟨(.cons (.declLocal .uint x (some (.binop .pow h hq a b))) .nil :
      Prog C [] [.val .uint])⟩ := by
  rw [fits_iff]
  rintro ⟨c, hc, -⟩
  simp only [progCost, stmtCost, valCost, true_or, if_true, addC, Option.bind_eq_bind,
    Option.bind_none, Option.bind_some, reduceCtorEq] at hc

end Solidity.Stipend

/-- info: 'Solidity.Stipend.fits_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Stipend.fits_iff
/-- info: 'Solidity.Stipend.requires_eleven_not_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Stipend.requires_eleven_not_fits

