import Solidity.Semantics

/-!
# An EVM-style stack machine

The compilation target of `Evm/Compile.lean`: a program-counter machine
over 256-bit words whose instruction meanings follow the EVM semantics
formalized in Lean by Nethermind's
[EVMYulLean](https://github.com/NethermindEth/EVMYulLean)
(`EvmYul/UInt256.lean`, `EvmYul/EVM/Semantics.lean`), the reference EVM
formalization this development targets:

- words are `2^256`-modular (`EvmYul.UInt256` is `Fin (2^256)`; here
  `BitVec 256`, the same data), and `ADD`/`SUB`/`MUL`/`EXP` wrap;
- `DIV a 0 = 0` and `MOD a 0 = 0` (EVMYulLean `UInt256.div`/`UInt256.mod`
  via `Fin` division);
- comparisons (`LT`, `GT`, `EQ`, `ISZERO`) push `1`/`0`;
- `DUP n` copies the `n`-th stack item, `SWAP n` swaps the top with the
  `(n+1)`-th (the Yellow Paper's `DUPn`/`SWAPn` indexing);
- `SLOAD`/`SSTORE` read and write a word-keyed storage where absent keys
  read `0`;
- `JUMPI` jumps iff the popped condition word is non-zero;
- `REVERT` aborts execution.

The simplifications relative to EVMYulLean, documented here once
(`docs/compiler-verification.md` repeats them):

- **no gas**: gas metering is orthogonal to the functional-correctness
  statement proved in `Evm/Correctness.lean`;
- **relative forward jumps** instead of absolute jump targets with
  `JUMPDEST` validation: `jump δ`/`jumpi δ` transfer control to
  `pc + 1 + δ`, which makes compiled code position-independent — the
  form of the correctness lemmas ("code placed at any `base`") depends
  on it. An assembler to absolute-target code is a layout-arithmetic
  pass kept out of scope;
- **no 1024-item stack-depth limit** (the compiler's `DUP`/`SWAP`
  depths are still checked against the EVM's hard limit of 16);
- **no value transfer**: there is no `CALL`/`SELFBALANCE`; the source
  `transfer` is compiled as bookkeeping on reserved storage words
  (`Compile.netSlotW` for the net ledger, `Compile.balanceSlotW` for
  the contract's own balance), with the balance check the EVM performs
  on a value-carrying call made explicit as a guard.

`Step` is the one-instruction transition relation, `Steps` its
reflexive-transitive closure, `Reverting` the abort observation, and
`run` a fuel-bounded executable mirror used by the differential tests in
`Evm/Examples.lean`.
-/

namespace Solidity
namespace Evm

open Semantics (lookupBy setBy)

/-- EVM machine word (EVMYulLean's `UInt256`, as core's `BitVec 256`). -/
abbrev Word := BitVec 256

/-- Word-keyed persistent storage; absent keys read `0`
(the all-zero initial storage of the Yellow Paper). -/
abbrev Store := List (Word × Word)

def Store.read (st : Store) (k : Word) : Word :=
  (lookupBy k st).getD 0

def Store.write (st : Store) (k v : Word) : Store :=
  setBy k v st

/-- `1`/`0` encoding of comparison results (Yellow Paper, EVMYulLean
`Bool.toUInt256`). -/
def wBool (b : Bool) : Word :=
  if b then 1 else 0

/-- `MOD`: zero modulus yields `0` (EVMYulLean `UInt256.mod`). `DIV` by
zero needs no special case — `BitVec.udiv` by `0` is already `0`. -/
def wMod (a b : Word) : Word :=
  if b = 0 then 0 else BitVec.umod a b

/-- `EXP`, modular exponentiation (Yellow Paper `EXP`). -/
def wExp (a b : Word) : Word :=
  BitVec.ofNat 256 (a.toNat ^ b.toNat)

/-- Storage-slot derivation for mapping entries: mapping at layout slot
`slot`, key `key`, lives at storage key `(slot+1)·2²²⁴ + key`.

This is the machine's stand-in for solc's
`keccak256(key ++ slot)` derivation: injective (hence collision-free
*by construction*) for `slot < 2³¹` and `key < 2²²⁴`, and disjoint from
the direct root slots (which stay below `2²²⁴`). Swapping in real
keccak is a documented delta: it would replace the injectivity lemmas
of `Evm/Correctness.lean` with a collision-freedom assumption on the
keys an execution touches. -/
def mapSlotW (slot key : Word) : Word :=
  BitVec.ofNat 256 ((slot.toNat + 1) * 2 ^ 224 + key.toNat)

/-- The instruction subset emitted by the compiler. Every constructor is
an EVM opcode (Yellow Paper appendix H); `jump`/`jumpi` carry relative
forward offsets (see the module docstring). -/
inductive Instr where
  | push (w : Word)
  | pop
  /-- `DUP n` (`n ∈ [1,16]`): push a copy of the `n`-th stack item. -/
  | dup (n : Nat)
  /-- `SWAP n` (`n ∈ [1,16]`): swap the top with the `(n+1)`-th item. -/
  | swap (n : Nat)
  | add | sub | mul | div | mod | exp
  | lt | gt | eq | iszero | and | or
  | sload | sstore
  /-- Derive a mapping entry's storage slot: pop the mapping's layout
  slot and the key, push `mapSlotW slot key` (the machine's stand-in
  for solc's `MSTORE`/`MSTORE`/`SHA3` sequence — see `mapSlotW`). -/
  | mapslot
  /-- Unconditional relative jump to `pc + 1 + delta`. -/
  | jump (delta : Nat)
  /-- Pop a condition word; jump to `pc + 1 + delta` iff it is
  non-zero. -/
  | jumpi (delta : Nat)
  | stop
  | revert
  deriving Repr, DecidableEq

abbrev Code := List Instr

/-- A machine configuration: program counter, word stack, storage. -/
structure Conf where
  pc : Nat
  stack : List Word
  store : Store
  deriving Repr

/-- One-instruction transition of the machine running code `C`.
Instruction meanings follow EVMYulLean (see module docstring); `stop`
and `revert` have no transitions — they are observed by `AtStop` /
`Reverting` below. -/
inductive Step (C : Code) : Conf → Conf → Prop where
  | push {pc σ st w} :
      C[pc]? = some (.push w) →
      Step C ⟨pc, σ, st⟩ ⟨pc + 1, w :: σ, st⟩
  | pop {pc σ st w} :
      C[pc]? = some .pop →
      Step C ⟨pc, w :: σ, st⟩ ⟨pc + 1, σ, st⟩
  /-- `DUP (n+1)` copies `σ[n]` (Yellow Paper `DUPn` duplicates the
  `n`-th item, 1-indexed). -/
  | dup {pc σ st n w} :
      C[pc]? = some (.dup (n + 1)) →
      σ[n]? = some w →
      Step C ⟨pc, σ, st⟩ ⟨pc + 1, w :: σ, st⟩
  /-- `SWAP (n+1)` swaps `σ[0]` and `σ[n+1]`. -/
  | swap {pc σ st n a b} :
      C[pc]? = some (.swap (n + 1)) →
      σ[0]? = some a →
      σ[n + 1]? = some b →
      Step C ⟨pc, σ, st⟩ ⟨pc + 1, (σ.set (n + 1) a).set 0 b, st⟩
  | add {pc σ st a b} :
      C[pc]? = some .add →
      Step C ⟨pc, a :: b :: σ, st⟩ ⟨pc + 1, (a + b) :: σ, st⟩
  | sub {pc σ st a b} :
      C[pc]? = some .sub →
      Step C ⟨pc, a :: b :: σ, st⟩ ⟨pc + 1, (a - b) :: σ, st⟩
  | mul {pc σ st a b} :
      C[pc]? = some .mul →
      Step C ⟨pc, a :: b :: σ, st⟩ ⟨pc + 1, (a * b) :: σ, st⟩
  | div {pc σ st a b} :
      C[pc]? = some .div →
      Step C ⟨pc, a :: b :: σ, st⟩ ⟨pc + 1, (BitVec.udiv a b) :: σ, st⟩
  | mod {pc σ st a b} :
      C[pc]? = some .mod →
      Step C ⟨pc, a :: b :: σ, st⟩ ⟨pc + 1, (wMod a b) :: σ, st⟩
  | exp {pc σ st a b} :
      C[pc]? = some .exp →
      Step C ⟨pc, a :: b :: σ, st⟩ ⟨pc + 1, (wExp a b) :: σ, st⟩
  | lt {pc σ st a b} :
      C[pc]? = some .lt →
      Step C ⟨pc, a :: b :: σ, st⟩ ⟨pc + 1, wBool (BitVec.ult a b) :: σ, st⟩
  | gt {pc σ st a b} :
      C[pc]? = some .gt →
      Step C ⟨pc, a :: b :: σ, st⟩ ⟨pc + 1, wBool (BitVec.ult b a) :: σ, st⟩
  | eq {pc σ st a b} :
      C[pc]? = some .eq →
      Step C ⟨pc, a :: b :: σ, st⟩ ⟨pc + 1, wBool (a = b) :: σ, st⟩
  | iszero {pc σ st a} :
      C[pc]? = some .iszero →
      Step C ⟨pc, a :: σ, st⟩ ⟨pc + 1, wBool (a = 0) :: σ, st⟩
  | and {pc σ st a b} :
      C[pc]? = some .and →
      Step C ⟨pc, a :: b :: σ, st⟩ ⟨pc + 1, (a &&& b) :: σ, st⟩
  | or {pc σ st a b} :
      C[pc]? = some .or →
      Step C ⟨pc, a :: b :: σ, st⟩ ⟨pc + 1, (a ||| b) :: σ, st⟩
  | sload {pc σ st k} :
      C[pc]? = some .sload →
      Step C ⟨pc, k :: σ, st⟩ ⟨pc + 1, st.read k :: σ, st⟩
  | sstore {pc σ st k v} :
      C[pc]? = some .sstore →
      Step C ⟨pc, k :: v :: σ, st⟩ ⟨pc + 1, σ, st.write k v⟩
  | mapslot {pc σ st slot key} :
      C[pc]? = some .mapslot →
      Step C ⟨pc, slot :: key :: σ, st⟩
        ⟨pc + 1, mapSlotW slot key :: σ, st⟩
  | jump {pc σ st δ} :
      C[pc]? = some (.jump δ) →
      Step C ⟨pc, σ, st⟩ ⟨pc + 1 + δ, σ, st⟩
  | jumpiTrue {pc σ st δ c} :
      C[pc]? = some (.jumpi δ) →
      c ≠ 0 →
      Step C ⟨pc, c :: σ, st⟩ ⟨pc + 1 + δ, σ, st⟩
  | jumpiFalse {pc σ st δ} :
      C[pc]? = some (.jumpi δ) →
      Step C ⟨pc, (0 : Word) :: σ, st⟩ ⟨pc + 1, σ, st⟩

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps (C : Code) : Conf → Conf → Prop where
  | refl (c : Conf) : Steps C c c
  | head {c₁ c₂ c₃} : Step C c₁ c₂ → Steps C c₂ c₃ → Steps C c₁ c₃

namespace Steps

theorem single {C : Code} {c₁ c₂ : Conf} (h : Step C c₁ c₂) :
    Steps C c₁ c₂ :=
  .head h (.refl c₂)

theorem trans {C : Code} {c₁ c₂ c₃ : Conf}
    (h₁ : Steps C c₁ c₂) (h₂ : Steps C c₂ c₃) : Steps C c₁ c₃ := by
  induction h₁ with
  | refl => exact h₂
  | head s _ ih => exact .head s (ih h₂)

end Steps

/-- The machine, started in `c`, reaches a `REVERT` instruction. -/
def Reverting (C : Code) (c : Conf) : Prop :=
  ∃ c', Steps C c c' ∧ C[c'.pc]? = some Instr.revert

theorem Reverting.of_steps {C : Code} {c c' : Conf}
    (h : Steps C c c') (hrev : Reverting C c') : Reverting C c := by
  obtain ⟨c'', hsteps, hfetch⟩ := hrev
  exact ⟨c'', h.trans hsteps, hfetch⟩

theorem Reverting.of_steps' {C : Code} {c c' : Conf}
    (hrev : Reverting C c') (h : Step C c c') : Reverting C c :=
  hrev.of_steps (Steps.single h)

/-! ## Code-in-context reasoning

`codeAt C base c`: the instruction sequence `c` occupies positions
`base, base+1, …` of the full program `C`. Because jumps are relative,
every correctness lemma over a compiled fragment is stated against an
arbitrary `codeAt` placement and composes by the decomposition lemmas
below (the "code in context" discipline of Leroy's verified compilation
of IMP to a stack VM). -/

def codeAt (C : Code) (base : Nat) (c : Code) : Prop :=
  ∃ pre post, C = pre ++ c ++ post ∧ pre.length = base

namespace codeAt

theorem fetch {C : Code} {base : Nat} {i : Instr} {c : Code}
    (h : codeAt C base (i :: c)) : C[base]? = some i := by
  obtain ⟨pre, post, hC, hlen⟩ := h
  subst hC hlen
  simp

theorem tail {C : Code} {base : Nat} {i : Instr} {c : Code}
    (h : codeAt C base (i :: c)) : codeAt C (base + 1) c := by
  obtain ⟨pre, post, hC, hlen⟩ := h
  exact ⟨pre ++ [i], post, by simp [hC], by simp [hlen]⟩

theorem append_left {C : Code} {base : Nat} {c₁ c₂ : Code}
    (h : codeAt C base (c₁ ++ c₂)) : codeAt C base c₁ := by
  obtain ⟨pre, post, hC, hlen⟩ := h
  exact ⟨pre, c₂ ++ post, by simp [hC], hlen⟩

theorem append_right {C : Code} {base : Nat} {c₁ c₂ : Code}
    (h : codeAt C base (c₁ ++ c₂)) : codeAt C (base + c₁.length) c₂ := by
  obtain ⟨pre, post, hC, hlen⟩ := h
  exact ⟨pre ++ c₁, post, by simp [hC], by simp [hlen]⟩

/-- Fetch the sole instruction of a singleton placement. -/
theorem fetch_singleton {C : Code} {base : Nat} {i : Instr}
    (h : codeAt C base [i]) : C[base]? = some i :=
  fetch h

end codeAt

/-! ## Executable runner (differential testing) -/

inductive RunRes where
  | ok (stack : List Word) (store : Store)
  | reverted
  | stuck
  | outOfFuel
  deriving Repr

/-- One-step outcome of the executable machine. -/
inductive Step1 where
  | next (c : Conf)
  | halt (stack : List Word) (store : Store)
  | reverted
  | stuck

/-- Execute a single fetched instruction (executable mirror of the
`Step` constructors; `stop` halts, `revert` reverts, operand
mismatches are stuck). -/
def execInstr (i : Instr) (pc : Nat) (σ : List Word) (st : Store) :
    Step1 :=
  match i with
  | .push w => .next ⟨pc + 1, w :: σ, st⟩
  | .pop =>
      match σ with
      | _ :: σ => .next ⟨pc + 1, σ, st⟩
      | _ => .stuck
  | .dup n =>
      match n, σ[n - 1]? with
      | _ + 1, some w => .next ⟨pc + 1, w :: σ, st⟩
      | _, _ => .stuck
  | .swap n =>
      match n, σ[0]?, σ[n]? with
      | _ + 1, some a, some b =>
          .next ⟨pc + 1, (σ.set n a).set 0 b, st⟩
      | _, _, _ => .stuck
  | .add =>
      match σ with
      | a :: b :: σ => .next ⟨pc + 1, (a + b) :: σ, st⟩
      | _ => .stuck
  | .sub =>
      match σ with
      | a :: b :: σ => .next ⟨pc + 1, (a - b) :: σ, st⟩
      | _ => .stuck
  | .mul =>
      match σ with
      | a :: b :: σ => .next ⟨pc + 1, (a * b) :: σ, st⟩
      | _ => .stuck
  | .div =>
      match σ with
      | a :: b :: σ => .next ⟨pc + 1, (BitVec.udiv a b) :: σ, st⟩
      | _ => .stuck
  | .mod =>
      match σ with
      | a :: b :: σ => .next ⟨pc + 1, (wMod a b) :: σ, st⟩
      | _ => .stuck
  | .exp =>
      match σ with
      | a :: b :: σ => .next ⟨pc + 1, (wExp a b) :: σ, st⟩
      | _ => .stuck
  | .lt =>
      match σ with
      | a :: b :: σ => .next ⟨pc + 1, wBool (BitVec.ult a b) :: σ, st⟩
      | _ => .stuck
  | .gt =>
      match σ with
      | a :: b :: σ => .next ⟨pc + 1, wBool (BitVec.ult b a) :: σ, st⟩
      | _ => .stuck
  | .eq =>
      match σ with
      | a :: b :: σ => .next ⟨pc + 1, wBool (a = b) :: σ, st⟩
      | _ => .stuck
  | .iszero =>
      match σ with
      | a :: σ => .next ⟨pc + 1, wBool (a = 0) :: σ, st⟩
      | _ => .stuck
  | .and =>
      match σ with
      | a :: b :: σ => .next ⟨pc + 1, (a &&& b) :: σ, st⟩
      | _ => .stuck
  | .or =>
      match σ with
      | a :: b :: σ => .next ⟨pc + 1, (a ||| b) :: σ, st⟩
      | _ => .stuck
  | .sload =>
      match σ with
      | k :: σ => .next ⟨pc + 1, st.read k :: σ, st⟩
      | _ => .stuck
  | .sstore =>
      match σ with
      | k :: v :: σ => .next ⟨pc + 1, σ, st.write k v⟩
      | _ => .stuck
  | .mapslot =>
      match σ with
      | slot :: key :: σ => .next ⟨pc + 1, mapSlotW slot key :: σ, st⟩
      | _ => .stuck
  | .jump δ => .next ⟨pc + 1 + δ, σ, st⟩
  | .jumpi δ =>
      match σ with
      | c :: σ =>
          if c = 0 then .next ⟨pc + 1, σ, st⟩
          else .next ⟨pc + 1 + δ, σ, st⟩
      | _ => .stuck
  | .stop => .halt σ st
  | .revert => .reverted

/-- One machine step: halt at the end of the code, else fetch and
execute. -/
def step1 (C : Code) (c : Conf) : Step1 :=
  if c.pc = C.length then .halt c.stack c.store
  else
    match C[c.pc]? with
    | none => .stuck
    | some i => execInstr i c.pc c.stack c.store

/-- Fuel-bounded executable mirror of `Step`/`Steps`: runs until the
program counter falls off the end of the code (success), `stop`
(success), `revert`, a stuck configuration, or fuel exhaustion. -/
def run (C : Code) : Nat → Conf → RunRes
  | 0, _ => .outOfFuel
  | fuel + 1, c =>
      match step1 C c with
      | .next c' => run C fuel c'
      | .halt σ st => .ok σ st
      | .reverted => .reverted
      | .stuck => .stuck

/-! ## Determinism and terminal configurations

The preservation theorems of `Evm/Correctness.lean` are *forward*
simulations: they exhibit one machine execution. The lemmas below close
the other direction: the machine is deterministic, so the exhibited
execution is the only one — any terminal configuration the machine can
reach is exactly the one the theorem describes. -/

/-- The machine is deterministic: a configuration has at most one
successor. -/
theorem Step.deterministic {C : Code} {c c₁ c₂ : Conf}
    (h₁ : Step C c c₁) (h₂ : Step C c c₂) : c₁ = c₂ := by
  cases h₁ <;> cases h₂ <;> simp_all

/-- A configuration with no successor. -/
def Terminal (C : Code) (c : Conf) : Prop :=
  ∀ c', ¬ Step C c c'

/-- Falling off the end of the code is terminal. -/
theorem terminal_of_end {C : Code} {pc : Nat} {σ : List Word}
    {st : Store} (h : C.length ≤ pc) : Terminal C ⟨pc, σ, st⟩ := by
  intro c' hs
  have hfetch : C[pc]? = none := by
    rw [List.getElem?_eq_none_iff]
    exact h
  cases hs <;> simp_all

/-- A `STOP` instruction is terminal. -/
theorem terminal_of_stop {C : Code} {pc : Nat} {σ : List Word}
    {st : Store} (h : C[pc]? = some Instr.stop) :
    Terminal C ⟨pc, σ, st⟩ := by
  intro c' hs
  cases hs <;> simp_all

/-- A `REVERT` instruction is terminal. -/
theorem terminal_of_revert {C : Code} {pc : Nat} {σ : List Word}
    {st : Store} (h : C[pc]? = some Instr.revert) :
    Terminal C ⟨pc, σ, st⟩ := by
  intro c' hs
  cases hs <;> simp_all

/-- Two executions from the same start that both reach a terminal
configuration reach the *same* configuration. -/
theorem Steps.unique_terminal {C : Code} {c d₁ : Conf}
    (h₁ : Steps C c d₁) :
    ∀ {d₂ : Conf}, Steps C c d₂ → Terminal C d₁ → Terminal C d₂ →
      d₁ = d₂ := by
  induction h₁ with
  | refl c =>
      intro d₂ h₂ t₁ _
      cases h₂ with
      | refl => rfl
      | head s _ => exact absurd s (t₁ _)
  | head s rest ih =>
      intro d₂ h₂ t₁ t₂
      cases h₂ with
      | refl => exact absurd s (t₂ _)
      | head s₂ rest₂ =>
          rw [← Step.deterministic s s₂] at rest₂
          exact ih rest₂ t₁ t₂

/-! ## Soundness of the fuel runner

`run` is the executable face of the machine (used by the differential
tests); the lemmas below tie its verdicts back to the relational
semantics, so a test and the preservation theorems provably talk about
the same executions. -/

/-- A configuration `run` reports as `.ok`: the program counter fell
off the end of the code, or sits on `STOP`. -/
def Halted (C : Code) (c : Conf) : Prop :=
  c.pc = C.length ∨ C[c.pc]? = some Instr.stop

theorem Terminal.of_halted {C : Code} {c : Conf} (h : Halted C c) :
    Terminal C c := by
  obtain ⟨pc, σ, st⟩ := c
  cases h with
  | inl h => exact terminal_of_end (by simp_all)
  | inr h => exact terminal_of_stop h

/-- A `.next` outcome of `execInstr` is a real machine step. -/
theorem execInstr_next_sound {C : Code} {i : Instr} {pc : Nat}
    {σ : List Word} {st : Store} {c' : Conf}
    (hfetch : C[pc]? = some i)
    (h : execInstr i pc σ st = .next c') : Step C ⟨pc, σ, st⟩ c' := by
  match i with
  | .push w =>
      simp only [execInstr, Step1.next.injEq] at h
      exact h ▸ Step.push hfetch
  | .pop =>
      match σ with
      | [] => simp [execInstr] at h
      | a :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.pop hfetch
  | .dup n =>
      match n with
      | 0 => simp [execInstr] at h
      | m + 1 =>
          cases hw : σ[m]? with
          | none => simp [execInstr, Nat.add_sub_cancel, hw] at h
          | some w =>
              simp only [execInstr, Nat.add_sub_cancel, hw,
                Step1.next.injEq] at h
              exact h ▸ Step.dup hfetch hw
  | .swap n =>
      match n with
      | 0 => simp [execInstr] at h
      | m + 1 =>
          cases ha : σ[0]? with
          | none => simp [execInstr, ha] at h
          | some a =>
              cases hb : σ[m + 1]? with
              | none => simp [execInstr, ha, hb] at h
              | some b =>
                  simp only [execInstr, ha, hb, Step1.next.injEq] at h
                  exact h ▸ Step.swap hfetch ha hb
  | .add =>
      match σ with
      | [] | [_] => simp [execInstr] at h
      | a :: b :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.add hfetch
  | .sub =>
      match σ with
      | [] | [_] => simp [execInstr] at h
      | a :: b :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.sub hfetch
  | .mul =>
      match σ with
      | [] | [_] => simp [execInstr] at h
      | a :: b :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.mul hfetch
  | .div =>
      match σ with
      | [] | [_] => simp [execInstr] at h
      | a :: b :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.div hfetch
  | .mod =>
      match σ with
      | [] | [_] => simp [execInstr] at h
      | a :: b :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.mod hfetch
  | .exp =>
      match σ with
      | [] | [_] => simp [execInstr] at h
      | a :: b :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.exp hfetch
  | .lt =>
      match σ with
      | [] | [_] => simp [execInstr] at h
      | a :: b :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.lt hfetch
  | .gt =>
      match σ with
      | [] | [_] => simp [execInstr] at h
      | a :: b :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.gt hfetch
  | .eq =>
      match σ with
      | [] | [_] => simp [execInstr] at h
      | a :: b :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.eq hfetch
  | .iszero =>
      match σ with
      | [] => simp [execInstr] at h
      | a :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.iszero hfetch
  | .and =>
      match σ with
      | [] | [_] => simp [execInstr] at h
      | a :: b :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.and hfetch
  | .or =>
      match σ with
      | [] | [_] => simp [execInstr] at h
      | a :: b :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.or hfetch
  | .sload =>
      match σ with
      | [] => simp [execInstr] at h
      | k :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.sload hfetch
  | .sstore =>
      match σ with
      | [] | [_] => simp [execInstr] at h
      | k :: v :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.sstore hfetch
  | .mapslot =>
      match σ with
      | [] | [_] => simp [execInstr] at h
      | slot :: key :: σ =>
          simp only [execInstr, Step1.next.injEq] at h
          exact h ▸ Step.mapslot hfetch
  | .jump δ =>
      simp only [execInstr, Step1.next.injEq] at h
      exact h ▸ Step.jump hfetch
  | .jumpi δ =>
      match σ with
      | [] => simp [execInstr] at h
      | cw :: σ =>
          simp only [execInstr] at h
          by_cases hc0 : cw = 0
          · rw [if_pos hc0] at h
            simp only [Step1.next.injEq] at h
            subst hc0
            exact h ▸ Step.jumpiFalse hfetch
          · rw [if_neg hc0] at h
            simp only [Step1.next.injEq] at h
            exact h ▸ Step.jumpiTrue hfetch hc0
  | .stop => simp [execInstr] at h
  | .revert => simp [execInstr] at h

/-- A `.halt` outcome of `execInstr` only arises from `STOP`, with the
incoming stack and storage. -/
theorem execInstr_halt_sound {i : Instr} {pc : Nat} {σ σ' : List Word}
    {st st' : Store} (h : execInstr i pc σ st = .halt σ' st') :
    i = .stop ∧ σ' = σ ∧ st' = st := by
  match i with
  | .stop =>
      simp only [execInstr, Step1.halt.injEq] at h
      exact ⟨rfl, h.1.symm, h.2.symm⟩
  | .push w => simp [execInstr] at h
  | .jump δ => simp [execInstr] at h
  | .revert => simp [execInstr] at h
  | .pop => cases σ <;> simp [execInstr] at h
  | .iszero => cases σ <;> simp [execInstr] at h
  | .sload => cases σ <;> simp [execInstr] at h
  | .add =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .sub =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .mul =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .div =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .mod =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .exp =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .lt =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .gt =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .eq =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .and =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .or =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .sstore =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .mapslot =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .jumpi δ =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons cw t =>
          simp only [execInstr] at h
          by_cases hc0 : cw = 0
          · rw [if_pos hc0] at h; simp at h
          · rw [if_neg hc0] at h; simp at h
  | .dup n =>
      match n with
      | 0 => simp [execInstr] at h
      | m + 1 =>
          cases hw : σ[m]? <;>
            simp [execInstr, Nat.add_sub_cancel, hw] at h
  | .swap n =>
      match n with
      | 0 => simp [execInstr] at h
      | m + 1 =>
          cases ha : σ[0]? <;> cases hb : σ[m + 1]? <;>
            simp [execInstr, ha, hb] at h

/-- A `.reverted` outcome of `execInstr` only arises from `REVERT`. -/
theorem execInstr_revert_sound {i : Instr} {pc : Nat} {σ : List Word}
    {st : Store} (h : execInstr i pc σ st = .reverted) :
    i = .revert := by
  match i with
  | .revert => rfl
  | .stop => simp [execInstr] at h
  | .push w => simp [execInstr] at h
  | .jump δ => simp [execInstr] at h
  | .pop => cases σ <;> simp [execInstr] at h
  | .iszero => cases σ <;> simp [execInstr] at h
  | .sload => cases σ <;> simp [execInstr] at h
  | .add =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .sub =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .mul =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .div =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .mod =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .exp =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .lt =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .gt =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .eq =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .and =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .or =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .sstore =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .mapslot =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons a t => cases t <;> simp [execInstr] at h
  | .jumpi δ =>
      cases σ with
      | nil => simp [execInstr] at h
      | cons cw t =>
          simp only [execInstr] at h
          by_cases hc0 : cw = 0
          · rw [if_pos hc0] at h; simp at h
          · rw [if_neg hc0] at h; simp at h
  | .dup n =>
      match n with
      | 0 => simp [execInstr] at h
      | m + 1 =>
          cases hw : σ[m]? <;>
            simp [execInstr, Nat.add_sub_cancel, hw] at h
  | .swap n =>
      match n with
      | 0 => simp [execInstr] at h
      | m + 1 =>
          cases ha : σ[0]? <;> cases hb : σ[m + 1]? <;>
            simp [execInstr, ha, hb] at h

/-- A `.next` outcome of `step1` is a real machine step. -/
theorem step1_next_sound {C : Code} {c c' : Conf}
    (h : step1 C c = .next c') : Step C c c' := by
  obtain ⟨pc, σ, st⟩ := c
  unfold step1 at h
  split at h
  case isTrue => exact absurd h (by simp)
  case isFalse hend =>
    cases hfetch : C[pc]? with
    | none => simp [hfetch] at h
    | some i =>
        simp only [hfetch] at h
        exact execInstr_next_sound hfetch h

/-- A `.halt` outcome of `step1` is a halted configuration reporting
its own stack and storage. -/
theorem step1_halt_sound {C : Code} {c : Conf} {σ : List Word}
    {st : Store} (h : step1 C c = .halt σ st) :
    σ = c.stack ∧ st = c.store ∧ Halted C c := by
  obtain ⟨pc, σ0, st0⟩ := c
  unfold step1 at h
  split at h
  case isTrue hend =>
    simp only [Step1.halt.injEq] at h
    exact ⟨h.1.symm, h.2.symm, Or.inl hend⟩
  case isFalse hend =>
    cases hfetch : C[pc]? with
    | none => simp [hfetch] at h
    | some i =>
        simp only [hfetch] at h
        obtain ⟨hstop, hσ, hst⟩ := execInstr_halt_sound h
        subst hstop
        exact ⟨hσ, hst, Or.inr hfetch⟩

/-- A `.reverted` outcome of `step1` sits on a `REVERT` instruction. -/
theorem step1_revert_sound {C : Code} {c : Conf}
    (h : step1 C c = .reverted) : C[c.pc]? = some Instr.revert := by
  obtain ⟨pc, σ0, st0⟩ := c
  unfold step1 at h
  split at h
  case isTrue => exact absurd h (by simp)
  case isFalse hend =>
    cases hfetch : C[pc]? with
    | none => simp [hfetch] at h
    | some i =>
        simp only [hfetch] at h
        rw [execInstr_revert_sound h]

/-- A `.ok` verdict of the runner is a real execution to a halted
configuration with the reported stack and storage. -/
theorem run_ok_sound {C : Code} :
    ∀ {fuel : Nat} {c : Conf} {σ : List Word} {st : Store},
      run C fuel c = .ok σ st →
      ∃ pc, Steps C c ⟨pc, σ, st⟩ ∧ Halted C ⟨pc, σ, st⟩ := by
  intro fuel
  induction fuel with
  | zero => intro c σ st h; simp [run] at h
  | succ fuel ih =>
      intro c σ st h
      rw [run] at h
      cases hs : step1 C c with
      | next c' =>
          rw [hs] at h
          obtain ⟨p, hsteps, hh⟩ := ih h
          exact ⟨p, Steps.head (step1_next_sound hs) hsteps, hh⟩
      | halt σ' st' =>
          rw [hs] at h
          cases h
          obtain ⟨hσ, hst, hhalted⟩ := step1_halt_sound hs
          subst hσ hst
          exact ⟨c.pc, by cases c; exact Steps.refl _,
            by cases c; exact hhalted⟩
      | reverted => rw [hs] at h; exact absurd h (by simp)
      | stuck => rw [hs] at h; exact absurd h (by simp)

/-- A `.reverted` verdict of the runner is a real execution to a
`REVERT` instruction. -/
theorem run_revert_sound {C : Code} :
    ∀ {fuel : Nat} {c : Conf},
      run C fuel c = .reverted → Reverting C c := by
  intro fuel
  induction fuel with
  | zero => intro c h; simp [run] at h
  | succ fuel ih =>
      intro c h
      rw [run] at h
      cases hs : step1 C c with
      | next c' =>
          rw [hs] at h
          exact (ih h).of_steps' (step1_next_sound hs)
      | halt σ' st' => rw [hs] at h; exact absurd h (by simp)
      | reverted =>
          exact ⟨c, Steps.refl _, step1_revert_sound hs⟩
      | stuck => rw [hs] at h; exact absurd h (by simp)

end Evm
end Solidity
