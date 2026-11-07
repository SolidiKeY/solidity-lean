import Solidity.Evm.Machine

/-!
# The EVM machine with revert and return data (version 2)

A versioned pair (H57) beside the frozen `Evm.Machine`/`Evm.Out`/`Evm.run`
of `Evm/Machine.lean`, which this module leaves unchanged.  The frozen model
has no data on a frame's exit: `Out.revert` carries no bytes, success is the
end of the code, and `CALL` takes only a value and an address.  Version 2
adds, as new declarations only:

* **Byte data at a frame's exit** (`OutV2`): `revert calls data` (EVM
  `REVERT`, with the journal of the external calls made before it, which a
  revert does not undo for the environment) and `ret m data` (EVM `RETURN`),
  a halting success with the final machine.
  Falling off the end of the code is success with empty data (`STOP`).
* **A return buffer** (`MachineV2.returndata`), read by `RETURNDATASIZE`
  and `RETURNDATACOPY`, and set by `CALLIN`.
* **`CALLIN`**, a `CALL` that also reads its input bytes from memory.  The
  callee's code is still not run; its answer is an oracle, `reply`, beside
  the frozen `accepts`: whether the callee accepts is `accepts` (so the
  balance and stack effects are exactly the frozen `CALL`'s), its output
  bytes are `reply callee value input`.  An entered call (the contract
  covers the value) sets the return buffer to that output and records the
  call in the ghost journal `calls`; a call that is not entered empties the
  buffer and records nothing.  This is the shape of the Bridge reference
  law `CallReturndataLaw.call_returnData` on V15's branch (an entered call's buffer is the
  callee's output, otherwise empty), without depth or gas.

**Memory stays word-addressed.**  A byte window starts at a cell and covers
`⌈len / 32⌉` cells, each the 32 big-endian bytes of its word
(`wordBytes`); solc builds revert and return data at a 32-byte aligned free
pointer, so the start is a cell.  A window over a cell holding a storage
slot (`Word.slot`) faults: such a word has no bytes.  `RETURNDATACOPY`
writes whole cells and keeps the bytes of a partly written last cell; it
faults when the source window leaves the buffer, as the EVM does.

**Migration.**  Every frozen instruction is a version-2 instruction
(`InstrV2.base`) that leaves the new fields alone, so frozen code embeds
(`lift`) and runs exactly as before: `run_lift` gives the version-2 outcome
of lifted code from the frozen one, and `forget_run_lift` the frozen outcome
from the version-2 one (forgetting data).  `callIn_forget` relates `CALLIN`
to the frozen `CALL`.  Frozen statements are untouched; no dependent of
`Evm/Machine.lean` imports this module.
-/

namespace Solidity
namespace Evm

/-! ## Bytes of words -/

/-- The 32 big-endian bytes of a word: what `MSTORE` lays out. -/
def wordBytes (n : Fin W) : List UInt8 :=
  (List.range 32).map fun i => UInt8.ofNat (n.1 / 256 ^ (31 - i))

/-- One big-endian digit more. -/
def byteStep (acc : Nat) (b : UInt8) : Nat := acc * 256 + b.toNat

/-- The number of the first 32 bytes, big-endian, padded on the right with
zeroes: what `MLOAD` reads from a byte window. -/
def bytesNat (bs : List UInt8) : Nat :=
  ((bs ++ List.replicate 32 0).take 32).foldl byteStep 0

theorem bytesNat_fold_lt (l : List UInt8) (acc : Nat) :
    l.foldl byteStep acc < (acc + 1) * 256 ^ l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, List.length_cons, byteStep]
    have h := ih (acc * 256 + b.toNat)
    simp only [byteStep] at h
    have hb : b.toNat < 256 := b.toNat_lt
    have : (acc * 256 + b.toNat + 1) * 256 ^ l.length ≤ (acc + 1) * 256 ^ (l.length + 1) := by
      rw [Nat.pow_succ', ← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    omega

/-- The word of a byte window's first 32 bytes. -/
def bytesWord (bs : List UInt8) : Fin W :=
  ⟨bytesNat bs, by
    have h := bytesNat_fold_lt ((bs ++ List.replicate 32 0).take 32) 0
    have hl : ((bs ++ List.replicate 32 0).take 32).length = 32 := by
      simp only [List.length_take, List.length_append, List.length_replicate]; omega
    rw [hl, Nat.zero_add, Nat.one_mul] at h
    have hw : (256 : Nat) ^ 32 = W := by unfold W; rfl
    rw [hw] at h
    exact h⟩

/-- The number of cells a window of `len` bytes covers: `⌈len / 32⌉`. -/
def cellsOf (len : Nat) : Nat := (len + 31) / 32

/-- The bytes of the cells `o, o + 1, …, o + n - 1`, `none` at a slot. -/
def readCells (mem : Nat → Word) (o : Nat) : Nat → Option (List UInt8)
  | 0 => some []
  | n + 1 => match mem o with
    | .val w => (readCells mem (o + 1) n).map (wordBytes w ++ ·)
    | .slot _ => none

/-- The `len` bytes of memory from cell `o`: `REVERT`'s and `RETURN`'s data. -/
def readBytes (mem : Nat → Word) (o len : Nat) : Option (List UInt8) :=
  (readCells mem o (cellsOf len)).map (·.take len)

/-- Write `bs` from cell `o` on, 32 bytes a cell, over at most `n` cells; a
last cell written only in part keeps its remaining bytes, so it must hold a
number. -/
def writeCells : Nat → (Nat → Word) → Nat → List UInt8 → Option (Nat → Word)
  | 0, mem, _, _ => some mem
  | _ + 1, mem, _, [] => some mem
  | n + 1, mem, o, b :: bs =>
    let chunk := (b :: bs).take 32
    if chunk.length = 32 then writeCells n (upd mem o (.val (bytesWord chunk))) (o + 1) (bs.drop 31)
    else match mem o with
      | .val w => some (upd mem o (.val (bytesWord (chunk ++ (wordBytes w).drop chunk.length))))
      | .slot _ => none

/-- Write `bs` from cell `o` on: `RETURNDATACOPY`'s memory effect. -/
def writeBytes (mem : Nat → Word) (o : Nat) (bs : List UInt8) : Option (Nat → Word) :=
  writeCells (cellsOf bs.length) mem o bs

/-! ## The machine and its outcomes -/

/-- One call `CALLIN` made to another account: callee, value, input bytes,
whether the callee accepted, and its output bytes. -/
structure CallRec where
  callee : Fin W
  value : Fin W
  input : List UInt8
  success : Bool
  output : List UInt8
  deriving DecidableEq, Repr

/-- The version-2 machine: the frozen machine, the return buffer, the
callee oracle and the ghost journal of calls. -/
structure MachineV2 where
  base : Machine
  /-- The return buffer: the output of the last entered `CALLIN`. -/
  returndata : List UInt8 := []
  /-- The output bytes of a call of `callee` with `value` and `input`: its
  return data when `accepts` holds, its revert data otherwise. -/
  reply : Fin W → Fin W → List UInt8 → List UInt8 := fun _ _ _ => []
  /-- The calls made so far, oldest first: a ghost, read by no instruction. -/
  calls : List CallRec := []

/-- A frozen machine with an empty buffer, journal and silent callees. -/
def MachineV2.ofBase (m : Machine) : MachineV2 := { base := m }

/-- Replace the frozen part. -/
def MachineV2.withBase (m : MachineV2) (b : Machine) : MachineV2 := { m with base := b }

@[simp] theorem MachineV2.withBase_base (m : MachineV2) (b : Machine) :
    (m.withBase b).base = b := rfl

@[simp] theorem MachineV2.withBase_self (m : MachineV2) : m.withBase m.base = m := rfl

/-- A version-2 outcome: continue with a pending skip, `RETURN` with data,
`REVERT` with data (and the calls journaled before it), or a fault. -/
inductive OutV2 where
  | ok (m : MachineV2) (skip : Nat)
  | ret (m : MachineV2) (data : List UInt8)
  | revert (calls : List CallRec) (data : List UInt8)
  | fault

instance : Inhabited OutV2 := ⟨.fault⟩

def OutV2.bind : OutV2 → (MachineV2 → Nat → OutV2) → OutV2
  | .ok m k, f => f m k
  | .ret m d, _ => .ret m d
  | .revert cs d, _ => .revert cs d
  | .fault, _ => .fault

@[simp] theorem OutV2.ok_bind (m : MachineV2) (k : Nat) (f : MachineV2 → Nat → OutV2) :
    (OutV2.ok m k).bind f = f m k := rfl
@[simp] theorem OutV2.ret_bind (m : MachineV2) (d : List UInt8) (f : MachineV2 → Nat → OutV2) :
    (OutV2.ret m d).bind f = .ret m d := rfl
@[simp] theorem OutV2.revert_bind (cs : List CallRec) (d : List UInt8)
    (f : MachineV2 → Nat → OutV2) : (OutV2.revert cs d).bind f = .revert cs d := rfl
@[simp] theorem OutV2.fault_bind (f : MachineV2 → Nat → OutV2) : OutV2.fault.bind f = .fault := rfl

theorem OutV2.bind_assoc (o : OutV2) (f g : MachineV2 → Nat → OutV2) :
    (o.bind f).bind g = o.bind (fun m k => (f m k).bind g) := by
  cases o <;> rfl

/-- **Forgetting data**: the frozen outcome.  A `RETURN` forgets to the end
of the code (the frozen model has no halting success); revert data is
dropped. -/
def OutV2.forget : OutV2 → Out
  | .ok m k => .ok m.base k
  | .ret m _ => .ok m.base 0
  | .revert _ _ => .revert
  | .fault => .fault

/-- A frozen outcome on top of the version-2 fields of `m`. -/
def OutV2.ofOut (m : MachineV2) : Out → OutV2
  | .ok b k => .ok (m.withBase b) k
  | .revert => .revert m.calls []
  | .fault => .fault

@[simp] theorem OutV2.forget_ofOut (m : MachineV2) (o : Out) : (OutV2.ofOut m o).forget = o := by
  cases o <;> rfl

/-- A frame's exit as its caller sees it: success with return data, revert
with revert data, or no exit (a fault, or a jump still pending). -/
def OutV2.exit : OutV2 → Option (Bool × List UInt8)
  | .ok _ 0 => some (true, [])
  | .ret _ d => some (true, d)
  | .revert _ d => some (false, d)
  | .ok _ (_ + 1) => none
  | .fault => none

/-- A revert exit is a revert with that data: decidable, so the kernel can
check a run's revert data (`decide +kernel`) where unfolding `execV2` in the
elaborator is slow. -/
theorem OutV2.eq_revert_of_exit {o : OutV2} {d : List UInt8} (h : o.exit = some (false, d)) :
    ∃ cs, o = .revert cs d := by
  cases o with
  | ok m k => cases k <;> simp only [OutV2.exit, Option.some.injEq, Prod.mk.injEq,
      Bool.true_eq_false, false_and, reduceCtorEq] at h
  | ret m e => simp only [OutV2.exit, Option.some.injEq, Prod.mk.injEq, Bool.true_eq_false,
      false_and] at h
  | revert cs e =>
    simp only [OutV2.exit, Option.some.injEq, Prod.mk.injEq, true_and] at h
    exact ⟨cs, by rw [h]⟩
  | fault => simp only [OutV2.exit, reduceCtorEq] at h

/-- A revert's journal and data (decidable). -/
def OutV2.revertView : OutV2 → Option (List CallRec × List UInt8)
  | .revert cs d => some (cs, d)
  | _ => none

theorem OutV2.eq_revertView {o : OutV2} {cs : List CallRec} {d : List UInt8}
    (h : o.revertView = some (cs, d)) : o = .revert cs d := by
  cases o <;> simp only [OutV2.revertView, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  rw [h.1, h.2]

/-- The continuing machine's stack, return buffer and journal (decidable). -/
def OutV2.okView : OutV2 → Option (List Word × List UInt8 × List CallRec)
  | .ok m 0 => some (m.base.stack, m.returndata, m.calls)
  | _ => none

/-- Whether an outcome is a fault (decidable). -/
def OutV2.isFault : OutV2 → Bool
  | .fault => true
  | _ => false

theorem OutV2.eq_fault {o : OutV2} (h : o.isFault = true) : o = .fault := by
  cases o <;> first | rfl | (simp only [OutV2.isFault, Bool.false_eq_true] at h)

/-! ## Instructions -/

inductive InstrV2 where
  /-- A frozen instruction, with its frozen meaning; it leaves the return
  buffer, the oracle and the journal alone. -/
  | base (i : Instr)
  /-- `REVERT(offset, len)`: the cell on top, then the byte length. -/
  | revertData
  /-- `RETURN(offset, len)`: the cell on top, then the byte length. -/
  | ret
  /-- `RETURNDATASIZE`. -/
  | returndatasize
  /-- `RETURNDATACOPY(dest, offset, len)`: the destination cell on top,
  then the byte offset in the buffer, then the byte length. -/
  | returndatacopy
  /-- `CALL` with input: value on top, then callee, input cell, input byte
  length (the frozen `CALL`'s order plus the input window; no gas and no
  output window, the output is read with `RETURNDATACOPY`); pushes `1` or
  `0` as the frozen `CALL` does. -/
  | callIn
  /-- A loop over version-2 code. -/
  | loop (cond body : List InstrV2)
  deriving Repr, Inhabited

/-- Frozen code as version-2 code. -/
def lift (c : List Instr) : List InstrV2 := c.map .base

@[simp] theorem lift_nil : lift [] = [] := rfl
@[simp] theorem lift_cons (i : Instr) (c : List Instr) : lift (i :: c) = .base i :: lift c := rfl
theorem lift_append (c₁ c₂ : List Instr) : lift (c₁ ++ c₂) = lift c₁ ++ lift c₂ :=
  List.map_append

/-! ## Loops (the frozen loop machinery over version-2 outcomes) -/

def loopTurnV2 (rc rb : MachineV2 → OutV2) (m : MachineV2) : MachineV2 ⊕ OutV2 :=
  match rc m with
  | .ok m₁ 0 => match m₁.base.stack with
    | .val w :: st =>
      let m₁' := m₁.withBase { m₁.base with stack := st }
      if w.1 = 0 then .inr (.ok m₁' 0) else
        match rb m₁' with
        | .ok m₂ 0 => .inl m₂
        | .ok _ (_ + 1) => .inr .fault
        | r => .inr r
    | _ => .inr .fault
  | .ok _ (_ + 1) => .inr .fault
  | r => .inr r

def loopIterNV2 (rc rb : MachineV2 → OutV2) : Nat → MachineV2 → MachineV2 ⊕ OutV2
  | 0, m => .inl m
  | n + 1, m => match loopTurnV2 rc rb m with
    | .inl m' => loopIterNV2 rc rb n m'
    | .inr r => .inr r

open Classical in
/-- A version-2 loop's outcome: what the turns end with, a fault where no
number of turns ends it.  Unlike the frozen `loopRun` it has no compiled
twin: version-2 runs are checked by the kernel, not evaluated. -/
noncomputable def loopRunV2 (rc rb : MachineV2 → OutV2) (m : MachineV2) : OutV2 :=
  if h : ∃ r n, loopIterNV2 rc rb n m = .inr r then Classical.choose h else .fault

theorem loopIterNV2_done_le {rc rb : MachineV2 → OutV2} {n k : Nat} {m : MachineV2} {r : OutV2}
    (hnk : n ≤ k) (h : loopIterNV2 rc rb n m = .inr r) : loopIterNV2 rc rb k m = .inr r := by
  induction n generalizing m k with
  | zero => simp only [loopIterNV2, reduceCtorEq] at h
  | succ n ih =>
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [loopIterNV2] at h ⊢
    split at h
    · exact ih (by omega) h
    · exact h

theorem loopRunV2_of_iterN {rc rb : MachineV2 → OutV2} {n : Nat} {m : MachineV2} {r : OutV2}
    (h : loopIterNV2 rc rb n m = .inr r) : loopRunV2 rc rb m = r := by
  have hex : ∃ r n, loopIterNV2 rc rb n m = .inr r := ⟨r, n, h⟩
  simp only [loopRunV2, hex, dif_pos]
  obtain ⟨n', hn'⟩ := Classical.choose_spec hex
  have h1 := loopIterNV2_done_le (Nat.le_max_left n n') h
  have h2 := loopIterNV2_done_le (Nat.le_max_right n n') hn'
  rw [h1] at h2
  exact (Sum.inr.inj h2).symm

theorem loopRunV2_of_forall {rc rb : MachineV2 → OutV2} {m : MachineV2}
    (h : ∀ n, ∃ m', loopIterNV2 rc rb n m = .inl m') : loopRunV2 rc rb m = .fault := by
  have hex : ¬ ∃ r n, loopIterNV2 rc rb n m = .inr r := by
    rintro ⟨r, n, hn⟩
    obtain ⟨m', hm'⟩ := h n
    rw [hm'] at hn
    cases hn
  simp only [loopRunV2, hex, dif_neg, not_false_eq_true]

/-! ## Steps -/

/-- `CALLIN` on the popped value `v`, callee `a` and input bytes: the frozen
`CALL`'s balance and stack effect, the return buffer and the journal. -/
def callInStep (m : MachineV2) (v a : Fin W) (input : List UInt8) (st : List Word) : OutV2 :=
  if m.base.bal m.base.self < v.1 then
    .ok { m with base := { m.base with stack := w[0] :: st }, returndata := [] } 0
  else
    let out := m.reply a v input
    let accepted := m.base.accepts a v
    let m' : MachineV2 :=
      { m with returndata := out, calls := m.calls ++ [CallRec.mk a v input accepted out] }
    if accepted = false then .ok (m'.withBase { m.base with stack := w[0] :: st }) 0
    else if a = m.base.self then .ok (m'.withBase { m.base with stack := w[1] :: st }) 0
    else
      let paid : Machine := { m.base with stack := w[1] :: st }
      .ok (m'.withBase { paid with bal := pay m.base.bal m.base.self a v.1 }) 0

/-- `RETURNDATACOPY` on the popped destination cell, buffer offset and length. -/
def copyStep (m : MachineV2) (d o len : Nat) (st : List Word) : OutV2 :=
  if m.returndata.length < o + len then .fault else
    match writeBytes m.base.mem d ((m.returndata.drop o).take len) with
    | some mem => .ok (m.withBase { m.base with stack := st, mem }) 0
    | none => .fault

mutual

/-- One version-2 instruction. -/
noncomputable def InstrV2.step : InstrV2 → MachineV2 → OutV2
  | .base i, m => OutV2.ofOut m (i.step m.base)
  | .revertData, m => match m.base.stack with
    | .val o :: .val n :: _ => match readBytes m.base.mem o.1 n.1 with
      | some d => .revert m.calls d
      | none => .fault
    | _ => .fault
  | .ret, m => match m.base.stack with
    | .val o :: .val n :: st => match readBytes m.base.mem o.1 n.1 with
      | some d => .ret (m.withBase { m.base with stack := st }) d
      | none => .fault
    | _ => .fault
  | .returndatasize, m =>
    .ok (m.withBase { m.base with stack := .val (wmod m.returndata.length) :: m.base.stack }) 0
  | .returndatacopy, m => match m.base.stack with
    | .val d :: .val o :: .val n :: st => copyStep m d.1 o.1 n.1 st
    | _ => .fault
  | .callIn, m => match m.base.stack with
    | .val v :: .val a :: .val o :: .val n :: st => match readBytes m.base.mem o.1 n.1 with
      | some input => callInStep m v a input st
      | none => .fault
    | _ => .fault
  | .loop c b, m => loopRunV2 (fun m => execV2 c 0 m) (fun m => execV2 b 0 m) m

/-- Run version-2 code, skipping `k` instructions first. -/
noncomputable def execV2 : List InstrV2 → Nat → MachineV2 → OutV2
  | [], k, m => .ok m k
  | _ :: c, k + 1, m => execV2 c k m
  | i :: c, 0, m => (i.step m).bind (fun m' k' => execV2 c k' m')

end

/-- Run version-2 code from its first instruction. -/
noncomputable def runV2 (c : List InstrV2) (m : MachineV2) : OutV2 := execV2 c 0 m

@[simp] theorem execV2_nil (k : Nat) (m : MachineV2) : execV2 [] k m = .ok m k := rfl
@[simp] theorem execV2_cons_succ (i : InstrV2) (c : List InstrV2) (k : Nat) (m : MachineV2) :
    execV2 (i :: c) (k + 1) m = execV2 c k m := rfl
@[simp] theorem execV2_cons_zero (i : InstrV2) (c : List InstrV2) (m : MachineV2) :
    execV2 (i :: c) 0 m = (i.step m).bind (fun m' k' => execV2 c k' m') := rfl

theorem execV2_append (c₁ c₂ : List InstrV2) (k : Nat) (m : MachineV2) :
    execV2 (c₁ ++ c₂) k m = (execV2 c₁ k m).bind (fun m' k' => execV2 c₂ k' m') := by
  induction c₁ generalizing k m with
  | nil => rfl
  | cons i c ih =>
    cases k with
    | succ k => exact ih k m
    | zero =>
      simp only [List.cons_append, execV2_cons_zero, OutV2.bind_assoc]
      congr 1; funext m' k'; exact ih k' m'

theorem runV2_append_ok {c₁ c₂ : List InstrV2} {m m' : MachineV2} (h : runV2 c₁ m = .ok m' 0) :
    runV2 (c₁ ++ c₂) m = runV2 c₂ m' := by
  simp only [runV2] at h ⊢; rw [execV2_append, h]; rfl

theorem runV2_append_revert {c₁ c₂ : List InstrV2} {m : MachineV2} {cs : List CallRec}
    {d : List UInt8} (h : runV2 c₁ m = .revert cs d) : runV2 (c₁ ++ c₂) m = .revert cs d := by
  simp only [runV2] at h ⊢; rw [execV2_append, h]; rfl

theorem runV2_append_ret {c₁ c₂ : List InstrV2} {m m' : MachineV2} {d : List UInt8}
    (h : runV2 c₁ m = .ret m' d) : runV2 (c₁ ++ c₂) m = .ret m' d := by
  simp only [runV2] at h ⊢; rw [execV2_append, h]; rfl

/-! ## Migration: version 2 → frozen -/

/-- **Lifted frozen code runs as before**, on the frozen part, and leaves the
return buffer, oracle and journal alone. -/
theorem execV2_lift (c : List Instr) (k : Nat) (m : MachineV2) :
    execV2 (lift c) k m = OutV2.ofOut m (exec c k m.base) := by
  induction c generalizing k m with
  | nil => rfl
  | cons i c ih =>
    cases k with
    | succ k => exact ih k m
    | zero =>
      simp only [lift_cons, execV2_cons_zero, exec_cons_zero, InstrV2.step]
      cases i.step m.base with
      | ok b k' => exact ih k' (m.withBase b)
      | revert => rfl
      | fault => rfl

theorem run_lift (c : List Instr) (m : MachineV2) :
    runV2 (lift c) m = OutV2.ofOut m (run c m.base) := execV2_lift c 0 m

/-- **Migration**: forgetting the data of a lifted run gives the frozen run. -/
theorem forget_run_lift (c : List Instr) (m : MachineV2) :
    (runV2 (lift c) m).forget = run c m.base := by
  rw [run_lift, OutV2.forget_ofOut]

/-- A frozen run of compiled code, from a fresh version-2 machine. -/
theorem forget_run_lift_ofBase (c : List Instr) (m : Machine) :
    (runV2 (lift c) (MachineV2.ofBase m)).forget = run c m := forget_run_lift c (MachineV2.ofBase m)

/-- A lifted frozen revert reverts with empty data. -/
theorem run_lift_revert {c : List Instr} {m : MachineV2} (h : run c m.base = .revert) :
    runV2 (lift c) m = .revert m.calls [] := by rw [run_lift, h]; rfl

/-- A lifted frozen success keeps the version-2 fields. -/
theorem run_lift_ok {c : List Instr} {m : MachineV2} {b : Machine} {k : Nat}
    (h : run c m.base = .ok b k) : runV2 (lift c) m = .ok (m.withBase b) k := by
  rw [run_lift, h]; rfl

/-- **`CALLIN` forgets to the frozen `CALL`**: same balances and pushed flag,
once the input operands are dropped. -/
theorem callIn_forget (m : MachineV2) (v a : Fin W) (input : List UInt8) (st : List Word) :
    (callInStep m v a input st).forget =
      Instr.call.step { m.base with stack := .val v :: .val a :: st } := by
  simp only [callInStep, Instr.step, Machine.next]
  by_cases hb : m.base.bal m.base.self < v.1
  · rw [if_pos hb, if_pos (Or.inl hb)]; rfl
  · rw [if_neg hb]
    cases ha : m.base.accepts a v
    · rw [if_pos rfl, if_pos (Or.inr rfl)]; rfl
    · have hc : ¬ (m.base.bal m.base.self < v.1 ∨ true = false) :=
        fun h => h.elim hb Bool.noConfusion
      rw [if_neg hc]
      by_cases hs : a = m.base.self
      · simp only [if_pos hs, Bool.true_eq_false, if_false]; rfl
      · simp only [if_neg hs, Bool.true_eq_false, if_false]; rfl

/-- **The return buffer after `CALLIN`** (the core counterpart of the Bridge
law `CallReturndataLaw.call_returnData`): an entered call (the contract
covers the value) leaves the callee's output for its exact input, and is
journaled; a call not entered leaves the buffer empty and the journal
unchanged. -/
theorem callIn_returndata (m : MachineV2) (v a : Fin W) (input : List UInt8) (st : List Word) :
    ∃ m' , callInStep m v a input st = .ok m' 0 ∧
      ((v.1 ≤ m.base.bal m.base.self ∧ m'.returndata = m.reply a v input ∧
          m'.calls = m.calls ++ [⟨a, v, input, m.base.accepts a v, m.reply a v input⟩]) ∨
        (m.base.bal m.base.self < v.1 ∧ m'.returndata = [] ∧ m'.calls = m.calls)) ∧
      m'.reply = m.reply := by
  simp only [callInStep]
  by_cases hb : m.base.bal m.base.self < v.1
  · rw [if_pos hb]
    exact ⟨_, rfl, .inr ⟨hb, rfl, rfl⟩, rfl⟩
  · rw [if_neg hb]
    have hle : v.1 ≤ m.base.bal m.base.self := by omega
    by_cases ha : m.base.accepts a v = false
    · rw [if_pos ha]
      exact ⟨_, rfl, .inl ⟨hle, rfl, rfl⟩, rfl⟩
    · rw [if_neg ha]
      by_cases hs : a = m.base.self
      · rw [if_pos hs]
        exact ⟨_, rfl, .inl ⟨hle, rfl, rfl⟩, rfl⟩
      · rw [if_neg hs]
        exact ⟨_, rfl, .inl ⟨hle, rfl, rfl⟩, rfl⟩

/-- **`CALLIN`'s input is its memory window**: on value `v`, callee `a`,
input cell `o` and byte length `n`, the step is `callInStep` on exactly the
bytes `readBytes` reads, and faults when that window holds a slot. -/
theorem callIn_step (m : MachineV2) (v a o n : Fin W) (st : List Word) :
    InstrV2.callIn.step (m.withBase { m.base with stack := .val v :: .val a :: .val o :: .val n :: st }) =
      match readBytes m.base.mem o.1 n.1 with
      | some input => callInStep (m.withBase { m.base with stack := .val v :: .val a :: .val o :: .val n :: st })
          v a input st
      | none => .fault := rfl

/-- The frozen `REVERT` and the data-carrying one forget alike. -/
theorem revertData_forget (m : MachineV2) (o n : Fin W) (st : List Word) (d : List UInt8)
    (h : readBytes m.base.mem o.1 n.1 = some d) :
    (InstrV2.revertData.step (m.withBase { m.base with stack := .val o :: .val n :: st })).forget =
      Instr.revert.step m.base := by
  simp only [InstrV2.step, MachineV2.withBase_base, h, OutV2.forget, Instr.step]

end Evm
end Solidity
