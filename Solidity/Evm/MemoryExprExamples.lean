import Solidity.Evm.Compiler
import Solidity.Evm.MemoryCompileExamples

/-! End-to-end regressions for memory operands in arithmetic, guards and
storage writes. Source results are actual scoped program runs; target results
run code returned by the public checked compiler. -/
namespace Solidity.Evm.Memory.ExprExamples

open CompileExamples (C Γ hp r0 r1 base σ machine fixture_repr fixture_six_cells)

private def first : Idx Γ (.mem (.array (.prim .uint))) := .there (.there .here)
private def other : Idx Γ (.mem (.array (.prim .uint))) := .there (.there (.there .here))

private def element (D : Contract) (i : Idx Γ (.mem (.array (.prim .uint))))
    (n : Int) (hn : PrimTy.uint.inRange n = true) : Val D Γ .uint :=
  .readMem (.index .dyn (.var i rfl) (.simple (.lit n hn)))
private def a : Val C Γ .uint := element C first 0 rfl
private def b : Val C Γ .uint := element C first 1 rfl
private def bad : Val C Γ .uint := element C other 1 rfl
private def lit (n : Int) (hn : PrimTy.uint.inRange n = true) : Val C Γ .uint := .simple (.lit n hn)

private def program {p : PrimTy} (e : Val C Γ p) : Prog C Γ (.val p :: Γ) :=
  .cons (.declLocal p (.user "result") (some e)) .nil

private def number : (p : PrimTy) → p.Denote → Option Int
  | .uint, v | .int, v => some v.1
  | .bool, _ => none

private def sourceNumber {p : PrimTy} (e : Val C Γ p) : Option Int :=
  match (program e).run σ with
  | .ok o => number p (TEnv.get (.here : Idx (.val p :: Γ) _) o.st.env)
  | .error _ => none

private def sourceBool (e : Val C Γ .bool) : Option Bool :=
  match (program e).run σ with
  | .ok o => some (TEnv.get (.here : Idx (.val .bool :: Γ) _) o.st.env)
  | .error _ => none

private def targetNumber {p : PrimTy} (e : Val C Γ p) : Option Nat := do
  let c ← Compiler.compile 0 (Frag.init Γ) (program e)
  match run c.code machine with
  | .ok m _ => match m.mem 4 with | .val w => some w.1 | _ => none
  | _ => none

private def sourceReverted {p : PrimTy} (e : Val C Γ p) : Bool :=
  match (program e).run σ with | .error .revert => true | _ => false
private def targetReverted {p : PrimTy} (e : Val C Γ p) : Bool :=
  match Compiler.compile 0 (Frag.init Γ) (program e) with
  | some c => match run c.code machine with | .revert => true | _ => false
  | none => false

def sumProduct : Val C Γ .uint :=
  .binop .mul rfl rfl (.binop .add rfl rfl a b) (lit 2 rfl)
def compiledArithmetic : Compiler.Compilation 0 (Frag.init Γ) (program sumProduct) :=
  (Compiler.compile 0 (Frag.init Γ) (program sumProduct)).get (by decide +kernel)

theorem arithmetic_simulates : compiledArithmetic.Agrees 1 6 base σ machine :=
  compiledArithmetic.correct ⟨fixture_six_cells, by decide +kernel, .inl (by decide +kernel)⟩

example : sourceNumber sumProduct = some 32 := by decide +kernel
example : targetNumber sumProduct = some 32 := by decide +kernel

private def failingBool : Val C Γ .bool := .binop .eqB rfl rfl bad (lit 0 rfl)
private def shortAnd : Val C Γ .bool :=
  .binop .and rfl rfl (.binop .gt rfl rfl a b) failingBool
private def shortOr : Val C Γ .bool :=
  .binop .or rfl rfl (.binop .lt rfl rfl a b) failingBool

/-- The rejected read is compiled, but the chosen Boolean path skips it. -/
example : sourceBool shortAnd = some false := by decide +kernel
example : targetNumber shortAnd = some 0 := by decide +kernel
example : sourceBool shortOr = some true := by decide +kernel
example : targetNumber shortOr = some 1 := by decide +kernel
example : sourceBool (.unop .not rfl rfl shortAnd) = some true := by decide +kernel
example : targetNumber (.unop .not rfl rfl shortAnd) = some 1 := by decide +kernel

private def failAnd : Val C Γ .bool :=
  .binop .and rfl rfl (.binop .lt rfl rfl a b) failingBool
private def failOr : Val C Γ .bool :=
  .binop .or rfl rfl (.binop .gt rfl rfl a b) failingBool
example : sourceReverted failAnd = true := by decide +kernel
example : targetReverted failAnd = true := by decide +kernel
example : sourceReverted failOr = true := by decide +kernel
example : targetReverted failOr = true := by decide +kernel

private def conditional : Val C Γ .uint :=
  .ternary (.binop .lt rfl rfl a b) (.binop .div rfl rfl b (lit 3 rfl)) bad
example : sourceNumber conditional = some 3 := by decide +kernel
example : targetNumber conditional = some 3 := by decide +kernel

private def conditionalElse : Val C Γ .uint :=
  .ternary (.binop .gt rfl rfl a b) bad (.binop .div rfl rfl b (lit 3 rfl))
example : sourceNumber conditionalElse = some 3 := by decide +kernel
example : targetNumber conditionalElse = some 3 := by decide +kernel

private def negative : Val C Γ .int := .unop .neg rfl rfl (.unop .toInt rfl rfl a)
example : sourceNumber negative = some (-7) := by decide +kernel
example : targetNumber negative = some (W - 7) := by decide +kernel

private def underflow : Val C Γ .uint := .binop .sub rfl rfl a b
private def overflow : Val C Γ .uint :=
  .binop .add rfl rfl a (lit ((W - 1 : Nat) : Int) (by decide +kernel))
private def divZero : Val C Γ .uint := .binop .div rfl rfl a (.binop .sub rfl rfl b b)
example : sourceReverted underflow = true := by decide +kernel
example : targetReverted underflow = true := by decide +kernel
example : sourceReverted overflow = true := by decide +kernel
example : targetReverted overflow = true := by decide +kernel
example : sourceReverted divZero = true := by decide +kernel
example : targetReverted divZero = true := by decide +kernel

def guarded : Prog C Γ Γ :=
  .cons (.require (.binop .lt rfl rfl a b)) (.cons (.assignLocal .here sumProduct) .nil)
def checkedGuard : Compiler.Compilation 0 (Frag.init Γ) guarded :=
  (Compiler.compile 0 (Frag.init Γ) guarded).get (by decide +kernel)
theorem guard_simulates : checkedGuard.Agrees 1 4 base σ machine :=
  checkedGuard.correct ⟨fixture_repr, by decide +kernel, .inl (by decide +kernel)⟩

private def localResult (out : TRes (Solidity.Out C CompileExamples.H Γ)) : Option Int :=
  match out with | .ok o => some (TEnv.get (.here : Idx Γ (.val .uint)) o.st.env).1 | _ => none
private def cell (out : Out) (n : Nat) : Option Nat :=
  match out with
  | .ok m _ => match m.mem n with | .val w => some w.1 | _ => none
  | _ => none

example : localResult (guarded.run σ) = some 32 := by decide +kernel
example : cell (run checkedGuard.code machine) 3 = some 32 := by decide +kernel

def falseGuard : Prog C Γ Γ :=
  .cons (.require (.binop .gt rfl rfl a b)) (.cons (.assignLocal .here sumProduct) .nil)
def checkedFalseGuard : Compiler.Compilation 0 (Frag.init Γ) falseGuard :=
  (Compiler.compile 0 (Frag.init Γ) falseGuard).get (by decide +kernel)
example : (match falseGuard.run σ with | .error .revert => true | _ => false) = true := by decide +kernel
example : run checkedFalseGuard.code machine = .revert :=
  Out.eq_revert (by decide +kernel)

namespace CompoundCase

private def update (op : BinOp) (hop : op.hasCompoundAssign = true)
    (i : Simple C Γ .uint) (r : Val C Γ .uint) : Stmt C Γ Γ :=
  .opAssign op hop rfl (.mindex .dyn (.var first rfl) i) r
private def updateLocal (op : BinOp) (hop : op.hasCompoundAssign = true)
    (r : Val C Γ .uint) : Stmt C Γ Γ :=
  .opAssign op hop rfl (.local .here) r
private def sequence : Prog C Γ Γ :=
  .cons (update .add rfl (.local .here) b)
  (.cons (updateLocal .add rfl a)
  (.cons (update .mul rfl (.lit 1 rfl) a)
  (.cons (update .sub rfl (.lit 1 rfl) (.simple (.local .here)))
  (.cons (update .div rfl (.lit 1 rfl) (lit 7 rfl))
  (.cons (update .mod rfl (.lit 0 rfl) (lit 3 rfl))
  (.cons (updateLocal .add rfl b) .nil))))))
private def compiled : Compiler.Compilation 0 (Frag.init Γ) sequence :=
  (Compiler.compile 0 (Frag.init Γ) sequence).get (by decide +kernel)

/-- All five compound operators compose with memory operands and primitive locals. -/
theorem simulates : compiled.Agrees 1 4 base σ machine := by
  apply compiled.correct
  rw [compiled.memory_input (by decide +kernel)]
  exact ⟨fixture_repr, by decide +kernel, .inl (by decide +kernel)⟩

private def sourceValues (out : TRes (Solidity.Out C CompileExamples.H Γ)) : Option (List Int) := do
  let o ← out.toOption
  let av ← (a.evalT o.st).toOption
  let bv ← (b.evalT o.st).toOption
  let aliasValue ← (element C (.there .here) 0 rfl).evalT o.st |>.toOption
  let independent ← (element C other 0 rfl).evalT o.st |>.toOption
  pure [av.val, bv.val, aliasValue.val, (TEnv.get (.here : Idx Γ (.val .uint)) o.st.env).val,
    independent.val, o.st.H.length]
private def targetValues (out : Out) : Option (List Nat) :=
  [3, 17, 18, 21, 16, 20, 0, 1, 2].mapM (cell out)

theorem source : sourceValues (sequence.run σ) = some [1, 18, 1, 34, 4, 2] := by
  decide +kernel
theorem target : targetValues (run compiled.code machine) = some [34, 1, 18, 4, 2, 1, 20, 16, 16] := by
  decide +kernel

inductive Failure where
  | bounds | rhs | both | underflow | overflow | divZero | modZero | localRhs | localOverflow

private def failure : Failure → Prog C Γ Γ
  | .bounds => .cons (update .add rfl (.lit 2 rfl) (lit 0 rfl)) .nil
  | .rhs => .cons (update .add rfl (.lit 0 rfl) bad) .nil
  | .both => .cons (update .add rfl (.lit 2 rfl) bad) .nil
  | .underflow => .cons (update .sub rfl (.lit 0 rfl) b) .nil
  | .overflow => .cons (update .add rfl (.lit 0 rfl)
      (lit ((W - 1 : Nat) : Int) (by decide +kernel))) .nil
  | .divZero => .cons (update .div rfl (.lit 0 rfl) (lit 0 rfl)) .nil
  | .modZero => .cons (update .mod rfl (.lit 0 rfl) (lit 0 rfl)) .nil
  | .localRhs => .cons (updateLocal .add rfl bad) .nil
  | .localOverflow =>
      .cons (.assignLocal .here (lit ((W - 1 : Nat) : Int) (by decide +kernel)))
        (.cons (updateLocal .add rfl a) .nil)
private def compiledFailure (f : Failure) : Compiler.Compilation 0 (Frag.init Γ) (failure f) :=
  (Compiler.compile 0 (Frag.init Γ) (failure f)).get (by cases f <;> decide +kernel)

/-- Failed reads, range checks and zero divisors use inhabited public compiler inputs. -/
theorem failure_simulates (f : Failure) : (compiledFailure f).Agrees 1 4 base σ machine := by
  apply (compiledFailure f).correct
  rw [(compiledFailure f).memory_input (by cases f <;> decide +kernel)]
  exact ⟨fixture_repr, by cases f <;> decide +kernel, .inl (by cases f <;> decide +kernel)⟩

theorem failure_source (f : Failure) :
    (match (failure f).run σ with | .error .revert => true | _ => false) = true := by
  cases f <;> decide +kernel

theorem failure_target (f : Failure) : run (compiledFailure f).code machine = .revert := by
  cases f <;> exact Out.eq_revert (by decide +kernel)

end CompoundCase

namespace IncrementCase

private def sequence (op : IncDec) : Prog C Γ Γ :=
  .cons (.assignLocal .here (lit 1 rfl))
    (.cons (.incDec op rfl (.mindex .dyn (.var first rfl) (.lit 0 rfl)))
      (.cons (.incDec op rfl (.local .here)) .nil))
private def compiled (op : IncDec) : Compiler.Compilation 0 (Frag.init Γ) (sequence op) :=
  (Compiler.compile 0 (Frag.init Γ) (sequence op)).get (by cases op <;> decide +kernel)

/-- All four bump spellings compose on an aliased element and a primitive local. -/
theorem simulates (op : IncDec) : (compiled op).Agrees 1 4 base σ machine := by
  apply (compiled op).correct
  rw [(compiled op).memory_input (by cases op <;> decide +kernel)]
  exact ⟨fixture_repr, by cases op <;> decide +kernel, .inl (by cases op <;> decide +kernel)⟩

private def sourceValues (op : IncDec) : Option (List Int) := do
  let o ← (sequence op).run σ |>.toOption
  let av ← a.evalT o.st |>.toOption
  let aliasValue ← (element C (.there .here) 0 rfl).evalT o.st |>.toOption
  let independent ← (element C other 0 rfl).evalT o.st |>.toOption
  pure [av.val, aliasValue.val, independent.val,
    (TEnv.get (.here : Idx Γ (.val .uint)) o.st.env).val, o.st.H.length]

theorem source (op : IncDec) : sourceValues op =
    some [if op.isIncrement then 8 else 6, if op.isIncrement then 8 else 6,
      4, if op.isIncrement then 2 else 0, 2] := by
  cases op <;> decide +kernel

theorem target (op : IncDec) :
    ([3, 17, 18, 21, 16, 20, 0, 1, 2].mapM (cell (run (compiled op).code machine))) =
      some [if op.isIncrement then 2 else 0, if op.isIncrement then 8 else 6,
        9, 4, 2, 1, 20, 16, 16] := by
  cases op <;> decide +kernel

inductive Failure where
  | bounds | underflow | overflow | localUnderflow | localOverflow
private def failure : Failure → Prog C Γ Γ
  | .bounds => .cons (.incDec .preInc rfl (.mindex .dyn (.var first rfl) (.lit 2 rfl))) .nil
  | .underflow => .cons (.assignMem (.index .dyn (.var first rfl) (.simple (.lit 0 rfl)))
      (.val (lit 0 rfl)))
      (.cons (.incDec .postDec rfl (.mindex .dyn (.var first rfl) (.lit 0 rfl))) .nil)
  | .overflow => .cons (.assignMem (.index .dyn (.var first rfl) (.simple (.lit 0 rfl)))
      (.val (lit ((W - 1 : Nat) : Int) (by decide +kernel))))
      (.cons (.incDec .postInc rfl (.mindex .dyn (.var first rfl) (.lit 0 rfl))) .nil)
  | .localUnderflow => .cons (.require (.binop .eqB rfl rfl a (lit 7 rfl)))
      (.cons (.incDec .preDec rfl (.local .here)) .nil)
  | .localOverflow =>
      .cons (.require (.binop .eqB rfl rfl a (lit 7 rfl)))
        (.cons (.assignLocal .here (lit ((W - 1 : Nat) : Int) (by decide +kernel)))
          (.cons (.incDec .preInc rfl (.local .here)) .nil))
private def compiledFailure (f : Failure) : Compiler.Compilation 0 (Frag.init Γ) (failure f) :=
  (Compiler.compile 0 (Frag.init Γ) (failure f)).get (by cases f <;> decide +kernel)

theorem failure_simulates (f : Failure) : (compiledFailure f).Agrees 1 4 base σ machine := by
  apply (compiledFailure f).correct
  rw [(compiledFailure f).memory_input (by cases f <;> decide +kernel)]
  exact ⟨fixture_repr, by cases f <;> decide +kernel, .inl (by cases f <;> decide +kernel)⟩

theorem failure_source (f : Failure) :
    (match (failure f).run σ with | .error .revert => true | _ => false) = true := by
  cases f <;> decide +kernel

theorem failure_target (f : Failure) : run (compiledFailure f).code machine = .revert := by
  cases f <;> exact Out.eq_revert (by decide +kernel)

end IncrementCase

namespace CaptureCase

private def sequence (op : IncDec) : Prog C Γ Γ :=
  .cons (.assignIncDec .here op rfl
    (.mindex .dyn (.var first rfl) (.local .here)) rfl) .nil
private def compiled (op : IncDec) : Compiler.Compilation 0 (Frag.init Γ) (sequence op) :=
  (Compiler.compile 0 (Frag.init Γ) (sequence op)).get (by cases op <;> decide +kernel)

/-- Updating the destination index happens after the original array slot is bumped. -/
theorem simulates (op : IncDec) : (compiled op).Agrees 1 4 base σ machine := by
  apply (compiled op).correct
  rw [(compiled op).memory_input (by cases op <;> decide +kernel)]
  exact ⟨fixture_repr, by cases op <;> decide +kernel, .inl (by cases op <;> decide +kernel)⟩

private def updated (op : IncDec) : Int := if op.isIncrement then 8 else 6
private def captured (op : IncDec) : Int := if op.isPre then updated op else 7
private def sourceValues (op : IncDec) : Option (List Int) := do
  let o ← (sequence op).run σ |>.toOption
  let av ← a.evalT o.st |>.toOption
  let aliasValue ← (element C (.there .here) 0 rfl).evalT o.st |>.toOption
  let independent ← (element C other 0 rfl).evalT o.st |>.toOption
  pure [av.val, aliasValue.val, independent.val,
    (TEnv.get (.here : Idx Γ (.val .uint)) o.st.env).val, o.st.H.length]

theorem source (op : IncDec) : sourceValues op = some [updated op, updated op, 4, captured op, 2] := by
  cases op <;> decide +kernel

theorem target (op : IncDec) :
    ([3, 17, 18, 21, 16, 20, 0, 1, 2].mapM (cell (run (compiled op).code machine))) =
      some [(captured op).toNat, (updated op).toNat, 9, 4, 2, 1, 20, 16, 16] := by
  cases op <;> decide +kernel

private def selfAssign (op : IncDec) : Prog C Γ Γ :=
  .cons (.require (.binop .eqB rfl rfl a (lit 7 rfl)))
    (.cons (.assignLocal .here (lit 1 rfl))
      (.cons (.assignIncDec .here op rfl (.local .here) rfl) .nil))
private def compiledSelf (op : IncDec) : Compiler.Compilation 0 (Frag.init Γ) (selfAssign op) :=
  (Compiler.compile 0 (Frag.init Γ) (selfAssign op)).get (by cases op <;> decide +kernel)

theorem self_simulates (op : IncDec) : (compiledSelf op).Agrees 1 4 base σ machine := by
  apply (compiledSelf op).correct
  rw [(compiledSelf op).memory_input (by cases op <;> decide +kernel)]
  exact ⟨fixture_repr, by cases op <;> decide +kernel, .inl (by cases op <;> decide +kernel)⟩

private def selfValue (op : IncDec) : Nat :=
  if op.isPre then (if op.isIncrement then 2 else 0) else 1

theorem self_source (op : IncDec) :
    localResult ((selfAssign op).run σ) = some (selfValue op : Int) := by
  cases op <;> decide +kernel

theorem self_target (op : IncDec) : cell (run (compiledSelf op).code machine) 3 = some (selfValue op) := by
  cases op <;> decide +kernel

private def failure : IncrementCase.Failure → Prog C Γ Γ
  | .bounds => .cons (.assignIncDec .here .postInc rfl
      (.mindex .dyn (.var first rfl) (.lit 2 rfl)) rfl) .nil
  | .underflow => .cons (.assignMem (.index .dyn (.var first rfl) (.simple (.lit 0 rfl)))
      (.val (lit 0 rfl))) (.cons (.assignIncDec .here .postDec rfl
        (.mindex .dyn (.var first rfl) (.lit 0 rfl)) rfl) .nil)
  | .overflow => .cons (.assignMem (.index .dyn (.var first rfl) (.simple (.lit 0 rfl)))
      (.val (lit ((W - 1 : Nat) : Int) (by decide +kernel))))
      (.cons (.assignIncDec .here .preInc rfl (.mindex .dyn (.var first rfl) (.lit 0 rfl)) rfl) .nil)
  | .localUnderflow => .cons (.require (.binop .eqB rfl rfl a (lit 7 rfl)))
      (.cons (.assignIncDec .here .postDec rfl (.local .here) rfl) .nil)
  | .localOverflow => .cons (.require (.binop .eqB rfl rfl a (lit 7 rfl)))
      (.cons (.assignLocal .here (lit ((W - 1 : Nat) : Int) (by decide +kernel)))
        (.cons (.assignIncDec .here .preInc rfl (.local .here) rfl) .nil))
private def compiledFailure (f : IncrementCase.Failure) :
    Compiler.Compilation 0 (Frag.init Γ) (failure f) :=
  (Compiler.compile 0 (Frag.init Γ) (failure f)).get (by cases f <;> decide +kernel)

theorem failure_simulates (f : IncrementCase.Failure) :
    (compiledFailure f).Agrees 1 4 base σ machine := by
  apply (compiledFailure f).correct
  rw [(compiledFailure f).memory_input (by cases f <;> decide +kernel)]
  exact ⟨fixture_repr, by cases f <;> decide +kernel, .inl (by cases f <;> decide +kernel)⟩

theorem failure_source (f : IncrementCase.Failure) :
    (match (failure f).run σ with | .error .revert => true | _ => false) = true := by
  cases f <;> decide +kernel

theorem failure_target (f : IncrementCase.Failure) : run (compiledFailure f).code machine = .revert := by
  cases f <;> exact Out.eq_revert (by decide +kernel)

end CaptureCase

namespace StorageCase

def D : Contract := contract!{ uint total; }
def state : State D Γ :=
  { storage := Storage.init D, H := CompileExamples.H, heap := hp, env := σ.env }

theorem fixture : StateRepr 1 0 6 (Frag.init Γ) state base machine := by
  have h := fixture_six_cells
  constructor
  · refine ⟨initStorage_repr D Nat.one_pos, ?_, ?_, h.core.net, h.core.netSelf,
      h.core.bound, ?_, h.core.env, h.core.funds, h.core.oracle⟩
    · intro p i
      cases i with
      | here => exact ⟨⟨0, W_pos⟩, rfl, rfl⟩
      | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
  · exact h.heap
  · intro p i
    cases i with
    | there i =>
      cases i with
      | here => exact ⟨r0, rfl, rfl⟩
      | there i =>
        cases i with
        | here => exact ⟨r0, rfl, rfl⟩
        | there i =>
          cases i with
          | here => exact ⟨r1, rfl, rfl⟩
          | there i => nomatch i
  · exact h.locals
  · exact h.structs
  · exact h.separated
  · exact h.refs

private def stored : Val D Γ .uint := .read (.root "total" rfl)
def sequence : Prog D Γ Γ :=
  .cons (.assign (.root "total" rfl)
    (.val (.binop .add rfl rfl (element D first 0 rfl) (element D first 1 rfl))))
  (.cons (.require (.binop .eqB rfl rfl stored (.simple (.lit 16 rfl))))
  (.cons (.assignMem (.index .dyn (.var first rfl) (.simple (.lit 0 rfl))) (.val stored)) .nil))

def compiled : Compiler.Compilation 0 (Frag.init Γ) sequence :=
  (Compiler.compile 0 (Frag.init Γ) sequence).get (by decide +kernel)

theorem storage_memory_simulate : compiled.Agrees 1 6 base state machine :=
  compiled.correct ⟨fixture, by decide +kernel, .inl (by decide +kernel)⟩

private def sourceRead (v : Val D Γ .uint) : Option Int :=
  match sequence.run state with
  | .ok o => match v.evalT o.st with | .ok n => some n.1 | _ => none
  | .error _ => none

private def targetStore : Option Nat :=
  match run compiled.code machine with
  | .ok m _ => some (m.store (rootSlot D "total"))
  | _ => none

example : compiled.isMemory = true := by decide +kernel
example : sourceRead stored = some 16 := by decide +kernel
example : sourceRead (element D first 0 rfl) = some 16 := by decide +kernel
example : targetStore = some 16 := by decide +kernel
example : cell (run compiled.code machine) 17 = some 16 := by decide +kernel
example : cell (run compiled.code machine) 18 = some 9 := by decide +kernel
example : cell (run compiled.code machine) 21 = some 4 := by decide +kernel
example : cell (run compiled.code machine) 1 = some 16 := by decide +kernel

end StorageCase

end Solidity.Evm.Memory.ExprExamples
