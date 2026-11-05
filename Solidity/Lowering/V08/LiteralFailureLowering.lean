import Solidity.Lowering.V08.SourceFailures
import Solidity.Backend.Failure.Correct

/-! G21: closed typed source failure expressions and the published terminal
instruction emitter. This is constant failure lowering, not an encoder that
reads unknown runtime memory, a source-world simulation or catch semantics. -/
namespace Solidity.Lowering.V08.LiteralFailureLowering
open Solidity Solidity.Source Solidity.Backend

/-- All actual source panic codes fit the unchanged intrinsic word. -/
def panicInput (c : PanicCode) : Failure.Input :=
  .panic ⟨c.code, by cases c <;> decide⟩

theorem panic_bytes (c : PanicCode) : (panicInput c).bytes = panicData c := by
  cases c <;> decide +kernel

def assertFalse {E : Env} {Γ : RCtx} : RExpr E Γ (.tuple []) :=
  .builtin .assert (.cons (.bool false) .nil) (by rfl)

def revertBare {E : Env} {Γ : RCtx} : RExpr E Γ (.tuple []) :=
  .builtin .revert .nil (by rfl)

def revertReason {E : Env} {Γ : RCtx} (bs : List UInt8) : RExpr E Γ (.tuple []) :=
  SourceFailures.reason bs

def requireFalse {E : Env} {Γ : RCtx} (bs : List UInt8) : RExpr E Γ (.tuple []) :=
  .builtin .require (.cons (.bool false) (.cons (.str bs) .nil)) (by rfl)

/-- Syntactic literal views over the existing indexed AST, not evaluators. -/
def boolLiteral {E : Env} {Γ : RCtx} {τ : STy} : RExpr E Γ τ → Option Bool
  | .bool b => some b
  | _ => none

def stringLiteral {E : Env} {Γ : RCtx} {τ : STy} : RExpr E Γ τ → Option (List UInt8)
  | .str bs => some bs
  | _ => none

def onlyString {E : Env} {Γ : RCtx} {ts : List STy} : RArgs E Γ ts → Option (List UInt8)
  | .cons e .nil => stringLiteral e
  | _ => none

def argsEmpty {E : Env} {Γ : RCtx} {ts : List STy} : RArgs E Γ ts → Bool
  | .nil => true
  | .cons _ _ => false

/-- Selection on existing typed arguments; there is no argument evaluator here. -/
def builtinInput {E : Env} {Γ : RCtx} {ts : List STy} (b : Builtin) (args : RArgs E Γ ts) : Option Failure.Input :=
  match b with
  | .assert => match args with
    | .nil => none
    | .cons e rest => if argsEmpty rest = true ∧ boolLiteral e = some false then some (panicInput .assert) else none
  | .revert => if argsEmpty args then some .empty else (onlyString args).map (fun bs => .custom (errorData bs))
  | .require => match args with
    | .nil => none
    | .cons e rest =>
      if boolLiteral e = some false then
        if argsEmpty rest then some .empty else (onlyString rest).map (fun bs => .custom (errorData bs))
      else none
  | _ => none

/-- Executable partial adapter over the EXISTING indexed AST. Other forms
remain unhandled by this helper; source admission is unchanged. -/
def literalInput {E : Env} {Γ : RCtx} {τ : STy} : RExpr E Γ τ → Option Failure.Input
  | .builtin b args _ => builtinInput b args
  | _ => none

def emitLiteral {E : Env} {Γ : RCtx} {τ : STy} (a : Nat) (e : RExpr E Γ τ) : Option Solidity.Backend.Program :=
  (literalInput e).map (Failure.emit a)

/-- The same original horizon variable is retained; no default is changed.
The equations preserve the entire actual source locals/state pair. -/
theorem assert_source {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (l : Locals E.layout Γ) (s : St E) :
    (evalE G F (n+6) assertFalse).run (l,s) =
      (.error (.revert (panicData .assert)),(l,s)) := by rfl

theorem bare_source {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (l : Locals E.layout Γ) (s : St E) :
    (evalE G F (n+6) revertBare).run (l,s) = (.error (.revert []),(l,s)) := by rfl

theorem reason_source {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (l : Locals E.layout Γ) (s : St E) (bs : List UInt8) :
    (evalE G F (n+6) (revertReason bs)).run (l,s) =
      (.error (.revert (errorData bs)),(l,s)) :=
  SourceFailures.eval_reason G F (n+1) bs l s

theorem require_source {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (l : Locals E.layout Γ) (s : St E) (bs : List UInt8) :
    (evalE G F (n+6) (requireFalse bs)).run (l,s) =
      (.error (.revert (errorData bs)),(l,s)) := by rfl

/-- Literal views retain the actual dependent source type and constructor. -/
theorem boolLiteral_inv {E : Env} {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) (b : Bool)
    (h : boolLiteral e = some b) : ∃ ht : τ = .bool, ht ▸ e = (.bool b : RExpr E Γ .bool) := by
  cases e <;> simp only [boolLiteral] at h
  all_goals cases h
  exact ⟨rfl,rfl⟩

theorem stringLiteral_inv {E : Env} {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) (bs : List UInt8)
    (h : stringLiteral e = some bs) : ∃ ht : τ = .stringLit bs, ht ▸ e = (.str bs : RExpr E Γ (.stringLit bs)) := by
  cases e <;> simp only [stringLiteral] at h
  all_goals cases h
  exact ⟨rfl,rfl⟩

def requireBare {E : Env} {Γ : RCtx} : RExpr E Γ (.tuple []) :=
  .builtin .require (.cons (.bool false) .nil) (by rfl)

theorem require_bare_source {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (l : Locals E.layout Γ) (s : St E) :
    (evalE G F (n+6) requireBare).run (l,s) = (.error (.revert []),(l,s)) := by rfl

theorem reason_length (bs : List UInt8) :
    (errorData bs).length = 68 + bs.length + (32-bs.length%32)%32 := by
  simp only [errorData,pad32,List.length_append,wordBytes_length,errorSelector,
    List.length_cons,List.length_nil,List.length_replicate]
  omega

/-- Consume the existing total Source/intrinsic Error encoder agreement. -/
theorem reason_packet_transport (bs : List UInt8) :
    (Failure.Input.custom (errorData bs)).bytes = Semantics.encodeError bs :=
  errorData_transport_total bs

theorem reason_bound (a : Nat) (bs : List UInt8) (fits : Failure.Fits a (errorData bs)) :
    bs.length < Failure.wordLimit := by
  have hn := fits.2.1
  rw [reason_length] at hn
  omega

theorem panic_observation (c : PanicCode) :
    (panicInput c).observation = revertOutcome (panicData c) := by
  change Solidity.Roadmap.Outcome.revert (panicInput c).bytes = .revert (panicData c)
  rw [panic_bytes]

/-- Every original source panic code, exact stack and memory frame. This
consumes the published instruction execution, not a target outcome oracle. -/
theorem panic_checked (c : PanicCode) (a : Nat) (tail : Solidity.Backend.Program) (m : Failure.Slice.Machine)
    (fits : Failure.Fits a (panicData c)) (stack : m.stack.length+2 ≤ 1024) :
    Failure.Slice.checkedRun (Failure.emit a (panicInput c) ++ tail) m =
      some ({m with memory := Failure.Slice.putBytes m.memory a (panicData c)},
        some (revertOutcome (panicData c))) := by
  have h := Failure.checkedRun_emit_suffix a (panicInput c) tail m
    (by simpa only [panic_bytes] using fits) stack
  simpa only [panic_bytes,panic_observation] using h

theorem raw_checked (a : Nat) (bs : List UInt8) (tail : Solidity.Backend.Program) (m : Failure.Slice.Machine)
    (fits : Failure.Fits a bs) (stack : m.stack.length+2 ≤ 1024) :
    Failure.Slice.checkedRun (Failure.emit a (.custom bs) ++ tail) m =
      some ({m with memory := Failure.Slice.putBytes m.memory a bs}, some (revertOutcome bs)) := by
  exact Failure.checkedRun_emit_suffix a (.custom bs) tail m fits stack

/-- Concrete typed source evaluation AND an actual compiled instruction
result. Source state and target byte memory remain distinct machines. -/
theorem assert_lowered {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (l : Locals E.layout Γ) (s : St E) (a : Nat) (m : Failure.Slice.Machine)
    (fits : Failure.Fits a (panicData .assert)) (stack : m.stack.length+2 ≤ 1024) :
    ∃ p, emitLiteral a (assertFalse (E:=E) (Γ:=Γ)) = some p ∧
      (evalE G F (n+6) assertFalse).run (l,s) = (.error (.revert (panicData .assert)),(l,s)) ∧
      Failure.Slice.checkedRun p m = some ({m with memory := Failure.Slice.putBytes m.memory a (panicData .assert)},
        some (revertOutcome (panicData .assert))) := by
  refine ⟨Failure.emit a (panicInput .assert),rfl,assert_source G F n l s,?_⟩
  simpa only [List.append_nil] using panic_checked .assert a [] m fits stack

theorem reason_lowered {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (l : Locals E.layout Γ) (s : St E) (bs : List UInt8) (a : Nat) (m : Failure.Slice.Machine)
    (fits : Failure.Fits a (errorData bs)) (stack : m.stack.length+2 ≤ 1024) :
    ∃ p, emitLiteral a (revertReason (E:=E) (Γ:=Γ) bs) = some p ∧
      (evalE G F (n+6) (revertReason bs)).run (l,s) = (.error (.revert (errorData bs)),(l,s)) ∧
      Failure.Slice.checkedRun p m = some ({m with memory := Failure.Slice.putBytes m.memory a (errorData bs)},
        some (revertOutcome (errorData bs))) := by
  refine ⟨Failure.emit a (.custom (errorData bs)),rfl,reason_source G F n l s bs,?_⟩
  simpa only [List.append_nil] using raw_checked a (errorData bs) [] m fits stack

theorem require_lowered {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
    (l : Locals E.layout Γ) (s : St E) (bs : List UInt8) (a : Nat) (m : Failure.Slice.Machine)
    (fits : Failure.Fits a (errorData bs)) (stack : m.stack.length+2 ≤ 1024) :
    ∃ p, emitLiteral a (requireFalse (E:=E) (Γ:=Γ) bs) = some p ∧
      (evalE G F (n+6) (requireFalse bs)).run (l,s) = (.error (.revert (errorData bs)),(l,s)) ∧
      Failure.Slice.checkedRun p m = some ({m with memory := Failure.Slice.putBytes m.memory a (errorData bs)},
        some (revertOutcome (errorData bs))) := by
  refine ⟨Failure.emit a (.custom (errorData bs)),rfl,require_source G F n l s bs,?_⟩
  simpa only [List.append_nil] using raw_checked a (errorData bs) [] m fits stack

theorem onlyString_inv {E : Env} {Γ : RCtx} {ts : List STy} (args : RArgs E Γ ts) (bs : List UInt8)
    (h : onlyString args = some bs) :
    ∃ ht : ts = [.stringLit bs], ht ▸ args = (.cons (.str bs) .nil : RArgs E Γ [.stringLit bs]) := by
  cases args with
  | nil => cases h
  | cons e rest =>
    cases rest with
    | cons x xs => cases h
    | nil =>
      obtain ⟨ht,he⟩ := stringLiteral_inv e bs h
      cases ht
      cases he
      exact ⟨rfl,rfl⟩

theorem argsEmpty_inv {E : Env} {Γ : RCtx} {ts : List STy} (args : RArgs E Γ ts)
    (h : argsEmpty args = true) : ∃ ht : ts = [], ht ▸ args = (.nil : RArgs E Γ []) := by
  cases args with
  | nil => exact ⟨rfl,rfl⟩
  | cons e rest => cases h

/-- Correctness of the executable recognition decision, not an assumed
source execution or future simulation premise. -/
theorem builtinInput_sound {E : Env} {Γ : RCtx} {ts : List STy} (G : Glob E) (F : Fr) (n : Nat)
    (l : Locals E.layout Γ) (s : St E) (b : Builtin) (args : RArgs E Γ ts) (τ : STy) (i : Failure.Input)
    (compiled : builtinInput b args = some i) :
    (evalBuiltin G F (n+5) b args τ).run (l,s) = (.error (.revert i.bytes),(l,s)) ∧
      i.observation = revertOutcome i.bytes := by
  cases b
  all_goals try exact Option.noConfusion compiled
  case assert =>
    revert compiled
    cases args with
    | nil => intro compiled; exact Option.noConfusion compiled
    | cons e rest =>
      intro compiled
      change (if argsEmpty rest = true ∧ boolLiteral e = some false then some (panicInput .assert) else none) = some i at compiled
      by_cases guard : argsEmpty rest = true ∧ boolLiteral e = some false
      · rw [if_pos guard] at compiled
        obtain ⟨ht,hr⟩ := argsEmpty_inv rest guard.1
        cases ht
        cases hr
        obtain ⟨ht,he⟩ := boolLiteral_inv e false guard.2
        cases ht
        cases he
        have hi := Option.some.inj compiled
        subst i
        constructor
        · rw [panic_bytes] <;> rfl
        · rfl
      · rw [if_neg guard] at compiled
        cases compiled

  case revert =>
    change (if argsEmpty args then some .empty else (onlyString args).map (fun bs => Failure.Input.custom (errorData bs))) = some i at compiled
    split at compiled
    · rename_i empty
      obtain ⟨ht,ha⟩ := argsEmpty_inv args empty
      cases ht
      cases ha
      have hi := Option.some.inj compiled
      subst i
      exact ⟨rfl,rfl⟩
    · cases hs : onlyString args with
      | none => simp only [hs,Option.map_none] at compiled; cases compiled
      | some bs =>
        simp only [hs,Option.map_some] at compiled
        obtain ⟨ht,ha⟩ := onlyString_inv args bs hs
        cases ht
        cases ha
        have hi := Option.some.inj compiled
        subst i
        exact ⟨rfl,rfl⟩
  case require =>
    revert compiled
    cases args with
    | nil => intro compiled; exact Option.noConfusion compiled
    | cons e rest =>
      intro compiled
      change (if boolLiteral e = some false then
        (if argsEmpty rest then some .empty else (onlyString rest).map (fun bs => Failure.Input.custom (errorData bs))) else none) = some i at compiled
      by_cases guard : boolLiteral e = some false
      · rw [if_pos guard] at compiled
        obtain ⟨ht,he⟩ := boolLiteral_inv e false guard
        cases ht
        cases he
        split at compiled
        · rename_i empty
          obtain ⟨ht,hr⟩ := argsEmpty_inv rest empty
          cases ht
          cases hr
          have hi := Option.some.inj compiled
          subst i
          exact ⟨rfl,rfl⟩
        · cases hs : onlyString rest with
          | none => simp only [hs,Option.map_none] at compiled; cases compiled
          | some bs =>
            simp only [hs,Option.map_some] at compiled
            obtain ⟨ht,hr⟩ := onlyString_inv rest bs hs
            cases ht
            cases hr
            have hi := Option.some.inj compiled
            subst i
            exact ⟨rfl,rfl⟩
      · rw [if_neg guard] at compiled
        cases compiled

theorem builtinInput_source {E : Env} {Γ : RCtx} {ts : List STy} (G : Glob E) (F : Fr) (n : Nat)
    (l : Locals E.layout Γ) (s : St E) (b : Builtin) (args : RArgs E Γ ts) (τ : STy) (i : Failure.Input)
    (compiled : builtinInput b args = some i) :
    (evalBuiltin G F (n+5) b args τ).run (l,s) = (.error (.revert i.bytes),(l,s)) :=
  (builtinInput_sound G F n l s b args τ i compiled).1

theorem literalInput_sound {E : Env} {Γ : RCtx} {τ : STy} (G : Glob E) (F : Fr) (n : Nat)
    (l : Locals E.layout Γ) (s : St E) (e : RExpr E Γ τ) (i : Failure.Input)
    (compiled : literalInput e = some i) :
    (evalE G F (n+6) e).run (l,s) = (.error (.revert i.bytes),(l,s)) ∧
      i.observation = revertOutcome i.bytes := by
  cases e <;> simp only [literalInput] at compiled
  all_goals first
    | exact Option.noConfusion compiled
    | exact builtinInput_sound G F n l s _ _ _ i compiled

/-- Every successful actual compiler decision has matching source and
checked target executions. Fits/stack are the existing architectural gates. -/
theorem literal_lowered {E : Env} {Γ : RCtx} {τ : STy} (G : Glob E) (F : Fr) (n : Nat)
    (l : Locals E.layout Γ) (s : St E) (e : RExpr E Γ τ) (i : Failure.Input)
    (compiled : literalInput e = some i) (a : Nat) (tail : Solidity.Backend.Program) (m : Failure.Slice.Machine)
    (fits : Failure.Fits a i.bytes) (stack : m.stack.length+2 ≤ 1024) :
    ∃ p, emitLiteral a e = some p ∧
      (evalE G F (n+6) e).run (l,s) = (.error (.revert i.bytes),(l,s)) ∧
      Failure.Slice.checkedRun (p ++ tail) m =
        some ({m with memory := Failure.Slice.putBytes m.memory a i.bytes}, some (revertOutcome i.bytes)) := by
  obtain ⟨source,observation⟩ := literalInput_sound G F n l s e i compiled
  refine ⟨Failure.emit a i,?_,source,?_⟩
  · simp only [emitLiteral,compiled,Option.map_some]
  · simpa only [observation] using Failure.checkedRun_emit_suffix a i tail m fits stack

/-- Source panic primitive, with the complete actual caller state retained.
This does not claim the origin of each code or transaction/world rollback. -/
theorem panic_source {E : Env} {Γ : RCtx} (c : PanicCode) (l : Locals E.layout Γ) (s : St E) :
    (EM.lift (panic c) : EM E Γ Unit).run (l,s) = (.error (.revert (panicData c)),(l,s)) := by rfl

end Solidity.Lowering.V08.LiteralFailureLowering
