import Solidity.Source.Semantics
import Solidity.Source.Examples
import Solidity.Source.Ledger

/-!
# Controls of the source semantics (S02, S03, S04.04, S05)

Kernel-checked runs of resolved programs (`decide` evaluates the
interpreter of `Solidity/Source/Eval.lean`), each with the wrong result it
excludes.  The hash is a toy checksum (`toyFixed`): the semantics takes the
hash as a fixed parameter, so these runs read selectors without computing
Keccak-256 in the kernel.

| Control | What it shows |
|---|---|
| `add_overflow_checked`, `add_overflow_unchecked` | `x + 1` at `uint8 255`: `Panic(0x11)` checked, `0` unchecked |
| `div_by_zero` | `x / 0`: `Panic(0x12)` |
| `order_legacy`, `order_viaIR` | `++a + a` at `a = 1`: `3` under legacy (right operand first), `4` via IR |
| `short_circuit` | `false && (++a > 0)` leaves `a` |
| `modifier_twice_legacy`, `modifier_twice_viaIR`, `modifier_once` | upstream `function_modifier_multi_invocation(_viair).sol`: `f(true)` is `2` legacy and `1` via IR, `f(false)` is `1` |
| `revert_rolls_back` | a transaction writing storage and transient storage, then reverting: both unchanged, the revert data the caller's |
| `commit_keeps_storage`, `transient_cleared` | without the revert the storage write stays and transient storage is cleared at the end of the transaction |
| `reentrant_callback` | a call out whose callee calls back into the contract before answering: the callback's write is seen, and the events are the call, the callback, its outcome, the answer and the transaction |
| `session_consistent` | the session family of a deployment is consistent (G01) |
-/

namespace Solidity.Source.SemanticsExamples

open Solidity.Source Solidity.Source.Examples
open Solidity.Roadmap (Address Word Bytes Event Outcome Move Request SessionEnv Pipeline)

/-! ## Fixed parameters and an empty program -/

/-- A toy hash: a positional checksum in the high four bytes. -/
def toyKeccak (bs : Bytes) : Nat := ((bs.foldl (fun a b => a * 257 + b.toNat) 0 % 2 ^ 32) * 2 ^ 224) % 2 ^ 256

def toyFixed : Solidity.Roadmap.Fixed where
  evm := { keccak := toyKeccak, keccak_lt := fun _ => Nat.mod_lt _ (by decide),
           precompile := fun _ _ => none, precompileGas := fun _ _ => 0 }
  ledger := fun bal _ a => bal a
  regionLen := 1
  rootSlots := 1

def addr (n : Nat) (h : n < 2 ^ 160 := by decide) : Address := ⟨n, h⟩
def word (n : Nat) (h : n < 2 ^ 256 := by decide) : Word := ⟨n, h⟩

def u8 : STy := .int IntTy.u8
def uint : STy := .int IntTy.u256

/-- The state before any instance exists. -/
def s0 {E : Env} : St E := St.init E

/-! ## S02: expressions -/

def E0 : Env := ⟨[]⟩

def P0 : Program E0 where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := []

def G0 (p : Pipeline) : Glob E0 :=
  ⟨P0, p, toyFixed, fun _ => word 0, fun _ _ => false, fun _ => .answer (.success []), word 0⟩

def F0 : Fr := { this := addr 1, sender := addr 2, value := word 0, static := false, contract := "C" }

/-- The revert data an evaluation ends with. -/
def revertOf {E : Env} {Γ : RCtx} {α : Type} (r : Except Halt α × (Locals E.layout Γ × St E)) : Option Bytes :=
  match r.1 with
  | .error (.revert d) => some d
  | _ => none

/-- The integer an evaluation returns. -/
def intOf {E : Env} {Γ : RCtx} {τ : STy} (r : Except Halt (RVal E.layout τ) × (Locals E.layout Γ × St E)) :
    Option Int :=
  match r.1 with
  | .ok (.val (.int v _)) => some v
  | _ => none

/-- `x + 1` at `uint8`. -/
def incX : RExpr E0 [u8] u8 := .binary .add (.local .here) (.conv (.const (Q.ofInt 1)) (.inl (by decide)))

def l255 : Locals E0.layout [u8] := .cons (.int 255 (by decide)) .nil

theorem add_overflow_checked :
    revertOf ((evalE (G0 .legacy) F0 10 incX).run (l255, s0)) = some (panicData .arithmetic) := by decide

theorem add_overflow_unchecked :
    intOf ((evalE (G0 .legacy) { F0 with checked := false } 10 incX).run (l255, s0)) = some 0 := by decide

/-- `x / 0`. -/
def divZero : RExpr E0 [u8] u8 := .binary .div (.local .here) (.conv (.const (Q.ofInt 0)) (.inl (by decide)))

theorem div_by_zero : revertOf ((evalE (G0 .viaIR) { F0 with checked := false } 10 divZero).run (l255, s0)) =
    some (panicData .divZero) := by decide

/-- `++a + a` at `uint256`. -/
def preIncPlus : RExpr E0 [uint] uint := .binary .add (.incDec true true (.local .here)) (.local .here)

def l1 : Locals E0.layout [uint] := .cons (.int 1 (by decide)) .nil

theorem order_legacy : intOf ((evalE (G0 .legacy) F0 10 preIncPlus).run (l1, s0)) = some 3 := by decide
theorem order_viaIR : intOf ((evalE (G0 .viaIR) F0 10 preIncPlus).run (l1, s0)) = some 4 := by decide

/-- Neither schedule gives the other's result. -/
theorem order_differs : intOf ((evalE (G0 .legacy) F0 10 preIncPlus).run (l1, s0)) ≠ some 4 := by decide

/-- `false && (++a > 0)`, then `a`. -/
def shortCircuit : RExpr E0 [uint] uint :=
  .binary .add (.cond (.binary .and (.bool false)
      (.compare .gt (.incDec true true (.local .here)) (.conv (.const (Q.ofInt 0)) (.inl (by decide)))))
    (.conv (.const (Q.ofInt 100)) (.inl (by decide))) (.conv (.const (Q.ofInt 0)) (.inl (by decide))))
    (.local .here)

theorem short_circuit : intOf ((evalE (G0 .viaIR) F0 20 shortCircuit).run (l1, s0)) = some 1 := by decide

/-! ## S03: a modifier with two placeholders -/

/-- `modifier repeat(bool twice) { if (twice) _; _; }` -/
def repeatDecl : Decl :=
  ⟨.modifier, "repeat", some "C", false, .modifier "repeat" (.some (.cons (.param (.elem .bool) none (some "twice")) .nil))
    false none .none⟩

/-- `function f(bool twice) public repeat(twice) returns (uint256 r) { r += 1; }` -/
def fDecl : Decl :=
  ⟨.function, "f", some "C", false, .function (.ident "f") (.cons (.param (.elem .bool) none (some "twice")) .nil)
    (some .pub) none .nil false none (.cons (.param u256 none (some "r")) .nil) .none⟩

def modBody : RBody E0 where
  ps := [.bool]
  rs := []
  inModifier := true
  locals := [.bool]
  out := [.bool]
  items := .stmt (.ifThen (.local .here) (.placeholder rfl)) (.stmt (.placeholder rfl) .nil)

def fBody : RBody E0 where
  ps := [.bool]
  rs := [uint]
  inModifier := false
  locals := [uint, .bool]
  out := [uint, .bool]
  items := .stmt (.expr (.compound .add (.local .here) (.const (Q.ofInt 1)) (by decide))) .nil
  mods := [⟨repeatDecl, [.bool], .cons (.local (.there .here)) rfl .nil⟩]

def P1 : Program E0 := { P0 with body := fun d => if d.name = "f" then some fBody else if d.name = "repeat" then some modBody else none }

def G1 (p : Pipeline) : Glob E0 := { G0 p with prog := P1 }

def callF (p : Pipeline) (twice : Bool) :=
  (callInternal (G1 p) F0 30 fDecl (Vals.cons (D := E0.layout) (.bool twice) .nil) [uint]).run (.nil, s0)

theorem modifier_twice_legacy : intOf (callF .legacy true) = some 2 := by decide
theorem modifier_twice_viaIR : intOf (callF .viaIR true) = some 1 := by decide
theorem modifier_once : intOf (callF .legacy false) = some 1 ∧ intOf (callF .viaIR false) = some 1 := by decide

/-! ## S04.04 and S05: transactions, rollback, transient storage, callbacks -/

/-- ```
contract C {
  uint256 x; uint256 transient t;
  function poke() public { x = 1; t = 2; revert(); }
  function g() public returns (uint256) { x = 5; t = 7; return x + t; }
  function cb() public { x = x + 1; }
  function callOut(address a) public { I(a).ping(); }
}
interface I { function ping() external; }
``` -/
def stX : Syn (.part false) := .stateVar u256 none none none false "x" .none
def stT : Syn (.part false) := .stateVar u256 none none none true "t" .none
def fn (name : String) (ps rs : Syn (.list .param)) (vis : Visibility := .pub) : Syn (.part false) :=
  .function (.ident name) ps (some vis) none .nil false none rs (.some (.block .nil))
def pAddr : Syn (.list .param) := .cons (.param (.elem .address) none (some "a")) .nil
def pUint : Syn (.list .param) := .cons (.param u256 none none) .nil

def unitB : Syn .unit :=
  .unit (.cons (.contract false "C" .none .nil
      (.cons stX (.cons stT (.cons (fn "poke" .nil .nil) (.cons (fn "g" .nil pUint)
        (.cons (fn "cb" .nil .nil) (.cons (fn "callOut" pAddr .nil) .nil)))))))
    (.cons (.interface "I" .nil (.cons (.function (.ident "ping") .nil (some .external) none .nil false none .nil .none) .nil))
      .nil))

def EB : Env := unitB.env

def dX : Decl := ⟨.stateVar, "x", some "C", false, stX⟩
def dT : Decl := ⟨.stateVar, "t", some "C", false, stT⟩
def dPing : Decl := ⟨.function, "ping", some "I", false,
  .function (.ident "ping") .nil (some .external) none .nil false none .nil .none⟩

theorem dX_ty : dX.varTy EB = some uint := by decide
theorem dT_ty : dT.varTy EB = some uint := by decide
theorem dPing_sig : dPing.fnSig EB = some ([], []) := by decide

theorem lit_ok (B : DeclName → DeclName → Bool) (k : Nat) (h : (Q.ofInt k).FitsInt IntTy.u256) :
    STy.implicit B (.rational (Q.ofInt k)) uint = true := by
  simp only [uint, STy.implicit, decide_eq_true_eq]
  exact h

def lit {Γ : RCtx} (k : Nat) (h : (Q.ofInt k).FitsInt IntTy.u256 := by decide) : RExpr EB Γ uint :=
  .conv (.const (Q.ofInt k)) (.inl (lit_ok _ k h))

def setX {R : List STy} {Γ : RCtx} (e : RExpr EB Γ uint) : RStmt EB R false .body Γ Γ :=
  .expr (.assign (.state dX dX_ty rfl) e)
def setT {R : List STy} {Γ : RCtx} (e : RExpr EB Γ uint) : RStmt EB R false .body Γ Γ :=
  .expr (.assign (.state dT dT_ty rfl) e)

def body0 (R : List STy) (items : RItems EB R false .body [] []) : RBody EB :=
  ⟨[], R, false, [], [], items, []⟩

/-- `x = 1; t = 2; revert();` -/
def pokeBody : RBody EB := body0 [] (.stmt (setX (lit 1)) (.stmt (setT (lit 2))
  (.stmt (.expr (.builtin .revert .nil rfl)) .nil)))

/-- `x = 5; t = 7; return x + t;` -/
def gBody : RBody EB := ⟨[], [uint], false, [uint], [uint],
  .stmt (setX (lit 5)) (.stmt (setT (lit 7))
    (.stmt (.retVal rfl (.binary .add (.state dX dX_ty) (.state dT dT_ty)) rfl) .nil)), []⟩

/-- `x = x + 1;` -/
def cbBody : RBody EB := body0 [] (.stmt (setX (.binary .add (.state dX dX_ty) (lit 1))) .nil)

/-- `I(a).ping();` -/
def callOutBody : RBody EB := ⟨[.address false], [], false, [.address false], [.address false],
  .stmt (.expr (.extCall (.convExplicit (τ := .contract ⟨none, "I"⟩) (.local .here) (by decide)) dPing dPing_sig (lit 0) .nil)) .nil, []⟩

def PB : Program EB where
  body d := match d.name with
    | "poke" => some pokeBody
    | "g" => some gBody
    | "cb" => some cbBody
    | "callOut" => some callOutBody
    | _ => none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := ["C"]

/-- The instance of `C` at address 1. -/
def thisC : Address := addr 1
def user : Address := addr 7
def ext : Address := addr 9

/-- A state with `C` deployed at `thisC`, `x = 3`, and transient `t = 4`. -/
def x3 : Val EB.layout (EB.cellTy dX.path) := (show Val EB.layout uint from .int 3 (by decide))
def t4 : Val EB.layout (EB.cellTy dT.path) := (show Val EB.layout uint from .int 4 (by decide))

def acctC : Account EB.layout (EB.lay thisC) :=
  { balance := word 0, nonce := 1, code := some 0, storage := Storage.empty.write dX.path x3 }

def sB : St EB :=
  { (s0 : St EB) with ex := ⟨(s0 : St EB).ex.world.set thisC acctC,
      (s0 : St EB).ex.transient.set thisC (Storage.empty.write dT.path t4), []⟩ }

def GB (callee : Solidity.Roadmap.Strategy) : Glob EB :=
  ⟨PB, .legacy, toyFixed, fun _ => word 0, fun _ _ => true, callee, word 0⟩

def selOf (sig : String) : Bytes := (wordBytes (toyFixed.hash (asciiBytes sig.toList))).take 4

def tx (input : Bytes) : Request := ⟨user, thisC, word 0, word 0, input⟩

/-- Run a transaction from a state. -/
def runTxB (callee : Solidity.Roadmap.Strategy) (s : St EB) (input : Bytes) (fuel : Nat := 20) :=
  runAt (fun n => runTx (GB callee) n (tx input)) s fuel

/-- The value of `x` and `t` at `thisC`. -/
def readX (s : St EB) : Option Int :=
  match (s.ex.world.accounts thisC).storage.read dX.path with
  | some (.int v _) => some v
  | _ => none
def readT (s : St EB) : Option Int :=
  match (s.ex.transient.cells thisC).read dT.path with
  | some (.int v _) => some v
  | _ => none

def outcomeOf (r : Except Halt Outcome × St EB) : Option Outcome :=
  match r.1 with
  | .ok o => some o
  | _ => none

def answerOnly : Solidity.Roadmap.Strategy := fun _ => .answer (.success [])

/-- **A revert rolls back storage and transient storage**: `poke` writes
`x` and `t`, then reverts; both keep their values (the transient one until
the transaction ends). -/
theorem revert_rolls_back :
    let r := runTxB answerOnly sB (selOf "poke()")
    outcomeOf r = some (.revert []) ∧ readX r.2 = some 3 ∧ readX r.2 ≠ some 1 := by decide +kernel

/-- The transient value before the end of a reverted call is the old one. -/
theorem revert_rolls_back_transient :
    let r := runAt (fun n => do
      let m ← mark
      let o ← enterInstance (GB answerOnly) n thisC user (word 0) (selOf "poke()") false "C" 1 m
      pure o) sB 20
    readT r.2 = some 4 ∧ readT r.2 ≠ some 2 := by decide +kernel

/-- **Without the revert the write stays**; transient storage is cleared
when the transaction ends; `g` returns `5 + 7`. -/
theorem commit_keeps_storage :
    let r := runTxB answerOnly sB (selOf "g()")
    outcomeOf r = some (.success (wordBytes (toWord 12))) ∧ readX r.2 = some 5 := by decide +kernel

theorem transient_cleared : readT (runTxB answerOnly sB (selOf "g()")).2 = some 0 := by decide +kernel

/-- The environment calls back into `cb()` once, then answers. -/
def reenterOnce : Solidity.Roadmap.Strategy := fun evs =>
  if evs.any (fun e => match e with | .reentered _ => true | _ => false) then .answer (.success [])
  else .reenter thisC ext (word 0) (selOf "cb()") false

/-- **A reentrant callback**: `callOut(ext)` calls `ext.ping()`; the
environment calls `cb()` back before answering; the callback's increment
is in storage when the transaction ends, and the events are the call, the
callback, its outcome, the answer and the transaction. -/
theorem reentrant_callback :
    let input := selOf "callOut(address)" ++ wordBytes (toWord ext.val)
    let r := runTxB reenterOnce sB input 30
    readX r.2 = some 4 ∧ outcomeOf r = some (.success []) ∧
    r.2.events = [.call ext (word 0) (selOf "ping()") false,
      .reenter thisC ext (word 0) (selOf "cb()") false,
      .reentered (.success []),
      .answer (.success []) none,
      .tx user thisC (word 0) (word 0) input (.success [])] := by decide +kernel

/-- Without the callback the increment does not happen. -/
theorem no_callback :
    readX (runTxB answerOnly sB (selOf "callOut(address)" ++ wordBytes (toWord ext.val))).2 = some 3 := by decide +kernel


/-! ## S03.02: constructor order -/

/-- ```
contract A { uint256 a = 1; constructor() { a = a + 1; } }
contract B is A { uint256 b = a; }
``` -/
def stA : Syn (.part false) := .stateVar u256 none none none false "a" .none
def stB : Syn (.part false) := .stateVar u256 none none none false "b" .none
def unitAB : Syn .unit :=
  .unit (.cons (.contract false "A" .none .nil (.cons stA (.cons (.constructor .nil .nil false none (.block .nil)) .nil)))
    (.cons (.contract false "B" .none (.cons (.inherit ⟨"A", []⟩ .none) .nil) (.cons stB .nil)) .nil))

def EAB : Env := unitAB.env
def dA : Decl := ⟨.stateVar, "a", some "A", false, stA⟩
def dB : Decl := ⟨.stateVar, "b", some "B", false, stB⟩
theorem dA_ty : dA.varTy EAB = some uint := by decide
theorem dB_ty : dB.varTy EAB = some uint := by decide

def litAB {Γ : RCtx} (k : Nat) (h : (Q.ofInt k).FitsInt IntTy.u256 := by decide) : RExpr EAB Γ uint :=
  .conv (.const (Q.ofInt k)) (.inl (lit_ok _ k h))

def ctorA : RBody EAB := ⟨[], [], false, [], [],
  .stmt (.expr (.assign (.state dA dA_ty rfl) (.binary .add (.state dA dA_ty) (litAB 1)))) .nil, []⟩

def PAB : Program EAB where
  body _ := none
  consts _ := none
  inits c := if c = "A" then [⟨dA, uint, dA_ty, litAB 1⟩] else if c = "B" then [⟨dB, uint, dB_ty, .state dA dA_ty⟩] else []
  ctor c := if c = "A" then some ctorA else none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := ["A", "B"]

def GAB (p : Pipeline) : Glob EAB := ⟨PAB, p, toyFixed, fun _ => word 0, fun _ _ => true, answerOnly, word 0⟩

/-- `b` after deploying `B` at `thisC`. -/
def deployB (p : Pipeline) : Option Int :=
  let r := runAt (fun n => deploy (GAB p) n "B" thisC user (word 0) []) (St.init EAB) 20
  match (r.2.ex.world.accounts thisC).storage.read dB.path with
  | some (.int v _) => some v
  | _ => none

/-- **Constructor order**: under legacy every initializer runs before the
constructor bodies, so `b` reads `a = 1`; via IR `A`'s body runs before
`B`'s initializers, so `b` reads `a = 2` (solc's `ir-breaking-changes`,
"order of state variable initialization"). -/
theorem ctor_order_legacy : deployB .legacy = some 1 := by decide +kernel
theorem ctor_order_viaIR : deployB .viaIR = some 2 := by decide +kernel

/-! ## Horizons and sessions -/

/-- **The outcome does not depend on the horizon once complete** (checked
here on a transaction: `g()` at horizons 20 and 40). -/
theorem horizon_stable : outcomeOf (runTxB answerOnly sB (selOf "g()") 20) =
    outcomeOf (runTxB answerOnly sB (selOf "g()") 40) := by decide +kernel

/-- A horizon too small for the transaction completes nothing. -/
theorem horizon_short : outcomeOf (runTxB answerOnly sB (selOf "g()") 3) = none := by decide +kernel

/-- The session family of every program is consistent (G01). -/
theorem session_consistent {E : Env} (P : SrcProg E) (env : SessionEnv) :
    Solidity.Roadmap.Prefixes.Consistent (sessionAt P env) := sessionAt_consistent P env

end Solidity.Source.SemanticsExamples


/-! ## Axiom pins -/


/-- info: 'Solidity.Source.sessionAt_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.sessionAt_consistent

/-- info: 'Solidity.Source.firstDone_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.firstDone_mono

/-- info: 'Solidity.Source.firstDone_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.firstDone_none_iff

/-- info: 'Solidity.Source.wrapBits_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.wrapBits_mem

/-- info: 'Solidity.Source.Env.fieldTy?_of_fieldAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.Env.fieldTy?_of_fieldAt

/-- info: 'Solidity.Source.Ledger.semExprCoverage_of_typed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Source.Ledger.semExprCoverage_of_typed

/-- info: 'Solidity.Source.SemanticsExamples.reentrant_callback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.SemanticsExamples.reentrant_callback

/-- info: 'Solidity.Source.SemanticsExamples.revert_rolls_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.SemanticsExamples.revert_rolls_back

/-- info: 'Solidity.Source.SemanticsExamples.modifier_twice_legacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.SemanticsExamples.modifier_twice_legacy

/-- info: 'Solidity.Source.SemanticsExamples.ctor_order_viaIR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.SemanticsExamples.ctor_order_viaIR

/-- info: 'Solidity.Source.SemanticsExamples.order_legacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Source.SemanticsExamples.order_legacy
