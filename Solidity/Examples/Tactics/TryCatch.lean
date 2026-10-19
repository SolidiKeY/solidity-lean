import Solidity.Tools.Run
import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.CallbackSound
import Solidity.Tools.Inspect

/-!
# `try`/`catch`: an external call and a block per way it ends

`try e.f(a) returns (uint v) { … } catch Error(string memory) { … }
catch Panic(uint c) { … } catch { … }` calls a function of another contract
(`Stmt.tryCall`).  Its callee is never run: without callbacks it changes
nothing of this contract, and how it ends is the transaction's
(`TTx.ext`), a call with no entry reaching an address with no code and
reverting in the caller.  So a proof of a `try` has a goal per clause
(`tryCallNoCallbackBox`): the success block for every value of the returned
data, and each `catch` block from the state the call was made in.  A
missing `Error`/`Panic` clause is the catch-all's block, and a missing
catch-all `revert();`, as solkey's `TryStatement.of` normalises it.

With callbacks (`tryCallWithCallbackBox`, `ProvesC.tryCall`) the contract
also owes its invariant where control leaves, and its success block runs
from any state the callee may leave in which the invariant holds.  A
diamond `try` closes to `false` (`tryCallDiamond`, solkey has no rule): the
call may revert in the caller, and no formula says it does not.
-/

namespace Solidity.Examples.Tactics.TryCatch

open Semantics

/-- A pinger: how often a ping went through, and how often it failed. -/
def Pinger : Contract := contract!{ uint pings; uint fails; uint last; }

local instance : InContract := ⟨Pinger⟩

open scoped Scoped

/-! ## The rules -/

/--
info: @Taclet.tryCallNoCallbackBox : ∀ {C : Contract} {k : Nat} {Γ : Ctx} {call : ExtCall C Γ} {x : Ctx} {rets : Binders x}
  {x_1 : Ctx} {body : Prog C (x ++ Γ) x_1} {x_2 : Ctx} {errorBody : Prog C Γ x_2} {x_3 : Ctx} {code : CodeBinder x_3}
  {x_4 : Ctx} {panicBody : Prog C (x_3 ++ Γ) x_4} {x_5 : Ctx} {otherBody : Prog C Γ x_5},
  dl{ [ try call returns (rets) body catch Error errorBody catch Panic(code) panicBody catch otherBody; ] ⇝
    "call succeeded": ∀ rets. [ body ] ; "Error caught": [ errorBody ] ; "Panic caught": ∀ code. [ panicBody ] ;
      "other failure caught": [ otherBody ] }
-/
#guard_msgs in #check @Taclet.tryCallNoCallbackBox

/--
info: @LeanTaclet.tryCallDiamond : ∀ {C : Contract} {k : Nat} {Γ : Ctx} {call : ExtCall C Γ} {x : Ctx} {rets : Binders x}
  {x_1 : Ctx} {body : Prog C (x ++ Γ) x_1} {x_2 : Ctx} {errorBody : Prog C Γ x_2} {x_3 : Ctx} {code : CodeBinder x_3}
  {x_4 : Ctx} {panicBody : Prog C (x_3 ++ Γ) x_4} {x_5 : Ctx} {otherBody : Prog C Γ x_5},
  dl[LeanTaclet C k]{ ⟨ try call returns (rets) body catch Error errorBody catch Panic(code) panicBody catch otherBody;
    ⟩ ⇝ false }
-/
#guard_msgs in #check @LeanTaclet.tryCallDiamond

/--
info: dl{
  [
    try address(7).get() returns (uint v) {last = v;} catch Error(string memory) {} catch Panic(uint c) {last = c;}
      catch {};
    ] true } : Fml Pinger []
-/
#guard_msgs in
#check (dl!{ [ try I(7).get() returns (uint v) { last = v; } catch Panic(uint c) { last = c; }
  catch { }; ] true } : Fml Pinger [])

/-! ## Reading and printing -/

/-- The clauses normalised: the missing `Error` and `Panic` clauses are the
catch-all's block, and the receiver `I(a)` is `a`. -/
example : Prog.toStr [] (sol{ uint a = 7;
    try I(a).ping() { pings += 1; } catch { fails += 1; } }) =
    "uint a = 7; try address(a).ping() { pings += 1; } \
      catch Error(string memory) { fails += 1; } catch Panic(uint) { fails += 1; } \
      catch { fails += 1; }" := rfl

/-- A missing catch-all reverts: the call's failure passes on to the caller. -/
example : Prog.toStr [] (sol{ uint a = 7;
    try I(a).get(1) returns (uint v) { last = v; } catch Panic(uint c) { last = c; } }) =
    "uint a = 7; try address(a).get(1) returns (uint v) { last = v; } \
      catch Error(string memory) { revert(); } catch Panic(uint c) { last = c; } \
      catch { revert(); }" := rfl

/-- A receiver that is not simple is read into a local before the call. -/
example : Prog.toStr [] (sol{ try I(last).ping() { pings += 1; } catch { fails += 1; } }) =
    "uint se1 = last; try address(se1).ping() { pings += 1; } \
      catch Error(string memory) { fails += 1; } catch Panic(uint) { fails += 1; } \
      catch { fails += 1; }" := rfl

/-! ## Running -/

/-- The call's outcome is the transaction's: here `ping` on `7` returns. -/
def pingOk : State Pinger [] :=
  { State.init Pinger with tx := { ext := [(⟨⟨7, rfl⟩, "ping", []⟩, .ok [])] } }

private def pingP : Prog Pinger [] [.val .uint] :=
  sol{ uint a = 7; try I(a).ping() { pings += 1; } catch { fails += 1; } }

/-- info: Except.ok (some "1") -/
#guard_msgs in
#eval do
  let σ ← Prog.runT pingOk pingP
  pure (Tools.fmtRoot σ.storage "pings")

/-- The same call reverting with `Panic(0x11)`: the `Panic` clause runs, with
the code bound. -/
def pingPanic : State Pinger [] :=
  { State.init Pinger with tx := { ext := [(⟨⟨7, rfl⟩, "ping", []⟩, .panic ⟨17, rfl⟩)] } }

private def pingPanicP : Prog Pinger [] [.val .uint] := sol{ uint a = 7;
  try I(a).ping() { pings += 1; } catch Panic(uint c) { last = c; } catch { fails += 1; } }

/-- info: Except.ok (some "17") -/
#guard_msgs in
#eval do
  let σ ← Prog.runT pingPanic pingPanicP
  pure (Tools.fmtRoot σ.storage "last")

/-! The returned data are ABI words, read at the locals' types when a `try`
decodes them (`PrimTy.ofWord?`): an `int256` is the word's two's
complement, a `bool` `0` or `1`. -/

section Decoding

def Decoder : Contract := contract!{ bool flag; int neg; }

local instance : InContract := ⟨Decoder⟩

private def decodeP : Prog Decoder [] [.val .uint] := sol{ uint a = 7;
  try I(a).get() returns (bool b, int n) { flag = b; neg = n; } catch { } }

def decodeOk : State Decoder [] :=
  { State.init Decoder with
    tx := { ext := [(⟨⟨7, rfl⟩, "get", []⟩, .ok [⟨1, rfl⟩, PrimTy.ofIntD .uint (2 ^ 256 - 1)])] } }

/-- info: Except.ok (some "true", some "-1") -/
#guard_msgs in
#eval do
  let σ ← Prog.runT decodeOk decodeP
  pure (Tools.fmtRoot σ.storage "flag", Tools.fmtRoot σ.storage "neg")

/-- A `bool` word that is neither `0` nor `1` does not decode: the caller
reverts, as solc's decoder does. -/
theorem decodeBadBool :
    (Prog.run { State.init Decoder with
      tx := { ext := [(⟨⟨7, rfl⟩, "get", []⟩, .ok [⟨2, rfl⟩, ⟨0, rfl⟩])] } } decodeP).halt? =
      some .revert := by
  decide +kernel

end Decoding

def pingNoCodeCore : Prog Pinger [] [.val .uint] := sol{ uint a = 7;
  try I(a).ping() { pings += 1; } catch { fails += 1; } }

/-- With no entry, the address has no code: the caller reverts (the typed
run from `Pinger`'s initial state, by the kernel). -/
theorem pingNoCode : (Prog.run (State.init Pinger) pingNoCodeCore).halt? = some .revert := by
  decide +kernel

/-! ## Proving, without callbacks -/

/-- Whatever the call does, one of the two counters goes up: the success
block and each `catch` block are a goal. -/
theorem pingCounts :
    ⊨ dl!{ pings == 0 ∧ fails == 0 →
      [ uint a = 7; try I(a).ping() { pings += 1; } catch { fails += 1; }; ]
        pings + fails == 1 } := by
  sol_symex
  sol_close

/-- The returned value is a value of its type, whatever the callee returned:
data that does not decode reverts in the caller. -/
theorem getStores :
    ⊨ dl!{ [ try I(7).get() returns (uint v) { last = v; pings = v; } catch { last = 0; pings = 0; }; ]
        last == pings } := by
  sol_symex
  sol_close

/-- One rule at a time: `tryCallNoCallbackBox` leaves a goal per clause, the
success block's for every value of `v` (`allRight`). -/
theorem getWalk :
    ⊨ dl!{ [ try I(7).get() returns (uint v) { last = v; } catch { last = 0; }; ] true } := by
  apply Proves.valid
  apply branches .tryCallNoCallbackBox <;>
      (try simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]) <;>
    (try and_intros)
  · apply allRight
    apply update .storageRootWriteStore
    sol_leaf
    sol_close
  all_goals
    apply update .storageRootWriteStore
    sol_leaf
    sol_close

/-! ## Proving, with callbacks

`fails <= pings` is the pinger's invariant: it holds where control leaves the
contract, and the success block may assume it of whatever state the callee
leaves.  The calculus with callbacks is `Calculus/Callback.lean`'s
`ProvesC`, sound against `ValidC` for a first-order invariant
(`ProvesC.valid`, `Calculus/CallbackSound.lean`); the success block's
goal reads the invariant assumed at its scope (`Proves.openInv`), past the
callee's `{havoc}`. -/

/-- `fails <= pings`. -/
def pingInv : Invariant Pinger := ⟨dl!{ fails <= pings }, rfl⟩

/-- A ping keeps the invariant with callbacks: it holds at the call, the
success block counts a ping in a state where it holds, and a failed call
changes nothing. -/
theorem pingKeepsInv :
    ValidC pingInv dl!{ fails <= pings →
      [ try I(7).ping() { pings += 1; } catch { }; ] fails <= pings } := by
  apply ProvesC.valid
  apply ProvesC.intro
  apply ProvesC.tryCall .tryCallWithCallbackBox
  · -- invariant on exit
    apply ProvesC.plain _ rfl
    sol_leaf
    sol_close
  · -- call succeeded: from any state the callee leaves in which `I` holds
    apply ProvesC.plain _ rfl
    sol_derive
    refine Proves.openInv ?_
    sol_leaf
    sol_close
  · -- each `catch` block, from where the call was made
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    refine ⟨?_, ?_, ?_⟩ <;>
    · apply ProvesC.plain _ rfl
      sol_derive
      all_goals
        sol_leaf
        sol_close

/-- What holds with callbacks holds without: the deterministic run is one of
the runs with callbacks. -/
theorem pingKeepsInv_noCallback :
    ⊨ dl!{ fails <= pings →
      [ try I(7).ping() { pings += 1; } catch { }; ] fails <= pings } :=
  valid_of_validC pingKeepsInv rfl rfl

/-! ## A callee calls back: solkey's bug 5

A `try` hands its callee all the gas, so the callee may call back into the
contract, the contract itself included (`try this.f()`), whatever
`transferSemantics` says: that option is about `transfer` and `send`, whose
2300 gas cannot call back.  `⊨` reads every callee as keeping this
contract's state, as solkey's `tryCallNoCallbackBox` does, and proves
`last == 0` past a call that may write `last`; `ValidT .noCallback` lets the
callee leave any state that keeps the invariant (`⊤` unless given), and
refutes it (`docs/options.md`). -/

/-- `last = 0;`, then a call that may write `last`. -/
def selfCall : Fml Pinger [] := dl!{ [ last = 0; try I(7).ping() { } catch { }; ] last == 0 }

/-- Read as every callee keeping the state, the call changes nothing. -/
theorem selfCall_valid : ⊨ dl!{ [ last = 0; try I(7).ping() { } catch { }; ] last == 0 } := by
  sol_symex
  sol_close

/-- A statement that forks nowhere runs as the typed run. -/
theorem execOfRun {C : Contract} {J : StateInv C} {Γ Γ' : Ctx} {σ : State C Γ}
    {s : Stmt C Γ Γ'} {o : Out C σ.H Γ'} (hf : s.forks = false)
    (h : s.run σ = .ok o) : ExecS J σ s (.ok o) := by
  have := ExecS.det (J := J) (σ := σ) (Stmt.forksIn_of_forks hf)
  rwa [h] at this

/-- `Pinger`'s storage: `pings`, `fails`, `last`. -/
def pinger (p f l : Nat) (hp : PrimTy.uint.inRange p = true := by decide)
    (hf : PrimTy.uint.inRange f = true := by decide)
    (hl : PrimTy.uint.inRange l = true := by decide) : Storage Pinger :=
  .cons (.prim ⟨p, hp⟩) (.cons (.prim ⟨f, hf⟩) (.cons (.prim ⟨l, hl⟩) .nil))

/-- **The callee may write `last`**: under `transferSemantics:noCallback`
the call succeeds having set `last` to `42`, which no invariant forbids. -/
theorem selfCall_noCallback : ¬ ValidT .noCallback selfCall := by
  intro h
  have H := h (State.init Pinger) _
    (.cons (execOfRun rfl rfl)
      (.cons (ExecS.tryOk (st := pinger 0 0 42) (nt := []) (vs := []) (rest := [])
        ?exit ?resume rfl .nil) .nil))
  case exit => trivial
  case resume => trivial
  have H2 := H _ ExecF.nil
  simp only [COut.after, holdsC, holds] at H2
  exact absurd H2 (by with_unfolding_all decide)

/-- With the invariant the callee keeps, the honest reading proves what the
invariant gives: `pingKeepsInv` under `noCallback`, the same derivation. -/
theorem pingKeepsInv_honest :
    ValidT (.noCallback pingInv) dl!{ fails <= pings →
      [ try I(7).ping() { pings += 1; } catch { }; ] fails <= pings } := by
  apply ProvesC.validT
  apply ProvesC.intro
  apply ProvesC.tryCall .tryCallWithCallbackBox
  · apply ProvesC.plain _ rfl
    sol_leaf
    sol_close
  · apply ProvesC.plain _ rfl
    sol_derive
    refine Proves.openInv ?_
    sol_leaf
    sol_close
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    refine ⟨?_, ?_, ?_⟩ <;>
    · apply ProvesC.plain _ rfl
      sol_derive
      all_goals
        sol_leaf
        sol_close

end Solidity.Examples.Tactics.TryCatch
