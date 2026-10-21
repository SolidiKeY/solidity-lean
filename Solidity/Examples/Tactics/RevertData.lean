import Solidity.Tools.Run
import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

/-!
# Revert data reaches a `catch`

A revert returns data (`docs/semantic-gaps.md`, "Revert data"):
`require(c, "m")` and `revert("m")` return `Error(m)`'s ABI encoding,
which `catch Error(string memory r)` decodes into `r`, and `catch (bytes
memory d)` binds raw.  The model computes the data where a `try` can read it,
in the callee a self-call `try` runs (`Stmt.revertData`), and a named clause
binds it by `Stmt.catchData`, which reads the data of the very call that
failed, from the state the `try` started in.

The rule `catchDataBox` gives a goal per datum the callee's body lists
(`Stmt.revertDatas`, sound by `Prog.run_dataS`): the clause after that
datum's allocation, so the closers read its bytes.  Another receiver's reason
is any bytes, which no formula quantifies: that goal is `false`, closed here
because the receiver is `this`.
-/

namespace Solidity.Examples.Tactics.RevertData

open Semantics

/-- Callees that revert with a reason. -/
def Reverter : Contract := contract!{
  uint last;
  function boom() { require(false, "boom"); }
  function check(uint x) { if (x > 3) { revert("big"); } last = x; }
  function two(bool b) { require(b, "a"); revert("bc"); }
  function plain(uint x) { require(x > 3); }
}

local instance : InContract := ⟨Reverter⟩

open scoped Scoped

/-! ## The data

`Error("boom")`: the selector, the offset `32`, the length `4`, the bytes
padded to 32; decoded back to the reason. -/

example : decodeError (encodeError [98, 111, 111, 109]) = some [98, 111, 111, 109] := by decide

/-- info: 100 -/
#guard_msgs in #eval (encodeError "boom".toUTF8.toList).length

/-! ## The program

The callee's copy in the `try` keeps its reason (`revert(hex…)`, here the
self-call body), and the `Error` clause binds `r` by `Stmt.catchData`
(`string memory r = reason(boom)`). -/

/--
info: "try address(address(this)).boom() { } catch Error(string memory) { { string memory r = reason(boom); last = r.length; } } catch Panic(uint) { last = 9; } catch { last = 9; }"
-/
#guard_msgs in
#eval Prog.toStr [] (sol[Reverter]{ try this.boom() { } catch Error(string memory r) {
    last = r.length; } catch { last = 9; } })

/-- A name the clause does not read binds nothing: the clause as written
(so another contract's `try` with a named, unread reason proves as before). -/
example : Prog.toStr [] (sol[Reverter]{ try address(7).boom() { } catch Error(string memory r) {
    last = 2; } catch { } }) =
  "try address(7).boom() { } catch Error(string memory) { last = 2; } \
    catch Panic(uint) { } catch { }" := rfl

/-! ## The run

From a state whose own address is `7`, `boom()` reverts with `Error("boom")`
and the `Error` clause stores the reason's length and first byte. -/

private def σ₇ : State Reverter [] := { State.init Reverter with tx := { selfAddress := ⟨7, rfl⟩ } }

/-- info: Except.ok "last = 98" -/
#guard_msgs in
#eval (Prog.runT σ₇ (sol[Reverter]{ try this.boom() { } catch Error(string memory r) {
    last = r[0]; } catch { last = 9; } })).map fun τ => Tools.fmtStorageLine Reverter τ.storage

/-- info: Except.ok "last = 9" -/
#guard_msgs in
#eval (Prog.runT σ₇ (sol[Reverter]{ try this.check(5) { last = 1; } catch (bytes memory d) {
    last = 9; } })).map fun τ => Tools.fmtStorageLine Reverter τ.storage

/-! ## The rule

One goal per datum the callee lists, the datum allocated as a literal in
front of the clause (`litBytes`); another receiver's goal `false`. -/

/--
info: @LeanTaclet.catchDataBox : ∀ {C : Contract} {k : Nat} {Γ ρ ps Γf Γ₁ : Ctx} {call : ExtCall C Γ} {rets : Binders ρ}
  {selfArgs : Args C Γ ps} {selfBody : Prog C (ρ ++ ps) Γf} {self : Bool} {kind : CatchKind} {x : Var}
  {body : Prog C (LTy.mem bytesR :: Γ) Γ₁},
  dl[LeanTaclet C k]{ [ {bytes memory x = data(call);body;}; ] ⇝
    "datum": ∀ d. [ {bytes memory x = d;body;} ] ; "another receiver": ∀ fresh. [ {bytes memory x = fresh;body;} ] }
-/
#guard_msgs in #check @LeanTaclet.catchDataBox

/-! ## Proving -/

/-- **The callee's reason reaches `catch Error(string memory r)`**:
`require(false, "boom")` in `boom()`, and `r`'s bytes are `"boom"`. -/
theorem boomReason : ⊨ dl!{ [ try this.boom() { } catch Error(string memory r) {
    assert(r.length == 4); assert(r[0] == 98); assert(r[1] == 111); assert(r[2] == 111);
    assert(r[3] == 109); } catch { }; ] true } := by
  sol_symex
  sol_decide

/-- `revert("big")` in a branch of the callee: its reason, when it reverts. -/
theorem checkReason : ⊨ dl!{ [ try this.check(5) { } catch Error(string memory r) {
    assert(r.length == 3); assert(r[0] == 98); } catch { }; ] true } := by
  sol_symex
  sol_decide

/-- Two reasons in the callee: the clause holds for each (`"a"` or
`"bc"`), the over-approximation the rule reads off the body. -/
theorem twoReasons : ⊨ dl!{ [ try this.two(false) { } catch Error(string memory r) {
    assert(r.length == 1 || r.length == 2); } catch { }; ] true } := by
  sol_symex
  sol_decide

/-- `catch (bytes memory d)`: the raw data.  `plain` reverts with none
(`require(x > 3)` carries no reason), so `d` is empty.  (`Error("boom")`'s
100 bytes, written out byte by byte, are past the closer's bounds.) -/
theorem plainData : ⊨ dl!{ [ try this.plain(1) { } catch (bytes memory d) {
    assert(d.length == 0); }; ] true } := by
  sol_symex
  sol_decide

/-! ## Custom errors

`revert E(7)` in a self-call's callee reverts with `E`'s selector, folded as
solc folds it (`0x002ff067`, the first four bytes of the Keccak-256 of
`E(uint256)`), then the argument's ABI word: a literal's, so the rule reads
the datum's 36 bytes. -/

/-- A callee that reverts with a custom error. -/
def Custom : Contract := contract!{
  error E(uint256 code);
  uint last;
  function failE() { revert E(7); }
  function failIf(uint x) { require(x > 3, E(x)); }
  function mixed(uint x) { if (x > 5) { revert E(x); } require(x > 1, "small"); }
}

#guard Keccak.selector "E(uint256)" == 0x002ff067

section Custom

local instance : InContract := ⟨Custom⟩

/-- info: Except.ok "last = 36" -/
#guard_msgs in
#eval (Prog.runT { State.init Custom with tx := { selfAddress := ⟨7, rfl⟩ } }
    (sol[Custom]{ try this.failE() { } catch (bytes memory d) { last = d.length; } })).map
  fun τ => Tools.fmtStorageLine Custom τ.storage

/-- info: Except.ok "last = 1" -/
#guard_msgs in
#eval (Prog.runT { State.init Custom with tx := { selfAddress := ⟨7, rfl⟩ } }
    (sol[Custom]{ try this.failIf(1) { } catch (bytes memory d) { last = d[35]; } })).map
  fun τ => Tools.fmtStorageLine Custom τ.storage

/-- **A custom error's data reaches `catch (bytes memory d)`**: its selector
and its argument. -/
theorem customData : ⊨ dl!{ [ try this.failE() { } catch (bytes memory d) {
    assert(d.length == 0 || d.length == 36 && d[1] == 47 && d[3] == 103 && d[35] == 7);
    }; ] true } := by
  sol_symex
  sol_prove

/-- A callee that reverts with a custom error of a symbolic argument and
with a reason: the custom datum cannot decode as `Error`
(`RevPart.notError`), so `catch Error(string memory r)` binds the reason. -/
theorem mixedReason : ⊨ dl!{ ∀ uint x; [ try this.mixed(x) { } catch Error(string memory r) {
    assert(r.length == 5); assert(r[0] == 115); } catch { }; ] true } := by
  sol_symex
  sol_decide

end Custom

/-! ## Another contract's reason

At another receiver the reason is any bytes: the rule's last goal is the
clause for every fresh `bytes` of any contents (`Fml.allocAll`, printed
`∀ fresh r`), behind `require(a != 0); require(a != address(this));`.  The
clause is proved for every reason, its length a `uint` the closer reads as
any other. -/

/-- **Another contract's reason**, its length read. -/
theorem externalReason : ⊨ dl!{ ∀ uint a; [ try address(a).boom() { } catch Error(string memory r) {
    if (r.length > 3) { assert(r.length >= 4); } } catch { }; ] true } := by
  sol_prove (steps := 256)
  · sol_leaf
    sol_close

end Solidity.Examples.Tactics.RevertData
