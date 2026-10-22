import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Close
import Solidity.Calculus.CorrectCallback
import Solidity.Calculus.CallbackSound

/-! Regressions for the strict correctness judgement and the October audit. -/
namespace Solidity.Examples.Tactics.AuditRepairs

open Semantics
open scoped Scoped

def Bank : Contract := contract!{
  function first(uint x, uint y) returns (uint) { return x; }
  function g(uint x, uint y) external { }
}
def IR : Contract := { Bank with evalOrder := .viaIR }

/-- The whole constant is folded before target typing or operand sequencing. -/
example : (Prog.run (State.init Bank) (sol[Bank]{
    uint x = 1 - 2 + 5; uint y = 2 * (1 / 2); uint z = (1 / 2) * 2;
    assert(x == 4); assert(y == 1); assert(z == 1);
  })).isOk = true := by decide +kernel
example : (Prog.run (State.init IR) (sol[IR]{
    uint x = 1 - 2 + 5; uint y = 2 * (1 / 2); uint z = (1 / 2) * 2;
    assert(x == 4); assert(y == 1); assert(z == 1);
  })).isOk = true := by decide +kernel

/-- Source constants fold before unchecked operators become wrapping ones. -/
example : (Prog.run (State.init Bank) (sol[Bank]{
    uint y; uint z; unchecked { y = 2 * (1 / 2); z = (1 / 2) * 2; };
    assert(y == 1); assert(z == 1);
  })).isOk = true := by decide +kernel
example : (Prog.run (State.init IR) (sol[IR]{
    uint y; uint z; unchecked { y = 2 * (1 / 2); z = (1 / 2) * 2; };
    assert(y == 1); assert(z == 1);
  })).isOk = true := by decide +kernel

example : True := by
  fail_if_success
    let _ := sol[Bank]{ uint y; unchecked { y = 0 - 1; }; }
  trivial

/-- Parentheses do not restore checked arithmetic inside unchecked. -/
example : (Prog.run (State.init Bank) (sol[Bank]{
    uint8 x = 255; uint8 y; unchecked { y = (x += 1); };
    assert(x == 0); assert(y == 0);
  })).isOk = true := by decide +kernel
example : (Prog.run (State.init Bank) (sol[Bank]{
    uint8 x = 255; uint8 y = (x += 1);
  })).halt? = some .revert := by decide +kernel

/-- Explicit wrapping notation used by printers retains its word semantics. -/
example : (Prog.run (State.init Bank) (sol[Bank]{
    uint x = 0 -% 1; assert(x == type(uint).max);
  })).isOk = true := by decide +kernel

/-- An earlier named argument is captured before a later increment. -/
example : (Prog.run (State.init Bank) (sol[Bank]{
    uint i = 1; uint x = first(i, i++); assert(x == 1); assert(i == 2);
  })).isOk = true := by decide +kernel
example : (Prog.run (State.init IR) (sol[IR]{
    uint i = 1; uint x = first(i, i++); assert(x == 1); assert(i == 2);
  })).isOk = true := by decide +kernel

private def funded : State Bank [] :=
  { State.init Bank with selfBalance := ⟨10, rfl⟩ }
/-- The transfer uses the original named receiver before the amount changes it. -/
example : ((Prog.run funded (sol[Bank]{
    uint r = 9; r.transfer((r = 3));
  })).toOption.map fun o =>
    ((lookupBy (⟨9, rfl⟩ : PrimTy.uint.Denote) o.st.net).getD 0,
     (lookupBy (⟨3, rfl⟩ : PrimTy.uint.Denote) o.st.net).getD 0,
     o.st.selfBalance.1)) = some (-3, 0, 7) := by decide +kernel

private def badTerm (n : Nat) (h : PrimTy.uint.inRange n = true) : Tm Bank [] (.val .uint) :=
  .app2 (.binop .add rfl) (.lit (p := .uint) ⟨115792089237316195423570985008687907853269984665640564039457584007913129639935, rfl⟩) (.lit ⟨n, h⟩)

/-- Both terms fail; total formula equality and strict Spec equality differ. -/
example : (badTerm 1 rfl).eval (State.init Bank) = none := by decide +kernel
example : holds (State.init Bank) (.eq (badTerm 1 rfl) (badTerm 2 rfl)) := by
  rw [holds_eq_of_agree rfl rfl]
  decide +kernel
example : ¬ Spec.sat (State.init Bank) (.eq (badTerm 1 rfl) (badTerm 2 rfl)) := by
  intro ⟨v, hv, _⟩
  have hn : (badTerm 1 rfl).eval (State.init Bank) = none := by decide +kernel
  rw [hn] at hv
  cases hv

example : ⊨ (Spec.box (sol[Bank]{ require(false); }) .tt) := by
  apply Proves.valid (R := .all)
  sol_prove
example : ⊨[Invariant.top] (Spec.tt : Spec Bank []) := by
  apply ProvesC.valid
  apply ProvesC.plain _ rfl
  exact .closeHolds (fun _ => trivial)

/-- Payment output makes its joint ledger/balance effect explicit and replays. -/
example : (dl[Bank]{ { pay(9, 3) } true } : Fml Bank []) =
    .upd .diamond (Upd.nil.snoc (.pay (.lit ⟨9, rfl⟩) (.lit ⟨3, rfl⟩))) .tt := rfl

/-- Net-only text cannot silently stand for a balance debit. -/
example : True := by
  fail_if_success
    have _ : Fml Bank [] :=
      dl[Bank]{ { net := if(9 = this) then net else store(net, at(9), net(9) - 3) } true }
  trivial

/-- A callback may leave a different live balance, even after the payment debit. -/
example : ExecS ((Invariant.top (C := Bank)).fml.stateInv true) funded
    (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 3 rfl)))
    (.ok ⟨(funded.pay ⟨9, rfl⟩ 3).havoc funded.storage [] ⟨42, rfl⟩,
      List.prefix_refl _⟩) :=
  .transferResume (J := (Invariant.top (C := Bank)).fml.stateInv true) (σ := funded)
    (r := .simple (.lit 9 rfl)) (a := .simple (.lit 3 rfl))
    (o₁ := ⟨funded.pay ⟨9, rfl⟩ 3, List.prefix_refl _⟩)
    (st := funded.storage) (nt := []) (sb := ⟨42, rfl⟩) rfl rfl trivial trivial

/-- The public judgement rejects internal formulas. -/
example : True := by
  fail_if_success have _ : Prop := ⊨ (Fml.tt : Fml Bank [])
  trivial

end Solidity.Examples.Tactics.AuditRepairs
