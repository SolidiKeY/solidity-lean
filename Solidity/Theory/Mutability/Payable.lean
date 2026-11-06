import Solidity.Theory.Mutability.View
import Solidity.Semantics.ContractWorld

/-!
# A non-payable entry refuses value (S3.1, payable)

`docs/feature-work/semantics-extensions.md`, S3.1: a non-payable function
reverts whenever `msg.value > 0`.

The intrinsic `Mutability` (`AST.lean`) has no `payable`: paying is a
property of an entry point, not of a body (a callee's booking of
`msg.value` is its caller's).  Every entry point of the semantics carries
the flag and checks it before the body runs, so the body is irrelevant:

* one transaction of a lifetime model, `Lifetime.System.run`;
* a deployment, `Contract.deployT` (the constructor's `payable`);
* a frame of the contract world, `ContractWorld.World.enter` and
  `World.callFrame`; a static frame refuses value too (`World.enter_static`);
* a transaction of the transient layer, `Transient.Program.transact`.

Not covered here: `World.create` (its frame, `World.deployFrame`, is
private to `Semantics/ContractWorld.lean`; it enters through `World.enter`
with the constructor's flag, so `World.enter_nonpayable` is its step),
`World.deployLibrary`, and the ABI dispatch of `Semantics/Dispatch.lean` and
`Semantics/AbiEntry*.lean`, which model no `callvalue` check.  The flag of a
`Lifetime.System` action or a `ContractWorld.Entry` is the model's: no
theorem here ties it to the declared `FunDecl.payable` (a constructor's,
`Contract.ctor`, is read directly by `deployT`).

`msg.value > 0` is `tx.msgValue.1 ≠ 0` (a `uint` is non-negative).
-/

namespace Solidity.Theory.Mutability

open Solidity

variable {C : Contract}

/-- `!payable && v ≠ 0` holds where the entry is non-payable and paid. -/
theorem refuses {payable : Bool} {v : Int} (hp : payable = false) (hv : v ≠ 0) :
    (!payable && v != 0) = true := by
  subst hp
  simpa only [Bool.not_false, Bool.true_and, bne_iff_ne, ne_eq] using hv

/-- **A non-payable action of a lifetime model reverts on value**, whatever
its body (`function f() { … }` called with `{value: 1}`). -/
theorem System.run_nonpayable {D A : Type} (M : Lifetime.System C D A) (s : Lifetime.World C)
    (a : A) (tx : TTx) (hp : M.payable a = false) (hv : tx.msgValue.1 ≠ 0) :
    M.run s a tx = .error .revert := by
  unfold Lifetime.System.run
  rw [if_pos (refuses hp hv)]

/-- **A deployment through a non-payable constructor reverts on value**
(the implicit constructor is non-payable). -/
theorem deployT_nonpayable {Γ' : Ctx} (P : Prog C [] Γ') (tx : TTx)
    (hp : (C.ctor.map (·.payable)).getD false = false) (hv : tx.msgValue.1 ≠ 0) :
    C.deployT P tx = .error .revert := by
  unfold Contract.deployT
  rw [if_pos (refuses hp hv)]

/-- **A transient-layer transaction of a non-payable entry reverts on
value.** -/
theorem transact_nonpayable {L : Transient.Layout} {α : Type} (body : Transient.Program C L α)
    (world : Lifetime.World C) (tx : TTx) (ctx : Transient.Context) (hv : tx.msgValue.1 ≠ 0) :
    Transient.Program.transact body world tx false ctx = .error .revert := by
  unfold Transient.Program.transact
  rw [if_pos (refuses rfl hv)]

namespace ContractWorld

open Solidity.ContractWorld

variable {K : Type} [DecidableEq K] {contracts : K → Contract}

omit [DecidableEq K] in
/-- **Entering a non-payable frame with value reverts**, funded or not. -/
theorem World.enter_nonpayable (w : World contracts) {k : K} (self : Address)
    (ctx : ContractWorld.Context) (st : Storage (contracts k)) (hv : ctx.value.1 ≠ 0) :
    w.enter self ctx st false = .error .revert := by
  unfold World.enter
  split
  · rfl
  · have h : ((!false || ctx.isStatic) && ctx.value.1 != 0) = true := by
      simpa only [Bool.not_false, Bool.true_or, Bool.true_and, bne_iff_ne, ne_eq] using hv
    simp only [h, if_true]

omit [DecidableEq K] in
/-- **Entering a static frame with value reverts**, payable or not
(`STATICCALL` carries no value). -/
theorem World.enter_static (w : World contracts) {k : K} (self : Address)
    (ctx : ContractWorld.Context) (st : Storage (contracts k)) (payable : Bool)
    (hs : ctx.isStatic = true) (hv : ctx.value.1 ≠ 0) :
    w.enter self ctx st payable = .error .revert := by
  unfold World.enter
  split
  · rfl
  · have h : ((!payable || ctx.isStatic) && ctx.value.1 != 0) = true := by
      have hv' : (ctx.value.1 != 0) = true := by simpa only [bne_iff_ne, ne_eq] using hv
      simp only [hs, Bool.or_true, hv', Bool.and_self]
    simp only [h, if_true]

/-- **A call frame of a non-payable entry reverts on value**, whatever the
body: `function f() external { … }` called as `c.f{value: 1}()`. -/
theorem World.callFrame_nonpayable (w : World contracts) {k : K} {α : Type} (r : Handle k)
    (entry : Entry (contracts k) α) (ctx : ContractWorld.Context) (hp : entry.payable = false)
    (hv : ctx.value.1 ≠ 0) : w.callFrame r entry ctx = .error .revert := by
  unfold World.callFrame
  split
  · rfl
  · cases hs : w.storage? r with
    | none => rfl
    | some st =>
      simp only [bind, Except.bind, TRes.ofOpt]
      rw [hp, World.enter_nonpayable w r.address ctx st hv]

end ContractWorld

end Solidity.Theory.Mutability
