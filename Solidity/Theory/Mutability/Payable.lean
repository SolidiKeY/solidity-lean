import Solidity.Theory.Mutability.View
import Solidity.Semantics.ContractWorld


namespace Solidity.Theory.Mutability

open Solidity

variable {C : Contract}

example (tx : TTx) : 0 < tx.msgValue.1 ↔ tx.msgValue.1 ≠ 0 := by
  have h := PrimTy.uint_nonneg tx.msgValue
  omega

theorem refuses {payable : Bool} {v : Int} (hp : payable = false) (hv : v ≠ 0) :
    (!payable && v != 0) = true := by
  subst hp
  simpa only [Bool.not_false, Bool.true_and, bne_iff_ne, ne_eq] using hv

theorem System.run_nonpayable {D A : Type} (M : Lifetime.System C D A) (s : Lifetime.World C)
    (a : A) (tx : TTx) (hp : M.payable a = false) (hv : tx.msgValue.1 ≠ 0) :
    M.run s a tx = .error .revert := by
  unfold Lifetime.System.run
  rw [if_pos (refuses hp hv)]

theorem deployT_nonpayable {Γ' : Ctx} (P : Prog C [] Γ') (tx : TTx)
    (hp : (C.ctor.map (·.payable)).getD false = false) (hv : tx.msgValue.1 ≠ 0) :
    C.deployT P tx = .error .revert := by
  unfold Contract.deployT
  rw [if_pos (refuses hp hv)]

example {Γ' : Ctx} (P : Prog C [] Γ') (tx : TTx)
    (hc : C.ctor = none) (hv : tx.msgValue.1 ≠ 0) :
    C.deployT P tx = .error .revert :=
  deployT_nonpayable P tx (by rw [hc]; rfl) hv

theorem transact_nonpayable {L : Transient.Layout} {α : Type} (body : Transient.Program C L α)
    (world : Lifetime.World C) (tx : TTx) (ctx : Transient.Context) (hv : tx.msgValue.1 ≠ 0) :
    Transient.Program.transact body world tx false ctx = .error .revert := by
  unfold Transient.Program.transact
  rw [if_pos (refuses rfl hv)]

namespace ContractWorld

open Solidity.ContractWorld

variable {K : Type} [DecidableEq K] {contracts : K → Contract}

omit [DecidableEq K] in
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
