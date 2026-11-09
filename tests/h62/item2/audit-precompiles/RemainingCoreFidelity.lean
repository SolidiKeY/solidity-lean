import Solidity.Precompiles.Osaka
import Solidity.Stipend.Rule

/-! Guards against source census fidelity dropping an implicit Contract or
dependent power typing proof. All41 remaining frozen core types are assigned
directly from imported constants; this is not a simultaneous witness or
an actual compiler-success theorem. -/
open Solidity Solidity.Precompiles Solidity.Roadmap.Evm
open Solidity.Precompiles.Bls12381 (r)

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.g1Discount_length
set_option linter.unusedVariables false in
example : g1Discount.length = 128 := @Solidity.Precompiles.Bls12381.g1Discount_length
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.g2Discount_length
set_option linter.unusedVariables false in
example : g2Discount.length = 128 := @Solidity.Precompiles.Bls12381.g2Discount_length
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.decodeFp_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (b : List Nat), decodeFp b = none ↔ p ≤ ofBE b := @Solidity.Precompiles.Bls12381.decodeFp_eq_none_iff
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.g1Add_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), g1Add d = none ↔ d.length ≠ 256 ∨ decodeG1 ((d.map UInt8.toNat).take 128) = none ∨
      decodeG1 ((d.map UInt8.toNat).drop 128) = none := @Solidity.Precompiles.Bls12381.g1Add_eq_none_iff
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.g2Add_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), g2Add d = none ↔ d.length ≠ 512 ∨ decodeG2 ((d.map UInt8.toNat).take 256) = none ∨
      decodeG2 ((d.map UInt8.toNat).drop 256) = none := @Solidity.Precompiles.Bls12381.g2Add_eq_none_iff
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.bind_some_eq_none
set_option linter.unusedVariables false in
example : ∀ {α β : Type} (o : Option α) (f : α → β), (do let a ← o; some (f a)) = none ↔ o = none := @Solidity.Precompiles.Bls12381.bind_some_eq_none
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.g1Msm_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), g1Msm d = none ↔ d.length = 0 ∨ d.length % 160 ≠ 0 ∨
      ∃ c ∈ chunks 160 (d.map UInt8.toNat), decodeG1Sub (c.take 128) = none := @Solidity.Precompiles.Bls12381.g1Msm_eq_none_iff
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.g2Msm_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), g2Msm d = none ↔ d.length = 0 ∨ d.length % 288 ≠ 0 ∨
      ∃ c ∈ chunks 288 (d.map UInt8.toNat), decodeG2Sub (c.take 256) = none := @Solidity.Precompiles.Bls12381.g2Msm_eq_none_iff
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.pair_eq_none
set_option linter.unusedVariables false in
example : ∀ (c : List Nat), (do let P ← decodeG1Sub (c.take 128); let Q ← decodeG2Sub (c.drop 128); some (P.1, Q.1)) = none ↔
      decodeG1Sub (c.take 128) = none ∨ decodeG2Sub (c.drop 128) = none := @Solidity.Precompiles.Bls12381.pair_eq_none
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.pairing_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), pairing d = none ↔ d.length = 0 ∨ d.length % 384 ≠ 0 ∨
      ∃ c ∈ chunks 384 (d.map UInt8.toNat),
        decodeG1Sub (c.take 128) = none ∨ decodeG2Sub (c.drop 128) = none := @Solidity.Precompiles.Bls12381.pairing_eq_none_iff
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.msmGas_succ
set_option linter.unusedVariables false in
example : ∀ (c : Nat) (table : List Nat) (cap k : Nat) (hlen : table.length = 128)
    (htab : ∀ i < 128, (i + 1) * table.getD i cap ≤ (i + 2) * table.getD (i + 1) cap), msmGas c table cap k ≤ msmGas c table cap (k + 1) := @Solidity.Precompiles.Bls12381.msmGas_succ
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.msmGas_mono
set_option linter.unusedVariables false in
example : ∀ (c : Nat) (table : List Nat) (cap : Nat) (hlen : table.length = 128)
    (htab : ∀ i < 128, (i + 1) * table.getD i cap ≤ (i + 2) * table.getD (i + 1) cap) {k l : Nat} (h : k ≤ l), msmGas c table cap k ≤ msmGas c table cap l := @Solidity.Precompiles.Bls12381.msmGas_mono
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.g1MsmGas_mono
set_option linter.unusedVariables false in
example : ∀ {d e : Bytes} (h : d.length ≤ e.length), g1MsmGas d ≤ g1MsmGas e := @Solidity.Precompiles.Bls12381.g1MsmGas_mono
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.g2MsmGas_mono
set_option linter.unusedVariables false in
example : ∀ {d e : Bytes} (h : d.length ≤ e.length), g2MsmGas d ≤ g2MsmGas e := @Solidity.Precompiles.Bls12381.g2MsmGas_mono
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.pairingGas_mono
set_option linter.unusedVariables false in
example : ∀ {d e : Bytes} (h : d.length ≤ e.length), pairingGas d ≤ pairingGas e := @Solidity.Precompiles.Bls12381.pairingGas_mono
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.mapFpToG1_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), mapFpToG1 d = none ↔ d.length ≠ 64 ∨ p ≤ ofBE (d.map UInt8.toNat) := @Solidity.Precompiles.Bls12381.mapFpToG1_eq_none_iff
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.decodeFp2_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (b : List Nat), decodeFp2 b = none ↔ p ≤ ofBE (b.take 64) ∨ p ≤ ofBE ((b.drop 64).take 64) := @Solidity.Precompiles.Bls12381.decodeFp2_eq_none_iff
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.Bls12381
-- Frozen source: Solidity.Precompiles.Bls12381.mapFp2ToG2_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), mapFp2ToG2 d = none ↔ d.length ≠ 128 ∨ decodeFp2 (d.map UInt8.toNat) = none := @Solidity.Precompiles.Bls12381.mapFp2ToG2_eq_none_iff
end Solidity.Precompiles.Bls12381

namespace Solidity.Precompiles.PointEval
-- Frozen source: Solidity.Precompiles.PointEval.bind_check_eq_none
set_option linter.unusedVariables false in
example : ∀ {α β : Type} (o : Option α) (f : α → Bool) (v : β), (o >>= fun i => if f i = true then some v else none) = none ↔
      o = none ∨ ∃ i, o = some i ∧ f i = false := @Solidity.Precompiles.PointEval.bind_check_eq_none
end Solidity.Precompiles.PointEval

namespace Solidity.Precompiles.PointEval
-- Frozen source: Solidity.Precompiles.PointEval.bind_check_eq_some
set_option linter.unusedVariables false in
example : ∀ {α β : Type} {o : Option α} {f : α → Bool} {v w : β}
    (h : (o >>= fun i => if f i = true then some v else none) = some w), w = v := @Solidity.Precompiles.PointEval.bind_check_eq_some
end Solidity.Precompiles.PointEval

namespace Solidity.Precompiles.PointEval
-- Frozen source: Solidity.Precompiles.PointEval.pointEval_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), pointEval d = none ↔ decode d = none ∨ ∃ i, decode d = some i ∧ verifies i = false := @Solidity.Precompiles.PointEval.pointEval_eq_none_iff
end Solidity.Precompiles.PointEval

namespace Solidity.Precompiles.PointEval
-- Frozen source: Solidity.Precompiles.PointEval.decode_length
set_option linter.unusedVariables false in
example : ∀ {d : Bytes} (h : d.length ≠ 192), decode d = none := @Solidity.Precompiles.PointEval.decode_length
end Solidity.Precompiles.PointEval

namespace Solidity.Precompiles.PointEval
-- Frozen source: Solidity.Precompiles.PointEval.pointEval_length
set_option linter.unusedVariables false in
example : ∀ {d : Bytes} (h : d.length ≠ 192), pointEval d = none := @Solidity.Precompiles.PointEval.pointEval_length
end Solidity.Precompiles.PointEval

namespace Solidity.Precompiles.PointEval
-- Frozen source: Solidity.Precompiles.PointEval.pointEval_result
set_option linter.unusedVariables false in
example : ∀ {d o : Bytes} (h : pointEval d = some o), o = word fieldElementsPerBlob ++ word r := @Solidity.Precompiles.PointEval.pointEval_result
end Solidity.Precompiles.PointEval

namespace Solidity.Precompiles.Osaka
-- Frozen source: Solidity.Precompiles.Osaka.fixed_precompileGas
set_option linter.unusedVariables false in
example : fixed.precompileGas = gas := @Solidity.Precompiles.Osaka.fixed_precompileGas
end Solidity.Precompiles.Osaka

namespace Solidity.Precompiles.Osaka
-- Frozen source: Solidity.Precompiles.Osaka.run_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (p : Precompile) (d : Bytes), run p d = none ↔ Malformed p d := @Solidity.Precompiles.Osaka.run_eq_none_iff
end Solidity.Precompiles.Osaka

namespace Solidity.Precompiles.Osaka
-- Frozen source: Solidity.Precompiles.Osaka.fixed_precompile_eq_none_iff
set_option linter.unusedVariables false in
example : ∀ (p : Precompile) (d : Bytes), fixed.precompile p d = none ↔ Malformed p d := @Solidity.Precompiles.Osaka.fixed_precompile_eq_none_iff
end Solidity.Precompiles.Osaka

namespace Solidity.Precompiles.Osaka
-- Frozen source: Solidity.Precompiles.Osaka.gas_mono
set_option linter.unusedVariables false in
example : ∀ {p : Precompile} (hp : LengthPriced p) {d e : Bytes}
    (h : d.length ≤ e.length), gas p d ≤ gas p e := @Solidity.Precompiles.Osaka.gas_mono
end Solidity.Precompiles.Osaka

namespace Solidity.Precompiles.Osaka
-- Frozen source: Solidity.Precompiles.Osaka.ecrecover_exceeds_stipend
set_option linter.unusedVariables false in
example : ∀ (d : Bytes), pinned.stipend < gas .ecrecover d := @Solidity.Precompiles.Osaka.ecrecover_exceeds_stipend
end Solidity.Precompiles.Osaka

namespace Solidity.Stipend
-- Frozen source: Solidity.Stipend.fits_iff
set_option linter.unusedVariables false in
example : ∀ {C : Contract} (b : Body C), (rule C).fits b ↔ ∃ c, progCost b.prog = some c ∧ c ≤ 40 := @Solidity.Stipend.fits_iff
end Solidity.Stipend

namespace Solidity.Stipend
-- Frozen source: Solidity.Stipend.not_fits_cons
set_option linter.unusedVariables false in
example : ∀ {C : Contract} {Γ₁ : Ctx} {out : Ctx} (s : Stmt C [] Γ₁) (P : Prog C Γ₁ out)
    (h : stmtCost s = none), ¬(rule C).fits ⟨.cons s P⟩ := @Solidity.Stipend.not_fits_cons
end Solidity.Stipend

namespace Solidity.Stipend
-- Frozen source: Solidity.Stipend.empty_fits
set_option linter.unusedVariables false in
example : ∀ {C : Contract} , (rule C).fits ⟨(.nil : Prog C [] [])⟩ := @Solidity.Stipend.empty_fits
end Solidity.Stipend

namespace Solidity.Stipend
-- Frozen source: Solidity.Stipend.requireValue_fits
set_option linter.unusedVariables false in
example : ∀ {C : Contract} , (rule C).fits ⟨(requireValue : Prog C [] [])⟩ := @Solidity.Stipend.requireValue_fits
end Solidity.Stipend

namespace Solidity.Stipend
-- Frozen source: Solidity.Stipend.transfer_not_fits
set_option linter.unusedVariables false in
example : ∀ {C : Contract} , ¬(rule C).fits ⟨(.cons (.transfer (.simple (.env .msgSender rfl)) (.simple (.lit 1 rfl))) .nil :
      Prog C [] [])⟩ := @Solidity.Stipend.transfer_not_fits
end Solidity.Stipend

namespace Solidity.Stipend
-- Frozen source: Solidity.Stipend.loop_not_fits
set_option linter.unusedVariables false in
example : ∀ {C : Contract} (a : LoopAnn C []), ¬(rule C).fits ⟨(.cons (.loop a (.simple (.bool false)) .nil) .nil : Prog C [] [])⟩ := @Solidity.Stipend.loop_not_fits
end Solidity.Stipend

namespace Solidity.Stipend
-- Frozen source: Solidity.Stipend.assign_not_fits
set_option linter.unusedVariables false in
example : ∀ {C : Contract} {T : Ty} (l : Loc C [] T) (r : Src C [] T), ¬(rule C).fits ⟨(.cons (.assign l r) .nil : Prog C [] [])⟩ := @Solidity.Stipend.assign_not_fits
end Solidity.Stipend

namespace Solidity.Stipend
-- Frozen source: Solidity.Stipend.read_not_fits
set_option linter.unusedVariables false in
example : ∀ {C : Contract} {p : PrimTy} (l : Loc C [] (.prim p)), ¬(rule C).fits ⟨(.cons (.require (.binop .eqB rfl rfl (.read l) (.read l))) .nil :
      Prog C [] [])⟩ := @Solidity.Stipend.read_not_fits
end Solidity.Stipend

namespace Solidity.Stipend
-- Frozen source: Solidity.Stipend.requires_cost
set_option linter.unusedVariables false in
example : ∀ {C : Contract} (n : Nat), progCost (requires n : Prog C [] []) = some (4 * n) := @Solidity.Stipend.requires_cost
end Solidity.Stipend

namespace Solidity.Stipend
-- Frozen source: Solidity.Stipend.requires_ten_fits
set_option linter.unusedVariables false in
example : ∀ {C : Contract} , (rule C).fits ⟨(requires 10 : Prog C [] [])⟩ := @Solidity.Stipend.requires_ten_fits
end Solidity.Stipend

namespace Solidity.Stipend
-- Frozen source: Solidity.Stipend.requires_eleven_not_fits
set_option linter.unusedVariables false in
example : ∀ {C : Contract} , ¬(rule C).fits ⟨(requires 11 : Prog C [] [])⟩ := @Solidity.Stipend.requires_eleven_not_fits
end Solidity.Stipend

namespace Solidity.Stipend
-- Frozen source: Solidity.Stipend.pow_not_fits
set_option linter.unusedVariables false in
example : ∀ {C : Contract} {p : PrimTy} (x : Var) (a b : Val C [] p) (h : BinOp.pow.accepts p = true)
    (hq : BinOp.pow.ret p = .uint), ¬(rule C).fits ⟨(.cons (.declLocal .uint x (some (.binop .pow h hq a b))) .nil :
      Prog C [] [.val .uint])⟩ := @Solidity.Stipend.pow_not_fits
end Solidity.Stipend

run_cmd Lean.logInfo "REMAINING_CORE_FULL_TYPE_FIDELITY_PASS total=41"
