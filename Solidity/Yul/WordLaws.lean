import Solidity.Yul.Words

/-! Universal zero-divisor and out-of-range-index contracts. These are kernel
laws over arbitrary words, separate from the finite Python-oracle controls. -/
namespace Solidity.Yul

theorem sdiv_zero (x : Word) :
    Pure.eval .sdiv (fun i => if i = 0 then x else word 0) = word 0 := rfl

theorem smod_zero (x : Word) :
    Pure.eval .smod (fun i => if i = 0 then x else word 0) = word 0 := rfl

theorem addmod_zero (x y : Word) :
    Pure.eval .addmod (fun i => if i = 0 then x else if i = 1 then y else word 0) = word 0 := rfl

theorem mulmod_zero (x y : Word) :
    Pure.eval .mulmod (fun i => if i = 0 then x else if i = 1 then y else word 0) = word 0 := rfl

theorem byte_large (k x : Word) (hk : 32 ≤ k.val) :
    Pure.eval .byte (fun i => if i = 0 then k else x) = word 0 := by
  change (if k.val ≥ 32 then word 0 else _) = word 0
  exact if_pos hk

theorem shl_large (k x : Word) (hk : 256 ≤ k.val) :
    Pure.eval .shl (fun i => if i = 0 then k else x) = word 0 := by
  change (if k.val ≥ 256 then word 0 else _) = word 0
  exact if_pos hk

theorem shr_large (k x : Word) (hk : 256 ≤ k.val) :
    Pure.eval .shr (fun i => if i = 0 then k else x) = word 0 := by
  change (if k.val ≥ 256 then word 0 else _) = word 0
  exact if_pos hk

theorem signextend_large (k x : Word) (hk : 31 ≤ k.val) :
    Pure.eval .signextend (fun i => if i = 0 then k else x) = x := by
  change (if k.val ≥ 31 then x else _) = x
  exact if_pos hk

theorem clz_zero : Pure.eval .clz (fun _ => word 0) = word 256 := rfl

end Solidity.Yul
