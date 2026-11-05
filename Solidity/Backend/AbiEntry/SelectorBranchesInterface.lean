import Solidity.Backend.AbiEntry.SelectorGateBody

/-! Actual two-branch selector compilation with exact compiler join behavior.
The matched code retains its trailing skip over the miss branch: arbitrary
body outcomes/skips are not assumed to be normal returns. Generic join removal,
Source body/table association, short special routing and native loading remain
separate obligations. Neither selected body runs nor poststates are premises. -/
namespace Solidity.Backend.AbiEntry.Interface
structure SelectorBranchesCertificate
    (program : {C : Contract} → {Γ ΔT ΔF : Ctx} → Idx Γ (.val .uint) → Fin Evm.W →
      Prog C Γ ΔT → Prog C Γ ΔF → Prog C Γ Γ) : Prop where
  selected : ∀ {C : Contract} {Γ ΔT ΔF : Ctx} (base : Nat) (frag : Evm.Frag Γ)
    (index : Idx Γ (.val .uint)) (tag : Fin Evm.W) (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF)
    (yesFrag : Evm.Frag ΔT) (noFrag : Evm.Frag ΔF),
    Evm.inFragP frag yes=some yesFrag → Evm.inFragP frag no=some noFrag →
    ∃ (whole : Evm.Compiler.Compilation base frag (program index tag yes no))
      (left : Evm.Compiler.Compilation base frag yes) (right : Evm.Compiler.Compilation base frag no),
      Evm.Compiler.compile base frag (program index tag yes no)=some whole ∧
      Evm.Compiler.compile base frag yes=some left ∧ Evm.Compiler.compile base frag no=some right
  executed : ∀ {C : Contract} {Γ ΔT ΔF : Ctx} (base : Nat) (frag : Evm.Frag Γ)
    (index : Idx Γ (.val .uint)) (tag : Fin Evm.W) (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF)
    (yesFrag : Evm.Frag ΔT) (noFrag : Evm.Frag ΔF),
    Evm.inFragP frag yes=some yesFrag → Evm.inFragP frag no=some noFrag →
    ∀ (whole : Evm.Compiler.Compilation base frag (program index tag yes no))
      (left : Evm.Compiler.Compilation base frag yes) (right : Evm.Compiler.Compilation base frag no),
      Evm.Compiler.compile base frag (program index tag yes no)=some whole →
      Evm.Compiler.compile base frag yes=some left → Evm.Compiler.compile base frag no=some right →
      ∀ (machine : Evm.Machine) (selector : Fin Evm.W), machine.mem (Evm.cellOf base index)=.val selector →
      Evm.run whole.code machine=if tag.val=selector.val then
        Evm.run (left.code++[.jump right.code.length]++right.code) machine else Evm.run right.code machine
end Solidity.Backend.AbiEntry.Interface
