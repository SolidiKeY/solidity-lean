import Solidity.Backend.AbiEntry.CoreJoin.Shared

/-! Actual short/full input branching at size four through the existing typed
compiler. Exact raw join behavior and represented core body outcomes are both
specified. Native calldata-size loading and Source declaration binding remain
separate obligations; no selected execution or poststate is a premise. -/
namespace Solidity.Backend.AbiEntry.Interface
structure SizeBranchesCertificate
    (program : {C : Contract} → {Γ ΔT ΔF : Ctx} → Idx Γ (.val .uint) →
      Prog C Γ ΔT → Prog C Γ ΔF → Prog C Γ Γ) : Prop where
  selected : ∀ {C : Contract} {Γ ΔT ΔF : Ctx} (base : Nat) (frag : Evm.Frag Γ)
    (index : Idx Γ (.val .uint)) (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF)
    (yesFrag : Evm.Frag ΔT) (noFrag : Evm.Frag ΔF),
    Evm.inFragP frag yes=some yesFrag → Evm.inFragP frag no=some noFrag →
    ∃ (whole : Evm.Compiler.Compilation base frag (program index yes no))
      (left : Evm.Compiler.Compilation base frag yes) (right : Evm.Compiler.Compilation base frag no),
      Evm.Compiler.compile base frag (program index yes no)=some whole ∧
      Evm.Compiler.compile base frag yes=some left ∧ Evm.Compiler.compile base frag no=some right
  executed : ∀ {C : Contract} {Γ ΔT ΔF : Ctx} (base : Nat) (frag : Evm.Frag Γ)
    (index : Idx Γ (.val .uint)) (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF)
    (yesFrag : Evm.Frag ΔT) (noFrag : Evm.Frag ΔF),
    Evm.inFragP frag yes=some yesFrag → Evm.inFragP frag no=some noFrag →
    ∀ (whole : Evm.Compiler.Compilation base frag (program index yes no))
      (left : Evm.Compiler.Compilation base frag yes) (right : Evm.Compiler.Compilation base frag no),
      Evm.Compiler.compile base frag (program index yes no)=some whole →
      Evm.Compiler.compile base frag yes=some left → Evm.Compiler.compile base frag no=some right →
      ∀ (machine : Evm.Machine) (size : Fin Evm.W), machine.mem (Evm.cellOf base index)=.val size →
      Evm.run whole.code machine=if size.val<4 then
        Evm.run (left.code++[.jump right.code.length]++right.code) machine else Evm.run right.code machine
  body_outcome : ∀ {C : Contract} {Γ ΔT ΔF : Ctx} (L base : Nat) (frag : Evm.Frag Γ)
    (index : Idx Γ (.val .uint)) (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF)
    (yesFrag : Evm.Frag ΔT) (noFrag : Evm.Frag ΔF)
    (_yesCore : Evm.inFragP frag yes=some yesFrag) (_noCore : Evm.inFragP frag no=some noFrag)
    (whole : Evm.Compiler.Compilation base frag (program index yes no))
    (left : Evm.Compiler.Compilation base frag yes) (right : Evm.Compiler.Compilation base frag no)
    (_wholeFound : Evm.Compiler.compile base frag (program index yes no)=some whole)
    (_leftFound : Evm.Compiler.compile base frag yes=some left) (_rightFound : Evm.Compiler.compile base frag no=some right)
    (state : State C Γ) (machine : Evm.Machine) (_represented : Evm.Sim C L base frag state machine)
    (_room : L+Evm.Prog.pushes yes≤Evm.Lmax) (size : Fin Evm.W) (_initial : machine.mem (Evm.cellOf base index)=.val size),
    Evm.run whole.code machine=if size.val<4 then Evm.run left.code machine else Evm.run right.code machine
end Solidity.Backend.AbiEntry.Interface
