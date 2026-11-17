import Solidity.Backend.Passes.ValueCertificate
import Solidity.Backend.InternalFlow.RuntimeFrameV3DisjointScalarEntry

/-! Checked primitive expressions with the same actual source value push the
same word on the SAME machine. This supplies genuine argument-prefix sharing
without assuming an endpoint or reducing a concrete whole caller state. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ArgumentAgreement
open Evm Evm.Memory

theorem common_value {C : Contract} {Γ : Ctx} {p : PrimTy} {L b frame : Nat} {F : Frag Γ}
 {x y : Val C Γ p} (left : CompiledVal b F x) (right : CompiledVal b F y)
 {caller : State C Γ} {base : Nat → Fin W} {before : Machine}
 (repr : StateRepr L b frame F caller base before) (value : p.Denote)
 (first : x.evalT caller=.ok value) (second : y.evalT caller=.ok value) :
 ∃ word, ReprV p value word ∧ run left.code before=.ok (before.push word) 0 ∧
   run right.code before=.ok (before.push word) 0 := by
 obtain ⟨wa,ra,xa⟩ := Passes.value_success_tail left repr first before.stack
 obtain ⟨wz,rz,xz⟩ := Passes.value_success_tail right repr second before.stack
 exact ⟨wa,ra,xa,(Restored.value_unique rz ra) ▸ xz⟩

theorem entry_suffix {C : Contract} {Γ : Ctx} {R : RefTy} {L b c frame : Nat} {F : Frag Γ}
 {x y : Val C Γ .uint} (left : CompiledVal b F x) (right : CompiledVal b F y)
 (reference : Idx Γ (.mem R)) {caller : State C Γ} {base : Nat → Fin W} {before : Machine}
 (repr : StateRepr L b frame F caller base before) (disjoint : b+Γ.length≤c) (space : c<frame)
 (value : PrimTy.uint.Denote) (first : x.evalT caller=.ok value) (second : y.evalT caller=.ok value)
 (suffix : List Instr) :
 run (DisjointScalarEntry.code b c reference left ++ suffix) before=
 run (DisjointScalarEntry.code b c reference right ++ suffix) before := by
 let middle := writeMachine before c (before.mem (cellOf b reference))
 obtain ⟨word,encoded,one,two⟩ := common_value left right (before:=middle) (reserved_write repr c disjoint space _) value first second
 have loaded : run [.mload (cellOf b reference),.mstore c] before=.ok middle 0 := rfl
 simp only [DisjointScalarEntry.code,List.append_assoc,run_append_ok loaded,run_append_ok one,run_append_ok two]

end Solidity.Backend.InternalFlow.RuntimeFrame.ArgumentAgreement
