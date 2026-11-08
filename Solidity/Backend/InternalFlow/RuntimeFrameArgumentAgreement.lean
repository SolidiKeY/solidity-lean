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
 rcases left.cert.correct repr with ⟨a,wa,ea,ra,xa⟩ | ⟨failed,xa⟩
 · have av : a=value := Except.ok.inj (ea.symm.trans first)
   subst a
   rcases right.cert.correct repr with ⟨z,wz,ez,rz,xz⟩ | ⟨failed,xz⟩
   · have zv : z=value := Except.ok.inj (ez.symm.trans second)
     subst z
     have same := Restored.value_unique ra rz
     rw [←same] at xz
     exact ⟨wa,ra,xa,xz⟩
   · rw [second] at failed
     cases failed
 · rw [first] at failed
   cases failed

theorem entry_suffix {C : Contract} {Γ : Ctx} {R : RefTy} {L b c frame : Nat} {F : Frag Γ}
 {x y : Val C Γ .uint} (left : CompiledVal b F x) (right : CompiledVal b F y)
 (reference : Idx Γ (.mem R)) {caller : State C Γ} {base : Nat → Fin W} {before : Machine}
 (repr : StateRepr L b frame F caller base before) (disjoint : b+Γ.length≤c) (space : c<frame)
 (value : PrimTy.uint.Denote) (first : x.evalT caller=.ok value) (second : y.evalT caller=.ok value)
 (suffix : List Instr) :
 run (DisjointScalarEntry.code b c reference left ++ suffix) before=
 run (DisjointScalarEntry.code b c reference right ++ suffix) before := by
 let middle := writeMachine before c (before.mem (cellOf b reference))
 have reached : StateRepr L b frame F caller base middle := reserved_write repr c disjoint space _
 obtain ⟨word,encoded,one,two⟩ := common_value left right reached value first second
 have loaded : run [.mload (cellOf b reference),.mstore c] before=.ok middle 0 := rfl
 simp only [DisjointScalarEntry.code,List.append_assoc]
 simp only [run_append_ok loaded,run_append_ok one,run_append_ok two]

end Solidity.Backend.InternalFlow.RuntimeFrame.ArgumentAgreement
