import Solidity.Backend.InternalDispatch.FrozenV3
import Solidity.Backend.InternalDispatch.FrozenV1Controls

/-! Inhabited typed selector controls and a frozen-V3 nonvacuity refusal.
The selector fixtures are Source-backed; they are not a fabricated physical
Source-to-intrinsic lowering or a family of P1 producers for those declarations. -/
namespace Solidity.Backend.InternalDispatch.FrozenV3Controls
open FrozenV1 FrozenV1Controls Controls

theorem first : select table (fun i => Fin (i.val+1)) token (Evm.wmod 1)=
 some ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩ := FrozenV1Controls.first

theorem second : select table (fun i => Fin (i.val+1)) token (Evm.wmod 2)=
 some ⟨⟨1,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩ := FrozenV1Controls.second

theorem wrong_payload : select table (fun i => Fin (i.val+1)) token (Evm.wmod 2)≠
 some ⟨⟨1,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩ := FrozenV1Controls.wrong_payload_refused

theorem zero : select table (fun i => Fin (i.val+1)) token (Evm.wmod 0)=none :=
 FrozenV1Controls.zero

theorem foreign : select table (fun i => Fin (i.val+1)) token (Evm.wmod 5)=none :=
 FrozenV1Controls.foreign

/-- An empty claimed admission cannot manufacture a V3 producer, regardless
of its proposed code or execution claims. -/
theorem empty_domain_refused {C : Contract} {Γ Δ ps rs Γf : Ctx}
 (b : Nat) (F : Evm.Frag Γ)
 (approved : Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV3.Admission C Γ)
 (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
 (body : Prog C (rs ++ ps) Γf) :
 ¬ Nonempty (Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV3.PendingCallProducer
  b F approved (fun _ _ _ _ _ _ => False) f args ret body) := by
 intro ⟨producer⟩
 obtain ⟨L,frame,caller,base,machine,start,out,member,entry,success⟩ :=
  producer.required_successful_entry
 exact member

end Solidity.Backend.InternalDispatch.FrozenV3Controls
