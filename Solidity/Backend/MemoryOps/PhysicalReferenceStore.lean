import Solidity.Backend.MemoryOps.PhysicalWordFrame

/-! G32/G34 existing-reference redirection across the published WORD and BYTE
store models. Word cells are mapped to byte offsets 32*c as in P6; hence a
pointer to logical base b must contain 32*b in the byte image, not b.
This proves actual typed heap/word-code/byte-store observations, not a new
pointer decoder or source compiler. Initial header/fit facts are explicit.
Children's typed identities/content are framed only at distinct object IDs;
physical child-byte framing additionally needs actual interval separation.
No constructors, copying, address injectivity or whole Source graph is supplied. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- Real existing typed reference writes retain identity, while the two actual
stores use their respective address units. Complete bytes are derived from the
existing serializer and actual byte MSTORE, not supplied as a postrelation. -/
theorem reference_store {H : HTy} {R : RefTy}
    (hp : Heap H) (root : HRef H (.array (.ref R))) (child : HRef H R)
    (base : Nat → Fin Evm.W) (m : Evm.Machine) (bytes : Environment.Memory)
    (i : Fin Evm.W) (hi : i.val<hp.len root .dyn)
    (header : m.mem (base root.id).val=.val (Evm.wmod (hp.len root .dyn)))
    (cellFits : 32*((base root.id).val+1+i.val)+32≤2^256)
    (childFits : 32*(base child.id).val<2^256) :
    let cell := (base root.id).val+1+i.val
    let byteNext := Environment.writeBytes bytes (32*cell)
      (Semantics.wordBytes (32*(base child.id).val))
    ∃ out : Heap H,
      hp.writeAddr (.index root .dyn (Evm.Memory.indexValue i)) child=some out ∧
      Evm.run (Evm.Memory.writeArrayCode (base root.id))
        ((m.push (.val (base child.id))).push (.val i))=
          .ok (Evm.Memory.writeMachine m cell (.val (base child.id))) 0 ∧
      (∃ offset : Fin Evm.W,offset.val=32*cell ∧ ∀ tail : List Environment.Word,
        Environment.cryptoStep (.op .MSTORE)
          ⟨lenU offset.val offset.isLt::lenU (32*(base child.id).val) childFits::tail,bytes⟩=
            some ⟨tail,byteNext⟩) ∧
      Environment.readMemory byteNext (32*cell) 32=Semantics.wordBytes (32*(base child.id).val) ∧
      (∀ k,k<32*cell ∨ 32*cell+32≤k → byteNext k=bytes k) ∧
      (∀ {Q : RefTy} (q : HRef H Q),root.id≠q.id → out.get q=hp.get q) := by
  dsimp only
  let cell := (base root.id).val+1+i.val
  let out := hp.set root (MObj.setElem .dyn (hp.get root) i.val child)
  have ht : hp.writeAddr (.index root .dyn (Evm.Memory.indexValue i)) child=some out := by
    change (if i.val<hp.len root .dyn then some out else none)=some out
    simp only [hi,↓reduceIte]
  have hc : cell<Evm.W := by change cell<2^256;dsimp only [cell];omega
  have address := Evm.Memory.arrayAddr_run (m.push (.val (base child.id))) (base root.id) i
    (hp.len root .dyn) (hp.len_dyn_lt root) header
  rw [if_pos hi] at address
  have hw : Evm.run (Evm.Memory.writeArrayCode (base root.id))
      ((m.push (.val (base child.id))).push (.val i))=
        .ok (Evm.Memory.writeMachine m cell (.val (base child.id))) 0 := by
    rw [Evm.Memory.writeArrayCode,Evm.run_append_ok address]
    have normalize : Evm.wmod ((base root.id).val+1+i.val)=(⟨cell,hc⟩ : Fin Evm.W) := Evm.wmod_of_lt hc
    rw [normalize]
    exact word_mstore m ⟨cell,hc⟩ (base child.id)
  have hb : Environment.readMemory (Environment.writeBytes bytes (32*cell)
      (Semantics.wordBytes (32*(base child.id).val))) (32*cell) 32=
        Semantics.wordBytes (32*(base child.id).val) := by
    simpa only [word_bytes_length] using Environment.read_written
      (Semantics.wordBytes (32*(base child.id).val)) (32*cell) bytes
  refine ⟨out,ht,hw,?_,hb,?_,?_⟩
  · refine ⟨⟨32*cell,by change 32*cell<2^256;dsimp only [cell];omega⟩,rfl,?_⟩
    intro tail
    exact byte_mstore bytes tail ⟨cell,hc⟩ ⟨32*(base child.id).val,childFits⟩ cellFits
  · intro k hk
    apply Environment.writeBytes_frame
    simpa only [word_bytes_length] using hk
  · intro Q q hne
    exact Heap.get_set_ne hp root q hne _

/-- info: 'Solidity.Backend.MemoryOps.Physical.reference_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reference_store
end Solidity.Backend.MemoryOps.Physical
