import Solidity.Backend.Transient.WordSource

/-! Non-bool typed Source words, signed extension, byte-sensitive values and
reference refusal. These use the existing Source Val.word encoder unchanged. -/
namespace Solidity.Backend.Transient.WordControls
open Solidity.Backend.Transient

def declaration (name : String) (signed : Bool) (bits : Nat)
    (valid : bits%8=0 ∧ 8≤bits ∧ bits≤256) : Source.Decl :=
  {kind:=.stateVar,name:=name,scope:=some "P7Word",top:=false,
    node:=.stateVar (.elem (.int signed bits valid)) none none none true name .none}
def env : Source.Env := ⟨[declaration "unsigned" false 256 (by decide),
  declaration "signed" true 8 (by decide)]⟩
def uintPath : Source.SPath := ⟨⟨some "P7Word","unsigned"⟩,[]⟩
def signedPath : Source.SPath := ⟨⟨some "P7Word","signed"⟩,[]⟩
def signedTy : Source.IntTy := ⟨true,8,by decide⟩
def unsigned : Source.Val env.layout (.int .u256) := .int (2^248+0xfe) (by decide +kernel)
def signed : Source.Val env.layout (.int signedTy) := .int (-2) (by decide)
def unsignedWord : Word := ⟨2^248+0xfe,by decide⟩
def signedWord : Word := ⟨2^256-2,by decide⟩
def source : Source.EMState env [.bool] :=
  ⟨.cons (.bool true) .nil,
   ⟨⟨⟨fun _ => Source.Account.empty _⟩,Source.Transient.empty,[]⟩,
    (Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [0xa1,0xfe]⟩).1,
    [.call Controls.other ⟨3,by decide⟩ [0x42] false],[(Controls.owner,[0x99])],
    ⟨[.bool],.cons (.bool false) .nil⟩⟩⟩

theorem unsigned_encoding : unsigned.word=some unsignedWord := by decide +kernel

theorem signed_encoding : signed.word=some signedWord := by decide

theorem unsigned_actual :
    (Source.writeAt Controls.frame uintPath unsigned).run source=
      (.ok (),(source.1,wordSourceWrite uintPath rfl Controls.owner unsigned source.2)) ∧
    run Controls.owner false (storeCode ⟨0x40,by decide⟩ unsignedWord) Controls.target=
      .ok (write Controls.target Controls.owner ⟨0x40,by decide⟩ unsignedWord) ∧
    WordRepresents uintPath rfl ⟨0x40,by decide⟩ Controls.owner
      (source.1,wordSourceWrite uintPath rfl Controls.owner unsigned source.2)
      (write Controls.target Controls.owner ⟨0x40,by decide⟩ unsignedWord) :=
  word_compiled_write uintPath rfl rfl Controls.frame rfl _ unsigned unsignedWord unsigned_encoding source Controls.target

theorem signed_actual :
    (Source.writeAt Controls.frame signedPath signed).run source=
      (.ok (),(source.1,wordSourceWrite signedPath rfl Controls.owner signed source.2)) ∧
    run Controls.owner false (storeCode ⟨0x41,by decide⟩ signedWord) Controls.target=
      .ok (write Controls.target Controls.owner ⟨0x41,by decide⟩ signedWord) ∧
    WordRepresents signedPath rfl ⟨0x41,by decide⟩ Controls.owner
      (source.1,wordSourceWrite signedPath rfl Controls.owner signed source.2)
      (write Controls.target Controls.owner ⟨0x41,by decide⟩ signedWord) :=
  word_compiled_write signedPath rfl rfl Controls.frame rfl _ signed signedWord signed_encoding source Controls.target

theorem byte_sensitive : unsignedWord.val/2^248=1 ∧ unsignedWord.val%256=0xfe ∧
    signedWord.val/2^248=0xff ∧ signedWord.val%256=0xfe := by decide

theorem reference_refused :
    (Source.Val.memRef rfl 0 : Source.Val env.layout (.bytes .memory)).word=none := rfl

theorem unsigned_not_signed : unsignedWord≠signedWord := by decide

theorem unsigned_reset :
    WordRepresents uintPath rfl ⟨0x40,by decide⟩ Controls.owner
      (source.1,{source.2 with ex:=source.2.ex.endTx}) (endTx Controls.target) :=
  word_end_represents uintPath rfl _ _ source Controls.target
    (.int (t:=.u256) 0 Source.IntTy.u256.zero_mem) rfl rfl

theorem signed_reset :
    WordRepresents signedPath rfl ⟨0x41,by decide⟩ Controls.owner
      (source.1,{source.2 with ex:=source.2.ex.endTx}) (endTx Controls.target) :=
  word_end_represents signedPath rfl _ _ source Controls.target
    (.int (t:=signedTy) 0 signedTy.zero_mem) rfl rfl

end Solidity.Backend.Transient.WordControls
