import Solidity.Semantics.Panic.Run.Receivers
import Solidity.Semantics.Panic.Run.Data

namespace Solidity.Semantics.Panic.Run

variable {C : Contract}

mutual

/-- The compiled typed run of a statement. -/
def stmt : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Step C Γ Γ'
  | _, _, .assign l r => assign l r
  | _, _, .rebind i r => rebind i r
  | _, _, .assignLocal i r => assignLocal i r
  | _, _, .declLocal p _ init => declLocal p init
  | _, _, .declStorage R _ init => declStorage R init
  | _, _, .opAssign op _ hp l r => opAssign op hp l r
  | _, _, .incDec op hp l => incDec op hp l
  | _, _, .pushOpAssign op _ hp b r => pushOpAssign op hp b r
  | _, _, .pushIncDec op hp b => pushIncDec op hp b
  | _, _, .assignIncDec i op hp l _ => assignIncDec i op hp l
  | _, _, .assignLocalPush i b => assignLocalPush i b
  | _, _, .push b v _ => push b v
  | _, _, .pop b => pop b
  | _, _, .transfer r a => transfer r a
  | _, _, .send pv r a _ => send pv r a
  | _, _, .declMem R _ init _ hm => declMem R init hm
  | _, _, .rebindMem i r => rebindMem i r
  | _, _, .assignFromMem l p => assignFromMem l p
  | _, _, .assignMem l r => assignMem l r
  | _, _, .delete l => delete l
  | _, _, .deleteMem p _ => deleteMem p
  | _, _, .assignNew l n h => assignNew l n h
  | _, _, .ite c thn els => ite c thn.ext (program thn) els.ext (program els)
  | _, _, .require c => require c
  | _, _, .assert c => assert c
  | _, _, .revert => fun _ => .error .revert
  | _, _, .assumeFalse => fun _ => .error .exhausted
  | _, _, .call _ args ret body => call args ret body.ext (program body)
  | _, _, .callReceiver _ args r body op => callReceiver args r body.ext (program body) op
  | _, _, .callReceiverPush _ args r body code value =>
    callReceiverPush args r body.ext (program body) code.ext (program code) value
  | _, _, .tryCall call rets ok err code pnc other sargs sbody self =>
    tryCall call rets ok.ext (program ok) err.ext (program err) code pnc.ext
      (program pnc) other.ext (program other) sargs sbody.ext (program sbody) self
  | _, _, .loop _ c body => loop c body.ext (program body)
  | _, _, .block body => block body.ext (program body)
  | _, _, .callRec _ _ args ret body => call args ret (body ()).ext (program (body ()))
  | _, _, .revertData d => revertData d
  | _, _, .catchData c rets sargs sbody self kind _ body =>
    catchData c rets sargs sbody.ext (program sbody) self kind body.ext (program body)

/-- The compiled typed run of a sequence. -/
def program : {Γ Γ' : Ctx} → Prog C Γ Γ' → Step C Γ Γ'
  | _, _, .nil => nil
  | _, _, .cons s P => seq (stmt s) (program P)

end

end Solidity.Semantics.Panic.Run
