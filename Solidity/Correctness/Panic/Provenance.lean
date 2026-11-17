import Solidity.Goals.PanicProvenance
import Solidity.Correctness.Panic.Provenance.Control
import Solidity.Correctness.Panic.Provenance.Updates

/-!
# Panic code provenance of the actual runner

Every failure of `Run.stmt` and `Run.program` is coded: an intrinsic halt
carries the code of the site its retained origin failed at
(`code_provenance`, the goal `Solidity.Goals.panicCodeProvenance`).

The leaves still missing are those of `Semantics/Panic/Run/Receivers.lean` and
`Semantics/Panic/Run/Data.lean`. One mutual induction over `Run.stmt` and
`Run.program` then applies one leaf per constructor to the induction hypotheses
of its sub-programs. An external revert payload is never an intrinsic halt:
`Coded` holds of it by constructor disjointness (`externalRevert_ne_intrinsic`),
whatever bytes it carries.
-/

namespace Solidity.Correctness.Panic

open Solidity.Semantics.Panic

open ErrCoded

variable {C : Contract} {Γ : Ctx}

namespace Run

/-! ## Receivers -/

theorem receiverOp_coded {E : Ty} (op : ReceiverOp C Γ E) (b : SPath C Γ (.array E)) :
    StepCoded (Run.receiverOp op b) := by
  cases op with
  | push v _ => exact push_coded b v
  | pop => exact pop_coded b

theorem callReceiver_coded {ps Γf : Ctx} {E : Ty} (args : Args C Γ ps) (r : Var)
    (h : Ext ([.alias (.array E)] ++ ps) Γf) {body : Step C ([.alias (.array E)] ++ ps) Γf}
    (op : ReceiverOp C Γ E) (hbody : StepCoded body) :
    StepCoded (Run.callReceiver args r h body op) := fun σ =>
  bind (call_coded args _ h hbody σ) fun _ => bind (receiverOp_coded _ _ _) fun _ => ok _

theorem pushAfterPrefix_coded {Γv : Ctx} {E : Ty} (h : Ext Γ Γv) {code : Step C Γ Γv}
    (value : Src C Γv E) (ref : SRef C (.ref (.array E))) (hcode : StepCoded code) :
    StepCoded (Run.pushAfterPrefix h code value ref) := fun σ =>
  bind (hcode σ) fun a => bind (source_coded a.st value) fun _ =>
    full_coded _ (bind (ofOpt _) fun _ => ok _)

theorem afterReceiverPrefix_coded {Γv : Ctx} {E : Ty} (he : Ext Γ Γv) {code : Step C Γ Γv}
    (value : Src C Γv E) (hcode : StepCoded code) :
    StepCoded (Run.afterReceiverPrefix he code value) := fun σ =>
  bind (path_coded σ _) fun _ => pushAfterPrefix_coded he value _ hcode _

theorem callReceiverPush_coded {ps Γf Γv : Ctx} {E : Ty} (args : Args C Γ ps) (r : Var)
    (hb : Ext ([.alias (.array E)] ++ ps) Γf) {body : Step C ([.alias (.array E)] ++ ps) Γf}
    (he : Ext Γ Γv) {code : Step C Γ Γv} (value : Src C Γv E)
    (hbody : StepCoded body) (hcode : StepCoded code) :
    StepCoded (Run.callReceiverPush args r hb body he code value) := fun σ =>
  bind (call_coded args _ hb hbody σ) fun _ =>
    map _ (afterReceiverPrefix_coded he value hcode _)

/-! ## Revert and catch data -/

theorem revPart_coded (σ : State C Γ) (p : RevPart C Γ) : ErrCoded (Run.revPart σ p) := by
  cases p with
  | bytes => exact ok _
  | sel => exact ok _
  | word v => exact bind (value_coded σ v) fun _ => ok _
  | mem => exact bind (mpath_coded σ _) fun _ => ok _

theorem revParts_coded (σ : State C Γ) (d : List (RevPart C Γ)) :
    ErrCoded (d.mapM (Run.revPart σ)) := by
  induction d with
  | nil => exact ok _
  | cons p d ih =>
    rw [List.mapM_cons]
    exact bind (revPart_coded σ p) fun _ => bind ih fun _ => ok _

/-- `revert(d)` ends with a plain or data revert, never an intrinsic halt of its own. -/
theorem revertData_coded (d : List (RevPart C Γ)) : StepCoded (Run.revertData d) := fun σ =>
  bind (revParts_coded σ d) fun bs => by
    cases bs.flatten with
    | nil => exact revert
    | cons => exact error _ fun _ _ e => nomatch e

theorem litWrites_coded {Γ₁ : Ctx} (bs : List UInt8) (i : Nat)
    {k : Step C (.mem bytesR :: Γ) Γ₁} (hk : StepCoded k) :
    StepCoded (Run.litWrites bs i k) := by
  induction bs generalizing i with
  | nil => exact hk
  | cons b bs ih =>
    unfold Run.litWrites
    split
    · exact seq_coded (assignMem_coded _ _) (ih _)
    · exact hk

theorem litBytes_coded {Γ₁ : Ctx} (bs : List UInt8) {k : Step C (.mem bytesR :: Γ) Γ₁}
    (hk : StepCoded k) : StepCoded (Run.litBytes bs k) := by
  unfold Run.litBytes
  split
  · exact seq_coded (declMem_coded _ _ _) (litWrites_coded bs 0 hk)
  · exact seq_coded (declMem_coded _ _ _) hk

/-- Catch data: the self-call's halt becomes bytes; what escapes is the clause's
outcome, a revert or a resource failure. -/
theorem catchData_coded {ρ ps Γf Γ₁ : Ctx} (c : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf) (self : Bool)
    (kind : CatchKind) (h₁ : Ext (.mem bytesR :: Γ) Γ₁) {body : Step C (.mem bytesR :: Γ) Γ₁}
    (hbody : StepCoded body) :
    StepCoded (Run.catchData c rets sargs hs sbody self kind h₁ body) := fun σ =>
  bind (catchBytes_coded c rets sargs hs sbody self σ) fun d => by
    cases kind.decode d with
    | none => exact revert
    | some bs => exact map _ (litBytes_coded bs hbody σ)

/-! ## The runner -/

mutual

/-- Every failure of a statement's run is coded. -/
theorem stmt_coded : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → StepCoded (Run.stmt s)
  | _, _, .assign l r => assign_coded l r
  | _, _, .rebind i r => rebind_coded i r
  | _, _, .assignLocal i r => assignLocal_coded i r
  | _, _, .declLocal p _ init => declLocal_coded p init
  | _, _, .declStorage R _ init => declStorage_coded R init
  | _, _, .opAssign op _ hp l r => opAssign_coded op hp l r
  | _, _, .incDec op hp l => incDec_coded op hp l
  | _, _, .pushOpAssign op _ hp b r => pushOpAssign_coded op hp b r
  | _, _, .pushIncDec op hp b => pushIncDec_coded op hp b
  | _, _, .assignIncDec i op hp l _ => assignIncDec_coded i op hp l
  | _, _, .assignLocalPush i b => assignLocalPush_coded i b
  | _, _, .push b v _ => push_coded b v
  | _, _, .pop b => pop_coded b
  | _, _, .transfer r a => transfer_coded r a
  | _, _, .send pv r a _ => send_coded pv r a
  | _, _, .declMem R _ init _ hm => declMem_coded R init hm
  | _, _, .rebindMem i r => rebindMem_coded i r
  | _, _, .assignFromMem l p => assignFromMem_coded l p
  | _, _, .assignMem l r => assignMem_coded l r
  | _, _, .delete l => delete_coded l
  | _, _, .deleteMem p _ => deleteMem_coded p
  | _, _, .assignNew l n h => assignNew_coded l n h
  | _, _, .ite c thn els => ite_coded c _ _ (program_coded thn) (program_coded els)
  | _, _, .require c => require_coded c
  | _, _, .assert c => assert_coded c
  | _, _, .revert => fun _ => revert
  | _, _, .assumeFalse => fun _ => exhausted
  | _, _, .call _ args ret body => call_coded args ret _ (program_coded body)
  | _, _, .callReceiver _ args r body op => callReceiver_coded args r _ op (program_coded body)
  | _, _, .callReceiverPush _ args r body code value =>
    callReceiverPush_coded args r _ _ value (program_coded body) (program_coded code)
  | _, _, .tryCall call rets ok err code pnc other sargs _ self =>
    tryCall_coded call rets _ _ code _ _ sargs _ _ self (program_coded ok)
      (program_coded err) (program_coded pnc) (program_coded other)
  | _, _, .loop _ c body => loop_coded c _ (program_coded body)
  | _, _, .block body => block_coded _ (program_coded body)
  | _, _, .callRec _ _ args ret body => call_coded args ret _ (program_coded (body ()))
  | _, _, .revertData d => revertData_coded d
  | _, _, .catchData c rets sargs _ self kind _ body =>
    catchData_coded c rets sargs _ _ self kind _ (program_coded body)

/-- Every failure of a sequence's run is coded. -/
theorem program_coded : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → StepCoded (Run.program P)
  | _, _, .nil => nil_coded
  | _, _, .cons s P => seq_coded (stmt_coded s) (program_coded P)

end

end Run

/-- An external revert payload is not an intrinsic halt, whatever its bytes
encode: no origin is built from it. -/
theorem externalRevert_ne_intrinsic (data : List UInt8) (code : Code) (origin : Raised) :
    (Halt.externalRevert data : Halt Raised) ≠ .intrinsic code origin :=
  fun e => nomatch e

/-- The nine solc codes are those of the retained sites. -/
theorem siteCode_codes : (siteCode .assertion).code = 0x01 ∧
    (siteCode .arithmetic).code = 0x11 ∧ (siteCode .zeroDivisor).code = 0x12 ∧
    (siteCode .enumConversion).code = 0x21 ∧ (siteCode .storageEncoding).code = 0x22 ∧
    (siteCode .emptyPop).code = 0x31 ∧ (siteCode .bounds).code = 0x32 ∧
    (siteCode .allocation).code = 0x41 ∧ (siteCode .zeroInternalFunction).code = 0x51 := by
  simp only [siteCode_code]
  exact Solidity.Panic.original_codes

/-- Code provenance of the actual runner: every intrinsic halt of a program or a
statement carries the code of the site its retained origin failed at. -/
theorem code_provenance : Solidity.Goals.panicCodeProvenance :=
  ⟨fun P σ _ _ e => (Run.program_coded P σ).intrinsic e,
   fun s σ _ _ e => (Run.stmt_coded s σ).intrinsic e⟩

end Solidity.Correctness.Panic
