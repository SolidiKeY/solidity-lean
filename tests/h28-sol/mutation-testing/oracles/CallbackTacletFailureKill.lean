import Solidity.Calculus.CallbackRules
import Solidity.Calculus.PremiseSound
import Solidity.Calculus.CallbackHolds

/-! The checked kill for the separate callback table (solkey's `sendWithCallbackBox`):
the same inhabited refusal state, premise and frames as the shared-table
callback oracle, but `source_link` names `CallbackTaclet.sendWithCallbackBox`,
so it is attributed to `Calculus/CallbackRules.lean`, not to `Taclet`. -/

namespace H28.CallbackTacletFailureKill
open Solidity

def C : Contract := { vars := [] }
abbrev Γ : Ctx := [.val .uint, .val .bool]
def flag : Idx Γ (.val .bool) := .there .here
def start : State C Γ := { ((State.init C).push (t := .val .bool) true).push (t := .val .uint) ⟨13, rfl⟩ with selfBalance := ⟨10, rfl⟩ }
def refusing : State C Γ := { start with tx := { ext := [(sendKey ⟨9, rfl⟩ ⟨5, rfl⟩, .other [])] } }
def statement : Stmt C Γ Γ := .send flag (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) false
def paid : State C Γ := (start.pay ⟨9, rfl⟩ 5).setLocal flag (true : Bool)
def failed : State C Γ := start.setLocal flag (false : Bool)
def resumed : State C Γ := ((start.pay ⟨9, rfl⟩ 5).havoc start.storage [(⟨9, rfl⟩, -77)] ⟨42, rfl⟩).setLocal flag (true : Bool)
def J : StateInv C := (Fml.tt : Fml C []).stateInv true
def frame : Frames C Γ [.val .bool] := .pop .capture (.push .refl) .nil
def dropUpdate : Upd C Γ [.val .bool] := .pop .nil (.push .refl)
def post : Fml C [.val .bool] := .eq (.pvV .here) (Tm.lit (p := .bool) true)
def postFlag : Fml C Γ := .eq (.pvV flag) (Tm.lit (p := .bool) true)
def first : Upd C Γ Γ := (Upd.nil.snoc (UpdElem.payTo (.lit 9 rfl) (.lit 5 rfl))).snoc (.local flag (.val (Tm.lit (p := .bool) true)))
def second : Upd C Γ Γ := .snoc .nil (.local flag (.val (Tm.lit (p := .bool) true)))
def premise : Premise C Γ Γ := .cases [] [first, second]

theorem source_link : CallbackTaclet C 0 .box statement premise := .sendWithCallbackBox (pv := flag) (sadr := .lit 9 rfl) (se := .lit 5 rfl)

theorem input_inhabited : Nonempty (State C Γ) := ⟨start⟩
theorem accepted_run : statement.runR start = .ok ⟨paid, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem refused_run : statement.runR refusing = .ok ⟨refusing.setLocal flag (false : Bool), List.prefix_refl _⟩ := by with_unfolding_all rfl

theorem callback_failed : ExecS J start statement (.ok ⟨failed, List.prefix_refl _⟩) := by
  exact ExecS.sendFailed (o₁ := ⟨start.pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩) rfl rfl

theorem callback_resumed : ExecS J start statement (.ok ⟨resumed, List.prefix_refl _⟩) := by
  exact ExecS.sendResume (J := J) (σ := start) (pv := flag) (r := .simple (.lit 9 rfl)) (a := .simple (.lit 5 rfl)) (full := false) (o₁ := ⟨start.pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩)
    (st := start.storage) (nt := [(⟨9, rfl⟩, -77)]) (sb := ⟨42, rfl⟩) rfl rfl trivial trivial

theorem callback_local_global_controls : resumed.env.1.1 = 13 ∧ resumed.env.2.1 = true ∧
    resumed.net = [(⟨9, rfl⟩, -77)] ∧ resumed.selfBalance.1 = 42 ∧
    failed.env.1.1 = 13 ∧ failed.env.2.1 = false ∧ failed.net = start.net ∧
    failed.selfBalance = start.selfBalance := by exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem failed_frame : ExecF J failed frame (.ok ⟨failed.drop (.push .refl), List.prefix_refl _⟩) := .pop .nil
theorem resumed_frame : ExecF J resumed frame (.ok ⟨resumed.drop (.push .refl), List.prefix_refl _⟩) := .pop .nil

theorem frame_preserves_flag : ∀ τ : State C Γ, ∀ o : COut C τ.H [.val .bool], ExecF J τ frame o →
    o.after .box (fun ζ : State C [.val .bool] => ζ.env.1 = τ.env.2.1) := by
  intro τ
  apply (ExecF.forall_iff (J := J) (σ := τ) (κ := frame) rfl
    (fun o => o.after .box (fun ζ : State C [.val .bool] => ζ.env.1 = τ.env.2.1))).2
  rfl

theorem drop_typed_landing (τ : State C Γ) : dropUpdate.Lands τ τ.globG (τ.drop (.push .refl)) := Upd.lands_pop_nil (.push .refl) τ

theorem callback_frames_rejects : ¬ holdsC .tt true start
    (.modal .box (.cons statement .nil) frame post) := by
  intro h
  have hp : ExecP J start (.cons statement .nil) (.ok ⟨failed, List.prefix_refl _⟩) := .cons callback_failed .nil
  have bad : some false = some true := (h _ hp) _ failed_frame
  cases bad

def mutantPaid : State C Γ := (refusing.pay ⟨9, rfl⟩ 5).setLocal flag (true : Bool)
def mutantFailed : State C Γ := refusing.setLocal flag (true : Bool)

theorem first_typed_landing : first.Lands refusing mutantPaid.globG mutantPaid := by
  apply Upd.lands_iff_applyV.mpr
  refine ⟨refusing.locV.set flag (true : Bool), ?_, ?_, ?_⟩
  · with_unfolding_all rfl
  · rfl
  · intro t i
    cases i with
    | here => rfl
    | there i => cases i with
      | here => rfl
      | there i => nomatch i

theorem second_typed_landing : second.Lands refusing mutantFailed.globG mutantFailed := by
  apply Upd.lands_iff_applyV.mpr
  refine ⟨refusing.locV.set flag (true : Bool), ?_, ?_, ?_⟩
  · with_unfolding_all rfl
  · rfl
  · intro t i
    cases i with
    | here => rfl
    | there i => cases i with
      | here => rfl
      | there i => nomatch i

def startPaid : State C Γ := (start.pay ⟨9, rfl⟩ 5).setLocal flag (true : Bool)
def startFailed : State C Γ := start.setLocal flag (true : Bool)

theorem first_start_landing : first.Lands start startPaid.globG startPaid := by
  apply Upd.lands_iff_applyV.mpr
  refine ⟨start.locV.set flag (true : Bool), ?_, ?_, ?_⟩
  · with_unfolding_all rfl
  · rfl
  · intro t i
    cases i with
    | here => rfl
    | there i => cases i with
      | here => rfl
      | there i => nomatch i

theorem second_start_landing : second.Lands start startFailed.globG startFailed := by
  apply Upd.lands_iff_applyV.mpr
  refine ⟨start.locV.set flag (true : Bool), ?_, ?_, ?_⟩
  · with_unfolding_all rfl
  · rfl
  · intro t i
    cases i with
    | here => rfl
    | there i => cases i with
      | here => rfl
      | there i => nomatch i

theorem first_post : first.afterT .box refusing (fun τ => holds τ postFlag) := by
  rw [Upd.afterT_applyV]
  intro τ _hg hl
  change some (τ.getV flag) = some true
  rw [hl flag]
  rfl

theorem second_post : second.afterT .box refusing (fun τ => holds τ postFlag) := by
  rw [Upd.afterT_applyV]
  intro τ _hg hl
  change some (τ.getV flag) = some true
  rw [hl flag]
  rfl

theorem premise_accepts_post : holds refusing (premise.fml .box .nil .nil postFlag) := ⟨first_post, second_post⟩

theorem real_frames : Prog.runFrames refusing (.cons statement .nil) .nil = .ok (refusing.setLocal flag (false : Bool)) := by with_unfolding_all rfl

theorem execution_rejects_post : ¬ holds refusing (.modal .box (.cons statement .nil) .nil postFlag) := by
  change ¬ Modality.afterRunTR .box (fun τ => holds τ postFlag) (Prog.runFrames refusing (.cons statement .nil) .nil)
  rw [real_frames]
  intro h
  have bad : some false = some true := h.1
  cases bad

theorem checked_kill : ¬ Premise.Sound .box statement premise refusing := by
  intro h
  exact execution_rejects_post (h .nil .nil postFlag premise_accepts_post)

theorem frame_post_of_true (τ : State C Γ) (ht : τ.getV flag = true) :
    holdsC .tt true τ (Fml.modalK .box .nil frame post) := by
  change dropUpdate.afterT .box τ (fun ζ => holdsC .tt true ζ post)
  rw [Upd.afterT_applyV]
  intro ζ _hg hl
  change some (ζ.getV .here) = some true
  rw [hl .here]
  exact congrArg some ht

theorem callback_premise_accepts_frames : holdsC .tt true start (premise.fml .box .nil frame post) := by
  change first.afterT .box start (fun τ => holdsC .tt true τ (Fml.modalK .box .nil frame post)) ∧
    second.afterT .box start (fun τ => holdsC .tt true τ (Fml.modalK .box .nil frame post))
  constructor
  all_goals
    rw [Upd.afterT_applyV]
    intro τ _hg hl
    apply frame_post_of_true
    exact hl flag

theorem checked_callback_frames : ¬ (holdsC .tt true start (premise.fml .box .nil frame post) →
    holdsC .tt true start (.modal .box (.cons statement .nil) frame post)) := by
  intro h
  exact callback_frames_rejects (h callback_premise_accepts_frames)

#print axioms source_link
#print axioms input_inhabited
#print axioms accepted_run
#print axioms refused_run
#print axioms callback_failed
#print axioms callback_resumed
#print axioms callback_local_global_controls
#print axioms failed_frame
#print axioms resumed_frame
#print axioms frame_preserves_flag
#print axioms drop_typed_landing
#print axioms callback_frames_rejects
#print axioms first_typed_landing
#print axioms second_typed_landing
#print axioms first_start_landing
#print axioms second_start_landing
#print axioms first_post
#print axioms second_post
#print axioms premise_accepts_post
#print axioms real_frames
#print axioms execution_rejects_post
#print axioms checked_kill
#print axioms frame_post_of_true
#print axioms callback_premise_accepts_frames
#print axioms checked_callback_frames
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @accepted_run
#check @refused_run
#check @callback_failed
#check @callback_resumed
#check @callback_local_global_controls
#check @failed_frame
#check @resumed_frame
#check @frame_preserves_flag
#check @drop_typed_landing
#check @callback_frames_rejects
#check @first_typed_landing
#check @second_typed_landing
#check @first_start_landing
#check @second_start_landing
#check @first_post
#check @second_post
#check @premise_accepts_post
#check @real_frames
#check @execution_rejects_post
#check @checked_kill
#check @frame_post_of_true
#check @callback_premise_accepts_frames
#check @checked_callback_frames
end H28.CallbackTacletFailureKill
