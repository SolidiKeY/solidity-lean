import Solidity.Calculus.CallbackRules
import Solidity.Calculus.PremiseSound
import Solidity.Calculus.CallbackHolds

/-! The normal baseline for the separate callback table (solkey's `sendWithCallbackBox`):
the same inhabited refusal state, premise and frames as the shared-table
callback oracle, but `source_link` names `CallbackTaclet.sendWithCallbackBox`,
so it is attributed to `Calculus/CallbackRules.lean`, not to `Taclet`. -/

namespace H28.CallbackTacletBaseline
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
def second : Upd C Γ Γ := .snoc .nil (.local flag (.val (Tm.lit (p := .bool) false)))
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
end H28.CallbackTacletBaseline
