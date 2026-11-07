import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound
import Solidity.Calculus.CallbackHolds

namespace H28.FrameReturnKill
open Solidity

def C : Contract := { vars := [] }
abbrev pairCtx : Ctx := [.val .uint, .val .bool]
def args : Args C [] pairCtx := .snoc (.snoc .nil .bool (.user (String.singleton 'b')) (.simple (.bool false))) .uint (.user (String.singleton 'a')) (.simple (.lit 3 rfl))
def rets : RetBinders pairCtx := .snoc (.snoc .nil .bool (.user (String.singleton 's'))) .uint (.user (String.singleton 'r'))
def body : Prog C (pairCtx ++ pairCtx) (pairCtx ++ pairCtx) := .cons (.assignLocal .here (.simple (.lit 42 rfl))) (.cons (.assignLocal (.there .here) (.simple (.bool true))) .nil)
def statement : Stmt C [] pairCtx := .call (String.singleton 'f') args (.rets rets) body
def expanded : Prog C [] (pairCtx ++ pairCtx) := args.declsThen (rets.declsThen (.cons (.block (body.wk (Thin.keepAll pairCtx (Thin.atop pairCtx []))).2.2) .nil))
def good : Thin pairCtx (pairCtx ++ pairCtx) := .keep (.keep (.drop (.drop .refl)))
def bad : Thin pairCtx (pairCtx ++ pairCtx) := .drop (.drop .refl)
def start : State C [] := { State.init C with selfBalance := ⟨10, rfl⟩ }
def returned : State C pairCtx := (start.push (t := .val .bool) true).push (t := .val .uint) ⟨42, rfl⟩
def parameters : State C pairCtx := (start.push (t := .val .bool) false).push (t := .val .uint) ⟨3, rfl⟩
def wide : State C (pairCtx ++ pairCtx) := ((parameters.push (t := .val .bool) true).push (t := .val .uint) ⟨42, rfl⟩)
def premise : Premise C [] pairCtx := .inline expanded bad

theorem source_link : Taclet C 0 .box statement premise := .functionBodyExpand (args := args) (ret := .rets rets) (body := body) (hexp := rfl) (hrets := rfl)

theorem input_inhabited : Nonempty (State C []) := ⟨start⟩
theorem callee_returns : statement.runR start = .ok ⟨returned, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem expanded_landing : Prog.run start expanded = .ok ⟨wide, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem correct_projection : wide.thin good = returned := by rfl
theorem wrong_projection : wide.thin bad = parameters := by rfl
theorem distinguishing_values : returned.env.1.1 = 42 ∧ returned.env.2.1 = true ∧ parameters.env.1.1 = 3 ∧ parameters.env.2.1 = false := ⟨rfl, rfl, rfl, rfl⟩

def post : Fml C pairCtx := .eq (.pvV .here) (Tm.lit (p := .uint) ⟨3, rfl⟩)
theorem premise_frames : Prog.runFrames start expanded (.drop bad (.seq .nil .nil)) = .ok parameters := by with_unfolding_all rfl
theorem actual_frames : Prog.runFrames start (.cons statement .nil) .nil = .ok returned := by with_unfolding_all rfl
theorem premise_accepts_post : holds start (premise.fml .box .nil .nil post) := by
  change Modality.afterRunTR .box (fun τ => holds τ post) (Prog.runFrames start expanded (.drop bad (.seq .nil .nil)))
  rw [premise_frames]
  exact ⟨rfl, nofun⟩
theorem execution_rejects_post : ¬ holds start (.modal .box (.cons statement .nil) .nil post) := by
  change ¬ Modality.afterRunTR .box (fun τ => holds τ post) (Prog.runFrames start (.cons statement .nil) .nil)
  rw [actual_frames]
  intro h
  have wrong : some (⟨42, rfl⟩ : PrimTy.uint.Denote) = some ⟨3, rfl⟩ := h.1
  have impossible : (42 : Int) = 3 := congrArg Subtype.val (Option.some.inj wrong)
  contradiction

theorem checked_kill : ¬ Premise.Sound .box statement premise start := by
  intro h
  exact execution_rejects_post (h .nil .nil post premise_accepts_post)

def J : StateInv C := (Fml.tt : Fml C []).stateInv true
def send : Stmt C pairCtx pairCtx := .send (.there .here) (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) false
def pending : Frames C pairCtx pairCtx := .seq (.cons send .nil) .nil
def resumed : State C pairCtx := ((returned.pay ⟨9, rfl⟩ 5).havoc returned.storage [(⟨9, rfl⟩, -77)] ⟨42, rfl⟩).setLocal (.there .here) (true : Bool)

theorem callback_preserves_number {o : COut C parameters.H pairCtx} (h : ExecS J parameters send o) :
    o.after .box (fun τ => holds τ post) := by
  change ExecS J parameters (.send (.there .here) (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) false) o at h
  cases h with
  | det hf =>
      have bad : true = false := hf
      cases bad
  | sendHalt _ hr =>
      have run : TRun.send (.there .here) (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) parameters = .ok ⟨(parameters.pay ⟨9, rfl⟩ 5).setLocal (.there .here) (true : Bool), List.prefix_refl _⟩ := by with_unfolding_all rfl
      rw [run] at hr
      cases hr
  | sendFailed => rfl
  | sendRefused => rfl
  | sendViolated _ _ hi => exact (hi trivial).elim
  | sendResume _ hr _ _ =>
      have run : TRun.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl)) parameters = .ok ⟨parameters.pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩ := by with_unfolding_all rfl
      rw [run] at hr
      cases hr
      rfl

theorem callback_program_preserves {o : COut C parameters.H pairCtx} (h : ExecP J parameters (.cons send .nil) o) :
    o.after .box (fun τ => holds τ post) := by
  cases h with
  | cons hs hn =>
      cases hn
      exact callback_preserves_number hs
  | halt hs => exact callback_preserves_number hs
  | violated hs => exact callback_preserves_number hs

theorem pending_preserves_number {o : COut C parameters.H pairCtx} (h : ExecF J parameters pending o) :
    o.after .box (fun τ => holds τ post) := by
  change ExecF J parameters (.seq (.cons send .nil) .nil) o at h
  cases h with
  | seq hp hf =>
      cases hf
      exact callback_program_preserves hp
  | seqHalt hp => exact callback_program_preserves hp
  | seqViolated hp => exact callback_program_preserves hp

theorem after_cat {H : HTy} {Δ Θ : Ctx} (a : Out C H Δ) (o : COut C a.st.H Θ) (p : State C Θ → Prop) :
    (o.map (Out.cat a)).after .box p ↔ o.after .box p := by cases o <;> rfl

theorem callback_premise_accepts : holdsC .tt true start (premise.fml .box .nil pending post) := by
  change ∀ o, ExecP J start expanded o → o.thenF J (.drop bad (.seq .nil pending)) .box (fun τ => holdsC .tt true τ post)
  apply (ExecP.forall_iff (J := J) (σ := start) (P := expanded) rfl
    (fun o => o.thenF J (.drop bad (.seq .nil pending)) .box (fun τ => holdsC .tt true τ post))).2
  change ∀ o, ExecF J wide (.drop bad (.seq .nil pending)) o → o.after .box (fun τ => holds τ post)
  intro o h
  cases h with
  | drop h =>
      cases h with
      | seq hp hf =>
          cases hp
          rw [after_cat]
          exact pending_preserves_number hf
      | seqHalt hp => cases hp
      | seqViolated hp => cases hp

theorem callback_resumes : ExecS J returned send (.ok ⟨resumed, List.prefix_refl _⟩) := by
  exact ExecS.sendResume (J := J) (σ := returned) (pv := .there .here) (r := .simple (.lit 9 rfl)) (a := .simple (.lit 5 rfl)) (full := false) (o₁ := ⟨returned.pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩)
    (st := returned.storage) (nt := [(⟨9, rfl⟩, -77)]) (sb := ⟨42, rfl⟩) rfl rfl trivial trivial

theorem callback_effect_controls : resumed.env.1.1 = 42 ∧ resumed.env.2.1 = true ∧ resumed.net = [(⟨9, rfl⟩, -77)] ∧ resumed.selfBalance.1 = 42 := ⟨rfl, rfl, rfl, rfl⟩

theorem real_callback_frame : ExecF J returned pending (.ok ⟨resumed, List.prefix_refl _⟩) := .seq (.cons callback_resumes .nil) .nil

theorem callback_execution_rejects : ¬ holdsC .tt true start (.modal .box (.cons statement .nil) pending post) := by
  intro h
  have hp : ExecP J start (.cons statement .nil) (.ok ⟨returned, List.prefix_refl _⟩) := ExecP.of_run (J := J) (by with_unfolding_all rfl)
  have wrong : some (⟨42, rfl⟩ : PrimTy.uint.Denote) = some ⟨3, rfl⟩ := (h _ hp) _ real_callback_frame
  have impossible : (42 : Int) = 3 := congrArg Subtype.val (Option.some.inj wrong)
  contradiction

theorem checked_callback_frames : ¬ (holdsC .tt true start (premise.fml .box .nil pending post) →
    holdsC .tt true start (.modal .box (.cons statement .nil) pending post)) := by
  intro h
  exact callback_execution_rejects (h callback_premise_accepts)

def sameWide : State C (pairCtx ++ pairCtx) := (parameters.push (t := .val .bool) false).push (t := .val .uint) ⟨3, rfl⟩
theorem same_payload_control : sameWide.thin good = parameters ∧ sameWide.thin bad = parameters := ⟨rfl, rfl⟩

theorem good_frame_projects (τ : State C (pairCtx ++ pairCtx)) :
    ∀ o, ExecF ((Fml.tt : Fml C []).stateInv true) τ (.drop good .nil) o →
      o.after .box (fun ζ : State C pairCtx => ζ.env.1 = τ.env.1 ∧ ζ.env.2.1 = τ.env.2.1) := by
  apply (ExecF.forall_iff (J := (Fml.tt : Fml C []).stateInv true) (σ := τ) (κ := .drop good .nil) rfl
    (fun o => o.after .box (fun ζ : State C pairCtx => ζ.env.1 = τ.env.1 ∧ ζ.env.2.1 = τ.env.2.1))).2
  exact ⟨rfl, rfl⟩

theorem bad_frame_projects (τ : State C (pairCtx ++ pairCtx)) :
    ∀ o, ExecF ((Fml.tt : Fml C []).stateInv true) τ (.drop bad .nil) o →
      o.after .box (fun ζ : State C pairCtx => ζ.env.1 = τ.env.2.2.1 ∧ ζ.env.2.1 = τ.env.2.2.2.1) := by
  apply (ExecF.forall_iff (J := (Fml.tt : Fml C []).stateInv true) (σ := τ) (κ := .drop bad .nil) rfl
    (fun o => o.after .box (fun ζ : State C pairCtx => ζ.env.1 = τ.env.2.2.1 ∧ ζ.env.2.1 = τ.env.2.2.2.1))).2
  exact ⟨rfl, rfl⟩

#print axioms source_link
#print axioms input_inhabited
#print axioms callee_returns
#print axioms expanded_landing
#print axioms correct_projection
#print axioms wrong_projection
#print axioms distinguishing_values
#print axioms premise_frames
#print axioms actual_frames
#print axioms premise_accepts_post
#print axioms execution_rejects_post
#print axioms checked_kill
#print axioms callback_preserves_number
#print axioms callback_program_preserves
#print axioms pending_preserves_number
#print axioms after_cat
#print axioms callback_premise_accepts
#print axioms callback_resumes
#print axioms callback_effect_controls
#print axioms real_callback_frame
#print axioms callback_execution_rejects
#print axioms checked_callback_frames
#print axioms same_payload_control
#print axioms good_frame_projects
#print axioms bad_frame_projects
set_option pp.fullNames true
#check @source_link
#check @input_inhabited
#check @callee_returns
#check @expanded_landing
#check @correct_projection
#check @wrong_projection
#check @distinguishing_values
#check @premise_frames
#check @actual_frames
#check @premise_accepts_post
#check @execution_rejects_post
#check @checked_kill
#check @callback_preserves_number
#check @callback_program_preserves
#check @pending_preserves_number
#check @after_cat
#check @callback_premise_accepts
#check @callback_resumes
#check @callback_effect_controls
#check @real_callback_frame
#check @callback_execution_rejects
#check @checked_callback_frames
#check @same_payload_control
#check @good_frame_projects
#check @bad_frame_projects
end H28.FrameReturnKill
