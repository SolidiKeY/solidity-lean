import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound
import Solidity.Calculus.CallbackHolds

namespace H28.FrameReturnBaseline
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
def premise : Premise C [] pairCtx := .inline expanded good

theorem source_link : Taclet C 0 .box statement premise := .functionBodyExpand (args := args) (ret := .rets rets) (body := body) (hexp := rfl) (hrets := rfl)

theorem input_inhabited : Nonempty (State C []) := ⟨start⟩
theorem callee_returns : statement.runR start = .ok ⟨returned, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem expanded_landing : Prog.run start expanded = .ok ⟨wide, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem correct_projection : wide.thin good = returned := by rfl
theorem wrong_projection : wide.thin bad = parameters := by rfl
theorem distinguishing_values : returned.env.1.1 = 42 ∧ returned.env.2.1 = true ∧ parameters.env.1.1 = 3 ∧ parameters.env.2.1 = false := ⟨rfl, rfl, rfl, rfl⟩

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
#check @same_payload_control
#check @good_frame_projects
#check @bad_frame_projects
end H28.FrameReturnBaseline
