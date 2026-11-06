import Solidity.Roadmap.G49Final.PassCorrectAdapters

/-! H68 owner-bridge target type. The five unresolved lane families deliver a
full `PassCorrect` between the canonical languages of their actual programs,
with an independently prescribed environment map `beta`, an independently
prescribed executable bound `nu`, and their ENTIRE original local conclusion
`Local`. This is the existing relation, not a second refinement relation, and
no bridge is assumed: owners prove factories into this type
(`tests/h55/g49-final-theorem/bridge-requests.json`). -/
namespace Solidity.Roadmap.G49Final

/-- The common result type of every H68 owner delivery. -/
abbrev BridgeGoal (A B : Lang Event Outcome)
    (ps : A.Prog) (pt : B.Prog)
    (beta : B.Env → A.Env)
    (nu : B.Env → A.Res → B.Res)
    (Local : Prop) :=
  { pc : PassCorrect (Behaviour.ofLang A ps) (Behaviour.ofLang B pt) //
      pc.envAbs = beta ∧ pc.need = nu ∧ Local }

/-- A delivered bridge enters the fold as an ordinary pass; its prescribed
map and bound are the ones the fold composes. -/
def BridgeGoal.pass {A B : Lang Event Outcome} {ps : A.Prog} {pt : B.Prog}
    {beta : B.Env → A.Env} {nu : B.Env → A.Res → B.Res} {Local : Prop}
    (bridge : BridgeGoal A B ps pt beta nu Local) :
    PassCorrect (Behaviour.ofLang A ps) (Behaviour.ofLang B pt) :=
  bridge.val

theorem BridgeGoal.envAbs_eq {A B : Lang Event Outcome} {ps : A.Prog} {pt : B.Prog}
    {beta : B.Env → A.Env} {nu : B.Env → A.Res → B.Res} {Local : Prop}
    (bridge : BridgeGoal A B ps pt beta nu Local) : bridge.pass.envAbs = beta :=
  bridge.property.1

theorem BridgeGoal.need_eq {A B : Lang Event Outcome} {ps : A.Prog} {pt : B.Prog}
    {beta : B.Env → A.Env} {nu : B.Env → A.Res → B.Res} {Local : Prop}
    (bridge : BridgeGoal A B ps pt beta nu Local) : bridge.pass.need = nu :=
  bridge.property.2.1

/-- The original local lane conclusion is retained, not replaced. -/
theorem BridgeGoal.local {A B : Lang Event Outcome} {ps : A.Prog} {pt : B.Prog}
    {beta : B.Env → A.Env} {nu : B.Env → A.Res → B.Res} {Local : Prop}
    (bridge : BridgeGoal A B ps pt beta nu Local) : Local :=
  bridge.property.2.2

/-- The full-certificate carrier already meets the target shape with its own
map and bound and no extra local claim: a positive control for the type. -/
def cert_bridge {A B : Lang Event Outcome} (pass : Pass A B) (certificate : Cert pass)
    (program : A.Prog) (domain : pass.Dom program) (target : B.Prog)
    (agrees : pass.run program domain = target) :
    BridgeGoal A B program target pass.envAbs (certificate.need program domain) True :=
  ⟨cert_adapter pass certificate program domain target agrees, rfl, rfl, trivial⟩

end Solidity.Roadmap.G49Final
