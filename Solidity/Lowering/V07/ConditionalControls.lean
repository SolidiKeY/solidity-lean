import Solidity.Lowering.V07.ConditionalAssignments
import Solidity.Lowering.V07.P12Controls

namespace Solidity.Lowering.V07.ConditionalControls
open Source.SemanticsExamples ConditionalAssignments
open P12Controls (C E BindingRel)
abbrev SrcCtx := .int Source.IntTy.u8 :: P12Controls.SrcCtx
abbrev TgtCtx := .val PrimTy.uint :: P12Controls.TgtCtx

def source (choice : Bool) : Source.EMState E SrcCtx :=
  (.cons (.int 11 (by decide)) (P12Controls.source.1.set (.there .here) (.bool choice)),P12Controls.source.2)
def target (choice : Bool) : State C TgtCtx :=
  (P12Controls.target.setLocal (.there .here) choice).push (integerValue .u8 11 (by decide))
def mapping : ContextMap SrcCtx TgtCtx := P12Controls.mapping.cons (.int .u8) (.val .uint)

def sci : Source.Idx SrcCtx .bool := .there .here
def sca : Source.Idx SrcCtx .bool := .there (.there .here)
def si : Source.Idx SrcCtx (.int .u8) := .there (.there (.there (.there .here)))
def sa : Source.Idx SrcCtx (.int .u8) := .there (.there (.there .here))
def sj : Source.Idx SrcCtx (.int .u8) := sa
def sb : Source.Idx SrcCtx (.int .u8) := .here

def tci : Idx TgtCtx (.val .bool) := .there .here
def tca : Idx TgtCtx (.val .bool) := .there (.there .here)
def ti : Idx TgtCtx (.val .uint) := .there (.there (.there (.there .here)))
def ta : Idx TgtCtx (.val .uint) := .there (.there (.there .here))
def tj : Idx TgtCtx (.val .uint) := ta
def tb : Idx TgtCtx (.val .uint) := .here

theorem initial (choice : Bool) : mapping.Related BindingRel (source choice).1 (target choice).env := by
  have old : P12Controls.mapping.Related BindingRel
      (P12Controls.source.1.set (.there .here) (.bool choice))
      (TEnv.set (.there .here) choice P12Controls.target.env) :=
    ContextMap.related_write P12Controls.mapping BindingRel P12Controls.source.1 P12Controls.target.env
      P12Controls.initial (.there .here) (.there .here) rfl (.bool choice) choice rfl
  intro τ k
  exact (ContextMap.related_cons P12Controls.mapping BindingRel _ _ old (.int .u8) (.val .uint)
    (.int 11 (by decide)) (integerValue .u8 11 (by decide)) ⟨rfl,rfl⟩) k

-- Inhabited clients for every generic headline, including the full initial map.
def conditional_source (p : Roadmap.Pipeline) (fuel : Nat) (choice : Bool) :=
  source_run (MixedAssignmentControls.globals p) F0 fuel (source choice) sci sca choice si sa sj sb rfl
def conditional_branch (choice : Bool) := branch_run (target choice) ti ta choice (PrimTy.dflt .uint)
def conditional_prefix (choice : Bool) := prefix_run (target choice) tci tca choice ti ta tj tb rfl
def conditional_operand (choice : Bool) := operand_run (target choice) tci tca choice ti ta tj tb rfl
def conditional_transport (p : Roadmap.Pipeline) (fuel : Nat) (choice : Bool) :=
  transport (MixedAssignmentControls.globals p) F0 fuel (source choice) (target choice) mapping BindingRel
    (initial choice) P12Controls.bool_reflect sci sca si sa sj sb tci tca ti ta tj tb rfl rfl rfl rfl rfl rfl
def conditional_extension (choice : Bool) := extension (target choice) tci tca choice ti ta tj tb rfl
  (Thin.drop (t := .val .bool) .refl) (true,(target choice).env)
def conditional_untouched (choice : Bool) := untouched (source choice) (target choice) choice sci si sa sj sb tci ti ta tj tb

def expression : Source.RExpr E SrcCtx (.int .u8) :=
  .cond (.assign (.local sci) (.local sca)) (.assign (.local si) (.local sa)) (.assign (.local sj) (.local sb))
def sourceObs (p : Roadmap.Pipeline) (choice : Bool) : List (Option Int) :=
  match (Source.evalE (MixedAssignmentControls.globals p) F0 6 expression).run (source choice) with
  | (.ok (.val v),post) => [v.key,(post.1.get sci).key,(post.1.get sca).key,
      (post.1.get sb).key,(post.1.get sa).key,(post.1.get si).key]
  | _ => []
def targetObs (choice : Bool) : List (Option Int) :=
  match (operand tci tca ti ta tj tb).run (target choice) with
  | .ok (post,.prim v) => [PrimTy.num? v,some (if TEnv.get tci post.st.env = true then 1 else 0),
      some (if TEnv.get tca post.st.env = true then 1 else 0),PrimTy.num? (TEnv.get tb post.st.env),
      PrimTy.num? (TEnv.get ta post.st.env),PrimTy.num? (TEnv.get ti post.st.env)]
  | _ => []
/-- info: [[some 11, some 0, some 0, some 11, some 11, some 3],
 [some 11, some 0, some 0, some 11, some 11, some 3],
 [some 7, some 1, some 1, some 11, some 7, some 7],
 [some 7, some 1, some 1, some 11, some 7, some 7]] -/
#guard_msgs in
#eval IO.println (reprStr [sourceObs .legacy false,sourceObs .viaIR false,sourceObs .legacy true,sourceObs .viaIR true])
/-- info: [[some 11, some 0, some 0, some 11, some 11, some 3], [some 7, some 1, some 1, some 11, some 7, some 7]] -/
#guard_msgs in
#eval IO.println (reprStr [targetObs false,targetObs true])

-- The complete caller and live references are real, not an empty frame.
example (choice : Bool) : (source choice).2.heap.get 0 = some ⟨.bytes .memory,.bytes [0,0]⟩ ∧
    E.pathTy MixedAssignmentControls.path = some (.bytes .storage) := ⟨rfl,rfl⟩
example (choice : Bool) : (targetAfter (target choice) tci choice ti ta tj tb).heap = (target choice).heap ∧
    (targetAfter (target choice) tci choice ti ta tj tb).glob = (target choice).glob ∧
    TEnv.get (.there (.there (.there (.there (.there (.there .here))))))
      (targetAfter (target choice) tci choice ti ta tj tb).env = some MixedAssignmentControls.storageRef := by
  cases choice <;> exact ⟨rfl,rfl,rfl⟩
example (choice : Bool) : ∃ r : HRef (target choice).H bytesR,
    TEnv.get (.there (.there (.there (.there (.there .here))))) (target choice).env = some r ∧
      (target choice).heap.len r .dyn = 2 := MixedAssignmentControls.live_memory

-- Wrong eager execution, stale condition and post-drop caller reads are actual wrong consumers.
def eager : Option Int :=
  match (code tci tca ti ta tj tb).run (target true) with
  | .ok out => match (branch tj tb).run out.st with
    | .ok wrong => PrimTy.num? (TEnv.get .here wrong.st.env)
    | _ => none
  | _ => none
def staleCondition : Option Int :=
  match (operand tci tci ti ta tj tb).run (target true) with
  | .ok (_, .prim v) => PrimTy.num? v | _ => none
def postDropRead : Option Int :=
  match (operand tci tca ti ta tj tb).run (target true) with
  | .ok (out,_) => PrimTy.num? (TEnv.get tb out.st.env) | _ => none
/-- info: [some 11, some 11, some 11, some 7] -/
#guard_msgs in
#eval IO.println (reprStr [eager,staleCondition,postDropRead,(targetObs true).head!])

-- Boolean aliases can overwrite the original condition AFTER its choice was captured.
abbrev BSrcCtx := .bool :: P12Controls.SrcCtx
abbrev BTgtCtx := .val PrimTy.bool :: P12Controls.TgtCtx
def bsource : Source.EMState E BSrcCtx := (.cons (.bool false) P12Controls.source.1,P12Controls.source.2)
def btarget : State C BTgtCtx := P12Controls.target.push (t := .val .bool) false
def bmapping : ContextMap BSrcCtx BTgtCtx := P12Controls.mapping.cons .bool (.val .bool)
theorem binitial : bmapping.Related BindingRel bsource.1 btarget.env := by
  exact ContextMap.related_cons P12Controls.mapping BindingRel _ _ P12Controls.initial
    .bool (.val .bool) (.bool false) false rfl

example (p : Roadmap.Pipeline) (fuel : Nat) :=
  transport (MixedAssignmentControls.globals p) F0 fuel bsource btarget bmapping BindingRel binitial
    P12Controls.bool_reflect (.there .here) (.there (.there .here))
    (.there .here) .here (.there (.there .here)) (.there .here)
    (.there .here) (.there (.there .here))
    (.there .here) .here (.there (.there .here)) (.there .here) rfl rfl rfl rfl rfl rfl
-- The condition destination aliases the selected donor; its REACHED value is required.
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  transport (MixedAssignmentControls.globals p) F0 fuel bsource btarget bmapping BindingRel binitial
    P12Controls.bool_reflect (.there .here) (.there (.there .here))
    .here (.there .here) (.there (.there .here)) (.there .here)
    (.there .here) (.there (.there .here))
    .here (.there .here) (.there (.there .here)) (.there .here) rfl rfl rfl rfl rfl rfl
-- All roles can name the same existing true cell.
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  transport (MixedAssignmentControls.globals p) F0 fuel bsource btarget bmapping BindingRel binitial
    P12Controls.bool_reflect (.there (.there .here)) (.there (.there .here))
    (.there (.there .here)) (.there (.there .here)) (.there (.there .here)) (.there (.there .here))
    (.there (.there .here)) (.there (.there .here))
    (.there (.there .here)) (.there (.there .here)) (.there (.there .here)) (.there (.there .here)) rfl rfl rfl rfl rfl rfl

def boolObs (reachedDonor : Bool) : List Bool :=
  let i : Idx BTgtCtx (.val .bool) := if reachedDonor then .here else .there .here
  let a : Idx BTgtCtx (.val .bool) := if reachedDonor then .there .here else .here
  match (operand (.there .here) (.there (.there .here)) i a (.there (.there .here)) (.there .here)).run btarget with
  | .ok (out,.prim v) => [v,TEnv.get .here out.st.env,TEnv.get (.there .here) out.st.env,
      TEnv.get (.there (.there .here)) out.st.env]
  | _ => []
/-- info: [[false, false, false, true], [true, true, true, true]] -/
#guard_msgs in
#eval IO.println (reprStr [boolObs false,boolObs true])

def boolSourceObs (p : Roadmap.Pipeline) (reachedDonor : Bool) : List Bool :=
  let i : Source.Idx BSrcCtx .bool := if reachedDonor then .here else .there .here
  let a : Source.Idx BSrcCtx .bool := if reachedDonor then .there .here else .here
  match (Source.evalE (MixedAssignmentControls.globals p) F0 6
    (.cond (.assign (.local (.there .here)) (.local (.there (.there .here))))
      (.assign (.local i) (.local a))
      (.assign (.local (.there (.there .here))) (.local (.there .here))))).run bsource with
  | (.ok (.val (.bool v)),out) =>
      let get (i : Source.Idx BSrcCtx .bool) := match out.1.get i with | .bool v => v
      [v,get .here,get (.there .here),get (.there (.there .here))]
  | _ => []
/-- info: [[false, false, false, true], [true, true, true, true], [false, false, false, true], [true, true, true, true]] -/
#guard_msgs in
#eval IO.println (reprStr [boolSourceObs .legacy false,boolSourceObs .legacy true,
  boolSourceObs .viaIR false,boolSourceObs .viaIR true])

-- Bounded failure controls ONLY: no general failure payload transport is asserted.
def poison : Source.RExpr E SrcCtx (.int .u8) :=
  .binary .div (.local sb) (.binary .sub (.local sb) (.local sb))
def sourcePoison (p : Roadmap.Pipeline) (choice : Bool) : Bool :=
  match (Source.evalE (MixedAssignmentControls.globals p) F0 8
    (.cond (.assign (.local sci) (.local sca)) (.assign (.local si) (.local sa)) poison)).run (source choice) with
  | (.ok _,_) => true | _ => false
def poisonCode : Prog C TgtCtx TgtCtx :=
  .cons (.assignLocal tci (.simple (.local tca)))
    (.cons (.ite (.simple (.local tci))
      (.cons (.assignLocal ti (.simple (.local ta))) .nil)
      (.cons (.assignLocal tj (.binop .div rfl rfl (.simple (.local tb))
        (.binop .sub rfl rfl (.simple (.local tb)) (.simple (.local tb))))) .nil)) .nil)
def targetPoison (choice : Bool) : Bool :=
  match poisonCode.run (target choice) with | .ok _ => true | _ => false
/-- info: [[true, false], [true, false], [true, false]] -/
#guard_msgs in
#eval IO.println (reprStr [[sourcePoison .legacy true,sourcePoison .legacy false],
  [sourcePoison .viaIR true,sourcePoison .viaIR false],[targetPoison true,targetPoison false]])

end Solidity.Lowering.V07.ConditionalControls
