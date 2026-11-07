import Solidity.Source.Semantics
import Solidity.Roadmap.Controls

/-! Guard treating target-only controls as inhabited Source premises or using a
stale hand-written Source.St layout. Shared typed expression context data uses
Source.St.init and existing Roadmap fixed parameters; no session/hash adequacy. -/
namespace Solidity.Backend.Passes.AuditSourceContext

def E : Source.Env := ⟨[]⟩
def program : Source.Program E where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := []
def globals (pipeline : Roadmap.Pipeline) : Source.Glob E :=
  ⟨program,pipeline,Roadmap.Controls.toyFixed,fun _ => ⟨0,by decide⟩,
    fun _ _ => false,fun _ => .answer (.success []),⟨0,by decide⟩⟩
def frame (checked : Bool) : Source.Fr :=
  {this := ⟨1,by decide⟩,sender := ⟨2,by decide⟩,value := ⟨0,by decide⟩,
    static := false,contract := "C",checked := checked}
def sourceState : Source.St E := Source.St.init E

/-- info: 'Solidity.Backend.Passes.AuditSourceContext.E' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditSourceContext.E

/-- info: 'Solidity.Backend.Passes.AuditSourceContext.program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditSourceContext.program

/-- info: 'Solidity.Backend.Passes.AuditSourceContext.globals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditSourceContext.globals

/-- info: 'Solidity.Backend.Passes.AuditSourceContext.frame' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditSourceContext.frame

/-- info: 'Solidity.Backend.Passes.AuditSourceContext.sourceState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditSourceContext.sourceState
end Solidity.Backend.Passes.AuditSourceContext
