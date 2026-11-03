import Solidity.Yul.World.MemoryEventEncoding

/-! General actual Source.emit transport using actual lower argument and owner
codec executions. Concrete memory controls derive both from Source bodies. -/
namespace Solidity.Yul.World.MemoryEventSource
open Solidity.Source
open Solidity.Roadmap (Bytes)

theorem actual {E Γ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts)
    (l next : Locals E.layout Γ) (entry state : St E) (vs : Vals E.layout ts)
    (evaluated : (Source.evalConvArgs G F n args).run ⟨l,entry⟩=(.ok vs,⟨next,state⟩))
    (data : Bytes) (codec : (Source.encodeVals F n false vs.toR).run ⟨Source.L0 E,state⟩=
      (.ok data,⟨Source.L0 E,state⟩)) (normal : F.static=false) :
    (Source.execS G F (n+1) 0 none (StaticEventSource.statement event typed args) l).run ⟨Source.L0 E,entry⟩=
      (.ok (.normal next),⟨Source.L0 E,{state with logs:=(F.this,G.selector (sigOf E.layout event.name ts)++data)::state.logs}⟩) := by
  simp only [Source.execS,StaticEventSource.statement,Source.Hoare.run_bind,Source.run_sub]
  rw [evaluated]
  dsimp only
  rw [codec]
  simp only [normal,Bool.false_eq_true,if_false]
  rfl

theorem actual_static {E Γ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts)
    (l next : Locals E.layout Γ) (entry state : St E) (vs : Vals E.layout ts)
    (evaluated : (Source.evalConvArgs G F n args).run ⟨l,entry⟩=(.ok vs,⟨next,state⟩))
    (data : Bytes) (codec : (Source.encodeVals F n false vs.toR).run ⟨Source.L0 E,state⟩=
      (.ok data,⟨Source.L0 E,state⟩)) (static : F.static=true) :
    (Source.execS G F (n+1) 0 none (StaticEventSource.statement event typed args) l).run ⟨Source.L0 E,entry⟩=
      (.error (.revert []),⟨Source.L0 E,state⟩) := by
  simp only [Source.execS,StaticEventSource.statement,Source.Hoare.run_bind,Source.run_sub]
  rw [evaluated]
  dsimp only
  rw [codec]
  simp only [static,if_true]
  rfl
end Solidity.Yul.World.MemoryEventSource
