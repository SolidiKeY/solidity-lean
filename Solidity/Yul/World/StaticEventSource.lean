import Solidity.Yul.World.StaticEventEncoding

/-! Actual Source.emit transport after argument evaluation. Premises describe
real expression evaluation, not an assumed emit outcome or world adequacy. -/
namespace Solidity.Yul.World.StaticEventSource
open Solidity.Source
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.World.StaticEventArgs

def statement {E Γ ts} (event : Decl) (typed : event.paramTys E=some ts)
    (args : RConvArgs E Γ ts) : RStmt E [] false ⟨false,false⟩ Γ Γ := .emit event typed args

theorem actual {E Γ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts)
    (l next : Locals E.layout Γ) (entry state : St E) (vs : Vals E.layout ts)
    (evaluated : (Source.evalConvArgs G F n args).run ⟨l,entry⟩=(.ok vs,⟨next,state⟩))
    (ws : List Word) (computed : words? vs=some ws) (nonstatic : F.static=false) :
    (Source.execS G F (n+1) 0 none (statement event typed args) l).run ⟨Source.L0 E,entry⟩=
      (.ok (.normal next),⟨Source.L0 E,{state with logs:=(F.this,G.selector (sigOf E.layout event.name ts)++
        Source.abiLayout (ws.map (fun w=>(false,wordBytes w))))::state.logs}⟩) := by
  simp only [Source.execS,statement,Source.Hoare.run_bind,Source.run_sub]
  rw [evaluated]
  dsimp only
  rw [encodeVals_words F n vs ws computed]
  simp only [nonstatic,Bool.false_eq_true,if_false]
  rfl
theorem actual_static {E Γ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (args : RConvArgs E Γ ts)
    (l next : Locals E.layout Γ) (entry state : St E) (vs : Vals E.layout ts)
    (evaluated : (Source.evalConvArgs G F n args).run ⟨l,entry⟩=(.ok vs,⟨next,state⟩))
    (ws : List Word) (computed : words? vs=some ws) (static : F.static=true) :
    (Source.execS G F (n+1) 0 none (statement event typed args) l).run ⟨Source.L0 E,entry⟩=
      (.error (.revert []),⟨Source.L0 E,state⟩) := by
  simp only [Source.execS,statement,Source.Hoare.run_bind,Source.run_sub]
  rw [evaluated]
  dsimp only
  rw [encodeVals_words F n vs ws computed]
  simp only [static,if_true]
  rfl
end Solidity.Yul.World.StaticEventSource
