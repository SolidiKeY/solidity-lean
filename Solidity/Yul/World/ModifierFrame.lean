import Solidity.Yul.World.CallerFrame

/-! Exact source modifier boundary. No universal preservation of arbitrary
argument expressions, dispatches or Invoke bodies is assumed. -/
namespace Solidity.Yul.World.ModifierFrame
open Solidity.Source

/-- With actual successful lookup/arity and no arguments, the modifier branch
restores the saved caller function locals even when its execItems halts. -/
theorem zeroArg_fnLocals {E} (G : Glob E) (F : Fr) (n : Nat) (b mb : RBody E) (d : Decl)
    (l : Source.Locals E.layout b.locals) (s : EMState E [])
    (found : G.prog.body (G.dispatchMod F.contract d)=some mb) (shape : mb.locals=[]) :
    ((Source.runMods G F (n+2) b [⟨d,[],.nil⟩] l).run s).2.2.fnLocals=s.2.fnLocals := by
  rw [Source.runMods,Source.Hoare.run_bind]
  change ((match G.prog.body (G.dispatchMod F.contract d) with
    | none => Source.EM.halt (.stuck "modifier without a body")
    | some mb => do
      if h : []=mb.locals then
        let saved := (← Source.EM.st).fnLocals
        Source.EM.modSt (fun state=>{state with fnLocals:=⟨_,l⟩})
        let result ← Source.EM.attempt (Source.execItems G F (n+1) mb.ps.length
          (some ⟨b,[],l⟩) mb.items (h ▸ Source.L0 E))
        let ⟨Γf,lf⟩ := (← Source.EM.st).fnLocals
        Source.EM.modSt (fun state=>{state with fnLocals:=saved})
        if let .error halt := result then Source.EM.halt halt
        if eq : Γf=b.locals then pure (eq ▸ lf) else Source.EM.halt (.stuck "modifier frame")
      else Source.EM.halt (.stuck "modifier parameters")).run s).2.2.fnLocals=s.2.fnLocals
  rw [found]
  dsimp only
  rw [dif_pos shape.symm]
  let resume := fun (result : Except Halt (Source.Out E.layout mb.locals mb.out)) => do
    let ⟨Γf,lf⟩ := (← Source.EM.st (E:=E) (Γ:=[])).fnLocals
    Source.EM.modSt (fun state=>{state with fnLocals:=s.2.fnLocals})
    if let .error halt := result then Source.EM.halt halt
    if eq : Γf=b.locals then pure (eq ▸ lf) else Source.EM.halt (.stuck "modifier frame")
  change ((do
    let result ← Source.EM.attempt (Source.execItems G F (n+1) mb.ps.length
      (some ⟨b,[],l⟩) mb.items (shape.symm ▸ Source.L0 E))
    resume result).run (s.1,{s.2 with fnLocals:=⟨_,l⟩})).2.2.fnLocals=s.2.fnLocals
  rw [Source.Hoare.run_bind]
  change (match (Source.execItems G F (n+1) mb.ps.length (some ⟨b,[],l⟩) mb.items
    (shape.symm ▸ Source.L0 E)).run (s.1,{s.2 with fnLocals:=⟨_,l⟩}) with
    | (result,after)=>(resume result).run after).2.2.fnLocals=s.2.fnLocals
  cases run : (Source.execItems G F (n+1) mb.ps.length (some ⟨b,[],l⟩) mb.items
    (shape.symm ▸ Source.L0 E)).run (s.1,{s.2 with fnLocals:=⟨_,l⟩}) with
  | mk status after =>
    rcases after with ⟨ll,ss⟩
    rcases ss with ⟨ex,heap,events,logs,⟨Γf,lf⟩⟩
    cases status with
    | error halt => rfl
    | ok out =>
      dsimp only [resume]
      rw [Source.Hoare.run_bind]
      change ((do
        Source.EM.modSt (fun state=>{state with fnLocals:=s.2.fnLocals})
        pure PUnit.unit
        if eq : Γf=b.locals then pure (eq ▸ lf) else Source.EM.halt (.stuck "modifier frame")).run
          (ll,⟨ex,heap,events,logs,⟨Γf,lf⟩⟩)).2.2.fnLocals=s.2.fnLocals
      rw [Source.Hoare.run_bind]
      change ((if eq : Γf=b.locals then pure (eq ▸ lf) else Source.EM.halt (.stuck "modifier frame")).run
        (ll,⟨ex,heap,events,logs,s.2.fnLocals⟩)).2.2.fnLocals=s.2.fnLocals
      split <;> rfl

end Solidity.Yul.World.ModifierFrame
