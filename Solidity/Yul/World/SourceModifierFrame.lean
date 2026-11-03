import Solidity.Source.Eval
import Solidity.Source.Hoare

/-! General modifier cleanup after actual argument evaluation. The saved frame
is the post-argument state, not an assumed pre-argument restoration. -/
namespace Solidity.Yul.World.SourceModifierFrame
open Solidity.Source
/-- Successful argument evaluation may have effects. Actual modifier cleanup
restores the function-local frame saved in its resulting state. The lookup and
shape facts concern this exact selected modifier; no body-run premise is used. -/
theorem fnLocals_after_arguments {E} (G : Glob E) (F : Fr) (n : Nat) (b mb : RBody E)
    (m : RModInv E b.locals) (rest : List (RModInv E b.locals))
    (l l1 : Locals E.layout b.locals) (s t : EMState E []) (vs : Vals E.layout m.ps)
    (argument : (Source.EM.sub l (Source.evalConvArgs G F n m.args)).run s=(.ok (vs,l1),t))
    (found : G.prog.body (G.dispatchMod F.contract m.modifier)=some mb)
    (shape : m.ps.reverseAux []=mb.locals) :
    ((Source.runMods G F (n+1) b (m::rest) l).run s).2.2.fnLocals=t.2.fnLocals := by
  rw [Source.runMods,Source.Hoare.run_bind,argument]
  change ((match G.prog.body (G.dispatchMod F.contract m.modifier) with
    | none => Source.EM.halt (.stuck "modifier without a body")
    | some mb => do
      if h : m.ps.reverseAux []=mb.locals then
        let saved := (← Source.EM.st).fnLocals
        Source.EM.modSt (fun state=>{state with fnLocals:=⟨_,l1⟩})
        let result ← Source.EM.attempt (Source.execItems G F n mb.ps.length
          (some ⟨b,rest,l1⟩) mb.items (h ▸ vs.onto (Source.L0 E)))
        let ⟨Γf,lf⟩ := (← Source.EM.st).fnLocals
        Source.EM.modSt (fun state=>{state with fnLocals:=saved})
        if let .error halt := result then Source.EM.halt halt
        if eq : Γf=b.locals then pure (eq ▸ lf) else Source.EM.halt (.stuck "modifier frame")
      else Source.EM.halt (.stuck "modifier parameters")).run t).2.2.fnLocals=t.2.fnLocals
  rw [found]
  dsimp only
  rw [dif_pos shape]

  let resume := fun (result : Except Halt (Source.Out E.layout mb.locals mb.out)) => do
    let ⟨Γf,lf⟩ := (← Source.EM.st (E:=E) (Γ:=[])).fnLocals
    Source.EM.modSt (fun state=>{state with fnLocals:=t.2.fnLocals})
    if let .error halt := result then Source.EM.halt halt
    if eq : Γf=b.locals then pure (eq ▸ lf) else Source.EM.halt (.stuck "modifier frame")
  change ((do
    let result ← Source.EM.attempt (Source.execItems G F n mb.ps.length
      (some ⟨b,rest,l1⟩) mb.items (shape ▸ vs.onto (Source.L0 E)))
    resume result).run (t.1,{t.2 with fnLocals:=⟨_,l1⟩})).2.2.fnLocals=t.2.fnLocals
  rw [Source.Hoare.run_bind]
  change (match (Source.execItems G F n mb.ps.length (some ⟨b,rest,l1⟩) mb.items
    (shape ▸ vs.onto (Source.L0 E))).run (t.1,{t.2 with fnLocals:=⟨_,l1⟩}) with
    | (result,after)=>(resume result).run after).2.2.fnLocals=t.2.fnLocals
  cases run : (Source.execItems G F n mb.ps.length (some ⟨b,rest,l1⟩) mb.items
    (shape ▸ vs.onto (Source.L0 E))).run (t.1,{t.2 with fnLocals:=⟨_,l1⟩}) with
  | mk status after =>
    rcases after with ⟨ll,ss⟩
    rcases ss with ⟨ex,heap,events,logs,⟨Γf,lf⟩⟩
    cases status with
    | error halt => rfl
    | ok out =>
      dsimp only [resume]
      rw [Source.Hoare.run_bind]
      change ((do
        Source.EM.modSt (fun state=>{state with fnLocals:=t.2.fnLocals})
        pure PUnit.unit
        if eq : Γf=b.locals then pure (eq ▸ lf) else Source.EM.halt (.stuck "modifier frame")).run
          (ll,⟨ex,heap,events,logs,⟨Γf,lf⟩⟩)).2.2.fnLocals=t.2.fnLocals
      rw [Source.Hoare.run_bind]
      change ((if eq : Γf=b.locals then pure (eq ▸ lf) else Source.EM.halt (.stuck "modifier frame")).run
        (ll,⟨ex,heap,events,logs,t.2.fnLocals⟩)).2.2.fnLocals=t.2.fnLocals
      split <;> rfl

/-- An argument halt skips modifier lookup/body execution and retains the
actual post-argument state, without recoding any halt constructor. -/
theorem argument_halt {E} (G : Glob E) (F : Fr) (n : Nat) (b : RBody E)
    (m : RModInv E b.locals) (rest : List (RModInv E b.locals))
    (l : Locals E.layout b.locals) (s t : EMState E []) (h : Halt)
    (argument : (Source.EM.sub l (Source.evalConvArgs G F n m.args)).run s=(.error h,t)) :
    (Source.runMods G F (n+1) b (m::rest) l).run s=(.error h,t) := by
  rw [Source.runMods,Source.Hoare.run_bind,argument]

end Solidity.Yul.World.SourceModifierFrame
