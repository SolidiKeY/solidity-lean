import Solidity.Yul.RawU8Statement
import Solidity.Yul.RawSequence

/-! Same-context mixed Boolean/checked-uint8 certificates over actual Source
items. Execution retains complete raw prefixes. This slice supplies concrete
Source composition under checked-frame/coherence premises, not admission. -/
namespace Solidity.Yul.RawCheckedSequence

inductive Supported (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
    (modifier : Bool) (control : Solidity.Source.SCtx) :
    Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys → Type where
  | nil : Supported ctx returns modifier control .nil
  | boolean {stmt rest} : RawSource.Supported ctx returns modifier control stmt →
      Supported ctx returns modifier control rest →
      Supported ctx returns modifier control (.stmt stmt rest)
  | uint8 {expr rest} : LocalU8Expr.Supported ctx.env ctx.tys expr →
      Supported ctx returns modifier control rest →
      Supported ctx returns modifier control (.stmt (.expr expr) rest)

def run {ctx returns modifier control items}
    (proof : Supported ctx returns modifier control items) :
    Solidity.Roadmap.Pipeline → Nat → RawFrame.State ctx →
      Solidity.Source.R Unit × RawFrame.State ctx := by
  apply Supported.casesOn (motive := fun _ _ =>
    Solidity.Roadmap.Pipeline → Nat → RawFrame.State ctx →
      Solidity.Source.R Unit × RawFrame.State ctx) proof
  case nil =>
    exact fun _ fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | _+1 => (.ok (),state)
  case boolean =>
    intro stmt rest head tail
    exact fun pipeline fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | fuel+1 =>
        let first := RawCoherent.execS head fuel state
        match first.1 with
        | .error halt => (.error halt,first.2)
        | .ok _ => run tail pipeline fuel first.2
  case uint8 =>
    intro expr rest head tail
    exact fun pipeline fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | fuel+1 =>
        let first := RawU8Statement.run head pipeline fuel state
        match first.1 with
        | .error halt => (.error halt,first.2)
        | .ok _ => run tail pipeline fuel first.2
termination_by structural proof

theorem run_boolean {ctx returns modifier control stmt rest}
    (head : RawSource.Supported ctx returns modifier control stmt)
    (tail : Supported ctx returns modifier control rest)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    run (.boolean head tail) pipeline (fuel+1) state =
      (let first := RawCoherent.execS head fuel state
       match first.1 with
       | .error halt => (.error halt,first.2)
       | .ok _ => run tail pipeline fuel first.2) := by rfl

theorem run_uint8 {ctx returns modifier control expr rest}
    (head : LocalU8Expr.Supported ctx.env ctx.tys expr)
    (tail : Supported ctx returns modifier control rest)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    run (.uint8 head tail) pipeline (fuel+1) state =
      (let first := RawU8Statement.run head pipeline fuel state
       match first.1 with
       | .error halt => (.error halt,first.2)
       | .ok _ => run tail pipeline fuel first.2) := by rfl

def block {ctx returns modifier control items}
    (proof : Supported ctx returns modifier control items)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | fuel+1 => run proof pipeline fuel state

theorem correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (items : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier control items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr),
 frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedSequence.run proof glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execItems glob frame fuel nps ph items state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedSequence.run proof glob.pipeline fuel state) := by
  intro ctx returns modifier control items proof glob frame checked fuel nps ph state same
  induction proof generalizing fuel state with
  | nil =>
    cases fuel <;> exact ⟨same,rfl⟩
  | @boolean stmt rest head tail ih =>
    cases fuel with
    | zero => exact ⟨same,rfl⟩
    | succ fuel =>
      have headSame := RawCoherent.invariant head glob frame fuel state same
      have headActual := RawCoherent.source_run head glob frame fuel nps ph state same
      have tailActual := ih fuel (RawCoherent.execS head fuel state).2 headSame
      have composition := RawSequence.source_cons glob frame fuel nps ph state
        (RawCoherent.execS head fuel state)
        (run tail glob.pipeline fuel (RawCoherent.execS head fuel state).2) headActual tailActual.2
      cases headTag : (RawCoherent.execS head fuel state).1 with
      | error halt =>
        simp only [run_boolean,headTag]
        simp only [headTag] at composition
        exact ⟨headSame,composition⟩
      | ok value =>
        simp only [run_boolean,headTag]
        simp only [headTag] at composition
        exact ⟨tailActual.1,composition⟩
  | @uint8 expr rest head tail ih =>
    cases fuel with
    | zero => exact ⟨same,rfl⟩
    | succ fuel =>
      have headFacts := RawU8Statement.correct ctx expr head glob frame checked
        fuel nps ph returns modifier control state same
      have headActual : (Solidity.Source.execS glob frame fuel nps ph
          (Solidity.Source.RStmt.expr (R:=returns) (M:=modifier) (k:=control) expr) state.clean).run
            (Solidity.Source.L0 ctx.env,state.world) =
          RawSequence.represented (RawU8Statement.run head glob.pipeline fuel state) := by
        have observed := headFacts.2
        unfold RawCoherent.observe at observed
        rw [if_pos headFacts.1] at observed
        exact (Option.some.inj observed).symm
      have tailActual := ih fuel (RawU8Statement.run head glob.pipeline fuel state).2 headFacts.1
      have composition := RawSequence.source_cons glob frame fuel nps ph state
        (RawU8Statement.run head glob.pipeline fuel state)
        (run tail glob.pipeline fuel (RawU8Statement.run head glob.pipeline fuel state).2)
        headActual tailActual.2
      cases headTag : (RawU8Statement.run head glob.pipeline fuel state).1 with
      | error halt =>
        simp only [run_uint8,headTag]
        simp only [headTag] at composition
        exact ⟨headFacts.1,composition⟩
      | ok value =>
        simp only [run_uint8,headTag]
        simp only [headTag] at composition
        exact ⟨tailActual.1,composition⟩

theorem block_correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (items : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier control items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr),
 frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent (Solidity.Yul.RawCheckedSequence.block proof glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.block items) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSequence.represented (Solidity.Yul.RawCheckedSequence.block proof glob.pipeline fuel state) := by
  intro ctx returns modifier control items proof glob frame checked fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    dsimp only [block]
    have actual := correct ctx returns modifier control items proof glob frame checked fuel nps ph state same
    constructor
    · exact actual.1
    · rw [Solidity.Source.execS,Solidity.Source.Hoare.run_bind,actual.2]
      cases tag : (run proof glob.pipeline fuel state).1 with
      | error halt => simp only [RawSequence.represented,tag,Except.map]
      | ok value =>
        simp only [RawSequence.represented,tag,Except.map,Solidity.Source.Out.close,RawSequence.restore_self]
        rfl


end Solidity.Yul.RawCheckedSequence
