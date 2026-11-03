import Solidity.Yul.RawCoherent

/-! Actual Source.RItems sequencing over the H11 raw frame.
The certificate has only same-context bool-expression statements. Execution
retains full raw partial state, and concrete Source.execItems agreement is
proved for coherent starts. It does not claim declarations/returns/sessions. -/
namespace Solidity.Yul.RawSequence

inductive Supported (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
    (modifier : Bool) (control : Solidity.Source.SCtx) :
    Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys → Type where
  | nil : Supported ctx returns modifier control .nil
  | cons {stmt rest} : RawSource.Supported ctx returns modifier control stmt →
      Supported ctx returns modifier control rest →
      Supported ctx returns modifier control (.stmt stmt rest)

def run {ctx returns modifier control items}
    (proof : Supported ctx returns modifier control items) :
    Nat → RawFrame.State ctx → Solidity.Source.R Unit × RawFrame.State ctx := by
  apply Supported.casesOn (motive := fun _ _ =>
    Nat → RawFrame.State ctx → Solidity.Source.R Unit × RawFrame.State ctx) proof
  case nil =>
    exact fun fuel state => match fuel with
      | 0 => (.error .timeout, state)
      | _+1 => (.ok (), state)
  case cons =>
    intro stmt rest head tail
    exact fun fuel state => match fuel with
      | 0 => (.error .timeout, state)
      | n+1 =>
        let first := RawCoherent.execS head n state
        match first.1 with
        | .error halt => (.error halt, first.2)
        | .ok _ => run tail n first.2
termination_by structural proof

theorem run_cons {ctx returns modifier control stmt rest}
    (head : RawSource.Supported ctx returns modifier control stmt)
    (tail : Supported ctx returns modifier control rest)
    (fuel : Nat) (state : RawFrame.State ctx) :
    run (.cons head tail) (fuel+1) state =
      (let first := RawCoherent.execS head fuel state
       match first.1 with
       | .error halt => (.error halt, first.2)
       | .ok _ => run tail fuel first.2) := rfl

/-- The Source observation represented by a coherent raw-frame result.
This is not a conversion theorem for arbitrary dirty frames. -/
def represented {ctx} (result : Solidity.Source.R Unit × RawFrame.State ctx) :
    Solidity.Source.R (Solidity.Source.Out ctx.env.layout ctx.tys ctx.tys) ×
      (Solidity.Source.Locals ctx.env.layout [] × Solidity.Source.St ctx.env) :=
  (result.1.map (fun _ => .normal result.2.clean),
    (Solidity.Source.L0 ctx.env, result.2.world))

theorem source_cons {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy}
    {modifier : Bool} {control : Solidity.Source.SCtx}
    {stmt : Solidity.Source.RStmt ctx.env returns modifier control ctx.tys ctx.tys}
    {rest : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys}
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx)
    (first second : Solidity.Source.R Unit × RawFrame.State ctx)
    (headRun : (Solidity.Source.execS glob frame fuel nps ph stmt state.clean).run
      (Solidity.Source.L0 ctx.env, state.world) = represented first)
    (tailRun : (Solidity.Source.execItems glob frame fuel nps ph rest first.2.clean).run
      (Solidity.Source.L0 ctx.env, first.2.world) = represented second) :
    (Solidity.Source.execItems glob frame (fuel+1) nps ph
      (Solidity.Source.RItems.stmt (R := returns) (M := modifier) (k := control) stmt rest)
      state.clean).run (Solidity.Source.L0 ctx.env, state.world) =
        match first.1 with
        | .error halt => represented (.error halt, first.2)
        | .ok _ => represented second := by
  rw [Solidity.Source.execItems, Solidity.Source.Hoare.run_bind, headRun]
  cases headTag : first.1 with
  | error halt =>
    simp only [represented, headTag, Except.map]
  | ok _value =>
    simp only [represented, headTag, Except.map]
    rw [Solidity.Source.Hoare.run_bind, tailRun]
    cases tailTag : second.1 with
    | error halt =>
      simp only [represented, tailTag, Except.map]
    | ok _value =>
      simp only [represented, tailTag, Except.map]
      rfl

theorem correct {ctx returns modifier control items}
    (proof : Supported ctx returns modifier control items)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.coherent (run proof fuel state).2 = true ∧
      (Solidity.Source.execItems glob frame fuel nps ph items state.clean).run
        (Solidity.Source.L0 ctx.env, state.world) = represented (run proof fuel state) := by
  induction proof generalizing fuel state with
  | nil =>
    cases fuel with
    | zero => exact ⟨same, rfl⟩
    | succ fuel => exact ⟨same, rfl⟩
  | @cons stmt rest head tail ih =>
    cases fuel with
    | zero => exact ⟨same, rfl⟩
    | succ fuel =>
      have headSame := RawCoherent.invariant head glob frame fuel state same
      have headActual := RawCoherent.source_run head glob frame fuel nps ph state same
      have tailActual := ih fuel (RawCoherent.execS head fuel state).2 headSame
      have composition := source_cons glob frame fuel nps ph state
        (RawCoherent.execS head fuel state)
        (run tail fuel (RawCoherent.execS head fuel state).2) headActual tailActual.2
      cases headTag : (RawCoherent.execS head fuel state).1 with
      | error halt =>
        simp only [run_cons, headTag]
        simp only [headTag] at composition
        exact ⟨headSame, composition⟩
      | ok _value =>
        simp only [run_cons, headTag]
        simp only [headTag] at composition
        exact ⟨tailActual.1, composition⟩

theorem restore_self {D : Solidity.Source.Layout} {ctx : Solidity.Source.RCtx}
    (locals : Solidity.Source.Locals D ctx) :
    locals.restore ctx = .ok locals := by
  unfold Solidity.Source.Locals.restore
  have same : ctx.drop (ctx.length - ctx.length) = ctx := by
    rw [Nat.sub_self, List.drop_zero]
  rw [dif_pos same]
  have dropped : ∀ (count : Nat) (zero : count = 0) (back : ctx.drop count = ctx),
      (back ▸ Solidity.Source.Locals.drop count locals) = locals := by
    intro count zero back
    subst count
    rfl
  rw [dropped (ctx.length - ctx.length) (Nat.sub_self _) same]
  rfl

/-- The extra horizon level is the ACTUAL Source block level. The body has
the same context on both ends, so closing it retains the raw frame verbatim. -/
def block {ctx returns modifier control items}
    (proof : Supported ctx returns modifier control items)
    (fuel : Nat) (state : RawFrame.State ctx) : Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout, state)
  | n+1 => run proof n state

theorem block_correct {ctx returns modifier control items}
    (proof : Supported ctx returns modifier control items)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.coherent (block proof fuel state).2 = true ∧
      (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.block items)
        state.clean).run (Solidity.Source.L0 ctx.env, state.world) =
          represented (block proof fuel state) := by
  cases fuel with
  | zero => exact ⟨same, rfl⟩
  | succ fuel =>
    dsimp only [block]
    have actual := correct proof glob frame fuel nps ph state same
    constructor
    · exact actual.1
    · rw [Solidity.Source.execS, Solidity.Source.Hoare.run_bind, actual.2]
      cases tag : (run proof fuel state).1 with
      | error halt =>
        simp only [represented, tag, Except.map]
      | ok _value =>
        simp only [represented, tag, Except.map]
        simp only [Solidity.Source.Out.close, restore_self]
        rfl

theorem source_agrees {ctx returns modifier control items}
    (proof : Supported ctx returns modifier control items)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.observe (run proof fuel state) =
      some ((Solidity.Source.execItems glob frame fuel nps ph items state.clean).run
        (Solidity.Source.L0 ctx.env, state.world)) := by
  have actual := correct proof glob frame fuel nps ph state same
  unfold RawCoherent.observe
  rw [if_pos actual.1]
  exact congrArg some actual.2.symm

theorem block_source_agrees {ctx returns modifier control items}
    (proof : Supported ctx returns modifier control items)
    (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr)
    (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx) (same : RawCoherent.coherent state = true) :
    RawCoherent.observe (block proof fuel state) =
      some ((Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.block items)
        state.clean).run (Solidity.Source.L0 ctx.env, state.world)) := by
  have actual := block_correct proof glob frame fuel nps ph state same
  unfold RawCoherent.observe
  rw [if_pos actual.1]
  exact congrArg some actual.2.symm

end Solidity.Yul.RawSequence
