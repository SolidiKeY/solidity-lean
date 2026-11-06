
import Solidity.Yul.ClosedPure

/-! Proposition-valued effect profiles over the ORIGINAL intrinsic AST.
The no-external-context interpreter can use erased evidence and thus cannot
depend on a choice of Type-valued admission derivation. These are effect
profiles, not source namespace/duplicate-case/target validity or admission. -/
namespace Solidity.Yul.Closed

def ExprWordP {F X n} {r : Nat} (e : Expr F X n r) : Prop := by
  apply Expr.casesOn (motive := fun _ _ => Prop) e
  case literal => intros; exact True
  case «local» => intros; exact True
  case external => intros; exact False
  case builtin =>
    intro a r builtin args
    exact (checkWordBuiltin builtin).isSome = true ∧ ∀ i, ExprWordP (args i)
  case call =>
    intro sig f args
    exact ∀ i, ExprWordP (args i)
termination_by structural e

def TargetWordP {X n} (target : Target X n) : Prop :=
  match target with
  | .«local» _ => True
  | .external _ => False

theorem targetWordP_closed {n} (target : Target [] n) : TargetWordP target := by
  cases target with
  | «local» i => exact True.intro
  | external ref => cases ref.index

mutual
def StmtWordP {F X c n} (s : Stmt F X c n) : Prop := by
  apply Stmt.casesOn (motive_1 := fun _ _ _ _ _ => Prop) s
  case seq =>
    intro F X c n first second
    exact StmtWordP first ∧ StmtWordP second
  case assign =>
    intro F X c n r targets expression
    exact (∀ i, TargetWordP (targets i)) ∧ ExprWordP expression
  case discard =>
    intro F X c n expression
    exact ExprWordP expression
  case let_ =>
    intro F X c n r expression body
    exact ExprWordP expression ∧ StmtWordP body
  case zero =>
    intro F X c n r body
    exact StmtWordP body
  case if_ =>
    intro F X c n expression body
    exact ExprWordP expression ∧ StmtWordP body
  case switch =>
    intro F X c n expression arms fallback
    exact ExprWordP expression ∧ CasesWordP arms ∧ StmtWordP fallback
  case for_ =>
    intro F X c n pre condition post body
    exact StmtWordP pre ∧ ExprWordP condition ∧ StmtWordP post ∧ StmtWordP body
  case functions =>
    intro F X c n signatures bodies rest
    exact BodiesWordP bodies ∧ StmtWordP rest
  all_goals intros; exact True
termination_by structural s

def CasesWordP {F X c n} (arms : Cases F X c n) : Prop := by
  apply Cases.casesOn (motive_2 := fun _ _ _ _ _ => Prop) arms
  case nil => intros; exact True
  case cons =>
    intro F X c n value body rest
    exact StmtWordP body ∧ CasesWordP rest
termination_by structural arms

def BodiesWordP {F G signatures} (bodies : Bodies F G signatures) : Prop := by
  apply Bodies.casesOn (motive_3 := fun _ _ _ _ => Prop) bodies
  case nil => intros; exact True
  case cons =>
    intro F G sig signatures body rest
    exact StmtWordP body ∧ BodiesWordP rest
termination_by structural bodies
end

def EnvWordP {F} (environment : FunctionEnv F) : Prop :=
  FunctionEnv.casesOn (motive := fun _ _ => Prop) environment
    (nil := True)
    (group := fun _signatures outer bodies => EnvWordP outer ∧ BodiesWordP bodies)
termination_by structural environment

theorem WordExprD.profile {F n r e} (d : @WordExprD F n r e) : ExprWordP e := by
  cases d with
  | literal => exact True.intro
  | «local» i => exact True.intro
  | builtin builtin args =>
      exact ⟨by rw [builtin.complete]; rfl, fun i => WordExprD.profile (args i)⟩
  | call f args => exact fun i => WordExprD.profile (args i)
termination_by structural d

theorem WordStmtD.profile {F c n s} (d : @WordStmtD F c n s) : StmtWordP s := by
  apply WordStmtD.rec
    (motive_1 := fun {F c n} s _ => StmtWordP s)
    (motive_2 := fun {F c n} arms _ => CasesWordP arms)
    (motive_3 := fun {F signatures} bodies _ => BodiesWordP bodies)
    (t := d)
  all_goals intros
  all_goals repeat' first
    | assumption
    | exact True.intro
    | exact WordExprD.profile (by assumption)
    | exact fun i => targetWordP_closed _
    | constructor

theorem WordCasesD.profile {F c n arms} (d : @WordCasesD F c n arms) : CasesWordP arms := by
  apply WordCasesD.rec
    (motive_1 := fun {F c n} s _ => StmtWordP s)
    (motive_2 := fun {F c n} arms _ => CasesWordP arms)
    (motive_3 := fun {F signatures} bodies _ => BodiesWordP bodies)
    (t := d)
  all_goals intros
  all_goals repeat' first
    | assumption
    | exact True.intro
    | exact WordExprD.profile (by assumption)
    | exact fun i => targetWordP_closed _
    | constructor

theorem WordBodiesD.profile {F signatures bodies} (d : @WordBodiesD F signatures bodies) : BodiesWordP bodies := by
  apply WordBodiesD.rec
    (motive_1 := fun {F c n} s _ => StmtWordP s)
    (motive_2 := fun {F c n} arms _ => CasesWordP arms)
    (motive_3 := fun {F signatures} bodies _ => BodiesWordP bodies)
    (t := d)
  all_goals intros
  all_goals repeat' first
    | assumption
    | exact True.intro
    | exact WordExprD.profile (by assumption)
    | exact fun i => targetWordP_closed _
    | constructor

theorem WordEnvD.profile {F environment} (d : @WordEnvD F environment) : EnvWordP environment := by
  cases d with
  | nil => exact True.intro
  | group outer bodies => exact ⟨WordEnvD.profile outer, WordBodiesD.profile bodies⟩
termination_by structural d


def HeadWordP (F : List Sig) (G : List ExternalType) (signatures : List Sig) :
    Bodies F G signatures → Prop :=
  match signatures with
  | [] => fun _ => True
  | _ :: _ => fun bodies => StmtWordP (bodyHead bodies)

def TailWordP (F : List Sig) (G : List ExternalType) (signatures : List Sig) :
    Bodies F G signatures → Prop :=
  match signatures with
  | [] => fun _ => True
  | _ :: _ => fun bodies => BodiesWordP (bodyTail bodies)

theorem bodyHead_profile {F G signatures} (bodies : Bodies F G signatures)
    (h : BodiesWordP bodies) : HeadWordP F G signatures bodies :=
  Bodies.casesOn (motive_3 := fun F G signatures bodies =>
      BodiesWordP bodies → HeadWordP F G signatures bodies) bodies
    (nil := fun _ => True.intro)
    (cons := fun _ _ h => h.1)
    h

theorem bodyTail_profile {F G signatures} (bodies : Bodies F G signatures)
    (h : BodiesWordP bodies) : TailWordP F G signatures bodies :=
  Bodies.casesOn (motive_3 := fun F G signatures bodies =>
      BodiesWordP bodies → TailWordP F G signatures bodies) bodies
    (nil := fun _ => True.intro)
    (cons := fun _ _ h => h.2)
    h

theorem bodyAt_profile {F G signatures sig} (i : Member signatures sig)
    (bodies : Bodies F G signatures) (h : BodiesWordP bodies) : StmtWordP (bodyAt i bodies) :=
  Member.casesOn (motive := fun signatures _sig i =>
      (bodies : Bodies F G signatures) → BodiesWordP bodies → StmtWordP (bodyAt i bodies)) i
    (here := fun {_ _} bodies h => bodyHead_profile bodies h)
    (there := fun {_ _ _} j bodies h =>
      bodyAt_profile j (bodyTail bodies) (bodyTail_profile bodies h))
    bodies h
termination_by structural i

def ClosureWordP {sig} (closure : Closure sig) : Prop :=
  EnvWordP closure.environment ∧ StmtWordP closure.body

/-- Every selected raw closure retains erased environment/body profile evidence.
The proof does not choose or replace the closure computed by raw lookup. -/
theorem lookup_profile {F} (environment : FunctionEnv F) (h : EnvWordP environment)
    {sig} (i : Member F sig) : ClosureWordP (lookup environment i) := by
  apply FunctionEnv.rec
    (motive := fun F environment => EnvWordP environment →
      {sig : Sig} → (i : Member F sig) → ClosureWordP (lookup environment i))
    (t := environment)
  · intro h sig i
    exact PEmpty.elim (peelMember i)
  · intro F signatures outer bodies ih h sig i
    rw [lookup_group]
    cases hs : splitMember signatures F i with
    | inl j => exact ⟨h, bodyAt_profile j bodies h.2⟩
    | inr j => exact ih h.1 j
  · exact h


end Solidity.Yul.Closed
