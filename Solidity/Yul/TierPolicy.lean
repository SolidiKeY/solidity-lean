import Solidity.Yul.Static

/-! Tier-policy traversal of the original intrinsic AST. This is neither source
typing/admission nor semantics of physical/world effects. Open function contexts
require separate policy evidence for their supplied definitions; a root has F=[].
All declared bodies are inspected even if no call executes them. -/
namespace Solidity.Yul.Policy

def BuiltinP {a r} (tier : Tier) (b : Builtin a r) : Prop :=
  b.name ≠ "callcode" ∧ b.tier.any tier.includes = true

def ExternalP (tier : Tier) (ty : ExternalType) : Prop :=
  match ty with
  | .internalFunction => False
  | .value _ | .externalFunction | .constant _ => True
  | _ => tier.includes .B = true

theorem builtin_iff {a r} (tier : Tier) (b : Builtin a r) :
    b.checkTier tier = .ok () ↔ BuiltinP tier b := by
  unfold Builtin.checkTier BuiltinP
  by_cases hc : b.name = "callcode"
  · rw [if_pos hc]
    constructor
    · intro h; cases h
    · intro h; exact False.elim (h.1 hc)
  · rw [if_neg hc]
    cases ht : b.tier with
    | none =>
      constructor
      · intro h; cases h
      · intro h; cases h.2
    | some required =>
      change (if tier.includes required then Except.ok () else Except.error (Refusal.needsTier required)) = .ok () ↔
        b.name ≠ "callcode" ∧ tier.includes required = true
      by_cases hi : tier.includes required = true
      · rw [if_pos hi]
        constructor
        · intro _; exact ⟨hc, hi⟩
        · intro _; rfl
      · rw [if_neg hi]
        constructor
        · intro h; cases h
        · intro h; exact False.elim (hi h.2)

theorem external_iff (tier : Tier) (ty : ExternalType) :
    admitExternal tier ty = .ok () ↔ ExternalP tier ty := by
  cases ty <;> cases tier <;>
    simp only [admitExternal, ExternalP, Tier.includes, ↓reduceIte, reduceCtorEq]

def allFin : (a : Nat) → (Fin a → Except Refusal Unit) → Except Refusal Unit
  | 0, _ => .ok ()
  | a + 1, get => do
    get 0
    allFin a (fun i => get i.succ)

theorem bind_iff (first second : Except Refusal Unit) :
    (first >>= fun _ => second) = .ok () ↔ first = .ok () ∧ second = .ok () := by
  cases first with
  | error error =>
    constructor
    · intro h; cases h
    · intro h; cases h.1
  | ok value =>
    cases value
    constructor
    · intro h; exact ⟨rfl, h⟩
    · intro h; exact h.2

theorem allFin_iff (a : Nat) (get : Fin a → Except Refusal Unit) :
    allFin a get = .ok () ↔ ∀ i, get i = .ok () := by
  induction a with
  | zero => constructor; intro _ i; exact Fin.elim0 i; intro _; rfl
  | succ a ih =>
    change ((get 0 >>= fun _ => allFin a (fun i => get i.succ)) = .ok ()) ↔ _
    rw [bind_iff, ih]
    constructor
    · intro h; exact Fin.cases h.1 h.2
    · intro h; exact ⟨h 0, fun i => h i.succ⟩

def ExprP (tier : Tier) {F X n r} (e : Expr F X n r) : Prop := by
  apply Expr.casesOn (motive := fun _ _ => Prop) e
  case literal => intros; exact True
  case «local» => intros; exact True
  case external => intro ref; exact ExternalP tier ref.ty
  case builtin => intro a r b args; exact BuiltinP tier b ∧ ∀ i, ExprP tier (args i)
  case call => intro sig f args; exact ∀ i, ExprP tier (args i)
termination_by structural e

def checkExpr (tier : Tier) {F X n r} (e : Expr F X n r) : Except Refusal Unit := by
  apply Expr.casesOn (motive := fun _ _ => Except Refusal Unit) e
  case literal => intros; exact .ok ()
  case «local» => intros; exact .ok ()
  case external => intro ref; exact admitExternal tier ref.ty
  case builtin =>
    intro a r b args
    exact do
      b.checkTier tier
      allFin a (fun i => checkExpr tier (args i))
  case call => intro sig f args; exact allFin sig.args (fun i => checkExpr tier (args i))
termination_by structural e

theorem expr_iff (tier : Tier) {F X n r} (e : Expr F X n r) :
    checkExpr tier e = .ok () ↔ ExprP tier e := by
  cases e with
  | literal value => exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | «local» i => exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | external ref => exact external_iff tier ref.ty
  | builtin b args =>
    change ((b.checkTier tier >>= fun _ => allFin _ (fun i => checkExpr tier (args i))) = .ok ()) ↔ _
    rw [bind_iff, builtin_iff, allFin_iff]
    exact and_congr Iff.rfl (forall_congr' (fun i => expr_iff tier (args i)))
  | call f args =>
    change allFin _ (fun i => checkExpr tier (args i)) = .ok () ↔ _
    rw [allFin_iff]
    exact forall_congr' (fun i => expr_iff tier (args i))
termination_by structural e

def TargetP (tier : Tier) {X n} : Target X n → Prop
  | .«local» _ => True
  | .external ref => ExternalP tier ref.ty

def checkTarget (tier : Tier) {X n} : Target X n → Except Refusal Unit
  | .«local» _ => .ok ()
  | .external ref => admitExternal tier ref.ty

theorem target_iff (tier : Tier) {X n} (target : Target X n) :
    checkTarget tier target = .ok () ↔ TargetP tier target := by
  cases target with
  | «local» i => exact ⟨fun _ => True.intro, fun _ => rfl⟩
  | external ref => exact external_iff tier ref.ty

mutual
def StmtP (tier : Tier) {F X c n} (s : Stmt F X c n) : Prop := by
  apply Stmt.casesOn (motive_1 := fun _ _ _ _ _ => Prop) s
  case seq => intro F X c n a b; exact StmtP tier a ∧ StmtP tier b
  case assign =>
    intro F X c n r targets e
    exact (∀ i, TargetP tier (targets i)) ∧ ExprP tier e
  case discard => intro F X c n e; exact ExprP tier e
  case let_ => intro F X c n r e body; exact ExprP tier e ∧ StmtP tier body
  case zero => intro F X c n r body; exact StmtP tier body
  case if_ => intro F X c n e body; exact ExprP tier e ∧ StmtP tier body
  case switch =>
    intro F X c n e arms fallback
    exact ExprP tier e ∧ CasesP tier arms ∧ StmtP tier fallback
  case for_ =>
    intro F X c n pre cond post body
    exact StmtP tier pre ∧ ExprP tier cond ∧ StmtP tier post ∧ StmtP tier body
  case functions =>
    intro F X c n ss bodies rest
    exact BodiesP tier bodies ∧ StmtP tier rest
  all_goals intros; exact True
termination_by structural s

def CasesP (tier : Tier) {F X c n} (arms : Cases F X c n) : Prop := by
  apply Cases.casesOn (motive_2 := fun _ _ _ _ _ => Prop) arms
  case nil => intros; exact True
  case cons =>
    intro F X c n value body rest
    exact StmtP tier body ∧ CasesP tier rest
termination_by structural arms

def BodiesP (tier : Tier) {F X ss} (bodies : Bodies F X ss) : Prop := by
  apply Bodies.casesOn (motive_3 := fun _ _ _ _ => Prop) bodies
  case nil => intros; exact True
  case cons =>
    intro F X sig ss body rest
    exact StmtP tier body ∧ BodiesP tier rest
termination_by structural bodies
end

mutual
def checkStmt (tier : Tier) {F X c n} (s : Stmt F X c n) : Except Refusal Unit := by
  apply Stmt.casesOn (motive_1 := fun _ _ _ _ _ => Except Refusal Unit) s
  case seq =>
    intro F X c n first second
    exact do
      checkStmt tier first
      checkStmt tier second
  case assign =>
    intro F X c n r targets expression
    exact do
      allFin r (fun i => checkTarget tier (targets i))
      checkExpr tier expression
  case discard => intro F X c n e; exact checkExpr tier e
  case let_ =>
    intro F X c n r e body
    exact do
      checkExpr tier e
      checkStmt tier body
  case zero => intro F X c n r body; exact checkStmt tier body
  case if_ =>
    intro F X c n e body
    exact do
      checkExpr tier e
      checkStmt tier body
  case switch =>
    intro F X c n e arms fallback
    exact do
      checkExpr tier e
      checkCases tier arms
      checkStmt tier fallback
  case for_ =>
    intro F X c n pre cond post body
    exact do
      checkStmt tier pre
      checkExpr tier cond
      checkStmt tier post
      checkStmt tier body
  case functions =>
    intro F X c n ss bodies rest
    exact do
      checkBodies tier bodies
      checkStmt tier rest
  all_goals intros; exact .ok ()
termination_by structural s

def checkCases (tier : Tier) {F X c n} (arms : Cases F X c n) : Except Refusal Unit := by
  apply Cases.casesOn (motive_2 := fun _ _ _ _ _ => Except Refusal Unit) arms
  case nil => intros; exact .ok ()
  case cons =>
    intro F X c n value body rest
    exact do
      checkStmt tier body
      checkCases tier rest
termination_by structural arms

def checkBodies (tier : Tier) {F X ss} (bodies : Bodies F X ss) : Except Refusal Unit := by
  apply Bodies.casesOn (motive_3 := fun _ _ _ _ => Except Refusal Unit) bodies
  case nil => intros; exact .ok ()
  case cons =>
    intro F X sig ss body rest
    exact do
      checkStmt tier body
      checkBodies tier rest
termination_by structural bodies
end

syntax "tier_iff_go" : tactic
macro_rules
  | `(tactic| tier_iff_go) => `(tactic| repeat' (first
    | (assumption)
    | (exact ⟨fun _ => True.intro, fun _ => rfl⟩)
    | (apply expr_iff)
    | (apply target_iff)
    | (apply Iff.trans (bind_iff _ _))
    | (apply Iff.trans (allFin_iff _ _))
    | (apply and_congr)
    | (apply forall_congr')
    | (intro _)))

theorem stmt_iff (tier : Tier) {F X c n} (term : Stmt F X c n) :
    checkStmt tier term = .ok () ↔ StmtP tier term := by
  apply Stmt.rec
    (motive_1 := fun F X c n s => checkStmt tier s = .ok () ↔ StmtP tier s)
    (motive_2 := fun F X c n arms => checkCases tier arms = .ok () ↔ CasesP tier arms)
    (motive_3 := fun F X ss bodies => checkBodies tier bodies = .ok () ↔ BodiesP tier bodies)
    (t := term)
  all_goals intros
  all_goals tier_iff_go

theorem cases_iff (tier : Tier) {F X c n} (term : Cases F X c n) :
    checkCases tier term = .ok () ↔ CasesP tier term := by
  apply Cases.rec
    (motive_1 := fun F X c n s => checkStmt tier s = .ok () ↔ StmtP tier s)
    (motive_2 := fun F X c n arms => checkCases tier arms = .ok () ↔ CasesP tier arms)
    (motive_3 := fun F X ss bodies => checkBodies tier bodies = .ok () ↔ BodiesP tier bodies)
    (t := term)
  all_goals intros
  all_goals tier_iff_go

theorem bodies_iff (tier : Tier) {F X ss} (term : Bodies F X ss) :
    checkBodies tier term = .ok () ↔ BodiesP tier term := by
  apply Bodies.rec
    (motive_1 := fun F X c n s => checkStmt tier s = .ok () ↔ StmtP tier s)
    (motive_2 := fun F X c n arms => checkCases tier arms = .ok () ↔ CasesP tier arms)
    (motive_3 := fun F X ss bodies => checkBodies tier bodies = .ok () ↔ BodiesP tier bodies)
    (t := term)
  all_goals intros
  all_goals tier_iff_go

/-- General-block policy only. The existing canonical rethrow exception is
handled by the existing frontend; this checker does not change it. The caller
must establish the flag from separately checked metadata. It is not a proof
of MemOK preservation. -/
def checkGeneral (tier : Tier) (memorySafe : Bool) {X c n}
    (body : Stmt [] X c n) : Except Refusal Unit := do
  admitSafety memorySafe
  checkStmt tier body

theorem checkGeneral_iff (tier : Tier) (memorySafe : Bool) {X c n}
    (body : Stmt [] X c n) :
    checkGeneral tier memorySafe body = .ok () ↔ memorySafe = true ∧ StmtP tier body := by
  change (admitSafety memorySafe >>= fun _ => checkStmt tier body) = .ok () ↔ _
  rw [bind_iff, stmt_iff]
  apply and_congr _ Iff.rfl
  cases memorySafe <;> simp only [admitSafety, Bool.false_eq_true, ↓reduceIte, reduceCtorEq]

end Solidity.Yul.Policy
