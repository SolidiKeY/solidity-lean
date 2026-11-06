
import Solidity.Yul.ClosedFunctions

/-! Intrinsic effect-profile derivations for the no-Solidity-externals backfill.
These certify pure-word/pop builtin use, not whole-block source typing, name
freshness, duplicate-target/case validity, execution or compiler correspondence.
The existing AST remains in every derivation's index; no raw IR is introduced. -/
namespace Solidity.Yul.Closed

inductive WordBuiltinD : {a r : Nat} → Builtin a r → Type where
  | pure {a} (op : Pure a) : WordBuiltinD (.pure op)
  | pop : WordBuiltinD .pop

def checkWordBuiltin {a r} (b : Builtin a r) : Option (WordBuiltinD b) := by
  apply Builtin.casesOn (motive := fun _ _ b => Option (WordBuiltinD b)) b
  case pure => intro a op; exact some (WordBuiltinD.pure op)
  case pop => exact some .pop
  all_goals exact none

theorem WordBuiltinD.complete {a r b} (d : @WordBuiltinD a r b) :
    checkWordBuiltin b = some d := by
  cases d <;> rfl

/-- The builtin subset is exactly the existing tier-A builtin admission. No
new exclusion or unsupported effect semantics is hidden in this profile. -/
theorem checkWordBuiltin_iff {a r} (b : Builtin a r) :
    (checkWordBuiltin b).isSome = true ↔ b.checkTier .A = .ok () := by
  cases b with
  | pure op => cases op <;> exact ⟨fun _ => rfl, fun _ => rfl⟩
  | pop => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | _ => constructor <;> intro h <;> cases h

inductive WordExprD : {F : List Sig} → {n r : Nat} → Expr F [] n r → Type where
  | literal {F n w} : WordExprD (Expr.literal (F := F) (X := []) (n := n) w)
  | local {F n} (i : Fin n) : WordExprD (Expr.local (F := F) (X := []) i)
  | builtin {F n a r} {b : Builtin a r} {args : Fin a → Expr F [] n 1} :
      WordBuiltinD b → (∀ i, WordExprD (args i)) → WordExprD (.builtin b args)
  | call {F n sig} {args : Fin sig.args → Expr F [] n 1} (f : Member F sig) :
      (∀ i, WordExprD (args i)) → WordExprD (.call f args)

mutual
inductive WordStmtD : {F : List Sig} → {c : Control} → {n : Nat} → Stmt F [] c n → Type where
  | skip {F c n} : WordStmtD (Stmt.skip (F := F) (X := []) (c := c) (n := n))
  | seq {F c n} {s t : Stmt F [] c n} : WordStmtD s → WordStmtD t → WordStmtD (.seq s t)
  | assign {F c n r} {targets : Fin r → Target [] n} {e : Expr F [] n r} :
      WordExprD e → WordStmtD (Stmt.assign (c := c) targets e)
  | discard {F c n} {e : Expr F [] n 0} :
      WordExprD e → WordStmtD (Stmt.discard (c := c) e)
  | let_ {F c n r} {e : Expr F [] n r} {body : Stmt F [] c (r + n)} :
      WordExprD e → WordStmtD body → WordStmtD (.let_ r e body)
  | zero {F c n r} {body : Stmt F [] c (r + n)} :
      WordStmtD body → WordStmtD (.zero r body)
  | if_ {F c n} {e : Expr F [] n 1} {body : Stmt F [] c n} :
      WordExprD e → WordStmtD body → WordStmtD (.if_ e body)
  | switch {F c n} {e : Expr F [] n 1} {cases : Cases F [] c n} {fallback : Stmt F [] c n} :
      WordExprD e → WordCasesD cases → WordStmtD fallback → WordStmtD (.switch e cases fallback)
  | for_ {F c n} {pre : Stmt F [] ⟨c.function, false⟩ n} {condition : Expr F [] n 1}
      {post : Stmt F [] ⟨c.function, false⟩ n} {body : Stmt F [] ⟨c.function, true⟩ n} :
      WordStmtD pre → WordExprD condition → WordStmtD post → WordStmtD body →
        WordStmtD (Stmt.for_ (c := c) pre condition post body)
  | leave {F loop n} : WordStmtD (Stmt.leave (F := F) (X := []) (l := loop) (n := n))
  | break_ {F function n} : WordStmtD (Stmt.break_ (F := F) (X := []) (f := function) (n := n))
  | continue_ {F function n} : WordStmtD (Stmt.continue_ (F := F) (X := []) (f := function) (n := n))
  | functions {F c n signatures} {bodies : Bodies (signatures ++ F) [] signatures}
      {rest : Stmt (signatures ++ F) [] c n} :
      WordBodiesD bodies → WordStmtD rest → WordStmtD (Stmt.functions signatures bodies rest)

inductive WordCasesD : {F : List Sig} → {c : Control} → {n : Nat} → Cases F [] c n → Type where
  | nil {F c n} : WordCasesD (Cases.nil (F := F) (X := []) (c := c) (n := n))
  | cons {F c n w} {body : Stmt F [] c n} {rest : Cases F [] c n} :
      WordStmtD body → WordCasesD rest → WordCasesD (.cons w body rest)

inductive WordBodiesD : {F signatures : List Sig} → Bodies F [] signatures → Type where
  | nil {F} : WordBodiesD (Bodies.nil (F := F) (G := []))
  | cons {F signatures} {sig : Sig} {body : Stmt F [] ⟨true, false⟩ (sig.args + sig.rets)}
      {rest : Bodies F [] signatures} :
      WordStmtD body → WordBodiesD rest → WordBodiesD (.cons body rest)
end

inductive WordEnvD : {F : List Sig} → FunctionEnv F → Type where
  | nil : WordEnvD .nil
  | group {F signatures} {outer : FunctionEnv F} {bodies : Bodies (signatures ++ F) [] signatures} :
      WordEnvD outer → WordBodiesD bodies → WordEnvD (.group signatures outer bodies)

structure WordEnvironment (F : List Sig) where
  environment : FunctionEnv F
  derivation : WordEnvD environment

structure WordClosure (sig : Sig) where
  closure : Closure sig
  environment : WordEnvD closure.environment
  body : WordStmtD closure.body

def WordHeadResult (F : List Sig) (signatures : List Sig) :
    Bodies F [] signatures → Type :=
  match signatures with
  | [] => fun _ => Unit
  | _ :: _ => fun bodies => WordStmtD (bodyHead bodies)

def WordTailResult (F : List Sig) (signatures : List Sig) :
    Bodies F [] signatures → Type :=
  match signatures with
  | [] => fun _ => Unit
  | _ :: _ => fun bodies => WordBodiesD (bodyTail bodies)

def wordBodyHead {F signatures} {bodies : Bodies F [] signatures} (d : WordBodiesD bodies) :
    WordHeadResult F signatures bodies :=
  WordBodiesD.casesOn (motive_3 := fun {F signatures} bodies _ => WordHeadResult F signatures bodies) d
    (nil := ())
    (cons := fun body _ => body)

def wordBodyTail {F signatures} {bodies : Bodies F [] signatures} (d : WordBodiesD bodies) :
    WordTailResult F signatures bodies :=
  WordBodiesD.casesOn (motive_3 := fun {F signatures} bodies _ => WordTailResult F signatures bodies) d
    (nil := ())
    (cons := fun _ rest => rest)

def wordBodyAt {F signatures sig} (i : Member signatures sig) {bodies : Bodies F [] signatures}
    (d : WordBodiesD bodies) : WordStmtD (bodyAt i bodies) :=
  Member.casesOn (motive := fun signatures _sig i =>
    {bodies : Bodies F [] signatures} → WordBodiesD bodies → WordStmtD (bodyAt i bodies)) i
    (here := fun {_ _} {_} d => wordBodyHead d)
    (there := fun {_ _ _} j {_} d => wordBodyAt j (wordBodyTail d))
    d
termination_by structural i

/-- Selecting a pure-word body retains its profile derivation and complete
lexical profile environment. This does not execute the selected code. -/
def lookupWord {F} {environment : FunctionEnv F} (d : WordEnvD environment) {sig}
    (i : Member F sig) : WordClosure sig :=
  WordEnvD.casesOn
    (motive := fun {F} _ _ => {sig : Sig} → Member F sig → WordClosure sig) d
    (nil := fun {_} i => PEmpty.elim (peelMember i))
    (group := fun {F signatures outer bodies} outerD bodiesD {_} i =>
      match splitMember signatures F i with
      | .inl j =>
          ⟨⟨_, .group signatures outer bodies, bodyAt j bodies⟩, .group outerD bodiesD,
            wordBodyAt j bodiesD⟩
      | .inr j => lookupWord outerD j)
    i
termination_by structural d


def WordBuiltinD.eval {a r b} (d : @WordBuiltinD a r b) : (Fin a → Word) → Fin r → Word :=
  WordBuiltinD.casesOn (motive := fun {a r} _ _ => (Fin a → Word) → Fin r → Word) d
    (pure := fun {_} op inputs _ => op.eval inputs)
    (pop := fun _ => Fin.elim0)

theorem WordBuiltinD.eval_pure {a} (op : Pure a) (inputs : Fin a → Word) :
    (WordBuiltinD.pure op).eval inputs 0 = op.eval inputs := rfl

theorem lookupWord_group {F signatures sig} {outer : FunctionEnv F}
    {bodies : Bodies (signatures ++ F) [] signatures}
    (outerD : WordEnvD outer) (bodiesD : WordBodiesD bodies) (i : Member (signatures ++ F) sig) :
    lookupWord (.group outerD bodiesD) i =
      (match splitMember signatures F i with
       | .inl j => ⟨⟨_, .group signatures outer bodies, bodyAt j bodies⟩,
           .group outerD bodiesD, wordBodyAt j bodiesD⟩
       | .inr j => lookupWord outerD j) := rfl

/-- Pure closure selection preserves the actual underlying lexical closure,
rather than selecting another body with the same signature. -/
theorem lookupWord_eq_lookup {F} {environment : FunctionEnv F} (d : WordEnvD environment)
    {sig} (i : Member F sig) : (lookupWord d i).closure = lookup environment i := by
  cases d with
  | nil => exact PEmpty.elim (peelMember i)
  | @group F signatures outer bodies outerD bodiesD =>
      rw [lookupWord_group, lookup_group]
      cases hs : splitMember signatures F i with
      | inl j => rfl
      | inr j => exact lookupWord_eq_lookup outerD j
termination_by structural d



theorem WordBuiltinD.unique {a r b} (left right : @WordBuiltinD a r b) : left = right :=
  Option.some.inj (left.complete.symm.trans right.complete)


end Solidity.Yul.Closed
