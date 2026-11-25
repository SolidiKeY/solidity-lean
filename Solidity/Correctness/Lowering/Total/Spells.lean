import Solidity.Correctness.Lowering.Total.Decode.Tables
import Solidity.Source.Unique

/-!
# Loop lowering: parameterized spelling

One inductive spelling relation checks the recursion and inference of every
`Decode.Tables` version. It shares the decoder tables and spelling choices;
it does not establish their semantic faithfulness. The original API below
specializes this relation to `Decode.tables1`. Completeness retains the
explicit Source-inference completeness premise.
-/
namespace Solidity.Correctness.Lowering.Total

namespace Spells
open Source (Syn SCtx STy)
open Decode (num uintElem intElem unbrace)

/-- Split the binds of a decoder equation. -/
local macro "bind_simp" " at " h:ident : tactic =>
  `(tactic| simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.map_eq_some_iff, Option.some.injEq, reduceCtorEq, exists_const, false_and,
      exists_false] at $h:ident)

/-- Unfold one decoder equation and split its binds. -/
local macro "spell_simp " f:ident " at " h:ident : tactic =>
  `(tactic| simp only [$f:ident, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.map_eq_some_iff, Option.some.injEq, reduceCtorEq, exists_const, false_and,
      exists_false] at $h:ident)

/-! ### Decoder versions

The same relation for `Decode.Tables.decode`, the generic decoder: the rules
for a declaration's type and for an environment read are by the version's
tables. The relation uses the version's own tables, so it checks the recursion
and inference of the version's decoder, not its tables. -/

variable {T : Decode.Tables}

mutual
inductive ExprT (T : Decode.Tables) : RawExpr → Syn .expr → Prop where
  | num (n : Nat) : ExprT T (.num n) (num n)
  | name (x : String) : ExprT T (.name x) (.ident x)
  | bool (b : Bool) : ExprT T (.bool b) (.lit (.bool b))
  | field {e e'} (f : String) : ExprT T e e' → ExprT T (.field e f) (.member e' f)
  | index {e e' k k'} : ExprT T e e' → ExprT T k k' → ExprT T (.index e k) (.index e' (.some k'))
  | binop {op f a a' b b' t} : Decode.binop op = some f → ExprT T a a' → ExprT T b b' →
      t = f a' b' → ExprT T (.binop op a b) t
  | neg {a a'} : ExprT T a a' → ExprT T (.unop .neg a) (.unaryPrefix .neg a')
  | not {a a'} : ExprT T a a' → ExprT T (.unop .not a) (.unaryPrefix .not a')
  | bnot {a a'} : ExprT T a a' → ExprT T (.unop .bnot a) (.unaryPrefix .bitNot a')
  | toInt {a a'} : ExprT T a a' → ExprT T (.unop .toInt a)
      (.call (.elemType intElem (by decide)) (.positional (.cons a' .nil)))
  | toUint {a a'} : ExprT T a a' → ExprT T (.unop .toUint a)
      (.call (.elemType uintElem (by decide)) (.positional (.cons a' .nil)))
  | ternary {c c' a a' b b'} : ExprT T c c' → ExprT T a a' → ExprT T b b' →
      ExprT T (.ternary c a b) (.cond c' a' b')
  | preInc {e e'} : ExprT T e e' → ExprT T (.incDec .preInc e) (.unaryPrefix .inc e')
  | preDec {e e'} : ExprT T e e' → ExprT T (.incDec .preDec e) (.unaryPrefix .dec e')
  | postInc {e e'} : ExprT T e e' → ExprT T (.incDec .postInc e) (.unarySuffix .inc e')
  | postDec {e e'} : ExprT T e e' → ExprT T (.incDec .postDec e) (.unarySuffix .dec e')
  | call {args args'} (f : String) : ExprsT T args args' →
      ExprT T (.call f args) (.call (.ident f) (.positional args'))
  | modular {a a' b b' k k'} (op : ModOp) : ExprT T a a' → ExprT T b b' → ExprT T k k' →
      ExprT T (.modular op a b k)
        (.call (.ident op.toStr) (.positional (.cons a' (.cons b' (.cons k' .nil)))))
  | env {k t} : T.env k = some t → ExprT T (.env k) t
  | tuple {a a' b b' rest rest'} : ExprT T a a' → ExprT T b b' → ComponentsT T rest rest' →
      ExprT T (.tuple (a :: b :: rest)) (.tuple (.some a') (.cons (.some b') rest'))
  | assign {l l' r r'} : ExprT T l l' → ExprT T r r' → ExprT T (.assign l r) (.assign .assign l' r')
  | opAssign {op o l l' r r'} : Decode.assignOp op = some o → ExprT T l l' → ExprT T r r' →
      ExprT T (.opAssign op l r) (.assign o l' r')
inductive ExprsT (T : Decode.Tables) : List RawExpr → Syn (.list .expr) → Prop where
  | nil : ExprsT T [] .nil
  | cons {e e' es es'} : ExprT T e e' → ExprsT T es es' → ExprsT T (e :: es) (.cons e' es')
inductive ComponentsT (T : Decode.Tables) : List RawExpr → Syn (.list (.opt .expr)) → Prop where
  | nil : ComponentsT T [] .nil
  | cons {e e' es es'} : ExprT T e e' → ComponentsT T es es' →
      ComponentsT T (e :: es) (.cons (.some e') es')
end

mutual
theorem ExprT.decode : ∀ {e t}, ExprT T e t → T.expr e = some t
  | _, _, .num _ | _, _, .name _ | _, _, .bool _ => by simp [Decode.Tables.expr]
  | _, _, .field _ h => by simp [Decode.Tables.expr, h.decode]
  | _, _, .index h k => by simp [Decode.Tables.expr, h.decode, k.decode]
  | _, _, .binop o h k e => by simp [Decode.Tables.expr, o, h.decode, k.decode, e]
  | _, _, .neg h | _, _, .not h | _, _, .bnot h | _, _, .toInt h | _, _, .toUint h
  | _, _, .preInc h | _, _, .preDec h | _, _, .postInc h | _, _, .postDec h => by
      simp [Decode.Tables.expr, h.decode]
  | _, _, .ternary c a b => by simp [Decode.Tables.expr, c.decode, a.decode, b.decode]
  | _, _, .call _ h => by simp [Decode.Tables.expr, h.decode]
  | _, _, .modular _ a b k => by simp [Decode.Tables.expr, a.decode, b.decode, k.decode]
  | _, _, .env h => by simp [Decode.Tables.expr, h]
  | _, _, .tuple a b r => by simp [Decode.Tables.expr, a.decode, b.decode, r.decode]
  | _, _, .assign l r => by simp [Decode.Tables.expr, l.decode, r.decode]
  | _, _, .opAssign o l r => by simp [Decode.Tables.expr, o, l.decode, r.decode]
theorem ExprsT.decode : ∀ {es t}, ExprsT T es t → T.exprs es = some t
  | _, _, .nil => by simp [Decode.Tables.exprs]
  | _, _, .cons h k => by simp [Decode.Tables.exprs, h.decode, k.decode]
theorem ComponentsT.decode : ∀ {es t}, ComponentsT T es t → T.components es = some t
  | _, _, .nil => by simp [Decode.Tables.components]
  | _, _, .cons h k => by simp [Decode.Tables.components, h.decode, k.decode]
end

mutual
theorem expr_spellsT : (e : RawExpr) → (t : Syn .expr) → T.expr e = some t → ExprT T e t
  | .num n, t, h => by spell_simp Decode.Tables.expr at h; subst h; exact .num n
  | .name x, t, h => by spell_simp Decode.Tables.expr at h; subst h; exact .name x
  | .bool b, t, h => by spell_simp Decode.Tables.expr at h; subst h; exact .bool b
  | .field e f, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨a, ha, rfl⟩ := h; exact .field f (expr_spellsT _ _ ha)
  | .index e k, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact .index (expr_spellsT _ _ ha) (expr_spellsT _ _ hb)
  | .binop op a b, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨f, hf, a', ha, b', hb, rfl⟩ := h
      exact .binop hf (expr_spellsT _ _ ha) (expr_spellsT _ _ hb) rfl
  | .unop .neg a, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .neg (expr_spellsT _ _ ha)
  | .unop .not a, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .not (expr_spellsT _ _ ha)
  | .unop .bnot a, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .bnot (expr_spellsT _ _ ha)
  | .unop .toInt a, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .toInt (expr_spellsT _ _ ha)
  | .unop .toUint a, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .toUint (expr_spellsT _ _ ha)
  | .ternary c a b, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨c', hc, a', ha, b', hb, rfl⟩ := h
      exact .ternary (expr_spellsT _ _ hc) (expr_spellsT _ _ ha) (expr_spellsT _ _ hb)
  | .incDec .preInc e, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .preInc (expr_spellsT _ _ ha)
  | .incDec .preDec e, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .preDec (expr_spellsT _ _ ha)
  | .incDec .postInc e, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .postInc (expr_spellsT _ _ ha)
  | .incDec .postDec e, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .postDec (expr_spellsT _ _ ha)
  | .call f args, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .call f (exprs_spellsT _ _ ha)
  | .modular op a b k, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨a', ha, b', hb, k', hk, rfl⟩ := h
      exact .modular op (expr_spellsT _ _ ha) (expr_spellsT _ _ hb) (expr_spellsT _ _ hk)
  | .env k, t, h => by spell_simp Decode.Tables.expr at h; exact .env h
  | .tuple (a :: b :: rest), t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨a', ha, b', hb, r', hr, rfl⟩ := h
      exact .tuple (expr_spellsT _ _ ha) (expr_spellsT _ _ hb) (components_spellsT _ _ hr)
  | .assign l r, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨l', hl, r', hr, rfl⟩ := h
      exact .assign (expr_spellsT _ _ hl) (expr_spellsT _ _ hr)
  | .opAssign op l r, t, h => by
      spell_simp Decode.Tables.expr at h; obtain ⟨o, ho, l', hl, r', hr, rfl⟩ := h
      exact .opAssign ho (expr_spellsT _ _ hl) (expr_spellsT _ _ hr)
  | .newArr .., _, h | .named .., _, h | .tuple [], _, h | .tuple [_], _, h => by
      spell_simp Decode.Tables.expr at h
theorem exprs_spellsT : (es : List RawExpr) → (t : Syn (.list .expr)) →
    T.exprs es = some t → ExprsT T es t
  | [], t, h => by spell_simp Decode.Tables.exprs at h; subst h; exact .nil
  | e :: es, t, h => by
      spell_simp Decode.Tables.exprs at h; obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact .cons (expr_spellsT _ _ ha) (exprs_spellsT _ _ hb)
theorem components_spellsT : (es : List RawExpr) → (t : Syn (.list (.opt .expr))) →
    T.components es = some t → ComponentsT T es t
  | [], t, h => by spell_simp Decode.Tables.components at h; subst h; exact .nil
  | e :: es, t, h => by
      spell_simp Decode.Tables.components at h; obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact .cons (expr_spellsT _ _ ha) (components_spellsT _ _ hb)
end

/-- Simple statements of a decoder version. -/
inductive SimpleT (T : Decode.Tables) : RawStmt → Syn .simple → Prop where
  | assign {l l' r r'} : ExprT T l l' → ExprT T r r' →
      SimpleT T (.assign l r) (.exprStmt (.assign .assign l' r'))
  | declNone {U T'} (x : String) : T.typeName U = some T' →
      SimpleT T (.decl U x none) (.declVar (.varDecl T' none x) .none)
  | declSome {U T' e e'} (x : String) : T.typeName U = some T' → ExprT T e e' →
      SimpleT T (.decl U x (some e)) (.declVar (.varDecl T' none x) (.some e'))
  | opAssign {op o l l' r r'} : Decode.assignOp op = some o → ExprT T l l' → ExprT T r r' →
      SimpleT T (.opAssign op l r) (.exprStmt (.assign o l' r'))
  | incDec {op l t} : ExprT T (.incDec op l) t → SimpleT T (.incDec op l) (.exprStmt t)
  | require {c c'} : ExprT T c c' →
      SimpleT T (.require c) (.exprStmt (.call (.ident "require") (.positional (.cons c' .nil))))
  | assert {c c'} : ExprT T c c' →
      SimpleT T (.assert c) (.exprStmt (.call (.ident "assert") (.positional (.cons c' .nil))))
  | revert : SimpleT T .revert (.exprStmt (.call (.ident "revert") (.positional .nil)))

theorem SimpleT.decode {s t} (h : SimpleT T s t) : T.simple s = some t := by
  cases h with
  | assign l r => simp [Decode.Tables.simple, Decode.Tables.WithExpr.simple, l.decode, r.decode]
  | declNone x hU => simp [Decode.Tables.simple, Decode.Tables.WithExpr.simple, hU]
  | declSome x hU e => simp [Decode.Tables.simple, Decode.Tables.WithExpr.simple, hU, e.decode]
  | opAssign o l r => simp [Decode.Tables.simple, Decode.Tables.WithExpr.simple, o, l.decode, r.decode]
  | incDec e => simp [Decode.Tables.simple, Decode.Tables.WithExpr.simple, e.decode]
  | require c => simp [Decode.Tables.simple, Decode.Tables.WithExpr.simple, c.decode]
  | assert c => simp [Decode.Tables.simple, Decode.Tables.WithExpr.simple, c.decode]
  | revert => simp [Decode.Tables.simple, Decode.Tables.WithExpr.simple]

theorem simple_spellsT (s : RawStmt) (t : Syn .simple) (h : T.simple s = some t) :
    SimpleT T s t := by
  cases s with
  | assign l r =>
      simp only [Decode.Tables.simple] at h; spell_simp Decode.Tables.WithExpr.simple at h; obtain ⟨l', hl, r', hr, rfl⟩ := h
      exact .assign (expr_spellsT _ _ hl) (expr_spellsT _ _ hr)
  | decl U x init =>
      cases init with
      | none => simp only [Decode.Tables.simple] at h; spell_simp Decode.Tables.WithExpr.simple at h; obtain ⟨T', hT, rfl⟩ := h; exact .declNone x hT
      | some e =>
        simp only [Decode.Tables.simple] at h; spell_simp Decode.Tables.WithExpr.simple at h; obtain ⟨T', hT, e', he, rfl⟩ := h
        exact .declSome x hT (expr_spellsT _ _ he)
  | opAssign op l r =>
      simp only [Decode.Tables.simple] at h; spell_simp Decode.Tables.WithExpr.simple at h; obtain ⟨o, ho, l', hl, r', hr, rfl⟩ := h
      exact .opAssign ho (expr_spellsT _ _ hl) (expr_spellsT _ _ hr)
  | incDec op l =>
      simp only [Decode.Tables.simple] at h; spell_simp Decode.Tables.WithExpr.simple at h; obtain ⟨a, ha, rfl⟩ := h; exact .incDec (expr_spellsT _ _ ha)
  | require c =>
      simp only [Decode.Tables.simple] at h; spell_simp Decode.Tables.WithExpr.simple at h; obtain ⟨a, ha, rfl⟩ := h; exact .require (expr_spellsT _ _ ha)
  | assert c =>
      simp only [Decode.Tables.simple] at h; spell_simp Decode.Tables.WithExpr.simple at h; obtain ⟨a, ha, rfl⟩ := h; exact .assert (expr_spellsT _ _ ha)
  | revert => simp only [Decode.Tables.simple] at h; spell_simp Decode.Tables.WithExpr.simple at h; subst h; exact .revert
  | _ => simp [Decode.Tables.simple, Decode.Tables.WithExpr.simple] at h

/-- A `for` initializer: none, or one simple statement. -/
inductive InitT (T : Decode.Tables) : List RawStmt → Syn (.opt .simple) → Prop where
  | absent : InitT T [] .none
  | one {s t} : SimpleT T s t → InitT T [s] (.some t)

/-- A `for` update: none, or one assignment or update expression. -/
inductive UpdT (T : Decode.Tables) : List RawStmt → Syn (.opt .expr) → Prop where
  | absent : UpdT T [] .none
  | assign {l l' r r'} : ExprT T l l' → ExprT T r r' → UpdT T [.assign l r] (.some (.assign .assign l' r'))
  | opAssign {op o l l' r r'} : Decode.assignOp op = some o → ExprT T l l' → ExprT T r r' →
      UpdT T [.opAssign op l r] (.some (.assign o l' r'))
  | incDec {op l t} : ExprT T (.incDec op l) t → UpdT T [.incDec op l] (.some t)

/-- A `for` condition, absent or present. -/
inductive CondT (T : Decode.Tables) : Option RawExpr → Syn (.opt .expr) → Prop where
  | absent : CondT T none .none
  | present {c c'} : ExprT T c c' → CondT T (some c) (.some c')

mutual
/-- Statements in a control context. -/
inductive StmtT (T : Decode.Tables) : (k : SCtx) → RawStmt → Syn (.stmt k) → Prop where
  | ite {k c c' thn thn'} : ExprT T c c' → ItemsT T k thn thn' →
      StmtT T k (.ite c thn []) (.ifStmt c' (unbrace thn') .none)
  | iteElse {k c c' thn thn' e els els'} : ExprT T c c' → ItemsT T k thn thn' →
      ItemsT T k (e :: els) els' →
      StmtT T k (.ite c thn (e :: els)) (.ifStmt c' (unbrace thn') (.some (unbrace els')))
  | retNone {k} : StmtT T k (.ret none) (.returnStmt .none)
  | retSome {k e e'} : ExprT T e e' → StmtT T k (.ret (some e)) (.returnStmt (.some e'))
  | block {k b b'} : ItemsT T k b b' → StmtT T k (.block b) (.blockStmt (.block b'))
  | whileLoop {l u c c' b b'} (spec : RawLoopSpec) : ExprT T c c' → ItemsT T ⟨true, u⟩ b b' →
      StmtT T ⟨l, u⟩ (.whileLoop spec c b) (.whileStmt c' (unbrace b'))
  | loop {l u c c' b b'} (spec : RawLoopSpec) : ExprT T c c' → ItemsT T ⟨true, u⟩ b b' →
      StmtT T ⟨l, u⟩ (.loop spec c b) (.whileStmt c' (unbrace b'))
  | doWhile {l u c c' b b'} (spec : RawLoopSpec) : ItemsT T ⟨true, u⟩ b b' → ExprT T c c' →
      StmtT T ⟨l, u⟩ (.doWhile spec b c) (.doWhile (unbrace b') c')
  | forLoop {l u init init' c c' upd upd' b b'} (spec : RawLoopSpec) : InitT T init init' →
      CondT T c c' → UpdT T upd upd' → ItemsT T ⟨true, u⟩ b b' →
      StmtT T ⟨l, u⟩ (.forLoop spec init c upd b) (.forStmt init' c' upd' (unbrace b'))
  | brk {u} : StmtT T ⟨true, u⟩ .brk .breakStmt
  | cont {u} : StmtT T ⟨true, u⟩ .cont .continueStmt
  | simple {k s t} : SimpleT T s t → StmtT T k s (.simpleStmt t)
/-- The items of a block; an `unchecked` block only in a checked context. -/
inductive ItemsT (T : Decode.Tables) : (k : SCtx) → List RawStmt → Syn (.list (.item k)) → Prop where
  | nil {k} : ItemsT T k [] .nil
  | unchecked {l b b' rest rest'} : ItemsT T ⟨l, true⟩ b b' → ItemsT T ⟨l, false⟩ rest rest' →
      ItemsT T ⟨l, false⟩ (.unchecked b :: rest) (.cons (.uncheckedItem (.block b')) rest')
  | stmt {k s s' rest rest'} : StmtT T k s s' → ItemsT T k rest rest' →
      ItemsT T k (s :: rest) (.cons (.stmtItem s') rest')
end

theorem InitT.decode {b t} (h : InitT T b t) : T.initializer b = some t := by
  cases h with
  | absent => rfl
  | one s => simp [Decode.Tables.initializer, Decode.Tables.WithExpr.initializer, s.decode]

theorem init_spellsT (b : List RawStmt) (t : Syn (.opt .simple))
    (h : T.initializer b = some t) : InitT T b t := by
  match b, h with
  | [], h => simp only [Decode.Tables.initializer] at h; spell_simp Decode.Tables.WithExpr.initializer at h; subst h; exact .absent
  | [s], h =>
    simp only [Decode.Tables.initializer] at h; spell_simp Decode.Tables.WithExpr.initializer at h; obtain ⟨a, ha, rfl⟩ := h; exact .one (simple_spellsT _ _ ha)
  | _ :: _ :: _, h => simp [Decode.Tables.initializer, Decode.Tables.WithExpr.initializer] at h

theorem UpdT.decode {b t} (h : UpdT T b t) : T.update b = some t := by
  cases h with
  | absent => rfl
  | assign l r => simp [Decode.Tables.update, Decode.Tables.WithExpr.update, l.decode, r.decode]
  | opAssign o l r => simp [Decode.Tables.update, Decode.Tables.WithExpr.update, o, l.decode, r.decode]
  | incDec e => simp [Decode.Tables.update, Decode.Tables.WithExpr.update, e.decode]

theorem upd_spellsT (b : List RawStmt) (t : Syn (.opt .expr)) (h : T.update b = some t) :
    UpdT T b t := by
  unfold Decode.Tables.update Decode.Tables.WithExpr.update at h
  split at h
  · cases h; exact .absent
  · bind_simp at h; obtain ⟨l', hl, r', hr, rfl⟩ := h
    exact .assign (expr_spellsT _ _ hl) (expr_spellsT _ _ hr)
  · bind_simp at h; obtain ⟨o, ho, l', hl, r', hr, rfl⟩ := h
    exact .opAssign ho (expr_spellsT _ _ hl) (expr_spellsT _ _ hr)
  · bind_simp at h; obtain ⟨a, ha, rfl⟩ := h; exact .incDec (expr_spellsT _ _ ha)
  · cases h

mutual
theorem StmtT.decode : ∀ {k s t}, StmtT T k s t → T.stmt k s = some t
  | _, _, _, .ite c thn => by simp [Decode.Tables.stmt, Decode.Tables.WithExpr.stmt, c.decode, thn.decode]
  | _, _, _, .iteElse c thn els => by simp [Decode.Tables.stmt, Decode.Tables.WithExpr.stmt, c.decode, thn.decode, els.decode]
  | _, _, _, .retNone => by simp [Decode.Tables.stmt, Decode.Tables.WithExpr.stmt]
  | _, _, _, .retSome e => by simp [Decode.Tables.stmt, Decode.Tables.WithExpr.stmt, e.decode]
  | _, _, _, .block b => by simp [Decode.Tables.stmt, Decode.Tables.WithExpr.stmt, b.decode]
  | _, _, _, .whileLoop _ c b | _, _, _, .loop _ c b => by
      simp [Decode.Tables.stmt, Decode.Tables.WithExpr.stmt, c.decode, b.decode]
  | _, _, _, .doWhile _ b c => by simp [Decode.Tables.stmt, Decode.Tables.WithExpr.stmt, c.decode, b.decode]
  | _, _, _, .forLoop _ i c u b => by
      cases c with
      | absent => simp [Decode.Tables.stmt, Decode.Tables.WithExpr.stmt, i.decode, u.decode, b.decode]
      | present c => simp [Decode.Tables.stmt, Decode.Tables.WithExpr.stmt, i.decode, u.decode, b.decode, c.decode]
  | _, _, _, .brk | _, _, _, .cont => by simp [Decode.Tables.stmt, Decode.Tables.WithExpr.stmt, Decode.jump]
  | _, _, _, .simple h => by
      have e := h.decode
      cases h <;> simp [Decode.Tables.stmt, Decode.Tables.WithExpr.stmt, e]
theorem ItemsT.decode : ∀ {k b t}, ItemsT T k b t → T.items k b = some t
  | _, _, _, .nil => by simp [Decode.Tables.items, Decode.Tables.WithExpr.items]
  | _, _, _, .unchecked b rest => by
      simp [Decode.Tables.items, Decode.Tables.WithExpr.items, b.decode, rest.decode, Decode.uncheckedItem]
  | _, _, _, .stmt s rest => by
      have e := s.decode
      have e' := rest.decode
      cases s with
      | simple h => cases h <;> simp [Decode.Tables.items, Decode.Tables.WithExpr.items, e, e']
      | _ => simp [Decode.Tables.items, Decode.Tables.WithExpr.items, e, e']
end

mutual
theorem stmt_spellsT : (k : SCtx) → (s : RawStmt) → (t : Syn (.stmt k)) →
    T.stmt k s = some t → StmtT T k s t
  | k, .ite c thn [], t, h => by
      simp only [Decode.Tables.stmt] at h; spell_simp Decode.Tables.WithExpr.stmt at h; obtain ⟨c', hc, thn', ht, rfl⟩ := h
      exact .ite (expr_spellsT _ _ hc) (items_spellsT _ _ _ ht)
  | k, .ite c thn (e :: els), t, h => by
      simp only [Decode.Tables.stmt] at h; spell_simp Decode.Tables.WithExpr.stmt at h; obtain ⟨c', hc, thn', ht, els', he, rfl⟩ := h
      exact .iteElse (expr_spellsT _ _ hc) (items_spellsT _ _ _ ht) (items_spellsT _ _ _ he)
  | k, .ret none, t, h => by simp only [Decode.Tables.stmt] at h; spell_simp Decode.Tables.WithExpr.stmt at h; subst h; exact .retNone
  | k, .ret (some e), t, h => by
      simp only [Decode.Tables.stmt] at h; spell_simp Decode.Tables.WithExpr.stmt at h; obtain ⟨e', he, rfl⟩ := h; exact .retSome (expr_spellsT _ _ he)
  | k, .block b, t, h => by
      simp only [Decode.Tables.stmt] at h; spell_simp Decode.Tables.WithExpr.stmt at h; obtain ⟨b', hb, rfl⟩ := h; exact .block (items_spellsT _ _ _ hb)
  | ⟨l, u⟩, .whileLoop spec c b, t, h => by
      simp only [Decode.Tables.stmt] at h; spell_simp Decode.Tables.WithExpr.stmt at h; obtain ⟨c', hc, b', hb, rfl⟩ := h
      exact .whileLoop spec (expr_spellsT _ _ hc) (items_spellsT _ _ _ hb)
  | ⟨l, u⟩, .loop spec c b, t, h => by
      simp only [Decode.Tables.stmt] at h; spell_simp Decode.Tables.WithExpr.stmt at h; obtain ⟨c', hc, b', hb, rfl⟩ := h
      exact .loop spec (expr_spellsT _ _ hc) (items_spellsT _ _ _ hb)
  | ⟨l, u⟩, .doWhile spec b c, t, h => by
      simp only [Decode.Tables.stmt] at h; spell_simp Decode.Tables.WithExpr.stmt at h; obtain ⟨b', hb, c', hc, rfl⟩ := h
      exact .doWhile spec (items_spellsT _ _ _ hb) (expr_spellsT _ _ hc)
  | ⟨l, u⟩, .forLoop spec init none upd b, t, h => by
      simp only [Decode.Tables.stmt] at h; spell_simp Decode.Tables.WithExpr.stmt at h; obtain ⟨i', hi, _, rfl, u', hu, b', hb, rfl⟩ := h
      exact .forLoop spec (init_spellsT _ _ hi) .absent (upd_spellsT _ _ hu) (items_spellsT _ _ _ hb)
  | ⟨l, u⟩, .forLoop spec init (some c) upd b, t, h => by
      simp only [Decode.Tables.stmt] at h; spell_simp Decode.Tables.WithExpr.stmt at h; obtain ⟨i', hi, _, ⟨c', hc, rfl⟩, u', hu, b', hb, rfl⟩ := h
      exact .forLoop spec (init_spellsT _ _ hi) (.present (expr_spellsT _ _ hc)) (upd_spellsT _ _ hu)
        (items_spellsT _ _ _ hb)
  | ⟨true, u⟩, .brk, t, h => by simp [Decode.Tables.stmt, Decode.Tables.WithExpr.stmt, Decode.jump] at h; subst h; exact .brk
  | ⟨false, u⟩, .brk, t, h => by simp [Decode.Tables.stmt, Decode.Tables.WithExpr.stmt, Decode.jump] at h
  | ⟨true, u⟩, .cont, t, h => by simp [Decode.Tables.stmt, Decode.Tables.WithExpr.stmt, Decode.jump] at h; subst h; exact .cont
  | ⟨false, u⟩, .cont, t, h => by simp [Decode.Tables.stmt, Decode.Tables.WithExpr.stmt, Decode.jump] at h
  | k, s@(.assign ..), t, h | k, s@(.decl ..), t, h | k, s@(.declStorage ..), t, h
  | k, s@(.declMemory ..), t, h | k, s@(.delete ..), t, h | k, s@(.opAssign ..), t, h
  | k, s@(.incDec ..), t, h | k, s@(.pushOpAssign ..), t, h | k, s@(.pushIncDec ..), t, h
  | k, s@(.call ..), t, h | k, s@(.assignIncDec ..), t, h | k, s@(.assignPush ..), t, h
  | k, s@(.declStoragePush ..), t, h | k, s@(.declPush ..), t, h | k, s@(.require ..), t, h
  | k, s@(.assert ..), t, h | k, s@.revert, t, h | k, s@(.revertMsg ..), t, h
  | k, s@(.requireMsg ..), t, h | k, s@(.revertReason ..), t, h | k, s@(.requireReason ..), t, h
  | k, s@(.revertRaw ..), t, h | k, s@(.revertErr ..), t, h | k, s@(.requireErr ..), t, h
  | k, s@.assumeFalse, t, h | k, s@(.eval ..), t, h | k, s@(.unchecked ..), t, h
  | k, s@(.checked ..), t, h | k, s@(.tryCall ..), t, h | k, s@(.send ..), t, h
  | k, s@(.tupleDecl ..), t, h | k, s@(.tupleAssign ..), t, h | k, s@.hole, t, h => by
      simp only [Decode.Tables.stmt] at h; spell_simp Decode.Tables.WithExpr.stmt at h; obtain ⟨a, ha, rfl⟩ := h; exact .simple (simple_spellsT _ _ ha)
theorem items_spellsT : (k : SCtx) → (b : List RawStmt) → (t : Syn (.list (.item k))) →
    T.items k b = some t → ItemsT T k b t
  | k, [], t, h => by simp only [Decode.Tables.items] at h; spell_simp Decode.Tables.WithExpr.items at h; subst h; exact .nil
  | ⟨l, false⟩, .unchecked b :: rest, t, h => by
      simp only [Decode.Tables.items, Decode.Tables.WithExpr.items, Decode.uncheckedItem] at h
      bind_simp at h
      obtain ⟨b', hb, _, rfl, r', hr, rfl⟩ := h
      exact .unchecked (items_spellsT _ _ _ hb) (items_spellsT _ _ _ hr)
  | ⟨l, true⟩, .unchecked b :: rest, t, h => by
      simp only [Decode.Tables.items, Decode.Tables.WithExpr.items, Decode.uncheckedItem] at h
      bind_simp at h
      obtain ⟨_, _, h⟩ := h
      exact h.elim
  | k, s@(.assign ..) :: rest, t, h | k, s@(.decl ..) :: rest, t, h
  | k, s@(.declStorage ..) :: rest, t, h | k, s@(.declMemory ..) :: rest, t, h
  | k, s@(.delete ..) :: rest, t, h | k, s@(.opAssign ..) :: rest, t, h
  | k, s@(.incDec ..) :: rest, t, h | k, s@(.pushOpAssign ..) :: rest, t, h
  | k, s@(.pushIncDec ..) :: rest, t, h | k, s@(.call ..) :: rest, t, h
  | k, s@(.assignIncDec ..) :: rest, t, h | k, s@(.assignPush ..) :: rest, t, h
  | k, s@(.declStoragePush ..) :: rest, t, h | k, s@(.declPush ..) :: rest, t, h
  | k, s@(.ite ..) :: rest, t, h | k, s@(.require ..) :: rest, t, h
  | k, s@(.assert ..) :: rest, t, h | k, s@.revert :: rest, t, h
  | k, s@(.revertMsg ..) :: rest, t, h | k, s@(.requireMsg ..) :: rest, t, h
  | k, s@(.revertReason ..) :: rest, t, h | k, s@(.requireReason ..) :: rest, t, h
  | k, s@(.revertRaw ..) :: rest, t, h | k, s@(.revertErr ..) :: rest, t, h
  | k, s@(.requireErr ..) :: rest, t, h | k, s@.assumeFalse :: rest, t, h
  | k, s@(.ret ..) :: rest, t, h | k, s@(.eval ..) :: rest, t, h
  | k, s@(.checked ..) :: rest, t, h | k, s@(.tryCall ..) :: rest, t, h
  | k, s@(.send ..) :: rest, t, h | k, s@(.tupleDecl ..) :: rest, t, h
  | k, s@(.tupleAssign ..) :: rest, t, h | k, s@(.block ..) :: rest, t, h
  | k, s@(.whileLoop ..) :: rest, t, h | k, s@(.forLoop ..) :: rest, t, h
  | k, s@(.doWhile ..) :: rest, t, h | k, s@.brk :: rest, t, h | k, s@.cont :: rest, t, h
  | k, s@(.loop ..) :: rest, t, h | k, s@.hole :: rest, t, h => by
      simp only [Decode.Tables.items] at h; spell_simp Decode.Tables.WithExpr.items at h; obtain ⟨s', hs, r', hr, rfl⟩ := h
      exact .stmt (stmt_spellsT _ _ _ hs) (items_spellsT _ _ _ hr)
end

end Spells

/-! ## The spelling relation of a decoder version -/

/-- **The spelling relation of a decoder version.** A plain request spells a
Source program when its raw input spells a block that has a Source typing
derivation from the caller's locals in the version's unit, and the program is
that derivation's resolution. No inference function is mentioned. -/
def SpellsT (T : Decode.Tables) (r : Request) (s : SourceProgram) : Prop :=
  Decode.plain r = true ∧
  ∃ (C : Source.Ctx) (L : List (String × Source.STy)) (b : Source.Syn (.list (.item .body)))
    (L' : List (String × Source.STy)) (d : Source.ItemsD C L b L'),
    T.context r = some C ∧ T.locals r.input.before.locals.1 = some L ∧
    Spells.ItemsT T .body r.input.raw b ∧
    s = ⟨C.env, C.rets, C.inModifier, .body, Source.tysOf L, Source.tysOf L', d.toR⟩

/-- Source inference finds a derivation whenever one exists, on the decoder's
image only: a request's canonical context and a block its raw input spells.
Not proved in the Source front end, whose inference is documented as possibly
incomplete in general; the version's decoder is complete for `SpellsT T` under
it. -/
def InferCompleteT (T : Decode.Tables) : Prop :=
  ∀ (r : Request) (C : Source.Ctx) (L : List (String × Source.STy))
    (b : Source.Syn (.list (.item .body))) (L' : List (String × Source.STy)),
    T.context r = some C → Spells.ItemsT T .body r.input.raw b → Source.ItemsD C L b L' →
    (Source.ItemsD.infer C L b).isSome = true

/-- The decoder is sound for the relation: what it returns is spelled. -/
theorem decode_spellsT {T : Decode.Tables} {r : Request} {s : SourceProgram} (h : T.decode r = some s) :
    SpellsT T r s := by
  unfold Decode.Tables.decode at h
  split at h
  · rename_i p
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨C, hC, L, hL, b, hb, ⟨L', d⟩, _, rfl⟩ := h
    exact ⟨p, C, L, b, L', d, hC, hL, Spells.items_spellsT _ _ _ hb, rfl⟩
  · cases h

/-- A request spells at most one program. -/
theorem SpellsT.unique {T : Decode.Tables} {r : Request} {s s' : SourceProgram} (h : SpellsT T r s) (h' : SpellsT T r s') :
    s = s' := by
  obtain ⟨_, C, L, b, L', d, hC, hL, hb, rfl⟩ := h
  obtain ⟨_, C', L₀, b', L'', d', hC', hL', hb', rfl⟩ := h'
  cases hC.symm.trans hC'
  cases hL.symm.trans hL'
  cases hb.decode.symm.trans hb'.decode
  obtain ⟨rfl, same⟩ := Source.ItemsD.unique d d'
  rw [eq_of_heq same]

/-- The decoder is complete for the relation if Source inference is. -/
theorem SpellsT.decode {T : Decode.Tables} (complete : InferCompleteT T) {r : Request} {s : SourceProgram}
    (h : SpellsT T r s) : T.decode r = some s := by
  have h₀ := h
  obtain ⟨p, C, L, b, L', d, hC, hL, hb, _⟩ := h₀
  obtain ⟨⟨L'', d'⟩, found⟩ := Option.isSome_iff_exists.mp (complete r C L b L' hC hb d)
  have decoded : T.decode r =
      some ⟨C.env, C.rets, C.inModifier, .body, Source.tysOf L, Source.tysOf L'', d'.toR⟩ := by
    simp [Decode.Tables.decode, p, hC, hL, hb.decode, found]
  exact decoded.trans (congrArg some (SpellsT.unique (decode_spellsT decoded) h))

namespace Spells

/-! The original syntax API is a specialization, not a second inductive.
The method wrappers retain conclusions about the original decoder functions. -/
abbrev Expr := ExprT Decode.tables1
abbrev Exprs := ExprsT Decode.tables1
abbrev Components := ComponentsT Decode.tables1
abbrev Simple := SimpleT Decode.tables1
abbrev Init := InitT Decode.tables1
abbrev Upd := UpdT Decode.tables1
abbrev Stmt := StmtT Decode.tables1
abbrev Items := ItemsT Decode.tables1

theorem Expr.decode {e : RawExpr} {t : Source.Syn .expr}
    (h : Expr e t) : Decode.expr e = some t :=
  (Decode.expr_tables1 e).symm.trans (ExprT.decode h)

theorem Exprs.decode {es : List RawExpr} {t : Source.Syn (.list .expr)}
    (h : Exprs es t) : Decode.exprs es = some t :=
  (Decode.exprs_tables1 es).symm.trans (ExprsT.decode h)

theorem Components.decode {es : List RawExpr} {t : Source.Syn (.list (.opt .expr))}
    (h : Components es t) : Decode.components es = some t :=
  (Decode.components_tables1 es).symm.trans (ComponentsT.decode h)

theorem Simple.decode {s : RawStmt} {t : Source.Syn .simple}
    (h : Simple s t) : Decode.simple s = some t :=
  (Decode.simple_tables1 s).symm.trans (SimpleT.decode h)

theorem Init.decode {b : List RawStmt} {t : Source.Syn (.opt .simple)}
    (h : Init b t) : Decode.initializer b = some t :=
  (Decode.initializer_tables1 b).symm.trans (InitT.decode h)

theorem Upd.decode {b : List RawStmt} {t : Source.Syn (.opt .expr)}
    (h : Upd b t) : Decode.update b = some t :=
  (Decode.update_tables1 b).symm.trans (UpdT.decode h)

theorem Stmt.decode {k : Source.SCtx} {s : RawStmt} {t : Source.Syn (.stmt k)}
    (h : Stmt k s t) : Decode.stmt k s = some t :=
  (Decode.stmt_tables1 k s).symm.trans (StmtT.decode h)

theorem Items.decode {k : Source.SCtx} {b : List RawStmt} {t : Source.Syn (.list (.item k))}
    (h : Items k b t) : Decode.items k b = some t :=
  (Decode.items_tables1 k b).symm.trans (ItemsT.decode h)

end Spells

/-- Original request spelling is the original-table specialization. -/
abbrev Spells := SpellsT Decode.tables1

/-- The original completeness premise is unchanged by specialization. -/
abbrev InferComplete := InferCompleteT Decode.tables1

/-- Original-decoder soundness, inherited from the generic theorem. -/
theorem decode_spells {r : Request} {s : SourceProgram} (h : Decode.decode r = some s) :
    Spells r s :=
  decode_spellsT ((Decode.decode_tables1 r).trans h)

/-- Original request spelling still determines at most one program. -/
theorem Spells.unique {r : Request} {s s' : SourceProgram}
    (h : Spells r s) (h' : Spells r s') : s = s' := SpellsT.unique h h'

/-- Original-decoder completeness retains its original premise. -/
theorem Spells.decode (complete : InferComplete) {r : Request} {s : SourceProgram}
    (h : Spells r s) : Decode.decode r = some s :=
  (Decode.decode_tables1 r).symm.trans (SpellsT.decode complete h)

end Solidity.Correctness.Lowering.Total
