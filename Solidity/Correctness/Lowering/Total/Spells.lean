import Solidity.Correctness.Lowering.Total.Decode
import Solidity.Source.Unique

/-!
# Loop lowering: the spelling relation (h1024)

An inductive relation between raw and Source syntax, written without the
decoder's functions, and `Spells` on requests, written with Source typing
derivations instead of the inference function. The decoder is proved sound for
it (`decode_spells`) and, if Source inference is complete, complete
(`Spells.decode`). It shares the decoder's operator, type and environment
tables, its `unbrace`, its `plain` test and its reading of the request's unit
and locals, and its constructors repeat the decoder's spelling choices. So it
is an independent check of the recursion and of inference, not of the choices. -/
namespace Solidity.Correctness.Lowering.Total

namespace Spells
open Source (Syn SCtx STy)
open Decode (num uintElem intElem unbrace)

mutual
inductive Expr : RawExpr → Syn .expr → Prop where
  | num (n : Nat) : Expr (.num n) (num n)
  | name (x : String) : Expr (.name x) (.ident x)
  | bool (b : Bool) : Expr (.bool b) (.lit (.bool b))
  | field {e e'} (f : String) : Expr e e' → Expr (.field e f) (.member e' f)
  | index {e e' k k'} : Expr e e' → Expr k k' → Expr (.index e k) (.index e' (.some k'))
  | binop {op f a a' b b' t} : Decode.binop op = some f → Expr a a' → Expr b b' →
      t = f a' b' → Expr (.binop op a b) t
  | neg {a a'} : Expr a a' → Expr (.unop .neg a) (.unaryPrefix .neg a')
  | not {a a'} : Expr a a' → Expr (.unop .not a) (.unaryPrefix .not a')
  | bnot {a a'} : Expr a a' → Expr (.unop .bnot a) (.unaryPrefix .bitNot a')
  | toInt {a a'} : Expr a a' → Expr (.unop .toInt a)
      (.call (.elemType intElem (by decide)) (.positional (.cons a' .nil)))
  | toUint {a a'} : Expr a a' → Expr (.unop .toUint a)
      (.call (.elemType uintElem (by decide)) (.positional (.cons a' .nil)))
  | ternary {c c' a a' b b'} : Expr c c' → Expr a a' → Expr b b' →
      Expr (.ternary c a b) (.cond c' a' b')
  | preInc {e e'} : Expr e e' → Expr (.incDec .preInc e) (.unaryPrefix .inc e')
  | preDec {e e'} : Expr e e' → Expr (.incDec .preDec e) (.unaryPrefix .dec e')
  | postInc {e e'} : Expr e e' → Expr (.incDec .postInc e) (.unarySuffix .inc e')
  | postDec {e e'} : Expr e e' → Expr (.incDec .postDec e) (.unarySuffix .dec e')
  | call {args args'} (f : String) : Exprs args args' →
      Expr (.call f args) (.call (.ident f) (.positional args'))
  | modular {a a' b b' k k'} (op : ModOp) : Expr a a' → Expr b b' → Expr k k' →
      Expr (.modular op a b k)
        (.call (.ident op.toStr) (.positional (.cons a' (.cons b' (.cons k' .nil)))))
  | env {k t} : Decode.env k = some t → Expr (.env k) t
  | tuple {a a' b b' rest rest'} : Expr a a' → Expr b b' → Components rest rest' →
      Expr (.tuple (a :: b :: rest)) (.tuple (.some a') (.cons (.some b') rest'))
  | assign {l l' r r'} : Expr l l' → Expr r r' → Expr (.assign l r) (.assign .assign l' r')
  | opAssign {op o l l' r r'} : Decode.assignOp op = some o → Expr l l' → Expr r r' →
      Expr (.opAssign op l r) (.assign o l' r')
inductive Exprs : List RawExpr → Syn (.list .expr) → Prop where
  | nil : Exprs [] .nil
  | cons {e e' es es'} : Expr e e' → Exprs es es' → Exprs (e :: es) (.cons e' es')
inductive Components : List RawExpr → Syn (.list (.opt .expr)) → Prop where
  | nil : Components [] .nil
  | cons {e e' es es'} : Expr e e' → Components es es' →
      Components (e :: es) (.cons (.some e') es')
end

mutual
theorem Expr.decode : ∀ {e t}, Expr e t → Decode.expr e = some t
  | _, _, .num _ | _, _, .name _ | _, _, .bool _ => by simp [Decode.expr]
  | _, _, .field _ h => by simp [Decode.expr, h.decode]
  | _, _, .index h k => by simp [Decode.expr, h.decode, k.decode]
  | _, _, .binop o h k e => by simp [Decode.expr, o, h.decode, k.decode, e]
  | _, _, .neg h | _, _, .not h | _, _, .bnot h | _, _, .toInt h | _, _, .toUint h
  | _, _, .preInc h | _, _, .preDec h | _, _, .postInc h | _, _, .postDec h => by
      simp [Decode.expr, h.decode]
  | _, _, .ternary c a b => by simp [Decode.expr, c.decode, a.decode, b.decode]
  | _, _, .call _ h => by simp [Decode.expr, h.decode]
  | _, _, .modular _ a b k => by simp [Decode.expr, a.decode, b.decode, k.decode]
  | _, _, .env h => by simp [Decode.expr, h]
  | _, _, .tuple a b r => by simp [Decode.expr, a.decode, b.decode, r.decode]
  | _, _, .assign l r => by simp [Decode.expr, l.decode, r.decode]
  | _, _, .opAssign o l r => by simp [Decode.expr, o, l.decode, r.decode]
theorem Exprs.decode : ∀ {es t}, Exprs es t → Decode.exprs es = some t
  | _, _, .nil => by simp [Decode.exprs]
  | _, _, .cons h k => by simp [Decode.exprs, h.decode, k.decode]
theorem Components.decode : ∀ {es t}, Components es t → Decode.components es = some t
  | _, _, .nil => by simp [Decode.components]
  | _, _, .cons h k => by simp [Decode.components, h.decode, k.decode]
end


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

mutual
theorem expr_spells : (e : RawExpr) → (t : Syn .expr) → Decode.expr e = some t → Expr e t
  | .num n, t, h => by spell_simp Decode.expr at h; subst h; exact .num n
  | .name x, t, h => by spell_simp Decode.expr at h; subst h; exact .name x
  | .bool b, t, h => by spell_simp Decode.expr at h; subst h; exact .bool b
  | .field e f, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a, ha, rfl⟩ := h; exact .field f (expr_spells _ _ ha)
  | .index e k, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact .index (expr_spells _ _ ha) (expr_spells _ _ hb)
  | .binop op a b, t, h => by
      spell_simp Decode.expr at h; obtain ⟨f, hf, a', ha, b', hb, rfl⟩ := h
      exact .binop hf (expr_spells _ _ ha) (expr_spells _ _ hb) rfl
  | .unop .neg a, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .neg (expr_spells _ _ ha)
  | .unop .not a, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .not (expr_spells _ _ ha)
  | .unop .bnot a, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .bnot (expr_spells _ _ ha)
  | .unop .toInt a, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .toInt (expr_spells _ _ ha)
  | .unop .toUint a, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .toUint (expr_spells _ _ ha)
  | .ternary c a b, t, h => by
      spell_simp Decode.expr at h; obtain ⟨c', hc, a', ha, b', hb, rfl⟩ := h
      exact .ternary (expr_spells _ _ hc) (expr_spells _ _ ha) (expr_spells _ _ hb)
  | .incDec .preInc e, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .preInc (expr_spells _ _ ha)
  | .incDec .preDec e, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .preDec (expr_spells _ _ ha)
  | .incDec .postInc e, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .postInc (expr_spells _ _ ha)
  | .incDec .postDec e, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .postDec (expr_spells _ _ ha)
  | .call f args, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, rfl⟩ := h; exact .call f (exprs_spells _ _ ha)
  | .modular op a b k, t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, b', hb, k', hk, rfl⟩ := h
      exact .modular op (expr_spells _ _ ha) (expr_spells _ _ hb) (expr_spells _ _ hk)
  | .env k, t, h => by spell_simp Decode.expr at h; exact .env h
  | .tuple (a :: b :: rest), t, h => by
      spell_simp Decode.expr at h; obtain ⟨a', ha, b', hb, r', hr, rfl⟩ := h
      exact .tuple (expr_spells _ _ ha) (expr_spells _ _ hb) (components_spells _ _ hr)
  | .assign l r, t, h => by
      spell_simp Decode.expr at h; obtain ⟨l', hl, r', hr, rfl⟩ := h
      exact .assign (expr_spells _ _ hl) (expr_spells _ _ hr)
  | .opAssign op l r, t, h => by
      spell_simp Decode.expr at h; obtain ⟨o, ho, l', hl, r', hr, rfl⟩ := h
      exact .opAssign ho (expr_spells _ _ hl) (expr_spells _ _ hr)
  | .newArr .., _, h | .named .., _, h | .tuple [], _, h | .tuple [_], _, h => by
      spell_simp Decode.expr at h
theorem exprs_spells : (es : List RawExpr) → (t : Syn (.list .expr)) →
    Decode.exprs es = some t → Exprs es t
  | [], t, h => by spell_simp Decode.exprs at h; subst h; exact .nil
  | e :: es, t, h => by
      spell_simp Decode.exprs at h; obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact .cons (expr_spells _ _ ha) (exprs_spells _ _ hb)
theorem components_spells : (es : List RawExpr) → (t : Syn (.list (.opt .expr))) →
    Decode.components es = some t → Components es t
  | [], t, h => by spell_simp Decode.components at h; subst h; exact .nil
  | e :: es, t, h => by
      spell_simp Decode.components at h; obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact .cons (expr_spells _ _ ha) (components_spells _ _ hb)
end

/-- Simple statements. -/
inductive Simple : RawStmt → Syn .simple → Prop where
  | assign {l l' r r'} : Expr l l' → Expr r r' →
      Simple (.assign l r) (.exprStmt (.assign .assign l' r'))
  | declNone {T T'} (x : String) : Decode.typeName T = some T' →
      Simple (.decl T x none) (.declVar (.varDecl T' none x) .none)
  | declSome {T T' e e'} (x : String) : Decode.typeName T = some T' → Expr e e' →
      Simple (.decl T x (some e)) (.declVar (.varDecl T' none x) (.some e'))
  | opAssign {op o l l' r r'} : Decode.assignOp op = some o → Expr l l' → Expr r r' →
      Simple (.opAssign op l r) (.exprStmt (.assign o l' r'))
  | incDec {op l t} : Expr (.incDec op l) t → Simple (.incDec op l) (.exprStmt t)
  | require {c c'} : Expr c c' →
      Simple (.require c) (.exprStmt (.call (.ident "require") (.positional (.cons c' .nil))))
  | assert {c c'} : Expr c c' →
      Simple (.assert c) (.exprStmt (.call (.ident "assert") (.positional (.cons c' .nil))))
  | revert : Simple .revert (.exprStmt (.call (.ident "revert") (.positional .nil)))

theorem Simple.decode {s t} (h : Simple s t) : Decode.simple s = some t := by
  cases h with
  | assign l r => simp [Decode.simple, l.decode, r.decode]
  | declNone x T => simp [Decode.simple, T]
  | declSome x T e => simp [Decode.simple, T, e.decode]
  | opAssign o l r => simp [Decode.simple, o, l.decode, r.decode]
  | incDec e => simp [Decode.simple, e.decode]
  | require c => simp [Decode.simple, c.decode]
  | assert c => simp [Decode.simple, c.decode]
  | revert => simp [Decode.simple]

theorem simple_spells (s : RawStmt) (t : Syn .simple) (h : Decode.simple s = some t) :
    Simple s t := by
  cases s with
  | assign l r =>
      spell_simp Decode.simple at h; obtain ⟨l', hl, r', hr, rfl⟩ := h
      exact .assign (expr_spells _ _ hl) (expr_spells _ _ hr)
  | decl T x init =>
      cases init with
      | none => spell_simp Decode.simple at h; obtain ⟨T', hT, rfl⟩ := h; exact .declNone x hT
      | some e =>
        spell_simp Decode.simple at h; obtain ⟨T', hT, e', he, rfl⟩ := h
        exact .declSome x hT (expr_spells _ _ he)
  | opAssign op l r =>
      spell_simp Decode.simple at h; obtain ⟨o, ho, l', hl, r', hr, rfl⟩ := h
      exact .opAssign ho (expr_spells _ _ hl) (expr_spells _ _ hr)
  | incDec op l =>
      spell_simp Decode.simple at h; obtain ⟨a, ha, rfl⟩ := h; exact .incDec (expr_spells _ _ ha)
  | require c =>
      spell_simp Decode.simple at h; obtain ⟨a, ha, rfl⟩ := h; exact .require (expr_spells _ _ ha)
  | assert c =>
      spell_simp Decode.simple at h; obtain ⟨a, ha, rfl⟩ := h; exact .assert (expr_spells _ _ ha)
  | revert => spell_simp Decode.simple at h; subst h; exact .revert
  | _ => simp [Decode.simple] at h

/-- A `for` initializer: none, or one simple statement. -/
inductive Init : List RawStmt → Syn (.opt .simple) → Prop where
  | absent : Init [] .none
  | one {s t} : Simple s t → Init [s] (.some t)

/-- A `for` update: none, or one assignment or update expression. -/
inductive Upd : List RawStmt → Syn (.opt .expr) → Prop where
  | absent : Upd [] .none
  | assign {l l' r r'} : Expr l l' → Expr r r' → Upd [.assign l r] (.some (.assign .assign l' r'))
  | opAssign {op o l l' r r'} : Decode.assignOp op = some o → Expr l l' → Expr r r' →
      Upd [.opAssign op l r] (.some (.assign o l' r'))
  | incDec {op l t} : Expr (.incDec op l) t → Upd [.incDec op l] (.some t)

/-- A `for` condition, absent or present. -/
inductive Cond : Option RawExpr → Syn (.opt .expr) → Prop where
  | absent : Cond none .none
  | present {c c'} : Expr c c' → Cond (some c) (.some c')

mutual
/-- Statements in a control context. -/
inductive Stmt : (k : SCtx) → RawStmt → Syn (.stmt k) → Prop where
  | ite {k c c' thn thn'} : Expr c c' → Items k thn thn' →
      Stmt k (.ite c thn []) (.ifStmt c' (unbrace thn') .none)
  | iteElse {k c c' thn thn' e els els'} : Expr c c' → Items k thn thn' →
      Items k (e :: els) els' →
      Stmt k (.ite c thn (e :: els)) (.ifStmt c' (unbrace thn') (.some (unbrace els')))
  | retNone {k} : Stmt k (.ret none) (.returnStmt .none)
  | retSome {k e e'} : Expr e e' → Stmt k (.ret (some e)) (.returnStmt (.some e'))
  | block {k b b'} : Items k b b' → Stmt k (.block b) (.blockStmt (.block b'))
  | whileLoop {l u c c' b b'} (spec : RawLoopSpec) : Expr c c' → Items ⟨true, u⟩ b b' →
      Stmt ⟨l, u⟩ (.whileLoop spec c b) (.whileStmt c' (unbrace b'))
  | loop {l u c c' b b'} (spec : RawLoopSpec) : Expr c c' → Items ⟨true, u⟩ b b' →
      Stmt ⟨l, u⟩ (.loop spec c b) (.whileStmt c' (unbrace b'))
  | doWhile {l u c c' b b'} (spec : RawLoopSpec) : Items ⟨true, u⟩ b b' → Expr c c' →
      Stmt ⟨l, u⟩ (.doWhile spec b c) (.doWhile (unbrace b') c')
  | forLoop {l u init init' c c' upd upd' b b'} (spec : RawLoopSpec) : Init init init' →
      Cond c c' → Upd upd upd' → Items ⟨true, u⟩ b b' →
      Stmt ⟨l, u⟩ (.forLoop spec init c upd b) (.forStmt init' c' upd' (unbrace b'))
  | brk {u} : Stmt ⟨true, u⟩ .brk .breakStmt
  | cont {u} : Stmt ⟨true, u⟩ .cont .continueStmt
  | simple {k s t} : Simple s t → Stmt k s (.simpleStmt t)
/-- The items of a block; an `unchecked` block only in a checked context. -/
inductive Items : (k : SCtx) → List RawStmt → Syn (.list (.item k)) → Prop where
  | nil {k} : Items k [] .nil
  | unchecked {l b b' rest rest'} : Items ⟨l, true⟩ b b' → Items ⟨l, false⟩ rest rest' →
      Items ⟨l, false⟩ (.unchecked b :: rest) (.cons (.uncheckedItem (.block b')) rest')
  | stmt {k s s' rest rest'} : Stmt k s s' → Items k rest rest' →
      Items k (s :: rest) (.cons (.stmtItem s') rest')
end

theorem Init.decode {b t} (h : Init b t) : Decode.initializer b = some t := by
  cases h with
  | absent => rfl
  | one s => simp [Decode.initializer, s.decode]

theorem init_spells (b : List RawStmt) (t : Syn (.opt .simple))
    (h : Decode.initializer b = some t) : Init b t := by
  match b, h with
  | [], h => spell_simp Decode.initializer at h; subst h; exact .absent
  | [s], h =>
    spell_simp Decode.initializer at h; obtain ⟨a, ha, rfl⟩ := h; exact .one (simple_spells _ _ ha)
  | _ :: _ :: _, h => simp [Decode.initializer] at h

theorem Upd.decode {b t} (h : Upd b t) : Decode.update b = some t := by
  cases h with
  | absent => rfl
  | assign l r => simp [Decode.update, l.decode, r.decode]
  | opAssign o l r => simp [Decode.update, o, l.decode, r.decode]
  | incDec e => simp [Decode.update, e.decode]

theorem upd_spells (b : List RawStmt) (t : Syn (.opt .expr)) (h : Decode.update b = some t) :
    Upd b t := by
  unfold Decode.update at h
  split at h
  · cases h; exact .absent
  · bind_simp at h; obtain ⟨l', hl, r', hr, rfl⟩ := h
    exact .assign (expr_spells _ _ hl) (expr_spells _ _ hr)
  · bind_simp at h; obtain ⟨o, ho, l', hl, r', hr, rfl⟩ := h
    exact .opAssign ho (expr_spells _ _ hl) (expr_spells _ _ hr)
  · bind_simp at h; obtain ⟨a, ha, rfl⟩ := h; exact .incDec (expr_spells _ _ ha)
  · cases h

mutual
theorem Stmt.decode : ∀ {k s t}, Stmt k s t → Decode.stmt k s = some t
  | _, _, _, .ite c thn => by simp [Decode.stmt, c.decode, thn.decode]
  | _, _, _, .iteElse c thn els => by simp [Decode.stmt, c.decode, thn.decode, els.decode]
  | _, _, _, .retNone => by simp [Decode.stmt]
  | _, _, _, .retSome e => by simp [Decode.stmt, e.decode]
  | _, _, _, .block b => by simp [Decode.stmt, b.decode]
  | _, _, _, .whileLoop _ c b | _, _, _, .loop _ c b => by
      simp [Decode.stmt, c.decode, b.decode]
  | _, _, _, .doWhile _ b c => by simp [Decode.stmt, c.decode, b.decode]
  | _, _, _, .forLoop _ i c u b => by
      cases c with
      | absent => simp [Decode.stmt, i.decode, u.decode, b.decode]
      | present c => simp [Decode.stmt, i.decode, u.decode, b.decode, c.decode]
  | _, _, _, .brk | _, _, _, .cont => by simp [Decode.stmt, Decode.jump]
  | _, _, _, .simple h => by
      have e := h.decode
      cases h <;> simp [Decode.stmt, e]
theorem Items.decode : ∀ {k b t}, Items k b t → Decode.items k b = some t
  | _, _, _, .nil => by simp [Decode.items]
  | _, _, _, .unchecked b rest => by
      simp [Decode.items, b.decode, rest.decode, Decode.uncheckedItem]
  | _, _, _, .stmt s rest => by
      have e := s.decode
      have e' := rest.decode
      cases s <;> first | simp [Decode.items, e, e'] | (rename_i h; cases h <;> simp [Decode.items, e, e'])
end

mutual
theorem stmt_spells : (k : SCtx) → (s : RawStmt) → (t : Syn (.stmt k)) →
    Decode.stmt k s = some t → Stmt k s t
  | k, .ite c thn [], t, h => by
      spell_simp Decode.stmt at h; obtain ⟨c', hc, thn', ht, rfl⟩ := h
      exact .ite (expr_spells _ _ hc) (items_spells _ _ _ ht)
  | k, .ite c thn (e :: els), t, h => by
      spell_simp Decode.stmt at h; obtain ⟨c', hc, thn', ht, els', he, rfl⟩ := h
      exact .iteElse (expr_spells _ _ hc) (items_spells _ _ _ ht) (items_spells _ _ _ he)
  | k, .ret none, t, h => by spell_simp Decode.stmt at h; subst h; exact .retNone
  | k, .ret (some e), t, h => by
      spell_simp Decode.stmt at h; obtain ⟨e', he, rfl⟩ := h; exact .retSome (expr_spells _ _ he)
  | k, .block b, t, h => by
      spell_simp Decode.stmt at h; obtain ⟨b', hb, rfl⟩ := h; exact .block (items_spells _ _ _ hb)
  | ⟨l, u⟩, .whileLoop spec c b, t, h => by
      spell_simp Decode.stmt at h; obtain ⟨c', hc, b', hb, rfl⟩ := h
      exact .whileLoop spec (expr_spells _ _ hc) (items_spells _ _ _ hb)
  | ⟨l, u⟩, .loop spec c b, t, h => by
      spell_simp Decode.stmt at h; obtain ⟨c', hc, b', hb, rfl⟩ := h
      exact .loop spec (expr_spells _ _ hc) (items_spells _ _ _ hb)
  | ⟨l, u⟩, .doWhile spec b c, t, h => by
      spell_simp Decode.stmt at h; obtain ⟨b', hb, c', hc, rfl⟩ := h
      exact .doWhile spec (items_spells _ _ _ hb) (expr_spells _ _ hc)
  | ⟨l, u⟩, .forLoop spec init none upd b, t, h => by
      spell_simp Decode.stmt at h; obtain ⟨i', hi, _, rfl, u', hu, b', hb, rfl⟩ := h
      exact .forLoop spec (init_spells _ _ hi) .absent (upd_spells _ _ hu) (items_spells _ _ _ hb)
  | ⟨l, u⟩, .forLoop spec init (some c) upd b, t, h => by
      spell_simp Decode.stmt at h; obtain ⟨i', hi, _, ⟨c', hc, rfl⟩, u', hu, b', hb, rfl⟩ := h
      exact .forLoop spec (init_spells _ _ hi) (.present (expr_spells _ _ hc)) (upd_spells _ _ hu)
        (items_spells _ _ _ hb)
  | ⟨true, u⟩, .brk, t, h => by simp [Decode.stmt, Decode.jump] at h; subst h; exact .brk
  | ⟨false, u⟩, .brk, t, h => by simp [Decode.stmt, Decode.jump] at h
  | ⟨true, u⟩, .cont, t, h => by simp [Decode.stmt, Decode.jump] at h; subst h; exact .cont
  | ⟨false, u⟩, .cont, t, h => by simp [Decode.stmt, Decode.jump] at h
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
      spell_simp Decode.stmt at h; obtain ⟨a, ha, rfl⟩ := h; exact .simple (simple_spells _ _ ha)
theorem items_spells : (k : SCtx) → (b : List RawStmt) → (t : Syn (.list (.item k))) →
    Decode.items k b = some t → Items k b t
  | k, [], t, h => by spell_simp Decode.items at h; subst h; exact .nil
  | ⟨l, false⟩, .unchecked b :: rest, t, h => by
      simp only [Decode.items, Decode.uncheckedItem] at h
      bind_simp at h
      obtain ⟨b', hb, _, rfl, r', hr, rfl⟩ := h
      exact .unchecked (items_spells _ _ _ hb) (items_spells _ _ _ hr)
  | ⟨l, true⟩, .unchecked b :: rest, t, h => by
      simp only [Decode.items, Decode.uncheckedItem] at h
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
      spell_simp Decode.items at h; obtain ⟨s', hs, r', hr, rfl⟩ := h
      exact .stmt (stmt_spells _ _ _ hs) (items_spells _ _ _ hr)
end
end Spells

/-- **The spelling relation.** A plain request spells a Source program when
its raw input spells a block that has a Source typing derivation from the
caller's locals in the canonical unit, and the program is that derivation's
resolution. No inference function is mentioned. -/
def Spells (r : Request) (s : SourceProgram) : Prop :=
  Decode.plain r = true ∧
  ∃ (C : Source.Ctx) (L : List (String × Source.STy)) (b : Source.Syn (.list (.item .body)))
    (L' : List (String × Source.STy)) (d : Source.ItemsD C L b L'),
    Decode.context r = some C ∧ Decode.locals r.input.before.locals.1 = some L ∧
    Spells.Items .body r.input.raw b ∧
    s = ⟨C.env, C.rets, C.inModifier, .body, Source.tysOf L, Source.tysOf L', d.toR⟩

/-- Source inference finds a derivation whenever one exists, on the decoder's
image only: a request's canonical context and a block its raw input spells.
Not proved in the Source front end, whose inference is documented as possibly
incomplete in general; the decoder is complete for `Spells` under it. -/
def InferComplete : Prop :=
  ∀ (r : Request) (C : Source.Ctx) (L : List (String × Source.STy))
    (b : Source.Syn (.list (.item .body))) (L' : List (String × Source.STy)),
    Decode.context r = some C → Spells.Items .body r.input.raw b → Source.ItemsD C L b L' →
    (Source.ItemsD.infer C L b).isSome = true

/-- The decoder is sound for the relation: what it returns is spelled. -/
theorem decode_spells {r : Request} {s : SourceProgram} (h : Decode.decode r = some s) :
    Spells r s := by
  unfold Decode.decode at h
  split at h
  · rename_i p
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨C, hC, L, hL, b, hb, ⟨L', d⟩, _, rfl⟩ := h
    exact ⟨p, C, L, b, L', d, hC, hL, Spells.items_spells _ _ _ hb, rfl⟩
  · cases h

/-- A request spells at most one program. -/
theorem Spells.unique {r : Request} {s s' : SourceProgram} (h : Spells r s) (h' : Spells r s') :
    s = s' := by
  obtain ⟨_, C, L, b, L', d, hC, hL, hb, rfl⟩ := h
  obtain ⟨_, C', L₀, b', L'', d', hC', hL', hb', rfl⟩ := h'
  cases hC.symm.trans hC'
  cases hL.symm.trans hL'
  cases hb.decode.symm.trans hb'.decode
  obtain ⟨rfl, same⟩ := Source.ItemsD.unique d d'
  rw [eq_of_heq same]

/-- The decoder is complete for the relation if Source inference is. -/
theorem Spells.decode (complete : InferComplete) {r : Request} {s : SourceProgram}
    (h : Spells r s) : Decode.decode r = some s := by
  have h₀ := h
  obtain ⟨p, C, L, b, L', d, hC, hL, hb, _⟩ := h₀
  obtain ⟨⟨L'', d'⟩, found⟩ := Option.isSome_iff_exists.mp (complete r C L b L' hC hb d)
  have decoded : Decode.decode r =
      some ⟨C.env, C.rets, C.inModifier, .body, Source.tysOf L, Source.tysOf L'', d'.toR⟩ := by
    simp [Decode.decode, p, hC, hL, hb.decode, found]
  exact decoded.trans (congrArg some (Spells.unique (decode_spells decoded) h))

end Solidity.Correctness.Lowering.Total
