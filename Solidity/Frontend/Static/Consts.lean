import Solidity.Source.ConstCheck
import Solidity.Frontend.Static.WellFormedCheck

/-!
# Checking compile-time constants (G13)

Checkers for `Solidity/Source/ConstCheck.lean`:

- `pureP`/`pureB`: decides purity, returning the proof (`pureB_iff`), hence `constInitsB` decides
  `ConstInitsPure` (`constInitsB_iff`): solc's compile-time check of
  constant initializers, which S01's `WellFormed` does not make.
- `tevalP`/`nconstP`: solc's typed compile-time evaluation
  (`TEval`/`NamedConst`), returning the derivations (sound by
  construction); `teval_complete`/`nconst_complete`: every value is found
  with enough levels of named constants.  The checker runs with
  `levels E = E.decls.length + 1` levels; that this bound suffices for
  every acyclic definition is not proved.
- `evalConst`, `arrayLenB`: constant expressions and array lengths with
  named constants (`evalConst_sound`, `arrayLenB_sound`).
- `acyclicB`: decides `ConstsAcyclic` (`acyclic_iff`), with `Closure.lean`.
-/

namespace Solidity.Frontend.Static

open Solidity.Source

/-! ## Purity -/

section
variable (Γ : Ctx)

/-- Both or none. -/
def both {P Q R : Prop} (a : Option (PLift P)) (b : Option (PLift Q)) (f : P → Q → R) : Option (PLift R) :=
  match a, b with
  | Option.some ⟨ha⟩, Option.some ⟨hb⟩ => Option.some ⟨f ha hb⟩
  | _, _ => Option.none

/-- A name denoting a constant. -/
def identP (x : String) : Option (PLift (PureS Γ .expr (.ident x))) :=
  match hr : Γ.resolve x with
  | Option.some (.decls [d]) => if hc : d.isConst = true then Option.some ⟨.named hr hc⟩ else Option.none
  | _ => Option.none

/-- **Purity**, decided over every category, with its proof: sound by
construction. -/
def pureP : {c : Cat} → (s : Syn c) → Option (PLift (PureS Γ c s))
  | _, .nil => Option.some ⟨.nil⟩
  | _, .cons x xs => both (pureP x) (pureP xs) .cons
  | _, .some x => (pureP x).map fun ⟨h⟩ => ⟨.some h⟩
  | _, .positional es => (pureP es).map fun ⟨h⟩ => ⟨.positional h⟩
  | _, .lit l => Option.some ⟨.lit l⟩
  | _, .litUnit n u => Option.some ⟨.litUnit n u⟩
  | _, .ident x => identP Γ x
  | _, .tuple o s => both (pureP o) (pureP s) .tuple
  | _, .unaryPrefix op x =>
    if hp : op.pure = true then (pureP x).map fun ⟨h⟩ => ⟨.unary hp h⟩ else Option.none
  | _, .mulDivMod op a b => both (pureP a) (pureP b) fun ha hb => .binary rfl ha hb
  | _, .addSub op a b => both (pureP a) (pureP b) fun ha hb => .binary rfl ha hb
  | _, .bitAnd a b => both (pureP a) (pureP b) fun ha hb => .binary rfl ha hb
  | _, .bitOr a b => both (pureP a) (pureP b) fun ha hb => .binary rfl ha hb
  | _, .bitXor a b => both (pureP a) (pureP b) fun ha hb => .binary rfl ha hb
  | _, .shift op a b => both (pureP a) (pureP b) fun ha hb => .binary rfl ha hb
  | _, .exp a b => both (pureP a) (pureP b) fun ha hb => .binary rfl ha hb
  | _, .order op a b => both (pureP a) (pureP b) fun ha hb => .binary rfl ha hb
  | _, .equality op a b => both (pureP a) (pureP b) fun ha hb => .binary rfl ha hb
  | _, .and a b => both (pureP a) (pureP b) fun ha hb => .binary rfl ha hb
  | _, .or a b => both (pureP a) (pureP b) fun ha hb => .binary rfl ha hb
  | _, .cond c a b => both (pureP c) (both (pureP a) (pureP b) And.intro) fun hc h => .cond hc h.1 h.2
  | _, .call f a =>
    if hh : pureHead Γ f = true then (pureP a).map fun ⟨h⟩ => ⟨.call hh h⟩ else Option.none
  | _, .payableConv a => (pureP a).map fun ⟨h⟩ => ⟨.payable h⟩
  | _, _ => Option.none

/-- Purity as a Boolean. -/
def pureB {c : Cat} (s : Syn c) : Bool := (pureP Γ s).isSome

end

theorem pureB_sound {Γ : Ctx} {c : Cat} {s : Syn c} (h : pureB Γ s = true) : PureS Γ c s := by
  unfold pureB at h
  cases hp : pureP Γ s with
  | none => rw [hp] at h; cases h
  | some p => exact p.down

theorem both_some {P Q R : Prop} {a : Option (PLift P)} {b : Option (PLift Q)} {f : P → Q → R}
    (ha : a.isSome = true) (hb : b.isSome = true) : (both a b f).isSome = true := by
  cases a with
  | none => cases ha
  | some x => cases b with
    | none => cases hb
    | some y => rfl

theorem map_some {P R : Prop} {a : Option (PLift P)} {f : PLift P → PLift R} (ha : a.isSome = true) :
    (a.map f).isSome = true := by
  cases a with
  | none => cases ha
  | some _ => rfl

theorem binary_pure {Γ : Ctx} {e a b : Syn .expr} {k : BinKind} (hk : e.binOp? = Option.some (k, a, b))
    (ha : (pureP Γ a).isSome = true) (hb : (pureP Γ b).isSome = true) : (pureP Γ e).isSome = true := by
  cases e <;> cases hk <;> exact both_some ha hb

theorem pureB_complete {Γ : Ctx} {c : Cat} {s : Syn c} (h : PureS Γ c s) : pureB Γ s = true := by
  unfold pureB
  induction h with
  | nil => rfl
  | cons _ _ ih ih' => exact both_some ih ih'
  | some _ ih => exact map_some ih
  | positional _ ih => exact map_some ih
  | lit _ => rfl
  | litUnit _ _ => rfl
  | named hr hc =>
    rename_i x d
    show (identP Γ x).isSome = true
    unfold identP
    split
    · rename_i d' hr'
      rw [hr] at hr'; cases hr'
      rw [dif_pos hc]; rfl
    · rename_i hn; exact absurd hr (hn d)
  | tuple _ _ ih ih' => exact both_some ih ih'
  | unary hp _ ih =>
    show (if hp : _ = true then _ else Option.none).isSome = true
    rw [dif_pos hp]; exact map_some ih
  | binary hk _ _ iha ihb => exact binary_pure hk iha ihb
  | cond _ _ _ ih ih' ih'' => exact both_some ih (both_some ih' ih'')
  | call hh _ ih =>
    show (if hh : _ = true then _ else Option.none).isSome = true
    rw [dif_pos hh]; exact map_some ih
  | payable _ ih => exact map_some ih

/-- **Purity is decided.** -/
theorem pureB_iff {Γ : Ctx} {e : Syn .expr} : pureB Γ e = true ↔ Pure Γ e :=
  ⟨pureB_sound, pureB_complete⟩

/-- The compile-time check of every constant's initializer. -/
def constInitsB (r : Resolution) : Bool :=
  r.unit.decls.all fun d => !d.isConst ||
    match d.init? with
    | Option.some e => pureB (Ctx.forInit r.env d.scope) e
    | Option.none => true

/-- **The check decides `ConstInitsPure`.** -/
theorem constInitsB_iff {r : Resolution} : constInitsB r = true ↔ ConstInitsPure r := by
  simp only [constInitsB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h d hd hc e he
    rcases h d hd with h' | h'
    · rw [hc] at h'; cases h'
    · rw [he] at h'
      exact pureB_iff.mp h'
  · intro h d hd
    cases hc : d.isConst with
    | false => exact .inl rfl
    | true =>
      right
      cases he : d.init? with
      | none => rfl
      | some e => exact pureB_iff.mpr (h d hd hc e he)

/-! ## Named constants -/

/-- A compile-time value of a tree with its evaluation, at expressions. -/
inductive TRes (E : Env) (scope : Option String) : (c : Cat) → Syn c → Type where
  | ev {e : Syn .expr} (v : TVal) : TEval E scope e v → TRes E scope .expr e

/-- The value of a result. -/
def TRes.val {E : Env} {scope : Option String} {c : Cat} {s : Syn c} : TRes E scope c s → TVal
  | .ev v _ => v

section
variable (E : Env) (scope : Option String)

/-- A literal-only expression's exact value, else the given evaluation. -/
def withConst (e : Syn .expr) (k : Option (TRes E scope .expr e)) : Option (TRes E scope .expr e) :=
  match h : e.const with
  | Option.some q => Option.some (.ev (Option.none, q) (.rational h))
  | Option.none => k

/-- A binary operation with a typed operand. -/
def binT (e : Syn .expr) (k : ConstOp) (a b : Syn .expr) (hk : e.constBin? = Option.some (k, a, b)) :
    Option (TRes E scope .expr a) → Option (TRes E scope .expr b) → Option (TRes E scope .expr e)
  | Option.some (.ev va ha), Option.some (.ev vb hb) =>
    if hs : (va.1.isSome || vb.1.isSome) = true then
      match ht : k.resultTy va vb with
      | Option.some t =>
        match hla : va.2.lit?, hlb : vb.2.lit? with
        | Option.some la, Option.some lb =>
          match hr : (k.mk la lb).const with
          | Option.some r =>
            match hr' : r.toIntTy? t with
            | Option.some r' => Option.some (.ev (Option.some t, r') (.binary hk ha hb hs ht hla hlb hr hr'))
            | Option.none => Option.none
          | Option.none => Option.none
        | _, _ => Option.none
      | Option.none => Option.none
    else Option.none
  | _, _ => Option.none

/-- A unary operation on a typed operand. -/
def unT (op : PrefixOp) (x : Syn .expr) : Option (TRes E scope .expr x) →
    Option (TRes E scope .expr (.unaryPrefix op x))
  | Option.some (.ev (Option.some t, q) hx) =>
    if hop : op = .neg ∨ op = .bitNot then
      match hl : q.lit? with
      | Option.some l =>
        match hr : (Syn.unaryPrefix op l).const with
        | Option.some r =>
          match hr' : r.toIntTy? t with
          | Option.some r' => Option.some (.ev (Option.some t, r') (.unary hop hx hl hr hr'))
          | Option.none => Option.none
        | Option.none => Option.none
      | Option.none => Option.none
    else Option.none
  | _ => Option.none

/-- A parenthesized typed value. -/
def parenT (e : Syn .expr) : Option (TRes E scope .expr e) → Option (TRes E scope .expr (.tuple (.some e) .nil))
  | Option.some (.ev (Option.some t, q) h) => Option.some (.ev (Option.some t, q) (.paren h))
  | _ => Option.none

/-- **Compile-time evaluation**, given the named constants' values, with
the evaluation itself: sound by construction. -/
def tevalP (named : (x : String) → Option {p : IntTy × Q // NamedConst E scope x p.1 p.2}) :
    {c : Cat} → (s : Syn c) → Option (TRes E scope c s)
  | _, .ident x => withConst E scope (.ident x)
      ((named x).map fun p => .ev (Option.some p.1.1, p.1.2) (.named p.2))
  | _, .lit l => withConst E scope (.lit l) Option.none
  | _, .litUnit n u => withConst E scope (.litUnit n u) Option.none
  | _, .tuple (.some e) .nil => withConst E scope _ (parenT E scope e (tevalP named e))
  | _, .unaryPrefix op x => withConst E scope _ (unT E scope op x (tevalP named x))
  | _, .addSub .add a b => withConst E scope _ (binT E scope _ .add a b rfl (tevalP named a) (tevalP named b))
  | _, .addSub .sub a b => withConst E scope _ (binT E scope _ .sub a b rfl (tevalP named a) (tevalP named b))
  | _, .mulDivMod .mul a b => withConst E scope _ (binT E scope _ .mul a b rfl (tevalP named a) (tevalP named b))
  | _, .mulDivMod .div a b => withConst E scope _ (binT E scope _ .div a b rfl (tevalP named a) (tevalP named b))
  | _, .mulDivMod .mod a b => withConst E scope _ (binT E scope _ .mod a b rfl (tevalP named a) (tevalP named b))
  | _, .exp a b => withConst E scope _ (binT E scope _ .exp a b rfl (tevalP named a) (tevalP named b))
  | _, .shift .shl a b => withConst E scope _ (binT E scope _ .shl a b rfl (tevalP named a) (tevalP named b))
  | _, .shift .sar a b => withConst E scope _ (binT E scope _ .sar a b rfl (tevalP named a) (tevalP named b))
  | _, .bitAnd a b => withConst E scope _ (binT E scope _ .bitAnd a b rfl (tevalP named a) (tevalP named b))
  | _, .bitOr a b => withConst E scope _ (binT E scope _ .bitOr a b rfl (tevalP named a) (tevalP named b))
  | _, .bitXor a b => withConst E scope _ (binT E scope _ .bitXor a b rfl (tevalP named a) (tevalP named b))
  | _, _ => Option.none

end

/-- **The value of a named constant**, with `n` levels of constants, with
its derivation. -/
def nconstP (E : Env) : Nat → (scope : Option String) → (x : String) →
    Option {p : IntTy × Q // NamedConst E scope x p.1 p.2}
  | 0, _, _ => Option.none
  | n + 1, scope, x =>
    match hl : E.lookup scope x with
    | [d] =>
      if hc : d.isConst = true then
        match he : d.init? with
        | Option.some e =>
          match hv : d.varTy E with
          | Option.some (.int t) =>
            match tevalP E d.scope (nconstP E n d.scope) e with
            | Option.some (.ev v hev) =>
              match hq : v.2.toIntTy? t with
              | Option.some q => Option.some ⟨(t, q), .mk hl hc he hv hev hq⟩
              | Option.none => Option.none
            | Option.none => Option.none
          | _ => Option.none
        | Option.none => Option.none
      else Option.none
    | _ => Option.none

/-- The levels the checker allows. -/
def levels (E : Env) : Nat := E.decls.length + 1

/-- The value of a constant expression in a scope. -/
def evalConst (E : Env) (scope : Option String) (e : Syn .expr) : Option TVal :=
  (tevalP E scope (nconstP E (levels E) scope) e).map TRes.val

theorem evalConst_sound {E : Env} {scope : Option String} {e : Syn .expr} {v : TVal}
    (h : evalConst E scope e = Option.some v) : TEval E scope e v := by
  unfold evalConst at h
  cases hp : tevalP E scope (nconstP E (levels E) scope) e with
  | none => rw [hp] at h; cases h
  | some r =>
    rw [hp] at h
    cases r with
    | ev v' hv =>
      simp only [Option.map_some, TRes.val, Option.some.injEq] at h
      subst h
      exact hv

/-- An array length with named constants. -/
def arrayLenB (E : Env) (scope : Option String) : Syn (.opt .expr) → Option (Option Nat)
  | .none => Option.some Option.none
  | .some e =>
    match evalConst E scope e with
    | Option.some v => if v.2.isInt ∧ 0 < v.2.toInt then Option.some (Option.some v.2.toInt.toNat) else Option.none
    | Option.none => Option.none

theorem arrayLenB_sound {E : Env} {scope : Option String} {o : Syn (.opt .expr)} {n : Option Nat}
    (h : arrayLenB E scope o = Option.some n) : ArrayLenOK E scope o n := by
  cases o with
  | none => simp only [arrayLenB, Option.some.injEq] at h; subst h; exact .dynamic
  | some e =>
    simp only [arrayLenB] at h
    split at h
    · rename_i v hv
      split at h
      · rename_i hp
        simp only [Option.some.injEq] at h
        subst h
        exact .static ⟨v.1, evalConst_sound hv⟩ hp.1 hp.2
      · cases h
    · cases h

/-! ### Completeness -/

section
variable {E : Env} {scope : Option String}

theorem withConst_const {e : Syn .expr} {k : Option (TRes E scope .expr e)} {q : Q} (h : e.const = Option.some q) :
    (withConst E scope e k).map TRes.val = Option.some (Option.none, q) := by
  unfold withConst
  split
  · rename_i q' h'
    rw [h] at h'; cases h'; rfl
  · rename_i h'; rw [h] at h'; cases h'

theorem withConst_none {e : Syn .expr} {k : Option (TRes E scope .expr e)} (h : e.const = Option.none) :
    withConst E scope e k = k := by
  unfold withConst
  split
  · rename_i q' h'; rw [h] at h'; cases h'
  · rfl

/-- A literal-only expression evaluates to its exact value. -/
theorem tevalP_const {named : (x : String) → Option {p : IntTy × Q // NamedConst E scope x p.1 p.2}}
    {e : Syn .expr} {q : Q} (h : e.const = Option.some q) :
    (tevalP E scope named e).map TRes.val = Option.some (Option.none, q) := by
  cases e with
  | tuple o s =>
    cases o with
    | none => cases h
    | some e' =>
      cases s with
      | nil => exact withConst_const h
      | cons _ _ => cases h
  | addSub op a b => cases op <;> exact withConst_const h
  | mulDivMod op a b => cases op <;> exact withConst_const h
  | shift op a b => cases op <;> first | exact withConst_const h | cases h
  | _ => first | exact withConst_const h | cases h

theorem constBin_eq {e a b : Syn .expr} {k : ConstOp} (hk : e.constBin? = Option.some (k, a, b)) :
    e = k.mk a b := by
  cases e <;> first
    | (cases hk; rfl)
    | (rename_i op _ _; cases op <;> first | (cases hk; rfl) | cases hk)
    | cases hk

theorem mk_const_none {k : ConstOp} {a b : Syn .expr} (h : a.const = Option.none ∨ b.const = Option.none) :
    (k.mk a b).const = Option.none := by
  rcases h with h | h
  · cases k
    all_goals first
      | (show (a.const >>= fun x => b.const >>= fun y => _) = Option.none; rw [h]; rfl)
      | (show (b.const >>= fun y => y.int? >>= fun k => a.const >>= fun x => _) = Option.none
         rw [h]; cases b.const with
         | none => rfl
         | some q => show (q.int? >>= fun k => _) = Option.none; cases q.int? <;> rfl)
      | (show (a.const >>= fun qa => qa.int? >>= fun x => b.const >>= fun qb => _) = Option.none
         rw [h]; rfl)
  · cases k
    all_goals first
      | (show (a.const >>= fun x => b.const >>= fun y => _) = Option.none; rw [h]; cases a.const <;> rfl)
      | (show (b.const >>= fun y => _) = Option.none; rw [h]; rfl)
      | (show (a.const >>= fun qa => qa.int? >>= fun x => b.const >>= fun qb => _) = Option.none
         rw [h]; cases a.const with
         | none => rfl
         | some q => show (q.int? >>= fun x => _) = Option.none; cases q.int? <;> rfl)

theorem unary_const_none {op : PrefixOp} {x : Syn .expr} (hop : op = .neg ∨ op = .bitNot)
    (h : x.const = Option.none) : (Syn.unaryPrefix op x).const = Option.none := by
  rcases hop with e | e <;> subst e
  · show Option.map Q.neg x.const = Option.none
    rw [h]; rfl
  · show (x.const >>= fun q => q.int? >>= fun k => pure (Q.ofInt (Int.bitNot k))) = Option.none
    rw [h]; rfl

/-- A typed value never comes from a literal-only expression. -/
theorem typed_const_none : {e : Syn .expr} → {v : TVal} → TEval E scope e v → v.1.isSome = true →
    e.const = Option.none
  | _, _, .rational _, h => by cases h
  | _, _, .named _, _ => rfl
  | _, _, .paren he, _ => by have h := typed_const_none he rfl; exact h
  | _, _, .unary hop hx _ _ _, _ => unary_const_none hop (typed_const_none hx rfl)
  | _, _, .binary (va := va) (vb := vb) hk ha hb hs _ _ _ _ _, _ => by
    rw [constBin_eq hk]
    apply mk_const_none
    cases hva : va.1 with
    | some _ => exact .inl (typed_const_none ha (by rw [hva]; rfl))
    | none =>
      rw [hva] at hs
      exact .inr (typed_const_none hb (by simpa only [Option.isSome_none, Bool.false_or] using hs))

theorem tevalP_bin {named : (x : String) → Option {p : IntTy × Q // NamedConst E scope x p.1 p.2}}
    {e a b : Syn .expr} {k : ConstOp} (hk : e.constBin? = Option.some (k, a, b)) :
    tevalP E scope named e =
      withConst E scope e (binT E scope e k a b hk (tevalP E scope named a) (tevalP E scope named b)) := by
  obtain rfl := constBin_eq hk
  cases k <;> rfl

theorem binT_val {e a b : Syn .expr} {k : ConstOp} {hk : e.constBin? = Option.some (k, a, b)}
    {ra : Option (TRes E scope .expr a)} {rb : Option (TRes E scope .expr b)} {va vb : TVal} {t : IntTy}
    {la lb : Syn .expr} {r r' : Q}
    (ha : ra.map TRes.val = Option.some va) (hb : rb.map TRes.val = Option.some vb)
    (hs : (va.1.isSome || vb.1.isSome) = true) (ht : k.resultTy va vb = Option.some t)
    (hla : va.2.lit? = Option.some la) (hlb : vb.2.lit? = Option.some lb)
    (hr : (k.mk la lb).const = Option.some r) (hr' : r.toIntTy? t = Option.some r') :
    (binT E scope e k a b hk ra rb).map TRes.val = Option.some (Option.some t, r') := by
  cases ra with
  | none => cases ha
  | some x =>
    cases x with
    | ev va' ha' =>
      cases ha
      cases rb with
      | none => cases hb
      | some y =>
        cases y with
        | ev vb' hb' =>
          cases hb
          simp only [TRes.val] at hs ht hla hlb
          simp only [binT]
          rw [dif_pos hs]
          split
          · rename_i t' ht'
            rw [ht] at ht'; cases ht'
            split
            · rename_i la' lb' hla' hlb'
              rw [hla] at hla'; cases hla'
              rw [hlb] at hlb'; cases hlb'
              split
              · rename_i r₁ hr₁
                rw [hr] at hr₁; cases hr₁
                split
                · rename_i r₂ hr₂
                  rw [hr'] at hr₂; cases hr₂; rfl
                · rename_i hr₂; rw [hr'] at hr₂; cases hr₂
              · rename_i hr₁; rw [hr] at hr₁; cases hr₁
            · rename_i hn; exact absurd hlb (hn la lb hla)
          · rename_i ht'; rw [ht] at ht'; cases ht'

theorem unT_val {op : PrefixOp} {x : Syn .expr} {rx : Option (TRes E scope .expr x)} {t : IntTy}
    {q r r' : Q} {l : Syn .expr} (hx : rx.map TRes.val = Option.some (Option.some t, q))
    (hop : op = .neg ∨ op = .bitNot) (hl : q.lit? = Option.some l)
    (hr : (Syn.unaryPrefix op l).const = Option.some r) (hr' : r.toIntTy? t = Option.some r') :
    (unT E scope op x rx).map TRes.val = Option.some (Option.some t, r') := by
  cases rx with
  | none => cases hx
  | some y =>
    cases y with
    | ev v hv =>
      cases hx
      simp only [unT]
      rw [dif_pos hop]
      split
      · rename_i l' hl'
        rw [hl] at hl'; cases hl'
        split
        · rename_i r₁ hr₁
          rw [hr] at hr₁; cases hr₁
          split
          · rename_i r₂ hr₂
            rw [hr'] at hr₂; cases hr₂; rfl
          · rename_i hr₂; rw [hr'] at hr₂; cases hr₂
        · rename_i hr₁; rw [hr] at hr₁; cases hr₁
      · rename_i hl'; rw [hl] at hl'; cases hl'

theorem parenT_val {e : Syn .expr} {re : Option (TRes E scope .expr e)} {t : IntTy} {q : Q}
    (h : re.map TRes.val = Option.some (Option.some t, q)) :
    (parenT E scope e re).map TRes.val = Option.some (Option.some t, q) := by
  cases re with
  | none => cases h
  | some y =>
    cases y with
    | ev v hv => cases h; rfl

end

mutual

/-- **Complete**: every compile-time value is computed with enough levels. -/
theorem teval_complete {E : Env} : {scope : Option String} → {e : Syn .expr} → {v : TVal} →
    TEval E scope e v → ∃ N, ∀ n, N ≤ n → (tevalP E scope (nconstP E n scope) e).map TRes.val = Option.some v
  | _, _, _, .rational h => ⟨0, fun _ _ => tevalP_const h⟩
  | _, _, _, .named hn => by
    obtain ⟨N, hN⟩ := nconst_complete hn
    refine ⟨N, fun n hn' => ?_⟩
    show (withConst E _ (.ident _) _).map TRes.val = _
    rw [withConst_none rfl]
    have h := hN n hn'
    cases hp : nconstP E n _ _ with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp only [Option.map_some, TRes.val, h]
  | _, _, _, .paren he => by
    obtain ⟨N, hN⟩ := teval_complete he
    refine ⟨N, fun n hn => ?_⟩
    show (withConst E _ (.tuple (.some _) .nil) _).map TRes.val = _
    rw [withConst_none (typed_const_none (.paren he) rfl)]
    exact parenT_val (hN n hn)
  | _, _, _, .unary hop hx hl hr hr' => by
    obtain ⟨N, hN⟩ := teval_complete hx
    refine ⟨N, fun n hn => ?_⟩
    show (withConst E _ (.unaryPrefix _ _) _).map TRes.val = _
    rw [withConst_none (typed_const_none (.unary hop hx hl hr hr') rfl)]
    exact unT_val (hN n hn) hop hl hr hr'
  | _, _, _, .binary hk ha hb hs ht hla hlb hr hr' => by
    obtain ⟨Na, hNa⟩ := teval_complete ha
    obtain ⟨Nb, hNb⟩ := teval_complete hb
    refine ⟨max Na Nb, fun n hn => ?_⟩
    rw [tevalP_bin hk, withConst_none (typed_const_none (.binary hk ha hb hs ht hla hlb hr hr') rfl)]
    exact binT_val (hNa n (by omega)) (hNb n (by omega)) hs ht hla hlb hr hr'

/-- **Complete**: every named constant's value is computed with enough
levels. -/
theorem nconst_complete {E : Env} : {scope : Option String} → {x : String} → {t : IntTy} → {q : Q} →
    NamedConst E scope x t q → ∃ N, ∀ n, N ≤ n → (nconstP E n scope x).map Subtype.val = Option.some (t, q)
  | _, _, _, _, .mk (d := d) (e := e) (v := v) hl hc he hv hev hq => by
    obtain ⟨N, hN⟩ := teval_complete hev
    refine ⟨N + 1, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm := hN m (by omega)
    unfold nconstP
    split
    · rename_i d' hl'
      rw [hl] at hl'; cases hl'
      rw [dif_pos hc]
      split
      · rename_i e' he'
        rw [he] at he'; cases he'
        split
        · rename_i t' hv'
          rw [hv] at hv'; cases hv'
          split
          · rename_i v' hev' heq
            rw [heq] at hm
            cases hm
            simp only [TRes.val] at hq
            split
            · rename_i q' hq'
              rw [hq] at hq'; cases hq'; rfl
            · rename_i hq'; rw [hq] at hq'; cases hq'
          · rename_i heq; rw [heq] at hm; cases hm
        · rename_i hn'; exact absurd hv (hn' _)
      · rename_i he'; rw [he] at he'; cases he'
    · rename_i hn'; exact absurd hl (hn' d)

end

/-- **Constant expressions**: everything `evalConst` computes is a value,
and every value is computed with enough levels. -/
theorem evalConst_complete {E : Env} {scope : Option String} {e : Syn .expr} {v : TVal}
    (h : TEval E scope e v) : ∃ N, ∀ n, N ≤ n →
      (tevalP E scope (nconstP E n scope) e).map TRes.val = Option.some v :=
  teval_complete h

/-! ## Acyclic constants -/

theorem Env.declared_sub {E : Env} {s : Option String} {x : String} {d : Decl}
    (h : d ∈ E.declared s x) : d ∈ E.decls := (List.mem_filter.mp h).1

theorem Env.visible_sub {E : Env} {c s : Option String} {x : String} {d : Decl}
    (h : d ∈ E.visible c s x) : d ∈ E.decls := Env.declared_sub (List.mem_filter.mp h).1

theorem Env.lookup_sub {E : Env} {s : Option String} {x : String} {d : Decl}
    (h : d ∈ E.lookup s x) : d ∈ E.decls := by
  unfold Env.lookup at h
  simp only at h
  split at h
  · exact Env.visible_sub h
  · exact Env.declared_sub h

theorem Env.lookupPath_sub {E : Env} {s : Option String} {p : IdPath} {d : Decl}
    (h : d ∈ E.lookupPath s p) : d ∈ E.decls := by
  unfold Env.lookupPath at h
  split at h
  · exact Env.lookup_sub h
  · exact Env.declared_sub h
  · cases h

/-- The constants of an environment, as nodes. -/
def constNodes (E : Env) : List (Option String × String) :=
  (E.decls.filter (·.isConst)).map fun d => (d.scope, d.name)

theorem constDeps_sub {E : Env} {a b : Option String × String} (h : b ∈ E.constDeps a) :
    b ∈ constNodes E := by
  unfold Env.constDeps at h
  split at h
  · split at h
    · split at h
      · obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp h
        split at hp
        · rename_i d' hd'
          split at hp
          · rename_i hc
            cases hp
            exact List.mem_map.mpr ⟨d', List.mem_filter.mpr
              ⟨Env.lookupPath_sub (by rw [hd']; exact List.mem_singleton.mpr rfl), hc⟩, rfl⟩
          · cases hp
        · cases hp
      · cases h
    · cases h
  · cases h

theorem depPath_iff {E : Env} {a b : Option String × String} :
    DepPath E a b ↔ ∃ m, m ∈ E.constDeps a ∧ Reach E.constDeps m b := by
  constructor
  · intro h
    induction h with
    | step hb => exact ⟨_, hb, .refl _⟩
    | trans hb _ ih =>
      obtain ⟨m, hm, hr⟩ := ih
      exact ⟨_, hb, .step hm hr⟩
  · intro ⟨m, hm, hr⟩
    induction hr generalizing a with
    | refl => exact .step hm
    | step hb _ ih => exact .trans hm (ih hb)

/-- **The cycle check.** -/
def acyclicB (E : Env) : Bool :=
  (E.decls.filter (·.isConst)).all fun d =>
    (E.constDeps (d.scope, d.name)).all fun m =>
      !(reachable E.constDeps (constNodes E) m).contains (d.scope, d.name)

/-- **The check decides `ConstsAcyclic`.** -/
theorem acyclic_iff {E : Env} : acyclicB E = true ↔ ConstsAcyclic E := by
  have hU : ∀ a, a ∈ constNodes E → ∀ b, b ∈ E.constDeps a → b ∈ constNodes E :=
    fun _ _ _ hb => constDeps_sub hb
  simp only [acyclicB, List.all_eq_true, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, and_imp]
  constructor
  · intro h d hd hc hp
    obtain ⟨m, hm, hr⟩ := depPath_iff.mp hp
    exact h d hd hc m hm ((mem_reachable hU (constDeps_sub hm)).mpr hr)
  · intro h d hd hc m hm hr
    exact h d hd hc (depPath_iff.mpr ⟨m, hm, (mem_reachable hU (constDeps_sub hm)).mp hr⟩)

end Solidity.Frontend.Static