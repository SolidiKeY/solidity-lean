import Solidity.Source.Typing

/-!
# The resolved layer (S01)

S01's output, intrinsically typed: expressions and statements over a
context of local *types* (`RCtx := List STy`, names kept beside it, as
Gate G0 condition 3 asks), with

- locals by position (`Idx Γ τ`); state variables, functions, events and
  errors by their declaration (`Decl`, so the overload is the one chosen),
  with the premise fixing the term's type (`d.varTy E = some τ`,
  `d.fnSig E = some (ps, rs)`, `d.paramTys E = some ps`);
- every implicit conversion an explicit node (`RExpr.conv`, carrying its
  proof), arguments converted to their parameters (`RConvArgs`), every
  explicit conversion a node (`RExpr.convExplicit`);
- operators by name (`BinOp`), constants by their exact value; no
  constructor leaves its result type free;
- statements indexed by their context (`SCtx`: `break`/`continue` only in a
  loop body, `unchecked` blocks not nested), the enclosing function's return
  types (`return` converts to them) and the modifier flag (`_` only in a
  modifier).

`Typed.toR`, `StmtD.toR` and `ItemsD.toR` read a typing derivation
(`Solidity/Source/Typing.lean`) as such a term, at the derivation's type.
Nothing of S00's string names remains in a resolved term except
declarations, which are identities.  S02 defines its semantics over these
terms.
-/

namespace Solidity.Source

/-- A context of local types, innermost first. -/
abbrev RCtx := List STy

/-- A position in a context, with its type. -/
inductive Idx : RCtx → STy → Type where
  | here {τ : STy} {Γ : RCtx} : Idx (τ :: Γ) τ
  | there {σ τ : STy} {Γ : RCtx} : Idx Γ τ → Idx (σ :: Γ) τ

/-- The position `i` of a context whose `i`-th type is `τ`. -/
def Idx.ofGet? : (Γ : RCtx) → (i : Nat) → {τ : STy} → Γ[i]? = some τ → Idx Γ τ
  | [], _, _, h => nomatch h
  | σ :: _, 0, _, h => by
    have e : σ = _ := Option.some.inj h
    exact e ▸ .here
  | _ :: Γ, i + 1, _, h => .there (Idx.ofGet? Γ i h)

/-- The position as a number. -/
def Idx.toNat {Γ : RCtx} {τ : STy} : Idx Γ τ → Nat
  | .here => 0
  | .there i => i.toNat + 1

/-- Binary operators by name. -/
inductive BinOp where
  | mul | div | mod | add | sub | bitAnd | bitOr | bitXor | shl | sar | shr | exp
  | lt | gt | le | ge | eq | ne | and | or
  deriving DecidableEq, Repr

/-- The operator of a binary expression (`.add` for any other). -/
def Syn.binOpName : Syn .expr → BinOp
  | .mulDivMod .mul _ _ => .mul | .mulDivMod .div _ _ => .div | .mulDivMod .mod _ _ => .mod
  | .addSub .add _ _ => .add | .addSub .sub _ _ => .sub
  | .bitAnd _ _ => .bitAnd | .bitOr _ _ => .bitOr | .bitXor _ _ => .bitXor
  | .shift .shl _ _ => .shl | .shift .sar _ _ => .sar | .shift .shr _ _ => .shr
  | .exp _ _ => .exp
  | .order .lt _ _ => .lt | .order .gt _ _ => .gt | .order .le _ _ => .le | .order .ge _ _ => .ge
  | .equality .eq _ _ => .eq | .equality .ne _ _ => .ne
  | .and _ _ => .and | .or _ _ => .or
  | _ => .add

/-- A conversion where two operand types meet: implicit, or none. -/
def Conv (B : DeclName → DeclName → Bool) (σ τ : STy) : Prop := σ.implicit B τ = true ∨ σ = τ

theorem common?_left {B : DeclName → DeclName → Bool} {a b c : STy} (h : STy.common? B a b = some c) :
    Conv B a c := by
  simp only [STy.common?] at h
  split at h
  · cases h; exact .inl (by assumption)
  · split at h
    · cases h; exact .inr rfl
    · cases h

theorem common?_right {B : DeclName → DeclName → Bool} {a b c : STy} (h : STy.common? B a b = some c) :
    Conv B b c := by
  simp only [STy.common?] at h
  split at h
  · cases h; exact .inr rfl
  · split at h
    · cases h; exact .inl (by assumption)
    · cases h

/-- A constant's mobile integer type holds it. -/
theorem Q.mobileInt?_fits {q : Q} {t : IntTy} (h : q.mobileInt? = some t) : q.FitsInt t := by
  simp only [Q.mobileInt?] at h
  split at h
  · rename_i hi
    have hm := List.mem_of_mem_head? h
    obtain ⟨k, _, hk⟩ := List.mem_filterMap.1 hm
    split at hk
    · split at hk
      · rename_i hr
        cases hk
        exact ⟨hi, hr.1, hr.2⟩
      · cases hk
    · cases hk
  · cases h

/-- A type converts to its mobile type. -/
theorem mobile_conv {B : DeclName → DeclName → Bool} {τ : STy} : Conv B τ τ.mobile := by
  cases τ with
  | rational q =>
    simp only [Conv, STy.mobile]
    cases hm : q.mobileInt? with
    | none => exact .inr rfl
    | some t =>
      left
      simp only [STy.implicit, decide_eq_true_eq]
      exact Q.mobileInt?_fits hm
  | stringLit bs => exact .inl rfl
  | _ => exact .inr rfl

mutual

/-- **Resolved expressions** over environment `E`, intrinsically typed. -/
inductive RExpr (E : Env) (Γ : RCtx) : STy → Type where
  | const (q : Q) : RExpr E Γ (.rational q)
  | bytesLit {len : Nat} {h : 1 ≤ len ∧ len ≤ 32} (n : NumLit) (hn : n.fitsBytes len = true) :
      RExpr E Γ (.fixedBytes len h)
  | addressLit (ds : List (Fin 16)) : RExpr E Γ (.address false)
  | bool (b : Bool) : RExpr E Γ .bool
  | str (bs : List UInt8) : RExpr E Γ (.stringLit bs)
  | local {τ : STy} (i : Idx Γ τ) : RExpr E Γ τ
  | state {τ : STy} (d : Decl) (h : d.varTy E = some τ) : RExpr E Γ τ
  | this (c : String) : RExpr E Γ (.contract ⟨none, c⟩)
  | tuple {τs : List STy} (es : RArgs E Γ τs) : RExpr E Γ (.tuple τs)
  /-- An implicit conversion (or the identity where operands already meet). -/
  | conv {σ τ : STy} (e : RExpr E Γ σ) (h : Conv E.isBase σ τ) : RExpr E Γ τ
  | convExplicit {σ τ : STy} (e : RExpr E Γ σ) (h : σ.explicit E.isBase τ = true) : RExpr E Γ τ
  | unary {τ : STy} (op : PrefixOp) (e : RExpr E Γ τ) : RExpr E Γ τ
  | incDec {τ : STy} (inc pre : Bool) (l : RLVal E Γ τ) : RExpr E Γ τ
  | delete {τ : STy} (l : RLVal E Γ τ) : RExpr E Γ (.tuple [])
  /-- An arithmetic, bitwise or logical operation on operands converted to
  their common type, at that type. -/
  | binary {τ : STy} (op : BinOp) (a b : RExpr E Γ τ) : RExpr E Γ τ
  /-- An order or equality comparison at the operands' common type. -/
  | compare {τ : STy} (op : BinOp) (a b : RExpr E Γ τ) : RExpr E Γ .bool
  /-- A comparison of two constants. -/
  | compareConst (op : BinOp) (qa qb : Q) : RExpr E Γ .bool
  /-- A shift or power: the operand at `τ`, the amount at its own type. -/
  | shiftLike {τ σ : STy} (op : BinOp) (a : RExpr E Γ τ) (b : RExpr E Γ σ) (h : σ.isAmount = true) :
      RExpr E Γ τ
  | cond {τ : STy} (c : RExpr E Γ .bool) (a b : RExpr E Γ τ) : RExpr E Γ τ
  | assign {τ : STy} (l : RLVal E Γ τ) (e : RExpr E Γ τ) : RExpr E Γ τ
  | compound {τ σ : STy} (op : AssignOp) (l : RLVal E Γ τ) (e : RExpr E Γ σ)
      (h : op.fits E.isBase σ τ = true) : RExpr E Γ τ
  | indexArray {l : DataLoc} {τ σ : STy} {n : Option Nat} (a : RExpr E Γ (.array l τ n))
      (i : RExpr E Γ σ) (h : σ.isIndex = true) : RExpr E Γ τ
  | indexMapping {τk τv : STy} (a : RExpr E Γ (.mapping τk τv)) (k : RExpr E Γ τk) : RExpr E Γ τv
  | indexBytes {τ σ : STy} (a : RExpr E Γ τ) (i : RExpr E Γ σ) (h : σ.isIndex = true) :
      RExpr E Γ (.fixedBytes 1 (by decide))
  | length {τ ρ : STy} (a : RExpr E Γ τ) (h : τ.lengthTy = some ρ) : RExpr E Γ ρ
  | payable {σ : STy} (e : RExpr E Γ σ) : RExpr E Γ (.address true)
  /-- A call of an internal function, the chosen overload, its arguments
  converted. -/
  | call {ps rs : List STy} (d : Decl) (h : d.fnSig E = some (ps, rs)) (args : RConvArgs E Γ ps) :
      RExpr E Γ (STy.ret rs)
  | magic {τ : STy} (b : Builtin) (m : String) (h : b.memberTy m = some τ) : RExpr E Γ τ
  | balance {p : Bool} (a : RExpr E Γ (.address p)) : RExpr E Γ (.int IntTy.u256)
  | builtin {σs : List STy} {τ : STy} (b : Builtin) (args : RArgs E Γ σs)
      (h : b.callTy E.isBase σs = some τ) : RExpr E Γ τ

/-- Resolved argument lists. -/
inductive RArgs (E : Env) (Γ : RCtx) : List STy → Type where
  | nil : RArgs E Γ []
  | cons {τ : STy} {τs : List STy} : RExpr E Γ τ → RArgs E Γ τs → RArgs E Γ (τ :: τs)

/-- Arguments converted to parameter types. -/
inductive RConvArgs (E : Env) (Γ : RCtx) : List STy → Type where
  | nil : RConvArgs E Γ []
  | cons {σ τ : STy} {τs : List STy} : RExpr E Γ σ → σ.implicit E.isBase τ = true → RConvArgs E Γ τs →
      RConvArgs E Γ (τ :: τs)

/-- Resolved lvalues. -/
inductive RLVal (E : Env) (Γ : RCtx) : STy → Type where
  | local {τ : STy} (i : Idx Γ τ) : RLVal E Γ τ
  | state {τ : STy} (d : Decl) (h : d.varTy E = some τ) (hm : d.mutable = true) : RLVal E Γ τ
  | indexArray {l : DataLoc} {τ σ : STy} {n : Option Nat} (a : RExpr E Γ (.array l τ n))
      (hl : l ≠ .calldata) (i : RExpr E Γ σ) (h : σ.isIndex = true) : RLVal E Γ τ
  | indexMapping {τk τv : STy} (a : RExpr E Γ (.mapping τk τv)) (k : RExpr E Γ τk) : RLVal E Γ τv
  | indexBytes {l : DataLoc} {σ : STy} (a : RExpr E Γ (.bytes l)) (hl : l ≠ .calldata) (i : RExpr E Γ σ)
      (h : σ.isIndex = true) : RLVal E Γ (.fixedBytes 1 (by decide))

end

/-- Converted arguments from typed arguments that fit. -/
def RArgs.convert {E : Env} {Γ : RCtx} :
    {σs : List STy} → (ps : List STy) → RArgs E Γ σs → argsFit E.isBase σs ps = true → RConvArgs E Γ ps
  | [], [], .nil, _ => .nil
  | _ :: _, p :: ps, .cons e es, h => by
    simp only [argsFit, List.length_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
      beq_iff_eq, Nat.add_right_cancel_iff] at h
    exact .cons e h.2.1 (es.convert ps (by
      simp only [argsFit, Bool.and_eq_true, beq_iff_eq]; exact ⟨h.1, h.2.2⟩))
  | [], _ :: _, _, h => by simp only [argsFit, List.length_nil, List.length_cons] at h; cases h
  | _ :: _, [], _, h => by simp only [argsFit, List.length_nil, List.length_cons] at h; cases h

/-- The member of a singleton filter satisfies the filter. -/
theorem mem_of_filter_eq {α : Type} {p : α → Bool} {l : List α} {d : α} (h : l.filter p = [d]) :
    p d = true :=
  (List.mem_filter.1 (h ▸ List.mem_singleton_self d)).2

/-- A matching declaration's parameters, from a singleton filter over
`paramTys` (events, errors). -/
def paramsOf (E : Env) (B : DeclName → DeclName → Bool) (σs : List STy) (d : Decl)
    (h : d.fitsParams E B σs = true) : Σ' ps, d.paramTys E = some ps ∧ argsFit B σs ps = true :=
  match hp : d.paramTys E with
  | some ps => ⟨ps, rfl, by simp only [Decl.fitsParams, hp] at h; exact h⟩
  | none => by simp only [Decl.fitsParams, hp] at h; exact absurd h Bool.false_ne_true

mutual

/-- **Elaboration**: a typing derivation as a resolved expression. -/
def Typed.toR {Γ : Ctx} {e : Syn .expr} {τ : STy} : Typed Γ e τ → RExpr Γ.env Γ.tys τ
  | .const (q := q) _ _ => .const q
  | .litBytes (n := n) h => .bytesLit n h
  | .litAddress (ds := ds) _ => .addressLit ds
  | .bool b => .bool b
  | .str bs => .str bs
  | .hexStr bs => .str bs
  | .unicodeStr bs => .str bs
  | .loc (i := i) _ h => .local (Idx.ofGet? _ i h)
  | .state (d := d) _ h => .state d h
  | .this (c := c) _ _ => .this c
  | .paren d => d.toR
  | .tuple d ds _ => .tuple (.cons (.conv d.toR mobile_conv) (TypedSlots.toR ds))
  | .neg d _ => .unary .neg d.toR
  | .negFixed d => .unary .neg d.toR
  | .not d => .unary .not d.toR
  | .bitNot d _ => .unary .bitNot d.toR
  | .incDec (op := op) _ l _ => .incDec (op == .inc) true l.toR
  | .incDecSuffix (op := op) l _ => .incDec (op == .inc) false l.toR
  | .delete l _ => .delete l.toR
  | .arith (e := e) _ da db h _ _ => .binary e.binOpName (.conv da.toR (common?_left h)) (.conv db.toR (common?_right h))
  | .bit (e := e) _ da db h _ => .binary e.binOpName (.conv da.toR (common?_left h)) (.conv db.toR (common?_right h))
  | .shift (e := e) _ da db _ h _ => .shiftLike e.binOpName (.conv da.toR mobile_conv) db.toR h
  | .exp _ da db _ h _ => .shiftLike .exp (.conv da.toR mobile_conv) db.toR h
  | .order (e := e) _ da db h _ => .compare e.binOpName (.conv da.toR (common?_left h)) (.conv db.toR (common?_right h))
  | .eq (e := e) _ da db h _ => .compare e.binOpName (.conv da.toR (common?_left h)) (.conv db.toR (common?_right h))
  | .compareConst (e := e) (qa := qa) (qb := qb) _ _ _ _ => .compareConst e.binOpName qa qb
  | .logic (e := e) _ da db => .binary e.binOpName da.toR db.toR
  | .cond dc da db h => .cond dc.toR (.conv (.conv da.toR mobile_conv) (common?_left h))
      (.conv (.conv db.toR mobile_conv) (common?_right h))
  | .assign l db h _ => .assign l.toR (.conv db.toR (.inl h))
  | .compound (op := op) l db h => .compound op l.toR db.toR h
  | .indexArray da di h _ => .indexArray da.toR di.toR h
  | .indexMapping da di h => .indexMapping da.toR (.conv di.toR (.inl h))
  | .indexBytes da _ di h _ => .indexBytes da.toR di.toR h
  | .length da h => .length da.toR h
  | .convElem dx hτ h => .convExplicit dx.toR (hτ ▸ h)
  | .convUser _ dx h => .convExplicit dx.toR h
  | .payable dx _ => .payable dx.toR
  | .callInternal (d := d) (ps := ps) da hf hs => .call d hs (RArgs.convert ps da.toR (by
      have hp := mem_of_filter_eq hf
      simp only [hs] at hp
      exact hp))
  | .magic (b := b) (m := m) _ _ h _ => .magic b m h
  | .balance da => .balance da.toR
  | .builtinCall (b := b) _ _ da h => .builtin b da.toR h

/-- Elaboration of argument lists. -/
def TypedArgs.toR {Γ : Ctx} {es : Syn (.list .expr)} {τs : List STy} :
    TypedArgs Γ es τs → RArgs Γ.env Γ.tys τs
  | .nil => .nil
  | .cons d ds => .cons d.toR ds.toR

/-- Elaboration of tuple slots, at their mobile types. -/
def TypedSlots.toR {Γ : Ctx} {es : Syn (.list (.opt .expr))} {τs : List STy} :
    TypedSlots Γ es τs → RArgs Γ.env Γ.tys (τs.map STy.mobile)
  | .nil => .nil
  | .cons d ds => .cons (.conv d.toR mobile_conv) ds.toR

/-- Elaboration of tuple slots as arguments (at their own types). -/
def TypedArgs.ofSlots {Γ : Ctx} {es : Syn (.list (.opt .expr))} {τs : List STy} :
    TypedSlots Γ es τs → RArgs Γ.env Γ.tys τs
  | .nil => .nil
  | .cons d ds => .cons d.toR (TypedArgs.ofSlots ds)

/-- Elaboration of lvalues. -/
def LVal.toR {Γ : Ctx} {e : Syn .expr} {τ : STy} : LVal Γ e τ → RLVal Γ.env Γ.tys τ
  | .loc (i := i) _ h => .local (Idx.ofGet? _ i h)
  | .state (d := d) _ h hm => .state d h hm
  | .paren l => l.toR
  | .indexArray da hl di h _ => .indexArray da.toR hl di.toR h
  | .indexMapping da di h => .indexMapping da.toR (.conv di.toR (.inl h))
  | .indexBytes da hl di h => .indexBytes da.toR hl di.toR h

end

/-! ## Statements -/

/-- An optional loop condition. -/
inductive ROptBool (E : Env) (Γ : RCtx) : Type where
  | none
  | some (c : RExpr E Γ .bool)

/-- An optional loop step. -/
inductive ROptExpr (E : Env) (Γ : RCtx) : Type where
  | none
  | some {τ : STy} (e : RExpr E Γ τ)

mutual

/-- **Resolved statements** of a body with return types `R` (`M`: a
modifier's), in context `k`, from local types `Γ` to `Γ'`. -/
inductive RStmt (E : Env) (R : List STy) (M : Bool) : SCtx → RCtx → RCtx → Type where
  | expr {k : SCtx} {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) : RStmt E R M k Γ Γ
  | placeholder {k : SCtx} {Γ : RCtx} (h : M = true) : RStmt E R M k Γ Γ
  /-- A declaration with the type's default value. -/
  | declVar {k : SCtx} {Γ : RCtx} (τ : STy) : RStmt E R M k Γ (τ :: Γ)
  | declInit {k : SCtx} {Γ : RCtx} {σ τ : STy} (e : RExpr E Γ σ) (h : σ.implicit E.isBase τ = true) :
      RStmt E R M k Γ (τ :: Γ)
  | block {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') : RStmt E R M k Γ Γ
  | ifThen {k : SCtx} {Γ Γ₁ : RCtx} (c : RExpr E Γ .bool) (s : RStmt E R M k Γ Γ₁) : RStmt E R M k Γ Γ
  | ifElse {k : SCtx} {Γ Γ₁ Γ₂ : RCtx} (c : RExpr E Γ .bool) (s : RStmt E R M k Γ Γ₁)
      (t : RStmt E R M k Γ Γ₂) : RStmt E R M k Γ Γ
  | whileLoop {l u : Bool} {Γ Γ₁ : RCtx} (c : RExpr E Γ .bool) (s : RStmt E R M ⟨true, u⟩ Γ Γ₁) :
      RStmt E R M ⟨l, u⟩ Γ Γ
  | doWhile {l u : Bool} {Γ Γ₁ : RCtx} (s : RStmt E R M ⟨true, u⟩ Γ Γ₁) (c : RExpr E Γ .bool) :
      RStmt E R M ⟨l, u⟩ Γ Γ
  | forLoop {l u : Bool} {Γ Γ₁ Γ₂ : RCtx} (init : RStmt E R M ⟨true, u⟩ Γ Γ₁) (c : ROptBool E Γ₁)
      (post : ROptExpr E Γ₁) (s : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) : RStmt E R M ⟨l, u⟩ Γ Γ
  | skip {k : SCtx} {Γ : RCtx} : RStmt E R M k Γ Γ
  | brk {u : Bool} {Γ : RCtx} : RStmt E R M ⟨true, u⟩ Γ Γ
  | cont {u : Bool} {Γ : RCtx} : RStmt E R M ⟨true, u⟩ Γ Γ
  | ret {k : SCtx} {Γ : RCtx} (h : R = []) : RStmt E R M k Γ Γ
  | retVal {k : SCtx} {Γ : RCtx} {σ τ : STy} (hR : R = [τ]) (e : RExpr E Γ σ)
      (h : σ.implicit E.isBase τ = true) : RStmt E R M k Γ Γ
  | retTuple {k : SCtx} {Γ : RCtx} (es : RConvArgs E Γ R) : RStmt E R M k Γ Γ
  | emit {k : SCtx} {Γ : RCtx} {ps : List STy} (ev : Decl) (h : ev.paramTys E = some ps)
      (args : RConvArgs E Γ ps) : RStmt E R M k Γ Γ
  | revertError {k : SCtx} {Γ : RCtx} {ps : List STy} (er : Decl) (h : er.paramTys E = some ps)
      (args : RConvArgs E Γ ps) : RStmt E R M k Γ Γ
  /-- The canonical rethrow of a `bytes memory` local. -/
  | rethrow {k : SCtx} {Γ : RCtx} (i : Idx Γ (.bytes .memory)) : RStmt E R M k Γ Γ

/-- Resolved blocks. -/
inductive RItems (E : Env) (R : List STy) (M : Bool) : SCtx → RCtx → RCtx → Type where
  | nil {k : SCtx} {Γ : RCtx} : RItems E R M k Γ Γ
  | stmt {k : SCtx} {Γ Γ₁ Γ₂ : RCtx} (s : RStmt E R M k Γ Γ₁) (rest : RItems E R M k Γ₁ Γ₂) :
      RItems E R M k Γ Γ₂
  | unchecked {l : Bool} {Γ Γ₁ Γ₂ : RCtx} (b : RItems E R M ⟨l, true⟩ Γ Γ₁)
      (rest : RItems E R M ⟨l, false⟩ Γ Γ₂) : RItems E R M ⟨l, false⟩ Γ Γ₂

end

/-- The local types of a list of locals. -/
abbrev tysOf (L : List (String × STy)) : RCtx := L.map Prod.snd

/-- An optional condition, resolved. -/
def OptCond.toR {Γ : Ctx} {c : Syn (.opt .expr)} : OptCond Γ c → ROptBool Γ.env Γ.tys
  | .none => .none
  | .some d => .some d.toR

/-- An optional step, resolved. -/
def OptExpr.toR {Γ : Ctx} {c : Syn (.opt .expr)} : OptExpr Γ c → ROptExpr Γ.env Γ.tys
  | .none => .none
  | .some d => .some d.toR

mutual

/-- **Elaboration of statements.** -/
def StmtD.toR {C : Ctx} {k : SCtx} {L L' : List (String × STy)} {s : Syn (.stmt k)} :
    StmtD C L s L' → RStmt C.env C.rets C.inModifier k (tysOf L) (tysOf L')
  | .expr d => .expr d.toR
  | .placeholder h => .placeholder h
  | .declVar (τ := τ) _ _ => .declVar τ
  | .declInit _ _ d h => .declInit d.toR h
  | .block b => .block b.toR
  | .ifThen dc _ ds => .ifThen dc.toR ds.toR
  | .ifElse dc _ _ ds dt => .ifElse dc.toR ds.toR dt.toR
  | .whileLoop dc _ ds => .whileLoop dc.toR ds.toR
  | .doWhile _ ds dc => .doWhile ds.toR dc.toR
  | .forLoop dc dp _ ds => .forLoop .skip dc.toR dp.toR ds.toR
  | .forInit di dc dp _ ds => .forLoop di.toR dc.toR dp.toR ds.toR
  | .brk => .brk
  | .cont => .cont
  | .ret h => .ret h
  | .retVal hR d h => .retVal hR d.toR h
  | .retTuple d ds h => .retTuple (RArgs.convert C.rets (.cons d.toR (TypedArgs.ofSlots ds)) h)
  | .emit (d := d) da hf =>
    let p := paramsOf C.env C.isBase _ d (mem_of_filter_eq hf)
    .emit d p.2.1 (RArgs.convert p.1 da.toR p.2.2)
  | .revertError (d := d) da hf =>
    let p := paramsOf C.env C.isBase _ d (mem_of_filter_eq hf)
    .revertError d p.2.1 (RArgs.convert p.1 da.toR p.2.2)
  | .rethrow (i := i) _ _ h _ => .rethrow (Idx.ofGet? _ i h)

/-- **Elaboration of blocks.** -/
def ItemsD.toR {C : Ctx} {k : SCtx} {L L' : List (String × STy)} {b : Syn (.list (.item k))} :
    ItemsD C L b L' → RItems C.env C.rets C.inModifier k (tysOf L) (tysOf L')
  | .nil => .nil
  | .stmt ds rest => .stmt ds.toR rest.toR
  | .unchecked db rest => .unchecked db.toR rest.toR

end

/-- **The resolved form has the derivation's type**: a well-typed
expression elaborates at its type, with no free choice of type left. -/
theorem HasType.resolved {Γ : Ctx} {e : Syn .expr} {τ : STy} (h : HasType Γ e τ) :
    Nonempty (RExpr Γ.env Γ.tys τ) :=
  h.elim fun d => ⟨d.toR⟩

/-- Every well-typed block elaborates in its body's frame and context. -/
theorem ItemsOK.resolved {C : Ctx} {k : SCtx} {L L' : List (String × STy)} {b : Syn (.list (.item k))}
    (h : ItemsOK C L b L') : Nonempty (RItems C.env C.rets C.inModifier k (tysOf L) (tysOf L')) :=
  h.elim fun d => ⟨d.toR⟩

end Solidity.Source
