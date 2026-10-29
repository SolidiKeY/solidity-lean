import Solidity.Source.Typing

/-!
# The resolved layer (S01)

S01's output, intrinsically typed: expressions and statements over a
context of local *types* (`RCtx := List STy`, names kept beside it, as
Gate G0 condition 3 asks), with

- locals by position (`Idx Γ τ`), state variables and functions by
  declaration (`DeclName`), the unique overload chosen;
- every implicit conversion an explicit node (`RExpr.conv`, carrying its
  proof), every explicit conversion one too (`RExpr.convExplicit`);
- operators by name (`BinOp`), constants by their exact value.

`Typed.toR`, `StmtD.toR` and `ItemsD.toR` read a typing derivation
(`Solidity/Source/Typing.lean`) as such a term: every well-typed expression,
statement and block has a resolved form (`HasType.resolved`,
`StmtOK.resolved`), whose type is the derivation's.  Nothing of S00's string
names remains in a resolved term except declaration names, which are
identities.  S02 defines its semantics over these terms.
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

/-- **Resolved expressions**, intrinsically typed. -/
inductive RExpr (B : DeclName → DeclName → Bool) (Γ : RCtx) : STy → Type where
  | const (q : Q) : RExpr B Γ (.rational q)
  | bytesLit {len : Nat} {h : 1 ≤ len ∧ len ≤ 32} (n : NumLit) : RExpr B Γ (.fixedBytes len h)
  | addressLit (ds : List (Fin 16)) : RExpr B Γ (.address false)
  | bool (b : Bool) : RExpr B Γ .bool
  | str (bs : List UInt8) : RExpr B Γ (.stringLit bs)
  | local {τ : STy} (i : Idx Γ τ) : RExpr B Γ τ
  | state {τ : STy} (d : DeclName) : RExpr B Γ τ
  | this (c : String) : RExpr B Γ (.contract ⟨none, c⟩)
  | tuple {τs : List STy} (es : RArgs B Γ τs) : RExpr B Γ (.tuple τs)
  /-- An implicit conversion (or the identity where operands already meet). -/
  | conv {σ τ : STy} (e : RExpr B Γ σ) (h : Conv B σ τ) : RExpr B Γ τ
  | convExplicit {σ τ : STy} (e : RExpr B Γ σ) (h : σ.explicit B τ = true) : RExpr B Γ τ
  | unary {τ : STy} (op : PrefixOp) (e : RExpr B Γ τ) : RExpr B Γ τ
  | incDec {τ : STy} (inc pre : Bool) (l : RLVal B Γ τ) : RExpr B Γ τ
  | delete {τ : STy} (l : RLVal B Γ τ) : RExpr B Γ (.tuple [])
  /-- A binary operation on operands converted to their common type `τ`. -/
  | binary {τ ρ : STy} (op : BinOp) (a b : RExpr B Γ τ) : RExpr B Γ ρ
  /-- A comparison of two constants. -/
  | compareConst (op : BinOp) (qa qb : Q) : RExpr B Γ .bool
  /-- A shift or power: the operand at `τ`, the amount at its own type. -/
  | shiftLike {τ σ : STy} (op : BinOp) (a : RExpr B Γ τ) (b : RExpr B Γ σ) : RExpr B Γ τ
  | cond {τ : STy} (c : RExpr B Γ .bool) (a b : RExpr B Γ τ) : RExpr B Γ τ
  | assign {τ : STy} (l : RLVal B Γ τ) (e : RExpr B Γ τ) : RExpr B Γ τ
  | compound {τ σ : STy} (op : AssignOp) (l : RLVal B Γ τ) (e : RExpr B Γ σ) : RExpr B Γ τ
  | indexArray {l : DataLoc} {τ σ : STy} {n : Option Nat} (a : RExpr B Γ (.array l τ n))
      (i : RExpr B Γ σ) : RExpr B Γ τ
  | indexMapping {τk τv : STy} (a : RExpr B Γ (.mapping τk τv)) (k : RExpr B Γ τk) : RExpr B Γ τv
  | indexBytes {τ σ : STy} (a : RExpr B Γ τ) (i : RExpr B Γ σ) : RExpr B Γ (.fixedBytes 1 (by decide))
  | length {τ : STy} {ρ : STy} (a : RExpr B Γ τ) : RExpr B Γ ρ
  | payable {σ : STy} (e : RExpr B Γ σ) : RExpr B Γ (.address true)
  /-- A call of an internal function, its arguments converted. -/
  | call {ps : List STy} {ρ : STy} (f : DeclName) (args : RConvArgs B Γ ps) : RExpr B Γ ρ
  | magic {τ : STy} (b : Builtin) (m : String) : RExpr B Γ τ
  | balance {p : Bool} (a : RExpr B Γ (.address p)) : RExpr B Γ (.int IntTy.u256)
  | builtin {σs : List STy} {τ : STy} (b : Builtin) (args : RArgs B Γ σs) : RExpr B Γ τ

/-- Resolved argument lists. -/
inductive RArgs (B : DeclName → DeclName → Bool) (Γ : RCtx) : List STy → Type where
  | nil : RArgs B Γ []
  | cons {τ : STy} {τs : List STy} : RExpr B Γ τ → RArgs B Γ τs → RArgs B Γ (τ :: τs)

/-- Arguments converted to parameter types. -/
inductive RConvArgs (B : DeclName → DeclName → Bool) (Γ : RCtx) : List STy → Type where
  | nil : RConvArgs B Γ []
  | cons {σ τ : STy} {τs : List STy} : RExpr B Γ σ → σ.implicit B τ = true → RConvArgs B Γ τs →
      RConvArgs B Γ (τ :: τs)

/-- Resolved lvalues. -/
inductive RLVal (B : DeclName → DeclName → Bool) (Γ : RCtx) : STy → Type where
  | local {τ : STy} (i : Idx Γ τ) : RLVal B Γ τ
  | state {τ : STy} (d : DeclName) : RLVal B Γ τ
  | indexArray {l : DataLoc} {τ σ : STy} {n : Option Nat} (a : RExpr B Γ (.array l τ n))
      (i : RExpr B Γ σ) : RLVal B Γ τ
  | indexMapping {τk τv σ : STy} (a : RExpr B Γ (.mapping τk τv)) (k : RExpr B Γ σ) : RLVal B Γ τv

end

/-- Converted arguments from typed arguments that fit. -/
def RArgs.convert {B : DeclName → DeclName → Bool} {Γ : RCtx} :
    {σs : List STy} → (ps : List STy) → RArgs B Γ σs → argsFit B σs ps = true → RConvArgs B Γ ps
  | [], [], .nil, _ => .nil
  | _ :: _, p :: ps, .cons e es, h => by
    simp only [argsFit, List.length_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
      beq_iff_eq, Nat.add_right_cancel_iff] at h
    exact .cons e h.2.1 (es.convert ps (by
      simp only [argsFit, Bool.and_eq_true, beq_iff_eq]; exact ⟨h.1, h.2.2⟩))
  | [], _ :: _, _, h => by simp only [argsFit, List.length_nil, List.length_cons] at h; cases h
  | _ :: _, [], _, h => by simp only [argsFit, List.length_nil, List.length_cons] at h; cases h

/-- The declaration name of a declaration. -/
def Decl.ref (d : Decl) : DeclName := ⟨d.scope, d.name⟩

mutual

/-- **Elaboration**: a typing derivation as a resolved expression. -/
def Typed.toR {Γ : Ctx} {e : Syn .expr} {τ : STy} : Typed Γ e τ → RExpr Γ.isBase Γ.tys τ
  | .const (q := q) _ _ => .const q
  | .litBytes (n := n) _ => .bytesLit n
  | .litAddress (ds := ds) _ => .addressLit ds
  | .bool b => .bool b
  | .str bs => .str bs
  | .hexStr bs => .str bs
  | .unicodeStr bs => .str bs
  | .loc (i := i) _ h => .local (Idx.ofGet? _ i h)
  | .state (d := d) _ _ => .state d.ref
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
  | .arith (e := e) _ da db h _ => .binary e.binOpName (.conv da.toR (common?_left h)) (.conv db.toR (common?_right h))
  | .bit (e := e) _ da db h _ => .binary e.binOpName (.conv da.toR (common?_left h)) (.conv db.toR (common?_right h))
  | .shift (e := e) _ da db _ _ => .shiftLike e.binOpName (.conv da.toR mobile_conv) db.toR
  | .exp _ da db _ _ => .shiftLike .exp (.conv da.toR mobile_conv) db.toR
  | .order (e := e) _ da db h _ => .binary e.binOpName (.conv da.toR (common?_left h)) (.conv db.toR (common?_right h))
  | .eq (e := e) _ da db h _ => .binary e.binOpName (.conv da.toR (common?_left h)) (.conv db.toR (common?_right h))
  | .compareConst (e := e) (qa := qa) (qb := qb) _ _ _ _ => .compareConst e.binOpName qa qb
  | .logic (e := e) _ da db => .binary e.binOpName da.toR db.toR
  | .cond dc da db h => .cond dc.toR (.conv (.conv da.toR mobile_conv) (common?_left h))
      (.conv (.conv db.toR mobile_conv) (common?_right h))
  | .assign l db h => .assign l.toR (.conv db.toR (.inl h))
  | .compound (op := op) _ l db _ => .compound op l.toR db.toR
  | .indexArray da di _ _ => .indexArray da.toR di.toR
  | .indexMapping da di h => .indexMapping da.toR (.conv di.toR (.inl h))
  | .indexBytes da _ di _ _ => .indexBytes da.toR di.toR
  | .length da _ => .length da.toR
  | .lengthBytesN da => .length da.toR
  | .convElem dx hτ h => .convExplicit dx.toR (hτ ▸ h)
  | .convUser _ dx h => .convExplicit dx.toR h
  | .payable dx _ => .payable dx.toR
  | .callInternal (d := d) (ps := ps) da hf hs => .call d.ref (RArgs.convert ps da.toR (by
      have hm : d ∈ _ := hf ▸ List.mem_singleton_self d
      have hp := (List.mem_filter.1 hm).2
      rw [hs] at hp
      exact hp))
  | .magic (b := b) (m := m) _ _ _ _ => .magic b m
  | .balance da => .balance da.toR
  | .builtinCall (b := b) _ _ da _ => .builtin b da.toR

/-- Elaboration of argument lists. -/
def TypedArgs.toR {Γ : Ctx} {es : Syn (.list .expr)} {τs : List STy} :
    TypedArgs Γ es τs → RArgs Γ.isBase Γ.tys τs
  | .nil => .nil
  | .cons d ds => .cons d.toR ds.toR

/-- Elaboration of tuple slots, at their mobile types. -/
def TypedSlots.toR {Γ : Ctx} {es : Syn (.list (.opt .expr))} {τs : List STy} :
    TypedSlots Γ es τs → RArgs Γ.isBase Γ.tys (τs.map STy.mobile)
  | .nil => .nil
  | .cons d ds => .cons (.conv d.toR mobile_conv) ds.toR

/-- Elaboration of tuple slots as arguments (at their own types). -/
def TypedArgs.ofSlots {Γ : Ctx} {es : Syn (.list (.opt .expr))} {τs : List STy} :
    TypedSlots Γ es τs → RArgs Γ.isBase Γ.tys τs
  | .nil => .nil
  | .cons d ds => .cons d.toR (TypedArgs.ofSlots ds)

/-- Elaboration of lvalues. -/
def LVal.toR {Γ : Ctx} {e : Syn .expr} {τ : STy} : LVal Γ e τ → RLVal Γ.isBase Γ.tys τ
  | .loc (i := i) _ h => .local (Idx.ofGet? _ i h)
  | .state (d := d) _ _ _ => .state d.ref
  | .paren l => l.toR
  | .indexArray da _ di _ _ => .indexArray da.toR di.toR
  | .indexMapping da di _ => .indexMapping da.toR di.toR

end

/-! ## Statements -/

/-- An optional loop condition. -/
inductive ROptBool (B : DeclName → DeclName → Bool) (Γ : RCtx) : Type where
  | none
  | some (c : RExpr B Γ .bool)

/-- An optional loop step. -/
inductive ROptExpr (B : DeclName → DeclName → Bool) (Γ : RCtx) : Type where
  | none
  | some {τ : STy} (e : RExpr B Γ τ)

mutual

/-- **Resolved statements**: from local types `Γ` to `Γ'`. -/
inductive RStmt (B : DeclName → DeclName → Bool) : RCtx → RCtx → Type where
  | expr {Γ : RCtx} {τ : STy} (e : RExpr B Γ τ) : RStmt B Γ Γ
  | placeholder {Γ : RCtx} : RStmt B Γ Γ
  /-- A declaration with the type's default value. -/
  | declVar {Γ : RCtx} (τ : STy) : RStmt B Γ (τ :: Γ)
  | declInit {Γ : RCtx} {σ τ : STy} (e : RExpr B Γ σ) (h : σ.implicit B τ = true) : RStmt B Γ (τ :: Γ)
  | block {Γ Γ' : RCtx} (b : RItems B Γ Γ') : RStmt B Γ Γ
  | ifThen {Γ Γ₁ : RCtx} (c : RExpr B Γ .bool) (s : RStmt B Γ Γ₁) : RStmt B Γ Γ
  | ifElse {Γ Γ₁ Γ₂ : RCtx} (c : RExpr B Γ .bool) (s : RStmt B Γ Γ₁) (t : RStmt B Γ Γ₂) : RStmt B Γ Γ
  | whileLoop {Γ Γ₁ : RCtx} (c : RExpr B Γ .bool) (s : RStmt B Γ Γ₁) : RStmt B Γ Γ
  | doWhile {Γ Γ₁ : RCtx} (s : RStmt B Γ Γ₁) (c : RExpr B Γ .bool) : RStmt B Γ Γ
  | forLoop {Γ Γ₁ Γ₂ : RCtx} (init : RStmt B Γ Γ₁) (c : ROptBool B Γ₁) (post : ROptExpr B Γ₁)
      (s : RStmt B Γ₁ Γ₂) : RStmt B Γ Γ
  | skip {Γ : RCtx} : RStmt B Γ Γ
  | brk {Γ : RCtx} : RStmt B Γ Γ
  | cont {Γ : RCtx} : RStmt B Γ Γ
  | ret {Γ : RCtx} : RStmt B Γ Γ
  | retVal {Γ : RCtx} {σ τ : STy} (e : RExpr B Γ σ) (h : σ.implicit B τ = true) : RStmt B Γ Γ
  | retTuple {Γ : RCtx} {σs : List STy} (es : RArgs B Γ σs) : RStmt B Γ Γ
  | emit {Γ : RCtx} {σs : List STy} (ev : DeclName) (args : RArgs B Γ σs) : RStmt B Γ Γ
  | revertError {Γ : RCtx} {σs : List STy} (er : DeclName) (args : RArgs B Γ σs) : RStmt B Γ Γ
  /-- The canonical rethrow of a `bytes memory` local. -/
  | rethrow {Γ : RCtx} (i : Idx Γ (.bytes .memory)) : RStmt B Γ Γ

/-- Resolved blocks. -/
inductive RItems (B : DeclName → DeclName → Bool) : RCtx → RCtx → Type where
  | nil {Γ : RCtx} : RItems B Γ Γ
  | stmt {Γ Γ₁ Γ₂ : RCtx} (s : RStmt B Γ Γ₁) (rest : RItems B Γ₁ Γ₂) : RItems B Γ Γ₂
  | unchecked {Γ Γ₁ Γ₂ : RCtx} (b : RItems B Γ Γ₁) (rest : RItems B Γ Γ₂) : RItems B Γ Γ₂

end

/-- The local types of a list of locals. -/
abbrev tysOf (L : List (String × STy)) : RCtx := L.map Prod.snd

/-- An optional condition, resolved. -/
def OptCond.toR {Γ : Ctx} {c : Syn (.opt .expr)} : OptCond Γ c → ROptBool Γ.isBase Γ.tys
  | .none => .none
  | .some d => .some d.toR

/-- An optional step, resolved. -/
def OptExpr.toR {Γ : Ctx} {c : Syn (.opt .expr)} : OptExpr Γ c → ROptExpr Γ.isBase Γ.tys
  | .none => .none
  | .some d => .some d.toR

mutual

/-- **Elaboration of statements.** -/
def StmtD.toR {C : Ctx} {k : SCtx} {L L' : List (String × STy)} {s : Syn (.stmt k)} :
    StmtD C L s L' → RStmt C.isBase (tysOf L) (tysOf L')
  | .expr d => .expr d.toR
  | .placeholder _ => .placeholder
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
  | .ret => .ret
  | .retVal _ d h => .retVal d.toR h
  | .retTuple d ds _ => .retTuple (.cons d.toR (TypedArgs.ofSlots ds))
  | .emit (d := d) da _ => .emit d.ref da.toR
  | .revertError (d := d) da _ => .revertError d.ref da.toR
  | .rethrow (i := i) _ _ h _ => .rethrow (Idx.ofGet? _ i h)

/-- **Elaboration of blocks.** -/
def ItemsD.toR {C : Ctx} {k : SCtx} {L L' : List (String × STy)} {b : Syn (.list (.item k))} :
    ItemsD C L b L' → RItems C.isBase (tysOf L) (tysOf L')
  | .nil => .nil
  | .stmt ds rest => .stmt ds.toR rest.toR
  | .unchecked db rest => .unchecked db.toR rest.toR

end

/-- **Every well-typed expression has a resolved form** of its type. -/
theorem HasType.resolved {Γ : Ctx} {e : Syn .expr} {τ : STy} (h : HasType Γ e τ) :
    Nonempty (RExpr Γ.isBase Γ.tys τ) :=
  h.elim fun d => ⟨d.toR⟩

/-- **Every well-typed statement has a resolved form.** -/
theorem StmtOK.resolved {C : Ctx} {k : SCtx} {L L' : List (String × STy)} {s : Syn (.stmt k)}
    (h : StmtOK C L s L') : Nonempty (RStmt C.isBase (tysOf L) (tysOf L')) :=
  h.elim fun d => ⟨d.toR⟩

end Solidity.Source
