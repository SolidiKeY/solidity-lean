import Solidity.Source.Typing

/-!
# Type inference for S01's expression typing (G13)

`infer Γ s` computes, for an expression `s`, **every** S01 derivation shape
of it: a list of typing derivations `Typed Γ s τ` and lvalue derivations
`LVal Γ s τ`, one per type (and rule) that applies.  The output is the
derivations themselves, so the checker is sound by construction: whatever
it returns is an S01 derivation, ready for `Typed.toR`.  Completeness
(`Solidity/Frontend/Static/InferComplete.lean`) proves that every type S01
derives is among them.

**Why a list.**  S01's `Typed` is a relation: a hexadecimal zero is a
constant and every `bytesN`, and several rules can type one expression.
The set of types of an expression is finite, and the checker returns all of
them; deciding `HasType Γ e τ` is then membership.

**One function over every category.**  `Syn` is an indexed family, and a
function over a fixed index (`Syn .expr` alone) is not structural.  So
`infer` walks every category (as S00's `Syn.collect` does), with one result
family `Res Γ c s` for all of them: typing and lvalue derivations of
expressions, of present tuple slots, of argument lists and slot lists, and
of positional call arguments.  Categories it does not type give `[]`.

The rules are grouped by the syntax they apply to; every one of S01's
`Typed`/`LVal`/`TypedArgs`/`TypedSlots` constructors is generated at the
syntax it names.  This is a static check, evaluated once per body, never
kernel-evaluated hot code (Gate G0).
-/

namespace Solidity.Frontend.Static

open Solidity.Source

section
variable (Γ : Ctx)

/-- What `infer` returns for a tree of category `c`. -/
inductive Res : (c : Cat) → Syn c → Type where
  | expr {e : Syn .expr} {τ : STy} : Typed Γ e τ → Res .expr e
  | lval {e : Syn .expr} {τ : STy} : LVal Γ e τ → Res .expr e
  | args {es : Syn (.list .expr)} {τs : List STy} : TypedArgs Γ es τs → Res (.list .expr) es
  | slots {s : Syn (.list (.opt .expr))} {τs : List STy} : TypedSlots Γ s τs →
      Res (.list (.opt .expr)) s
  /-- The empty list of any category: no arguments, no slots. -/
  | nilList {c : Cat} : Res (.list c) .nil
  | slot {e : Syn .expr} {τ : STy} : Typed Γ e τ → Res (.opt .expr) (.some e)
  | slotL {e : Syn .expr} {τ : STy} : LVal Γ e τ → Res (.opt .expr) (.some e)
  | pos {es : Syn (.list .expr)} {τs : List STy} : TypedArgs Γ es τs → Res .callArgs (.positional es)

/-- The typing derivations among an expression's results. -/
def tysOf {e : Syn .expr} : List (Res Γ .expr e) → List (Σ τ, Typed Γ e τ) :=
  List.filterMap fun r =>
    match r with
    | .expr d => Option.some ⟨_, d⟩
    | .lval _ => Option.none

/-- The lvalue derivations among an expression's results. -/
def lvsOf {e : Syn .expr} : List (Res Γ .expr e) → List (Σ τ, LVal Γ e τ) :=
  List.filterMap fun r =>
    match r with
    | .expr _ => Option.none
    | .lval d => Option.some ⟨_, d⟩

/-- The argument-list derivations. -/
def argsOf {es : Syn (.list .expr)} : List (Res Γ (.list .expr) es) → List (Σ τs, TypedArgs Γ es τs) :=
  List.filterMap fun r =>
    match r with
    | .args d => Option.some ⟨_, d⟩
    | .nilList => Option.some ⟨[], .nil⟩

/-- The slot-list derivations. -/
def slotsOf {s : Syn (.list (.opt .expr))} :
    List (Res Γ (.list (.opt .expr)) s) → List (Σ τs, TypedSlots Γ s τs) :=
  List.filterMap fun r =>
    match r with
    | .slots d => Option.some ⟨_, d⟩
    | .nilList => Option.some ⟨[], .nil⟩

/-- One element prepended to a list's derivation. -/
def consOne : {c : Cat} → {x : Syn c} → {xs : Syn (.list c)} → Res Γ c x → Res Γ (.list c) xs →
    Option (Res Γ (.list c) (.cons x xs))
  | _, _, _, .expr d, .args ds => Option.some (.args (.cons d ds))
  | _, _, _, .expr d, .nilList => Option.some (.args (.cons d .nil))
  | _, _, _, .slot d, .slots ds => Option.some (.slots (.cons d ds))
  | _, _, _, .slot d, .nilList => Option.some (.slots (.cons d .nil))
  | _, _, _, _, _ => Option.none

/-- A present slot. -/
def someOne : {c : Cat} → {x : Syn c} → Res Γ c x → Option (Res Γ (.opt c) (.some x))
  | _, _, .expr d => Option.some (.slot d)
  | _, _, .lval d => Option.some (.slotL d)
  | _, _, _ => Option.none

/-! ## Rules by syntax -/

/-- S01's premise shapes, as functions (each unfolds to S01's `match`). -/
def isMappingTy (τ : STy) : Bool := τ matches .mapping _ _
def bytesLike (τ : STy) : Bool :=
  match τ with
  | .bytes _ => true
  | .fixedBytes _ _ => true
  | _ => false
def fixedLen (τ : STy) : Option Nat :=
  match τ with
  | .fixedBytes n _ => Option.some n
  | _ => Option.none
def payableArg (σ : STy) : Bool :=
  match σ with
  | .address _ => true
  | .contract _ => true
  | _ => false
def convLoc (σ : STy) : DataLoc :=
  match σ with
  | .bytes l => l
  | .string l => l
  | _ => .memory

/-- `const`: a constant expression at its exact value. -/
def constRes (e : Syn .expr) : List (Res Γ .expr e) :=
  match hq : e.const, ha : e.isAddressLit with
  | Option.some _, false => [.expr (.const hq ha)]
  | _, _ => []

/-- The lengths `1 … 32`. -/
def lens : List Nat := (List.range 32).map (· + 1)

/-- Literals. -/
def litRes : (l : Lit) → List (Res Γ .expr (.lit l))
  | .bool b => [.expr (.bool b)]
  | .str bs => [.expr (.str bs)]
  | .hexStr bs => [.expr (.hexStr bs)]
  | .unicodeStr bs => [.expr (.unicodeStr bs)]
  | .num n =>
    (lens.filterMap fun len =>
      if h : 1 ≤ len ∧ len ≤ 32 then
        if hf : n.fitsBytes len = true then Option.some (.expr (.litBytes (h := h) hf)) else Option.none
      else Option.none) ++
    (match n with
     | .hex ds true => if h : ds.length = 40 then [.expr (.litAddress h)] else []
     | _ => [])

/-- `this`. -/
def thisRes : List (Res Γ .expr (.ident "this")) :=
  match hr : Γ.resolve "this", hs : Γ.scope with
  | Option.some (.builtin .this), Option.some _ => [.expr (.this hr hs)]
  | _, _ => []

/-- `this`, when the name is `this`. -/
def thisFor : (x : String) → List (Res Γ .expr (.ident x))
  | "this" => thisRes Γ
  | _ => []

/-- Identifiers: locals, state variables and constants, `this`. -/
def identRes (x : String) : List (Res Γ .expr (.ident x)) :=
  (match hr : Γ.resolve x with
   | Option.some (.loc i) =>
     match ht : Γ.tys[i]? with
     | Option.some _ => [.expr (.loc hr ht), .lval (.loc hr ht)]
     | Option.none => []
   | Option.some (.decls [d]) =>
     match hv : d.varTy Γ.env with
     | Option.some _ =>
       .expr (.state hr hv) :: (if hm : d.mutable = true then [.lval (.state hr hv hm)] else [])
     | Option.none => []
   | _ => []) ++
  thisFor Γ x

/-- `( … )`: a parenthesized expression or a tuple of present slots. -/
def tupleOne {o : Syn (.opt .expr)} {s : Syn (.list (.opt .expr))} :
    Res Γ (.opt .expr) o → Res Γ (.list (.opt .expr)) s → List (Res Γ .expr (.tuple o s))
  | .slot d, .nilList => [.expr (.paren d)]
  | .slotL d, .nilList => [.lval (.paren d)]
  | .slot d, .slots (τs := _ :: _) ds => [.expr (.tuple d ds (List.cons_ne_nil _ _))]
  | _, _ => []

/-- Prefix operators on one result of the operand. -/
def prefixOne (op : PrefixOp) {x : Syn .expr} : Res Γ .expr x → List (Res Γ .expr (.unaryPrefix op x))
  | .expr (τ := τ) d =>
    match op with
    | .neg =>
      (match τ, d with
       | .int t, d => if h : t.signed = true then [.expr (.neg d h)] else []
       | .fixed _, d => [.expr (.negFixed d)]
       | _, _ => [])
    | .not =>
      (match τ, d with
       | .bool, d => [.expr (.not d)]
       | _, _ => [])
    | .bitNot => if h : τ.isBits = true then [.expr (.bitNot d h)] else []
    | _ => []
  | .lval (τ := τ) d =>
    match op with
    | .inc => if h : τ.isNumeric = true then [.expr (.incDec (.inl rfl) d h)] else []
    | .dec => if h : τ.isNumeric = true then [.expr (.incDec (.inr rfl) d h)] else []
    | .delete => if h : isMappingTy τ = false then [.expr (.delete d h)] else []
    | _ => []

/-- Suffix `++`/`--`. -/
def suffixOne (op : SuffixOp) {x : Syn .expr} : Res Γ .expr x → List (Res Γ .expr (.unarySuffix op x))
  | .lval (τ := τ) d => if h : τ.isNumeric = true then [.expr (.incDecSuffix d h)] else []
  | .expr _ => []

/-- A binary rule on one pair of operand derivations. -/
def binPair (e a b : Syn .expr) : (k : BinKind) → e.binOp? = Option.some (k, a, b) →
    (τa : STy) → Typed Γ a τa → (τb : STy) → Typed Γ b τb → List (Res Γ .expr e)
  | .arith, hk, τa, da, τb, db =>
    match hc : STy.common? Γ.isBase τa τb with
    | Option.some τ =>
      if hn : τ.isNumeric = true then
        if hz : (e.isDivMod && τb.isZeroConst) = false then [.expr (.arith hk da db hc hn hz)] else []
      else []
    | Option.none => []
  | .bit, hk, τa, da, τb, db =>
    match hc : STy.common? Γ.isBase τa τb with
    | Option.some τ => if hn : τ.isBits = true then [.expr (.bit hk da db hc hn)] else []
    | Option.none => []
  | .shift, hk, τa, da, τb, db =>
    if h1 : τa.mobile.isBits = true then
      if h2 : τb.isAmount = true then
        if h3 : (a.const.isSome && b.const.isSome) = false then [.expr (.shift hk da db h1 h2 h3)]
        else []
      else []
    else []
  | .exp, hk, τa, da, τb, db =>
    if h1 : τa.mobile.isInt = true then
      if h2 : τb.isAmount = true then
        if h3 : (a.const.isSome && b.const.isSome) = false then [.expr (.exp hk da db h1 h2 h3)]
        else []
      else []
    else []
  | .order, hk, τa, da, τb, db =>
    match hc : STy.common? Γ.isBase τa τb with
    | Option.some τ => if hn : τ.isOrdered = true then [.expr (.order hk da db hc hn)] else []
    | Option.none => []
  | .eq, hk, τa, da, τb, db =>
    match hc : STy.common? Γ.isBase τa τb with
    | Option.some τ => if hn : τ.hasEq = true then [.expr (.eq hk da db hc hn)] else []
    | Option.none => []
  | .logic, hk, τa, da, τb, db =>
    match τa, da, τb, db with
    | .bool, da, .bool, db => [.expr (.logic hk da db)]
    | _, _, _, _ => []

/-- A comparison of two constants. -/
def compareConstRes (e a b : Syn .expr) : (k : BinKind) → e.binOp? = Option.some (k, a, b) →
    List (Res Γ .expr e)
  | .order, hk =>
    match ha : a.const, hb : b.const with
    | Option.some _, Option.some _ => [.expr (.compareConst hk (.inl rfl) ha hb)]
    | _, _ => []
  | .eq, hk =>
    match ha : a.const, hb : b.const with
    | Option.some _, Option.some _ => [.expr (.compareConst hk (.inr rfl) ha hb)]
    | _, _ => []
  | _, _ => []

/-- All binary rules, over all operand derivations. -/
def binRes (e a b : Syn .expr) (k : BinKind) (hk : e.binOp? = Option.some (k, a, b))
    (ra : List (Res Γ .expr a)) (rb : List (Res Γ .expr b)) : List (Res Γ .expr e) :=
  ((tysOf Γ ra).flatMap fun pa => (tysOf Γ rb).flatMap fun pb => binPair Γ e a b k hk pa.1 pa.2 pb.1 pb.2) ++
    compareConstRes Γ e a b k hk

/-- `c ? a : b`. -/
def condRes {c a b : Syn .expr} (rc : List (Res Γ .expr c)) (ra : List (Res Γ .expr a))
    (rb : List (Res Γ .expr b)) : List (Res Γ .expr (.cond c a b)) :=
  (tysOf Γ rc).flatMap fun pc =>
    match pc with
    | ⟨.bool, dc⟩ =>
      (tysOf Γ ra).flatMap fun pa => (tysOf Γ rb).flatMap fun pb =>
        match hc : STy.common? Γ.isBase pa.1.mobile pb.1.mobile with
        | Option.some _ => [.expr (.cond dc pa.2 pb.2 hc)]
        | Option.none => []
    | _ => []

/-- `a = b`, `a ∘= b`. -/
def assignRes (op : AssignOp) {a b : Syn .expr} (ra : List (Res Γ .expr a)) (rb : List (Res Γ .expr b)) :
    List (Res Γ .expr (.assign op a b)) :=
  (lvsOf Γ ra).flatMap fun pa => (tysOf Γ rb).flatMap fun pb =>
    (match op with
     | .assign =>
       if h1 : pb.1.implicit Γ.isBase pa.1 = true then
         if h2 : isMappingTy pa.1 = false then [.expr (.assign pa.2 pb.2 h1 h2)] else []
       else []
     | _ => []) ++
    (if h : op.fits Γ.isBase pb.1 pa.1 = true then [.expr (.compound pa.2 pb.2 h)] else [])

/-- `a[i]` for one derivation of `a` and of `i`. -/
def indexPair {a i : Syn .expr} : (τ : STy) → Typed Γ a τ → (σ : STy) → Typed Γ i σ →
    List (Res Γ .expr (.index a (.some i)))
  | τ, da, σ, di =>
    (match τ, da with
     | .array l τ' n, da =>
       if h1 : σ.isIndex = true then
         if h2 : inBounds σ n = true then
           .expr (.indexArray da di h1 h2) ::
             (if hl : l ≠ .calldata then [.lval (.indexArray da hl di h1 h2)] else [])
         else []
       else []
     | .mapping τk τv, da =>
       if h : σ.implicit Γ.isBase τk = true then [.expr (.indexMapping da di h), .lval (.indexMapping da di h)]
       else []
     | _, _ => []) ++
    (if hm : bytesLike τ = true then
      if h1 : σ.isIndex = true then
        if h2 : inBounds σ (fixedLen τ) = true then
          [.expr (.indexBytes da hm di h1 h2)]
        else []
      else []
     else []) ++
    (match τ, da with
     | .bytes l, da =>
       if hl : l ≠ .calldata then
         if h1 : σ.isIndex = true then [.lval (.indexBytes da hl di h1)] else []
       else []
     | _, _ => [])

/-- `a[i]`: `i` present. -/
def indexRes {a : Syn .expr} {o : Syn (.opt .expr)} (ra : List (Res Γ .expr a)) :
    Res Γ (.opt .expr) o → List (Res Γ .expr (.index a o))
  | .slot (τ := σ) di => (tysOf Γ ra).flatMap fun pa => indexPair Γ pa.1 pa.2 σ di
  | _ => []

/-- `a.m`: `length`, `balance`. -/
def memberRes {a : Syn .expr} (m : String) (ra : List (Res Γ .expr a)) : List (Res Γ .expr (.member a m)) :=
  match m with
  | "length" =>
    (tysOf Γ ra).flatMap fun pa =>
      match hρ : pa.1.lengthTy with
      | Option.some _ => [.expr (.length pa.2 hρ)]
      | Option.none => []
  | "balance" =>
    (tysOf Γ ra).flatMap fun pa =>
      match pa with
      | ⟨.address _, da⟩ => [.expr (.balance da)]
      | _ => []
  | _ => []

/-- `g.m` for a magic `g`. -/
def magicRes (g m : String) : List (Res Γ .expr (.member (.ident g) m)) :=
  match hr : Γ.resolve g with
  | Option.some (.builtin b) =>
    match hs : b.memberStatus m with
    | Option.some (.admitted _) =>
      match ht : b.memberTy m with
      | Option.some _ =>
        if hv : (b == .msg && m == "value" && !Γ.msgValue) = false then [.expr (.magic hr hs ht hv)]
        else []
      | Option.none => []
    | _ => []
  | _ => []

/-- Magic members, when the base is a name. -/
def magicFor : (a : Syn .expr) → (m : String) → List (Res Γ .expr (.member a m))
  | .ident g, m => magicRes Γ g m
  | _, _ => []

/-- `f(args)` with a named callee: conversions to contracts and enums,
internal calls, builtin calls. -/
def callIdentRes (f : String) {es : Syn (.list .expr)} (σs : List STy) (ds : TypedArgs Γ es σs) :
    List (Res Γ .expr (.call (.ident f) (.positional es))) :=
  (match es, σs, ds with
   | .cons _ .nil, [σ], .cons dx .nil =>
     match ht : Γ.convTarget f with
     | Option.some τ => if h : σ.explicit Γ.isBase τ = true then [.expr (.convUser ht dx h)] else []
     | Option.none => []
   | _, _, _ => []) ++
  (match hf : (Γ.functions f).filter (fun d' => match d'.fnSig Γ.env with
      | Option.some (ps', _) => argsFit Γ.isBase σs ps'
      | Option.none => false) with
   | [d] =>
     match hs : d.fnSig Γ.env with
     | Option.some _ => [.expr (.callInternal ds hf hs)]
     | Option.none => []
   | _ => []) ++
  (match hr : Γ.resolve f with
   | Option.some (.builtin b) =>
     match hst : b.status with
     | .admitted _ =>
       match hc : b.callTy Γ.isBase σs with
       | Option.some _ => [.expr (.builtinCall hr hst ds hc)]
       | Option.none => []
     | _ => []
   | _ => [])

/-- `T(e)` for an elementary `T`. -/
def convElemRes (el : Elem) (h : el ≠ .addressPayable) {es : Syn (.list .expr)} (σs : List STy)
    (ds : TypedArgs Γ es σs) : List (Res Γ .expr (.call (.elemType el h) (.positional es))) :=
  match es, σs, ds with
  | .cons _ .nil, [σ], .cons dx .nil =>
    if hx : σ.explicit Γ.isBase (el.ty (convLoc σ)) = true
    then [.expr (.convElem dx rfl hx)] else []
  | _, _, _ => []

/-- `payable(e)`. -/
def payableRes {es : Syn (.list .expr)} (σs : List STy) (ds : TypedArgs Γ es σs) :
    List (Res Γ .expr (.payableConv (.positional es))) :=
  match es, σs, ds with
  | .cons _ .nil, [σ], .cons dx .nil =>
    if h : payableArg σ = true then
      [.expr (.payable dx h)] else []
  | _, _, _ => []

/-- Calls, by the callee's syntax. -/
def callRes : (f : Syn .expr) → {a : Syn .callArgs} → Res Γ .callArgs a → List (Res Γ .expr (.call f a))
  | .ident n, _, .pos ds => callIdentRes Γ n _ ds
  | .elemType el h, _, .pos ds => convElemRes Γ el h _ ds
  | _, _, _ => []

/-- `payable(…)`. -/
def payableConvRes {a : Syn .callArgs} : Res Γ .callArgs a → List (Res Γ .expr (.payableConv a))
  | .pos ds => payableRes Γ _ ds

/-! ## The checker -/

/-- **Type inference**: every derivation S01 gives the tree, by rule. -/
def infer : {c : Cat} → (s : Syn c) → List (Res Γ c s)
  | _, .nil => [.nilList]
  | _, .cons x xs => (infer x).flatMap fun r => (infer xs).filterMap fun r' => consOne Γ r r'
  | _, .some x => (infer x).filterMap (someOne Γ)
  | _, .positional es => (argsOf Γ (infer es)).map fun p => .pos p.2
  | _, .ident x => constRes Γ (.ident x) ++ identRes Γ x
  | _, .lit l => constRes Γ (.lit l) ++ litRes Γ l
  | _, .litUnit n u => constRes Γ (.litUnit n u)
  | _, .tuple o s => constRes Γ (.tuple o s) ++
      (infer o).flatMap fun r => (infer s).flatMap fun r' => tupleOne Γ r r'
  | _, .unaryPrefix op x => constRes Γ (.unaryPrefix op x) ++ (infer x).flatMap (prefixOne Γ op)
  | _, .unarySuffix op x => constRes Γ (.unarySuffix op x) ++ (infer x).flatMap (suffixOne Γ op)
  | _, .mulDivMod op a b => constRes Γ _ ++ binRes Γ (.mulDivMod op a b) a b .arith rfl (infer a) (infer b)
  | _, .addSub op a b => constRes Γ _ ++ binRes Γ (.addSub op a b) a b .arith rfl (infer a) (infer b)
  | _, .bitAnd a b => constRes Γ _ ++ binRes Γ (.bitAnd a b) a b .bit rfl (infer a) (infer b)
  | _, .bitOr a b => constRes Γ _ ++ binRes Γ (.bitOr a b) a b .bit rfl (infer a) (infer b)
  | _, .bitXor a b => constRes Γ _ ++ binRes Γ (.bitXor a b) a b .bit rfl (infer a) (infer b)
  | _, .shift op a b => constRes Γ _ ++ binRes Γ (.shift op a b) a b .shift rfl (infer a) (infer b)
  | _, .exp a b => constRes Γ _ ++ binRes Γ (.exp a b) a b .exp rfl (infer a) (infer b)
  | _, .order op a b => constRes Γ _ ++ binRes Γ (.order op a b) a b .order rfl (infer a) (infer b)
  | _, .equality op a b => constRes Γ _ ++ binRes Γ (.equality op a b) a b .eq rfl (infer a) (infer b)
  | _, .and a b => constRes Γ _ ++ binRes Γ (.and a b) a b .logic rfl (infer a) (infer b)
  | _, .or a b => constRes Γ _ ++ binRes Γ (.or a b) a b .logic rfl (infer a) (infer b)
  | _, .cond c a b => constRes Γ _ ++ condRes Γ (infer c) (infer a) (infer b)
  | _, .assign op a b => constRes Γ _ ++ assignRes Γ op (infer a) (infer b)
  | _, .index a o => constRes Γ _ ++ (infer o).flatMap (indexRes Γ (infer a))
  | _, .member a m => constRes Γ _ ++ memberRes Γ m (infer a) ++ magicFor Γ a m
  | _, .call f a => constRes Γ _ ++ (infer a).flatMap (callRes Γ f)
  | _, .payableConv a => constRes Γ _ ++ (infer a).flatMap (payableConvRes Γ)
  | _, .slice a o o' => constRes Γ (.slice a o o')
  | _, .callOptions f n ns => constRes Γ (.callOptions f n ns)
  | _, .metaType t => constRes Γ (.metaType t)
  | _, .new t => constRes Γ (.new t)
  | _, .inlineArray x xs => constRes Γ (.inlineArray x xs)
  | _, .elemType el h => constRes Γ (.elemType el h)
  | _, _ => []

end

/-- The types `infer` finds for an expression. -/
def inferTys (Γ : Ctx) (e : Syn .expr) : List STy := (tysOf Γ (infer Γ e)).map Sigma.fst

end Solidity.Frontend.Static

