import Solidity.Source.Typing

/-!
# Type inference: derivations computed (S02 item 1b)

`Typed.infer Γ e` returns a type and a derivation `Typed Γ e τ`, or `none`;
`StmtD.infer` and `ItemsD.infer` do the same for statements and blocks.
The result is a derivation, so inference is sound by construction; by
`Typed.unique` (`Solidity/Source/Unique.lean`) the derivation it finds has
the meaning every derivation has.  Inference follows the rules' premises in
order; its recursion is structural on a fuel bounded by the syntax's size
(`Syn.nodes`), so it runs in the kernel.

It is not proved complete: where it returns `none`, a derivation may still
exist.  The rules are syntax-directed except for the choices below, which
inference makes in this order:

- a constant expression is `const` (`Typed.constShape`: every other
  derivation of it means the same);
- `return (a, b, …);` is `retTuple` before `retVal`;
- `f(x)` is a conversion (`convUser`), then a struct (`structNew`), then a
  builtin, then an internal call, as `f` resolves;
- `a = b` is `assign` before `assignCopy`.
-/

namespace Solidity.Source

/-- A typed expression: its type and derivation. -/
abbrev Inferred (Γ : Ctx) (e : Syn .expr) := (τ : STy) × Typed Γ e τ

/-- Whether a type is a mapping (`Typed.delete`'s and `Typed.assign`'s test). -/
def STy.isMapping (τ : STy) : Bool := τ matches .mapping _ _

/-- Whether a type is an address or contract (`Typed.payable`'s test). -/
def STy.isPayableArg (σ : STy) : Bool :=
  match σ with | .address _ => true | .contract _ => true | _ => false

/-- The location an elementary conversion keeps (`Typed.convElem`). -/
def STy.convLoc (σ : STy) : DataLoc :=
  match σ with | .bytes l => l | .string l => l | _ => .memory

/-- The `const` rule, when its premises hold. -/
def tryConst (Γ : Ctx) (e : Syn .expr) : Option (Inferred Γ e) :=
  match hc : e.const, ha : e.isAddressLit, hx : e.hexLen? with
  | Option.some _, false, Option.none => Option.some ⟨_, .const hc ha hx⟩
  | _, _, _ => Option.none

/-- A binary operation of kind `k` from its operands' derivations. -/
def inferBin (Γ : Ctx) (e a b : Syn .expr) (k : BinKind) (hb : e.binOp? = Option.some (k, a, b))
    (ra : Option (Inferred Γ a)) (rb : Option (Inferred Γ b)) : Option (Inferred Γ e) :=
  match k, hb, a.const, b.const with
  | .order, hb, Option.some _, Option.some _ =>
    match hqa : a.const, hqb : b.const with
    | Option.some _, Option.some _ => Option.some ⟨.bool, .compareConst hb (Or.inl rfl) hqa hqb⟩
    | _, _ => Option.none
  | .eq, hb, Option.some _, Option.some _ =>
    match hqa : a.const, hqb : b.const with
    | Option.some _, Option.some _ => Option.some ⟨.bool, .compareConst hb (Or.inr rfl) hqa hqb⟩
    | _, _ => Option.none
  | k, hb, _, _ =>
    match ra, rb with
    | Option.some ⟨τa, da⟩, Option.some ⟨τb, db⟩ =>
      match k, hb with
      | .arith, hb =>
        match hc : STy.common? Γ.isBase τa τb with
        | Option.some τ =>
          if hn : τ.isNumeric = true then
            if hz : (e.isDivMod && τb.isZeroConst) = false then
              Option.some ⟨τ, .arith hb da db hc hn hz⟩
            else Option.none
          else Option.none
        | Option.none => Option.none
      | .bit, hb =>
        match hc : STy.common? Γ.isBase τa τb with
        | Option.some τ =>
          if hn : τ.isBits = true then Option.some ⟨τ, .bit hb da db hc hn⟩ else Option.none
        | Option.none => Option.none
      | .shift, hb =>
        if h1 : τa.shiftTy.isBits = true then
          if h2 : τb.isAmount = true then
            if h3 : (a.const.isSome && b.const.isSome) = false then
              Option.some ⟨_, .shift hb da db h1 h2 h3⟩
            else Option.none
          else Option.none
        else Option.none
      | .exp, hb =>
        if h1 : τa.shiftTy.isInt = true then
          if h2 : τb.isAmount = true then
            if h3 : (a.const.isSome && b.const.isSome) = false then
              Option.some ⟨_, .exp hb da db h1 h2 h3⟩
            else Option.none
          else Option.none
        else Option.none
      | .order, hb =>
        match hc : STy.common? Γ.isBase τa τb with
        | Option.some τ =>
          if hn : τ.isOrdered = true then Option.some ⟨.bool, .order hb da db hc hn⟩ else Option.none
        | Option.none => Option.none
      | .eq, hb =>
        match hc : STy.common? Γ.isBase τa τb with
        | Option.some τ =>
          if hn : τ.hasEq = true then Option.some ⟨.bool, .eq hb da db hc hn⟩ else Option.none
        | Option.none => Option.none
      | .logic, hb =>
        match τa, da, τb, db with
        | .bool, da, .bool, db => Option.some ⟨.bool, .logic hb da db⟩
        | _, _, _, _ => Option.none
    | _, _ => Option.none

/-- A magic member `g.m` of a builtin `g`. -/
def tryMagic (Γ : Ctx) (g m : String) : Option (Inferred Γ (.member (.ident g) m)) :=
  match hr : Γ.resolve g with
  | Option.some (.builtin b) =>
    match hs : b.memberStatus m, ht : b.memberTy m with
    | Option.some (.admitted _), Option.some τ =>
      if hv : (b == .msg && m == "value" && !Γ.msgValue) = false then
        Option.some ⟨τ, .magic hr hs ht hv⟩
      else Option.none
    | _, _ => Option.none
  | _ => Option.none

/-- An internal call `f(args)` from its arguments' types. -/
def inferCall (Γ : Ctx) (f : String) (args : Syn (.list .expr)) (σs : List STy)
    (da : TypedArgs Γ args σs) : Option (Inferred Γ (.call (.ident f) (.positional args))) :=
  match hf : (Γ.functions f).filter (fun d' => match d'.fnSig Γ.env with
      | Option.some (ps', _) => argsFit Γ.isBase σs ps'
      | Option.none => false) with
  | [d] =>
    match hs : d.fnSig Γ.env with
    | Option.some (_, _) => Option.some ⟨_, .callInternal da hf hs⟩
    | Option.none => Option.none
  | _ => Option.none

mutual

/-- **Type inference** of an expression: a type and a derivation. -/
def Typed.inferN (n : Nat) (Γ : Ctx) (e : Syn .expr) : Option (Inferred Γ e) :=
  match n with
  | 0 => Option.none
  | n + 1 =>
  (tryConst Γ e).orElse fun _ =>
  match e with
  | .lit (.num n) =>
    match hx : (Syn.lit (.num n) : Syn .expr).hexLen? with
    | Option.some _ => Option.some ⟨_, .litBytes hx⟩
    | Option.none =>
      match n with
      | .hex ds true => if h : ds.length = 40 then Option.some ⟨_, .litAddress h⟩ else Option.none
      | _ => Option.none
  | .lit (.bool b) => Option.some ⟨_, .bool b⟩
  | .lit (.str bs) => Option.some ⟨_, .str bs⟩
  | .lit (.hexStr bs) => Option.some ⟨_, .hexStr bs⟩
  | .lit (.unicodeStr bs) => Option.some ⟨_, .unicodeStr bs⟩
  | .ident x =>
    match hr : Γ.resolve x with
    | Option.some (.loc i) =>
      match ht : Γ.tys[i]? with
      | Option.some τ => Option.some ⟨τ, .loc hr ht⟩
      | Option.none => Option.none
    | Option.some (.decls [d]) =>
      match hv : d.varTy Γ.env with
      | Option.some τ => Option.some ⟨τ, .state hr hv⟩
      | Option.none => Option.none
    | Option.some (.builtin .this) =>
      if hx : x = "this" then
        match hs : Γ.scope with
        | Option.some c => Option.some ⟨.contract ⟨Option.none, c⟩, by subst hx; exact .this hr hs⟩
        | Option.none => Option.none
      else Option.none
    | _ => Option.none
  | .tuple (.some a) .nil => do
    let ⟨τ, d⟩ ← Typed.inferN n Γ a
    pure ⟨τ, .paren d⟩
  | .tuple (.some a) s => do
    let ⟨τ, d⟩ ← Typed.inferN n Γ a
    let ⟨τs, ds⟩ ← TypedSlots.inferN n Γ s
    match τs, ds with
    | [], _ => Option.none
    | σ :: σs, ds => pure ⟨_, .tuple d ds (List.cons_ne_nil σ σs)⟩
  | .unaryPrefix .neg a => do
    match ← Typed.inferN n Γ a with
    | ⟨.int t, d⟩ => if h : t.signed = true then pure ⟨_, .neg d h⟩ else Option.none
    | ⟨.fixed _, d⟩ => pure ⟨_, .negFixed d⟩
    | _ => Option.none
  | .unaryPrefix .not a => do
    match ← Typed.inferN n Γ a with
    | ⟨.bool, d⟩ => pure ⟨_, .not d⟩
    | _ => Option.none
  | .unaryPrefix .bitNot a => do
    let ⟨τ, d⟩ ← Typed.inferN n Γ a
    if h : τ.isBits = true then pure ⟨τ, .bitNot d h⟩ else Option.none
  | .unaryPrefix .inc a => do
    let ⟨τ, l⟩ ← LVal.inferN n Γ a
    if h : τ.isNumeric = true then pure ⟨τ, .incDec (Or.inl rfl) l h⟩ else Option.none
  | .unaryPrefix .dec a => do
    let ⟨τ, l⟩ ← LVal.inferN n Γ a
    if h : τ.isNumeric = true then pure ⟨τ, .incDec (Or.inr rfl) l h⟩ else Option.none
  | .unaryPrefix .delete a => do
    let ⟨τ, l⟩ ← LVal.inferN n Γ a
    if h : τ.isMapping = false then
      if hp : (τ.storageRef && Γ.namesLocal a) = false then pure ⟨_, .delete l h hp⟩
      else Option.none
    else Option.none
  | .unarySuffix _ a => do
    let ⟨τ, l⟩ ← LVal.inferN n Γ a
    if h : τ.isNumeric = true then pure ⟨τ, .incDecSuffix l h⟩ else Option.none
  | .mulDivMod op a b => inferBin Γ (.mulDivMod op a b) a b .arith rfl (Typed.inferN n Γ a) (Typed.inferN n Γ b)
  | .addSub op a b => inferBin Γ (.addSub op a b) a b .arith rfl (Typed.inferN n Γ a) (Typed.inferN n Γ b)
  | .bitAnd a b => inferBin Γ (.bitAnd a b) a b .bit rfl (Typed.inferN n Γ a) (Typed.inferN n Γ b)
  | .bitOr a b => inferBin Γ (.bitOr a b) a b .bit rfl (Typed.inferN n Γ a) (Typed.inferN n Γ b)
  | .bitXor a b => inferBin Γ (.bitXor a b) a b .bit rfl (Typed.inferN n Γ a) (Typed.inferN n Γ b)
  | .shift op a b => inferBin Γ (.shift op a b) a b .shift rfl (Typed.inferN n Γ a) (Typed.inferN n Γ b)
  | .exp a b => inferBin Γ (.exp a b) a b .exp rfl (Typed.inferN n Γ a) (Typed.inferN n Γ b)
  | .order op a b => inferBin Γ (.order op a b) a b .order rfl (Typed.inferN n Γ a) (Typed.inferN n Γ b)
  | .equality op a b => inferBin Γ (.equality op a b) a b .eq rfl (Typed.inferN n Γ a) (Typed.inferN n Γ b)
  | .and a b => inferBin Γ (.and a b) a b .logic rfl (Typed.inferN n Γ a) (Typed.inferN n Γ b)
  | .or a b => inferBin Γ (.or a b) a b .logic rfl (Typed.inferN n Γ a) (Typed.inferN n Γ b)
  | .cond c a b => do
    match ← Typed.inferN n Γ c with
    | ⟨.bool, dc⟩ =>
      let ⟨τa, da⟩ ← Typed.inferN n Γ a
      let ⟨τb, db⟩ ← Typed.inferN n Γ b
      match hc : STy.common? Γ.isBase τa.mobile τb.mobile with
      | Option.some τ => pure ⟨τ, .cond dc da db hc⟩
      | Option.none => Option.none
    | _ => Option.none
  | .assign .assign a b => do
    let ⟨τ, l⟩ ← LVal.inferN n Γ a
    let ⟨σ, d⟩ ← Typed.inferN n Γ b
    if h : σ.implicit Γ.isBase τ = true then
      if hm : τ.isMapping = false then pure ⟨τ, .assign l d h hm⟩ else Option.none
    else if hc : σ.copiesTo τ = true then
      if hl : Γ.namesLocal a = false then pure ⟨τ, .assignCopy l d hc hl⟩ else Option.none
    else Option.none
  | .assign op a b => do
    let ⟨τ, l⟩ ← LVal.inferN n Γ a
    let ⟨σ, d⟩ ← Typed.inferN n Γ b
    if h : op.fits Γ.isBase σ τ = true then pure ⟨τ, .compound l d h⟩ else Option.none
  | .index a (.some i) => do
    let ⟨τ, da⟩ ← Typed.inferN n Γ a
    let ⟨σ, di⟩ ← Typed.inferN n Γ i
    match τ, da with
    | .array _ _ n, da =>
      if h1 : σ.isIndex = true then
        if h2 : inBounds σ n = true then pure ⟨_, .indexArray da di h1 h2⟩ else Option.none
      else Option.none
    | .mapping τk _, da =>
      if h : σ.implicit Γ.isBase τk = true then pure ⟨_, .indexMapping da di h⟩ else Option.none
    | .bytes l, da =>
      if h1 : σ.isIndex = true then
        if h2 : inBounds σ Option.none = true then
          pure ⟨_, .indexBytes (τ := .bytes l) da rfl di h1 h2⟩
        else Option.none
      else Option.none
    | .fixedBytes n hn, da =>
      if h1 : σ.isIndex = true then
        if h2 : inBounds σ (Option.some n) = true then
          pure ⟨_, .indexBytes (τ := .fixedBytes n hn) da rfl di h1 h2⟩
        else Option.none
      else Option.none
    | _, _ => Option.none
  | .member a x =>
    ((match a with
      | .ident g => tryMagic Γ g x
      | _ => Option.none : Option (Inferred Γ (.member a x)))).orElse fun _ => do
    let ⟨τ, da⟩ ← Typed.inferN n Γ a
    match hl : τ.lengthTy with
    | Option.some ρ =>
      if hx : x = "length" then pure ⟨ρ, by subst hx; exact .length da hl⟩ else Option.none
    | Option.none =>
      match τ, da with
      | .address _, da =>
        if hb : x = "balance" then pure ⟨_, by subst hb; exact .balance da⟩ else Option.none
      | .struct _ dn, da =>
        match hf : Γ.env.fieldAt dn _ x with
        | Option.some (_, τ) => pure ⟨τ, .member da hf⟩
        | Option.none => Option.none
      | _, _ => Option.none
  | .call (.elemType el h) (.positional (.cons x .nil)) => do
    let ⟨σ, d⟩ ← Typed.inferN n Γ x
    if he : σ.explicit Γ.isBase (el.ty σ.convLoc) = true then pure ⟨_, .convElem d rfl he⟩
    else Option.none
  | .payableConv (.positional (.cons x .nil)) => do
    let ⟨σ, d⟩ ← Typed.inferN n Γ x
    if hp : σ.isPayableArg = true then
      pure ⟨_, .payable d hp⟩
    else Option.none
  | .call (.ident f) (.positional args) => do
    let ⟨σs, da⟩ ← TypedArgs.inferN n Γ args
    match hct : Γ.convTarget f, args, σs, da with
    | Option.some τ, .cons _ .nil, [σ], .cons dx .nil =>
      if he : σ.explicit Γ.isBase τ = true then pure ⟨τ, .convUser hct dx he⟩ else Option.none
    | _, args, σs, da =>
      match hs : Γ.structOf f with
      | Option.some dn =>
        match hfs : Γ.env.structFields dn .memory with
        | Option.some fs =>
          if hfit : argsFit Γ.isBase σs (fs.map Prod.snd) = true then
            pure ⟨_, .structNew hs hfs da hfit⟩
          else Option.none
        | Option.none => Option.none
      | Option.none =>
        match hr : Γ.resolve f with
        | Option.some (.builtin b) =>
          match hst : b.status, hτ : b.callTy Γ.isBase σs with
          | .admitted _, Option.some τ => pure ⟨τ, .builtinCall hr hst da hτ⟩
          | _, _ => Option.none
        | _ => inferCall Γ f args σs da
  | .call (.member c f) (.positional args) => do
    let ⟨σs, da⟩ ← TypedArgs.inferN n Γ args
    let abi : Option (Inferred Γ (.call (.member c f) (.positional args))) :=
      match c with
      | .ident g =>
        match hr : Γ.resolve g, hk : AbiKind.ofMember f with
        | Option.some (.builtin .abi), Option.some k =>
          if hok : k.argsOK Γ.isBase σs = true then Option.some ⟨_, .abiEncode hr hk da hok⟩
          else Option.none
        | _, _ => Option.none
      | _ => Option.none
    abi.orElse fun _ => do
    let ⟨τc, dc⟩ ← Typed.inferN n Γ c
    match τc, dc, args, σs, da with
    | .address true, dc, .cons _ .nil, [σ], .cons dv .nil =>
      if hv : σ.implicit Γ.isBase (.int IntTy.u256) = true then
        if ht : f = "transfer" then pure ⟨_, by subst ht; exact .transfer dc dv hv⟩
        else if hs : f = "send" then pure ⟨_, by subst hs; exact .send dc dv hv⟩
        else Option.none
      else Option.none
    | .contract dn, dc, _, σs, da =>
      match ho : extOverloads Γ.env Γ.isBase dn f σs with
      | [d] =>
        match hs : d.fnSig Γ.env with
        | Option.some (_, _) => pure ⟨_, .extCall dc da ho hs⟩
        | Option.none => Option.none
      | _ => Option.none
    | _, _, _, _, _ => Option.none
  | .call (.callOptions (.member c f) (.namedArg "value" v) .nil) (.positional args) => do
    let ⟨τc, dc⟩ ← Typed.inferN n Γ c
    let ⟨σ, dv⟩ ← Typed.inferN n Γ v
    let ⟨σs, da⟩ ← TypedArgs.inferN n Γ args
    match τc, dc with
    | .contract dn, dc =>
      if hv : σ.implicit Γ.isBase (.int IntTy.u256) = true then
        match ho : extOverloads Γ.env Γ.isBase dn f σs with
        | [d] =>
          match hs : d.fnSig Γ.env, hm : d.fnMut with
          | Option.some (_, _), Option.some .payable => pure ⟨_, .extCallValue dc dv hv da ho hs hm⟩
          | _, _ => Option.none
        | _ => Option.none
      else Option.none
    | _, _ => Option.none
  | _ => Option.none
termination_by structural n

/-- Inference of an lvalue. -/
def LVal.inferN (n : Nat) (Γ : Ctx) (e : Syn .expr) : Option ((τ : STy) × LVal Γ e τ) :=
  match n with
  | 0 => Option.none
  | n + 1 =>
  match e with
  | .ident x =>
    match hr : Γ.resolve x with
    | Option.some (.loc i) =>
      match ht : Γ.tys[i]? with
      | Option.some τ => Option.some ⟨τ, .loc hr ht⟩
      | Option.none => Option.none
    | Option.some (.decls [d]) =>
      match hv : d.varTy Γ.env with
      | Option.some τ => if hm : d.mutable = true then Option.some ⟨τ, .state hr hv hm⟩ else Option.none
      | Option.none => Option.none
    | _ => Option.none
  | .tuple (.some a) .nil => do
    let ⟨τ, l⟩ ← LVal.inferN n Γ a
    pure ⟨τ, .paren l⟩
  | .index a (.some i) => do
    let ⟨τ, da⟩ ← Typed.inferN n Γ a
    let ⟨σ, di⟩ ← Typed.inferN n Γ i
    match τ, da with
    | .array l _ n, da =>
      if hl : l = .calldata then Option.none else
      if h1 : σ.isIndex = true then
        if h2 : inBounds σ n = true then pure ⟨_, .indexArray da hl di h1 h2⟩ else Option.none
      else Option.none
    | .mapping τk _, da =>
      if h : σ.implicit Γ.isBase τk = true then pure ⟨_, .indexMapping da di h⟩ else Option.none
    | .bytes l, da =>
      if hl : l = .calldata then Option.none else
      if h1 : σ.isIndex = true then pure ⟨_, .indexBytes da hl di h1⟩ else Option.none
    | _, _ => Option.none
  | .member a x => do
    let ⟨τ, da⟩ ← Typed.inferN n Γ a
    match τ, da with
    | .struct l dn, da =>
      if hl : l = .calldata then Option.none else
      match hf : Γ.env.fieldAt dn l x with
      | Option.some (_, τ) => pure ⟨τ, .member da hl hf⟩
      | Option.none => Option.none
    | _, _ => Option.none
  | _ => Option.none
termination_by structural n

/-- Inference of an argument list. -/
def TypedArgs.inferN (n : Nat) (Γ : Ctx) (es : Syn (.list .expr)) :
    Option ((τs : List STy) × TypedArgs Γ es τs) :=
  match n with
  | 0 => Option.none
  | n + 1 =>
  match es with
  | .nil => Option.some ⟨[], .nil⟩
  | .cons e es => do
    let ⟨τ, d⟩ ← Typed.inferN n Γ e
    let ⟨τs, ds⟩ ← TypedArgs.inferN n Γ es
    pure ⟨τ :: τs, .cons d ds⟩
termination_by structural n

/-- Inference of tuple slots, each present. -/
def TypedSlots.inferN (n : Nat) (Γ : Ctx) (s : Syn (.list (.opt .expr))) :
    Option ((τs : List STy) × TypedSlots Γ s τs) :=
  match n with
  | 0 => Option.none
  | n + 1 =>
  match s with
  | .nil => Option.some ⟨[], .nil⟩
  | .cons (.some e) es => do
    let ⟨τ, d⟩ ← Typed.inferN n Γ e
    let ⟨τs, ds⟩ ← TypedSlots.inferN n Γ es
    pure ⟨τ :: τs, .cons d ds⟩
  | .cons .none _ => Option.none
termination_by structural n

end

/-- **Type inference** of an expression, with fuel its number of nodes
(each rule's premises are about strictly smaller syntax, so the fuel never
runs out first). -/
def Typed.infer (Γ : Ctx) (e : Syn .expr) : Option (Inferred Γ e) := Typed.inferN (e.nodes.length + 1) Γ e

/-- Inference of an lvalue. -/
def LVal.infer (Γ : Ctx) (e : Syn .expr) : Option ((τ : STy) × LVal Γ e τ) :=
  LVal.inferN (e.nodes.length + 1) Γ e

/-- Inference of an argument list. -/
def TypedArgs.infer (Γ : Ctx) (es : Syn (.list .expr)) : Option ((τs : List STy) × TypedArgs Γ es τs) :=
  TypedArgs.inferN (es.nodes.length + 1) Γ es

/-- Inference of tuple slots. -/
def TypedSlots.infer (Γ : Ctx) (s : Syn (.list (.opt .expr))) :
    Option ((τs : List STy) × TypedSlots Γ s τs) :=
  TypedSlots.inferN (s.nodes.length + 1) Γ s

/-- Inference of an optional loop condition. -/
def OptCond.infer (Γ : Ctx) (c : Syn (.opt .expr)) : Option (OptCond Γ c) :=
  match c with
  | .none => Option.some .none
  | .some e =>
    match Typed.infer Γ e with
    | Option.some ⟨.bool, d⟩ => Option.some (.some d)
    | _ => Option.none

/-- Inference of an optional loop step. -/
def OptExpr.infer (Γ : Ctx) (c : Syn (.opt .expr)) : Option (OptExpr Γ c) :=
  match c with
  | .none => Option.some .none
  | .some e => (Typed.infer Γ e).map fun ⟨_, d⟩ => .some d

/-- The locals a statement leaves, and its derivation. -/
abbrev StmtInferred (C : Ctx) {k : SCtx} (L : List (String × STy)) (s : Syn (.stmt k)) :=
  (L' : List (String × STy)) × StmtD C L s L'

/-- Inference of a simple statement (no nested statements). -/
def StmtD.inferSimple (C : Ctx) {k : SCtx} (L : List (String × STy)) (i : Syn .simple) :
    Option (StmtInferred C (k := k) L (.simpleStmt i)) :=
  match i with
  | .exprStmt e =>
    match e with
    | .ident x =>
      if hx : x = "_" then
        if hm : C.inModifier = true then Option.some ⟨L, by subst hx; exact .placeholder hm⟩
        else (Typed.infer (C.at L) (.ident x)).bind fun ⟨_, d⟩ =>
          if hu : (C.inModifier && (Syn.ident x : Syn .expr).isUnderscore) = false then
            Option.some ⟨L, .expr d hu⟩
          else Option.none
      else (Typed.infer (C.at L) (.ident x)).bind fun ⟨_, d⟩ =>
        if hu : (C.inModifier && (Syn.ident x : Syn .expr).isUnderscore) = false then
          Option.some ⟨L, .expr d hu⟩
        else Option.none
    | e => (Typed.infer (C.at L) e).bind fun ⟨_, d⟩ =>
      if hu : (C.inModifier && e.isUnderscore) = false then Option.some ⟨L, .expr d hu⟩
      else Option.none
  | .declVar (.varDecl t l x) .none =>
    match ht : t.ty C.env C.scope (l.getD .memory) with
    | Option.some τ =>
      if hl : locOK τ l false = true then Option.some ⟨_, .declVar ht hl⟩ else Option.none
    | Option.none => Option.none
  | .declVar (.varDecl t l x) (.some e) =>
    match ht : t.ty C.env C.scope (l.getD .memory) with
    | Option.some τ =>
      if hl : locOK τ l true = true then
        (Typed.infer (C.at L) e).bind fun ⟨σ, d⟩ =>
          if h : σ.implicit C.isBase τ = true then Option.some ⟨_, .declInit ht hl d h⟩
          else Option.none
      else Option.none
    | Option.none => Option.none
  | _ => Option.none

/-- `return e;` against a single return. -/
def StmtD.inferSingle (C : Ctx) {k : SCtx} (L : List (String × STy)) (e : Syn .expr) :
    Option (StmtInferred C (k := k) L (.returnStmt (.some e))) :=
  match hR : C.rets with
  | [τ] => (Typed.infer (C.at L) e).bind fun ⟨σ, d⟩ =>
    if h : σ.implicit C.isBase τ = true then Option.some ⟨L, .retVal hR d h⟩ else Option.none
  | _ => Option.none

/-- `return e;`: a tuple of two or more components against the returns,
otherwise a single value. -/
def StmtD.inferReturn (C : Ctx) {k : SCtx} (L : List (String × STy)) (e : Syn .expr) :
    Option (StmtInferred C (k := k) L (.returnStmt (.some e))) :=
  match e with
  | .tuple (.some a) s =>
    ((match Typed.infer (C.at L) a, TypedSlots.infer (C.at L) s with
      | Option.some ⟨σ, d⟩, Option.some ⟨σ' :: σs, ds⟩ =>
        if h : argsFit C.isBase (σ :: σ' :: σs) C.rets = true then
          Option.some ⟨L, .retTuple d ds (List.cons_ne_nil σ' σs) h⟩
        else Option.none
      | _, _ => Option.none : Option (StmtInferred C (k := k) L (.returnStmt (.some (.tuple (.some a) s))))
      )).orElse fun _ => StmtD.inferSingle C L _
  | e => StmtD.inferSingle C L e

mutual

/-- **Inference of a statement**: the locals it leaves and a derivation. -/
def StmtD.inferN (n : Nat) (C : Ctx) {k : SCtx} (L : List (String × STy)) (s : Syn (.stmt k)) :
    Option (StmtInferred C L s) :=
  match n with
  | 0 => Option.none
  | n + 1 =>
  match k, s with
  | _, .simpleStmt i => StmtD.inferSimple C L i
  | _, .blockStmt (.block b) => (ItemsD.inferN n C L b).map fun ⟨_, d⟩ => ⟨L, .block d⟩
  | _, .ifStmt c s .none =>
    match Typed.infer (C.at L) c with
    | Option.some ⟨.bool, dc⟩ =>
      if hd : s.isDecl = false then
        (StmtD.inferN n C L s).map fun ⟨_, ds⟩ => ⟨L, .ifThen dc hd ds⟩
      else Option.none
    | _ => Option.none
  | _, .ifStmt c s (.some t) =>
    match Typed.infer (C.at L) c with
    | Option.some ⟨.bool, dc⟩ =>
      if hd : s.isDecl = false then
        if ht : t.isDecl = false then
          (StmtD.inferN n C L s).bind fun ⟨_, ds⟩ =>
            (StmtD.inferN n C L t).map fun ⟨_, dt⟩ => ⟨L, .ifElse dc hd ht ds dt⟩
        else Option.none
      else Option.none
    | _ => Option.none
  | _, .whileStmt c s =>
    match Typed.infer (C.at L) c with
    | Option.some ⟨.bool, dc⟩ =>
      if hd : s.isDecl = false then
        (StmtD.inferN n C L s).map fun ⟨_, ds⟩ => ⟨L, .whileLoop dc hd ds⟩
      else Option.none
    | _ => Option.none
  | _, .doWhile s c =>
    match Typed.infer (C.at L) c with
    | Option.some ⟨.bool, dc⟩ =>
      if hd : s.isDecl = false then
        (StmtD.inferN n C L s).map fun ⟨_, ds⟩ => ⟨L, .doWhile hd ds dc⟩
      else Option.none
    | _ => Option.none
  | _, .forStmt .none c post s =>
    match OptCond.infer (C.at L) c, OptExpr.infer (C.at L) post with
    | Option.some dc, Option.some dp =>
      if hd : s.isDecl = false then
        (StmtD.inferN n C L s).map fun ⟨_, ds⟩ => ⟨L, .forLoop dc dp hd ds⟩
      else Option.none
    | _, _ => Option.none
  | _, .forStmt (.some i) c post s =>
    (StmtD.inferSimple C (k := ⟨true, _⟩) L i).bind fun ⟨L₁, di⟩ =>
    match OptCond.infer (C.at L₁) c, OptExpr.infer (C.at L₁) post with
    | Option.some dc, Option.some dp =>
      if hd : s.isDecl = false then
        (StmtD.inferN n C L₁ s).map fun ⟨_, ds⟩ => ⟨L, .forInit di dc dp hd ds⟩
      else Option.none
    | _, _ => Option.none
  | _, .breakStmt => Option.some ⟨L, .brk⟩
  | _, .continueStmt => Option.some ⟨L, .cont⟩
  | _, .returnStmt .none =>
    match hR : C.rets with
    | [] => Option.some ⟨L, .ret hR⟩
    | _ => Option.none
  | _, .returnStmt (.some e) => StmtD.inferReturn C L e
  | _, .emit (.ident ev) (.positional args) =>
    (TypedArgs.infer (C.at L) args).bind fun ⟨σs, da⟩ =>
    match hf : ((C.at L).declsOf .event ev).filter (·.fitsParams C.env C.isBase σs) with
    | [_] => Option.some ⟨L, .emit da hf⟩
    | _ => Option.none
  | _, .revert (.ident er) (.positional args) =>
    (TypedArgs.infer (C.at L) args).bind fun ⟨σs, da⟩ =>
    match hf : ((C.at L).declsOf .error er).filter (·.fitsParams C.env C.isBase σs) with
    | [_] => Option.some ⟨L, .revertError da hf⟩
    | _ => Option.none
  | _, .assembly false _ body =>
    if hb : isRethrow body = true then
      match hv : rethrowVar? body with
      | Option.some d =>
        match hr : (C.at L).resolve d with
        | Option.some (.loc i) =>
          match ht : (L.map Prod.snd)[i]? with
          | Option.some (.bytes .memory) => Option.some ⟨L, .rethrow hb hr ht hv⟩
          | _ => Option.none
        | _ => Option.none
      | Option.none => Option.none
    else Option.none
  | _, _ => Option.none
termination_by structural n

/-- **Inference of a block**: its items in order. -/
def ItemsD.inferN (n : Nat) (C : Ctx) {k : SCtx} (L : List (String × STy)) (b : Syn (.list (.item k))) :
    Option ((L' : List (String × STy)) × ItemsD C L b L') :=
  match n with
  | 0 => Option.none
  | n + 1 =>
  match k, b with
  | _, .nil => Option.some ⟨L, .nil⟩
  | _, .cons (.stmtItem s) rest =>
    (StmtD.inferN n C L s).bind fun ⟨L₁, ds⟩ =>
      (ItemsD.inferN n C L₁ rest).map fun ⟨L₂, dr⟩ => ⟨L₂, .stmt ds dr⟩
  | _, .cons (.uncheckedItem (.block b)) rest =>
    (ItemsD.inferN n C L b).bind fun ⟨_, db⟩ =>
      (ItemsD.inferN n C L rest).map fun ⟨L₂, dr⟩ => ⟨L₂, .unchecked db dr⟩
termination_by structural n

end

/-- Inference of a statement. -/
def StmtD.infer (C : Ctx) {k : SCtx} (L : List (String × STy)) (s : Syn (.stmt k)) :
    Option (StmtInferred C L s) :=
  StmtD.inferN (s.nodes.length + 1) C L s

/-- Inference of a block. -/
def ItemsD.infer (C : Ctx) {k : SCtx} (L : List (String × STy)) (b : Syn (.list (.item k))) :
    Option ((L' : List (String × STy)) × ItemsD C L b L') :=
  ItemsD.inferN (b.nodes.length + 1) C L b

end Solidity.Source
