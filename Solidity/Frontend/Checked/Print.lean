import Solidity.Frontend.Checked.Token

/-!
# The token yield of the source syntax (G09–G11)

`Syn.yield t L` is the token sequence a tree `t : Syn c` (S00,
`Solidity/Source/Syntax.lean`) derives in the pinned grammar
(`SolidityParser.g4`), one clause per constructor, read off the grammar's
rule for it.  It is the specification the parser is checked against:
`parse ts = .ok t` implies `t.yield L = some (ts, [])` for the layout `L` the
parser returns (`Solidity/Frontend/Checked/Check.lean`).

**Layouts.**  S00 abstracts two spellings the grammar distinguishes: the
order of a definition's attributes (`public view`, `view public`), which the
grammar allows in any order but S00 stores as fields, and the fragments of a
concatenated string literal (`"a" "b"`), which S00 stores as one byte
string.  A layout is the list of these choices, consumed in pre-order
(`Choice.attrs` per attribute-bearing node, `Choice.frags` per string
literal), so `∃ L, t.yield L = some (ts, [])` is the grammar derivation of
`ts` from `t`.  Every other spelling difference is below the tokens (`uint`
and `uint256` are one token, G08).

**Parentheses are syntax.**  S00 represents `(e)` as a one-component tuple,
so the yield inserts no parentheses: it is the grammar's derivation, not a
pretty printer.  Which of several trees with one yield the parser returns is
fixed by the precedence predicate `Syn.Prec` (`Solidity/Frontend/Checked/Prec.lean`).
-/

namespace Solidity.Frontend.Checked

open Solidity.Source

/-- An attribute slot of a definition, in the order the source spells them;
`modInv` takes the next modifier invocation. -/
inductive Slot where
  | vis | mutab | modInv | virt | over | payable | ext | const | transient
  deriving DecidableEq, Repr

/-- One layout choice. -/
inductive Choice where
  /-- The source order of a definition's attributes. -/
  | attrs (order : List Slot)
  /-- The byte lengths of a string literal's fragments (at least one). -/
  | frags (lens : List Nat)
  /-- A contract with both `layout at` and `is`: whether `layout` comes first. -/
  | layoutFirst (b : Bool)
  deriving DecidableEq, Repr

/-- The printer's state: the remaining layout. -/
abbrev Pr := StateT (List Choice) Option

def Pr.pop : Pr Choice := fun s =>
  match s with
  | c :: cs => some (c, cs)
  | [] => none

def Pr.lift {α : Type} (o : Option α) : Pr α := fun s => o.map (·, s)

end Solidity.Frontend.Checked

/-! ## Token helpers -/

namespace Solidity.Source

open Solidity.Frontend.Checked

def tk (k : Kw) : List Tok := [.kw k]
def pu (p : Punct) : List Tok := [.punct p]
def idt (s : String) : List Tok := [.ident s]

/-- `identifierPath`. -/
def IdPath.toks (p : IdPath) : List Tok :=
  .ident p.head :: p.tail.flatMap fun s => [.punct .period, .ident s]

/-- Items separated by commas. -/
def commaSep (xs : List (List Tok)) : List Tok := (xs.intersperse (pu .comma)).flatten

def parens (xs : List Tok) : List Tok := pu .lparen ++ xs ++ pu .rparen
def braces (xs : List Tok) : List Tok := pu .lbrace ++ xs ++ pu .rbrace

/-- `elementaryTypeName`: `address payable` is two tokens. -/
def Elem.toks : Elem → List Tok
  | .addressPayable => [.elem .address, .kw .payable]
  | e => [.elem e]

def Visibility.toks : Visibility → List Tok
  | .internal => tk .internal | .external => tk .external
  | .priv => tk .private_ | .pub => tk .public_
def Mutability.toks : Mutability → List Tok
  | .pure => tk .pure | .view => tk .view | .payable => tk .payable
def DataLoc.toks : DataLoc → List Tok
  | .memory => tk .memory | .storage => tk .storage | .calldata => tk .calldata
def StateVis.toks : StateVis → List Tok
  | .pub => tk .public_ | .priv => tk .private_ | .internal => tk .internal
def CtorVis.toks : CtorVis → List Tok
  | .internal => tk .internal | .pub => tk .public_

def optToks {α : Type} (f : α → List Tok) : Option α → List Tok
  | some a => f a
  | none => []

/-- `overrideSpecifier`. -/
def overrideToks : Option (List IdPath) → List Tok
  | none => []
  | some [] => tk .override
  | some ps => tk .override ++ parens (commaSep (ps.map IdPath.toks))

def UserOp.toks : UserOp → List Tok
  | .bitAnd => pu .bitAnd | .bitNot => pu .bitNot | .bitOr => pu .bitOr
  | .bitXor => pu .bitXor | .add => pu .add | .div => pu .div | .mod => pu .mod
  | .mul => pu .mul | .sub => pu .sub | .eq => pu .equal | .gt => pu .gt
  | .ge => pu .ge | .lt => pu .lt | .le => pu .le | .ne => pu .notEqual

def PrefixOp.punct : PrefixOp → List Tok
  | .inc => pu .inc | .dec => pu .dec | .not => pu .not | .bitNot => pu .bitNot
  | .delete => tk .delete | .neg => pu .sub
def SuffixOp.punct : SuffixOp → Punct
  | .inc => .inc | .dec => .dec
def MulOp.punct : MulOp → Punct
  | .mul => .mul | .div => .div | .mod => .mod
def AddOp.punct : AddOp → Punct
  | .add => .add | .sub => .sub
def ShiftOp.punct : ShiftOp → Punct
  | .shl => .shl | .sar => .sar | .shr => .shr
def OrderOp.punct : OrderOp → Punct
  | .lt => .lt | .gt => .gt | .le => .le | .ge => .ge
def EqOp.punct : EqOp → Punct
  | .eq => .equal | .ne => .notEqual
def AssignOp.punct : AssignOp → Punct
  | .assign => .assign | .bitOr => .assignBitOr | .bitXor => .assignBitXor
  | .bitAnd => .assignBitAnd | .shl => .assignShl | .sar => .assignSar
  | .shr => .assignShr | .add => .assignAdd | .sub => .assignSub | .mul => .assignMul
  | .div => .assignDiv | .mod => .assignMod

def YulLit.toks : YulLit → List Tok
  | .dec n => [.yulDec n] | .hex n => [.yulHex n] | .str b => [.str b]
  | .hexStr b => [.hexStr b] | .bool b => [.bool b]

/-- Cut `bs` into fragments of the given lengths, exactly. -/
def chunks (bs : Bytes) : List Nat → Option (List Bytes)
  | [] => if bs.isEmpty then some [] else none
  | n :: ns => (chunks (bs.drop n) ns).bind fun r =>
      if n ≤ bs.length then some (bs.take n :: r) else none

/-- A string literal's fragments (`stringLiteral`, `hexStringLiteral`,
`unicodeStringLiteral`: one or more tokens), from its `frags` choice. -/
def fragsP (mk : Bytes → Tok) (bs : Bytes) : Pr (List Tok) := do
  match ← Pr.pop with
  | .frags lens@(_ :: _) =>
    let cs ← Pr.lift (chunks bs lens)
    pure (cs.map mk)
  | _ => Pr.lift Option.none

/-- `literal`. -/
def litP : Lit → Pr (List Tok)
  | .str b => fragsP .str b
  | .hexStr b => fragsP .hexStr b
  | .unicodeStr b => fragsP .unicodeStr b
  | .bool b => pure [.bool b]
  | .num n => pure [.num n]

/-- Arrange present attributes (`singles`, each once) and modifier
invocations (`mods`, in order) in the source order `o`. -/
def arrange : List Slot → List (Slot × List Tok) → List (List Tok) → Option (List Tok)
  | [], [], [] => some []
  | .modInv :: o, singles, m :: ms => (arrange o singles ms).map (m ++ ·)
  | s :: o, singles, ms =>
    if s == .modInv then none else
    match singles.find? (·.1 == s) with
    | some (_, ts) => (arrange o (singles.filter (·.1 != s)) ms).map (ts ++ ·)
    | none => none
  | [], _, _ => none

/-- An attribute run, from its `attrs` choice. -/
def attrsP (singles : List (Slot × List Tok)) (mods : List (List Tok)) (o : List Slot) :
    Pr (List Tok) :=
  Pr.lift (arrange o singles mods)

def popAttrs : Pr (List Slot) := do
  match ← Pr.pop with
  | .attrs o => pure o
  | _ => Pr.lift Option.none

/-- A present attribute. -/
def single (s : Slot) (ts : List Tok) : List (Slot × List Tok) :=
  if ts.isEmpty then [] else [(s, ts)]

/-! ## The yield -/

/-- **The yield**: a tree's tokens, as items.  A tree of a list category
yields one item per element, an option none or one, any other one item; the
parent joins them by its rule (`commaSep`, juxtaposition). -/
def Syn.yield : {c : Cat} → Syn c → Pr (List (List Tok))
  | _, .nil => pure []
  | _, .cons x xs => do
    let a ← x.yield
    let b ← xs.yield
    pure (a.flatten :: b)
  | _, .none => pure []
  | _, .some x => do pure [(← x.yield).flatten]
  | _, .unit xs => do pure [(← xs.yield).flatten]
  | _, .pragma ws => pure [tk .pragma ++ ws.map .pragmaWord ++ pu .semi]
  | _, .importPath p a =>
    pure [tk .import_ ++ [.str (ascii p)] ++ optToks (fun a => tk .as_ ++ idt a) a ++ pu .semi]
  | _, .importSymbols a as p => do
    let x ← a.yield
    let xs ← as.yield
    pure [tk .import_ ++ braces (commaSep (x.flatten :: xs)) ++ idt "from" ++ [.str (ascii p)] ++
      pu .semi]
  | _, .importStar a p =>
    pure [tk .import_ ++ pu .mul ++ tk .as_ ++ idt a ++ idt "from" ++ [.str (ascii p)] ++ pu .semi]
  | _, .importAlias s a => pure [idt s ++ optToks (fun a => tk .as_ ++ idt a) a]
  | _, .contract abs name lay inh body => do
    let lf ← match lay, inh with
      | .some _, .cons _ _ => do
        match ← Pr.pop with
        | .layoutFirst b => pure b
        | _ => Pr.lift Option.none
      | _, _ => pure true
    let l ← lay.yield
    let i ← inh.yield
    let b ← body.yield
    let layT := match l with
      | [e] => idt "layout" ++ idt "at" ++ e
      | _ => []
    let inhT := if i.isEmpty then [] else tk .is ++ commaSep i
    pure [(if abs then tk .abstract else []) ++ tk .contract ++ idt name ++
      (if lf then layT ++ inhT else inhT ++ layT) ++ braces b.flatten]
  | _, .interface name inh body => do
    let i ← inh.yield
    let b ← body.yield
    pure [tk .interface ++ idt name ++ (if i.isEmpty then [] else tk .is ++ commaSep i) ++
      braces b.flatten]
  | _, .library name body => do
    let b ← body.yield
    pure [tk .library ++ idt name ++ braces b.flatten]
  | _, .topPart p => p.yield
  | _, .inherit base args => do
    pure [base.toks ++ (← args.yield).flatten]
  | _, .constructor ps mods payable vis body => do
    let o ← popAttrs
    let p ← ps.yield
    let m ← mods.yield
    let a ← attrsP (single .payable (if payable then tk .payable else []) ++
      single .vis (optToks CtorVis.toks vis)) m o
    let b ← body.yield
    pure [tk .constructor ++ parens (commaSep p) ++ a ++ b.flatten]
  | _, .function name ps vis mu mods virt over rets body => do
    let o ← popAttrs
    let p ← ps.yield
    let m ← mods.yield
    let a ← attrsP (single .vis (optToks Visibility.toks vis) ++
      single .mutab (optToks Mutability.toks mu) ++
      single .virt (if virt then tk .virtual else []) ++ single .over (overrideToks over)) m o
    let r ← rets.yield
    let b ← body.yield
    let nameT := match name with
      | .ident s => idt s | .fallback => tk .fallback | .receive => tk .receive
    pure [tk .function ++ nameT ++ parens (commaSep p) ++ a ++
      (if r.isEmpty then [] else tk .returns ++ parens (commaSep r)) ++
      (match b with | [x] => x | _ => pu .semi)]
  | _, .modifier name ps virt over body => do
    let o ← popAttrs
    let p ← ps.yield
    let a ← attrsP (single .virt (if virt then tk .virtual else []) ++
      single .over (overrideToks over)) [] o
    let b ← body.yield
    pure [tk .modifier ++ idt name ++ (match p with | [x] => parens x | _ => []) ++ a ++
      (match b with | [x] => x | _ => pu .semi)]
  | _, .fallback sig ext mu mods virt over body => do
    let o ← popAttrs
    let s ← sig.yield
    let m ← mods.yield
    let a ← attrsP (single .ext (if ext then tk .external else []) ++
      single .mutab (optToks Mutability.toks mu) ++
      single .virt (if virt then tk .virtual else []) ++ single .over (overrideToks over)) m o
    let b ← body.yield
    -- `sig` yields the parameters and, separately, the `returns` clause.
    match s with
    | [ps, rs] =>
      pure [tk .fallback ++ parens ps ++ a ++ rs ++ (match b with | [x] => x | _ => pu .semi)]
    | _ => Pr.lift Option.none
  | _, .fbNoParams => pure [[], []]
  | _, .fbParams p ps rets => do
    let x ← p.yield
    let xs ← ps.yield
    let r ← rets.yield
    pure [commaSep (x.flatten :: xs), if r.isEmpty then [] else tk .returns ++ parens (commaSep r)]
  | _, .receive ext payable mods virt over body => do
    let o ← popAttrs
    let m ← mods.yield
    let a ← attrsP (single .ext (if ext then tk .external else []) ++
      single .payable (if payable then tk .payable else []) ++
      single .virt (if virt then tk .virtual else []) ++ single .over (overrideToks over)) m o
    let b ← body.yield
    pure [tk .receive ++ pu .lparen ++ pu .rparen ++ a ++ (match b with | [x] => x | _ => pu .semi)]
  | _, .struct name m ms => do
    let x ← m.yield
    let xs ← ms.yield
    pure [tk .struct ++ idt name ++ braces (x.flatten ++ xs.flatten)]
  | _, .structMember t name => do
    pure [(← t.yield).flatten ++ idt name ++ pu .semi]
  | _, .enum name first rest =>
    pure [tk .enum ++ idt name ++ braces (commaSep ((first :: rest).map idt))]
  | _, .udvt name e => pure [tk .type_ ++ idt name ++ tk .is ++ e.toks ++ pu .semi]
  | _, .stateVar t vis const over trans name init => do
    let o ← popAttrs
    let ty ← t.yield
    let a ← attrsP (single .vis (optToks StateVis.toks vis) ++
      single .const (optToks (fun | .constant => tk .constant | .immutable => tk .immutable) const) ++
      single .over (overrideToks over) ++ single .transient (if trans then idt "transient" else [])) [] o
    let i ← init.yield
    pure [ty.flatten ++ a ++ idt name ++ (match i with | [x] => pu .assign ++ x | _ => []) ++ pu .semi]
  | _, .constant t name e => do
    let ty ← t.yield
    let x ← e.yield
    pure [ty.flatten ++ tk .constant ++ idt name ++ pu .assign ++ x.flatten ++ pu .semi]
  | _, .event name ps anon => do
    let p ← ps.yield
    pure [tk .event ++ idt name ++ parens (commaSep p) ++ (if anon then tk .anonymous else []) ++
      pu .semi]
  | _, .eventParam t idx name => do
    pure [(← t.yield).flatten ++ (if idx then tk .indexed else []) ++ optToks idt name]
  | _, .error name ps => do
    let p ← ps.yield
    pure [idt "error" ++ idt name ++ parens (commaSep p) ++ pu .semi]
  | _, .errorParam t name => do
    pure [(← t.yield).flatten ++ optToks idt name]
  | _, .usingPart u => u.yield
  | _, .usingPath lib ty glob => do
    let t ← ty.yield
    pure [tk .using ++ lib.toks ++ tk .for_ ++ (match t with | [x] => x | _ => pu .mul) ++
      (if glob then idt "global" else []) ++ pu .semi]
  | _, .usingAliases a as ty glob => do
    let x ← a.yield
    let xs ← as.yield
    let t ← ty.yield
    pure [tk .using ++ braces (commaSep (x.flatten :: xs)) ++ tk .for_ ++
      (match t with | [x] => x | _ => pu .mul) ++ (if glob then idt "global" else []) ++ pu .semi]
  | _, .usingAlias fn op => pure [fn.toks ++ optToks (fun o => tk .as_ ++ o.toks) op]
  | _, .positional es => do pure [parens (commaSep (← es.yield))]
  | _, .named as => do pure [parens (braces (commaSep (← as.yield)))]
  | _, .namedArg name e => do pure [idt name ++ pu .colon ++ (← e.yield).flatten]
  | _, .modInv name args => do pure [name.toks ++ (← args.yield).flatten]
  | _, .param t loc name => do
    pure [(← t.yield).flatten ++ optToks DataLoc.toks loc ++ optToks idt name]
  | _, .elem e => pure [e.toks]
  | _, .fnType ps vis mu rets => do
    let o ← popAttrs
    let p ← ps.yield
    let a ← attrsP (single .vis (optToks Visibility.toks vis) ++
      single .mutab (optToks Mutability.toks mu)) [] o
    let r ← rets.yield
    pure [tk .function ++ parens (commaSep p) ++ a ++
      (if r.isEmpty then [] else tk .returns ++ parens (commaSep r))]
  | _, .mapping key kn v vn => do
    let k := match key with | .elem e _ => e.toks | .path p => p.toks
    pure [tk .mapping ++ parens (k ++ optToks idt kn ++ pu .doubleArrow ++ (← v.yield).flatten ++
      optToks idt vn)]
  | _, .userType p => pure [p.toks]
  | _, .array t len => do
    let ty ← t.yield
    let l ← len.yield
    pure [ty.flatten ++ pu .lbrack ++ l.flatten ++ pu .rbrack]
  | _, .varDecl t loc name => do
    pure [(← t.yield).flatten ++ optToks DataLoc.toks loc ++ idt name]
  | _, .index e i => do
    let a ← e.yield
    let b ← i.yield
    pure [a.flatten ++ pu .lbrack ++ b.flatten ++ pu .rbrack]
  | _, .slice e i j => do
    let a ← e.yield
    let b ← i.yield
    let c ← j.yield
    pure [a.flatten ++ pu .lbrack ++ b.flatten ++ pu .colon ++ c.flatten ++ pu .rbrack]
  | _, .member e name => do
    pure [(← e.yield).flatten ++ pu .period ++
      (if name == "address" then [.elem .address] else idt name)]
  | _, .callOptions e a as => do
    let x ← e.yield
    let y ← a.yield
    let ys ← as.yield
    pure [x.flatten ++ braces (commaSep (y.flatten :: ys))]
  | _, .call e args => do
    let x ← e.yield
    let a ← args.yield
    pure [x.flatten ++ a.flatten]
  | _, .payableConv args => do pure [tk .payable ++ (← args.yield).flatten]
  | _, .metaType t => do pure [tk .type_ ++ parens (← t.yield).flatten]
  | _, .unaryPrefix op e => do pure [op.punct ++ (← e.yield).flatten]
  | _, .unarySuffix op e => do pure [(← e.yield).flatten ++ pu op.punct]
  | _, .exp a b => do
    let x ← a.yield
    let y ← b.yield
    pure [x.flatten ++ pu .exp ++ y.flatten]
  | _, .mulDivMod op a b => do
    let x ← a.yield
    let y ← b.yield
    pure [x.flatten ++ pu op.punct ++ y.flatten]
  | _, .addSub op a b => do
    let x ← a.yield
    let y ← b.yield
    pure [x.flatten ++ pu op.punct ++ y.flatten]
  | _, .shift op a b => do
    let x ← a.yield
    let y ← b.yield
    pure [x.flatten ++ pu op.punct ++ y.flatten]
  | _, .bitAnd a b => do
    let x ← a.yield
    let y ← b.yield
    pure [x.flatten ++ pu .bitAnd ++ y.flatten]
  | _, .bitXor a b => do
    let x ← a.yield
    let y ← b.yield
    pure [x.flatten ++ pu .bitXor ++ y.flatten]
  | _, .bitOr a b => do
    let x ← a.yield
    let y ← b.yield
    pure [x.flatten ++ pu .bitOr ++ y.flatten]
  | _, .order op a b => do
    let x ← a.yield
    let y ← b.yield
    pure [x.flatten ++ pu op.punct ++ y.flatten]
  | _, .equality op a b => do
    let x ← a.yield
    let y ← b.yield
    pure [x.flatten ++ pu op.punct ++ y.flatten]
  | _, .and a b => do
    let x ← a.yield
    let y ← b.yield
    pure [x.flatten ++ pu .and ++ y.flatten]
  | _, .or a b => do
    let x ← a.yield
    let y ← b.yield
    pure [x.flatten ++ pu .or ++ y.flatten]
  | _, .cond c a b => do
    let x ← c.yield
    let y ← a.yield
    let z ← b.yield
    pure [x.flatten ++ pu .question ++ y.flatten ++ pu .colon ++ z.flatten]
  | _, .assign op a b => do
    let x ← a.yield
    let y ← b.yield
    pure [x.flatten ++ pu op.punct ++ y.flatten]
  | _, .new t => do pure [tk .new ++ (← t.yield).flatten]
  | _, .tuple a as => do
    let x ← a.yield
    let xs ← as.yield
    pure [parens (x.flatten ++ xs.flatMap (pu .comma ++ ·))]
  | _, .inlineArray a as => do
    let x ← a.yield
    let xs ← as.yield
    pure [pu .lbrack ++ commaSep (x.flatten :: xs) ++ pu .rbrack]
  | _, .ident name => pure [idt name]
  | _, .lit l => do pure [← litP l]
  | _, .litUnit n u => pure [[.num n, .denom u]]
  | _, .elemType e _ => pure [[.elem e]]
  | _, .declVar d init => do
    let x ← d.yield
    let i ← init.yield
    pure [x.flatten ++ (match i with | [e] => pu .assign ++ e | _ => [])]
  | _, .declTuple holes d ds e => do
    let x ← d.yield
    let xs ← ds.yield
    let y ← e.yield
    pure [pu .lparen ++ (List.replicate holes (pu .comma)).flatten ++ x.flatten ++
      xs.flatMap (pu .comma ++ ·) ++ pu .rparen ++ pu .assign ++ y.flatten]
  | _, .exprStmt e => e.yield
  | _, .blockStmt b => b.yield
  | _, .simpleStmt s => do pure [(← s.yield).flatten ++ pu .semi]
  | _, .ifStmt c t e => do
    let x ← c.yield
    let y ← t.yield
    let z ← e.yield
    pure [tk .if_ ++ parens x.flatten ++ y.flatten ++
      (match z with | [s] => tk .else_ ++ s | _ => [])]
  | _, .forStmt i c u b => do
    let x ← i.yield
    let y ← c.yield
    let z ← u.yield
    let w ← b.yield
    pure [tk .for_ ++ parens (x.flatten ++ pu .semi ++ y.flatten ++ pu .semi ++ z.flatten) ++
      w.flatten]
  | _, .whileStmt c b => do
    let x ← c.yield
    let y ← b.yield
    pure [tk .while_ ++ parens x.flatten ++ y.flatten]
  | _, .doWhile b c => do
    let x ← b.yield
    let y ← c.yield
    pure [tk .do_ ++ x.flatten ++ tk .while_ ++ parens y.flatten ++ pu .semi]
  | _, .continueStmt => pure [tk .continue_ ++ pu .semi]
  | _, .breakStmt => pure [tk .break_ ++ pu .semi]
  | _, .tryStmt e rets b c cs => do
    let x ← e.yield
    let r ← rets.yield
    let y ← b.yield
    let z ← c.yield
    let zs ← cs.yield
    pure [tk .try_ ++ x.flatten ++ (if r.isEmpty then [] else tk .returns ++ parens (commaSep r)) ++
      y.flatten ++ z.flatten ++ zs.flatten]
  | _, .catchPlain b => do pure [tk .catch_ ++ (← b.yield).flatten]
  | _, .catchSig name p ps b => do
    let x ← p.yield
    let xs ← ps.yield
    let y ← b.yield
    pure [tk .catch_ ++ optToks idt name ++ parens (commaSep (x.flatten :: xs)) ++ y.flatten]
  | _, .returnStmt e => do pure [tk .return_ ++ (← e.yield).flatten ++ pu .semi]
  | _, .emit e args => do
    let x ← e.yield
    let a ← args.yield
    pure [tk .emit ++ x.flatten ++ a.flatten ++ pu .semi]
  | _, .revert e args => do
    let x ← e.yield
    let a ← args.yield
    pure [idt "revert" ++ x.flatten ++ a.flatten ++ pu .semi]
  | _, .assembly evm flags body => do
    let b ← body.yield
    pure [tk .assembly ++ (if evm then [.str (ascii "evmasm")] else []) ++
      (if flags.isEmpty then [] else parens (commaSep (flags.map fun f => [.str (ascii f)]))) ++
      braces b.flatten]
  | _, .block items => do pure [braces (← items.yield).flatten]
  | _, .stmtItem s => s.yield
  | _, .uncheckedItem b => do pure [tk .unchecked ++ (← b.yield).flatten]
  | _, .yulBlock ss => do pure [braces (← ss.yield).flatten]
  | _, .yulLet first rest e => do
    let x ← e.yield
    pure [[.yulKw .let_] ++ commaSep ((first :: rest).map idt) ++
      (match x with | [v] => pu .yulAssign ++ v | _ => [])]
  | _, .yulAssign first rest e => do
    let x ← e.yield
    let path (p : List String) : List Tok := ((p.map idt).intersperse (pu .period)).flatten
    pure [commaSep ((first :: rest).map path) ++ pu .yulAssign ++ x.flatten]
  | _, .yulExprStmt e => e.yield
  | _, .yulIf c b => do
    let x ← c.yield
    let y ← b.yield
    pure [[.yulKw .if_] ++ x.flatten ++ braces y.flatten]
  | _, .yulFor i c p b => do
    let w ← i.yield
    let x ← c.yield
    let y ← p.yield
    let z ← b.yield
    pure [[.yulKw .for_] ++ braces w.flatten ++ x.flatten ++ braces y.flatten ++ braces z.flatten]
  | _, .yulSwitch e cs d => do
    let x ← e.yield
    let y ← cs.yield
    let z ← d.yield
    pure [[.yulKw .switch] ++ x.flatten ++ y.flatten ++
      (match z with | [b] => [.yulKw .default] ++ braces b | _ => [])]
  | _, .yulCase l b => do pure [[.yulKw .case] ++ l.toks ++ braces (← b.yield).flatten]
  | _, .yulLeave => pure [[.yulKw .leave]]
  | _, .yulBreak => pure [[.yulKw .break_]]
  | _, .yulContinue => pure [[.yulKw .continue_]]
  | _, .yulFun name args rets b => do
    let x ← b.yield
    pure [[.yulKw .function] ++ idt name ++ parens (commaSep (args.map idt)) ++
      (if rets.isEmpty then [] else pu .rightArrow ++ commaSep (rets.map idt)) ++ braces x.flatten]
  | _, .yulPath h t => pure [((( h :: t).map idt).intersperse (pu .period)).flatten]
  | _, .yulCall fn args => do pure [idt fn ++ parens (commaSep (← args.yield))]
  | _, .yulLit l => pure [l.toks]

/-- A tree's tokens under a layout, consuming all of it. -/
def Syn.toks {c : Cat} (t : Syn c) (L : List Choice) : Option (List Tok) :=
  match t.yield L with
  | Option.some (items, []) => Option.some items.flatten
  | _ => Option.none

/-- **The grammar derivation**: `t` derives `ts` under some layout. -/
def Syn.Derives {c : Cat} (t : Syn c) (ts : List Tok) : Prop :=
  ∃ L, t.toks L = Option.some ts

end Solidity.Source
