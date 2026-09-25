import Solidity.Kernel.Erase
import Solidity.Kernel.Print

/-!
# Elaboration: Solidity text into kernel terms

`ksol[C]{ … }` reads Solidity statements, elaborates them against the
contract `C`, starting from the empty context, and splices the resulting
`Prog C [] Γ'` into the file as a constructor term (after mini-solkey's
`Ch01_Syntax`/`Ch02_Elab`).  `ksol{ … }` is the same against the file's
`InContract` instance.

The elaborator is an ordinary function, `elabProg`, run at compile time with
`evalExpr`.  Its result is turned back into a term by hand-written quoters,
because `deriving ToExpr` cannot handle an indexed family whose constructors
carry proofs.  The quoters point at the contract by its constant, and spell
every proof `Eq.refl`, so **the kernel re-checks each one** by computing
`lookupBy`, `C.rootType` or `C.fieldType`: nothing the elaborator computed is
trusted.  Once a term exists, only the kernel's check stands behind it.

Two rules decide how names resolve, and both are `resolveS`'s: a local
shadows a state variable of the same name, and a name that is neither is an
error.  (Function parameters are declared locals here, where mini-solkey read
an unknown name as a parameter.)  A literal takes the type the other operand,
or the target, gives it, and is a `uint` otherwise.
-/

namespace Solidity
namespace Kernel

open Semantics

/-! ## Raw syntax -/

inductive RawTy where
  | named (s : String)
  | mapping (k v : RawTy)
  | array (t : RawTy)
  deriving Repr, Inhabited

inductive RawExpr where
  | num (n : Nat)
  | name (x : String)
  | bool (b : Bool)
  | field (e : RawExpr) (f : String)
  | index (e k : RawExpr)
  | binop (op : BinOp) (a b : RawExpr)
  | unop (op : UnOp) (a : RawExpr)
  deriving Repr, Inhabited

inductive RawStmt where
  | assign (l r : RawExpr)
  | decl (T : RawTy) (x : String) (init : Option RawExpr)
  | declStorage (T : RawTy) (x : String) (init : Option RawExpr)
  | delete (e : RawExpr)
  | ite (c : RawExpr) (thn els : List RawStmt)
  | require (c : RawExpr)
  | assert (c : RawExpr)
  | revert
  deriving Repr, Inhabited

/-! ## Surface syntax -/

declare_syntax_cat ksol_expr (behavior := both)
syntax:max num : ksol_expr
syntax:max ident : ksol_expr
syntax:max ksol_expr:max "." ident : ksol_expr
syntax:max ksol_expr:max "[" ksol_expr "]" : ksol_expr
syntax:max "(" ksol_expr ")" : ksol_expr
syntax:80 "!" ksol_expr:80 : ksol_expr
syntax:80 "-" ksol_expr:80 : ksol_expr
syntax:70 ksol_expr:70 " * " ksol_expr:71 : ksol_expr
syntax:70 ksol_expr:70 " / " ksol_expr:71 : ksol_expr
syntax:70 ksol_expr:70 " % " ksol_expr:71 : ksol_expr
syntax:65 ksol_expr:65 " + " ksol_expr:66 : ksol_expr
syntax:65 ksol_expr:65 " - " ksol_expr:66 : ksol_expr
syntax:50 ksol_expr:51 " < " ksol_expr:51 : ksol_expr
syntax:50 ksol_expr:51 " > " ksol_expr:51 : ksol_expr
syntax:50 ksol_expr:51 " <= " ksol_expr:51 : ksol_expr
syntax:50 ksol_expr:51 " >= " ksol_expr:51 : ksol_expr
syntax:45 ksol_expr:46 " == " ksol_expr:46 : ksol_expr
syntax:45 ksol_expr:46 " != " ksol_expr:46 : ksol_expr
syntax:35 ksol_expr:36 " && " ksol_expr:35 : ksol_expr
syntax:30 ksol_expr:31 " || " ksol_expr:30 : ksol_expr

declare_syntax_cat ksol_stmt (behavior := both)
declare_syntax_cat ksol_block (behavior := both)
syntax "{" (ksol_stmt ";")* "}" : ksol_block
syntax ksol_expr " = " ksol_expr : ksol_stmt
syntax kernel_ty ident : ksol_stmt
syntax kernel_ty ident " = " ksol_expr : ksol_stmt
syntax kernel_ty &"storage" ident : ksol_stmt
syntax kernel_ty &"storage" ident " = " ksol_expr : ksol_stmt
syntax &"delete " ksol_expr : ksol_stmt
syntax "if " "(" ksol_expr ") " ksol_block (" else " ksol_block)? : ksol_stmt
syntax &"require" "(" ksol_expr ")" : ksol_stmt
syntax &"assert" "(" ksol_expr ")" : ksol_stmt
syntax &"revert" "(" ")" : ksol_stmt

/-- `ksol!{ s₁; s₂; … }`: the raw statements, before elaboration. -/
syntax "ksol!{" (ksol_stmt ";")* "}" : term

/-- The dot-separated parts of a name: `alice.account` is `["alice", "account"]`. -/
def nameParts : Lean.Name → List String
  | .anonymous => []
  | .str p s => nameParts p ++ [s]
  | .num p n => nameParts p ++ [toString n]

open Lean in
/-- `alice.account.age` arrives as one identifier; split it into members. -/
def expandIdent (x : Ident) : MacroM Term := do
  match nameParts x.getId with
  | [] => Macro.throwError "empty identifier"
  | ["true"] => `(RawExpr.bool true)
  | ["false"] => `(RawExpr.bool false)
  | root :: flds =>
    flds.foldlM (init := ← `(RawExpr.name $(quote root)))
      fun acc f => `(RawExpr.field $acc $(quote f))

open Lean in
partial def expandExpr : TSyntax `ksol_expr → MacroM Term
  | `(ksol_expr| $n:num) => `(RawExpr.num $n)
  | `(ksol_expr| $x:ident) => expandIdent x
  | `(ksol_expr| $e:ksol_expr . $f:ident) => do
      (nameParts f.getId).foldlM (init := ← expandExpr e)
        fun acc c => `(RawExpr.field $acc $(quote c))
  | `(ksol_expr| $e:ksol_expr [ $k:ksol_expr ]) => do
      `(RawExpr.index $(← expandExpr e) $(← expandExpr k))
  | `(ksol_expr| ( $e:ksol_expr )) => expandExpr e
  | `(ksol_expr| ! $a) => do `(RawExpr.unop .not $(← expandExpr a))
  | `(ksol_expr| - $a) => do `(RawExpr.unop .neg $(← expandExpr a))
  | `(ksol_expr| $a * $b) => bin ``BinOp.mul a b
  | `(ksol_expr| $a / $b) => bin ``BinOp.div a b
  | `(ksol_expr| $a % $b) => bin ``BinOp.mod a b
  | `(ksol_expr| $a + $b) => bin ``BinOp.add a b
  | `(ksol_expr| $a - $b) => bin ``BinOp.sub a b
  | `(ksol_expr| $a < $b) => bin ``BinOp.lt a b
  | `(ksol_expr| $a > $b) => bin ``BinOp.gt a b
  | `(ksol_expr| $a <= $b) => bin ``BinOp.le a b
  | `(ksol_expr| $a >= $b) => bin ``BinOp.ge a b
  | `(ksol_expr| $a == $b) => bin ``BinOp.eqB a b
  | `(ksol_expr| $a != $b) => bin ``BinOp.neB a b
  | `(ksol_expr| $a && $b) => bin ``BinOp.and a b
  | `(ksol_expr| $a || $b) => bin ``BinOp.or a b
  | _ => Macro.throwUnsupported
where
  bin (op : Lean.Name) (a b : TSyntax `ksol_expr) : MacroM Term := do
    `(RawExpr.binop $(mkIdent op) $(← expandExpr a) $(← expandExpr b))

open Lean in
partial def expandTy : TSyntax `kernel_ty → MacroM Term
  | `(kernel_ty| $x:ident) => `(RawTy.named $(quote x.getId.toString))
  | `(kernel_ty| mapping ( $k => $v )) => do
      `(RawTy.mapping $(← expandTy k) $(← expandTy v))
  | `(kernel_ty| $t[]) => do `(RawTy.array $(← expandTy t))
  | _ => Macro.throwUnsupported

open Lean in
partial def expandStmt : TSyntax `ksol_stmt → MacroM Term
  | `(ksol_stmt| $l:ksol_expr = $r:ksol_expr) => do
      `(RawStmt.assign $(← expandExpr l) $(← expandExpr r))
  | `(ksol_stmt| $T:kernel_ty storage $x:ident = $e) => do
      `(RawStmt.declStorage $(← expandTy T) $(quote x.getId.toString)
          (some $(← expandExpr e)))
  | `(ksol_stmt| $T:kernel_ty storage $x:ident) => do
      `(RawStmt.declStorage $(← expandTy T) $(quote x.getId.toString) none)
  | `(ksol_stmt| $T:kernel_ty $x:ident = $e) => do
      `(RawStmt.decl $(← expandTy T) $(quote x.getId.toString) (some $(← expandExpr e)))
  | `(ksol_stmt| $T:kernel_ty $x:ident) => do
      `(RawStmt.decl $(← expandTy T) $(quote x.getId.toString) none)
  | `(ksol_stmt| delete $e) => do `(RawStmt.delete $(← expandExpr e))
  | `(ksol_stmt| if ($c) $t $[else $f]?) => do
      let els ← match f with
        | some f => block f
        | none => `([])
      `(RawStmt.ite $(← expandExpr c) $(← block t) $els)
  | `(ksol_stmt| require ($c)) => do `(RawStmt.require $(← expandExpr c))
  | `(ksol_stmt| assert ($c)) => do `(RawStmt.assert $(← expandExpr c))
  | `(ksol_stmt| revert ()) => `(RawStmt.revert)
  | _ => Macro.throwUnsupported
where
  block : TSyntax `ksol_block → MacroM Term
    | `(ksol_block| { $[$ss:ksol_stmt;]* }) => do `([$(← ss.mapM expandStmt),*])
    | _ => Macro.throwUnsupported

macro_rules
  | `(ksol!{ $[$ss:ksol_stmt;]* }) => do `([$(← ss.mapM expandStmt),*])

/-! ## The elaborator

Synthesis returns a path or a value with its type; checking takes the
expected primitive type, which is how a literal gets one.  Every place two
types must agree is a `decEq`, and every proof a constructor needs comes from
a `match h : …` on the check that justifies it. -/

def elabTy : RawTy → Ty
  | .named "uint" | .named "address" => .uint
  | .named "int" => .int
  | .named "bool" => .bool
  | .named s => .struct s
  | .mapping k v => .mapping (elabTy k) (elabTy v)
  | .array t => .array (elabTy t)

/-- A synthesised expression: a storage path, or a value. -/
inductive TExpr (C : Contract) (Γ : Ctx) where
  | path (T : Ty) (p : SPath C Γ T)
  | val (p : PrimTy) (v : Val C Γ p)

/-- A storage path of primitive type is read as a value. -/
def TExpr.toVal? {C : Contract} {Γ : Ctx} : TExpr C Γ → Option ((p : PrimTy) × Val C Γ p)
  | .val p v => some ⟨p, v⟩
  | .path (.prim p) (.loc l) => some ⟨p, .read l⟩
  | .path _ _ => none

def primName : PrimTy → String
  | .uint => "uint" | .int => "int" | .bool => "bool"

mutual

def synth (C : Contract) (Γ : Ctx) : RawExpr → Except String (TExpr C Γ)
  | .num n => pure (.val .uint (.lit n rfl))
  | .bool b => pure (.val .bool (.bool b))
  | .name x =>
    match h : lookupBy x Γ with
    | some (.stack (.prim p)) => pure (.val p (.local x h))
    | some (.path (.ref R)) => pure (.path (.ref R) (.alias x h))
    | some _ => throw s!"{x} is a local this fragment cannot use"
    | none =>
      match hr : C.rootType x with
      | some T => pure (.path T (.loc (.root x h hr)))
      | none => throw s!"unknown name {x}"
  | .field e f => do
    match ← synth C Γ e with
    | .path (.ref (.struct s)) b =>
      match h : C.fieldType s f with
      | some T => pure (.path T (.loc (.field b f h)))
      | none => throw s!"struct {s} has no member {f}"
    | _ => throw s!"member access .{f} on a non-struct"
  | .index e k => do
    match ← synth C Γ e with
    | .path (.ref (.mapping (.prim kp) V)) b => pure (.path V (.loc (.mapIndex b (← check C Γ kp k))))
    | .path (.ref (.array E)) b => pure (.path E (.loc (.arrIndex b (← check C Γ .uint k))))
    | _ => throw "indexing something that is not a mapping or an array"
  | .binop op a b => do
    -- the operand type: the first operand that is not a literal gives it
    let t ← if a matches .num _ then synth C Γ b else synth C Γ a
    let some ⟨p, _⟩ := t.toVal? | throw "an operand of reference type"
    match h : op.accepts p with
    | true => pure (.val _ (.binop op h (← check C Γ p a) (← check C Γ p b)))
    | false => throw s!"operator {repr op} does not take {primName p}"
  | .unop op a => do
    let some ⟨p, a⟩ := (← synth C Γ a).toVal? | throw "an operand of reference type"
    match h : op.accepts p with
    | true => pure (.val _ (.unop op h a))
    | false => throw s!"operator {repr op} does not take {primName p}"
termination_by e => (sizeOf e, 0)

def check (C : Contract) (Γ : Ctx) (p : PrimTy) : RawExpr → Except String (Val C Γ p)
  | .num n =>
    match h : p.isNumeric with
    | true => pure (.lit n h)
    | false => throw s!"a number where a {primName p} is expected"
  | e => do
    let some ⟨q, v⟩ := (← synth C Γ e).toVal? | throw s!"a storage reference where a {primName p} is expected"
    if h : q = p then pure (h ▸ v) else throw s!"a {primName q} where a {primName p} is expected"
termination_by e => (sizeOf e, 1)

end

/-- `e` as a storage path of type `T`. -/
def checkPath (C : Contract) (Γ : Ctx) (T : Ty) (e : RawExpr) :
    Except String (SPath C Γ T) := do
  match ← synth C Γ e with
  | .path T' p => if h : T' = T then pure (h ▸ p) else throw "a storage path of another type"
  | .val .. => throw "a value where a storage reference is expected"

/-- A statement, with the context after it. -/
abbrev TStmt (C : Contract) (Γ : Ctx) := (Γ' : Ctx) × Stmt C Γ Γ'

mutual

def elabStmt (C : Contract) (Γ : Ctx) : RawStmt → Except String (TStmt C Γ)
  | .assign l r => do
    match ← synth C Γ l with
    | .val p (.local x h) => pure ⟨Γ, .assignLocal x h (← check C Γ p r)⟩
    | .val .. => throw "assigning to a value"
    | .path (.prim p) (.loc l) => pure ⟨Γ, .assign l (.val (← check C Γ p r))⟩
    | .path (.ref R) (.loc l) =>
      match h : (Ty.ref R).mapFree with
      | true => pure ⟨Γ, .assign l (.copy (← checkPath C Γ (.ref R) r) h)⟩
      | false => throw "a storage copy of a type that holds a mapping"
    | .path (.ref R) (.alias x h) => pure ⟨Γ, .rebind x h (← checkPath C Γ (.ref R) r)⟩
  | .decl T x init => do
    let .prim p := elabTy T | throw s!"{x}: a reference type needs a data location"
    pure ⟨_, .declLocal p x (← init.mapM (check C Γ p))⟩
  | .declStorage T x init => do
    let .ref R := elabTy T | throw s!"{x}: `storage` on a value type"
    match init with
    | some e => pure ⟨_, .declStorage R x (← checkPath C Γ (.ref R) e)⟩
    | none => pure ⟨_, .declStorageSkip R x⟩
  | .delete e => do
    match ← synth C Γ e with
    | .path T p =>
      match p with
      | .loc l =>
        if T matches .ref (.mapping ..) then throw "a mapping cannot be deleted"
        else pure ⟨Γ, .delete l⟩
      | .alias .. => throw "`delete` on a storage pointer"
    | .val .. => throw "`delete` needs a storage location"
  | .ite c thn els => do
    let c ← check C Γ .bool c
    pure ⟨Γ, .ite c (← elabBranch C Γ thn) (← elabBranch C Γ els)⟩
  | .require c => do pure ⟨Γ, .require (← check C Γ .bool c)⟩
  | .assert c => do pure ⟨Γ, .assert (← check C Γ .bool c)⟩
  | .revert => pure ⟨Γ, .revert⟩

/-- A block, with the context after it. -/
def elabProg (C : Contract) (Γ : Ctx) : List RawStmt → Except String ((Γ' : Ctx) × Prog C Γ Γ')
  | [] => pure ⟨Γ, .nil⟩
  | s :: ss => do
    let ⟨Γ₁, s⟩ ← elabStmt C Γ s
    let ⟨Γ₂, P⟩ ← elabProg C Γ₁ ss
    pure ⟨Γ₂, .cons s P⟩

/-- A branch leaves the context as it found it (`stmtWt`'s join). -/
def elabBranch (C : Contract) (Γ : Ctx) (ss : List RawStmt) : Except String (Prog C Γ Γ) := do
  let ⟨Γ', P⟩ ← elabProg C Γ ss
  if h : Γ' = Γ then pure (h ▸ P) else throw "a branch may not declare a variable"

end

/-! ## Quoting -/

deriving instance Lean.ToExpr for PrimTy
deriving instance Lean.ToExpr for RefTy, Ty
deriving instance Lean.ToExpr for BTy
deriving instance Lean.ToExpr for BinOp
deriving instance Lean.ToExpr for UnOp

section Quote
open Lean (mkAppN mkConst toExpr)

/-- `a = b`, by computation. -/
def quoteRefl (α a : Lean.Expr) : Lean.Expr := mkAppN (mkConst ``Eq.refl [1]) #[α, a]

def optTy : Lean.Expr := mkAppN (mkConst ``Option [0]) #[mkConst ``Ty]
def optBTy : Lean.Expr := mkAppN (mkConst ``Option [0]) #[mkConst ``BTy]
def someE (α a : Lean.Expr) : Lean.Expr := mkAppN (mkConst ``Option.some [0]) #[α, a]
def boolTrue : Lean.Expr := quoteRefl (mkConst ``Bool) (mkConst ``Bool.true)

variable (c : Lean.Expr)

mutual

def SPath.quote (Γ : Ctx) : (T : Ty) → SPath C Γ T → Lean.Expr
  | .ref R, .alias x _ =>
    mkAppN (mkConst ``SPath.alias) #[c, toExpr Γ, toExpr R, toExpr x,
      quoteRefl optBTy (someE (mkConst ``BTy) (toExpr (BTy.path (.ref R))))]
  | T, .loc l => mkAppN (mkConst ``SPath.loc) #[c, toExpr Γ, toExpr T, Loc.quote Γ T l]

def Loc.quote (Γ : Ctx) : (T : Ty) → Loc C Γ T → Lean.Expr
  | T, .root r _ _ =>
    mkAppN (mkConst ``Loc.root) #[c, toExpr Γ, toExpr T, toExpr r,
      quoteRefl optBTy (mkAppN (mkConst ``Option.none [0]) #[mkConst ``BTy]),
      quoteRefl optTy (someE (mkConst ``Ty) (toExpr T))]
  | T, @Loc.field _ _ s _ b f _ =>
    mkAppN (mkConst ``Loc.field) #[c, toExpr Γ, toExpr s, toExpr T,
      SPath.quote Γ _ b, toExpr f, quoteRefl optTy (someE (mkConst ``Ty) (toExpr T))]
  | V, @Loc.mapIndex _ _ k _ b i =>
    mkAppN (mkConst ``Loc.mapIndex) #[c, toExpr Γ, toExpr k, toExpr V,
      SPath.quote Γ _ b, Val.quote Γ k i]
  | E, .arrIndex b i =>
    mkAppN (mkConst ``Loc.arrIndex) #[c, toExpr Γ, toExpr E, SPath.quote Γ _ b,
      Val.quote Γ .uint i]

def Val.quote (Γ : Ctx) : (p : PrimTy) → Val C Γ p → Lean.Expr
  | p, .lit n _ => mkAppN (mkConst ``Val.lit) #[c, toExpr Γ, toExpr p, toExpr n, boolTrue]
  | _, .bool b => mkAppN (mkConst ``Val.bool) #[c, toExpr Γ, toExpr b]
  | p, .local x _ =>
    mkAppN (mkConst ``Val.local) #[c, toExpr Γ, toExpr p, toExpr x,
      quoteRefl optBTy (someE (mkConst ``BTy) (toExpr (BTy.stack (.prim p))))]
  | p, .read l => mkAppN (mkConst ``Val.read) #[c, toExpr Γ, toExpr p, Loc.quote Γ _ l]
  | _, @Val.binop _ _ p op _ a b =>
    mkAppN (mkConst ``Val.binop) #[c, toExpr Γ, toExpr p, toExpr op, boolTrue,
      Val.quote Γ p a, Val.quote Γ p b]
  | _, @Val.unop _ _ p op _ a =>
    mkAppN (mkConst ``Val.unop) #[c, toExpr Γ, toExpr p, toExpr op, boolTrue,
      Val.quote Γ p a]

end

def Src.quote (Γ : Ctx) : (T : Ty) → Src C Γ T → Lean.Expr
  | _, @Src.val _ _ p v => mkAppN (mkConst ``Src.val) #[c, toExpr Γ, toExpr p, Val.quote c Γ p v]
  | _, @Src.copy _ _ R p _ =>
    mkAppN (mkConst ``Src.copy) #[c, toExpr Γ, toExpr R, SPath.quote c Γ (.ref R) p, boolTrue]

def valTy (Γ : Ctx) (p : PrimTy) : Lean.Expr :=
  mkAppN (mkConst ``Val) #[c, toExpr Γ, toExpr p]

mutual

def Stmt.quote : (Γ Γ' : Ctx) → Stmt C Γ Γ' → Lean.Expr
  | Γ, _, @Stmt.assign _ _ T l r =>
    mkAppN (mkConst ``Stmt.assign) #[c, toExpr Γ, toExpr T, Loc.quote c Γ T l,
      Src.quote c Γ T r]
  | Γ, _, @Stmt.rebind _ _ R x _ r =>
    mkAppN (mkConst ``Stmt.rebind) #[c, toExpr Γ, toExpr R, toExpr x,
      quoteRefl optBTy (someE (mkConst ``BTy) (toExpr (BTy.path (.ref R)))),
      SPath.quote c Γ (.ref R) r]
  | Γ, _, @Stmt.assignLocal _ _ p x _ r =>
    mkAppN (mkConst ``Stmt.assignLocal) #[c, toExpr Γ, toExpr p, toExpr x,
      quoteRefl optBTy (someE (mkConst ``BTy) (toExpr (BTy.stack (.prim p)))),
      Val.quote c Γ p r]
  | Γ, _, .declLocal p x init =>
    let init := match init with
      | none => mkAppN (mkConst ``Option.none [0]) #[valTy c Γ p]
      | some v => someE (valTy c Γ p) (Val.quote c Γ p v)
    mkAppN (mkConst ``Stmt.declLocal) #[c, toExpr Γ, toExpr p, toExpr x, init]
  | Γ, _, .declStorage R x init =>
    mkAppN (mkConst ``Stmt.declStorage) #[c, toExpr Γ, toExpr R, toExpr x,
      SPath.quote c Γ (.ref R) init]
  | Γ, _, .declStorageSkip R x =>
    mkAppN (mkConst ``Stmt.declStorageSkip) #[c, toExpr Γ, toExpr R, toExpr x]
  | Γ, _, .bindAlias R x init =>
    mkAppN (mkConst ``Stmt.bindAlias) #[c, toExpr Γ, toExpr R, toExpr x,
      SPath.quote c Γ (.ref R) init]
  | Γ, _, @Stmt.delete _ _ T l =>
    mkAppN (mkConst ``Stmt.delete) #[c, toExpr Γ, toExpr T, Loc.quote c Γ T l]
  | Γ, _, .ite cond thn els =>
    mkAppN (mkConst ``Stmt.ite) #[c, toExpr Γ, Val.quote c Γ .bool cond,
      Prog.quote Γ Γ thn, Prog.quote Γ Γ els]
  | Γ, _, .require cond =>
    mkAppN (mkConst ``Stmt.require) #[c, toExpr Γ, Val.quote c Γ .bool cond]
  | Γ, _, .assert cond =>
    mkAppN (mkConst ``Stmt.assert) #[c, toExpr Γ, Val.quote c Γ .bool cond]
  | Γ, _, .revert => mkAppN (mkConst ``Stmt.revert) #[c, toExpr Γ]

def Prog.quote : (Γ Γ' : Ctx) → Prog C Γ Γ' → Lean.Expr
  | Γ, _, .nil => mkAppN (mkConst ``Prog.nil) #[c, toExpr Γ]
  | Γ, Γ₂, @Prog.cons _ _ Γ₁ _ s P =>
    mkAppN (mkConst ``Prog.cons) #[c, toExpr Γ, toExpr Γ₁, toExpr Γ₂,
      Stmt.quote Γ Γ₁ s, Prog.quote Γ₁ Γ₂ P]

end

/-- A block elaborated from the empty context, as a term. -/
def Prog.quoteFrom : ((Γ' : Ctx) × Prog C [] Γ') → Lean.Expr
  | ⟨Γ', P⟩ => Prog.quote c [] Γ' P

end Quote

/-! ## `ksol[C]{ … }` -/

/-- `ksol[C]{ s₁; s₂; … }`: the statements, elaborated against the named
contract `C` from the empty context, as a `Prog C [] Γ'`. -/
syntax "ksol[" term "]{" (ksol_stmt ";")* "}" : term

/-- `ksol{ … }`: `ksol[C]{ … }` for the file's `InContract` contract. -/
syntax "ksol{" (ksol_stmt ";")* "}" : term

open Lean Elab Term Meta in
/-- Run `f C` at compile time for the contract the term `c` names, and splice
the term it computes; an elaboration error is reported at the source.  `c` is
unfolded through instances only, so it may be `InContract.contract` but must
end at a named contract. -/
def elabAgainst (c : Lean.Term) (f : Lean.Term → TermElabM Lean.Term) : TermElabM Lean.Expr := do
  let C ← withTransparency .instances <| whnf (← elabTermAndSynthesize c (mkConst ``Contract))
  let some n := C.constName? | throwError "not a named contract: {C}"
  let t ← f (← `(Lean.mkConst $(quote n)))
  let ty := mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String) (mkConst ``Lean.Expr)
  let e ← elabTermEnsuringType t ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  match ← unsafe evalExpr (Except String Lean.Expr) ty e with
  | .ok r => pure r
  | .error msg => throwError "Solidity elaboration failed: {msg}"

open Lean Elab Term Meta in
elab_rules : term
  | `(ksol[ $c ]{ $[$ss:ksol_stmt;]* }) => do
    let raw ← `(ksol!{ $[$ss;]* })
    elabAgainst c fun q =>
      `((elabProg $c [] $raw).map (Prog.quoteFrom $q))

macro_rules
  | `(ksol{ $[$ss;]* }) => `(ksol[InContract.contract]{ $[$ss;]* })

/-! ## Examples -/

section Examples

local instance : InContract := ⟨StandardExample⟩

/-- A block over `StandardExample`: a local, an alias, writes through both, a
mapping entry, a branch, a delete, a struct copy into a mapping, a guard. -/
def tour := ksol{
  uint x = alice.age + 1;
  Person storage p = alice;
  p.age = x;
  balances[x] = 10;
  if (x > 3) { alice.age = 0; } else { revert(); };
  delete bob.account;
  folks[1] = bob;
  require(flags[x] || x == 2);
}

/--
info: uint x = alice.age + 1;
Person storage p = alice;
p.age = x;
balances[x] = 10;
if (x > 3) { alice.age = 0; } else { revert(); }
delete bob.account;
folks[1] = bob;
require(flags[x] || (x == 2));
-/
#guard_msgs in #eval IO.println tour.show

/-- The context after `tour` is its two declarations, as `stmtWt` computes
it: `Stmt.erase_wt` on the block, with nothing to check by hand. -/
example : blockWt [] StandardExample.layout tour.erase =
    some [("x", .stack .uint), ("p", .path (.struct "Person"))] :=
  Prog.erase_wt tour

/-- A local shadows the state variable of its name, as `resolveS` does:
after `uint age = 1;`, `age` is the local, not the root. -/
example : (ksol{ uint age = 1; age = 2; }).toStr = "uint age = 1; age = 2;" := rfl

/-- error: Solidity elaboration failed: a storage reference where a uint is expected -/
#guard_msgs in #check ksol{ uint y = alice; }

/-- error: Solidity elaboration failed: `delete` on a storage pointer -/
#guard_msgs in #check ksol{ Person storage q = alice; delete q; }

/-- error: Solidity elaboration failed: struct Person has no member balance -/
#guard_msgs in #check ksol{ alice.balance = 1; }

/-- error: Solidity elaboration failed: a branch may not declare a variable -/
#guard_msgs in #check ksol{ if (true) { uint t = 1; } else { }; }

/-- error: Solidity elaboration failed: a storage copy of a type that holds a mapping -/
#guard_msgs in #check ksol{ wallet = wallet; }

/-- An alias assigned a path is rebound, not written through. -/
example : (ksol{ Person storage p = alice; p = bob; }).toStr =
    "Person storage p = alice; p = bob;" := rfl

end Examples

end Kernel
end Solidity
