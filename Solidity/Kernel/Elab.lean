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
  | ternary (c a b : RawExpr)
  deriving Repr, Inhabited

inductive RawStmt where
  | assign (l r : RawExpr)
  | decl (T : RawTy) (x : String) (init : Option RawExpr)
  | declStorage (T : RawTy) (x : String) (init : Option RawExpr)
  | declMemory (T : RawTy) (x : String) (init : Option RawExpr)
  | delete (e : RawExpr)
  | opAssign (op : BinOp) (l r : RawExpr)
  | incDec (op : IncDec) (l : RawExpr)
  /-- `f()`, `f(a)`: here `b.push()`, `b.push(a)`, `b.pop()`. -/
  | call (f : RawExpr) (args : List RawExpr)
  | assignIncDec (x : RawExpr) (op : IncDec) (l : RawExpr)
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
syntax:20 ksol_expr:21 " ? " ksol_expr:21 " : " ksol_expr:20 : ksol_expr

declare_syntax_cat ksol_stmt (behavior := both)
declare_syntax_cat ksol_block (behavior := both)
syntax "{" (ksol_stmt ";")* "}" : ksol_block
syntax ksol_expr " = " ksol_expr : ksol_stmt
syntax kernel_ty ident : ksol_stmt
syntax kernel_ty ident " = " ksol_expr : ksol_stmt
syntax kernel_ty &"storage" ident : ksol_stmt
syntax kernel_ty &"memory" ident : ksol_stmt
syntax kernel_ty &"memory" ident " = " ksol_expr : ksol_stmt
syntax kernel_ty &"storage" ident " = " ksol_expr : ksol_stmt
syntax &"delete " ksol_expr : ksol_stmt
-- `.push(`, `.push()` and `.pop()` are tokens (the `sol!` syntax's), so a
-- push on a member or an entry is spelt with them; one on a name is an
-- identifier `values.push` called.
syntax ksol_expr ".push(" ksol_expr ")" : ksol_stmt
syntax ksol_expr ".push()" : ksol_stmt
syntax ksol_expr ".pop()" : ksol_stmt
syntax ksol_expr ".transfer(" ksol_expr ")" : ksol_stmt
syntax ksol_expr "(" ")" : ksol_stmt
syntax ksol_expr "(" ksol_expr ")" : ksol_stmt
syntax ksol_expr "++" : ksol_stmt
syntax "++" ksol_expr : ksol_stmt
syntax ksol_expr " = " ksol_expr "++" : ksol_stmt
syntax ksol_expr " = " "++" ksol_expr : ksol_stmt
syntax ksol_expr " += " ksol_expr : ksol_stmt
syntax ksol_expr " -= " ksol_expr : ksol_stmt
syntax ksol_expr " *= " ksol_expr : ksol_stmt
syntax ksol_expr " /= " ksol_expr : ksol_stmt
syntax ksol_expr " %= " ksol_expr : ksol_stmt
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
  | `(ksol_expr| $c ? $a : $b) => do
      `(RawExpr.ternary $(← expandExpr c) $(← expandExpr a) $(← expandExpr b))
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
  | `(ksol_stmt| $T:kernel_ty memory $x:ident = $e) => do
      `(RawStmt.declMemory $(← expandTy T) $(quote x.getId.toString) (some $(← expandExpr e)))
  | `(ksol_stmt| $T:kernel_ty memory $x:ident) => do
      `(RawStmt.declMemory $(← expandTy T) $(quote x.getId.toString) none)
  | `(ksol_stmt| $T:kernel_ty $x:ident = $e) => do
      `(RawStmt.decl $(← expandTy T) $(quote x.getId.toString) (some $(← expandExpr e)))
  | `(ksol_stmt| $T:kernel_ty $x:ident) => do
      `(RawStmt.decl $(← expandTy T) $(quote x.getId.toString) none)
  | `(ksol_stmt| delete $e) => do `(RawStmt.delete $(← expandExpr e))
  | `(ksol_stmt| $b:ksol_expr .push( $a:ksol_expr )) => do
      `(RawStmt.call (.field $(← expandExpr b) "push") [$(← expandExpr a)])
  | `(ksol_stmt| $b:ksol_expr .push()) => do `(RawStmt.call (.field $(← expandExpr b) "push") [])
  | `(ksol_stmt| $b:ksol_expr .pop()) => do `(RawStmt.call (.field $(← expandExpr b) "pop") [])
  | `(ksol_stmt| $r:ksol_expr .transfer( $a:ksol_expr )) => do
      `(RawStmt.call (.field $(← expandExpr r) "transfer") [$(← expandExpr a)])
  | `(ksol_stmt| $f:ksol_expr ( )) => do `(RawStmt.call $(← expandExpr f) [])
  | `(ksol_stmt| $f:ksol_expr ( $a:ksol_expr )) => do
      `(RawStmt.call $(← expandExpr f) [$(← expandExpr a)])
  | `(ksol_stmt| $l:ksol_expr ++) => do `(RawStmt.incDec .postInc $(← expandExpr l))
  | `(ksol_stmt| ++ $l:ksol_expr) => do `(RawStmt.incDec .preInc $(← expandExpr l))
  | `(ksol_stmt| $x:ksol_expr = $l:ksol_expr ++) => do
      `(RawStmt.assignIncDec $(← expandExpr x) .postInc $(← expandExpr l))
  | `(ksol_stmt| $x:ksol_expr = ++ $l:ksol_expr) => do
      `(RawStmt.assignIncDec $(← expandExpr x) .preInc $(← expandExpr l))
  | `(ksol_stmt| $l:ksol_expr += $r) => do `(RawStmt.opAssign .add $(← expandExpr l) $(← expandExpr r))
  | `(ksol_stmt| $l:ksol_expr -= $r) => do `(RawStmt.opAssign .sub $(← expandExpr l) $(← expandExpr r))
  | `(ksol_stmt| $l:ksol_expr *= $r) => do `(RawStmt.opAssign .mul $(← expandExpr l) $(← expandExpr r))
  | `(ksol_stmt| $l:ksol_expr /= $r) => do `(RawStmt.opAssign .div $(← expandExpr l) $(← expandExpr r))
  | `(ksol_stmt| $l:ksol_expr %= $r) => do `(RawStmt.opAssign .mod $(← expandExpr l) $(← expandExpr r))
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

/-- A synthesised expression: a storage path, a memory path, or a value. -/
inductive TExpr (C : Contract) (Γ : Ctx) where
  | path (T : Ty) (p : SPath C Γ T)
  | mpath (T : Ty) (p : MPath C Γ T)
  | val (p : PrimTy) (v : Val C Γ p)

/-- A storage path of primitive type is read as a value. -/
def TExpr.toVal? {C : Contract} {Γ : Ctx} : TExpr C Γ → Option ((p : PrimTy) × Val C Γ p)
  | .val p v => some ⟨p, v⟩
  | .path (.prim p) (.loc l) => some ⟨p, .read l⟩
  | .mpath (.prim p) (.loc l) => some ⟨p, .readMem l⟩
  | .path _ _ | .mpath _ _ => none

def primName : PrimTy → String
  | .uint => "uint" | .int => "int" | .bool => "bool"

mutual

def synth (C : Contract) (Γ : Ctx) : RawExpr → Except String (TExpr C Γ)
  | .num n => pure (.val .uint (.simple (.lit n rfl)))
  | .bool b => pure (.val .bool (.simple (.bool b)))
  | .name x =>
    match h : lookupBy x Γ with
    | some (.stack (.prim p)) => pure (.val p (.simple (.local x h)))
    | some (.path (.ref R)) => pure (.path (.ref R) (.alias x h))
    | some (.mem (.ref R)) => pure (.mpath (.ref R) (.var x h))
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
    | .mpath (.ref (.struct s)) b =>
      match h : C.fieldType s f with
      | some T => pure (.mpath T (.loc (.field b f h)))
      | none => throw s!"struct {s} has no member {f}"
    | _ => throw s!"member access .{f} on a non-struct"
  | .index e k => do
    match ← synth C Γ e with
    | .path (.ref (.mapping (.prim kp) V)) b => pure (.path V (.loc (.index .map b (← check C Γ kp k))))
    | .path (.ref (.array E)) b => pure (.path E (.loc (.index .arr b (← check C Γ .uint k))))
    | .mpath (.ref (.array E)) b => pure (.mpath E (.loc (.index b (← check C Γ .uint k))))
    | _ => throw "indexing something that is not a mapping or an array"
  | .binop op a b => do
    -- the operand type: the first operand that is not a literal gives it
    let t ← if a matches .num _ then synth C Γ b else synth C Γ a
    let some ⟨p, _⟩ := t.toVal? | throw "an operand of reference type"
    match h : op.accepts p with
    | true => pure (.val _ (.binop op h rfl (← check C Γ p a) (← check C Γ p b)))
    | false => throw s!"operator {repr op} does not take {primName p}"
  | .ternary c a b => do
    -- the branch type: the first branch that is not a literal gives it
    let t ← if a matches .num _ then synth C Γ b else synth C Γ a
    let some ⟨p, _⟩ := t.toVal? | throw "a conditional of reference type"
    pure (.val p (.ternary (← check C Γ .bool c) (← check C Γ p a) (← check C Γ p b)))
  | .unop op a => do
    let some ⟨p, a⟩ := (← synth C Γ a).toVal? | throw "an operand of reference type"
    match h : op.accepts p with
    | true => pure (.val _ (.unop op h rfl a))
    | false => throw s!"operator {repr op} does not take {primName p}"
termination_by e => (sizeOf e, 0)

def check (C : Contract) (Γ : Ctx) (p : PrimTy) : RawExpr → Except String (Val C Γ p)
  | .num n =>
    match h : p.isNumeric with
    | true => pure (.simple (.lit n h))
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
  | .mpath .. | .val .. => throw "a value where a storage reference is expected"

/-- `e` as a memory path of type `T`. -/
def checkMPath (C : Contract) (Γ : Ctx) (T : Ty) (e : RawExpr) :
    Except String (MPath C Γ T) := do
  match ← synth C Γ e with
  | .mpath T' p => if h : T' = T then pure (h ▸ p) else throw "a memory path of another type"
  | .path .. | .val .. => throw "a memory reference is expected"

/-- `v`, if it is simple. -/
def Val.toSimple? {C : Contract} {Γ : Ctx} {p : PrimTy} : Val C Γ p → Option (Simple C Γ p)
  | .simple s => some s
  | _ => none

/-- A condition, as a simple value: a simple one as it is, any other
captured into a fresh `bool` local first (the paper's `ifElseUnfold` and
`requireConditionCapture`, done here rather than in the calculus, whose
branch and guard rules take a simple condition). -/
def elabCond (C : Contract) (Γ : Ctx) (e : RawExpr) :
    Except String ((Γ' : Ctx) × Prog C Γ Γ' × Simple C Γ' .bool) := do
  let v ← check C Γ .bool e
  match v.toSimple? with
  | some c => pure ⟨Γ, .nil, c⟩
  | none =>
    let x := freshName C Γ "se"
    pure ⟨_, .cons (.declLocal .bool x (freshName_isFresh C Γ "se") (some v)) .nil,
      .local x (SemanticsProperties.lookupBy_setBy_self ..)⟩

/-- `x` may be declared: it is neither a local nor a state variable. -/
def checkFresh (C : Contract) (Γ : Ctx) (x : Name) : Except String (PLift (isFresh C Γ x = true)) :=
  if h : isFresh C Γ x = true then pure ⟨h⟩
  else throw s!"{x} is already declared, or names a state variable"

/-- A compound assignment's target, as an `OpLoc`: a non-simple index is
captured into a fresh `ie` first, and the target read again with `ie` in
its place (`values[i + 1] += 1;` is `uint ie = i + 1; values[ie] += 1;`). -/
def elabOpTarget (C : Contract) (Γ : Ctx) (l : RawExpr) :
    Except String ((Γ' : Ctx) × Prog C Γ Γ' × (p : PrimTy) × OpLoc C Γ' p) := do
  match ← synth C Γ l with
  | .val p (.simple (.local x h)) => pure ⟨Γ, .nil, p, .local x h⟩
  | .path (.prim p) (.loc (.root r hΓ h)) => pure ⟨Γ, .nil, p, .root r hΓ h⟩
  | .path (.prim p) (.loc (.field b f h)) => pure ⟨Γ, .nil, p, .field b f h⟩
  | .path (.prim p) (.loc (@Loc.index _ _ _ k _ it b i)) =>
    match i.toSimple? with
    | some ie => pure ⟨Γ, .nil, p, .index it b ie⟩
    | none =>
      let .index e _ := l | throw "an index target that is not an index"
      let x := freshName C Γ "ie"
      let hx := freshName_isFresh C Γ "ie"
      match ← synth C (setBy x (.stack (.prim k)) Γ) (.index e (.name x)) with
      | .path (.prim p') (.loc (.index it' b' (.simple ie))) =>
        pure ⟨_, .cons (.declLocal k x hx (some i)) .nil, p', .index it' b' ie⟩
      | _ => throw "the captured index did not read back"
  | _ => throw "a compound assignment needs a local or a storage place of value type"

/-- An inc/dec target for an assignment form: as `elabOpTarget`, with a
non-simple receiver captured into a fresh `sp` first (`y = folks[i].age++;`
is `Person storage sp = folks[i]; y = sp.age++;`). -/
def elabIncTarget (C : Contract) (Γ : Ctx) (l : RawExpr) :
    Except String ((Γ' : Ctx) × Prog C Γ Γ' × (p : PrimTy) × (t : OpLoc C Γ' p) ×'
      t.recvSimple = true) := do
  let recapture (e : RawExpr) (rebuild : RawExpr → RawExpr) :
      Except String ((Γ' : Ctx) × Prog C Γ Γ' × (p : PrimTy) × (t : OpLoc C Γ' p) ×'
        t.recvSimple = true) := do
    match ← synth C Γ e with
    | .path (.ref R) b =>
      let x := freshName C Γ "sp"
      let hx := freshName_isFresh C Γ "sp"
      let ⟨Γ₂, pre, p, t⟩ ← elabOpTarget C (setBy x (.path (.ref R)) Γ) (rebuild (.name x))
      match hs : t.recvSimple with
      | true => pure ⟨Γ₂, .cons (.declStorage true R x hx b) pre, p, t, hs⟩
      | false => throw "the captured receiver did not read back"
    | .path .. | .mpath .. | .val .. => throw "a receiver that is a value"
  let ⟨Γ₁, pre, p, t⟩ ← elabOpTarget C Γ l
  match hs : t.recvSimple with
  | true => pure ⟨Γ₁, pre, p, t, hs⟩
  | false =>
    match l with
    | .field e f => recapture e (.field · f)
    | .index e k => recapture e (.index · k)
    | _ => throw "a non-simple receiver that is not a member or an entry"

/-- What a memory local is bound to: a memory path aliased, or a storage path
deep-copied. -/
def elabMRhs (C : Contract) (Γ : Ctx) (R : RefTy) (e : RawExpr) : Except String (MRhs C Γ R) := do
  match ← synth C Γ e with
  | .mpath T p => if h : T = .ref R then pure (.alias (h ▸ p)) else throw "a memory path of another type"
  | .path T p =>
    if h : T = .ref R then
      match hm : (Ty.ref R).mapFree with
      | true => pure (.copy (h ▸ p) hm)
      | false => throw "a copy into memory of a type that holds a mapping"
    else throw "a storage path of another type"
  | .val .. => throw "a value where a memory reference is expected"

/-- A block fragment, with the context after it. -/
abbrev TProg (C : Contract) (Γ : Ctx) := (Γ' : Ctx) × Prog C Γ Γ'

def TProg.one {C : Contract} {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : TProg C Γ := ⟨Γ', .cons s .nil⟩

mutual

/-- A statement, as a block: a condition may need a capture before it. -/
def elabStmt (C : Contract) (Γ : Ctx) : RawStmt → Except String (TProg C Γ)
  | .assign l r => do
    match ← synth C Γ l with
    | .val p (.simple (.local x h)) => pure (.one (.assignLocal x h (← check C Γ p r)))
    | .val .. => throw "assigning to a value"
    | .path (.prim p) (.loc l) => pure (.one (.assign l (.val (← check C Γ p r))))
    | .path (.ref R) (.loc l) =>
      match ← synth C Γ r with
      | .mpath T mp =>
        if hT : T = .ref R then pure (.one (.assignFromMem l (hT ▸ mp)))
        else throw "a memory path of another type"
      | _ =>
        match h : (Ty.ref R).mapFree with
        | true => pure (.one (.assign l (.copy (← checkPath C Γ (.ref R) r) h)))
        | false => throw "a storage copy of a type that holds a mapping"
    | .path (.ref R) (.alias x h) => pure (.one (.rebind x h (← checkPath C Γ (.ref R) r)))
    | .mpath (.ref R) (.var x h) => pure (.one (.rebindMem x h (← elabMRhs C Γ R r)))
    | .mpath (.prim p) (.loc l) => pure (.one (.assignMem l (.val (← check C Γ p r))))
    | .mpath (.ref R) (.loc l) => pure (.one (.assignMem l (.ref (← checkMPath C Γ (.ref R) r))))
  | .decl T x init => do
    let .prim p := elabTy T | throw s!"{x}: a reference type needs a data location"
    let ⟨hx⟩ ← checkFresh C Γ x
    pure (.one (.declLocal p x hx (← init.mapM (check C Γ p))))
  | .declStorage T x init => do
    let .ref R := elabTy T | throw s!"{x}: `storage` on a value type"
    let ⟨hx⟩ ← checkFresh C Γ x
    let some e := init | throw s!"{x}: an uninitialised storage pointer"
    pure (.one (.declStorage false R x hx (← checkPath C Γ (.ref R) e)))
  | .declMemory T x init => do
    let .ref R := elabTy T | throw s!"{x}: `memory` on a value type"
    let ⟨hx⟩ ← checkFresh C Γ x
    match init with
    | some e => pure (.one (.declMem R x hx (some (← elabMRhs C Γ R e)) rfl))
    | none =>
      match hd : (Ty.ref R).defaultOkS with
      | true => pure (.one (.declMem R x hx none (by simp [hd])))
      | false => throw s!"{x}: a memory object whose default is not well-formed"
  | .delete e => do
    match ← synth C Γ e with
    | .path T p =>
      match p with
      | .loc l =>
        if T matches .ref (.mapping ..) then throw "a mapping cannot be deleted"
        else pure (.one (.delete l))
      | .alias .. => throw "`delete` on a storage pointer"
    | .mpath .. => throw "`delete` in memory is not yet a kernel statement"
    | .val .. => throw "`delete` needs a storage location"
  | .opAssign op l r => do
    let ⟨Γ₁, pre, p, t⟩ ← elabOpTarget C Γ l
    match hop : op.hasCompoundAssign, hp : p.isNumeric with
    | true, true => pure ⟨Γ₁, pre.append (.cons (.opAssign op hop hp t (← check C Γ₁ p r)) .nil)⟩
    | false, _ => throw s!"no compound assignment for {repr op}"
    | _, false => throw s!"a compound assignment at {primName p}"
  | .incDec op l => do
    let ⟨Γ₁, pre, p, t⟩ ← elabOpTarget C Γ l
    match hp : p.isNumeric with
    | true => pure ⟨Γ₁, pre.append (.cons (.incDec op hp t) .nil)⟩
    | false => throw s!"++ or -- at {primName p}"
  | .assignIncDec x op l => do
    let ⟨Γ₁, pre, p, t, hs⟩ ← elabIncTarget C Γ l
    match ← synth C Γ₁ x with
    | .val q (.simple (.local y h)) =>
      match hp : p.isNumeric, decEq q p with
      | true, isTrue e => pure ⟨Γ₁, pre.append (.cons (.assignIncDec y (e ▸ h) op hp t hs) .nil)⟩
      | false, _ => throw s!"++ or -- at {primName p}"
      | _, isFalse _ => throw s!"a {primName p} assigned to a {primName q}"
    | _ => throw "the result of ++ or -- goes to a stack local"
  | .call (.field e "push") args => do
    let .path (.ref (.array E)) b ← synth C Γ e | throw "push on something that is not an array"
    match args with
    | [] =>
      match hd : E.defaultOkS with
      | true => pure (.one (.push b none (by simp [hd])))
      | false => throw "push() of an element whose default is not well-formed"
    | [a] =>
      match E with
      | .prim p => pure (.one (.push b (some (.val (← check C Γ p a))) rfl))
      | .ref R =>
        match h : (Ty.ref R).mapFree with
        | true => pure (.one (.push b (some (.copy (← checkPath C Γ (.ref R) a) h)) rfl))
        | false => throw "a push copying a type that holds a mapping"
    | _ => throw "push takes at most one argument"
  | .call (.field e "pop") [] => do
    let .path (.ref (.array _)) b ← synth C Γ e | throw "pop on something that is not an array"
    pure (.one (.pop b))
  | .call (.field e "transfer") [a] => do
    pure (.one (.transfer (← check C Γ .uint e) (← check C Γ .uint a)))
  | .call .. => throw "only push, pop and transfer are calls here"
  | .ite c thn els => do
    let ⟨Γ₁, pre, c⟩ ← elabCond C Γ c
    let s := Stmt.ite c (← elabBranch C Γ₁ thn) (← elabBranch C Γ₁ els)
    pure ⟨Γ₁, pre.append (.cons s .nil)⟩
  | .require c => do
    let ⟨Γ₁, pre, c⟩ ← elabCond C Γ c
    pure ⟨Γ₁, pre.append (.cons (.require c) .nil)⟩
  | .assert c => do
    let ⟨Γ₁, pre, c⟩ ← elabCond C Γ c
    pure ⟨Γ₁, pre.append (.cons (.assert c) .nil)⟩
  | .revert => pure (.one .revert)

/-- A block, with the context after it. -/
def elabProg (C : Contract) (Γ : Ctx) : List RawStmt → Except String (TProg C Γ)
  | [] => pure ⟨Γ, .nil⟩
  | s :: ss => do
    let ⟨Γ₁, P⟩ ← elabStmt C Γ s
    let ⟨Γ₂, Q⟩ ← elabProg C Γ₁ ss
    pure ⟨Γ₂, P.append Q⟩

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
deriving instance Lean.ToExpr for IncDec

section Quote
open Lean (mkAppN mkConst toExpr)

/-- `a = b`, by computation. -/
def quoteRefl (α a : Lean.Expr) : Lean.Expr := mkAppN (mkConst ``Eq.refl [1]) #[α, a]

def optTy : Lean.Expr := mkAppN (mkConst ``Option [0]) #[mkConst ``Ty]
def optBTy : Lean.Expr := mkAppN (mkConst ``Option [0]) #[mkConst ``BTy]
def someE (α a : Lean.Expr) : Lean.Expr := mkAppN (mkConst ``Option.some [0]) #[α, a]
def boolTrue : Lean.Expr := quoteRefl (mkConst ``Bool) (mkConst ``Bool.true)

/-- An index witness, as a term. -/
def IndexTy.quote : {R : RefTy} → {k : PrimTy} → {V : Ty} → IndexTy R k V → Lean.Expr
  | _, _, _, @IndexTy.map k V => mkAppN (mkConst ``IndexTy.map) #[toExpr k, toExpr V]
  | _, _, _, @IndexTy.arr E => mkAppN (mkConst ``IndexTy.arr) #[toExpr E]

variable (c : Lean.Expr)

def Simple.quote (Γ : Ctx) : (p : PrimTy) → Simple C Γ p → Lean.Expr
  | p, .lit n _ => mkAppN (mkConst ``Simple.lit) #[c, toExpr Γ, toExpr p, toExpr n, boolTrue]
  | _, .bool b => mkAppN (mkConst ``Simple.bool) #[c, toExpr Γ, toExpr b]
  | p, .local x _ =>
    mkAppN (mkConst ``Simple.local) #[c, toExpr Γ, toExpr p, toExpr x,
      quoteRefl optBTy (someE (mkConst ``BTy) (toExpr (BTy.stack (.prim p))))]

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
  | V, @Loc.index _ _ R k _ it b i =>
    mkAppN (mkConst ``Loc.index) #[c, toExpr Γ, toExpr R, toExpr k, toExpr V, IndexTy.quote it,
      SPath.quote Γ _ b, Val.quote Γ k i]

def MPath.quote (Γ : Ctx) : (T : Ty) → MPath C Γ T → Lean.Expr
  | .ref R, .var x _ =>
    mkAppN (mkConst ``MPath.var) #[c, toExpr Γ, toExpr R, toExpr x,
      quoteRefl optBTy (someE (mkConst ``BTy) (toExpr (BTy.mem (.ref R))))]
  | T, .loc l => mkAppN (mkConst ``MPath.loc) #[c, toExpr Γ, toExpr T, MLoc.quote Γ T l]

def MLoc.quote (Γ : Ctx) : (T : Ty) → MLoc C Γ T → Lean.Expr
  | T, @MLoc.field _ _ s _ b f _ =>
    mkAppN (mkConst ``MLoc.field) #[c, toExpr Γ, toExpr s, toExpr T,
      MPath.quote Γ _ b, toExpr f, quoteRefl optTy (someE (mkConst ``Ty) (toExpr T))]
  | E, .index b i =>
    mkAppN (mkConst ``MLoc.index) #[c, toExpr Γ, toExpr E, MPath.quote Γ _ b, Val.quote Γ .uint i]

def Val.quote (Γ : Ctx) : (p : PrimTy) → Val C Γ p → Lean.Expr
  | p, .simple s => mkAppN (mkConst ``Val.simple) #[c, toExpr Γ, toExpr p, Simple.quote c Γ p s]
  | p, .read l => mkAppN (mkConst ``Val.read) #[c, toExpr Γ, toExpr p, Loc.quote Γ _ l]
  | _, @Val.binop _ _ p q op _ _ a b =>
    mkAppN (mkConst ``Val.binop) #[c, toExpr Γ, toExpr p, toExpr q, toExpr op, boolTrue,
      quoteRefl (mkConst ``PrimTy) (toExpr q),
      Val.quote Γ p a, Val.quote Γ p b]
  | _, @Val.unop _ _ p q op _ _ a =>
    mkAppN (mkConst ``Val.unop) #[c, toExpr Γ, toExpr p, toExpr q, toExpr op, boolTrue,
      quoteRefl (mkConst ``PrimTy) (toExpr q),
      Val.quote Γ p a]
  | p, .ternary cv a b =>
    mkAppN (mkConst ``Val.ternary) #[c, toExpr Γ, toExpr p, Val.quote Γ .bool cv, Val.quote Γ p a,
      Val.quote Γ p b]
  | p, .readMem l => mkAppN (mkConst ``Val.readMem) #[c, toExpr Γ, toExpr p, MLoc.quote Γ _ l]

end

def Src.quote (Γ : Ctx) : (T : Ty) → Src C Γ T → Lean.Expr
  | _, @Src.val _ _ p v => mkAppN (mkConst ``Src.val) #[c, toExpr Γ, toExpr p, Val.quote c Γ p v]
  | _, @Src.copy _ _ R p _ =>
    mkAppN (mkConst ``Src.copy) #[c, toExpr Γ, toExpr R, SPath.quote c Γ (.ref R) p, boolTrue]

def OpLoc.quote (Γ : Ctx) : (p : PrimTy) → OpLoc C Γ p → Lean.Expr
  | p, .local x _ =>
    mkAppN (mkConst ``OpLoc.local) #[c, toExpr Γ, toExpr p, toExpr x,
      quoteRefl optBTy (someE (mkConst ``BTy) (toExpr (BTy.stack (.prim p))))]
  | p, .root r _ _ =>
    mkAppN (mkConst ``OpLoc.root) #[c, toExpr Γ, toExpr p, toExpr r,
      quoteRefl optBTy (mkAppN (mkConst ``Option.none [0]) #[mkConst ``BTy]),
      quoteRefl optTy (someE (mkConst ``Ty) (toExpr (Ty.prim p)))]
  | p, @OpLoc.field _ _ s _ b f _ =>
    mkAppN (mkConst ``OpLoc.field) #[c, toExpr Γ, toExpr s, toExpr p,
      SPath.quote c Γ _ b, toExpr f, quoteRefl optTy (someE (mkConst ``Ty) (toExpr (Ty.prim p)))]
  | p, @OpLoc.index _ _ R k _ it b i =>
    mkAppN (mkConst ``OpLoc.index) #[c, toExpr Γ, toExpr R, toExpr k, toExpr p, IndexTy.quote it,
      SPath.quote c Γ _ b, Simple.quote c Γ k i]

def MRhs.quote (Γ : Ctx) (R : RefTy) : MRhs C Γ R → Lean.Expr
  | .alias p => mkAppN (mkConst ``MRhs.alias) #[c, toExpr Γ, toExpr R, MPath.quote c Γ (.ref R) p]
  | .copy p _ => mkAppN (mkConst ``MRhs.copy) #[c, toExpr Γ, toExpr R, SPath.quote c Γ (.ref R) p, boolTrue]

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
  | Γ, _, .declLocal p x _ init =>
    let init := match init with
      | none => mkAppN (mkConst ``Option.none [0]) #[valTy c Γ p]
      | some v => someE (valTy c Γ p) (Val.quote c Γ p v)
    mkAppN (mkConst ``Stmt.declLocal) #[c, toExpr Γ, toExpr p, toExpr x, boolTrue, init]
  | Γ, _, .declStorage capture R x _ init =>
    mkAppN (mkConst ``Stmt.declStorage) #[c, toExpr Γ, toExpr capture, toExpr R, toExpr x,
      boolTrue, SPath.quote c Γ (.ref R) init]
  | Γ, _, .declMem R x _ init _ =>
    let rhsTy := mkAppN (mkConst ``MRhs) #[c, toExpr Γ, toExpr R]
    let init := match init with
      | none => mkAppN (mkConst ``Option.none [0]) #[rhsTy]
      | some r => someE rhsTy (MRhs.quote c Γ R r)
    mkAppN (mkConst ``Stmt.declMem) #[c, toExpr Γ, toExpr R, toExpr x, boolTrue, init, boolTrue]
  | Γ, _, @Stmt.rebindMem _ _ R x _ r =>
    mkAppN (mkConst ``Stmt.rebindMem) #[c, toExpr Γ, toExpr R, toExpr x,
      quoteRefl optBTy (someE (mkConst ``BTy) (toExpr (BTy.mem (.ref R)))), MRhs.quote c Γ R r]
  | Γ, _, @Stmt.assignFromMem _ _ R l p =>
    mkAppN (mkConst ``Stmt.assignFromMem) #[c, toExpr Γ, toExpr R, Loc.quote c Γ (.ref R) l,
      MPath.quote c Γ (.ref R) p]
  | Γ, _, @Stmt.assignMem _ _ T l r =>
    let r := match T, r with
      | _, @MSrc.val _ _ p v => mkAppN (mkConst ``MSrc.val) #[c, toExpr Γ, toExpr p, Val.quote c Γ p v]
      | _, @MSrc.ref _ _ R p => mkAppN (mkConst ``MSrc.ref) #[c, toExpr Γ, toExpr R, MPath.quote c Γ (.ref R) p]
    mkAppN (mkConst ``Stmt.assignMem) #[c, toExpr Γ, toExpr T, MLoc.quote c Γ T l, r]
  | Γ, _, @Stmt.opAssign _ _ p op _ _ l r =>
    mkAppN (mkConst ``Stmt.opAssign) #[c, toExpr Γ, toExpr p, toExpr op, boolTrue, boolTrue,
      OpLoc.quote c Γ p l, Val.quote c Γ p r]
  | Γ, _, @Stmt.incDec _ _ p op _ l =>
    mkAppN (mkConst ``Stmt.incDec) #[c, toExpr Γ, toExpr p, toExpr op, boolTrue, OpLoc.quote c Γ p l]
  | Γ, _, @Stmt.assignIncDec _ _ p x _ op _ l _ =>
    mkAppN (mkConst ``Stmt.assignIncDec) #[c, toExpr Γ, toExpr p, toExpr x,
      quoteRefl optBTy (someE (mkConst ``BTy) (toExpr (BTy.stack (.prim p)))), toExpr op, boolTrue,
      OpLoc.quote c Γ p l, boolTrue]
  | Γ, _, @Stmt.push _ _ E b v _ =>
    let srcTy := mkAppN (mkConst ``Src) #[c, toExpr Γ, toExpr E]
    let v := match v with
      | none => mkAppN (mkConst ``Option.none [0]) #[srcTy]
      | some r => someE srcTy (Src.quote c Γ E r)
    mkAppN (mkConst ``Stmt.push) #[c, toExpr Γ, toExpr E, SPath.quote c Γ _ b, v, boolTrue]
  | Γ, _, @Stmt.pop _ _ E b =>
    mkAppN (mkConst ``Stmt.pop) #[c, toExpr Γ, toExpr E, SPath.quote c Γ _ b]
  | Γ, _, .transfer r a =>
    mkAppN (mkConst ``Stmt.transfer) #[c, toExpr Γ, Val.quote c Γ .uint r, Val.quote c Γ .uint a]
  | Γ, _, @Stmt.delete _ _ T l =>
    mkAppN (mkConst ``Stmt.delete) #[c, toExpr Γ, toExpr T, Loc.quote c Γ T l]
  | Γ, _, .ite cond thn els =>
    mkAppN (mkConst ``Stmt.ite) #[c, toExpr Γ, Simple.quote c Γ .bool cond,
      Prog.quote Γ Γ thn, Prog.quote Γ Γ els]
  | Γ, _, .require cond =>
    mkAppN (mkConst ``Stmt.require) #[c, toExpr Γ, Simple.quote c Γ .bool cond]
  | Γ, _, .assert cond =>
    mkAppN (mkConst ``Stmt.assert) #[c, toExpr Γ, Simple.quote c Γ .bool cond]
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
bool se = x > 3;
if (se) { alice.age = 0; } else { revert(); }
delete bob.account;
folks[1] = bob;
bool se1 = flags[x] || (x == 2);
require(se1);
-/
#guard_msgs in #eval IO.println tour.show

/-- The context after `tour` is its declarations, the two captured
conditions among them, as `stmtWt` computes it: `Prog.erase_wt` on the
block, with nothing to check by hand. -/
example : blockWt [] StandardExample.layout tour.erase =
    some [("x", .stack .uint), ("p", .path (.struct "Person")), ("se", .stack .bool),
      ("se1", .stack .bool)] :=
  Prog.erase_wt tour

/-- error: Solidity elaboration failed: age is already declared, or names a state variable -/
#guard_msgs in #check ksol{ uint age = 1; }

/-- A condition that is not simple is captured into a fresh `bool` first. -/
example : (ksol{ require(alice.age > 3); }).toStr = "bool se = alice.age > 3; require(se);" := rfl

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
