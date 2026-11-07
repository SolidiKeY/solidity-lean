import Solidity.SolcValidation.IrSyntax
import Solidity.SolcValidation.DataResolution
import Solidity.Yul.Words

/-!
# Execution of solc's object dialect over an EVM machine interface

A fuelled interpreter for the intrinsic IR tree of `SolcValidation/IrSyntax.lean`.
Pure builtins use the owner's `Solidity.Yul.Pure.eval` directly. Every other
EVM builtin goes to a `Machine σ` supplied by the consumer (the world or
byte-memory model), so this module fixes the dialect's control and object
semantics without choosing a memory or world representation. It is a separate
interpreter over the C06 tree, not an adapter of `Yul/ClosedRun.lean`: no
theorem relates the two yet (open work), and gas, memory expansion, returndata,
calls and creation are entirely the machine's.

The object operations are interpreted as solc's assembler resolves them:
`datasize`/`dataoffset` through a checked `DataTable` of the assembled artifact
(`SolcValidation/DataLayout.lean`), `datacopy` as `codecopy`, `setimmutable` as
one `mstore` per recorded position of the immutable in the runtime code,
`loadimmutable` and `linkersymbol` through the deploy-time tables, and
`memoryguard(n)` as `n` (the value of the program as emitted; solc's
StackLimitEvader, an optimizer transformation, rewrites the literal before
assembly and is outside this semantics). A missing label is `stuck` (solc refuses it at
assembly), never a default value.

Arguments are evaluated right to left, as in Yul. Values are intrinsic
(`Vals L` has exactly one word per name in scope).
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

/-! ## Values -/

/-- One word per local in scope, innermost first. -/
inductive Vals : List String → Type where
  | nil : Vals []
  | cons {x : String} {L : List String} : Word → Vals L → Vals (x :: L)

namespace Vals

def get : {L : List String} → {x : String} → Vals L → Mem L x → Word
  | _, _, .cons v _, .here => v
  | _, _, .cons _ vs, .there m => vs.get m

def set : {L : List String} → {x : String} → Vals L → Mem L x → Word → Vals L
  | _, _, .cons _ vs, .here, w => .cons w vs
  | _, _, .cons v vs, .there m, w => .cons v (vs.set m w)

def append : {xs L : List String} → Vals xs → Vals L → Vals (xs ++ L)
  | _, _, .nil, back => back
  | _, _, .cons v vs, back => .cons v (append vs back)

def drop : (xs : List String) → {L : List String} → Vals (xs ++ L) → Vals L
  | [], _, vs => vs
  | _ :: xs, _, .cons _ vs => drop xs vs

def take : (xs : List String) → {L : List String} → Vals (xs ++ L) → Vals xs
  | [], _, _ => .nil
  | _ :: xs, _, .cons v vs => .cons v (take xs vs)

def ofFn : (xs : List String) → (Fin xs.length → Word) → Vals xs
  | [], _ => .nil
  | _ :: xs, f => .cons (f ⟨0, Nat.zero_lt_succ _⟩) (ofFn xs fun i => f i.succ)

def toFn : {L : List String} → Vals L → Fin L.length → Word
  | _, .cons v _, ⟨0, _⟩ => v
  | _, .cons _ vs, ⟨i + 1, h⟩ => vs.toFn ⟨i, Nat.lt_of_succ_lt_succ h⟩

def zeros (xs : List String) : Vals xs := ofFn xs fun _ => 0

end Vals

/-! ## Function environments -/

/-- The runtime function environment mirrors the lexical stack of groups. -/
inductive FunEnv : List FnSig → Type where
  | nil : FunEnv []
  | group {F : List FnSig} (ss : List FnSig) : Bodies (ss ++ F) ss → FunEnv F → FunEnv (ss ++ F)

/-- A function's body together with the environment it was defined in. -/
structure Closure (s : FnSig) where
  scope : List FnSig
  env : FunEnv scope
  body : Block scope ⟨true, false⟩ (s.params ++ s.rets)

def Mem.split {α : Type} {F : List α} {a : α} : (ss : List α) → Mem (ss ++ F) a → Mem ss a ⊕ Mem F a
  | [], m => .inr m
  | _ :: _, .here => .inl .here
  | _ :: ss, .there m => (Mem.split ss m).elim (fun m => .inl (.there m)) .inr

def Bodies.get {G : List FnSig} : {ss : List FnSig} → {s : FnSig} → Bodies G ss → Mem ss s →
    Block G ⟨true, false⟩ (s.params ++ s.rets)
  | _, _, .cons body _, .here => body
  | _, _, .cons _ rest, .there m => rest.get m

/-- A group's functions run in the group's own environment (recursion included). -/
def FunEnv.lookup {s : FnSig} : {F : List FnSig} → FunEnv F → Mem F s → Closure s
  | _, .group ss bodies outer, m =>
      match Mem.split ss m with
      | .inl here => ⟨_, .group ss bodies outer, bodies.get here⟩
      | .inr there => outer.lookup there

/-! ## Machine and object context -/

/-- Why the machine stopped. Return data, if any, is in the machine state. -/
inductive HaltKind where
  | stop | «return» | revert | invalid
  /-- Any other exceptional halt of the consumer's machine (out of gas, …). -/
  | exceptional (why : String)
  deriving DecidableEq, Repr

/-- What a machine may report besides a result: it halted, or the builtin is
outside the consumer's model. It cannot report the interpreter's `fuel`. -/
inductive MachineFault (σ : Type) where
  | halt (state : σ) (kind : HaltKind)
  | unsupported (why : String)

inductive Fault (σ : Type) where
  /-- The machine stopped (stop, return, revert, invalid, …) in this state. -/
  | halt (state : σ) (kind : HaltKind)
  /-- A static error (missing object label, immutable or linker symbol) or a
  builtin outside the machine's model. -/
  | stuck (reason : String)
  /-- The interpreter's fuel horizon is exhausted; not a program failure. -/
  | fuel

abbrev Run (σ α : Type) := Except (Fault σ) α

def MachineFault.lift {σ : Type} : MachineFault σ → Fault σ
  | .halt s k => .halt s k
  | .unsupported why => .stuck why

/-- Effects of the non-pure EVM builtins, supplied by the consumer's model. -/
structure Machine (σ : Type) where
  exec : {a r : Nat} → Solidity.Yul.Builtin a r → (Fin a → Word) → σ →
    Except (MachineFault σ) (σ × (Fin r → Word))

/-- A machine step inside the interpreter. -/
def Machine.run {σ : Type} (M : Machine σ) {a r : Nat} (b : Solidity.Yul.Builtin a r)
    (xs : Fin a → Word) (s : σ) : Run σ (σ × (Fin r → Word)) :=
  (M.exec b xs s).mapError MachineFault.lift

/-- Assembled-object facts that the object operations read. -/
structure ObjectCtx where
  artifact : List DataByte
  table : DataTable artifact
  /-- Byte positions of each immutable in the runtime code (creation side). -/
  immutablePositions : String → List Nat
  /-- Deployed immutable values (runtime side). -/
  immutables : String → Option Word
  /-- Linked library addresses. -/
  links : String → Option Word

inductive Flow where
  | normal | leave | break_ | continue_
  deriving DecidableEq, Repr

/-- Prepend a word to a word vector. -/
def consFn {k : Nat} (w : Word) (ws : Fin k → Word) : Fin (k + 1) → Word
  | ⟨0, _⟩ => w
  | ⟨i + 1, h⟩ => ws ⟨i, Nat.lt_of_succ_lt_succ h⟩


def mstoreAll {σ : Type} (M : Machine σ) (value : Word) : List Word → σ → Run σ σ
  | [], s => .ok s
  | p :: ps, s => do
      let (s, _) ← M.run .«mstore» (consFn p (consFn value Fin.elim0)) s
      mstoreAll M value ps s

def evalObjectOp {σ : Type} (M : Machine σ) (ctx : ObjectCtx) :
    {a r : Nat} → ObjectOp a r → (Fin a → Word) → σ → Run σ (σ × (Fin r → Word))
  | _, _, .datasize l, _, s =>
      match ctx.table.select l with
      | some sel => .ok (s, fun _ => sel.ref.datasize)
      | none => .error (.stuck s!"datasize: no object {l}")
  | _, _, .dataoffset l, _, s =>
      match ctx.table.select l with
      | some sel => .ok (s, fun _ => sel.ref.dataoffset)
      | none => .error (.stuck s!"dataoffset: no object {l}")
  | _, _, .datacopy, xs, s => M.run .«codecopy» xs s
  | _, _, .setimmutable l, xs, s => do
      let offset := xs 0
      let positions := (ctx.immutablePositions l).map fun p => Solidity.Yul.word (offset.val + p)
      let s ← mstoreAll M (xs 1) positions s
      pure (s, Fin.elim0)
  | _, _, .loadimmutable l, _, s =>
      match ctx.immutables l with
      | some v => .ok (s, fun _ => v)
      | none => .error (.stuck s!"loadimmutable: no immutable {l}")
  | _, _, .linkersymbol l, _, s =>
      match ctx.links l with
      | some v => .ok (s, fun _ => v)
      | none => .error (.stuck s!"linkersymbol: unlinked {l}")
  | _, _, .memoryguard n, _, s => .ok (s, fun _ => n)

def evalOp {σ : Type} (M : Machine σ) (ctx : ObjectCtx) :
    {a r : Nat} → Op a r → (Fin a → Word) → σ → Run σ (σ × (Fin r → Word))
  | _, _, .evm (.pure p), xs, s => .ok (s, fun _ => Solidity.Yul.Pure.eval p xs)
  | _, _, .evm b, xs, s => M.run b xs s
  | _, _, .object o, xs, s => evalObjectOp M ctx o xs s

/-! ## The interpreter -/

/-- The first case whose label equals the selector. -/
def Cases.select {F c L} : Cases F c L → Word → Option (Block F c L)
  | .nil, _ => none
  | .cons l b rest, v => if l.value = v then some b else rest.select v

def assignAll {L : List String} : (ts : List (Var L)) → (Fin ts.length → Word) → Vals L → Vals L
  | [], _, vs => vs
  | t :: ts, ws, vs => assignAll ts (fun i => ws i.succ) (vs.set t.2 (ws ⟨0, Nat.zero_lt_succ _⟩))

section
variable {σ : Type} (M : Machine σ) (ctx : ObjectCtx)

mutual
def evalExpr : Nat → {F : List FnSig} → {L : List String} → {r : Nat} →
    FunEnv F → Expr F L r → Vals L → σ → Run σ (σ × (Fin r → Word))
  | 0, _, _, _, _, _, _, _ => .error .fuel
  | _ + 1, _, _, _, _, .lit l, _, s => .ok (s, fun _ => l.value)
  | _ + 1, _, _, _, _, .var _ m, vs, s => .ok (s, fun _ => vs.get m)
  | k + 1, _, _, _, env, .op o args, vs, s => do
      let (s, xs) ← evalArgs k env args vs s
      evalOp M ctx o xs s
  | k + 1, _, _, _, env, .call m args, vs, s => do
      let (s, xs) ← evalArgs k env args vs s
      let closure := env.lookup m
      let (s, out, _) ← evalBlock k closure.env closure.body
        (Vals.append (Vals.ofFn _ xs) (Vals.zeros _)) s
      pure (s, (Vals.drop _ out).toFn)

/-- Right-to-left argument evaluation. -/
def evalArgs : Nat → {F : List FnSig} → {L : List String} → {k : Nat} →
    FunEnv F → Args F L k → Vals L → σ → Run σ (σ × (Fin k → Word))
  | 0, _, _, _, _, _, _, _ => .error .fuel
  | _ + 1, _, _, _, _, .nil, _, s => .ok (s, Fin.elim0)
  | k + 1, _, _, _, env, .cons e rest, vs, s => do
      let (s, tail) ← evalArgs k env rest vs s
      let (s, head) ← evalExpr k env e vs s
      pure (s, consFn (head 0) tail)

def evalStmt : Nat → {F : List FnSig} → {c : Ctl} → {L : List String} →
    FunEnv F → Stmt F c L → Vals L → σ → Run σ (σ × Vals L × Flow)
  | 0, _, _, _, _, _, _, _ => .error .fuel
  | k + 1, _, _, _, env, .block b, vs, s => evalBlock k env b vs s
  | k + 1, _, _, _, env, .discard e, vs, s => do
      let (s, _) ← evalExpr k env e vs s
      pure (s, vs, .normal)
  | k + 1, _, _, _, env, .assign ts e, vs, s => do
      let (s, ws) ← evalExpr k env e vs s
      pure (s, assignAll ts ws vs, .normal)
  | k + 1, _, _, _, env, .if_ e b, vs, s => do
      let (s, v) ← evalExpr k env e vs s
      if v 0 = 0 then pure (s, vs, .normal) else evalBlock k env b vs s
  | k + 1, _, _, _, env, .switch e cs, vs, s => do
      let (s, v) ← evalExpr k env e vs s
      match cs.select (v 0) with
      | some b => evalBlock k env b vs s
      | none => pure (s, vs, .normal)
  | k + 1, _, _, _, env, .switchDefault e cs d, vs, s => do
      let (s, v) ← evalExpr k env e vs s
      evalBlock k env ((cs.select (v 0)).getD d) vs s
  | k + 1, _, _, _, env, .for_ lp, vs, s => evalLoop k env lp vs s
  | _ + 1, _, _, _, _, .leave, vs, s => .ok (s, vs, .leave)
  | _ + 1, _, _, _, _, .break_, vs, s => .ok (s, vs, .break_)
  | _ + 1, _, _, _, _, .continue_, vs, s => .ok (s, vs, .continue_)

/-- Initialization items, then the loop proper. -/
def evalLoop : Nat → {F : List FnSig} → {c : Ctl} → {L : List String} →
    FunEnv F → Loop F c L → Vals L → σ → Run σ (σ × Vals L × Flow)
  | 0, _, _, _, _, _, _, _ => .error .fuel
  | k + 1, _, _, _, env, .stmt st rest, vs, s => do
      let (s, vs, flow) ← evalStmt k env st vs s
      if flow = .normal then evalLoop k env rest vs s else pure (s, vs, flow)
  | k + 1, _, _, _, env, .let_ xs init rest, vs, s => do
      let (s, fresh) ← evalInit k env xs init vs s
      let (s, out, flow) ← evalLoop k env rest (Vals.append fresh vs) s
      pure (s, Vals.drop xs out, flow)
  | k + 1, _, _, _, env, .run cond post body, vs, s => iterate k env cond post body vs s

/-- One loop turn per unit of fuel: condition, body, post. -/
def iterate : Nat → {F : List FnSig} → {c : Ctl} → {L : List String} →
    FunEnv F → Expr F L 1 → Block F ⟨c.function, false⟩ L → Block F ⟨c.function, true⟩ L →
    Vals L → σ → Run σ (σ × Vals L × Flow)
  | 0, _, _, _, _, _, _, _, _, _ => .error .fuel
  | k + 1, _, _, _, env, cond, post, body, vs, s => do
      let (s, v) ← evalExpr k env cond vs s
      if v 0 = 0 then pure (s, vs, .normal) else
      let (s, vs, flow) ← evalBlock k env body vs s
      match flow with
      | .break_ => pure (s, vs, .normal)
      | .leave => pure (s, vs, .leave)
      | .normal | .continue_ => do
          let (s, vs, flow) ← evalBlock k env post vs s
          if flow = .leave then pure (s, vs, .leave)
          else iterate k env cond post body vs s

def evalInit : Nat → {F : List FnSig} → {L : List String} → FunEnv F → (xs : List String) →
    Option (Expr F L xs.length) → Vals L → σ → Run σ (σ × Vals xs)
  | 0, _, _, _, _, _, _, _ => .error .fuel
  | _ + 1, _, _, _, xs, none, _, s => .ok (s, Vals.zeros xs)
  | k + 1, _, _, env, xs, some e, vs, s => do
      let (s, ws) ← evalExpr k env e vs s
      pure (s, Vals.ofFn xs ws)

def evalItems : Nat → {F : List FnSig} → {c : Ctl} → {L : List String} → {g : Nat} →
    FunEnv F → Items F c L g → Vals L → σ → Run σ (σ × Vals L × Flow)
  | 0, _, _, _, _, _, _, _, _ => .error .fuel
  | _ + 1, _, _, _, _, _, .nil, vs, s => .ok (s, vs, .normal)
  | k + 1, _, _, _, _, env, .stmt st rest, vs, s => do
      let (s, vs, flow) ← evalStmt k env st vs s
      if flow = .normal then evalItems k env rest vs s else pure (s, vs, flow)
  | k + 1, _, _, _, _, env, .let_ xs init rest, vs, s => do
      let (s, fresh) ← evalInit k env xs init vs s
      let (s, out, flow) ← evalItems k env rest (Vals.append fresh vs) s
      pure (s, Vals.drop xs out, flow)
  | k + 1, _, _, _, _, env, .fn _ rest, vs, s => evalItems k env rest vs s

/-- A block installs its function group, then runs its items; block-local
variables are dropped by `evalItems`. -/
def evalBlock : Nat → {F : List FnSig} → {c : Ctl} → {L : List String} →
    FunEnv F → Block F c L → Vals L → σ → Run σ (σ × Vals L × Flow)
  | 0, _, _, _, _, _, _, _ => .error .fuel
  | k + 1, _, _, _, env, .mk ss bodies items, vs, s => evalItems k (.group ss bodies env) items vs s
end

/-- Run an object's code from the empty environment. -/
def runCode (fuel : Nat) (code : Code) (s : σ) : Run σ σ :=
  (fun (r : σ × Vals [] × Flow) => r.1) <$> evalBlock M ctx fuel .nil code .nil s

end

/-! ## Adapter laws -/
namespace IrEvalLaws
variable {σ : Type} (M : Machine σ) (ctx : ObjectCtx)

/-- A zero-argument operation evaluates exactly as the operation itself. -/
theorem evalExpr_op_nil (k : Nat) {F L r} (env : FunEnv F) (o : Op 0 r) (vs : Vals L) (s : σ) :
    evalExpr M ctx (k + 2) env (Expr.op o Args.nil) vs s = evalOp M ctx o Fin.elim0 s := by
  simp only [evalExpr, evalArgs, bind, Except.bind]

/-- `datasize` of a label in the checked table is that reference's exact byte length. -/
theorem datasize_exact (k : Nat) {F L} (env : FunEnv F) (vs : Vals L) (s : σ) (l : String)
    (sel : DataSelection ctx.table.entries l) :
    evalExpr M ctx (k + 2) env (.op (.object (.datasize l)) .nil) vs s =
      .ok (s, fun _ => sel.ref.datasize) := by
  rw [evalExpr_op_nil]
  simp only [evalOp, evalObjectOp, DataTable.select_complete ctx.table sel]

/-- `dataoffset` of a label in the checked table is that reference's assembled position. -/
theorem dataoffset_exact (k : Nat) {F L} (env : FunEnv F) (vs : Vals L) (s : σ) (l : String)
    (sel : DataSelection ctx.table.entries l) :
    evalExpr M ctx (k + 2) env (.op (.object (.dataoffset l)) .nil) vs s =
      .ok (s, fun _ => sel.ref.offset) := by
  rw [evalExpr_op_nil]
  simp only [evalOp, evalObjectOp, DataTable.select_complete ctx.table sel, DataRef.dataoffset]

/-- A label absent from the table is a static error, never a default size. -/
theorem datasize_missing (k : Nat) {F L} (env : FunEnv F) (vs : Vals L) (s : σ) (l : String)
    (absent : ∀ ref, (l, ref) ∉ ctx.table.entries) :
    evalExpr M ctx (k + 2) env (.op (.object (.datasize l)) .nil) vs s =
      .error (.stuck s!"datasize: no object {l}") := by
  rw [evalExpr_op_nil]
  have none : ctx.table.select l = none := by
    cases h : ctx.table.select l with
    | none => rfl
    | some sel => exact absurd sel.member (absent sel.ref)
  simp only [evalOp, evalObjectOp, none]

/-- `memoryguard(n)` is `n`, with no effect. -/
theorem memoryguard_value (k : Nat) {F L} (env : FunEnv F) (vs : Vals L) (s : σ) (n : Word) :
    evalExpr M ctx (k + 2) env (.op (.object (.memoryguard n)) .nil) vs s = .ok (s, fun _ => n) := by
  rw [evalExpr_op_nil]
  rfl

/-- `loadimmutable` reads the deployed value of that immutable. -/
theorem loadimmutable_value (k : Nat) {F L} (env : FunEnv F) (vs : Vals L) (s : σ) (l : String)
    (v : Word) (h : ctx.immutables l = some v) :
    evalExpr M ctx (k + 2) env (.op (.object (.loadimmutable l)) .nil) vs s = .ok (s, fun _ => v) := by
  rw [evalExpr_op_nil]
  simp only [evalOp, evalObjectOp, h]

/-- `linkersymbol` reads the linked address. -/
theorem linkersymbol_value (k : Nat) {F L} (env : FunEnv F) (vs : Vals L) (s : σ) (l : String)
    (v : Word) (h : ctx.links l = some v) :
    evalExpr M ctx (k + 2) env (.op (.object (.linkersymbol l)) .nil) vs s = .ok (s, fun _ => v) := by
  rw [evalExpr_op_nil]
  simp only [evalOp, evalObjectOp, h]

/-- `datacopy` and `codecopy` evaluate identically on the same arguments. -/
theorem datacopy_codecopy (n : Nat) {F L} (env : FunEnv F) (args : Args F L 3) (vs : Vals L) (s : σ) :
    evalExpr M ctx n env (.op (.object .datacopy) args) vs s =
      evalExpr M ctx n env (.op (.evm .«codecopy») args) vs s := by
  cases n with
  | zero => rfl
  | succ k => simp only [evalExpr, evalOp, evalObjectOp]

/-- Pure builtins use the owner's word semantics on the evaluated arguments,
with no effect beyond evaluating those arguments. -/
theorem pure_value (k : Nat) {F L a} (env : FunEnv F) (p : Solidity.Yul.Pure a) (args : Args F L a)
    (vs : Vals L) (s s' : σ) (xs : Fin a → Word) (h : evalArgs M ctx k env args vs s = .ok (s', xs)) :
    evalExpr M ctx (k + 1) env (.op (.evm (.pure p)) args) vs s =
      .ok (s', fun _ => Solidity.Yul.Pure.eval p xs) := by
  simp only [evalExpr, h, bind, Except.bind, evalOp]

/-- `setimmutable(offset, name, value)` is one `mstore` of `value` per recorded
position of the immutable, relative to `offset`, in order. -/
theorem setimmutable_stores (k : Nat) {F L} (env : FunEnv F) (l : String) (args : Args F L 2)
    (vs : Vals L) (s s' : σ) (xs : Fin 2 → Word) (h : evalArgs M ctx k env args vs s = .ok (s', xs)) :
    evalExpr M ctx (k + 1) env (.op (.object (.setimmutable l)) args) vs s =
      (fun s'' => (s'', (Fin.elim0 : Fin 0 → Word))) <$>
        mstoreAll M (xs 1) ((ctx.immutablePositions l).map fun p => Solidity.Yul.word ((xs 0).val + p)) s' := by
  simp only [evalExpr, h, bind, Except.bind, evalOp, evalObjectOp]
  cases mstoreAll M (xs 1) ((ctx.immutablePositions l).map fun p => Solidity.Yul.word ((xs 0).val + p)) s' <;> rfl

end IrEvalLaws

end Solidity.SolcValidation.IrSyntax
