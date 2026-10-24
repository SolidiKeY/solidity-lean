import Solidity.Calculus.Lower
import Solidity.Calculus.SyntaxSize

/-!
# A call's summary (`internalCallSummary`, Lean only)

A callee whose body only computes values (`T v = e;`, `v = e;`, a block,
a call of the same kind assigned to a value local) runs as one update: its
return variable's value, a term over its parameters (KeY's contract-based
`methodCall` with the contract derived, not written).  The body is executed
symbolically once, in its own frame (`Prog.sym`): every value local holds a
term over the frame's locals, and a call in it is the callee's summary,
instantiated at its arguments.  A call site then assigns the summary,
instantiated at its arguments, to its target (`CallRet.summary?`), one
update where the body was inlined, so nested calls are executed once per
function and not once per call path (`docs/automation.md`, M6).

**Failure.**  A term is read lazily nowhere but under `?:`, `&&`, `||`; a
term that may revert (an overflow, a failed read) is owed: the local that
holds it is *pending* (its flag) until a term that reads it where it is
always read (`Tm.strictReads`) takes it over, and a pending local is never
overwritten or popped.  So, at the end of the body, every way it can revert
is a way its return value's term reverts, and the update `{y := t}` fails
exactly where the call reverts.  A body that would drop a pending value
(`uint t = x + 1;` never read) has no summary, and the call is inlined
(`internalCallExpand`).

**What has a summary**: a call `y = f(a₁, …);` of one value return, its
arguments simple (`functionCallArgCapture` first), its body built of value
declarations, value assignments whose right-hand sides read value locals
and the storage (no alias, no memory local), blocks and such calls; an
`if`, a `require`, a loop, a write to the state, an external call has none.

The functions on the context-indexed families are written by their
recursors (Gate G0), each with its `match` form as the compiled twin.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3)

variable {C : Contract}

/-! ## The symbolic frame -/

/-- What the summary holds for a local of type `t`, over the locals `Γ₀` it
started from: a value local's term and whether its definedness is owed (it
is *pending*); nothing for any other local (no summary reads one). -/
def LTy.STm (C : Contract) (Γ₀ : Ctx) : LTy → Type
  | .val p => Tm C Γ₀ (.val p) × Bool
  | _ => Unit

/-- A symbolic frame: a `LTy.STm` for every local of `Δ`, computed from the
context as `TEnv` is. -/
def SEnv (C : Contract) (Γ₀ : Ctx) : Ctx → Type
  | [] => Unit
  | t :: Δ => LTy.STm C Γ₀ t × SEnv C Γ₀ Δ

namespace SEnv

variable {Γ₀ : Ctx}

/-- The local at a position. -/
def get : {Δ : Ctx} → {t : LTy} → Idx Δ t → SEnv C Γ₀ Δ → LTy.STm C Γ₀ t
  | _, _, i => Idx.casesOn (motive := fun Δ t _ => SEnv C Γ₀ Δ → LTy.STm C Γ₀ t) i
      (fun e => e.1) (fun i e => SEnv.get i e.2)
  termination_by structural _ _ i => i

/-- The local at a position, set. -/
def set : {Δ : Ctx} → {t : LTy} → Idx Δ t → LTy.STm C Γ₀ t → SEnv C Γ₀ Δ → SEnv C Γ₀ Δ
  | _, _, i => Idx.casesOn
      (motive := fun Δ t _ => LTy.STm C Γ₀ t → SEnv C Γ₀ Δ → SEnv C Γ₀ Δ) i
      (fun w e => (w, e.2)) (fun i w e => (e.1, SEnv.set i w e.2))
  termination_by structural _ _ i => i

/-- A local's owed definedness discharged where `c` holds. -/
def _root_.Solidity.LTy.sclear (c : Bool) : (t : LTy) → LTy.STm C Γ₀ t → LTy.STm C Γ₀ t
  | .val _, x => (x.1, x.2 && !c)
  | .alias _, x => x
  | .mem _, x => x
  | .old, x => x
  | .oldNet, x => x
  | .kint, x => x

/-- Whether a local is pending. -/
def _root_.Solidity.LTy.spend : (t : LTy) → LTy.STm C Γ₀ t → Bool
  | .val _, x => x.2
  | .alias _, _ => false
  | .mem _, _ => false
  | .old, _ => false
  | .oldNet, _ => false
  | .kint, _ => false

/-- The locals at the positions `n, n + 1, …` where `c` holds discharged. -/
def clear (c : Nat → Bool) (n : Nat) : (Δ : Ctx) → SEnv C Γ₀ Δ → SEnv C Γ₀ Δ
  | [], e => e
  | t :: Δ, e => (LTy.sclear (c n) t e.1, clear c (n + 1) Δ e.2)

/-- No local is pending. -/
def clean : (Δ : Ctx) → SEnv C Γ₀ Δ → Bool
  | [], _ => true
  | t :: Δ, e => !LTy.spend t e.1 && clean Δ e.2

/-- The locals a suffix pushed, popped, none of them pending. -/
def dropChk {Δ : Ctx} : {Δ' : Ctx} → Ext Δ Δ' → SEnv C Γ₀ Δ' → Option (SEnv C Γ₀ Δ)
  | _, h => Ext.casesOn (motive := fun Δ' _ => SEnv C Γ₀ Δ' → Option (SEnv C Γ₀ Δ)) h
      (fun e => some e)
      (fun {t} {_} h e => if LTy.spend t e.1 then none else SEnv.dropChk h e.2)
  termination_by structural _ h => h

/-- A local's term, as itself. -/
def _root_.Solidity.LTy.sid : (t : LTy) → Idx Γ₀ t → LTy.STm C Γ₀ t
  | .val _, i => (.pvV i, false)
  | .alias _, _ => ()
  | .mem _, _ => ()
  | .old, _ => ()
  | .oldNet, _ => ()
  | .kint, _ => ()

/-- Every local of `Δ` as the local of `Γ₀` that `f` names. -/
def idAt : (Δ : Ctx) → ({t : LTy} → Idx Δ t → Idx Γ₀ t) → SEnv C Γ₀ Δ
  | [], _ => ()
  | t :: Δ, f => (LTy.sid t (f .here), idAt Δ fun i => f (.there i))

/-- Every local as itself. -/
def id (Δ : Ctx) : SEnv C Δ Δ := idAt Δ fun i => i

theorem get_idAt : {Δ : Ctx} → (f : {t : LTy} → Idx Δ t → Idx Γ₀ t) → {p : PrimTy} →
    (i : Idx Δ (.val p)) → (SEnv.idAt (C := C) Δ f).get i = (.pvV (f i), false)
  | _ :: _, _, _, .here => rfl
  | _ :: _, f, _, .there i => get_idAt (fun j => f (.there j)) i

end SEnv

/-! ## Terms read through a symbolic frame -/

section Terms

variable {Γ₀ Δ : Ctx}

/-- `substE` by `match`, its compiled form. -/
def Tm.substEM (E : SEnv C Γ₀ Δ) : {s : Srt} → Tm C Δ s → Option (Tm C Γ₀ s)
  | _, .pvV i => some (E.get i).1
  | _, .pvP _ => none
  | _, .pvS _ => none
  | _, .pvI _ => none
  | _, .netOf _ _ => none
  | _, .app0 o => some (.app0 o)
  | _, .app1 o x => (x.substEM E).map (.app1 o)
  | _, .app2 o x y => (x.substEM E).bind fun x' => (y.substEM E).map fun y' => .app2 o x' y'
  | _, .app3 o x y z => (x.substEM E).bind fun x' => (y.substEM E).bind fun y' =>
      (z.substEM E).map fun z' => .app3 o x' y' z'
  | _, .pvZ _ => none

/-- **A term of the frame `Δ` read over `Γ₀`**: each value local replaced by
its term in `E`; a term that reads any other local has none. -/
@[implemented_by Tm.substEM]
def Tm.substE (E : SEnv C Γ₀ Δ) {s : Srt} (t : Tm C Δ s) : Option (Tm C Γ₀ s) :=
  @Tm.rec C Δ (fun s _ => Option (Tm C Γ₀ s))
    (fun i => some (E.get i).1)
    (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ _ => none)
    (fun o => some (.app0 o))
    (fun o _ ix => ix.map (.app1 o))
    (fun o _ _ ix iy => ix.bind fun x' => iy.map fun y' => .app2 o x' y')
    (fun o _ _ _ ix iy iz => ix.bind fun x' => iy.bind fun y' => iz.map fun z' => .app3 o x' y' z')
    (fun _ => none) s t

theorem Tm.substE_eq_substEM (E : SEnv C Γ₀ Δ) : {s : Srt} → (t : Tm C Δ s) →
    t.substE E = t.substEM E
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .netOf _ _ | _, .app0 _ | _, .pvZ _ => rfl
  | _, .app1 o x => by
    show (x.substE E).map _ = (x.substEM E).map _
    rw [Tm.substE_eq_substEM E x]
  | _, .app2 o x y => by
    show (x.substE E).bind _ = (x.substEM E).bind _
    rw [Tm.substE_eq_substEM E x]
    show (x.substEM E).bind (fun x' => (y.substE E).map _) = _
    rw [Tm.substE_eq_substEM E y]
  | _, .app3 o x y z => by
    show (x.substE E).bind _ = (x.substEM E).bind _
    rw [Tm.substE_eq_substEM E x]
    show (x.substEM E).bind (fun x' => (y.substE E).bind fun y' => (z.substE E).map _) = _
    rw [Tm.substE_eq_substEM E y, Tm.substE_eq_substEM E z]

/-- A binary operator that reads its second operand only on some values of
the first (`&&`, `||`, `BinOp.shortT`). -/
def _root_.Solidity.BinOp.lazyB : BinOp → Bool
  | .and | .or => true
  | _ => false

/-- A binary symbol that reads both its arguments whatever they are. -/
def _root_.Solidity.Op2.strictB {a b s : Srt} : Op2 C a b s → Bool
  | .binop op _ => !op.lazyB
  | _ => false

/-- `strictReads` by `match`, its compiled form. -/
def Tm.strictReadsM (n : Nat) : {s : Srt} → Tm C Δ s → Bool
  | _, .pvV i => i.toNat == n
  | _, .app1 _ x => x.strictReadsM n
  | _, .app2 o x y => o.strictB && (x.strictReadsM n || y.strictReadsM n)
  | _, _ => false

/-- **The term reads the value local at position `n` wherever it is read**:
the local itself, under a unary symbol, or under a binary operator that
reads both its operands (not `&&`, `||`): if the term returns, the local's
term does. -/
@[implemented_by Tm.strictReadsM]
def Tm.strictReads (n : Nat) {s : Srt} (t : Tm C Δ s) : Bool :=
  @Tm.rec C Δ (fun _ _ => Bool)
    (fun i => i.toNat == n)
    (fun _ => false) (fun _ => false) (fun _ => false) (fun _ _ _ => false)
    (fun _ => false)
    (fun _ _ ix => ix)
    (fun o _ _ ix iy => o.strictB && (ix || iy))
    (fun _ _ _ _ _ _ _ => false)
    (fun _ => false) s t

theorem Tm.strictReads_eq_strictReadsM (n : Nat) : {s : Srt} → (t : Tm C Δ s) →
    t.strictReads n = t.strictReadsM n
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .netOf _ _ | _, .app0 _ | _, .pvZ _
  | _, .app3 .. => rfl
  | _, .app1 o x => Tm.strictReads_eq_strictReadsM n x
  | _, .app2 o x y => by
    show (o.strictB && (x.strictReads n || y.strictReads n)) = _
    rw [Tm.strictReads_eq_strictReadsM n x, Tm.strictReads_eq_strictReadsM n y]; rfl

/-- A literal. -/
def _root_.Solidity.Op0.litB {s : Srt} : Op0 C s → Bool
  | .lit _ => true
  | _ => false

/-- A term that always returns: a local, a literal. -/
def Tm.alwaysB {s : Srt} : Tm C Γ₀ s → Bool
  | .pvV _ => true
  | .app0 o => o.litB
  | _ => false

/-! ### Offsets folded -/

section Fold

variable {Γ : Ctx}

/-- A `uint` literal's integer. -/
def _root_.Solidity.Op0.litInt? {s : Srt} : Op0 C s → Option Int
  | .lit (p := .uint) v => some v.1
  | _ => none

/-- A term that is a `uint` literal: its integer. -/
def Tm.litInt? {s : Srt} : Tm C Γ s → Option Int
  | .app0 o => o.litInt?
  | _ => none

/-- `u + c`, `c` a `uint` literal: `u` and `c`. -/
def _root_.Solidity.Op2.addParts : {a b s : Srt} → Op2 C a b s → Tm C Γ a → Tm C Γ b →
    Option (Tm C Γ s × Int)
  | _, _, _, .binop .add _, u, w => w.litInt?.map fun c => (u, c)
  | _, _, _, _, _, _ => none

/-- A term `u + c`, `c` a `uint` literal: `u` and `c`. -/
def Tm.addParts? {s : Srt} : Tm C Γ s → Option (Tm C Γ s × Int)
  | .app2 o u w => o.addParts u w
  | _ => none

/-- **A binary symbol applied, offsets folded**: `(u + c₁) + c₂` at `uint` is
`u + (c₁ + c₂)` where the sum is a `uint`; any other application as it is. -/
def _root_.Solidity.Op2.mk2 : {a b s : Srt} → Op2 C a b s → Tm C Γ a → Tm C Γ b → Tm C Γ s
  | _, _, _, .binop .add (p := .uint) h, x, y =>
    match y.litInt?, x.addParts? with
    | some c₂, some (u, c₁) =>
      if hr : PrimTy.uint.inRange (c₁ + c₂) = true then
        .app2 (.binop .add h) u (.app0 (.lit (p := .uint) ⟨c₁ + c₂, hr⟩))
      else .app2 (.binop .add h) x y
    | _, _ => .app2 (.binop .add h) x y
  | _, _, _, o, x, y => .app2 o x y

/-- `norm` by `match`, its compiled form. -/
def Tm.normM : {s : Srt} → Tm C Γ s → Tm C Γ s
  | _, .netOf i a => .netOf i a.normM
  | _, .app1 o x => .app1 o x.normM
  | _, .app2 o x y => o.mk2 x.normM y.normM
  | _, .app3 o x y z => .app3 o x.normM y.normM z.normM
  | _, t => t

/-- **A term's offsets folded**: `(u + c₁) + c₂` at `uint` is `u + (c₁ + c₂)`
wherever both are literals and the sum is a `uint` (`Op2.mk2`), as KeY's
`polySimp` adds literal summands. -/
@[implemented_by Tm.normM]
def Tm.norm {s : Srt} (t : Tm C Γ s) : Tm C Γ s :=
  @Tm.rec C Γ (fun s _ => Tm C Γ s)
    (fun i => .pvV i) (fun i => .pvP i) (fun i => .pvS i) (fun i => .pvI i)
    (fun i _ ia => .netOf i ia) (fun o => .app0 o) (fun o _ ix => .app1 o ix)
    (fun o _ _ ix iy => o.mk2 ix iy) (fun o _ _ _ ix iy iz => .app3 o ix iy iz)
    (fun i => .pvZ i) s t

theorem Tm.norm_eq_normM : {s : Srt} → (t : Tm C Γ s) → t.norm = t.normM
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .app0 _ | _, .pvZ _ => rfl
  | _, .netOf i a => by
    show Tm.netOf i a.norm = _
    rw [Tm.norm_eq_normM a]; rfl
  | _, .app1 o x => by
    show Tm.app1 o x.norm = _
    rw [Tm.norm_eq_normM x]; rfl
  | _, .app2 o x y => by
    show o.mk2 x.norm y.norm = _
    rw [Tm.norm_eq_normM x, Tm.norm_eq_normM y]; rfl
  | _, .app3 o x y z => by
    show Tm.app3 o x.norm y.norm z.norm = _
    rw [Tm.norm_eq_normM x, Tm.norm_eq_normM y, Tm.norm_eq_normM z]; rfl

end Fold

end Terms

/-! ## The symbolic run of a body -/

section Sym

variable {Γ₀ : Ctx}

/-- A value local set to `t`, read in `Δ` as `src` (`v = e;`): the locals
`src` takes over discharged, then the target, which must not be pending
unless `src` took it over, holds `t`, pending unless it always returns. -/
def SEnv.assign {Δ : Ctx} {p : PrimTy} (E : SEnv C Γ₀ Δ) (src : Nat → Bool) (i : Idx Δ (.val p))
    (t : Tm C Γ₀ (.val p)) : Option (SEnv C Γ₀ Δ) :=
  if ((SEnv.clear src 0 Δ E).get i).2 then none
  else some ((SEnv.clear src 0 Δ E).set i (t, !t.alwaysB))

/-- The arguments of a call as the callee's frame sees them: each simple
value read through `E`; none for an argument that is not a simple value. -/
def Args.sym {Δ : Ctx} (E : SEnv C Γ₀ Δ) : {ps : Ctx} → Args C Δ ps → Option (SEnv C Γ₀ ps)
  | _, as => Args.casesOn (motive := fun ps _ => Option (SEnv C Γ₀ ps)) as (some ())
      (fun as _ _ e => match e with
        | .simple s => (s.lower.substE E).bind fun t => (Args.sym E as).map fun θ => ((t, false), θ)
        | _ => none)
      (fun _ _ _ _ => none) (fun _ _ _ _ => none)
  termination_by structural _ as => as

/-- The caller's positions a callee takes over through its arguments: the
local passed as the parameter at position `n + 1` of the frame (the return
variable at `0`) where the summary reads it wherever it is read (`c n`). -/
def Args.takes {Δ : Ctx} (c : Nat → Bool) : {ps : Ctx} → Args C Δ ps → Nat → Bool
  | _, as => Args.casesOn (motive := fun _ _ => Nat → Bool) as (fun _ => false)
      (fun as _ _ e => fun m => (match e with
          | .simple (.local i) => c 0 && i.toNat == m
          | _ => false) || Args.takes (fun n => c (n + 1)) as m)
      (fun _ _ _ _ _ => false) (fun _ _ _ _ _ => false)
  termination_by structural _ as => as

/-- A callee's summary from its body's symbolic run `R?` in its own frame:
the return variable's term, every other local of the frame and every local
the body pushed not pending. -/
def CallRet.sumOf {ps Γf : Ctx} {p : PrimTy} (hb : Ext (.val p :: ps) Γf)
    (R? : Option (SEnv C (.val p :: ps) Γf)) : Option (Tm C (.val p :: ps) (.val p)) :=
  (R?.bind (SEnv.dropChk hb)).bind fun E =>
    if SEnv.clean ps E.2 then some E.1.1 else Option.none

/-- A call `y = f(args);` run symbolically in the caller's frame `E`: the
callee's summary `R` read at the arguments, assigned to `y`. -/
def CallRet.sym {Δ Δ' ps rs Γf : Ctx} (args : Args C Δ ps) (ret : CallRet Δ rs Δ')
    (hb : Ext (rs ++ ps) Γf) (R? : Option (SEnv C (rs ++ ps) Γf)) (E : SEnv C Γ₀ Δ) :
    Option (SEnv C Γ₀ Δ') :=
  CallRet.casesOn (motive := fun rs Δ' _ => Ext (rs ++ ps) Γf → Option (SEnv C (rs ++ ps) Γf) →
      Option (SEnv C Γ₀ Δ')) ret
    (fun _ _ => Option.none)
    (fun p _ res hb R? => Option.casesOn (motive := fun _ => Option (SEnv C Γ₀ Δ)) res Option.none
      fun j => (CallRet.sumOf hb R?).bind fun R => (Args.sym E args).bind fun θ =>
        (Tm.substE (Γ₀ := Γ₀) (Δ := .val p :: ps) ((Tm.app0 (.lit (PrimTy.dflt p)), false), θ)
          R).bind fun t => E.assign (Args.takes (fun n => R.strictReads (n + 1)) args) j t.norm)
    (fun _ _ _ => Option.none) (fun _ _ _ _ _ _ => Option.none) (fun _ _ _ _ => Option.none) hb R?

/-- The motive of the symbolic run: from a frame over `Γ₀` for `Δ`, the frame
for `Δ'`, if the program has a summary. -/
abbrev SymM (C : Contract) (Δ Δ' : Ctx) : Type :=
  (Γ₀ : Ctx) → SEnv C Γ₀ Δ → Option (SEnv C Γ₀ Δ')

mutual

/-- `sym` by `match`, its compiled form. -/
def Stmt.symM : {Δ Δ' : Ctx} → Stmt C Δ Δ' → SymM C Δ Δ'
  | _, _, .assignLocal i v, _, E =>
    (v.lower.substE E).bind fun t => E.assign (fun n => v.lower.strictReads n) i t.norm
  | _, _, .declLocal p _ none, _, E => some (((Tm.app0 (.lit (PrimTy.dflt p))), false), E)
  | _, _, .declLocal _ _ (some v), _, E =>
    (v.lower.substE E).bind fun t =>
      some ((t.norm, !t.norm.alwaysB), SEnv.clear (fun n => v.lower.strictReads n) 0 _ E)
  | _, _, .block body, Γ₀, E => (Prog.symM body Γ₀ E).bind (SEnv.dropChk body.ext)
  | _, _, .call _ args ret body, _, E =>
    CallRet.sym args ret body.ext (Prog.symM body _ (SEnv.id _)) E
  | _, _, _, _, _ => none

/-- `sym` of a sequence by `match`, its compiled form. -/
def Prog.symM : {Δ Δ' : Ctx} → Prog C Δ Δ' → SymM C Δ Δ'
  | _, _, .nil, _, E => some E
  | _, _, .cons s P, Γ₀, E => (Stmt.symM s Γ₀ E).bind (Prog.symM P Γ₀)

end


/-- **The symbolic run of a statement** (`Stmt.symM`, by the recursor). -/
@[implemented_by Stmt.symM]
def Stmt.sym {Δ Δ' : Ctx} (s : Stmt C Δ Δ') : SymM C Δ Δ' :=
  Stmt.rec (motive_1 := fun Δ Δ' _ => SymM C Δ Δ') (motive_2 := fun Δ Δ' _ => SymM C Δ Δ')
    (fun _ _ _ _ => none) (fun _ _ _ _ => none)
    (fun i v _ E => (v.lower.substE E).bind fun t => E.assign (fun n => v.lower.strictReads n) i t.norm)
    (fun p _ init _ E => Option.casesOn (motive := fun _ => Option (SEnv C _ (.val p :: _))) init
      (some (((Tm.app0 (.lit (PrimTy.dflt p))), false), E))
      fun v => (v.lower.substE E).bind fun t =>
        some ((t.norm, !t.norm.alwaysB), SEnv.clear (fun n => v.lower.strictReads n) 0 _ E))
    (fun _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ _ => none) (fun _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
    (fun _ _ _ _ _ => none)
    (fun _ _ _ => none) (fun _ _ _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
    (fun _ _ _ _ => none) (fun _ _ _ _ => none)
    (fun _ _ _ => none) (fun _ _ _ _ => none) (fun _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ _ => none)
    (fun _ _ _ => none) (fun _ _ _ => none) (fun _ _ => none)
    (fun _ _ => none)
    (fun _ args ret body ih _ E => CallRet.sym args ret body.ext (ih _ (SEnv.id _)) E)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ => none) (fun body ih Γ₀ E => (ih Γ₀ E).bind (SEnv.dropChk body.ext))
    (fun _ _ _ _ _ _ _ => none) (fun _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ _ _ => none)
    (fun _ _ _ => none)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => none)
    (fun _ E => some E) (fun _ _ ihS ihP Γ₀ E => (ihS Γ₀ E).bind (ihP Γ₀)) s

/-- **The symbolic run of a sequence** (`Prog.symM`, by the recursor). -/
@[implemented_by Prog.symM]
def Prog.sym {Δ Δ' : Ctx} (P : Prog C Δ Δ') : SymM C Δ Δ' :=
  Prog.rec (motive_1 := fun Δ Δ' _ => SymM C Δ Δ') (motive_2 := fun Δ Δ' _ => SymM C Δ Δ')
    (fun _ _ _ _ => none) (fun _ _ _ _ => none)
    (fun i v _ E => (v.lower.substE E).bind fun t => E.assign (fun n => v.lower.strictReads n) i t.norm)
    (fun p _ init _ E => Option.casesOn (motive := fun _ => Option (SEnv C _ (.val p :: _))) init
      (some (((Tm.app0 (.lit (PrimTy.dflt p))), false), E))
      fun v => (v.lower.substE E).bind fun t =>
        some ((t.norm, !t.norm.alwaysB), SEnv.clear (fun n => v.lower.strictReads n) 0 _ E))
    (fun _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ _ => none) (fun _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
    (fun _ _ _ _ _ => none)
    (fun _ _ _ => none) (fun _ _ _ _ => none) (fun _ _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ _ => none) (fun _ _ _ _ => none)
    (fun _ _ _ _ => none) (fun _ _ _ _ => none)
    (fun _ _ _ => none) (fun _ _ _ _ => none) (fun _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ _ => none)
    (fun _ _ _ => none) (fun _ _ _ => none) (fun _ _ => none)
    (fun _ _ => none)
    (fun _ args ret body ih _ E => CallRet.sym args ret body.ext (ih _ (SEnv.id _)) E)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ => none) (fun body ih Γ₀ E => (ih Γ₀ E).bind (SEnv.dropChk body.ext))
    (fun _ _ _ _ _ _ _ => none) (fun _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ _ _ _ _ => none)
    (fun _ _ _ _ _ _ _ _ => none)
    (fun _ _ _ => none)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => none)
    (fun _ E => some E) (fun _ _ ihS ihP Γ₀ E => (ihS Γ₀ E).bind (ihP Γ₀)) P

mutual

theorem Stmt.sym_eq_symM : {Δ Δ' : Ctx} → (s : Stmt C Δ Δ') → s.sym = s.symM
  | _, _, .assignLocal _ _ => rfl
  | _, _, .declLocal _ _ none => rfl
  | _, _, .declLocal _ _ (some _) => rfl
  | _, _, .block body => by
    show (fun Γ₀ E => (body.sym Γ₀ E).bind (SEnv.dropChk body.ext)) = _
    rw [Prog.sym_eq_symM body]; rfl
  | _, _, .call f args ret body => by
    show (fun _ E => CallRet.sym args ret body.ext (body.sym _ (SEnv.id _)) E) = _
    rw [Prog.sym_eq_symM body]; rfl
  | _, _, .assign .. | _, _, .rebind .. | _, _, .declStorage .. | _, _, .opAssign ..
  | _, _, .incDec .. | _, _, .assignIncDec .. | _, _, .pushOpAssign .. | _, _, .pushIncDec ..
  | _, _, .assignLocalPush .. | _, _, .push .. | _, _, .pop .. | _, _, .transfer ..
  | _, _, .send .. | _, _, .declMem .. | _, _, .rebindMem .. | _, _, .assignFromMem ..
  | _, _, .assignMem .. | _, _, .delete .. | _, _, .deleteMem .. | _, _, .assignNew ..
  | _, _, .ite .. | _, _, .require .. | _, _, .assert .. | _, _, .revert | _, _, .assumeFalse
  | _, _, .tryCall .. | _, _, .loop .. | _, _, .callReceiver .. | _, _, .callReceiverPush ..
  | _, _, .callRec .. | _, _, .revertData _ | _, _, .catchData .. => rfl

theorem Prog.sym_eq_symM : {Δ Δ' : Ctx} → (P : Prog C Δ Δ') → P.sym = P.symM
  | _, _, .nil => rfl
  | _, _, .cons s P => by
    show (fun Γ₀ E => (s.sym Γ₀ E).bind (P.sym Γ₀)) = _
    rw [Stmt.sym_eq_symM s, Prog.sym_eq_symM P]; rfl

end

/-- A binary symbol that does not push (`pushSlot`, `extend`). -/
def _root_.Solidity.Op2.noPushB {a b s : Srt} : Op2 C a b s → Bool
  | .pushSlot | .extend => false
  | _ => true

/-- A ternary symbol that does not push. -/
def _root_.Solidity.Op3.noPushB {a b c s : Srt} : Op3 C a b c s → Bool
  | .push => false
  | _ => true

/-- `valOnly` by `match`, its compiled form. -/
def Tm.valOnlyM {Γ : Ctx} : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV _ => true
  | _, .app0 _ => true
  | _, .app1 _ x => x.valOnlyM
  | _, .app2 o x y => o.noPushB && x.valOnlyM && y.valOnlyM
  | _, .app3 o x y z => o.noPushB && x.valOnlyM && y.valOnlyM && z.valOnlyM
  | _, _ => false

/-- The term reads value locals only and pushes nothing: read through any
frame, it has a reading (`Tm.substE`), and it is never out of gas. -/
@[implemented_by Tm.valOnlyM]
def Tm.valOnly {Γ : Ctx} {s : Srt} (t : Tm C Γ s) : Bool :=
  @Tm.rec C Γ (fun _ _ => Bool)
    (fun _ => true) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ _ _ => false)
    (fun _ => true) (fun _ _ ix => ix) (fun o _ _ ix iy => o.noPushB && ix && iy)
    (fun o _ _ _ ix iy iz => o.noPushB && ix && iy && iz) (fun _ => false) s t

theorem Tm.valOnly_eq_valOnlyM {Γ : Ctx} : {s : Srt} → (t : Tm C Γ s) → t.valOnly = t.valOnlyM
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .netOf _ _ | _, .app0 _ | _, .pvZ _ => rfl
  | _, .app1 _ x => Tm.valOnly_eq_valOnlyM x
  | _, .app2 o x y => by
    show (o.noPushB && x.valOnly && y.valOnly) = _
    rw [Tm.valOnly_eq_valOnlyM x, Tm.valOnly_eq_valOnlyM y]; rfl
  | _, .app3 o x y z => by
    show (o.noPushB && x.valOnly && y.valOnly && z.valOnly) = _
    rw [Tm.valOnly_eq_valOnlyM x, Tm.valOnly_eq_valOnlyM y, Tm.valOnly_eq_valOnlyM z]; rfl

/-- Every argument is a simple value. -/
def Args.simpleVals {Δ : Ctx} : {ps : Ctx} → Args C Δ ps → Bool
  | _, as => Args.casesOn (motive := fun _ _ => Bool) as true
      (fun as _ _ e => (match e with | .simple _ => true | _ => false) && Args.simpleVals as)
      (fun _ _ _ _ => false) (fun _ _ _ _ => false)
  termination_by structural _ as => as

/-- `hasCall` by `match`, its compiled form. -/
def Prog.hasCallM : {Δ Δ' : Ctx} → Prog C Δ Δ' → Bool
  | _, _, .nil => false
  | _, _, .cons (.call ..) _ => true
  | _, _, .cons (.block b) P => b.hasCallM || P.hasCallM
  | _, _, .cons _ P => P.hasCallM

/-- **The body calls**: a call among its statements or its blocks'. -/
@[implemented_by Prog.hasCallM]
def Prog.hasCall {Δ Δ' : Ctx} (P : Prog C Δ Δ') : Bool :=
  Prog.rec (motive_1 := fun _ _ _ => Bool) (motive_2 := fun _ _ _ => Bool)
    (fun _ _ => false) (fun _ _ => false) (fun _ _ => false) (fun _ _ _ => false)
    (fun _ _ _ => false) (fun _ _ _ _ _ => false) (fun _ _ _ => false) (fun _ _ _ _ _ => false)
    (fun _ _ => false) (fun _ _ _ => false) (fun _ => false) (fun _ _ => false)
    (fun _ _ _ _ => false) (fun _ _ _ _ _ => false) (fun _ _ => false) (fun _ _ => false)
    (fun _ _ => false) (fun _ => false) (fun _ _ => false) (fun _ _ _ => false)
    (fun _ _ _ _ _ => false) (fun _ => false) (fun _ => false) false false
    (fun _ _ _ _ _ => true)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => false)
    (fun _ _ _ _ => false) (fun _ ih => ih)
    (fun _ _ _ _ _ => false) (fun _ _ _ => false)
    (fun _ _ _ _ _ _ => false) (fun _ _ _ _ _ _ _ _ => false)
    (fun _ _ _ _ _ _ => false) (fun _ => false) (fun _ _ _ _ _ _ _ _ _ _ => false)
    false (fun _ _ ihS ihP => ihS || ihP) P

/-- The gate of a summary: the callee calls (a body that does not runs
once per call either way, `internalCallExpand`), its summary reads value
locals only, and it is smaller than the bound on what a rule emits
(`Stmt.step_tmSize_le`) allows. -/
def Tm.sumGate {Γ Δ' : Ctx} {p : PrimTy} (body : Prog C Γ Δ') (R : Tm C Γ (.val p)) : Bool :=
  R.valOnly && decide (R.size < 16 * body.size + 16)

/-- **A call's summary, as the update of its target** (`internalCallSummary`):
`y = f(args);` with simple arguments, whose callee calls and has a summary
`R` (`CallRet.sumOf`, `Tm.sumGate`), is `{ y := R(args) }`; any other call
has none. -/
def CallRet.summary? {Γ Γ' ps rs Γf : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (body : Prog C (rs ++ ps) Γf) : Option (Upd C Γ Γ') :=
  CallRet.casesOn (motive := fun rs Γ' _ => Prog C (rs ++ ps) Γf → Option (Upd C Γ Γ')) ret
    (fun _ => Option.none)
    (fun p _ res body => Option.casesOn (motive := fun _ => Option (Upd C Γ Γ)) res Option.none
      fun j => if body.hasCall then
        (CallRet.sumOf body.ext (body.sym _ (SEnv.id _))).bind fun R =>
          if Tm.sumGate body R then
            (Args.sym (SEnv.id Γ) args).bind fun θ =>
              (Tm.substE (Γ₀ := Γ) (Δ := .val p :: ps)
                ((Tm.app0 (.lit (PrimTy.dflt p)), false), θ) R).map fun t =>
                  Upd.nil.snoc (.local j (.val t))
          else Option.none
        else Option.none)
    (fun _ _ => Option.none) (fun _ _ _ _ _ => Option.none) (fun _ _ _ => Option.none) body

/-- Whether a call has a summary, read off its shape: one value assigned,
simple arguments, a callee that calls and whose summary passes the gate. -/
def CallRet.sumOK {Γ Γ' ps rs Γf : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (body : Prog C (rs ++ ps) Γf) : Bool :=
  CallRet.casesOn (motive := fun rs _ _ => Prog C (rs ++ ps) Γf → Bool) ret
    (fun _ => false)
    (fun _ _ res body => res.isSome && body.hasCall &&
      ((CallRet.sumOf body.ext (body.sym _ (SEnv.id _))).any (Tm.sumGate body)) && args.simpleVals)
    (fun _ _ => false) (fun _ _ _ _ _ => false) (fun _ _ _ => false) body

theorem Tm.substE_isSome {Γ₀ Δ : Ctx} (E : SEnv C Γ₀ Δ) : {s : Srt} → (t : Tm C Δ s) →
    t.valOnly = true → (t.substE E).isSome = true
  | _, .pvV _, _ => rfl
  | _, .app0 _, _ => rfl
  | _, .app1 o x, h => by
    have hx := Tm.substE_isSome E x h
    show ((x.substE E).map (Tm.app1 o)).isSome = true
    revert hx
    cases x.substE E with
    | none => exact id
    | some _ => exact fun _ => rfl
  | _, .app2 o x y, h => by
    have h' : (o.noPushB && x.valOnly && y.valOnly) = true := h
    have hx := Tm.substE_isSome E x (Bool.and_eq_true _ _ ▸ (Bool.and_eq_true _ _ ▸ h').1).2
    have hy := Tm.substE_isSome E y (Bool.and_eq_true _ _ ▸ h').2
    show ((x.substE E).bind fun x' => (y.substE E).map fun y' => Tm.app2 o x' y').isSome = true
    revert hx hy
    cases x.substE E with
    | none => exact fun h _ => h
    | some _ =>
      cases y.substE E with
      | none => exact fun _ h => h
      | some _ => exact fun _ _ => rfl
  | _, .app3 o x y z, h => by
    have h' : (o.noPushB && x.valOnly && y.valOnly && z.valOnly) = true := h
    have h₁ := Bool.and_eq_true _ _ ▸ h'
    have h₂ := Bool.and_eq_true _ _ ▸ h₁.1
    have h₃ := Bool.and_eq_true _ _ ▸ h₂.1
    have hx := Tm.substE_isSome E x h₃.2
    have hy := Tm.substE_isSome E y h₂.2
    have hz := Tm.substE_isSome E z h₁.2
    show ((x.substE E).bind fun x' => (y.substE E).bind fun y' =>
      (z.substE E).map fun z' => Tm.app3 o x' y' z').isSome = true
    revert hx hy hz
    cases x.substE E with
    | none => exact fun h _ _ => h
    | some _ =>
      cases y.substE E with
      | none => exact fun _ h _ => h
      | some _ =>
        cases z.substE E with
        | none => exact fun _ _ h => h
        | some _ => exact fun _ _ _ => rfl
  | _, .pvP _, h | _, .pvS _, h | _, .pvI _, h | _, .netOf _ _, h | _, .pvZ _, h => nomatch h

theorem Args.sym_isSome {Γ₀ Δ : Ctx} (E : SEnv C Γ₀ Δ) : {ps : Ctx} → (args : Args C Δ ps) →
    (Args.sym E args).isSome = args.simpleVals
  | _, .nil => rfl
  | _, .snoc as p x e => by
    cases e with
    | simple s =>
      have hs : (s.lower.substE E).isSome = true :=
        Tm.substE_isSome E s.lower (by cases s <;> first | rfl | (rename_i hp; subst hp; rfl))
      have ih := Args.sym_isSome E as
      show ((s.lower.substE E).bind fun t => (Args.sym E as).map fun θ => ((t, false), θ)).isSome =
        (true && Args.simpleVals as)
      revert hs ih
      cases s.lower.substE E with
      | none => exact fun h _ => nomatch h
      | some t =>
        intro _ ih
        rw [Bool.true_and, ← ih]
        show ((Args.sym E as).map fun θ => ((t, false), θ)).isSome = (Args.sym E as).isSome
        cases Args.sym E as <;> rfl
    | _ => rfl
  | _, .snocStorage .. | _, .snocMemory .. => rfl

/-- **A call has a summary exactly where its shape says so.** -/
theorem CallRet.summary?_isSome {Γ Γ' ps rs Γf : Ctx} (args : Args C Γ ps)
    (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf) :
    (CallRet.summary? args ret body).isSome = CallRet.sumOK args ret body := by
  cases ret with
  | val p r res =>
    cases res with
    | none => rfl
    | some j =>
      show (if body.hasCall then _ else Option.none).isSome =
        (true && body.hasCall && _ && args.simpleVals)
      cases hc : body.hasCall with
      | false => rfl
      | true =>
        show (Option.bind _ _).isSome = _
        cases hR : CallRet.sumOf body.ext (body.sym _ (SEnv.id _)) with
        | none => rfl
        | some R =>
          show (if Tm.sumGate body R then _ else Option.none).isSome =
            (true && true && Tm.sumGate body R && args.simpleVals)
          cases hg : Tm.sumGate body R with
          | false => rfl
          | true =>
            have hv : R.valOnly = true := (Bool.and_eq_true _ _ ▸ hg).1
            show ((Args.sym (SEnv.id Γ) args).bind _).isSome = (true && true && true && args.simpleVals)
            rw [← Args.sym_isSome (SEnv.id Γ) args]
            cases Args.sym (SEnv.id Γ) args with
            | none => rfl
            | some θ =>
              have hs := Tm.substE_isSome (Δ := .val p :: ps)
                (show SEnv C Γ (.val p :: ps) from ((Tm.app0 (.lit (PrimTy.dflt p)), false), θ)) R hv
              show (Option.map _ _).isSome = true
              revert hs
              cases Tm.substE (Δ := .val p :: ps)
                (show SEnv C Γ (.val p :: ps) from ((Tm.app0 (.lit (PrimTy.dflt p)), false), θ)) R with
              | none => exact id
              | some _ => exact fun _ => rfl
  | none => rfl
  | rets _ => rfl
  | mem _ _ _ _ => rfl
  | storage _ _ => rfl

end Sym

end Solidity
