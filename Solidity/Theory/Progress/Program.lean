import Solidity.Theory.Progress.Calls
import Solidity.Lowering.P9.FunctionCatalog

/-!
# Progress (S4.1): the public statements

A program whose allowed internal functions are bodies of the extended
fragment (`CallsOKX`, `Theory/Progress/Calls.lean`), with a sound
extension (`StmtExt.Sound`), **never gets stuck**: every expression,
statement, block, modifier-free body and internal call of the fragment,
run from any state at any horizon, returns, panics, reverts with other
data, or runs out of fuel (`Ends`, `Theory/Progress/Outcome.lean`).

* `expr_progress`, `stmt_progress`, `items_progress`, `body_progress`,
  `call_progress`: the general statements, for any extension.
* `tuple_stmt_progress`: no extension and no calls, so no program premise:
  the existing value fragment with tuple declarations.
* `elaborated_call_progress`, `elaborated_stmt_progress`: for an actually
  elaborated program whose complete function catalogue P9 checks
  (`WholeProgram.checkFunctions`), the premise is derived
  (`WholeProgram.functions_from_elaborate`, `CallsOK.toX`); the statement
  itself may contain tuple declarations and admitted extension nodes.

The core run's progress is `Prog.run_ends`/`Prog.runF_ends`
(by construction).

**Not covered** (the fragment's boundary, recorded in
`docs/feature-work/semantics-extensions.md`, "Handoffs"): memory and
reference values, external calls, `try`, modifiers, the transaction layer
(dispatch, ABI decoding, deployment, callbacks); gas is not charged (D2).
-/

namespace Solidity.Theory.Progress

open Solidity.Source Solidity.Source.Progress EM

variable {E : Env} {X : StmtExt E} {A : Decl → Prop} {G : Glob E} {c : String}

/-- **Progress of expressions** of the call fragment. -/
theorem expr_progress (hG : CallsOKX X A G c) (hS : X.Sound G A (· = c)) (F : Fr) (hc : F.contract = c)
    (n : Nat) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) (hf : RExpr.ValFragC A e) (ho : e.OpsOK)
    (x : Locals E.layout Γ × St E) : Ends ((evalE G F n e).run x).1 :=
  NS.ends (((fragXAt hG hS n).expr n (Nat.le_refl n) F hc).val e hf ho) x

/-- **Progress of statements** of the extended fragment, in a body frame. -/
theorem stmt_progress (hG : CallsOKX X A G c) (hS : X.Sound G A (· = c)) (F : Fr) (hc : F.contract = c)
    (n nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) (hf : SFrag X A s) (ho : s.OpsOK)
    (hfr : BodyFrame nps R Γ) (x : Locals E.layout [] × St E) : Ends ((execS G F n nps ph s l).run x).1 :=
  NS.ends ((fragXAt hG hS n).stmt.execS F hc nps ph s l hf ho hfr).ns x

/-- **Progress of blocks** of the extended fragment, in a body frame. -/
theorem items_progress (hG : CallsOKX X A G c) (hS : X.Sound G A (· = c)) (F : Fr) (hc : F.contract = c)
    (n nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) (hf : IFrag X A b) (ho : b.OpsOK)
    (hfr : BodyFrame nps R Γ) (x : Locals E.layout [] × St E) : Ends ((execItems G F n nps ph b l).run x).1 :=
  NS.ends ((fragXAt hG hS n).stmt.execItems F hc nps ph b l hf ho hfr).ns x

/-- **Progress of a body** without modifiers, run in its frame. -/
theorem body_progress (hG : CallsOKX X A G c) (hS : X.Sound G A (· = c)) (F : Fr) (hc : F.contract = c)
    (n : Nat) (b : RBody E) (l : Locals E.layout b.locals) (hf : IFrag X A b.items) (ho : b.items.OpsOK)
    (hfr : BodyFrame b.ps.length b.rs b.locals) (x : Locals E.layout [] × St E) :
    Ends ((runMods G F n b [] l).run x).1 :=
  NS.ends ((fragXAt hG hS n).mods F hc b l hf ho hfr) x

/-- **Progress of internal calls** to the allowed functions: a call never
gets stuck. -/
theorem call_progress (hG : CallsOKX X A G c) (hS : X.Sound G A (· = c)) (F : Fr) (hc : F.contract = c)
    (n : Nat) (d : Decl) {ps rs : List STy} (hs : d.fnSig E = some (ps, rs)) (hA : A d)
    (vs : Vals E.layout ps) (x : Locals E.layout [] × St E) :
    Ends ((callInternal G F n d vs rs).run x).1 :=
  NS.ends ((fragXAt hG hS n).call F hc d hs hA vs) x

/-- Without allowed calls the program premise holds for every program. -/
theorem callsOKX_none (X : StmtExt E) (G : Glob E) (c : String) : CallsOKX X (fun _ => False) G c :=
  fun _ _ _ _ h => h.elim

/-- **Tuple declarations in the value fragment**: a statement of the value
fragment extended with tuple declarations (no calls, no extension) never
gets stuck, in any program. -/
theorem tuple_stmt_progress (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ)
    (hf : SFrag (StmtExt.none E) (fun _ => False) s) (ho : s.OpsOK) (hfr : BodyFrame nps R Γ)
    (x : Locals E.layout [] × St E) : Ends ((execS G F n nps ph s l).run x).1 :=
  stmt_progress (c := F.contract) (callsOKX_none _ G F.contract) (StmtExt.none_sound G _ _) F rfl n nps ph s l hf ho hfr x

section
open Solidity.Lowering.P9

variable {res : Resolution} {G : Glob res.env} {c : String}

/-- **Elaborated programs**: for an elaborated program whose complete
function catalogue P9 checks, every internal call of a catalogued function
ends. -/
theorem elaborated_call_progress (ha : (Source.elaborate res).isSome = true)
    (hg : G.prog = Source.progOf res.env) (hc : WholeProgram.checkFunctions res G c = true)
    (F : Fr) (hF : F.contract = c) (n : Nat) (d : Decl) {ps rs : List STy}
    (hs : d.fnSig res.env = some (ps, rs)) (hd : d ∈ WholeProgram.functions res)
    (vs : Vals res.env.layout ps) (x : Locals res.env.layout [] × St res.env) :
    Ends ((callInternal G F n d vs rs).run x).1 :=
  call_progress (CallsOK.toX (WholeProgram.functions_from_elaborate res ha G hg c hc) (StmtExt.none _))
    (StmtExt.none_sound G _ _) F hF n d hs hd vs x

/-- **Elaborated programs, statements of the extended fragment**: in such a
program, a statement calling catalogued functions, possibly with tuple
declarations and nodes of a sound extension, ends. -/
theorem elaborated_stmt_progress {X : StmtExt res.env} (ha : (Source.elaborate res).isSome = true)
    (hg : G.prog = Source.progOf res.env) (hc : WholeProgram.checkFunctions res G c = true)
    (hS : X.Sound G (fun d => d ∈ WholeProgram.functions res) (· = c))
    (F : Fr) (hF : F.contract = c) (n nps : Nat) (ph : Option (Ph res.env)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt res.env R M k Γ Γ') (l : Locals res.env.layout Γ)
    (hf : SFrag X (fun d => d ∈ WholeProgram.functions res) s) (ho : s.OpsOK) (hfr : BodyFrame nps R Γ)
    (x : Locals res.env.layout [] × St res.env) : Ends ((execS G F n nps ph s l).run x).1 :=
  stmt_progress (CallsOK.toX (WholeProgram.functions_from_elaborate res ha G hg c hc) X) hS F hF n nps ph s l hf ho hfr x

end

end Solidity.Theory.Progress
