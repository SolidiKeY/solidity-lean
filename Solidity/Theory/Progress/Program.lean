import Solidity.Theory.Progress.Calls
import Solidity.Theory.Progress.Leaves
import Solidity.Lowering.P9.FunctionCatalog


namespace Solidity.Theory.Progress

open Solidity.Source Solidity.Source.Progress EM

variable {E : Env} {X : StmtExt E} {A : Decl → Prop} {G : Glob E} {c : String}

theorem expr_progress (hG : CallsOKX X A G c) (hS : X.Sound G A (· = c)) (F : Fr) (hc : F.contract = c)
    (n : Nat) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) (hf : RExpr.ValFragC A e) (ho : e.OpsOK)
    (x : Locals E.layout Γ × St E) : Ends ((evalE G F n e).run x).1 :=
  NS.ends (((fragXAt hG hS n).expr n (Nat.le_refl n) F hc).val e hf ho) x

theorem stmt_progress (hG : CallsOKX X A G c) (hS : X.Sound G A (· = c)) (F : Fr) (hc : F.contract = c)
    (n nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) (hf : SFrag X A s) (ho : s.OpsOK)
    (hfr : BodyFrame nps R Γ) (x : Locals E.layout [] × St E) : Ends ((execS G F n nps ph s l).run x).1 :=
  NS.ends ((fragXAt hG hS n).stmt.execS F hc nps ph s l hf ho hfr).ns x

theorem items_progress (hG : CallsOKX X A G c) (hS : X.Sound G A (· = c)) (F : Fr) (hc : F.contract = c)
    (n nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) (hf : IFrag X A b) (ho : b.OpsOK)
    (hfr : BodyFrame nps R Γ) (x : Locals E.layout [] × St E) : Ends ((execItems G F n nps ph b l).run x).1 :=
  NS.ends ((fragXAt hG hS n).stmt.execItems F hc nps ph b l hf ho hfr).ns x

theorem body_progress (hG : CallsOKX X A G c) (hS : X.Sound G A (· = c)) (F : Fr) (hc : F.contract = c)
    (n : Nat) (b : RBody E) (l : Locals E.layout b.locals) (hf : IFrag X A b.items) (ho : b.items.OpsOK)
    (hfr : BodyFrame b.ps.length b.rs b.locals) (x : Locals E.layout [] × St E) :
    Ends ((runMods G F n b [] l).run x).1 :=
  NS.ends ((fragXAt hG hS n).mods F hc b l hf ho hfr) x

theorem call_progress (hG : CallsOKX X A G c) (hS : X.Sound G A (· = c)) (F : Fr) (hc : F.contract = c)
    (n : Nat) (d : Decl) {ps rs : List STy} (hs : d.fnSig E = some (ps, rs)) (hA : A d)
    (vs : Vals E.layout ps) (x : Locals E.layout [] × St E) :
    Ends ((callInternal G F n d vs rs).run x).1 :=
  NS.ends ((fragXAt hG hS n).call F hc d hs hA vs) x

theorem callsOKX_none (X : StmtExt E) (G : Glob E) (c : String) : CallsOKX X (fun _ => False) G c :=
  fun _ _ _ _ h => h.elim

theorem tuple_stmt_progress (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ)
    (hf : SFrag (StmtExt.none E) (fun _ => False) s) (ho : s.OpsOK) (hfr : BodyFrame nps R Γ)
    (x : Locals E.layout [] × St E) : Ends ((execS G F n nps ph s l).run x).1 :=
  stmt_progress (c := F.contract) (callsOKX_none _ G F.contract) (StmtExt.none_sound G _ _) F rfl n nps ph s l hf ho hfr x


theorem SFrag.cast_out {X : StmtExt E} {A : Decl → Prop} {R : List STy} {M : Bool} {k : SCtx} {Γ Γ₁ Γ₂ : RCtx}
    (h : Γ₁ = Γ₂) (s : RStmt E R M k Γ Γ₁) (hs : SFrag X A s) :
    SFrag X A (cast (congrArg (RStmt E R M k Γ) h) s) := by
  subst h
  exact hs

theorem StmtD.declTuple_frag {C : Source.Ctx} {X : StmtExt C.env} {A : Decl → Prop} {k : SCtx} {L : List (String × STy)}
    {h : Nat} {d : Syn .varDecl} {ds : Syn (.list (.opt .varDecl))} {e : Syn .expr}
    {slots : List (Option (String × STy))} {σs : List STy}
    (hs : C.tupleSlots h d ds = some slots) (de : Typed (C.at L) e (.tuple σs))
    (hf : slotsFit C.isBase C.mapFree (slots.map (Option.map Prod.snd)) σs = true)
    (hi : TupleInit A de.toR) (ho : SlotsOK (slots.map (Option.map Prod.snd)) σs) :
    SFrag X A (StmtD.declTuple (k := k) hs de hf).toR :=
  SFrag.cast_out (pushSlots_tys slots L).symm _ (.declTuple _ _ _ hi ho)

section
open Solidity.Lowering.P9

variable {res : Resolution} {G : Glob res.env} {c : String}

theorem elaborated_call_progress (ha : (Source.elaborate res).isSome = true)
    (hg : G.prog = Source.progOf res.env) (hc : WholeProgram.checkFunctions res G c = true)
    (F : Fr) (hF : F.contract = c) (n : Nat) (d : Decl) {ps rs : List STy}
    (hs : d.fnSig res.env = some (ps, rs)) (hd : d ∈ WholeProgram.functions res)
    (vs : Vals res.env.layout ps) (x : Locals res.env.layout [] × St res.env) :
    Ends ((callInternal G F n d vs rs).run x).1 :=
  call_progress (CallsOK.toX (WholeProgram.functions_from_elaborate res ha G hg c hc) (StmtExt.none _))
    (StmtExt.none_sound G _ _) F hF n d hs hd vs x

theorem elaborated_stmt_progress {X : StmtExt res.env} (ha : (Source.elaborate res).isSome = true)
    (hg : G.prog = Source.progOf res.env) (hc : WholeProgram.checkFunctions res G c = true)
    (hS : X.Sound G (fun d => d ∈ WholeProgram.functions res) (· = c))
    (F : Fr) (hF : F.contract = c) (n nps : Nat) (ph : Option (Ph res.env)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt res.env R M k Γ Γ') (l : Locals res.env.layout Γ)
    (hf : SFrag X (fun d => d ∈ WholeProgram.functions res) s) (ho : s.OpsOK) (hfr : BodyFrame nps R Γ)
    (x : Locals res.env.layout [] × St res.env) : Ends ((execS G F n nps ph s l).run x).1 :=
  stmt_progress (CallsOK.toX (WholeProgram.functions_from_elaborate res ha G hg c hc) X) hS F hF n nps ph s l hf ho hfr x

theorem elaborated_leafExt_sound (ha : (Source.elaborate res).isSome = true)
    (hg : G.prog = Source.progOf res.env) (hc : WholeProgram.checkFunctions res G c = true) :
    (leafExt (fun d => d ∈ WholeProgram.functions res)).Sound G (fun d => d ∈ WholeProgram.functions res) (· = c) :=
  leafExt_sound fun n F hF => (checked_fragments ha hg hc n).1.expr F hF

end

end Solidity.Theory.Progress
