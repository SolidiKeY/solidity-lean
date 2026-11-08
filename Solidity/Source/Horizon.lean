import Solidity.Source.HorizonApproxStatements

/-!
# Horizons: timed-out runs show a prefix of the events

The last part of the horizon results (S05 item 2), whose overview is in
`Solidity/Source/HorizonFuel.lean`: fuel monotonicity and horizon
independence there, events only grow in `HorizonGrow`, helpers keep the
events in `HorizonConst`, and here `approxAt` and `runTx_events_mono`. The
module was split for checking cost; importers of `Solidity.Source.Horizon`
see every part. Expression and statement proof stages are imported through
HorizonApproxExpressions and HorizonApproxStatements; qualified theorem names
and the frozen record remain unchanged.
-/

namespace Solidity.Source

open EM
open Solidity.Roadmap (Address Word Bytes Request Outcome Event)

variable {E : Env}

section
variable (G : Glob E)

/-- **The induction hypothesis**: every interpreter function at horizon `n`
approximates itself at `n + 1`. -/
structure ApproxAt (n : Nat) : Prop where
  evalE : ∀ (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ), Approx (evalE G F n e) (evalE G F (n + 1) e)
  evalPair : ∀ (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ),
    Approx (evalPair G F n a b) (evalPair G F (n + 1) a b)
  evalArgs : ∀ (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs),
    Approx (evalArgs G F n es) (evalArgs G F (n + 1) es)
  evalConvArgs : ∀ (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs),
    Approx (evalConvArgs G F n es) (evalConvArgs G F (n + 1) es)
  evalLoc : ∀ (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ), Approx (evalLoc G F n l) (evalLoc G F (n + 1) l)
  evalBuiltin : ∀ (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin) (args : RArgs E Γ σs) (τ : STy),
    Approx (evalBuiltin G F n b args τ) (evalBuiltin G F (n + 1) b args τ)
  evalArgsRev : ∀ (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs),
    Approx (evalArgsRev G F n es) (evalArgsRev G F (n + 1) es)
  pay : ∀ (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)),
    Approx (pay G F n a v) (pay G F (n + 1) a v)
  execS : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ),
    Approx (execS G F n nps ph s l) (execS G F (n + 1) nps ph s l)
  forIter : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool} {Γ₁ Γ₂ : RCtx}
    (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁),
    Approx (forIter G F n nps ph c post body l) (forIter G F (n + 1) nps ph c post body l)
  execItems : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ),
    Approx (execItems G F n nps ph b l) (execItems G F (n + 1) nps ph b l)
  runMods : ∀ (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals)) (l : Locals E.layout b.locals),
    Approx (runMods G F n b mods l) (runMods G F (n + 1) b mods l)
  callInternal : ∀ (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps) (rs : List STy),
    Approx (callInternal G F n d vs rs) (callInternal G F (n + 1) d vs rs)
  callAddr : ∀ (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word) (input : Solidity.Roadmap.Bytes)
    (static : Bool), Approx (callAddr G F n a v input static) (callAddr G F (n + 1) a v input static)
  enterInstance : ∀ (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word) (input : Solidity.Roadmap.Bytes)
    (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout),
    Approx (enterInstance G n a sender v input static c depth m)
      (enterInstance G (n + 1) a sender v input static c depth m)
  envLoop : ∀ (depth : Nat) (pstatic : Bool), Approx (envLoop G n depth pstatic) (envLoop G (n + 1) depth pstatic)
  dispatch : ∀ (F : Fr) (input : Solidity.Roadmap.Bytes), Approx (dispatch G F n input) (dispatch G F (n + 1) input)

theorem approxAt_zero : ApproxAt G 0 where
  evalE := by intros; rw [evalE.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalE
  evalPair := by intros; rw [evalPair.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalPair
  evalArgs := by intros; rw [evalArgs.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalArgs
  evalConvArgs := by intros; rw [evalConvArgs.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalConvArgs
  evalLoc := by intros; rw [evalLoc.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalLoc
  evalBuiltin := by intros; rw [evalBuiltin.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalBuiltin
  evalArgsRev := by intros; rw [evalArgsRev.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalArgsRev
  pay := by intros; rw [pay.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).pay
  execS := by intros; rw [execS.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).execS
  forIter := by intros; rw [forIter.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).forIter
  execItems := by intros; rw [execItems.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).execItems
  runMods := by intros; rw [runMods.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).runMods
  callInternal := by intros; rw [callInternal.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).callInternal
  callAddr := by intros; rw [callAddr.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).callAddr
  enterInstance := by intros; rw [enterInstance.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).enterInstance
  envLoop := by intros; rw [envLoop.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).envLoop
  dispatch := by intros; rw [dispatch.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).dispatch

variable {G} {n : Nat}

theorem evalE_apart_0 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 0 ≤ e.ctorIdx ∧ e.ctorIdx < 12) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_1 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 12 ≤ e.ctorIdx ∧ e.ctorIdx < 24) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_2 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 24 ≤ e.ctorIdx ∧ e.ctorIdx < 28) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_3 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 28 ≤ e.ctorIdx ∧ e.ctorIdx < 32) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_4 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 32 ≤ e.ctorIdx ∧ e.ctorIdx < 33) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_5 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 33 ≤ e.ctorIdx ∧ e.ctorIdx < 34) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_6 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 34 ≤ e.ctorIdx ∧ e.ctorIdx < 35) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_7 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 35 ≤ e.ctorIdx ∧ e.ctorIdx < 36) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_apart_8 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 36 ≤ e.ctorIdx ∧ e.ctorIdx < 60) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalE_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) :
    Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  exact (approxAtKnown G (n + 1)).evalE true F e

theorem evalPair_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ) :
    Approx (evalPair G F (n + 1) a b) (evalPair G F (n + 1 + 1) a b) := by
  exact (approxAtKnown G (n + 1)).evalPair true F a b

theorem evalArgs_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Approx (evalArgs G F (n + 1) es) (evalArgs G F (n + 1 + 1) es) := by
  exact (approxAtKnown G (n + 1)).evalArgs true F es

theorem evalConvArgs_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) :
    Approx (evalConvArgs G F (n + 1) es) (evalConvArgs G F (n + 1 + 1) es) := by
  exact (approxAtKnown G (n + 1)).evalConvArgs true F es

theorem evalLoc_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    Approx (evalLoc G F (n + 1) l) (evalLoc G F (n + 1 + 1) l) := by
  exact (approxAtKnown G (n + 1)).evalLoc true F l

theorem evalBuiltin_apart_0 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .require ∨ b = .assert ∨ b = .revert) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  exact (approxAtKnown G (n + 1)).evalBuiltin true F b args τ

theorem evalBuiltin_apart_1 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .keccak256 ∨ b = .sha256 ∨ b = .ripemd160) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  exact (approxAtKnown G (n + 1)).evalBuiltin true F b args τ

theorem evalBuiltin_apart_2 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .addmod) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  exact (approxAtKnown G (n + 1)).evalBuiltin true F b args τ

theorem evalBuiltin_apart_3 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .mulmod) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  exact (approxAtKnown G (n + 1)).evalBuiltin true F b args τ

theorem evalBuiltin_apart_4 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .ecrecover) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  exact (approxAtKnown G (n + 1)).evalBuiltin true F b args τ

theorem evalBuiltin_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin)
    (args : RArgs E Γ σs) (τ : STy) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  exact (approxAtKnown G (n + 1)).evalBuiltin true F b args τ

theorem evalArgsRev_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Approx (evalArgsRev G F (n + 1) es) (evalArgsRev G F (n + 1 + 1) es) := by
  exact (approxAtKnown G (n + 1)).evalArgsRev true F es

theorem pay_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true))
    (v : RExpr E Γ (.int IntTy.u256)) : Approx (pay G F (n + 1) a v) (pay G F (n + 1 + 1) a v) := by
  exact (approxAtKnown G (n + 1)).pay true F a v

theorem execS_apart_0 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ)
    (h : 0 ≤ s.ctorIdx ∧ s.ctorIdx < 8) :
    Approx (execS G F (n + 1) nps ph s l) (execS G F (n + 1 + 1) nps ph s l) := by
  exact (approxAtKnown G (n + 1)).execS true F nps ph s l

theorem execS_apart_1 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ)
    (h : 8 ≤ s.ctorIdx ∧ s.ctorIdx < 16) :
    Approx (execS G F (n + 1) nps ph s l) (execS G F (n + 1 + 1) nps ph s l) := by
  exact (approxAtKnown G (n + 1)).execS true F nps ph s l

theorem execS_apart_2 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ)
    (h : 16 ≤ s.ctorIdx ∧ s.ctorIdx < 40) :
    Approx (execS G F (n + 1) nps ph s l) (execS G F (n + 1 + 1) nps ph s l) := by
  exact (approxAtKnown G (n + 1)).execS true F nps ph s l

theorem execS_astep (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) :
    Approx (execS G F (n + 1) nps ph s l) (execS G F (n + 1 + 1) nps ph s l) := by
  exact (approxAtKnown G (n + 1)).execS true F nps ph s l

theorem forIter_astep (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool}
    {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂)
    (l : Locals E.layout Γ₁) :
    Approx (forIter G F (n + 1) nps ph c post body l) (forIter G F (n + 1 + 1) nps ph c post body l) := by
  exact (approxAtKnown G (n + 1)).forIter true F nps ph c post body l

theorem execItems_astep (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) :
    Approx (execItems G F (n + 1) nps ph b l) (execItems G F (n + 1 + 1) nps ph b l) := by
  exact (approxAtKnown G (n + 1)).execItems true F nps ph b l

theorem runMods_astep (ih : ApproxAt G n) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals))
    (l : Locals E.layout b.locals) : Approx (runMods G F (n + 1) b mods l) (runMods G F (n + 1 + 1) b mods l) := by
  exact (approxAtKnown G (n + 1)).runMods true F b mods l

theorem callInternal_astep (ih : ApproxAt G n) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps)
    (rs : List STy) : Approx (callInternal G F (n + 1) d vs rs) (callInternal G F (n + 1 + 1) d vs rs) := by
  exact (approxAtKnown G (n + 1)).callInternal true F d vs rs

theorem callAddr_astep (ih : ApproxAt G n) (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) :
    Approx (callAddr G F (n + 1) a v input static) (callAddr G F (n + 1 + 1) a v input static) := by
  exact (approxAtKnown G (n + 1)).callAddr F a v input static

theorem enterInstance_astep (ih : ApproxAt G n) (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout) :
    Approx (enterInstance G (n + 1) a sender v input static c depth m)
      (enterInstance G (n + 1 + 1) a sender v input static c depth m) := by
  exact (approxAtKnown G (n + 1)).enterInstance a sender v input static c depth m

theorem envLoop_astep (ih : ApproxAt G n) (depth : Nat) (pstatic : Bool) :
    Approx (envLoop G (n + 1) depth pstatic) (envLoop G (n + 1 + 1) depth pstatic) := by
  exact (approxAtKnown G (n + 1)).envLoop depth pstatic

theorem dispatch_apart_fn {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d : Decl}
    (hp : G.pickFn F input = some d) (he : input.isEmpty = false) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gn_c {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} {ri : RInit E}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = some ri) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gn_v {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} {τ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = none) (hv : d.varTy E = some τ) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gn_x {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} 
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = none) (hv : d.varTy E = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gn_u {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} 
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = false) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gn {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {r : Decl × List STy × STy} (hg : G.pickGetter F input = some r) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gs_c {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} {ri : RInit E}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = some ri) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gs_v {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} {τ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = none) (hv : d.varTy E = some τ) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gs_x {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} 
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = true) (hc : G.prog.consts d = none) (hv : d.varTy E = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gs_u {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} 
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hm : (ρ :: ps).all STy.isValueTy = false) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_gs {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {r : Decl × List STy × STy} (hg : G.pickGetter F input = some r) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_sn {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes)
    (hp : G.pickFn F input = none) (hg : G.pickGetter F input = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_apart_ss {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d : Decl}
    (hp : G.pickFn F input = some d) (he : input.isEmpty = true) (hg : G.pickGetter F input = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

theorem dispatch_astep (ih : ApproxAt G n) (F : Fr) (input : Solidity.Roadmap.Bytes) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (approxAtKnown G (n + 1)).dispatch F input

/-- **Every interpreter function is monotone in its horizon.** -/
theorem approxAt (G : Glob E) : ∀ n, ApproxAt G n
  | 0 => approxAt_zero G
  | n + 1 =>
    have h : ApproxAtKnown G (n + 1) := approxAtKnown G (n + 1)
    ⟨h.evalE true, h.evalPair true, h.evalArgs true, h.evalConvArgs true,
      h.evalLoc true, h.evalBuiltin true, h.evalArgsRev true, h.pay true,
      h.execS true, h.forIter true, h.execItems true, h.runMods true,
      h.callInternal true, h.callAddr, h.enterInstance, h.envLoop,
      h.dispatch⟩

end

/-! ### Transactions show a prefix of their events -/

theorem runTx_grow (G : Glob E) (n : Nat) (q : Request) : Grow (runTx G n q) := by
  have gn := growAt { G with timestamp := q.timestamp } n
  unfold runTx
  dsimp only
  grow_go [gn.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow]

theorem runTx_approx (G : Glob E) (n : Nat) (q : Request) : Approx (runTx G n q) (runTx G (n + 1) q) := by
  have ih := approxAt { G with timestamp := q.timestamp } n
  unfold runTx
  dsimp only
  refine Approx.bind (Approx.refl (mark_grow)) fun m => ?_
  refine Approx.bind (Approx.refl (instanceAt_grow _ _)) fun oc => ?_
  split
  · exact Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow])
  · refine Approx.attempt_bind ?_ (fun _ => Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow])) (fun _ => ⟨rfl, rfl⟩)
    exact Approx.bind (Approx.refl (credit_grow _ _)) fun _ => ih.dispatch _ _

theorem Approx.mono {Γ : RCtx} {α : Type} {f : Nat → EM E Γ α} (h : ∀ n, Approx (f n) (f (n + 1)))
    (hg : ∀ n, Grow (f n)) {n m : Nat} (hnm : n ≤ m) : Approx (f n) (f m) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction d with
  | zero => exact Approx.refl (hg n)
  | succ d ih => exact (ih (by omega)).trans (h _)

/-- **A transaction's events grow with its horizon**: a run that has not
completed at horizon `k` shows a prefix of the events of the run at every
`k' ≥ k`. -/
theorem runTx_events_mono (G : Glob E) (q : Request) (s : St E) {k k' : Nat} (hk : k ≤ k')
    (hd : Done (runAt (fun f => runTx G f q) s k) = false) :
    (runAt (fun f => runTx G f q) s k).2.events <+: (runAt (fun f => runTx G f q) s k').2.events := by
  have ha := Approx.mono (f := fun f => runTx G f q) (fun n => runTx_approx G n q) (fun n => runTx_grow G n q) hk
  simp only [runAt]
  rcases ha.2.2 (L0 E, s) with ⟨_, he⟩ | he
  · exact he
  · rw [he]; exact List.prefix_refl _

/-- A transaction's events extend the events before it. -/
theorem runTx_extends (G : Glob E) (q : Request) (s : St E) (k : Nat) :
    s.events <+: (runAt (fun f => runTx G f q) s k).2.events := runTx_grow G k q (L0 E, s)

/-- info: 'Solidity.Source.belowAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms belowAt

/-- info: 'Solidity.Source.runTx_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runTx_stable

/-- info: 'Solidity.Source.deploy_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deploy_stable

/-- info: 'Solidity.Source.firstDone_runTx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms firstDone_runTx

/-- info: 'Solidity.Source.runTx_stuck_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runTx_stuck_stable

end Solidity.Source