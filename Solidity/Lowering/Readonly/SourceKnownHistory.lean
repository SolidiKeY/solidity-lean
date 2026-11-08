import Solidity.Lowering.Readonly.SourceStatementParts.Part4
import Solidity.Lowering.Readonly.SourceCallAddressEffects
import Solidity.Lowering.Readonly.SourceEnvironmentEffects
import Solidity.Lowering.Readonly.CallbackFrame

/-! Generic journal-history interface for both delegated calldata modes.
Regression purpose: library entries with an unavailable pointer ABI must retain
journal histories through internal calls and explicit calldata refusals.
The existing seventeen-field `At` and all its statements remain unchanged. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
variable {E : Env}

/-- Smaller-bound histories quantify the actual calldata guard and include the
same typed delegated entry. No endpoint equality or ABI adequacy is assumed. -/
structure KnownAt (G : Glob E) (n : Nat) : Prop where
  evalE : ∀ (known : Bool) (F : Fr) ⦃Γ : RCtx⦄ ⦃τ : STy⦄ (e : RExpr E Γ τ), Effect F.static (evalE (calldataKnown := known) G F n e)
  evalPair : ∀ (known : Bool) (F : Fr) ⦃Γ : RCtx⦄ ⦃σ τ : STy⦄ (a : RExpr E Γ σ) (b : RExpr E Γ τ), Effect F.static (evalPair (calldataKnown := known) G F n a b)
  evalArgs : ∀ (known : Bool) (F : Fr) ⦃Γ : RCtx⦄ ⦃τs : List STy⦄ (es : RArgs E Γ τs), Effect F.static (evalArgs (calldataKnown := known) G F n es)
  evalConvArgs : ∀ (known : Bool) (F : Fr) ⦃Γ : RCtx⦄ ⦃τs : List STy⦄ (es : RConvArgs E Γ τs), Effect F.static (evalConvArgs (calldataKnown := known) G F n es)
  evalLoc : ∀ (known : Bool) (F : Fr) ⦃Γ : RCtx⦄ ⦃τ : STy⦄ (l : RLVal E Γ τ), Effect F.static (evalLoc (calldataKnown := known) G F n l)
  evalBuiltin : ∀ (known : Bool) (F : Fr) ⦃Γ : RCtx⦄ ⦃σs : List STy⦄ (b : Builtin) (args : RArgs E Γ σs) (τ : STy), Effect F.static (evalBuiltin (calldataKnown := known) G F n b args τ)
  evalArgsRev : ∀ (known : Bool) (F : Fr) ⦃Γ : RCtx⦄ ⦃τs : List STy⦄ (es : RArgs E Γ τs), Effect F.static (evalArgsRev (calldataKnown := known) G F n es)
  pay : ∀ (known : Bool) (F : Fr) ⦃Γ : RCtx⦄ (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)), Effect F.static (pay (calldataKnown := known) G F n a v)
  execS : ∀ (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) ⦃R : List STy⦄ ⦃M : Bool⦄ ⦃k : SCtx⦄ ⦃Γ Γ' : RCtx⦄ (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ), Effect F.static (execS (calldataKnown := known) G F n nps ph s l)
  forIter : ∀ (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) ⦃R : List STy⦄ ⦃M u : Bool⦄ ⦃Γ₁ Γ₂ : RCtx⦄ (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁), Effect F.static (forIter (calldataKnown := known) G F n nps ph c post body l)
  execItems : ∀ (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) ⦃R : List STy⦄ ⦃M : Bool⦄ ⦃k : SCtx⦄ ⦃Γ Γ' : RCtx⦄ (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ), Effect F.static (execItems (calldataKnown := known) G F n nps ph b l)
  runMods : ∀ (known : Bool) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals)) (l : Locals E.layout b.locals), Effect F.static (runMods (calldataKnown := known) G F n b mods l)
  callInternal : ∀ (known : Bool) (F : Fr) (d : Decl) ⦃ps : List STy⦄ (vs : Vals E.layout ps) (rs : List STy), Effect F.static (callInternal (calldataKnown := known) G F n d vs rs)
  callAddr : ∀ (F : Fr) (a : Address) (v : Word) (input : Bytes) (static : Bool), Effect (static || F.static) (callAddr G F n a v input static)
  enterInstance : ∀ (a sender : Address) (v : Word) (input : Bytes) (static : Bool) (c : String) (depth : Nat) (entry credited : St E), StaticJournal.History entry.ex static credited.ex → StaticJournal.History entry.ex static ((enterInstance G n a sender v input static c depth (entry.ex.journal.length, entry.logs.length, entry.heap)).run (L0 E, credited)).2.2.ex
  envLoop : ∀ (depth : Nat) (pstatic : Bool), Effect pstatic (envLoop G n depth pstatic)
  dispatch : ∀ (F : Fr) (input : Bytes), Effect F.static (dispatch G F n input)
  callLibrary : ∀ (F : Fr) (d : Decl) ⦃ps : List STy⦄ (vs : Vals E.layout ps) (rs : List STy), Effect F.static (callLibrary G F n d vs rs)

/-- The original available-calldata interface is an exact projection. -/
def KnownAt.toAt {G : Glob E} {n : Nat} (h : KnownAt G n) : At G n where
  evalE := h.evalE true
  evalPair := h.evalPair true
  evalArgs := h.evalArgs true
  evalConvArgs := h.evalConvArgs true
  evalLoc := h.evalLoc true
  evalBuiltin := h.evalBuiltin true
  evalArgsRev := h.evalArgsRev true
  pay := h.pay true
  execS := h.execS true
  forIter := h.forIter true
  execItems := h.execItems true
  runMods := h.runMods true
  callInternal := h.callInternal true
  callAddr := h.callAddr
  enterInstance := h.enterInstance
  envLoop := h.envLoop
  dispatch := h.dispatch

/-- Guard refusal does not mutate the world; the available branch uses its
actual action's history, without replacing an unavailable observation. -/
theorem withLibraryCalldata_effect {Γ : RCtx} {α : Type} (mode known : Bool)
    (ty : STy) (action : EM E Γ α) (history : Effect mode action) :
    Effect mode (withLibraryCalldata known ty action) := by
  cases known
  · simp only [withLibraryCalldata]
    split
    · exact Effect.halt mode _
    · exact history
  · exact history

theorem known_at_zero (global : Glob E) : KnownAt global 0 := by
  constructor <;> intros <;> first
  | (unfold Effect; intro locals state; exact .start _ _)
  | assumption

macro "known_history_go " h:ident F:ident n:ident : tactic =>
 `(tactic| repeat' first
   | (with_reducible exact ($h).evalE _ $F _)
   | (with_reducible exact ($h).evalPair _ $F _ _)
   | (with_reducible exact ($h).evalArgs _ $F _)
   | (with_reducible exact ($h).evalConvArgs _ $F _)
   | (with_reducible exact ($h).evalLoc _ $F _)
   | (with_reducible exact ($h).evalBuiltin _ $F _ _ _)
   | (with_reducible exact ($h).evalArgsRev _ $F _)
   | (with_reducible exact ($h).pay _ $F _ _)
   | (with_reducible exact ($h).execS _ $F _ _ _ _)
   | (with_reducible exact ($h).forIter _ $F _ _ _ _ _ _)
   | (with_reducible exact ($h).execItems _ $F _ _ _ _)
   | (with_reducible exact ($h).runMods _ $F _ _ _)
   | (with_reducible exact ($h).callInternal _ $F _ _ _)
   | (with_reducible exact ($h).callLibrary $F _ _ _)
   | (with_reducible exact Effect.parent ($F).static _ _ (($h).callAddr $F _ _ _ _))
   | (with_reducible exact Effect.pure ($F).static _)
   | (with_reducible exact Effect.halt ($F).static _)
   | (with_reducible exact Effect.lift ($F).static _)
   | (with_reducible exact Effect.locals ($F).static)
   | (with_reducible exact Effect.st ($F).static)
   | (with_reducible exact Effect.modSt ($F).static _ (fun _ => rfl))
   | (with_reducible exact getV_effect ($F).static _)
   | (with_reducible exact indexNat_effect ($F).static _)
   | (with_reducible exact readAt_effect ($F).static $F _ _)
   | (with_reducible exact storRef_effect ($F).static _ _)
   | (with_reducible exact readLoc_effect ($F).static $F _)
   | (with_reducible exact writeLoc_effect $F $n _ _)
   | (with_reducible exact deleteLoc_effect $F $n _)
   | (with_reducible exact indexLoc_effect ($F).static $F _ _)
   | (with_reducible exact keyStep_effect ($F).static $F $n _)
   | (with_reducible exact bytesOfRV_effect ($F).static $F $n _)
   | (with_reducible exact convRV_effect ($F).static $F $n _ _)
   | (with_reducible exact convExplicitRV_effect ($F).static $F $n _ _)
   | (with_reducible exact instanceAt_effect ($F).static _ _)
   | (with_reducible exact fieldsOf_effect ($F).static _ _)
   | (with_reducible exact allocRef_effect ($F).static _)
   | (with_reducible exact encodeVals_effect ($F).static $F $n _ _)
   | (with_reducible exact extReturn_effect ($F).static _ _)
   | (with_reducible exact copyInto_effect $F $n _ _ _)
   | (with_reducible exact abiDecodeData_effect ($F).static _ _)
   | (with_reducible exact lengthOf_effect ($F).static $F _)
   | (with_reducible exact readLen_effect ($F).static $F _)
   | (with_reducible exact ret32_effect ($F).static _ _)
   | (with_reducible exact zeroVals_effect ($F).static $n _)
   | (with_reducible exact emitEvent_effect ($F).static _)
   | (with_reducible exact (zero_histories ($F).static $n).2.1 _)
   | refine Effect.bind _ _ _ ?_ (fun value => ?_)
   | (with_reducible apply Effect.sub ($F).static)
   | (with_reducible apply Effect.attempt ($F).static)
   | split
   | dsimp only)

theorem evalPair_succ_known : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (known : Bool) (_h : KnownAt G n) {Γ : Solidity.Source.RCtx} {σ τ : Solidity.Source.STy} (a : Solidity.Source.RExpr E Γ σ) (b : Solidity.Source.RExpr E Γ τ), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.evalPair (calldataKnown := known) G F (n+1) a b) := by
  intro E G F n known h
  intros
  unfold Solidity.Source.evalPair
  known_history_go h F n

theorem evalArgs_succ_known : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (known : Bool) (_h : KnownAt G n) {Γ : Solidity.Source.RCtx} {τs : List Solidity.Source.STy} (es : Solidity.Source.RArgs E Γ τs), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.evalArgs (calldataKnown := known) G F (n+1) es) := by
  intro E G F n known h
  intros
  unfold Solidity.Source.evalArgs
  known_history_go h F n

theorem evalConvArgs_succ_known : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (known : Bool) (_h : KnownAt G n) {Γ : Solidity.Source.RCtx} {τs : List Solidity.Source.STy} (es : Solidity.Source.RConvArgs E Γ τs), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.evalConvArgs (calldataKnown := known) G F (n+1) es) := by
  intro E G F n known h
  intros
  unfold Solidity.Source.evalConvArgs
  known_history_go h F n

theorem evalArgsRev_succ_known : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (known : Bool) (_h : KnownAt G n) {Γ : Solidity.Source.RCtx} {τs : List Solidity.Source.STy} (es : Solidity.Source.RArgs E Γ τs), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.evalArgsRev (calldataKnown := known) G F (n+1) es) := by
  intro E G F n known h
  intros
  unfold Solidity.Source.evalArgsRev
  known_history_go h F n

theorem evalLoc_succ_known : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (known : Bool) (_h : KnownAt G n) {Γ : Solidity.Source.RCtx} {τ : Solidity.Source.STy} (l : Solidity.Source.RLVal E Γ τ), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.evalLoc (calldataKnown := known) G F (n+1) l) := by
  intro E G F n known h
  intros
  unfold Solidity.Source.evalLoc
  known_history_go h F n

theorem pay_succ_known : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (known : Bool) (_h : KnownAt G n) {Γ : Solidity.Source.RCtx} (a : Solidity.Source.RExpr E Γ (.address true)) (v : Solidity.Source.RExpr E Γ (.int Solidity.Source.IntTy.u256)), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.pay (calldataKnown := known) G F (n+1) a v) := by
  intro E G F n known h
  intros
  unfold Solidity.Source.pay
  known_history_go h F n

theorem evalBuiltin_succ_known : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (known : Bool) (_h : KnownAt G n) {Γ : Solidity.Source.RCtx} {σs : List Solidity.Source.STy} (b : Solidity.Source.Builtin) (args : Solidity.Source.RArgs E Γ σs) (τ : Solidity.Source.STy), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.evalBuiltin (calldataKnown := known) G F (n+1) b args τ) := by
  intro E G F n known h Γ σs b args τ
  cases b <;> unfold Solidity.Source.evalBuiltin <;> dsimp only
  all_goals repeat' first
   | (with_reducible exact h.evalArgsRev known F _)
   | (with_reducible exact h.evalArgs known F _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.bytesOfRV_effect F.static F n _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convRV_effect F.static F n _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.ret32_effect F.static _ _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

end Solidity.Lowering.Readonly.SourceHistory

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.KnownAt.toAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.KnownAt.toAt

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.withLibraryCalldata_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.withLibraryCalldata_effect

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.known_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.known_at_zero

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.evalPair_succ_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.evalPair_succ_known

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.evalArgs_succ_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.evalArgs_succ_known

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.evalConvArgs_succ_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.evalConvArgs_succ_known

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.evalArgsRev_succ_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.evalArgsRev_succ_known

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.evalLoc_succ_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.evalLoc_succ_known

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.pay_succ_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.pay_succ_known

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.evalBuiltin_succ_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.evalBuiltin_succ_known
