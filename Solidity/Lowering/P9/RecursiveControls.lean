import Solidity.Lowering.P9.ProgramAdmission
import Solidity.Lowering.P9.InferenceCuts
import Solidity.Lowering.P9.AdmissionControls

/-! An actual elaborated recursive source function feeds the general checker.
This is source non-stuckness only: no recursive compiler or termination claim.
-/
namespace Solidity.Lowering.P9.RecursiveControls
open Source Roadmap

def function : Source.Syn (.part true) :=
  .function (.ident "recur") .nil none none .nil false none
    (.cons (.param (.elem .bool) none none) .nil)
    (.some (.block (.cons (.stmtItem (.returnStmt
      (.some (.call (.ident "recur") (.positional .nil))))) .nil)))
def unit : Source.Syn .unit := .unit (.cons (.topPart function) .nil)
def resolution := Source.resolveUnit {pipeline := .legacy} unit
def declaration : Source.Decl := ⟨.function, "recur", none, true, function⟩
def frame := (declaration.frame? resolution.env).get (by rfl)
def inferred := (Source.ItemsD.infer (frame.ctx resolution.env declaration.scope) frame.locals frame.body).get (by rfl)

theorem frame_eq : declaration.frame? resolution.env = some frame := rfl
theorem inferred_eq : Source.ItemsD.infer (frame.ctx resolution.env declaration.scope) frame.locals frame.body = some inferred := rfl
theorem invs_eq : declaration.modInvs.invList = [] := by
  rw [show declaration.modInvs = .nil from rfl, Source.Syn.invList]
theorem body_exists : (Source.elabBody resolution.env declaration).isSome = true :=
  InferenceCuts.body_some resolution.env declaration frame frame_eq (by rw [inferred_eq]; rfl) invs_eq

theorem elaborates_eq : Source.elaborates resolution.env = true := by
  change ((((Source.elabBody resolution.env declaration).isSome && true) && true) && true) = true
  rw [body_exists]
  rfl

theorem actual_elaboration : (Source.elaborate resolution).isSome = true := by
  simp only [Source.elaborate, elaborates_eq, ↓reduceIte, Option.isSome_some]

def body := Source.RBody.ofDerivation frame inferred.2 []
theorem prog_body : (Source.progOf resolution.env).body declaration = some body := by
  have hm : (Source.elabMods resolution.env declaration frame declaration.modInvs.invList).map Subtype.val = some [] := by
    rw [invs_eq, Source.elabMods]
    rfl
  simp only [Source.progOf, Source.elabBody, frame_eq, inferred_eq]
  cases he : Source.elabMods resolution.env declaration frame declaration.modInvs.invList with
  | none => rw [he] at hm; cases hm
  | some v =>
    rcases v with ⟨ms, hms⟩
    simp only [he, Option.map_some, Option.some.injEq] at hm
    subst ms
    rfl

def glob (fixed : Roadmap.Fixed) : Source.Glob resolution.env :=
  ⟨Source.progOf resolution.env, .legacy, fixed, fun _ => ⟨0, by decide⟩,
    fun _ _ => true, fun _ => .answer (.success []), ⟨0, by decide⟩⟩
theorem signature : declaration.fnSig resolution.env = some ([], [.bool]) := rfl

/-- A shared intrinsic normal form, tied to the computed elaboration below. -/
def flatBody : Source.RBody resolution.env where
  ps := []
  rs := [.bool]
  inModifier := false
  locals := [.bool]
  out := [.bool]
  items := .stmt (.retVal rfl (.call declaration signature .nil) (by rfl)) .nil
  mods := []

theorem body_flat : body = flatBody := by rfl

/-- A pointwise body cache with a proved equality to the actual source program.
It avoids repeating inference while reducing execution; no execution is assumed. -/
def cachedGlob (fixed : Roadmap.Fixed) : Source.Glob resolution.env :=
  {glob fixed with prog := {(glob fixed).prog with
    body := fun d => if d = declaration then some flatBody else (glob fixed).prog.body d}}

theorem cachedGlob_eq (fixed : Roadmap.Fixed) : cachedGlob fixed = glob fixed := by
  have hb : (glob fixed).prog.body declaration = some flatBody := by
    rw [show (glob fixed).prog = Source.progOf resolution.env from rfl, prog_body, body_flat]
  have hp : (fun d => if d = declaration then some flatBody else (glob fixed).prog.body d) =
      (glob fixed).prog.body := by
    funext d
    split
    next h => subst d; exact hb.symm
    next h => rfl
  unfold cachedGlob
  rw [hp]

theorem dispatch_eq (fixed : Roadmap.Fixed) : (glob fixed).dispatchFn "P9" declaration = declaration := by
  unfold Source.Glob.dispatchFn
  rw [signature]
  rfl

theorem checker_accepts (fixed : Roadmap.Fixed) :
    WholeProgram.check resolution (glob fixed) "P9" [declaration] = true := by
  simp only [WholeProgram.check, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨rfl, List.mem_singleton.mpr rfl, ?_⟩
  have hb : (glob fixed).prog.body declaration = some body := prog_body
  simp only [WholeProgram.checkBody, signature, dispatch_eq, hb]
  rfl

theorem derived_callsOK (fixed : Roadmap.Fixed) :
    Source.CallsOK (fun d => d ∈ [declaration]) (glob fixed) "P9" :=
  WholeProgram.from_elaborate resolution actual_elaboration (glob fixed) rfl "P9" [declaration] (checker_accepts fixed)

def call : Source.RExpr resolution.env [] .bool := .call declaration signature .nil

theorem recursive_not_stuck (fixed : Roadmap.Fixed) (n : Nat) :
    Source.NS (Source.evalE (glob fixed) Solidity.Lowering.P9.caller n call) :=
  Source.evalE_callFrag_ns (derived_callsOK fixed) Solidity.Lowering.P9.caller rfl n call
    ⟨List.mem_singleton.mpr rfl, trivial⟩ trivial

/-- Same finite horizon used by the existing source recursion control. -/
theorem recursive_timeout (fixed : Roadmap.Fixed) (s : Source.St resolution.env) :
    (Source.evalE (glob fixed) Solidity.Lowering.P9.caller 12 call).run (.nil, s) =
      (.error .timeout, (.nil, s)) := by
  rw [← cachedGlob_eq fixed]
  rfl

#print axioms actual_elaboration
#print axioms checker_accepts
#print axioms derived_callsOK
#print axioms recursive_not_stuck
#print axioms recursive_timeout
end Solidity.Lowering.P9.RecursiveControls
